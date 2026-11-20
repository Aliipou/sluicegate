------------------------- MODULE TraceAuthGateV3 -------------------------
(*
  T8 — trace validation of AuthGateV3 against JSON-lines traces emitted by the
  Rust gate (cargo feature `trace`, authgate-kernel/src/tcb/trace.rs).

  NO refinement proof. This checks that each recorded finite trace is a
  behaviour of AuthGateV3: every event must be an enabled AuthGateV3 step
  (AdvanceEpoch / Revoke / ExecuteVerify) and, for verify events, the TLA
  Verify() decision must equal the decision the Rust code returned.

  Trace file: ./trace.jsonl (relative to TLC's cwd; validate_traces.sh copies
  each trace there). Line 1 = header (constants), then one event per line.
  Mapping of Rust -> TLA state/actions is documented in trace.rs.

  Accepted  <=> TLC: "No error has been found"
  Rejected  <=> TLC: "Temporal property TraceAccepted was violated" (trace gets stuck)
*)
EXTENDS AuthGateV3, Json, Sequences, Naturals, FiniteSets, TLC

Trace   == ndJsonDeserialize("trace.jsonl")
Hdr     == Trace[1]
Events  == SubSeq(Trace, 2, Len(Trace))
N       == Len(Events)

ToSet(s) == {s[i] : i \in 1..Len(s)}

TActors      == ToSet(Hdr.actors)
TResources   == ToSet(Hdr.resources)
TProofHashes == ToSet(Hdr.proof_hashes)
TPublicKeys  == ToSet(Hdr.pubkeys)
TRootKey     == Hdr.root_key
TMaxDepth    == Hdr.max_chain_depth
TMaxEpoch    == Hdr.max_epoch
THash(k)     == Hdr.hash[k]

ToCap(c) == [proof_hash    |-> c.proof_hash,
             subject_id    |-> c.subject_id,
             resource_hash |-> c.resource_hash,
             rights        |-> ToSet(c.rights),
             expiry        |-> c.expiry,
             epoch         |-> c.epoch,
             issuer        |-> c.issuer,
             issuer_pubkey |-> c.issuer_pubkey,
             sig_valid     |-> c.sig_valid]

ToAction(a) == [actor_id        |-> a.actor_id,
                resource_hash   |-> a.resource_hash,
                required_rights |-> ToSet(a.required_rights),
                min_epoch       |-> a.min_epoch,
                timestamp       |-> a.timestamp,
                cap_bundle      |-> {ToCap(a.cap_bundle[i]) : i \in 1..Len(a.cap_bundle)},
                binding_valid   |-> a.binding_valid]

VARIABLE pos

TVars == <<global_epoch, revoked_set, session_rights, audit_log, pos>>

TInit == Init /\ pos = 1

TNext ==
  /\ pos <= N
  /\ LET e == Events[pos] IN
       \/ /\ e.kind = "advance"
          /\ AdvanceEpoch(e.epoch)
       \/ /\ e.kind = "revoke"
          /\ Revoke(e.hash)
       \/ /\ e.kind = "verify"
          /\ ExecuteVerify(ToAction(e.action), e.now)
          /\ audit_log'[Len(audit_log')].decision = e.decision
  /\ pos' = pos + 1

TSpec == TInit /\ [][TNext]_TVars /\ WF_TVars(TNext)

\* The whole trace must be consumed.
TraceAccepted == <>(pos = N + 1)

=============================================================================
