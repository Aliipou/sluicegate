# Sluicegate

**A small, deterministic gate that decides whether an action is covered by a valid, signed capability.**

Give it an action and a set of signed proofs. It returns `Permit` or `Deny`. Same inputs, same answer. No LLM calls, no scores, no network.

[![CI](https://github.com/Aliipou/sluicegate/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Aliipou/sluicegate/actions)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

[Live demo](https://authgate-hub.vercel.app) runs the compiled kernel in your browser.

## The problem

An agent, planner or service can ask to read a file, call an API or move money faster than a human can review. Most systems treat "it asked" as permission. Prompt tricks, framework bugs or a compromised sub-agent can then invent authority.

Sluicegate puts one check in front of the action:

```text
decision-maker  ->  Sluicegate (verify proof)  ->  tool / IO
                          |
                          +-- Deny: logged, action does not run
```

The check is one question: *does this actor hold a valid, signed, non-revoked capability for this resource and these rights?* If not, nothing runs.

## What it gives you

| Feature | In practice |
|---|---|
| Signed capability chains | Ed25519 proofs. Identity is bound as `subject_id = SHA-256(pubkey)`. |
| Attenuation | A delegated capability can only carry a subset of its parent's rights, never more. |
| Epoch revocation | Raise `min_epoch` to invalidate a whole cohort in one step. No denylist to maintain. |
| Deterministic decisions | Same action, same trust root, same time gives the same result. |
| Tamper-evident audit | Every decision goes into a SHA-256 hash-chained log. |
| Small trusted core | The Rust path that enforces decisions is a few hundred lines with `#![forbid(unsafe_code)]`. |
| JSON wire contract | Integrate through schemas, not a framework. |

Wire schemas: [`spec/canonical_action.schema.json`](spec/canonical_action.schema.json) (what you submit), [`spec/gate_result.schema.json`](spec/gate_result.schema.json) (what you get back), [`spec/audit_entry.schema.json`](spec/audit_entry.schema.json) (what is logged).

## How a decision is made

```text
Human principal (trust root)
   signs capability chains, sets min_epoch
        |
        v
CanonicalAction: actor, resource, rights, proofs, nonce, binding_hash
        |
        v
CallGate checks, in order:
   binding -> identity -> expiry -> epoch -> resource -> attenuation -> revocation
        |
        v
Permit | Deny { reason }   ->   hash-chained audit log
```

The nine invariants the gate enforces on every call:

| # | Name | Meaning |
|---|---|---|
| I1 | CanonicalBinding | `binding_hash` equals the SHA-256 of the other fields |
| I2 | IdentityBinding | the capability's subject matches the actor |
| I3 | ExpiryGate | the capability has not expired |
| I4 | EpochSafety | the leaf epoch is at least `min_epoch` |
| I5 | ResourceBinding | the capability's resource matches the action's |
| I6 | Attenuation | child rights are a subset of parent rights at every hop |
| I7 | ChainEpoch | intermediate nodes also meet the epoch |
| I8 | ChainComplete | every delegated capability in a Permit has a valid parent in the bundle |
| I9 | RevocationSafety | only root-signed revocations change a decision |

## Quick start

**Docker verifier API** (details in [INFRA.md](INFRA.md)):

```bash
cp .env.example .env   # set AUTHGATE_ADMIN_TOKEN
docker compose up --build -d
curl -s localhost:8000/readyz
```

**Rust** (this is the part that carries the security claims):

```rust
use authgate_kernel::tcb::{call_gate::CallGate, types::{CanonicalAction, Decision}};

let gate = CallGate::new(root_verifying_key);
let mut action = build_canonical_action(/* ... */);
action.binding_hash = action.compute_hash();

match gate.execute(&action, unix_now()) {
    Decision::Permit => execute_action(),
    Decision::Deny { reason } => reject(reason),
}
```

**Python** is a compatibility runtime and can be bypassed. Do not use it as the security boundary.

```python
from authgate.kernel.entities import AgentType, Entity, Resource, ResourceType, RightsClaim
from authgate.kernel.registry import OwnershipRegistry
from authgate.kernel.verifier import Action, FreedomVerifier

registry = OwnershipRegistry()
alice = Entity("alice", AgentType.HUMAN)
bot = Entity("analyst-bot", AgentType.MACHINE)
data = Resource("sales-data", ResourceType.DATASET, scope="/data/sales/")

registry.register_machine(bot, alice)
registry.add_claim(RightsClaim(bot, data, can_read=True))

verifier = FreedomVerifier(registry.freeze())
print(verifier.verify(Action("read-sales", actor=bot, resources_read=[data])).summary())
```

**CLI:** `pip install -e . && authgate-cli verify --registry registry.json --action action.json --audit log.jsonl`

**Sandboxing:** `cargo build --features sandbox` adds a WASM executor limited to the permitted rights. On Linux, `SeccompExecutor` applies a matching syscall allowlist.

## What is verified

Three layers, each with a different strength. None of them is a full proof of the Rust code.

| Layer | What it covers | Status |
|---|---|---|
| Rust tests | Kernel behaviour | 301 library tests pass (`cargo test`) |
| Kani | Bounded model checking of Rust properties, such as determinism and attenuation | Harnesses in [`formal/`](formal/) |
| TLA+ / TLC | Safety of the abstract state machine | Bounded model check, run in CI |
| Lean 4 | Abstract models of the gate | Two packages, below |

**Lean 4.** The axiom guard (`formal/lean4/run_axiom_guard.sh`) checks every theorem constant. Current result:

| Package | Theorems checked | Declared axioms | Violations |
|---|---|---|---|
| `FreedomKernel` | 152 | 0 | 0 |
| `Authgate` | 19 | 0 | 0 |

The guard counts theorem constants, including Lean-generated helper lemmas, so these are not counts of hand-written theorems. It fails the build on `sorry`, extra axioms, and three kinds of empty proof:

- **VACUOUS-THM:** the conclusion is true for any input.
- **RESTATED:** the proof just returns its own hypothesis.
- **TAUTOLOGY:** the statement is `x = x` or similar.

What the Lean models cover:

- `Composition.lean`: a veto-only verdict lattice (`allow < limit < contain < defer < deny`). Combining verdicts can never be more permissive than the most restrictive input.
- `Chain.lean`: the delegation-chain check from `dag.rs`, over 64-bit rights with a depth limit of 16.
- `MultiAgent.lean`: attenuation is transitive and never escalates read, write or delegate rights.
- `Temporal.lean`: information-flow control over a plan. Data read at one step is never written to a lower-labelled resource later. Unknown labels fail closed.
- `TCB.lean`: the forbidden-flag and human-ownership rules of the verifier core.

Limits you should know about:

- The Lean results are about abstract models. The link from those models to the signed-token Rust code is not formalised.
- Determinism of `verify` is checked by Kani, not Lean.
- There is no refinement proof from TLA+ to Rust.

Details and the full gap list: [formal/README.md](formal/README.md), [formal/INCOMPLETENESS.md](formal/INCOMPLETENESS.md).

## What it does not do

| Not this | Why |
|---|---|
| Stop an action that bypasses the gate | That needs process isolation, which is a separate and partial layer. |
| Understand intent or truth | The gate is structural. It does not read prompts. |
| Align model behaviour | Out of scope. |
| Defend against side channels | See [THREAT_MODEL.md](THREAT_MODEL.md). |
| Handle a malicious trust root | The root key is assumed honest. |
| Make Python a security boundary | Only the Rust core carries the claims. |
| Provide distributed consensus | Non-goal, see [NON_GOALS.md](NON_GOALS.md). |

The clock is supplied by the caller. Use the monotonic `SessionClock` so backward time jumps are rejected within a session.

Read [ASSUMPTIONS.md](ASSUMPTIONS.md) before relying on any claim here.

## How it compares

Sluicegate is not a replacement for general policy engines.

- Use **OPA** or **Cedar** for service or cloud policy.
- Use **OpenFGA / Zanzibar** for relationship graphs at scale.
- Use **a sandbox** (gVisor, Firecracker) to isolate processes.

Use Sluicegate for a narrow job: a cryptographic authority check between an agent and its tools, with delegation, attenuation and cohort revocation built in. Comparison and kill-tests: [COMPARATIVE_EVALUATION.md](COMPARATIVE_EVALUATION.md), [WHY_NOT_OPA.md](WHY_NOT_OPA.md).

## Run the tests

```bash
# Rust kernel
cd authgate-kernel && cargo test

# Lean: two packages, then the guard (must exit 0)
(cd formal/lean4 && lake exe cache get && lake build)   # Authgate (uses mathlib)
(cd formal/lean4/FreedomKernel && lake build)           # FreedomKernel
formal/lean4/run_axiom_guard.sh all

# Python
pip install -e ".[dev]" && pytest

# Attack harness
python attack_harness/wire_attacks.py
```

Run the guard only through `run_axiom_guard.sh`. Calling `lake env lean check_axioms.lean` directly prints nothing and exits 0 without checking anything.

## Repository layout

```text
authgate-kernel/    Rust kernel. Trusted core in src/tcb/.
formal/             TLA+, Kani, Lean 4, coverage and gap notes
src/authgate/       Python compatibility runtime and adapters (not trusted)
spec/               JSON Schema wire contract
attack_harness/     Wire, differential and mutation probes
examples/           Integrations, including a Kubernetes sidecar
```

Operations guides: [KEY_MANAGEMENT.md](KEY_MANAGEMENT.md), [DISASTER_RECOVERY.md](DISASTER_RECOVERY.md), [MIGRATION.md](MIGRATION.md), [DEPLOYMENT.md](DEPLOYMENT.md).

Background and positioning: [POSITIONING.md](POSITIONING.md), [`PHILOSOPHY/`](PHILOSOPHY/). The constitution this repo implements the authority half of is in [Aliipou/freedom-theory](https://github.com/Aliipou/freedom-theory).

## Contributing

Before changing anything under `authgate-kernel/src/tcb/`, ask: can this live outside the trusted core? If yes, keep it out. Changes to the core need an invariant justification, proof or model-check evidence where it applies, and regression tests. See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

[Apache-2.0](LICENSE), with [NOTICE](NOTICE). Versions published before 2026-10-10 (as *authgate-kernel*) were released under PolyForm Noncommercial 1.0.0 and stay under it. Contributions are accepted under the [Developer Certificate of Origin](CONTRIBUTING.md#developer-certificate-of-origin-dco).

**Name.** Sluicegate was *AuthGate* / *authgate-kernel* until 2026-10-10. The `authgate` package, the `authgate-kernel` crate and wire-format tags keep the old name for now so signed artifacts do not break. They will be renamed in a separate versioned release.
