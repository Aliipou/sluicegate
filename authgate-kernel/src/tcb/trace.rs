//! T8: JSON-lines trace emitter for TLA+ trace validation (feature `trace`).
//!
//! NOT part of the verification logic: it only observes `engine::verify` inputs
//! and outputs. Compiled only with `--features trace`; writes only when the env
//! var `AUTHGATE_TRACE_DIR` is set.
//!
//! # Mapping to formal/AuthGateV3.tla (also see formal/TraceAuthGateV3.tla)
//!
//! One trace file = one per-thread (= per cargo test) run of consecutive
//! `verify` calls that are consistent with AuthGateV3's cumulative state.
//! Events (one JSON object per line; line 1 is a `header`):
//!
//! | Rust observation                                 | TLA action        |
//! |--------------------------------------------------|-------------------|
//! | call with `min_epoch` > previous `min_epoch`     | `AdvanceEpoch(e)` |
//! | root-signed `RevocationProof` target not yet seen | `Revoke(h)`       |
//! | every `verify` call                              | `ExecuteVerify`   |
//!
//! State variables: `global_epoch` := `min_epoch` of the call (mapped);
//! `revoked_set` := targets of root-signature-valid revocation proofs in the
//! call (mapped); `audit_log` := (action, decision) pairs (mapped, Rust
//! `Decision` compared with the TLA `Verify` result); `session_rights` is NOT
//! observed from Rust (SequenceContext is not wired in): TLA derives it from
//! its own Permit decisions, so it is not validated against Rust.
//!
//! Abstractions (documented, lossy): 32-byte values are interned per trace as
//! symbolic names (a#, r#, h#, pk#); `Hash(pk)` is the real SHA-256 relation
//! interned the same way; `sig_valid` is the real ed25519 verify_strict result
//! (Root: against `root_key`, Delegated: against `issuer_pubkey`);
//! `binding_valid` is the real `verify_binding()`; `u64` values (expiry, epoch,
//! timestamp, now, min_epoch) are clamped to 2^30 (comparisons preserved except
//! ties among values > 2^30). Calls with `requires_consent` or rights bits >= 8
//! are not representable in AuthGateV3 and are SKIPPED (logged to skipped.jsonl).
//! A new trace file is started when the call is inconsistent with cumulative
//! TLA state (lower `min_epoch`, or revocation set not a superset of previous).

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::io::Write as _;

use ed25519_dalek::{Signature, VerifyingKey};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use crate::tcb::types::{CanonicalAction, CapabilityProof, Decision, IssuerRef, Rights};

const CLAMP: u64 = 1 << 30;
const MAX_CHAIN_DEPTH: u64 = 16;
const RIGHT_NAMES: [&str; 8] = [
    "READ", "WRITE", "DELEGATE", "EXECUTE", "SPAWN", "NETWORK", "MODEL_INVOKE", "POLICY_MODIFY",
];

#[derive(Default)]
struct Interner(Vec<[u8; 32]>);

impl Interner {
    fn id(&mut self, v: &[u8; 32]) -> usize {
        if let Some(i) = self.0.iter().position(|x| x == v) {
            return i;
        }
        self.0.push(*v);
        self.0.len() - 1
    }
}

#[derive(Default)]
struct Trace {
    n: u32,
    epoch: u64,
    revoked: BTreeSet<[u8; 32]>,
    actors: Interner,
    resources: Interner,
    hashes: Interner,
    pks: Interner,
    root: Option<usize>,
    events: Vec<Value>,
    max_epoch: u64,
}

thread_local! {
    static TRACE: RefCell<Trace> = RefCell::new(Trace::default());
}

fn rights_json(r: Rights) -> Value {
    Value::Array(
        RIGHT_NAMES
            .iter()
            .enumerate()
            .filter(|(i, _)| r & (1u64 << i) != 0)
            .map(|(_, n)| json!(n))
            .collect(),
    )
}

fn sig_ok(cap: &CapabilityProof, root_key: &VerifyingKey) -> bool {
    let sig = Signature::from_bytes(&cap.signature);
    let msg = cap.signing_message();
    match &cap.issuer {
        IssuerRef::Root => root_key.verify_strict(&msg, &sig).is_ok(),
        IssuerRef::Delegated { .. } => VerifyingKey::from_bytes(&cap.issuer_pubkey)
            .and_then(|k| k.verify_strict(&msg, &sig))
            .is_ok(),
    }
}

fn cl(x: u64) -> u64 {
    x.min(CLAMP)
}

fn skip(reason: &str) {
    if let Ok(dir) = std::env::var("AUTHGATE_TRACE_DIR") {
        let _ = std::fs::create_dir_all(&dir);
        let name = std::thread::current().name().unwrap_or("unnamed").to_string();
        if let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("{dir}/skipped.jsonl"))
        {
            let _ = writeln!(f, "{}", json!({"thread": name, "reason": reason}));
        }
    }
}

pub(crate) fn record(action: &CanonicalAction, root_key: &VerifyingKey, now: u64, decision: &Decision) {
    let Ok(dir) = std::env::var("AUTHGATE_TRACE_DIR") else { return };
    if action.requires_consent {
        return skip("requires_consent: consent layer not modeled in AuthGateV3");
    }
    let wide = |r: Rights| r >> 8 != 0;
    if wide(action.required_rights) || action.capability_proofs.iter().any(|c| wide(c.rights)) {
        return skip("rights bit >= 8 not in AuthGateV3 AllRights");
    }
    let root_bytes = root_key.to_bytes();
    // Valid (root-signed) revocation targets of this call.
    let call_rev: BTreeSet<[u8; 32]> = action
        .revocation_proofs
        .iter()
        .filter(|r| {
            let sig = Signature::from_bytes(&r.signature);
            root_key.verify_strict(&r.signing_message(), &sig).is_ok()
        })
        .map(|r| r.target_proof_hash)
        .collect();
    let me = cl(action.min_epoch);

    TRACE.with(|t| {
        let mut t = t.borrow_mut();
        if !t.events.is_empty() && (me < t.epoch || !t.revoked.is_subset(&call_rev)) {
            let n = t.n + 1;
            *t = Trace { n, ..Trace::default() };
        }
        if t.root.is_none() {
            let r = t.pks.id(&root_bytes);
            t.root = Some(r);
        }
        if me > t.epoch {
            t.events.push(json!({"kind": "advance", "epoch": me}));
            t.epoch = me;
            t.max_epoch = t.max_epoch.max(me);
        }
        let new_rev: Vec<[u8; 32]> = call_rev.difference(&t.revoked).copied().collect();
        for h in &new_rev {
            let hid = t.hashes.id(h);
            t.events.push(json!({"kind": "revoke", "hash": format!("h{hid}")}));
        }
        t.revoked = call_rev.clone();

        let actor = t.actors.id(&action.actor_id);
        let res = t.resources.id(&action.resource_hash);
        let mut caps = Vec::new();
        for c in &action.capability_proofs {
            let ph = t.hashes.id(&c.proof_hash);
            let sub = t.actors.id(&c.subject_id);
            let cr = t.resources.id(&c.resource_hash);
            let pk = t.pks.id(&c.issuer_pubkey);
            let issuer = match &c.issuer {
                IssuerRef::Root => json!({"type": "Root"}),
                IssuerRef::Delegated { parent_hash } => {
                    let p = t.hashes.id(parent_hash);
                    json!({"type": "Delegated", "parent_hash": format!("h{p}")})
                }
            };
            caps.push(json!({
                "proof_hash": format!("h{ph}"), "subject_id": format!("a{sub}"),
                "resource_hash": format!("r{cr}"), "rights": rights_json(c.rights),
                "expiry": cl(c.expiry), "epoch": cl(c.epoch), "issuer": issuer,
                "issuer_pubkey": format!("pk{pk}"), "sig_valid": sig_ok(c, root_key),
            }));
        }
        let d = if matches!(decision, Decision::Permit) { "Permit" } else { "Deny" };
        t.events.push(json!({
            "kind": "verify", "now": cl(now), "decision": d,
            "action": {
                "actor_id": format!("a{actor}"), "resource_hash": format!("r{res}"),
                "required_rights": rights_json(action.required_rights),
                "min_epoch": me, "timestamp": cl(action.timestamp),
                "cap_bundle": caps, "binding_valid": action.verify_binding(),
            }
        }));

        // Header (recomputed each time; Hash(pk) = SHA-256(pk) interned as actor).
        let mut hash_map = serde_json::Map::new();
        for i in 0..t.pks.0.len() {
            let pkb = t.pks.0.get(i).copied().unwrap_or([0u8; 32]);
            let img: [u8; 32] = Sha256::digest(pkb).into();
            let a = t.actors.id(&img);
            hash_map.insert(format!("pk{i}"), json!(format!("a{a}")));
        }
        let names = |p: &str, n: usize| -> Vec<String> { (0..n).map(|i| format!("{p}{i}")).collect() };
        let header = json!({
            "kind": "header",
            "actors": names("a", t.actors.0.len()), "resources": names("r", t.resources.0.len()),
            "proof_hashes": names("h", t.hashes.0.len()), "pubkeys": names("pk", t.pks.0.len()),
            "root_key": format!("pk{}", t.root.unwrap_or(0)), "hash": Value::Object(hash_map),
            "max_chain_depth": MAX_CHAIN_DEPTH, "max_epoch": t.max_epoch.max(1),
        });
        let mut out = header.to_string();
        out.push('\n');
        for e in &t.events {
            out.push_str(&e.to_string());
            out.push('\n');
        }
        let th = std::thread::current();
        let name: String = th
            .name()
            .unwrap_or("unnamed")
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '-' })
            .collect();
        let _ = std::fs::create_dir_all(&dir);
        if let Err(e) = std::fs::write(format!("{dir}/{name}__{}.jsonl", t.n), out) {
            eprintln!("trace write failed: {e}");
        }
    });
}
