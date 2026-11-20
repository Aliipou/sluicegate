//! T3 red-team: small-order / non-canonical / malleated Ed25519 inputs must
//! be rejected on every signature path (root chain, delegated chain, consent,
//! revocation). Vectors are table-driven over all 8 torsion encodings.

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use rand_core::OsRng;
use sha2::{Digest, Sha256};

use crate::tcb::consent::{verify_consent, ConsentRecord};
use crate::tcb::dag::validate_chain;
use crate::tcb::types::*;

const L_LE: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
];

fn h(s: &str) -> [u8; 32] {
    let v = hex::decode(s).unwrap();
    let mut o = [0u8; 32];
    o.copy_from_slice(&v);
    o
}

/// The 8 canonical torsion-subgroup encodings.
pub(crate) fn torsion() -> Vec<[u8; 32]> {
    let mut id = [0u8; 32];
    id[0] = 1;
    let mut y0 = [0u8; 32];
    let mut y0s = [0u8; 32];
    y0s[31] = 0x80;
    let mut m1 = [0xffu8; 32];
    m1[0] = 0xec;
    m1[31] = 0x7f;
    y0[0] = 0;
    vec![
        id,
        h("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a"),
        y0,
        h("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05"),
        m1,
        h("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85"),
        y0s,
        h("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa"),
    ]
}

/// Non-canonical (y >= p) re-encodings of the torsion points with y in {0,1}
/// (y+p fits in 255 bits), with both sign bits.
pub(crate) fn non_canonical_points() -> Vec<[u8; 32]> {
    let mut out = vec![];
    for (lo, _) in [(0xedu8, 0u8), (0xee, 1)] {
        for sign in [0u8, 0x80] {
            let mut b = [0xffu8; 32];
            b[0] = lo;
            b[31] = 0x7f | sign;
            out.push(b);
        }
    }
    out
}

fn all_points() -> Vec<[u8; 32]> {
    let mut v = torsion();
    v.extend(non_canonical_points());
    v
}

fn s_variants() -> Vec<[u8; 32]> {
    let mut one = [0u8; 32];
    one[0] = 1;
    let mut l_plus_1 = L_LE;
    l_plus_1[0] = l_plus_1[0].wrapping_add(1);
    let mut lm1 = L_LE;
    lm1[0] -= 1;
    vec![[0u8; 32], one, lm1, L_LE, l_plus_1, [0xffu8; 32]]
}

/// (public key bytes, signature bytes) attack corpus: every point as key,
/// every point as R, S in {0, 1, L-1, L, L+1, 2^256-1}.
pub(crate) fn attack_pairs() -> Vec<([u8; 32], [u8; 64])> {
    let mut v = vec![];
    for a in all_points() {
        for r in all_points() {
            for s in s_variants() {
                let mut sig = [0u8; 64];
                sig[..32].copy_from_slice(&r);
                sig[32..].copy_from_slice(&s);
                v.push((a, sig));
            }
        }
    }
    v
}

/// Sanity: the corpus actually bites -- non-strict `verify` accepts at least
/// one pair, strict accepts none (so the tests below are not vacuous).
#[test]
fn corpus_is_nonvacuous_and_strict_rejects_all() {
    let msg = b"anything";
    let mut lax = 0;
    for (a, s) in attack_pairs() {
        if let Ok(vk) = VerifyingKey::from_bytes(&a) {
            let sig = Signature::from_bytes(&s);
            if vk.verify(msg, &sig).is_ok() {
                lax += 1;
            }
            assert!(vk.verify_strict(msg, &sig).is_err(), "strict accepted {a:?} {s:?}");
        }
    }
    assert!(lax > 0, "corpus never beats non-strict verify; vectors are weak");
}

#[test]
fn all_eight_torsion_encodings_are_weak_keys() {
    let t = torsion();
    assert_eq!(t.len(), 8);
    for p in t {
        let vk = VerifyingKey::from_bytes(&p).expect("torsion encoding decompresses");
        assert!(vk.is_weak(), "{p:?}");
    }
}

fn root_proof_with(sig: [u8; 64]) -> CapabilityProof {
    CapabilityProof {
        proof_hash: [1u8; 32],
        subject_id: [1u8; 32],
        resource_hash: [2u8; 32],
        rights: 1,
        expiry: u64::MAX,
        epoch: 1,
        issuer: IssuerRef::Root,
        signature: sig,
        issuer_pubkey: [0u8; 32],
    }
}

#[test]
fn root_chain_rejects_attack_corpus() {
    for (a, s) in attack_pairs() {
        let Ok(vk) = VerifyingKey::from_bytes(&a) else { continue };
        let p = root_proof_with(s);
        assert!(validate_chain(&p, &[p.clone()], &vk, 0).is_err(), "root accepted {a:?} {s:?}");
    }
}

#[test]
fn delegated_chain_rejects_attack_corpus() {
    let root = SigningKey::generate(&mut OsRng);
    for (a, s) in attack_pairs() {
        let mut p = root_proof_with(s);
        p.issuer = IssuerRef::Delegated { parent_hash: [8u8; 32] };
        p.issuer_pubkey = a;
        // Parent absent: the only acceptable Ok would be a bypass; the error
        // must never be success, and a signature acceptance would surface as
        // "parent proof not found in bundle" (checked below).
        let r = validate_chain(&p, &[], &root.verifying_key(), 0);
        assert!(r.is_err());
        assert_ne!(r, Err("parent proof not found in bundle"), "delegated sig accepted {a:?} {s:?}");
    }
}

#[test]
fn consent_rejects_attack_corpus() {
    let grantee = [5u8; 32];
    let res = [6u8; 32];
    for (a, s) in attack_pairs() {
        let mut c = ConsentRecord {
            grantor: Sha256::digest(a).into(),
            grantee,
            resource_hash: res,
            rights: 1,
            expires_at: 0,
            revocable: false,
            nonce: [3u8; 16],
            consent_id: [0u8; 32],
            signature: s,
            grantor_pubkey: a,
        };
        c.consent_id = c.compute_consent_id();
        assert!(verify_consent(&c, grantee, res, 1, 10).is_err(), "consent accepted {a:?} {s:?}");
    }
}

#[test]
fn malleated_and_tampered_valid_signatures_rejected() {
    let sk = SigningKey::generate(&mut OsRng);
    let vk = sk.verifying_key();
    let msg = b"m";
    let sig = sk.sign(msg).to_bytes();
    assert!(vk.verify_strict(msg, &Signature::from_bytes(&sig)).is_ok());
    // S + L
    let mut m = sig;
    let mut carry = 0u16;
    for i in 0..32 {
        let v = sig[32 + i] as u16 + L_LE[i] as u16 + carry;
        m[32 + i] = v as u8;
        carry = v >> 8;
    }
    assert!(vk.verify_strict(msg, &Signature::from_bytes(&m)).is_err());
    // R replaced by each torsion point / non-canonical point
    for r in all_points() {
        let mut t = sig;
        t[..32].copy_from_slice(&r);
        assert!(vk.verify_strict(msg, &Signature::from_bytes(&t)).is_err());
    }
    // S = 0 and S = L
    for s in [[0u8; 32], L_LE] {
        let mut t = sig;
        t[32..].copy_from_slice(&s);
        assert!(vk.verify_strict(msg, &Signature::from_bytes(&t)).is_err());
    }
    // single-bit flips in every byte
    for i in 0..64 {
        let mut t = sig;
        t[i] ^= 1;
        assert!(vk.verify_strict(msg, &Signature::from_bytes(&t)).is_err(), "bitflip {i}");
    }
}
