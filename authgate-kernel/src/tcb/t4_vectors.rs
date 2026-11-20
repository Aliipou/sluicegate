//! T4: RFC 8032 section 7.1 Ed25519 test vectors, run with whichever curve25519-dalek backend
//! is selected (`.cargo/config.toml` selects `fiat`). Checks signing AND `verify_strict`.
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

fn h(s: &str) -> Vec<u8> {
    hex::decode(s).unwrap()
}

fn check(sk_hex: &str, pk_hex: &str, msg_hex: &str, sig_hex: &str) {
    let sk_bytes: [u8; 32] = h(sk_hex).try_into().unwrap();
    let sk = SigningKey::from_bytes(&sk_bytes);
    let pk_bytes: [u8; 32] = h(pk_hex).try_into().unwrap();
    assert_eq!(sk.verifying_key().to_bytes(), pk_bytes, "derived public key");
    let msg = h(msg_hex);
    let sig_bytes: [u8; 64] = h(sig_hex).try_into().unwrap();
    assert_eq!(sk.sign(&msg).to_bytes(), sig_bytes, "deterministic signature");
    let vk = VerifyingKey::from_bytes(&pk_bytes).unwrap();
    vk.verify_strict(&msg, &Signature::from_bytes(&sig_bytes)).expect("verify_strict");
}

#[test]
fn rfc8032_test1_empty_message() {
    check(
        "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        "",
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    );
}

#[test]
fn rfc8032_test2_one_byte() {
    check(
        "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
        "72",
        "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
    );
}
