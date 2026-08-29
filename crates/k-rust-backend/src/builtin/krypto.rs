//! Pure-Rust cryptographic hooks implemented by Kore's fallback evaluator.

use k256::ecdsa::{RecoveryId, Signature, VerifyingKey};
use k256::elliptic_curve::sec1::ToSec1Point;
use num_traits::ToPrimitive;
use ripemd::Ripemd160;
use sha2::{Digest, Sha256, Sha512_256};
use sha3::{Keccak256, Sha3_256};

use super::{BuiltinError, BuiltinResult, bytes, check_interrupted, expect_arity, read_int};
use crate::term::{Sort, Term};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    match hook {
        "KRYPTO.keccak256" | "HASH.keccak256" => hash_hex::<Keccak256>(hook, arguments),
        "KRYPTO.keccak256raw" => hash_raw::<Keccak256>(hook, arguments),
        "KRYPTO.sha256" | "HASH.sha256" => hash_hex::<Sha256>(hook, arguments),
        "KRYPTO.sha3256" | "HASH.sha3_256" => hash_hex::<Sha3_256>(hook, arguments),
        "KRYPTO.sha512_256raw" => hash_raw::<Sha512_256>(hook, arguments),
        "KRYPTO.ripemd160" | "HASH.ripemd160" => hash_hex::<Ripemd160>(hook, arguments),
        "KRYPTO.ecdsaPubKey" => ecdsa_public_key(arguments),
        "KRYPTO.ecdsaRecover" | "SECP256K1.ecdsaRecover" => ecdsa_recover(hook, arguments),
        _ => Ok(BuiltinResult::NotApplicable),
    }
}

fn hash_hex<D>(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError>
where
    D: Digest,
{
    let Some(digest) = digest::<D>(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(encode_hex(&digest))))
}

fn encode_hex(input: &[u8]) -> String {
    let mut encoded = String::with_capacity(input.len() * 2);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in input {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn hash_raw<D>(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError>
where
    D: Digest,
{
    let Some(digest) = digest::<D>(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(bytes::bytes_term(&digest)))
}

fn digest<D>(hook: &str, arguments: &[Term]) -> Result<Option<Vec<u8>>, BuiltinError>
where
    D: Digest,
{
    expect_arity(hook, arguments, 1)?;
    let Some(input) = bytes::read_bytes(&arguments[0]) else {
        return Ok(None);
    };
    let mut digest = D::new();
    for chunk in input.chunks(64 * 1024) {
        check_interrupted()?;
        digest.update(chunk);
    }
    Ok(Some(digest.finalize().to_vec()))
}

fn ecdsa_public_key(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("KRYPTO.ecdsaPubKey", arguments, 1)?;
    let Some(secret) = bytes::read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let encoded = k256::SecretKey::from_slice(&secret)
        .ok()
        .map(|secret| secret.public_key().to_sec1_point(false))
        .and_then(|point| point.as_bytes().get(1..).map(encode_hex))
        .unwrap_or_default();
    Ok(BuiltinResult::Value(string_term(encoded)))
}

fn ecdsa_recover(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 4)?;
    let Some(message_hash) = bytes::read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(v) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(r) = bytes::read_bytes(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(s) = bytes::read_bytes(&arguments[3]) else {
        return Ok(BuiltinResult::NotApplicable);
    };

    let Some(v) = v.to_u8().filter(|v| matches!(v, 27 | 28)) else {
        return Ok(invalid_ecdsa_recovery());
    };
    let Some(recovery_id) = v
        .checked_sub(27)
        .and_then(|id| RecoveryId::try_from(id).ok())
    else {
        return Ok(invalid_ecdsa_recovery());
    };
    let Ok(message_hash): Result<[u8; 32], _> = message_hash.try_into() else {
        return Ok(invalid_ecdsa_recovery());
    };
    let Ok(r): Result<[u8; 32], _> = r.try_into() else {
        return Ok(invalid_ecdsa_recovery());
    };
    let Ok(s): Result<[u8; 32], _> = s.try_into() else {
        return Ok(invalid_ecdsa_recovery());
    };
    let mut signature_bytes = [0_u8; 64];
    signature_bytes[..32].copy_from_slice(&r);
    signature_bytes[32..].copy_from_slice(&s);
    let Ok(signature) = Signature::from_slice(&signature_bytes) else {
        return Ok(invalid_ecdsa_recovery());
    };
    let Ok(key) = VerifyingKey::recover_from_prehash(&message_hash, &signature, recovery_id) else {
        return Ok(invalid_ecdsa_recovery());
    };
    let encoded = key.to_sec1_point(false);
    let Some(coordinates) = encoded.as_bytes().get(1..) else {
        return Ok(invalid_ecdsa_recovery());
    };
    Ok(BuiltinResult::Value(bytes::bytes_term(coordinates)))
}

fn invalid_ecdsa_recovery() -> BuiltinResult {
    BuiltinResult::Value(bytes::bytes_term(&[]))
}

fn string_term(value: impl Into<String>) -> Term {
    Term::domain_value(Sort::simple("SortString"), value.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn string(value: &str) -> BuiltinResult {
        BuiltinResult::Value(string_term(value))
    }

    #[test]
    fn pinned_hash_hooks_match_standard_empty_vectors() {
        let empty = bytes::bytes_term(&[]);
        let cases = [
            (
                "KRYPTO.keccak256",
                "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            ),
            (
                "KRYPTO.sha256",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                "KRYPTO.sha3256",
                "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
            ),
            (
                "KRYPTO.ripemd160",
                "9c1185a5c5e9fc54612808977ee8f548b2258d31",
            ),
        ];

        for (hook, expected) in cases {
            assert_eq!(
                evaluate(hook, std::slice::from_ref(&empty)),
                Ok(string(expected))
            );
        }
    }

    #[test]
    fn raw_hash_hooks_return_bytes() {
        let empty = bytes::bytes_term(&[]);
        let expected = [
            0xc6, 0x72, 0xb8, 0xd1, 0xef, 0x56, 0xed, 0x28, 0xab, 0x87, 0xc3, 0x62, 0x2c, 0x51,
            0x14, 0x06, 0x9b, 0xdd, 0x3a, 0xd7, 0xb8, 0xf9, 0x73, 0x74, 0x98, 0xd0, 0xc0, 0x1e,
            0xce, 0xf0, 0x96, 0x7a,
        ];

        assert_eq!(
            evaluate("KRYPTO.sha512_256raw", &[empty]),
            Ok(BuiltinResult::Value(bytes::bytes_term(&expected)))
        );
    }

    #[test]
    fn derives_the_uncompressed_public_key_without_its_prefix() {
        let mut secret = [0_u8; 32];
        secret[31] = 1;
        let expected = concat!(
            "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
            "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"
        );

        assert_eq!(
            evaluate("KRYPTO.ecdsaPubKey", &[bytes::bytes_term(&secret)]),
            Ok(string(expected))
        );
        assert_eq!(
            evaluate("KRYPTO.ecdsaPubKey", &[bytes::bytes_term(&[0; 32])]),
            Ok(string(""))
        );
    }

    #[test]
    fn recovers_a_public_key_from_a_prehash_signature() {
        use k256::ecdsa::SigningKey;

        let mut secret = [0_u8; 32];
        secret[31] = 1;
        let signing_key = SigningKey::from_slice(&secret).expect("valid secret key");
        let message_hash = Sha256::digest(b"k-rust recovery test");
        let (signature, recovery_id) = signing_key.sign_prehash_recoverable(&message_hash);
        let signature = signature.to_bytes();
        let arguments = [
            bytes::bytes_term(&message_hash),
            super::super::int_term((27 + recovery_id.to_byte()).into()),
            bytes::bytes_term(&signature[..32]),
            bytes::bytes_term(&signature[32..]),
        ];
        let public_key = signing_key.verifying_key().to_sec1_point(false);

        assert_eq!(
            evaluate("KRYPTO.ecdsaRecover", &arguments),
            Ok(BuiltinResult::Value(bytes::bytes_term(
                &public_key.as_bytes()[1..]
            )))
        );
        assert_eq!(
            evaluate("SECP256K1.ecdsaRecover", &arguments),
            Ok(BuiltinResult::Value(bytes::bytes_term(
                &public_key.as_bytes()[1..]
            )))
        );
    }

    #[test]
    fn invalid_concrete_ecdsa_recovery_returns_empty_bytes() {
        use k256::ecdsa::SigningKey;

        let mut secret = [0_u8; 32];
        secret[31] = 1;
        let signing_key = SigningKey::from_slice(&secret).expect("valid secret key");
        let message_hash = Sha256::digest(b"k-rust invalid recovery test");
        let (signature, _) = signing_key.sign_prehash_recoverable(&message_hash);
        let signature = signature.to_bytes();
        let r = signature[..32].to_vec();
        let s = signature[32..].to_vec();
        let expected = Ok(BuiltinResult::Value(bytes::bytes_term(&[])));
        let arguments = |hash: &[u8], v: i32, r: &[u8], s: &[u8]| {
            vec![
                bytes::bytes_term(hash),
                super::super::int_term(v.into()),
                bytes::bytes_term(r),
                bytes::bytes_term(s),
            ]
        };

        let mut long_r = vec![0];
        long_r.extend_from_slice(&r);
        let mut long_s = vec![0];
        long_s.extend_from_slice(&s);
        let zero_scalar = [0_u8; 32];
        let out_of_range_scalar = [0xff_u8; 32];
        let cases = [
            ("negative v", arguments(&message_hash, -1, &r, &s)),
            ("v below range", arguments(&message_hash, 26, &r, &s)),
            ("v above range", arguments(&message_hash, 29, &r, &s)),
            ("large v", arguments(&message_hash, 300, &r, &s)),
            ("short hash", arguments(&message_hash[..31], 27, &r, &s)),
            ("short r", arguments(&message_hash, 27, &r[..31], &s)),
            ("long r", arguments(&message_hash, 27, &long_r, &s)),
            ("short s", arguments(&message_hash, 27, &r, &s[..31])),
            ("long s", arguments(&message_hash, 27, &r, &long_s)),
            ("zero r", arguments(&message_hash, 27, &zero_scalar, &s)),
            (
                "out-of-range s",
                arguments(&message_hash, 27, &r, &out_of_range_scalar),
            ),
        ];

        for (name, arguments) in cases {
            assert_eq!(evaluate("KRYPTO.ecdsaRecover", &arguments), expected, "{name}");
        }
    }
}
