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
        return Ok(failed_recovery());
    };
    let Some(recovery_id) = v
        .checked_sub(27)
        .and_then(|id| RecoveryId::try_from(id).ok())
    else {
        return Ok(failed_recovery());
    };
    let Ok(message_hash): Result<[u8; 32], _> = message_hash.try_into() else {
        return Ok(failed_recovery());
    };
    let Ok(r): Result<[u8; 32], _> = r.try_into() else {
        return Ok(failed_recovery());
    };
    let Ok(s): Result<[u8; 32], _> = s.try_into() else {
        return Ok(failed_recovery());
    };
    let mut signature_bytes = [0_u8; 64];
    signature_bytes[..32].copy_from_slice(&r);
    signature_bytes[32..].copy_from_slice(&s);
    let Ok(signature) = Signature::from_slice(&signature_bytes) else {
        return Ok(failed_recovery());
    };
    let Ok(key) = VerifyingKey::recover_from_prehash(&message_hash, &signature, recovery_id) else {
        return Ok(failed_recovery());
    };
    let encoded = key.to_sec1_point(false);
    let Some(coordinates) = encoded.as_bytes().get(1..) else {
        return Ok(failed_recovery());
    };
    Ok(BuiltinResult::Value(bytes::bytes_term(coordinates)))
}

fn failed_recovery() -> BuiltinResult {
    BuiltinResult::Value(bytes::bytes_term(&[]))
}

fn string_term(value: impl Into<String>) -> Term {
    Term::domain_value(Sort::simple("SortString"), value.into())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::{
        cancellation::CancellationToken,
        term::{Symbol, Variable},
    };

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
    fn hash_hooks_match_standard_nonempty_vectors() {
        let abc = bytes::bytes_term(b"abc");
        let cases = [
            (
                "KRYPTO.keccak256",
                "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
            ),
            (
                "KRYPTO.sha256",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                "KRYPTO.sha3256",
                "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
            ),
            (
                "KRYPTO.ripemd160",
                "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc",
            ),
        ];

        for (hook, expected) in cases {
            assert_eq!(
                evaluate(hook, std::slice::from_ref(&abc)),
                Ok(string(expected))
            );
        }
    }

    #[test]
    fn keccak256raw_returns_the_raw_digest_bytes() {
        let cases: [(&[u8], [u8; 32]); 2] = [
            (
                b"",
                [
                    0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc,
                    0xc7, 0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa,
                    0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70,
                ],
            ),
            (
                b"abc",
                [
                    0x4e, 0x03, 0x65, 0x7a, 0xea, 0x45, 0xa9, 0x4f, 0xc7, 0xd4, 0x7b, 0xa8, 0x26,
                    0xc8, 0xd6, 0x67, 0xc0, 0xd1, 0xe6, 0xe3, 0x3a, 0x64, 0xa0, 0x36, 0xec, 0x44,
                    0xf5, 0x8f, 0xa1, 0x2d, 0x6c, 0x45,
                ],
            ),
        ];

        for (input, expected) in cases {
            assert_eq!(
                evaluate("KRYPTO.keccak256raw", &[bytes::bytes_term(input)]),
                Ok(BuiltinResult::Value(bytes::bytes_term(&expected)))
            );
        }
    }

    #[test]
    fn hash_namespace_aliases_agree_with_their_krypto_spelling() {
        let abc = bytes::bytes_term(b"abc");
        for (alias, canonical) in [
            ("HASH.keccak256", "KRYPTO.keccak256"),
            ("HASH.sha256", "KRYPTO.sha256"),
            ("HASH.sha3_256", "KRYPTO.sha3256"),
            ("HASH.ripemd160", "KRYPTO.ripemd160"),
        ] {
            assert_eq!(
                evaluate(alias, std::slice::from_ref(&abc)),
                evaluate(canonical, std::slice::from_ref(&abc)),
                "{alias}"
            );
        }
    }

    #[test]
    fn symbolic_arguments_stay_not_applicable_for_every_hook() {
        let symbolic_bytes = || Term::variable(Variable::new("Bytes", Sort::simple("SortBytes")));
        for hook in [
            "KRYPTO.keccak256",
            "HASH.keccak256",
            "KRYPTO.keccak256raw",
            "KRYPTO.sha256",
            "HASH.sha256",
            "KRYPTO.sha3256",
            "HASH.sha3_256",
            "KRYPTO.sha512_256raw",
            "KRYPTO.ripemd160",
            "HASH.ripemd160",
            "KRYPTO.ecdsaPubKey",
        ] {
            assert_eq!(
                evaluate(hook, &[symbolic_bytes()]),
                Ok(BuiltinResult::NotApplicable)
            );
        }

        let concrete_bytes = bytes::bytes_term(&[1; 32]);
        let concrete_v = super::super::int_term(27.into());
        let symbolic_int = Term::variable(Variable::new("V", Sort::simple("SortInt")));
        for hook in ["KRYPTO.ecdsaRecover", "SECP256K1.ecdsaRecover"] {
            for position in 0..4 {
                let mut arguments = [
                    concrete_bytes.clone(),
                    concrete_v.clone(),
                    concrete_bytes.clone(),
                    concrete_bytes.clone(),
                ];
                arguments[position] = if position == 1 {
                    symbolic_int.clone()
                } else {
                    symbolic_bytes()
                };
                assert_eq!(
                    evaluate(hook, &arguments),
                    Ok(BuiltinResult::NotApplicable),
                    "{hook}, symbolic position {position}"
                );
            }
        }
    }

    #[test]
    fn wrong_sort_and_non_byte_domain_values_are_not_applicable() {
        let sort_bytes = Sort::simple("SortBytes");
        let non_domain = Term::application(
            Arc::new(Symbol::constructor("bytes", vec![], sort_bytes.clone())),
            vec![],
            vec![],
        );
        let cases = [
            Term::domain_value(Sort::simple("SortString"), "abc"),
            Term::domain_value(sort_bytes, "\u{100}"),
            non_domain,
        ];

        for argument in cases {
            assert_eq!(
                evaluate("KRYPTO.keccak256", &[argument]),
                Ok(BuiltinResult::NotApplicable)
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
    fn invalid_concrete_secrets_yield_the_empty_public_key() {
        let curve_order = [
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c,
            0xd0, 0x36, 0x41, 0x41,
        ];
        for (name, secret) in [
            ("empty", vec![]),
            ("zero scalar", vec![0; 32]),
            ("33 bytes", vec![1; 33]),
            ("curve order", curve_order.to_vec()),
        ] {
            assert_eq!(
                evaluate("KRYPTO.ecdsaPubKey", &[bytes::bytes_term(&secret)]),
                Ok(string("")),
                "{name}"
            );
        }
    }

    #[test]
    fn digests_are_interruptible() {
        let token = CancellationToken::new();
        token.cancel();

        assert_eq!(
            token.scope(|| evaluate("KRYPTO.keccak256", &[bytes::bytes_term(b"abc")])),
            Err(BuiltinError::Interrupted)
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
    fn invalid_concrete_recoveries_return_empty_bytes() {
        let hash = vec![1_u8; 32];
        let scalar = vec![1_u8; 32];
        let curve_order = vec![
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c,
            0xd0, 0x36, 0x41, 0x41,
        ];
        let cases = vec![
            (
                "negative v",
                hash.clone(),
                (-1).into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "v = 26",
                hash.clone(),
                26.into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "v = 29",
                hash.clone(),
                29.into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "v = 30",
                hash.clone(),
                30.into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "v >= 256",
                hash.clone(),
                256.into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "31-byte hash",
                vec![1; 31],
                27.into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "33-byte hash",
                vec![1; 33],
                27.into(),
                scalar.clone(),
                scalar.clone(),
            ),
            (
                "31-byte r",
                hash.clone(),
                27.into(),
                vec![1; 31],
                scalar.clone(),
            ),
            (
                "33-byte zero-prefixed r",
                hash.clone(),
                27.into(),
                [vec![0], scalar.clone()].concat(),
                scalar.clone(),
            ),
            (
                "31-byte s",
                hash.clone(),
                27.into(),
                scalar.clone(),
                vec![1; 31],
            ),
            (
                "33-byte s",
                hash.clone(),
                27.into(),
                scalar.clone(),
                vec![1; 33],
            ),
            (
                "zero r",
                hash.clone(),
                27.into(),
                vec![0; 32],
                scalar.clone(),
            ),
            ("s at curve order", hash, 27.into(), scalar, curve_order),
        ];
        let empty = BuiltinResult::Value(bytes::bytes_term(&[]));

        for (name, hash, v, r, s) in cases {
            let arguments = [
                bytes::bytes_term(&hash),
                super::super::int_term(v),
                bytes::bytes_term(&r),
                bytes::bytes_term(&s),
            ];
            assert_eq!(
                evaluate("KRYPTO.ecdsaRecover", &arguments),
                Ok(empty.clone()),
                "{name}"
            );
        }

        let symbolic = [
            bytes::bytes_term(&[1; 32]),
            Term::variable(crate::term::Variable::new("V", Sort::simple("SortInt"))),
            bytes::bytes_term(&[1; 32]),
            bytes::bytes_term(&[1; 32]),
        ];
        assert_eq!(
            evaluate("KRYPTO.ecdsaRecover", &symbolic),
            Ok(BuiltinResult::NotApplicable)
        );
    }
}
