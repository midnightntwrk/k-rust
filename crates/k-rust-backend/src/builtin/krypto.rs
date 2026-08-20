//! Pure-Rust cryptographic hooks implemented by Kore's fallback evaluator.

use ripemd::Ripemd160;
use sha2::{Digest, Sha256, Sha512_256};
use sha3::{Keccak256, Sha3_256};

use super::{BuiltinError, BuiltinResult, bytes, expect_arity};
use crate::term::{Sort, Term};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    match hook {
        "KRYPTO.keccak256" | "HASH.keccak256" => hash_hex::<Keccak256>(hook, arguments),
        "KRYPTO.keccak256raw" => hash_raw::<Keccak256>(hook, arguments),
        "KRYPTO.sha256" | "HASH.sha256" => hash_hex::<Sha256>(hook, arguments),
        "KRYPTO.sha3256" | "HASH.sha3_256" => hash_hex::<Sha3_256>(hook, arguments),
        "KRYPTO.sha512_256raw" => hash_raw::<Sha512_256>(hook, arguments),
        "KRYPTO.ripemd160" | "HASH.ripemd160" => hash_hex::<Ripemd160>(hook, arguments),
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
    let mut encoded = String::with_capacity(digest.len() * 2);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    Ok(BuiltinResult::Value(Term::domain_value(
        Sort::simple("SortString"),
        encoded,
    )))
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
    Ok(Some(D::digest(input).to_vec()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn string(value: &str) -> BuiltinResult {
        BuiltinResult::Value(Term::domain_value(Sort::simple("SortString"), value))
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
}
