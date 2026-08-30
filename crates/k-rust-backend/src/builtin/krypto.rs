//! Pure-Rust cryptographic hooks implemented by Kore's fallback evaluator.

use std::sync::Arc;

use k256::ecdsa::{RecoveryId, Signature, VerifyingKey};
use k256::elliptic_curve::sec1::ToSec1Point;
use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;
use ripemd::Ripemd160;
use sha2::{Digest, Sha256, Sha512_256};
use sha3::{Keccak256, Sha3_256};
use substrate_bn::{AffineG1, AffineG2, Fq, Fq2, Fr, G1, G2, Group, Gt, pairing_batch};

use super::{
    BuiltinError, BuiltinResult, bool_term, bytes, check_interrupted, expect_arity, read_int,
};
use crate::term::{Sort, Symbol, Term, TermKind};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    match hook {
        "KRYPTO.keccak256" | "HASH.keccak256" => hash_hex::<Keccak256>(hook, arguments),
        "KRYPTO.keccak256raw" => hash_raw::<Keccak256>(hook, arguments),
        "KRYPTO.sha256" | "HASH.sha256" => hash_hex::<Sha256>(hook, arguments),
        "KRYPTO.sha256raw" => hash_raw::<Sha256>(hook, arguments),
        "KRYPTO.sha3256" | "HASH.sha3_256" => hash_hex::<Sha3_256>(hook, arguments),
        "KRYPTO.sha512_256raw" => hash_raw::<Sha512_256>(hook, arguments),
        "KRYPTO.ripemd160" | "HASH.ripemd160" => hash_hex::<Ripemd160>(hook, arguments),
        "KRYPTO.ripemd160raw" => hash_raw::<Ripemd160>(hook, arguments),
        "KRYPTO.ecdsaPubKey" => ecdsa_public_key(arguments),
        "KRYPTO.ecdsaRecover" | "SECP256K1.ecdsaRecover" => ecdsa_recover(hook, arguments),
        "KRYPTO.bn128valid" => bn128_valid(hook, arguments),
        "KRYPTO.bn128g2valid" => bn128_g2_valid(hook, arguments),
        "KRYPTO.bn128add" => bn128_add(hook, arguments),
        "KRYPTO.bn128mul" => bn128_mul(hook, arguments),
        "KRYPTO.bn128ate" => bn128_ate(hook, arguments),
        _ => Ok(BuiltinResult::NotApplicable),
    }
}

enum Reading<T> {
    Concrete(T),
    Invalid,
    Symbolic,
}

struct ConcreteG1 {
    symbol: Arc<Symbol>,
    sort_arguments: Vec<Sort>,
    x: BigInt,
    y: BigInt,
}

struct ConcreteG2 {
    x_c0: BigInt,
    x_c1: BigInt,
    y_c0: BigInt,
    y_c1: BigInt,
}

fn without_injections(mut term: &Term) -> &Term {
    while let TermKind::Injection { term: inner, .. } = term.kind() {
        term = inner;
    }
    term
}

fn unreadable<T>(term: &Term) -> Reading<T> {
    if term.attributes().variables.is_empty() {
        Reading::Invalid
    } else {
        Reading::Symbolic
    }
}

fn concrete_g1(term: &Term) -> Reading<ConcreteG1> {
    let term = without_injections(term);
    let TermKind::Application {
        symbol,
        sort_arguments,
        arguments,
    } = term.kind()
    else {
        return unreadable(term);
    };
    let [x, y] = arguments.as_slice() else {
        return unreadable(term);
    };
    let Some(x) = read_int(x) else {
        return unreadable(term);
    };
    let Some(y) = read_int(y) else {
        return unreadable(term);
    };
    Reading::Concrete(ConcreteG1 {
        symbol: symbol.clone(),
        sort_arguments: sort_arguments.clone(),
        x,
        y,
    })
}

fn concrete_g2(term: &Term) -> Reading<ConcreteG2> {
    let term = without_injections(term);
    let TermKind::Application { arguments, .. } = term.kind() else {
        return unreadable(term);
    };
    let [x_c0, x_c1, y_c0, y_c1] = arguments.as_slice() else {
        return unreadable(term);
    };
    let Some(x_c0) = read_int(x_c0) else {
        return unreadable(term);
    };
    let Some(x_c1) = read_int(x_c1) else {
        return unreadable(term);
    };
    let Some(y_c0) = read_int(y_c0) else {
        return unreadable(term);
    };
    let Some(y_c1) = read_int(y_c1) else {
        return unreadable(term);
    };
    Reading::Concrete(ConcreteG2 {
        x_c0,
        x_c1,
        y_c0,
        y_c1,
    })
}

fn coordinate_bytes(value: &BigInt) -> Option<[u8; 32]> {
    let (sign, significant) = value.to_bytes_be();
    if sign == Sign::Minus || significant.len() > 32 {
        return None;
    }
    let mut bytes = [0_u8; 32];
    bytes[32 - significant.len()..].copy_from_slice(&significant);
    Some(bytes)
}

fn g1_value(point: &ConcreteG1) -> Option<G1> {
    let x = Fq::from_slice(&coordinate_bytes(&point.x)?).ok()?;
    let y = Fq::from_slice(&coordinate_bytes(&point.y)?).ok()?;
    if x.is_zero() && y.is_zero() {
        Some(G1::zero())
    } else {
        AffineG1::new(x, y).ok().map(Into::into)
    }
}

fn g2_value(point: &ConcreteG2) -> Option<G2> {
    let x_c0 = Fq::from_slice(&coordinate_bytes(&point.x_c0)?).ok()?;
    let x_c1 = Fq::from_slice(&coordinate_bytes(&point.x_c1)?).ok()?;
    let y_c0 = Fq::from_slice(&coordinate_bytes(&point.y_c0)?).ok()?;
    let y_c1 = Fq::from_slice(&coordinate_bytes(&point.y_c1)?).ok()?;
    if x_c0.is_zero() && x_c1.is_zero() && y_c0.is_zero() && y_c1.is_zero() {
        Some(G2::zero())
    } else {
        AffineG2::new(Fq2::new(x_c0, x_c1), Fq2::new(y_c0, y_c1))
            .ok()
            .map(Into::into)
    }
}

fn bn128_valid(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 1)?;
    Ok(match concrete_g1(&arguments[0]) {
        Reading::Concrete(point) => BuiltinResult::Value(bool_term(g1_value(&point).is_some())),
        Reading::Invalid => BuiltinResult::Value(bool_term(false)),
        Reading::Symbolic => BuiltinResult::NotApplicable,
    })
}

fn bn128_g2_valid(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 1)?;
    Ok(match concrete_g2(&arguments[0]) {
        Reading::Concrete(point) => BuiltinResult::Value(bool_term(g2_value(&point).is_some())),
        Reading::Invalid => BuiltinResult::Value(bool_term(false)),
        Reading::Symbolic => BuiltinResult::NotApplicable,
    })
}

fn bn128_add(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let left = match concrete_g1(&arguments[0]) {
        Reading::Concrete(point) => point,
        Reading::Invalid => return Ok(BuiltinResult::Bottom),
        Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
    };
    let right = match concrete_g1(&arguments[1]) {
        Reading::Concrete(point) => point,
        Reading::Invalid => return Ok(BuiltinResult::Bottom),
        Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
    };
    if left.symbol.name != right.symbol.name || left.sort_arguments != right.sort_arguments {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(sum) = g1_value(&left)
        .zip(g1_value(&right))
        .map(|(left, right)| left + right)
    else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(concrete_g1_term(&left, sum)))
}

fn bn128_mul(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let point = match concrete_g1(&arguments[0]) {
        Reading::Concrete(point) => point,
        Reading::Invalid => return Ok(BuiltinResult::Bottom),
        Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
    };
    let Some(scalar) = read_int(&arguments[1]) else {
        return Ok(if arguments[1].attributes().variables.is_empty() {
            BuiltinResult::Bottom
        } else {
            BuiltinResult::NotApplicable
        });
    };
    let Some((value, scalar)) = g1_value(&point)
        .zip(coordinate_bytes(&scalar).and_then(|bytes| Fr::from_slice(&bytes).ok()))
    else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(concrete_g1_term(
        &point,
        value * scalar,
    )))
}

fn concrete_g1_term(template: &ConcreteG1, value: G1) -> Term {
    let (x, y) = if let Some(affine) = AffineG1::from_jacobian(value) {
        let mut x = [0_u8; 32];
        let mut y = [0_u8; 32];
        affine
            .x()
            .to_big_endian(&mut x)
            .expect("a fixed-width Fq coordinate encodes into 32 bytes");
        affine
            .y()
            .to_big_endian(&mut y)
            .expect("a fixed-width Fq coordinate encodes into 32 bytes");
        (
            BigInt::from_bytes_be(Sign::Plus, &x),
            BigInt::from_bytes_be(Sign::Plus, &y),
        )
    } else {
        (BigInt::from(0), BigInt::from(0))
    };
    Term::application(
        template.symbol.clone(),
        template.sort_arguments.clone(),
        vec![super::int_term(x), super::int_term(y)],
    )
}

fn complete_list(term: &Term) -> Reading<&[Term]> {
    match term.kind() {
        TermKind::List {
            heads, rest: None, ..
        } => Reading::Concrete(heads),
        TermKind::List { rest: Some(_), .. } => Reading::Symbolic,
        _ => unreadable(term),
    }
}

fn bn128_ate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let g1_terms = match complete_list(&arguments[0]) {
        Reading::Concrete(terms) => terms,
        Reading::Invalid => return Ok(BuiltinResult::Bottom),
        Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
    };
    let g2_terms = match complete_list(&arguments[1]) {
        Reading::Concrete(terms) => terms,
        Reading::Invalid => return Ok(BuiltinResult::Bottom),
        Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
    };
    if g1_terms.len() != g2_terms.len() {
        return Ok(BuiltinResult::Bottom);
    }

    check_interrupted()?;
    let mut pairs = Vec::with_capacity(g1_terms.len());
    for (g1_term, g2_term) in g1_terms.iter().zip(g2_terms) {
        check_interrupted()?;
        let g1 = match concrete_g1(g1_term) {
            Reading::Concrete(point) => g1_value(&point),
            Reading::Invalid => return Ok(BuiltinResult::Bottom),
            Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
        };
        let g2 = match concrete_g2(g2_term) {
            Reading::Concrete(point) => g2_value(&point),
            Reading::Invalid => return Ok(BuiltinResult::Bottom),
            Reading::Symbolic => return Ok(BuiltinResult::NotApplicable),
        };
        let Some(pair) = g1.zip(g2) else {
            return Ok(BuiltinResult::Bottom);
        };
        pairs.push(pair);
    }

    Ok(BuiltinResult::Value(bool_term(
        pairing_batch(&pairs) == Gt::one(),
    )))
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
    let secret = if secret.len() == 32 {
        k256::SecretKey::from_slice(&secret).ok()
    } else {
        None
    };
    let encoded = secret
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

    use num_bigint::BigInt;

    use super::*;
    use crate::{
        cancellation::CancellationToken,
        term::{CollectionSymbols, ListDefinition, Symbol, Variable},
    };

    fn string(value: &str) -> BuiltinResult {
        BuiltinResult::Value(string_term(value))
    }

    fn decimal(value: &str) -> BigInt {
        BigInt::parse_bytes(value.as_bytes(), 10).expect("decimal curve fixture")
    }

    fn hex_coordinate(value: &str) -> BigInt {
        BigInt::parse_bytes(value.as_bytes(), 16).expect("hexadecimal curve fixture")
    }

    fn g1_symbol() -> Arc<Symbol> {
        Arc::new(Symbol::constructor(
            "Lblg1Point",
            vec![Sort::simple("SortInt"), Sort::simple("SortInt")],
            Sort::simple("SortG1Point"),
        ))
    }

    fn g1_point(symbol: &Arc<Symbol>, x: BigInt, y: BigInt) -> Term {
        Term::application(
            symbol.clone(),
            Vec::new(),
            vec![super::super::int_term(x), super::super::int_term(y)],
        )
    }

    fn g2_symbol() -> Arc<Symbol> {
        Arc::new(Symbol::constructor(
            "Lblg2Point",
            vec![Sort::simple("SortInt"); 4],
            Sort::simple("SortG2Point"),
        ))
    }

    fn g2_point(symbol: &Arc<Symbol>, coordinates: [BigInt; 4]) -> Term {
        Term::application(
            symbol.clone(),
            Vec::new(),
            coordinates
                .into_iter()
                .map(super::super::int_term)
                .collect(),
        )
    }

    fn g2_generator(symbol: &Arc<Symbol>) -> Term {
        g2_point(
            symbol,
            [
                decimal(
                    "10857046999023057135944570762232829481370756359578518086990519993285655852781",
                ),
                decimal(
                    "11559732032986387107991004021392285783925812861821192530917403151452391805634",
                ),
                decimal(
                    "8495653923123431417604973247489272438418190587263600148770280649306958101930",
                ),
                decimal(
                    "4082367875863433681332203403145435568316851327593401208105741076214120093531",
                ),
            ],
        )
    }

    fn point_list(items: Vec<Term>) -> Term {
        Term::list(
            Arc::new(ListDefinition {
                symbols: CollectionSymbols {
                    unit: "Lbl'Stop'List".into(),
                    element: "LblListItem".into(),
                    concat: "Lbl'Unds'List'Unds'".into(),
                },
                element_sort: "SortKItem".into(),
                list_sort: "SortList".into(),
            }),
            items,
            None,
        )
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
            "KRYPTO.sha256raw",
            "HASH.sha256",
            "KRYPTO.sha3256",
            "HASH.sha3_256",
            "KRYPTO.sha512_256raw",
            "KRYPTO.ripemd160",
            "KRYPTO.ripemd160raw",
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
        let cases = [
            (
                "KRYPTO.sha256raw",
                &[
                    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99,
                    0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95,
                    0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55,
                ][..],
            ),
            (
                "KRYPTO.ripemd160raw",
                &[
                    0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28, 0x08, 0x97, 0x7e,
                    0xe8, 0xf5, 0x48, 0xb2, 0x25, 0x8d, 0x31,
                ][..],
            ),
            (
                "KRYPTO.sha512_256raw",
                &[
                    0xc6, 0x72, 0xb8, 0xd1, 0xef, 0x56, 0xed, 0x28, 0xab, 0x87, 0xc3, 0x62, 0x2c,
                    0x51, 0x14, 0x06, 0x9b, 0xdd, 0x3a, 0xd7, 0xb8, 0xf9, 0x73, 0x74, 0x98, 0xd0,
                    0xc0, 0x1e, 0xce, 0xf0, 0x96, 0x7a,
                ][..],
            ),
        ];

        for (hook, expected) in cases {
            assert_eq!(
                evaluate(hook, std::slice::from_ref(&empty)),
                Ok(BuiltinResult::Value(bytes::bytes_term(expected))),
                "{hook}"
            );
        }
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
            ("31 bytes", vec![1; 31]),
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

    #[test]
    fn validates_concrete_bn128_g1_points() {
        let symbol = g1_symbol();
        let field_modulus = decimal(
            "21888242871839275222246405745257275088696311157297823662689037894645226208583",
        );

        for (name, point, expected) in [
            ("infinity", g1_point(&symbol, 0.into(), 0.into()), true),
            ("generator", g1_point(&symbol, 1.into(), 2.into()), true),
            ("off curve", g1_point(&symbol, 1.into(), 3.into()), false),
            (
                "out of field",
                g1_point(&symbol, field_modulus, 2.into()),
                false,
            ),
        ] {
            assert_eq!(
                evaluate("KRYPTO.bn128valid", &[point]),
                Ok(BuiltinResult::Value(super::super::bool_term(expected))),
                "{name}"
            );
        }

        let symbolic = Term::application(
            symbol,
            Vec::new(),
            vec![
                Term::variable(Variable::new("X", Sort::simple("SortInt"))),
                super::super::int_term(2.into()),
            ],
        );
        assert_eq!(
            evaluate("KRYPTO.bn128valid", &[symbolic]),
            Ok(BuiltinResult::NotApplicable)
        );
    }

    #[test]
    fn validates_concrete_bn128_g2_points_and_subgroup() {
        let symbol = g2_symbol();
        let generator = g2_generator(&symbol);
        let infinity = g2_point(&symbol, std::array::from_fn(|_| 0.into()));
        let off_curve = g2_point(
            &symbol,
            [
                decimal(
                    "10857046999023057135944570762232829481370756359578518086990519993285655852781",
                ),
                decimal(
                    "11559732032986387107991004021392285783925812861821192530917403151452391805634",
                ),
                decimal(
                    "8495653923123431417604973247489272438418190587263600148770280649306958101931",
                ),
                decimal(
                    "4082367875863433681332203403145435568316851327593401208105741076214120093531",
                ),
            ],
        );
        let out_of_field = g2_point(
            &symbol,
            [
                decimal(
                    "21888242871839275222246405745257275088696311157297823662689037894645226208583",
                ),
                0.into(),
                0.into(),
                0.into(),
            ],
        );
        // ethereum/execution-specs' `one_point_not_in_subgroup` vector is encoded
        // imaginary-first for calldata. The K production is c0-first, so each Fq2
        // pair is reversed here.
        let non_subgroup = g2_point(
            &symbol,
            [
                8.into(),
                0.into(),
                hex_coordinate("2588360d269af2cd3e0803839ea274c2b8f062a6308e8da85fd774c26f1bcb87"),
                hex_coordinate("00d3270b7da683f988d3889abcdad9776ecd45abaca689f1118c3fd33404b439"),
            ],
        );

        for (name, point, expected) in [
            ("generator", generator, true),
            ("infinity", infinity, true),
            ("off curve", off_curve, false),
            ("out of field", out_of_field, false),
            ("outside the order-r subgroup", non_subgroup, false),
        ] {
            assert_eq!(
                evaluate("KRYPTO.bn128g2valid", &[point]),
                Ok(BuiltinResult::Value(super::super::bool_term(expected))),
                "{name}"
            );
        }
    }

    #[test]
    fn orders_g2_coordinates_as_the_k_production_declares() {
        let symbol = g2_symbol();
        let calldata_order = g2_point(
            &symbol,
            [
                decimal(
                    "11559732032986387107991004021392285783925812861821192530917403151452391805634",
                ),
                decimal(
                    "10857046999023057135944570762232829481370756359578518086990519993285655852781",
                ),
                decimal(
                    "4082367875863433681332203403145435568316851327593401208105741076214120093531",
                ),
                decimal(
                    "8495653923123431417604973247489272438418190587263600148770280649306958101930",
                ),
            ],
        );

        assert_eq!(
            evaluate("KRYPTO.bn128g2valid", &[g2_generator(&symbol)]),
            Ok(BuiltinResult::Value(super::super::bool_term(true)))
        );
        assert_eq!(
            evaluate("KRYPTO.bn128g2valid", &[calldata_order]),
            Ok(BuiltinResult::Value(super::super::bool_term(false)))
        );
    }

    #[test]
    fn adds_concrete_bn128_g1_points() {
        let symbol = g1_symbol();
        let left = g1_point(
            &symbol,
            hex_coordinate("18b18acfb4c2c30276db5411368e7185b311dd124691610c5d3b74034e093dc9"),
            hex_coordinate("063c909c4720840cb5134cb9f59fa749755796819658d32efc0d288198f37266"),
        );
        let right = g1_point(
            &symbol,
            hex_coordinate("07c2b7f58a84bd6145f00c9c2bc0bb1a187f20ff2c92963a88019e7c6a014eed"),
            hex_coordinate("06614e20c147e940f2d70da3f74c9a17df361706a4485c742bd6788478fa17d7"),
        );
        let expected = g1_point(
            &symbol,
            hex_coordinate("2243525c5efd4b9c3d3c45ac0ca3fe4dd85e830a4ce6b65fa1eeaee202839703"),
            hex_coordinate("301d1d33be6da8e509df21cc35964723180eed7532537db9ae5e7d48f195c915"),
        );

        assert_eq!(
            evaluate("KRYPTO.bn128add", &[left, right]),
            Ok(BuiltinResult::Value(expected))
        );

        let infinity = g1_point(&symbol, 0.into(), 0.into());
        assert_eq!(
            evaluate("KRYPTO.bn128add", &[infinity.clone(), infinity.clone()]),
            Ok(BuiltinResult::Value(infinity))
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128add",
                &[
                    g1_point(&symbol, 1.into(), 3.into()),
                    g1_point(&symbol, 1.into(), 2.into()),
                ],
            ),
            Ok(BuiltinResult::Bottom)
        );

        let alternate_symbol = Arc::new(Symbol::constructor(
            "LblalternateG1Point",
            vec![Sort::simple("SortInt"), Sort::simple("SortInt")],
            Sort::simple("SortG1Point"),
        ));
        assert_eq!(
            evaluate(
                "KRYPTO.bn128add",
                &[
                    g1_point(&symbol, 1.into(), 2.into()),
                    g1_point(&alternate_symbol, 1.into(), 2.into()),
                ],
            ),
            Ok(BuiltinResult::Bottom)
        );

        let symbolic = Term::variable(Variable::new("P", Sort::simple("SortG1Point")));
        assert_eq!(
            evaluate(
                "KRYPTO.bn128add",
                &[symbolic, g1_point(&symbol, 1.into(), 2.into())],
            ),
            Ok(BuiltinResult::NotApplicable)
        );
    }

    #[test]
    fn multiplies_concrete_bn128_g1_points_with_reduced_scalars() {
        let symbol = g1_symbol();
        let generator = g1_point(&symbol, 1.into(), 2.into());
        let doubled = g1_point(
            &symbol,
            hex_coordinate("030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd3"),
            hex_coordinate("15ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4"),
        );
        let group_order = decimal(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
        );

        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[generator.clone(), super::super::int_term(2.into())],
            ),
            Ok(BuiltinResult::Value(doubled.clone()))
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[generator.clone(), super::super::int_term(0.into())],
            ),
            Ok(BuiltinResult::Value(g1_point(&symbol, 0.into(), 0.into())))
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[
                    g1_point(&symbol, 1.into(), 3.into()),
                    super::super::int_term(2.into()),
                ],
            ),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[generator.clone(), super::super::int_term((-1).into()),],
            ),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[
                    generator.clone(),
                    super::super::int_term(group_order.clone()),
                ],
            ),
            Ok(BuiltinResult::Value(g1_point(&symbol, 0.into(), 0.into())))
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[generator.clone(), super::super::int_term(&group_order + 2),],
            ),
            Ok(BuiltinResult::Value(doubled))
        );

        let max_scalar = (BigInt::from(1) << 256) - 1;
        let max_reduced = &max_scalar % &group_order;
        assert_eq!(
            evaluate(
                "KRYPTO.bn128mul",
                &[generator.clone(), super::super::int_term(max_scalar),],
            ),
            evaluate(
                "KRYPTO.bn128mul",
                &[generator.clone(), super::super::int_term(max_reduced)],
            )
        );

        let symbolic_scalar = Term::variable(Variable::new("S", Sort::simple("SortInt")));
        assert_eq!(
            evaluate("KRYPTO.bn128mul", &[generator, symbolic_scalar]),
            Ok(BuiltinResult::NotApplicable)
        );
    }

    #[test]
    fn evaluates_concrete_bn128_pairing_products() {
        let g1 = g1_symbol();
        let g2 = g2_symbol();
        let generator_g1 = g1_point(&g1, 1.into(), 2.into());
        let generator_g2 = g2_generator(&g2);
        let injected_generator_g1 = Term::injection(
            Sort::simple("SortG1Point"),
            Sort::simple("SortKItem"),
            generator_g1.clone(),
        );
        let injected_generator_g2 = Term::injection(
            Sort::simple("SortG2Point"),
            Sort::simple("SortKItem"),
            generator_g2.clone(),
        );

        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[point_list(Vec::new()), point_list(Vec::new())],
            ),
            Ok(BuiltinResult::Value(super::super::bool_term(true)))
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[
                    point_list(vec![injected_generator_g1]),
                    point_list(vec![injected_generator_g2]),
                ],
            ),
            Ok(BuiltinResult::Value(super::super::bool_term(false)))
        );

        let negative_generator_g1 = g1_point(
            &g1,
            1.into(),
            decimal(
                "21888242871839275222246405745257275088696311157297823662689037894645226208581",
            ),
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[
                    point_list(vec![generator_g1, negative_generator_g1]),
                    point_list(vec![generator_g2.clone(), generator_g2]),
                ],
            ),
            Ok(BuiltinResult::Value(super::super::bool_term(true)))
        );
    }

    #[test]
    fn rejects_malformed_concrete_bn128_pairing_arguments() {
        let g1 = g1_symbol();
        let g2 = g2_symbol();
        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[
                    point_list(vec![g1_point(&g1, 1.into(), 2.into())]),
                    point_list(Vec::new()),
                ],
            ),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[
                    point_list(vec![g1_point(&g1, 1.into(), 3.into())]),
                    point_list(vec![g2_generator(&g2)]),
                ],
            ),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[
                    point_list(vec![Term::domain_value(
                        Sort::simple("SortKItem"),
                        "malformed",
                    )]),
                    point_list(vec![g2_generator(&g2)]),
                ],
            ),
            Ok(BuiltinResult::Bottom)
        );

        let definition = match point_list(Vec::new()).kind() {
            TermKind::List { definition, .. } => definition.clone(),
            _ => unreachable!(),
        };
        let opaque = Term::list(
            definition,
            Vec::new(),
            Some((
                Term::variable(Variable::new("REST", Sort::simple("SortList"))),
                Vec::new(),
            )),
        );
        assert_eq!(
            evaluate("KRYPTO.bn128ate", &[opaque, point_list(Vec::new())]),
            Ok(BuiltinResult::NotApplicable)
        );

        let symbolic_element = Term::variable(Variable::new("P", Sort::simple("SortG1Point")));
        assert_eq!(
            evaluate(
                "KRYPTO.bn128ate",
                &[
                    point_list(vec![symbolic_element]),
                    point_list(vec![g2_generator(&g2)]),
                ],
            ),
            Ok(BuiltinResult::NotApplicable)
        );
    }

    #[test]
    fn interrupted_bn128_pairing_stops_before_the_product() {
        let g1 = g1_symbol();
        let g2 = g2_symbol();
        let token = CancellationToken::new();
        token.cancel();

        let g1s = point_list(vec![
            g1_point(&g1, 1.into(), 2.into()),
            g1_point(&g1, 1.into(), 2.into()),
        ]);
        let g2s = point_list(vec![g2_generator(&g2), g2_generator(&g2)]);
        assert_eq!(
            token.scope(|| evaluate("KRYPTO.bn128ate", &[g1s, g2s])),
            Err(BuiltinError::Interrupted)
        );
    }
}
