//! Oracle test for `kompile.constant_folding.evaluate`: every hook in the folding table, applied
//! to random constant arguments, either folds to the value the backend's own evaluator computes
//! (`k_rust_backend::builtin::evaluate_hook`) or is rejected where that evaluator finds the hook
//! undefined. Hooks the backend does not evaluate are compared with a small model in this file,
//! written from the hook's documented meaning. The two evaluators are independent
//! implementations of the same hook semantics, so a difference is a defect on one side.
//!
//! The folder is exercised through `Folder::try_fold` on one resolved definition that declares
//! every hooked production, so the case loop pays for neither a prelude nor a resolution.
#![allow(
    clippy::wildcard_enum_match_arm,
    reason = "the test classifies hook outcomes and only names the variants it distinguishes"
)]

use std::collections::BTreeMap;

use k_rust_backend::{
    builtin::{BuiltinError, BuiltinResult, UnsupportedHookReason, evaluate_hook},
    term::{Sort as BackendSort, Term as BackendTerm, TermKind},
};
use k_rust_kore::names::BuiltinSort;
use num_bigint::{BigInt, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};
use proptest::{
    prelude::*,
    sample::select,
    test_runner::{Config, RngAlgorithm, TestCaseError, TestRng, TestRunner},
};
use serde_json::json;

use super::{Folder, MAX_FOLDED_BITS, Unfolded};
use crate::{
    definition::{
        Attributes, Definition, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::{Label, Sort, Term},
};

/// Cases per hook. Each case costs one fold and one backend evaluation.
const CASES: u32 = 96;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    Bool,
    Int,
    Str,
    Float,
    Id,
}

use Kind::{Bool as B, Float as F, Id as D, Int as I, Str as S};

/// The folding table (`Folder::evaluate`): hook, argument kinds, result kind.
const HOOKS: &[(&str, &[Kind], Kind)] = &[
    ("BOOL.not", &[B], B),
    ("BOOL.and", &[B, B], B),
    ("BOOL.andThen", &[B, B], B),
    ("BOOL.xor", &[B, B], B),
    ("BOOL.or", &[B, B], B),
    ("BOOL.orElse", &[B, B], B),
    ("BOOL.implies", &[B, B], B),
    ("BOOL.eq", &[B, B], B),
    ("BOOL.ne", &[B, B], B),
    ("INT.not", &[I], I),
    ("INT.pow", &[I, I], I),
    ("INT.powmod", &[I, I, I], I),
    ("INT.mul", &[I, I], I),
    ("INT.tdiv", &[I, I], I),
    ("INT.tmod", &[I, I], I),
    ("INT.ediv", &[I, I], I),
    ("INT.emod", &[I, I], I),
    ("INT.add", &[I, I], I),
    ("INT.sub", &[I, I], I),
    ("INT.shr", &[I, I], I),
    ("INT.shl", &[I, I], I),
    ("INT.and", &[I, I], I),
    ("INT.xor", &[I, I], I),
    ("INT.or", &[I, I], I),
    ("INT.min", &[I, I], I),
    ("INT.max", &[I, I], I),
    ("INT.abs", &[I], I),
    ("INT.log2", &[I], I),
    ("INT.bitRange", &[I, I, I], I),
    ("INT.signExtendBitRange", &[I, I, I], I),
    ("INT.lt", &[I, I], B),
    ("INT.gt", &[I, I], B),
    ("INT.le", &[I, I], B),
    ("INT.ge", &[I, I], B),
    ("INT.eq", &[I, I], B),
    ("INT.ne", &[I, I], B),
    ("STRING.concat", &[S, S], S),
    ("STRING.length", &[S], I),
    ("STRING.chr", &[I], S),
    ("STRING.ord", &[S], I),
    ("STRING.substr", &[S, I, I], S),
    ("STRING.find", &[S, S, I], I),
    ("STRING.rfind", &[S, S, I], I),
    ("STRING.findChar", &[S, S, I], I),
    ("STRING.rfindChar", &[S, S, I], I),
    ("STRING.string2int", &[S], I),
    ("STRING.int2string", &[I], S),
    ("STRING.string2base", &[S, I], I),
    ("STRING.base2string", &[I, I], S),
    ("STRING.replaceAll", &[S, S, S], S),
    ("STRING.replace", &[S, S, S, I], S),
    ("STRING.replaceFirst", &[S, S, S], S),
    ("STRING.countAllOccurrences", &[S, S], I),
    ("STRING.eq", &[S, S], B),
    ("STRING.ne", &[S, S], B),
    ("STRING.lt", &[S, S], B),
    ("STRING.gt", &[S, S], B),
    ("STRING.le", &[S, S], B),
    ("STRING.ge", &[S, S], B),
    ("STRING.token2string", &[D], S),
    ("STRING.string2token", &[S], D),
    ("STRING.float2string", &[F], S),
    ("STRING.floatFormat", &[F, S], S),
    ("STRING.string2float", &[S], F),
    ("FLOAT.precision", &[F], I),
    ("FLOAT.exponentBits", &[F], I),
    ("FLOAT.exponent", &[F], I),
    ("FLOAT.sign", &[F], B),
    ("FLOAT.isNaN", &[F], B),
    ("FLOAT.neg", &[F], F),
    ("FLOAT.abs", &[F], F),
    ("FLOAT.floor", &[F], F),
    ("FLOAT.ceil", &[F], F),
    ("FLOAT.trunc", &[F], F),
    ("FLOAT.exp", &[F], F),
    ("FLOAT.log", &[F], F),
    ("FLOAT.sin", &[F], F),
    ("FLOAT.cos", &[F], F),
    ("FLOAT.tan", &[F], F),
    ("FLOAT.asin", &[F], F),
    ("FLOAT.acos", &[F], F),
    ("FLOAT.atan", &[F], F),
    ("FLOAT.add", &[F, F], F),
    ("FLOAT.sub", &[F, F], F),
    ("FLOAT.mul", &[F, F], F),
    ("FLOAT.div", &[F, F], F),
    ("FLOAT.rem", &[F, F], F),
    ("FLOAT.pow", &[F, F], F),
    ("FLOAT.atan2", &[F, F], F),
    ("FLOAT.min", &[F, F], F),
    ("FLOAT.max", &[F, F], F),
    ("FLOAT.lt", &[F, F], B),
    ("FLOAT.le", &[F, F], B),
    ("FLOAT.gt", &[F, F], B),
    ("FLOAT.ge", &[F, F], B),
    ("FLOAT.eq", &[F, F], B),
    ("FLOAT.ne", &[F, F], B),
    ("FLOAT.root", &[F, I], F),
    ("FLOAT.round", &[F, I, I], F),
    ("FLOAT.int2float", &[I, I, I], F),
    ("FLOAT.float2int", &[F], I),
    ("FLOAT.maxValue", &[I, I], F),
    ("FLOAT.minValue", &[I, I], F),
];

/// A constant argument, convertible to a frontend token and to a backend domain value.
#[derive(Clone, Debug)]
enum Arg {
    Bool(bool),
    Int(BigInt),
    Str(String),
    /// A `Float` token, such as `1.5e0`, `2.5e-1f`, `NaNp24x8` or `-Infinity`.
    Float(String),
    Id(String),
}

impl Arg {
    fn token(&self) -> Term {
        let (token, sort) = match self {
            Self::Bool(value) => (value.to_string(), "Bool"),
            Self::Int(value) => (value.to_string(), "Int"),
            Self::Str(value) => (crate::kast::string::quote(value), "String"),
            Self::Float(value) => (value.clone(), "Float"),
            Self::Id(value) => (value.clone(), "Id"),
        };
        Term::Token {
            token,
            sort: Sort::new(sort),
        }
    }

    fn domain_value(&self) -> BackendTerm {
        match self {
            Self::Bool(value) => BackendTerm::domain_value(
                BackendSort::builtin(BuiltinSort::Bool),
                value.to_string(),
            ),
            Self::Int(value) => {
                BackendTerm::domain_value(BackendSort::builtin(BuiltinSort::Int), value.to_string())
            }
            Self::Str(value) => {
                BackendTerm::domain_value(BackendSort::builtin(BuiltinSort::String), value.clone())
            }
            Self::Float(value) => {
                BackendTerm::domain_value(BackendSort::builtin(BuiltinSort::Float), value.clone())
            }
            Self::Id(value) => {
                BackendTerm::domain_value(BackendSort::simple("SortId"), value.clone())
            }
        }
    }

    fn int(&self) -> &BigInt {
        match self {
            Self::Int(value) => value,
            other => panic!("expected an Int argument, got {other:?}"),
        }
    }

    fn str(&self) -> &str {
        match self {
            Self::Str(value) => value,
            other => panic!("expected a String argument, got {other:?}"),
        }
    }

    fn float(&self) -> &str {
        match self {
            Self::Float(value) => value,
            other => panic!("expected a Float argument, got {other:?}"),
        }
    }
}

/// A Float value in one of the two IEEE formats the oracles represent exactly; any other
/// precision and exponent width is kept as its token.
#[derive(Clone, Copy, Debug)]
enum Fl {
    B32(f32),
    B64(f64),
}

impl Fl {
    fn as_f64(self) -> f64 {
        match self {
            Self::B32(value) => f64::from(value),
            Self::B64(value) => value,
        }
    }

    fn same(self, other: Self) -> bool {
        match (self, other) {
            (Self::B32(a), Self::B32(b)) => {
                (a.is_nan() && b.is_nan()) || a.to_bits() == b.to_bits()
            }
            (Self::B64(a), Self::B64(b)) => {
                (a.is_nan() && b.is_nan()) || a.to_bits() == b.to_bits()
            }
            _ => false,
        }
    }

    /// Whether `self` is `other` or one unit in the last place away, with the same sign; zeros,
    /// infinities and NaN must match exactly.
    fn within_one_ulp(self, other: Self) -> bool {
        if self.same(other) {
            return true;
        }
        let (a, b) = (self.as_f64(), other.as_f64());
        if !a.is_finite() || !b.is_finite() || a == 0.0 || b == 0.0 {
            return false;
        }
        if a.is_sign_negative() != b.is_sign_negative() {
            return false;
        }
        match (self, other) {
            (Self::B32(a), Self::B32(b)) => a.to_bits().abs_diff(b.to_bits()) <= 1,
            (Self::B64(a), Self::B64(b)) => a.to_bits().abs_diff(b.to_bits()) <= 1,
            _ => false,
        }
    }
}

/// A decoded hook result.
#[derive(Clone, Debug)]
enum Out {
    Bool(bool),
    Int(BigInt),
    Str(Vec<u8>),
    Float(Fl),
    /// A Float in a context other than binary32 or binary64: only its token is known.
    FloatToken(String),
    Id(String),
}

impl Out {
    /// The size of the value in the unit of the fold's result bound.
    fn bits(&self) -> u64 {
        match self {
            Self::Bool(_) => 1,
            Self::Int(value) => value.bits(),
            Self::Str(bytes) => 8 * bytes.len() as u64,
            Self::Float(Fl::B32(_)) => 24,
            Self::Float(Fl::B64(_)) => 53,
            Self::FloatToken(token) => float_parts(token).map_or(0, |parts| u64::from(parts.1)),
            Self::Id(text) => 8 * text.len() as u64,
        }
    }

    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Int(a), Self::Int(b)) => a == b,
            (Self::Str(a), Self::Str(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => a.same(*b),
            (Self::FloatToken(a), Self::FloatToken(b)) => a == b,
            (Self::Id(a), Self::Id(b)) => a == b,
            _ => false,
        }
    }
}

/// What the oracle says a case must fold to.
#[derive(Debug)]
enum Expect {
    /// The hook is defined here and has this value.
    Value(Out),
    /// The hook is undefined here (`#False` in its documentation, `Bottom` in the backend), so
    /// the fold must leave the application unfolded, as undefined, rather than produce a token.
    Undefined,
    /// The value is defined and larger than the fold's result bound, so the fold must leave the
    /// application unfolded as too large.
    TooLarge,
    /// The hook is `total` and its documentation gives no value here (the backend leaves it
    /// `Unspecified`), so the fold must leave the application unfolded as unspecified.
    Unspecified,
    /// No oracle covers this case; the fold must still finish without panicking.
    Unchecked,
}

/// Splits a Float token into its text and its precision and exponent width.
fn float_parts(token: &str) -> Option<(&str, u32, u32)> {
    if let Some((rest, exponent_bits)) = token.rsplit_once(['x', 'X'])
        && let Some((text, precision)) = rest.rsplit_once(['p', 'P'])
    {
        return Some((text, precision.parse().ok()?, exponent_bits.parse().ok()?));
    }
    if let Some(text) = token.strip_suffix(['f', 'F']) {
        Some((text, 24, 8))
    } else {
        Some((token.strip_suffix(['d', 'D']).unwrap_or(token), 53, 11))
    }
}

fn decode_float(token: &str) -> Result<Out, String> {
    let (text, precision, exponent_bits) =
        float_parts(token).ok_or_else(|| format!("unreadable Float token {token:?}"))?;
    let special = match text {
        "NaN" => Some(f64::NAN),
        "Infinity" => Some(f64::INFINITY),
        "-Infinity" => Some(f64::NEG_INFINITY),
        _ => None,
    };
    match (precision, exponent_bits) {
        (24, 8) => special
            .map(|value| value as f32)
            .or_else(|| text.parse::<f32>().ok())
            .map(|value| Out::Float(Fl::B32(value))),
        (53, 11) => special
            .or_else(|| text.parse::<f64>().ok())
            .map(|value| Out::Float(Fl::B64(value))),
        _ => Some(Out::FloatToken(token.to_owned())),
    }
    .ok_or_else(|| format!("unreadable Float token {token:?}"))
}

fn decode_folded(term: &Term, kind: Kind) -> Result<Out, String> {
    let Term::Token { token, .. } = term.unannotated() else {
        return Err(format!("the fold produced a non-token {term:?}"));
    };
    match kind {
        Kind::Bool => token
            .parse()
            .map(Out::Bool)
            .map_err(|_| format!("bad Bool token {token:?}")),
        Kind::Int => token
            .parse()
            .map(Out::Int)
            .map_err(|_| format!("bad Int token {token:?}")),
        Kind::Str => crate::kast::string::unquote(token).map(|value| Out::Str(value.into_bytes())),
        Kind::Float => decode_float(token),
        Kind::Id => Ok(Out::Id(token.clone())),
    }
}

fn decode_backend(term: &BackendTerm, kind: Kind) -> Result<Out, String> {
    let TermKind::DomainValue { value, .. } = term.kind() else {
        return Err(format!("the backend produced a non-value {term:?}"));
    };
    let text = || {
        value
            .as_utf8()
            .map_err(|_| format!("non-UTF-8 backend value {term:?}"))
    };
    match kind {
        Kind::Bool => text()?
            .parse()
            .map(Out::Bool)
            .map_err(|_| format!("bad Bool value {term:?}")),
        Kind::Int => text()?
            .parse()
            .map(Out::Int)
            .map_err(|_| format!("bad Int value {term:?}")),
        Kind::Str => Ok(Out::Str(value.as_bytes().to_vec())),
        Kind::Float => decode_float(text()?),
        Kind::Id => Ok(Out::Id(text()?.to_owned())),
    }
}

fn label(hook: &str) -> String {
    format!("hook_{}", hook.replace('.', "_"))
}

/// One module declaring the four hooked sorts, an unhooked `Id`, and one function production
/// per hook in the table.
fn definition() -> Definition {
    fn attributes(entries: &[(&str, &str)]) -> Attributes {
        Attributes::new(
            entries
                .iter()
                .map(|(key, value)| ((*key).to_owned(), json!(value)))
                .collect::<BTreeMap<_, _>>(),
        )
    }
    let sort = |kind: Kind| {
        Sort::new(match kind {
            Kind::Bool => "Bool",
            Kind::Int => "Int",
            Kind::Str => "String",
            Kind::Float => "Float",
            Kind::Id => "Id",
        })
    };
    let mut sentences = [
        ("Bool", Some("BOOL.Bool")),
        ("Int", Some("INT.Int")),
        ("String", Some("STRING.String")),
        ("Float", Some("FLOAT.Float")),
        ("Id", None),
    ]
    .into_iter()
    .map(|(name, hook)| Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new(name),
        attributes: hook.map_or_else(Attributes::default, |hook| attributes(&[("hook", hook)])),
    })
    .collect::<Vec<_>>();
    sentences.extend(HOOKS.iter().map(|(hook, arguments, result)| {
        Sentence::Production {
            label: Some(Label::new(label(hook))),
            parameters: Vec::new(),
            sort: sort(*result),
            items: arguments
                .iter()
                .map(|kind| ProductionItem::NonTerminal {
                    sort: sort(*kind),
                    name: None,
                })
                .collect(),
            attributes: attributes(&[("function", ""), ("hook", hook)]),
        }
    }));
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: sentences.into_iter().map(std::sync::Arc::new).collect(),
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

// ---- argument strategies -------------------------------------------------------------------

fn big(value: i128) -> BigInt {
    BigInt::from(value)
}

fn pow2(bits: u32) -> BigInt {
    BigInt::one() << bits
}

/// Integers at the boundaries the hooks care about: zero, signs, the 32- and 64-bit edges, and
/// multi-word values.
fn int_edges() -> Vec<BigInt> {
    let mut edges = [0, 1, -1, 2, -2, 3, 7, -7, 8, 255, -256]
        .into_iter()
        .map(big)
        .collect::<Vec<_>>();
    for bits in [31, 32, 63, 64, 100] {
        edges.extend([pow2(bits) - 1, pow2(bits), pow2(bits) + 1, -pow2(bits)]);
    }
    edges
}

fn any_int() -> BoxedStrategy<BigInt> {
    prop_oneof![
        3 => select(int_edges()),
        3 => (-40i64..40).prop_map(BigInt::from),
        2 => any::<i64>().prop_map(BigInt::from),
        2 => (any::<bool>(), prop::collection::vec(any::<u32>(), 1..6)).prop_map(
            |(negative, digits)| BigInt::from_slice(
                if negative { Sign::Minus } else { Sign::Plus },
                &digits
            )
        ),
    ]
    .boxed()
}

/// Values for a natural-number Int parameter: small ones, negative ones, and the 32- and 64-bit
/// edges. `cheap` excludes `2^31 - 1`, for hooks whose backend evaluation would then take
/// gigabytes.
fn parameter(cheap: bool) -> BoxedStrategy<BigInt> {
    let mut edges = vec![
        big(-1),
        big(-2),
        -pow2(40),
        pow2(31),
        pow2(32) - 1,
        pow2(32),
        pow2(64),
    ];
    if !cheap {
        edges.push(pow2(31) - 1);
    }
    prop_oneof![
        5 => (-3i64..80).prop_map(BigInt::from),
        1 => select(edges),
    ]
    .boxed()
}

const ALPHABET: &[char] = &[
    'a', 'b', 'A', 'Z', '0', '1', '7', '9', '-', '+', '_', ' ', '"', '\\', '\n', '\t', '\u{0}',
    '\u{7f}', 'é', 'λ', '\u{fffd}', '🦀',
];

fn any_string(max: usize) -> BoxedStrategy<String> {
    prop::collection::vec(select(ALPHABET), 0..=max)
        .prop_map(|chars| chars.into_iter().collect())
        .boxed()
}

/// A haystack and a needle that is, half of the time, one of the haystack's substrings.
fn haystack_and_needle() -> BoxedStrategy<(String, String)> {
    prop_oneof![
        (any_string(6), any_string(2)),
        any_string(6).prop_flat_map(|haystack| {
            let length = haystack.chars().count();
            (Just(haystack), 0..=length, 0..=length).prop_map(|(haystack, a, b)| {
                let needle = haystack
                    .chars()
                    .skip(a.min(b))
                    .take(a.max(b) - a.min(b))
                    .collect();
                (haystack, needle)
            })
        }),
    ]
    .boxed()
}

/// An index into `text` measured in characters: mostly in range, sometimes just outside it or at
/// the parameter edges.
fn index(text: &str) -> BoxedStrategy<BigInt> {
    let length = text.chars().count() as i64;
    prop_oneof![
        4 => (0..=length).prop_map(BigInt::from),
        1 => (-2..=length + 2).prop_map(BigInt::from),
        1 => parameter(false),
    ]
    .boxed()
}

/// Float values at the edges of binary64 and binary32: signed zeros, halfway cases, the extreme
/// normal and subnormal magnitudes, the binary32 overflow tie, infinities and NaN.
fn float_edges() -> Vec<f64> {
    let single_maximum = f64::from(f32::MAX);
    vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -0.5,
        1.5,
        2.5,
        -2.5,
        3.0,
        0.1,
        1e10,
        1e-10,
        1e300,
        -1e300,
        f64::MAX,
        -f64::MAX,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        -f64::from_bits(1),
        f64::from_bits(0x000f_ffff_ffff_ffff),
        2f64.powi(53) + 2.0,
        single_maximum,
        // Halfway between the largest binary32 value and the next power of two.
        single_maximum + 2f64.powi(103),
        f64::from(f32::MIN_POSITIVE),
        f64::from(f32::from_bits(1)),
        std::f64::consts::PI,
        std::f64::consts::E,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
    ]
}

/// Float formats a token can name: plain and `d` (binary64), `f` (binary32), explicit `p`/`x`
/// contexts for both, and binary16, which only the fold evaluates.
#[derive(Clone, Copy, Debug)]
enum Format {
    Double,
    DoubleD,
    DoubleExplicit,
    Single,
    SingleExplicit,
    Half,
}

fn float_value() -> BoxedStrategy<f64> {
    prop_oneof![
        4 => select(float_edges()),
        2 => (-40i32..40).prop_map(|quarter| f64::from(quarter) / 4.0),
        2 => -1e6f64..1e6,
        2 => any::<u64>().prop_map(f64::from_bits),
    ]
    .boxed()
}

fn float_token(value: f64, format: Format) -> String {
    let single = matches!(
        format,
        Format::Single | Format::SingleExplicit | Format::Half
    );
    // A binary64 value can overflow to an infinity in binary32.
    let value = if single {
        f64::from(value as f32)
    } else {
        value
    };
    let text = if value.is_nan() {
        "NaN".to_owned()
    } else if value.is_infinite() {
        if value < 0.0 { "-Infinity" } else { "Infinity" }.to_owned()
    } else if single {
        format!("{:e}", value as f32)
    } else {
        format!("{value:e}")
    };
    let suffix = match format {
        Format::Double => "",
        Format::DoubleD => "d",
        Format::DoubleExplicit => "p53x11",
        Format::Single => "f",
        Format::SingleExplicit => "p24x8",
        Format::Half => "p11x5",
    };
    format!("{text}{suffix}")
}

fn float_format() -> BoxedStrategy<Format> {
    prop_oneof![
        3 => Just(Format::Double),
        1 => Just(Format::DoubleD),
        1 => Just(Format::DoubleExplicit),
        3 => Just(Format::Single),
        1 => Just(Format::SingleExplicit),
        1 => Just(Format::Half),
    ]
    .boxed()
}

fn any_float() -> BoxedStrategy<String> {
    (float_value(), float_format())
        .prop_map(|(value, format)| float_token(value, format))
        .boxed()
}

/// Two Float tokens, usually of one format.
fn float_pair() -> BoxedStrategy<Vec<Arg>> {
    prop_oneof![
        9 => (float_value(), float_value(), float_format()).prop_map(|(a, b, format)| vec![
            Arg::Float(float_token(a, format)),
            Arg::Float(float_token(b, format)),
        ]),
        1 => (any_float(), any_float()).prop_map(|(a, b)| vec![Arg::Float(a), Arg::Float(b)]),
    ]
    .boxed()
}

/// A precision and exponent width: the binary32 and binary64 contexts, other valid ones, and
/// invalid ones.
fn context() -> BoxedStrategy<(BigInt, BigInt)> {
    select(vec![
        (24, 8),
        (24, 8),
        (53, 11),
        (53, 11),
        (11, 5),
        (113, 15),
        (2, 2),
        (1, 8),
        (24, 1),
        (24, 31),
        (24, 32),
        (-1, 8),
        (1 << 31, 8),
        (24, 1 << 40),
    ])
    .prop_map(|(precision, exponent_bits): (i128, i128)| (big(precision), big(exponent_bits)))
    .boxed()
}

/// Decimal integers with an optional sign, and near misses of that syntax.
fn integer_text() -> BoxedStrategy<String> {
    prop_oneof![
        3 => (any_int(), any::<bool>()).prop_map(|(value, plus)| {
            if plus && !value.is_negative() { format!("+{value}") } else { value.to_string() }
        }),
        2 => select(vec![
            "", "+", "-", "1_0", "_1", "1_", "-_1", " 1", "1 ", "0x1f", "++1", "+-1", "-+1",
            "1e3", "1.0", "\u{661}", "007", "-0",
        ])
        .prop_map(str::to_owned),
        2 => prop::collection::vec(select(&['0', '1', '9', '-', '+', '_', ' ', 'a'][..]), 0..5)
            .prop_map(|chars| chars.into_iter().collect()),
    ]
    .boxed()
}

fn base() -> BoxedStrategy<BigInt> {
    prop_oneof![
        6 => (2i64..=36).prop_map(BigInt::from),
        1 => select(vec![big(0), big(1), big(37), big(-2), big(-16), pow2(40)]),
    ]
    .boxed()
}

/// Strings in the documented `String2Base` syntax for some base, and near misses.
fn base_text_and_base() -> BoxedStrategy<Vec<Arg>> {
    prop_oneof![
        2 => (any_int(), 2u32..=36, any::<bool>()).prop_map(|(value, radix, upper)| {
            let text = value.to_str_radix(radix);
            vec![
                Arg::Str(if upper { text.to_uppercase() } else { text }),
                Arg::Int(BigInt::from(radix)),
            ]
        }),
        2 => (
            prop::collection::vec(
                select(&['0', '1', '7', '9', 'a', 'f', 'z', 'A', 'F', 'Z', '_', '-', '+', ' '][..]),
                0..5,
            ),
            base(),
        )
            .prop_map(|(chars, base)| vec![Arg::Str(chars.into_iter().collect()), Arg::Int(base)]),
    ]
    .boxed()
}

/// Strings in the documented `Float` syntax, and near misses.
fn float_text() -> BoxedStrategy<String> {
    prop_oneof![
        3 => any_float(),
        2 => select(vec![
            "", "inf", "nan", "Inf", "infinity", "1e", "abc", "1.5.5", " 1", "1 ", "0x10",
            "1_0", "Infinityx", "1p53", "1p53x", "@inf@", "+Infinity", "-NaN", ".5", "5.",
            "1e+5", "1E5", "-.5e-3", "1.5F", "2D", "1P24X8", "NaNf", "Infinityp24x8",
        ])
        .prop_map(str::to_owned),
    ]
    .boxed()
}

fn int_args(count: usize) -> BoxedStrategy<Vec<Arg>> {
    prop::collection::vec(any_int().prop_map(Arg::Int), count).boxed()
}

fn ints(values: Vec<BigInt>) -> Vec<Arg> {
    values.into_iter().map(Arg::Int).collect()
}

fn arguments(hook: &str) -> BoxedStrategy<Vec<Arg>> {
    match hook {
        _ if hook.starts_with("BOOL.") => {
            let arity = HOOKS.iter().find(|entry| entry.0 == hook).unwrap().1.len();
            prop::collection::vec(any::<bool>().prop_map(Arg::Bool), arity).boxed()
        }
        "INT.not" | "INT.abs" | "INT.log2" | "STRING.int2string" => int_args(1),
        "INT.pow" => prop_oneof![
            // Any base with a bounded exponent.
            (any_int(), -3i64..300).prop_map(|(base, exponent)| ints(vec![base, exponent.into()])),
            // A base whose powers stay small, with every exponent edge.
            (select(vec![big(0), big(1), big(-1)]), parameter(false))
                .prop_map(|(base, exponent)| ints(vec![base, exponent])),
            // Exponents beyond the fold's bound, whose results only the bases 0, 1 and -1 keep
            // small.
            (any_int(), select(vec![pow2(33), pow2(64)]))
                .prop_map(|(base, exponent)| ints(vec![base, exponent])),
        ]
        .boxed(),
        "INT.powmod" => (
            any_int(),
            prop_oneof![(-5i64..300).prop_map(BigInt::from), any_int()],
            prop_oneof![(-12i64..13).prop_map(BigInt::from), any_int()],
        )
            .prop_map(|(base, exponent, modulus)| ints(vec![base, exponent, modulus]))
            .boxed(),
        "INT.tdiv" | "INT.tmod" | "INT.ediv" | "INT.emod" => (
            any_int(),
            prop_oneof![1 => Just(BigInt::zero()), 4 => any_int()],
        )
            .prop_map(|(a, b)| ints(vec![a, b]))
            .boxed(),
        "INT.shr" => (any_int(), parameter(false))
            .prop_map(|(value, amount)| ints(vec![value, amount]))
            .boxed(),
        "INT.shl" => prop_oneof![
            // A nonzero value shifted by a small amount, a negative one, or one whose result
            // neither evaluator computes; amounts near 2^31 would make the backend build and
            // print a result of hundreds of megabytes.
            (
                any_int(),
                prop_oneof![
                    5 => (-3i64..300).prop_map(BigInt::from),
                    1 => select(vec![big(-1), big(-2), -pow2(40), pow2(33), pow2(64)]),
                ],
            )
                .prop_map(|(value, amount)| ints(vec![value, amount])),
            parameter(false).prop_map(|amount| ints(vec![BigInt::zero(), amount])),
        ]
        .boxed(),
        "INT.bitRange" | "INT.signExtendBitRange" => (any_int(), parameter(true), parameter(true))
            .prop_map(|(value, index, length)| ints(vec![value, index, length]))
            .boxed(),
        _ if hook.starts_with("INT.") => prop_oneof![
            int_args(2),
            any_int().prop_map(|value| ints(vec![value.clone(), value])),
        ]
        .boxed(),
        "STRING.concat" => (any_string(4), any_string(4))
            .prop_map(|(a, b)| vec![Arg::Str(a), Arg::Str(b)])
            .boxed(),
        "STRING.length" | "STRING.string2token" => {
            any_string(6).prop_map(|a| vec![Arg::Str(a)]).boxed()
        }
        "STRING.ord" => any_string(2).prop_map(|a| vec![Arg::Str(a)]).boxed(),
        "STRING.chr" => prop_oneof![
            (0i64..0x80).prop_map(BigInt::from),
            (0i64..0x11_0000).prop_map(BigInt::from),
            select(vec![
                big(0xd7ff),
                big(0xd800),
                big(0xdbff),
                big(0xdc00),
                big(0xdfff),
                big(0xe000),
                big(0x10_ffff),
                big(0x11_0000),
                big(-1),
                pow2(32) - 1,
                pow2(64),
            ]),
        ]
        .prop_map(|code| vec![Arg::Int(code)])
        .boxed(),
        "STRING.substr" => any_string(6)
            .prop_flat_map(|text| {
                let start = index(&text);
                let end = index(&text);
                (Just(text), start, end, any::<bool>())
            })
            // Half of the pairs in order, so that most cases lie in the documented domain.
            .prop_map(|(text, start, end, ordered)| {
                if ordered && start > end {
                    (text, end, start)
                } else {
                    (text, start, end)
                }
            })
            .prop_map(|(text, start, end)| vec![Arg::Str(text), Arg::Int(start), Arg::Int(end)])
            .boxed(),
        "STRING.find" | "STRING.rfind" | "STRING.findChar" | "STRING.rfindChar" => {
            haystack_and_needle()
                .prop_flat_map(|(haystack, needle)| {
                    let index = index(&haystack);
                    (Just(haystack), Just(needle), index)
                })
                .prop_map(|(haystack, needle, index)| {
                    vec![Arg::Str(haystack), Arg::Str(needle), Arg::Int(index)]
                })
                .boxed()
        }
        "STRING.string2int" => integer_text().prop_map(|text| vec![Arg::Str(text)]).boxed(),
        "STRING.string2base" => base_text_and_base(),
        "STRING.base2string" => (any_int(), base())
            .prop_map(|(value, base)| ints(vec![value, base]))
            .boxed(),
        "STRING.replaceAll" | "STRING.replaceFirst" => (haystack_and_needle(), any_string(2))
            .prop_map(|((haystack, needle), replacement)| {
                vec![Arg::Str(haystack), Arg::Str(needle), Arg::Str(replacement)]
            })
            .boxed(),
        "STRING.replace" => (
            haystack_and_needle(),
            any_string(2),
            prop_oneof![4 => (-2i64..5).prop_map(BigInt::from), 1 => parameter(true)],
        )
            .prop_map(|((haystack, needle), replacement, count)| {
                vec![
                    Arg::Str(haystack),
                    Arg::Str(needle),
                    Arg::Str(replacement),
                    Arg::Int(count),
                ]
            })
            .boxed(),
        "STRING.countAllOccurrences" => haystack_and_needle()
            .prop_map(|(haystack, needle)| vec![Arg::Str(haystack), Arg::Str(needle)])
            .boxed(),
        "STRING.token2string" => select(vec!["x", "foo", "Foo1", "a_b", "'q", "\"quoted\""])
            .prop_map(|token| vec![Arg::Id(token.to_owned())])
            .boxed(),
        "STRING.float2string" | "FLOAT.float2int" => {
            any_float().prop_map(|a| vec![Arg::Float(a)]).boxed()
        }
        "STRING.floatFormat" => (
            any_float(),
            prop_oneof![
                3 => (0u32..6).prop_map(|digits| format!("%.{digits}Rf")),
                1 => select(vec![
                    "%Rf", "%.3RNe", "%s", "%Rf %Rf", "%*Rf", "x=%.1Rf%%", "%", "%d", "%.2RZf",
                    "plain",
                ])
                .prop_map(str::to_owned),
            ],
        )
            .prop_map(|(value, format)| vec![Arg::Float(value), Arg::Str(format)])
            .boxed(),
        "STRING.string2float" => float_text().prop_map(|text| vec![Arg::Str(text)]).boxed(),
        _ if hook.starts_with("STRING.") => prop_oneof![
            (any_string(3), any_string(3)).prop_map(|(a, b)| vec![Arg::Str(a), Arg::Str(b)]),
            any_string(3).prop_map(|a| vec![Arg::Str(a.clone()), Arg::Str(a)]),
            (any_string(3), any_string(2))
                .prop_map(|(a, b)| vec![Arg::Str(a.clone()), Arg::Str(format!("{a}{b}"))]),
        ]
        .boxed(),
        "FLOAT.root" => (
            any_float(),
            prop_oneof![
                3 => Just(big(2)),
                2 => (-3i64..6).prop_map(BigInt::from),
                1 => select(vec![pow2(31) - 1, pow2(31), -pow2(31), -pow2(31) - 1]),
            ],
        )
            .prop_map(|(value, degree)| vec![Arg::Float(value), Arg::Int(degree)])
            .boxed(),
        "FLOAT.round" => (any_float(), context())
            .prop_map(|(value, (precision, exponent_bits))| {
                vec![
                    Arg::Float(value),
                    Arg::Int(precision),
                    Arg::Int(exponent_bits),
                ]
            })
            .boxed(),
        "FLOAT.int2float" => (any_int(), context())
            .prop_map(|(value, (precision, exponent_bits))| {
                vec![
                    Arg::Int(value),
                    Arg::Int(precision),
                    Arg::Int(exponent_bits),
                ]
            })
            .boxed(),
        "FLOAT.maxValue" | "FLOAT.minValue" => context()
            .prop_map(|(precision, exponent_bits)| {
                vec![Arg::Int(precision), Arg::Int(exponent_bits)]
            })
            .boxed(),
        _ if hook.starts_with("FLOAT.") => {
            match HOOKS.iter().find(|entry| entry.0 == hook).unwrap().1.len() {
                1 => any_float().prop_map(|a| vec![Arg::Float(a)]).boxed(),
                _ => float_pair(),
            }
        }
        _ => panic!("no argument strategy for {hook}"),
    }
}

// ---- oracles -------------------------------------------------------------------------------

/// The backend's verdict, or `None` when it has no evaluator for the case.
fn backend_expectation(
    hook: &str,
    arguments: &[Arg],
    result: Kind,
) -> Result<Option<Expect>, String> {
    let terms = arguments.iter().map(Arg::domain_value).collect::<Vec<_>>();
    let outcome = evaluate_hook(hook, &terms)
        .map_err(|stop| format!("the backend stopped without a deadline: {stop:?}"))?;
    match outcome {
        Ok(BuiltinResult::Value(value)) => {
            decode_backend(&value, result).map(Expect::Value).map(Some)
        }
        Ok(BuiltinResult::Bottom) => Ok(Some(Expect::Undefined)),
        Ok(BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })) => {
            Ok(Some(Expect::Unspecified))
        }
        // The hooks of the table that refuse a result as too large are `^Int`, `<<Int` and
        // `bitRangeInt`, whose bound is `result_size_limit(MAX_INT_RESULT_BITS, ..)`, never below
        // `MAX_INT_RESULT_BITS`; that is at least the fold's `MAX_FOLDED_BITS` (asserted in
        // `constant_folding.rs`), so a value the backend refuses is one the fold must refuse too.
        Ok(BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })) => {
            Ok(Some(Expect::TooLarge))
        }
        Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented
            | UnsupportedHookReason::ArgumentOutOfRange { .. },
        )) => Ok(None),
        // Without a result sort the backend cannot name the token's sort.
        Ok(BuiltinResult::NotApplicable) if hook == "STRING.string2token" => Ok(None),
        Err(BuiltinError::MismatchedFloatFormats { .. }) => Ok(Some(Expect::Undefined)),
        Err(
            BuiltinError::UnsupportedFloatFormat { .. }
            | BuiltinError::UnsupportedFloatFormatParameters { .. },
        ) => Ok(None),
        other => Err(format!("unexpected backend outcome {other:?}")),
    }
}

/// The documented syntax of `String2Int`: a nonempty sequence of decimal digits, optionally
/// prefixed by a sign.
fn is_integer_text(text: &str) -> bool {
    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
}

/// The documented syntax of `String2Base`: the digits of the base, letters in either case. A
/// sign is read as for `String2Int`, which the documentation does not exclude.
fn is_base_text(text: &str, radix: u32) -> bool {
    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
    !digits.is_empty() && digits.chars().all(|character| character.is_digit(radix))
}

/// Expectations derived from a hook's documentation that bind both evaluators: they are checked
/// against the backend as well as the fold.
fn documented_expectation(hook: &str, arguments: &[Arg]) -> Option<Expect> {
    match hook {
        "STRING.string2int" => {
            let text = arguments[0].str();
            Some(if is_integer_text(text) {
                Expect::Value(Out::Int(text.parse().ok()?))
            } else {
                Expect::Undefined
            })
        }
        "STRING.string2base" | "STRING.base2string" => {
            let Some(radix) = arguments[1]
                .int()
                .to_u32()
                .filter(|radix| (2..=36).contains(radix))
            else {
                // Bases run from 2 to 36.
                return Some(Expect::Undefined);
            };
            if hook == "STRING.base2string" {
                return None;
            }
            let text = arguments[0].str();
            Some(if is_base_text(text, radix) {
                Expect::Value(Out::Int(BigInt::parse_bytes(text.as_bytes(), radix)?))
            } else {
                Expect::Undefined
            })
        }
        _ => None,
    }
}

/// The first position at or after `index` (`findChar`), or the last at or before it (`rfind`,
/// `rfindChar`), holding the needle or one of the needle characters; -1 if there is none. Every
/// integer index is one: the candidates are the positions on that side of it.
fn search(hook: &str, haystack: &str, needles: &str, index: &BigInt) -> i64 {
    let haystack = haystack.chars().collect::<Vec<_>>();
    let needle = needles.chars().collect::<Vec<_>>();
    let occurs_at = |position: usize| match hook {
        "STRING.rfind" => haystack[position..].starts_with(&needle),
        _ => position < haystack.len() && needle.contains(&haystack[position]),
    };
    let mut positions = (0..=haystack.len()).filter(|&position| {
        let position = BigInt::from(position);
        match hook {
            "STRING.findChar" => position >= *index,
            _ => position <= *index,
        }
    });
    let found = match hook {
        "STRING.findChar" => positions.find(|&position| occurs_at(position)),
        _ => positions.rfind(|&position| occurs_at(position)),
    };
    found.map_or(-1, |position| position as i64)
}

/// Replaces the first `count` non-overlapping occurrences of a nonempty `needle`, scanning
/// characters left to right.
fn replace(haystack: &str, needle: &str, replacement: &str, count: usize) -> (String, usize) {
    let haystack = haystack.chars().collect::<Vec<_>>();
    let needle = needle.chars().collect::<Vec<_>>();
    let mut output = String::new();
    let mut replaced = 0;
    let mut position = 0;
    while position < haystack.len() {
        if replaced < count && haystack[position..].starts_with(&needle) {
            output.push_str(replacement);
            position += needle.len();
            replaced += 1;
        } else {
            output.push(haystack[position]);
            position += 1;
        }
    }
    (output, replaced)
}

fn standard_float(token: &str) -> Option<Fl> {
    match decode_float(token).ok()? {
        Out::Float(value) => Some(value),
        _ => None,
    }
}

fn exponent_field(value: Fl) -> i64 {
    match value {
        Fl::B32(value) => i64::from((value.to_bits() >> 23) & 0xff) - 127,
        Fl::B64(value) => i64::from(((value.to_bits() >> 52) & 0x7ff) as u32) - 1023,
    }
}

fn in_format(like: Fl, value: f64) -> Fl {
    match like {
        Fl::B32(_) => Fl::B32(value as f32),
        Fl::B64(_) => Fl::B64(value),
    }
}

/// The documented `Float` token syntax.
fn is_float_text(text: &str) -> bool {
    static SYNTAX: std::sync::LazyLock<regex::Regex> = std::sync::LazyLock::new(|| {
        let suffix = r"([fFdD]|[pP][0-9]+[xX][0-9]+)?";
        regex::Regex::new(&format!(
            r"^(([+-]?[0-9]+(\.[0-9]*)?|\.[0-9]+)([eE][+-]?[0-9]+)?{suffix}|[+-]?Infinity{suffix}|NaN{suffix})$"
        ))
        .unwrap()
    });
    SYNTAX.is_match(text)
}

/// A finite `f64` as `mantissa * 2^exponent` with an integer mantissa.
fn exact_parts(value: f64) -> (BigInt, i32) {
    let bits = value.to_bits();
    let field = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1 << 52) - 1);
    let (mantissa, exponent) = if field == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1 << 52), field - 1075)
    };
    let mantissa = BigInt::from(mantissa);
    (if value < 0.0 { -mantissa } else { mantissa }, exponent)
}

/// `value * 2^exponent` for a product that is representable, scaling in exact steps.
fn scale(mut value: f64, mut exponent: i32) -> f64 {
    while exponent != 0 {
        let step = exponent.clamp(-1000, 1000);
        value *= 2f64.powi(step);
        exponent -= step;
    }
    value
}

/// The IEEE remainder `x - n y`, with `n` the integer nearest `x / y` (ties to even), computed
/// in exact integer arithmetic. The result is exactly representable in the operands' format.
fn ieee_remainder(x: Fl, y: Fl) -> Fl {
    let (a, b) = (x.as_f64(), y.as_f64());
    if a.is_nan() || b.is_nan() || a.is_infinite() || b == 0.0 {
        return in_format(x, f64::NAN);
    }
    if b.is_infinite() {
        return x;
    }
    let ((a_mantissa, a_exponent), (b_mantissa, b_exponent)) = (exact_parts(a), exact_parts(b));
    let exponent = a_exponent.min(b_exponent);
    // x = numerator 2^exponent and y = denominator 2^exponent, with the sign of y moved to x.
    let sign = if b_mantissa.is_negative() { -1 } else { 1 };
    let numerator = a_mantissa * BigInt::from(sign) * pow2((a_exponent - exponent) as u32);
    let denominator = b_mantissa.abs() * pow2((b_exponent - exponent) as u32);
    let mut floor = &numerator / &denominator;
    if numerator.is_negative() && !(&numerator % &denominator).is_zero() {
        floor -= 1;
    }
    let twice_fraction: BigInt = (&numerator - &floor * &denominator) * 2;
    let nearest = match twice_fraction.cmp(&denominator) {
        std::cmp::Ordering::Less => floor,
        std::cmp::Ordering::Greater => floor + 1,
        std::cmp::Ordering::Equal if (&floor % BigInt::from(2)).is_zero() => floor,
        std::cmp::Ordering::Equal => floor + 1,
    };
    let remainder = (numerator - nearest * denominator) * BigInt::from(sign);
    let value = scale(remainder.to_f64().unwrap(), exponent);
    let (value_mantissa, value_exponent) = exact_parts(value);
    let common = exponent.min(value_exponent);
    assert_eq!(
        value_mantissa * pow2((value_exponent - common) as u32),
        remainder * pow2((exponent - common) as u32),
        "the remainder of {a} and {b} is exact"
    );
    let value = if value == 0.0 {
        0.0f64.copysign(a)
    } else {
        value
    };
    in_format(x, value)
}

/// The model for hooks the backend does not evaluate.
fn model_expectation(hook: &str, arguments: &[Arg]) -> Expect {
    let value = |out| Expect::Value(out);
    if let [Arg::Float(a), Arg::Float(b)] = arguments
        && let (Some(a), Some(b)) = (standard_float(a), standard_float(b))
        && !matches!((a, b), (Fl::B32(_), Fl::B32(_)) | (Fl::B64(_), Fl::B64(_)))
        && HOOKS
            .iter()
            .any(|entry| entry.0 == hook && entry.2 == Kind::Float)
    {
        // A binary Float operation rounds to its operands' common precision and exponent
        // width, so operands of two formats have no result. Comparisons need no format.
        return Expect::Undefined;
    }
    if let Some(libm) = libm_model(hook, arguments) {
        return value(Out::Float(libm));
    }
    match hook {
        "STRING.rfind" | "STRING.findChar" | "STRING.rfindChar" => value(Out::Int(
            search(
                hook,
                arguments[0].str(),
                arguments[1].str(),
                arguments[2].int(),
            )
            .into(),
        )),
        "STRING.replaceAll" | "STRING.replaceFirst" | "STRING.replace" => {
            let count = match hook {
                "STRING.replaceAll" => usize::MAX,
                "STRING.replaceFirst" => 1,
                _ if arguments[3].int().is_negative() => return Expect::Undefined,
                _ => arguments[3].int().to_usize().unwrap_or(usize::MAX),
            };
            let (haystack, needle, replacement) =
                (arguments[0].str(), arguments[1].str(), arguments[2].str());
            if needle.is_empty() {
                // `domains.md` defines `replace` by finding the needle at 0 and recursing on
                // the whole haystack, so an empty needle inserts the replacement `count` times
                // in front; `replaceAll` replaces `countAllOccurrences` copies, which has no value
                // for an empty needle (below).
                let bytes = (count as u128) * (replacement.len() as u128) + haystack.len() as u128;
                return match hook {
                    "STRING.replaceAll" => Expect::Unspecified,
                    _ if bytes * 8 > u128::from(MAX_FOLDED_BITS) => Expect::TooLarge,
                    _ => value(Out::Str(
                        format!("{}{haystack}", replacement.repeat(count)).into_bytes(),
                    )),
                };
            }
            let (output, _) = replace(haystack, needle, replacement, count);
            value(Out::Str(output.into_bytes()))
        }
        "STRING.countAllOccurrences" => {
            let (haystack, needle) = (arguments[0].str(), arguments[1].str());
            if needle.is_empty() {
                // `domains.md` counts by finding the needle and recursing on the rest: for an
                // empty needle `countAllOccurrences(S, "") = 1 +Int countAllOccurrences(S, "")`,
                // which no integer satisfies, and the hook is total.
                return Expect::Unspecified;
            }
            value(Out::Int(replace(haystack, needle, "", usize::MAX).1.into()))
        }
        "STRING.string2token" => value(Out::Id(arguments[0].str().to_owned())),
        "STRING.string2float" => {
            let text = arguments[0].str();
            if !is_float_text(text) {
                return Expect::Undefined;
            }
            decode_float(text)
                .ok()
                .filter(|out| matches!(out, Out::Float(_)))
                .map_or(Expect::Unchecked, Expect::Value)
        }
        "STRING.float2string" => match standard_float(arguments[0].float()) {
            // The documented contract: the string reads back as the same Float.
            Some(float) => value(Out::Float(float)),
            None => Expect::Unchecked,
        },
        "STRING.floatFormat" => {
            let format = arguments[1].str();
            let Some(float) = standard_float(arguments[0].float()) else {
                return Expect::Unchecked;
            };
            let digits = format
                .strip_prefix("%.")
                .and_then(|rest| rest.strip_suffix("Rf"))
                .and_then(|digits| digits.parse::<usize>().ok());
            match digits {
                Some(digits) if float.as_f64().is_finite() => value(Out::Str(
                    format!("{:.digits$}", float.as_f64()).into_bytes(),
                )),
                _ => Expect::Unchecked,
            }
        }
        "FLOAT.exponent" => match standard_float(arguments[0].float()) {
            Some(float) => value(Out::Int(exponent_field(float).into())),
            None => Expect::Unchecked,
        },
        "FLOAT.minValue" => match (arguments[0].int().to_u32(), arguments[1].int().to_u32()) {
            (Some(24), Some(8)) => value(Out::Float(Fl::B32(f32::from_bits(1)))),
            (Some(53), Some(11)) => value(Out::Float(Fl::B64(f64::from_bits(1)))),
            _ => Expect::Unchecked,
        },
        "FLOAT.ne" => match (
            standard_float(arguments[0].float()),
            standard_float(arguments[1].float()),
        ) {
            (Some(a), Some(b)) => value(Out::Bool(a.as_f64() != b.as_f64())),
            _ => Expect::Unchecked,
        },
        "FLOAT.rem" => match (
            standard_float(arguments[0].float()),
            standard_float(arguments[1].float()),
        ) {
            (Some(a), Some(b))
                if matches!((a, b), (Fl::B32(_), Fl::B32(_)) | (Fl::B64(_), Fl::B64(_))) =>
            {
                value(Out::Float(ieee_remainder(a, b)))
            }
            _ => Expect::Unchecked,
        },
        _ => Expect::Unchecked,
    }
}

/// Hooks whose model is the platform's `f64` math library, accurate to one unit in the last
/// place rather than correctly rounded.
fn libm_model(hook: &str, arguments: &[Arg]) -> Option<Fl> {
    let operation: fn(f64, f64) -> f64 = match hook {
        "FLOAT.exp" => |x, _| x.exp(),
        "FLOAT.log" => |x, _| x.ln(),
        "FLOAT.sin" => |x, _| x.sin(),
        "FLOAT.cos" => |x, _| x.cos(),
        "FLOAT.tan" => |x, _| x.tan(),
        "FLOAT.asin" => |x, _| x.asin(),
        "FLOAT.acos" => |x, _| x.acos(),
        "FLOAT.atan" => |x, _| x.atan(),
        "FLOAT.pow" => f64::powf,
        "FLOAT.atan2" => f64::atan2,
        _ => return None,
    };
    let first = standard_float(arguments[0].float())?;
    let second = match arguments.get(1) {
        Some(argument) => {
            let second = standard_float(argument.float())?;
            if !matches!(
                (first, second),
                (Fl::B32(_), Fl::B32(_)) | (Fl::B64(_), Fl::B64(_))
            ) {
                return None;
            }
            second.as_f64()
        }
        None => 0.0,
    };
    Some(in_format(first, operation(first.as_f64(), second)))
}

#[derive(Default, Debug)]
struct Tally {
    values: usize,
    undefined: usize,
    too_large: usize,
    unspecified: usize,
    unchecked: usize,
}

fn check_case(
    folder: &Folder<'_, '_>,
    hook: &str,
    result: Kind,
    arguments: &[Arg],
    tally: &mut Tally,
) -> Result<(), String> {
    let tokens = arguments.iter().map(Arg::token).collect::<Vec<_>>();
    let folded = folder.try_fold(&Label::new(label(hook)), &tokens);
    let folded = match folded {
        // The documented contract of `Float2String` is that its string reads back as the same
        // Float, so the folded string is compared as a Float.
        Ok(Some(term)) if hook == "STRING.float2string" => match decode_folded(&term, result)? {
            Out::Str(text) => Ok(decode_float(&String::from_utf8(text).unwrap())?),
            other => return Err(format!("Float2String folded to {other:?}")),
        },
        Ok(Some(term)) => Ok(decode_folded(&term, result)?),
        Ok(None) => return Err("the fold left a constant hooked application unfolded".into()),
        Err(message) => Err(message),
    };

    let backend = backend_expectation(hook, arguments, result)?;
    let expected = match documented_expectation(hook, arguments) {
        Some(documented) => {
            match (&documented, &backend) {
                (Expect::Value(a), Some(Expect::Value(b))) if a.same(b) => {}
                (Expect::Undefined, Some(Expect::Undefined)) | (_, None) => {}
                _ => {
                    return Err(format!(
                        "the backend gives {backend:?} where the hook's documentation gives {documented:?}"
                    ));
                }
            }
            documented
        }
        None => backend.unwrap_or_else(|| model_expectation(hook, arguments)),
    };

    match (expected, folded) {
        (Expect::Value(expected), Ok(folded)) => {
            let agrees = match (&expected, &folded) {
                (Out::Float(expected), Out::Float(folded)) if uses_libm(hook) => {
                    folded.within_one_ulp(*expected)
                }
                _ => expected.same(&folded),
            };
            if !agrees {
                return Err(format!(
                    "the fold gives {folded:?}, the oracle {expected:?}"
                ));
            }
            tally.values += 1;
        }
        // The fold writes no value larger than its own bound, which the backend may compute.
        (Expect::Value(expected), Err(Unfolded::TooLarge(_)))
            if expected.bits() > MAX_FOLDED_BITS =>
        {
            tally.too_large += 1;
        }
        (Expect::Value(expected), Err(unfolded)) => {
            return Err(format!(
                "the fold leaves {unfolded:?} where the oracle gives {expected:?}"
            ));
        }
        (Expect::Undefined, Ok(folded)) => {
            return Err(format!(
                "the fold gives {folded:?} where the hook is undefined"
            ));
        }
        (Expect::Undefined, Err(Unfolded::Undefined(_))) => tally.undefined += 1,
        (Expect::TooLarge, Err(Unfolded::TooLarge(_))) => tally.too_large += 1,
        (Expect::Unspecified, Err(Unfolded::Unspecified(_))) => tally.unspecified += 1,
        (Expect::Unspecified, folded) => {
            return Err(format!(
                "the fold gives {folded:?} where the hook's value is unspecified"
            ));
        }
        (Expect::TooLarge, folded) => {
            return Err(format!(
                "the fold gives {folded:?} where the value is larger than the result bound"
            ));
        }
        (Expect::Undefined, Err(unfolded)) => {
            return Err(format!(
                "the fold leaves {unfolded:?} where the hook is undefined"
            ));
        }
        (Expect::Unchecked, _) => tally.unchecked += 1,
    }
    Ok(())
}

/// Hooks whose transcendental results the oracle checks only to one unit in the last place.
fn uses_libm(hook: &str) -> bool {
    matches!(
        hook,
        "FLOAT.exp"
            | "FLOAT.log"
            | "FLOAT.sin"
            | "FLOAT.cos"
            | "FLOAT.tan"
            | "FLOAT.asin"
            | "FLOAT.acos"
            | "FLOAT.atan"
            | "FLOAT.pow"
            | "FLOAT.atan2"
    )
}

/// Runs every hook in the table through `CASES` deterministic random cases and returns one line
/// per hook that disagrees with its oracle.
fn disagreements(hooks: &[(&'static str, &'static [Kind], Kind)]) -> Vec<String> {
    let definition = definition();
    let resolved = ResolvedDefinition::resolve(&definition).expect("the hook module resolves");
    let views = resolved.views();
    let folder = Folder::new(&views, resolved.module_id("MAIN").unwrap());
    let mut failures = Vec::new();
    let mut summary = Vec::new();
    for (hook, _, result) in hooks {
        let mut runner = TestRunner::new_with_rng(
            Config {
                cases: CASES,
                failure_persistence: None,
                ..Config::default()
            },
            TestRng::deterministic_rng(RngAlgorithm::ChaCha),
        );
        let tally = std::cell::RefCell::new(Tally::default());
        let outcome = runner.run(&arguments(hook), |arguments| {
            check_case(&folder, hook, *result, &arguments, &mut tally.borrow_mut())
                .map_err(|message| TestCaseError::fail(format!("{arguments:?}: {message}")))
        });
        let tally = tally.into_inner();
        match outcome {
            Ok(()) => {
                // Every hook must reach its value comparison.
                if tally.values == 0 {
                    failures.push(format!("{hook}: no case compared a folded value {tally:?}"));
                }
            }
            Err(error) => failures.push(format!("{hook}: {error}")),
        }
        summary.push(format!("{hook} {tally:?}"));
    }
    eprintln!("{}", summary.join("\n"));
    failures
}

#[cfg(feature = "mpfr-folding")]
#[test]
fn constant_folding_agrees_with_the_backend_hooks() {
    let failures = disagreements(HOOKS);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Without MPFR the fold leaves every `FLOAT` hook (and the `STRING` conversions to and from
/// `Float`) unfolded; the other hooks are compared as with MPFR.
#[cfg(not(feature = "mpfr-folding"))]
#[test]
fn constant_folding_agrees_with_the_backend_hooks() {
    let (float, other): (Vec<_>, Vec<_>) =
        HOOKS.iter().copied().partition(|(_, arguments, result)| {
            arguments.contains(&Kind::Float) || *result == Kind::Float
        });
    let failures = disagreements(&other);
    assert!(failures.is_empty(), "{}", failures.join("\n"));

    let definition = definition();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let views = resolved.views();
    let folder = Folder::new(&views, resolved.module_id("MAIN").unwrap());
    for (hook, arguments, _) in float {
        let tokens = arguments
            .iter()
            .map(|kind| match kind {
                Kind::Float => Arg::Float("1.5".into()),
                Kind::Int => Arg::Int(BigInt::from(53)),
                Kind::Str => Arg::Str("1.5".into()),
                other => panic!("unexpected argument kind {other:?}"),
            })
            .map(|argument| argument.token())
            .collect::<Vec<_>>();
        let unfolded = folder
            .try_fold(&Label::new(label(hook)), &tokens)
            .expect_err(hook);
        assert!(
            matches!(&unfolded, Unfolded::Unsupported(message)
                if message.contains("requires the native MPFR implementation")),
            "{hook}: {unfolded:?}"
        );
    }
}
