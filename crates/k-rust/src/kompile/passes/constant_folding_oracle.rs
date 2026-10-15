//! Oracle test for the MPFR fold of `kompile.constant_folding.evaluate`: every `FLOAT` hook in
//! the folding table, and every `STRING` conversion to and from `Float`, applied to random
//! constant arguments, either folds to the value the backend's own evaluator computes
//! (`k_rust_backend::builtin::evaluate_hook`) or is rejected where that evaluator finds the hook
//! undefined. Hooks the backend does not evaluate are compared with a small model in this file,
//! written from the hook's documented meaning. The MPFR fold and the backend are independent
//! implementations of the same hook semantics, so a difference is a defect on one side.
//!
//! The other hooks are folded through the backend's evaluation entry itself (`Folder::evaluate`),
//! so they have no second implementation to compare.
//!
//! The folder is exercised through `float::fold` on one resolved definition that declares every
//! hooked production, so the case loop pays for neither a prelude nor a resolution.
#![allow(
    clippy::wildcard_enum_match_arm,
    reason = "the test classifies hook outcomes and only names the variants it distinguishes"
)]

use std::collections::BTreeMap;

use k_rust_backend::{
    builtin::{BuiltinResult, UnsupportedHookReason, evaluate_hook},
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

use super::{
    Folder, MAX_FOLDED_BITS,
    float::{self, Unfolded},
};
use crate::{
    definition::{
        Attributes, Definition, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::{Label, Sort, Term},
    kompile::declaration_facts::EmittedDeclarations,
};

/// Cases per hook. Each case costs one fold and one backend evaluation.
const CASES: u32 = 96;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    Bool,
    Int,
    Str,
    Float,
}

use Kind::{Bool as B, Float as F, Int as I, Str as S};

/// The MPFR folding table (`float::folds`): hook, argument kinds, result kind.
const HOOKS: &[(&str, &[Kind], Kind)] = &[
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
    Int(BigInt),
    Str(String),
    /// A `Float` token, such as `1.5e0`, `2.5e-1f`, `NaNp24x8` or `-Infinity`.
    Float(String),
}

impl Arg {
    fn token(&self) -> Term {
        let (token, sort) = match self {
            Self::Int(value) => (value.to_string(), "Int"),
            Self::Str(value) => (crate::kast::string::quote(value), "String"),
            Self::Float(value) => (value.clone(), "Float"),
        };
        Term::Token {
            token,
            sort: Sort::new(sort),
        }
    }

    fn domain_value(&self) -> BackendTerm {
        match self {
            Self::Int(value) => BackendTerm::int(value.clone()),
            Self::Str(value) => BackendTerm::string(value),
            // A `Float` value has no constructor of its own kind yet; the oracle's texts are
            // the canonical ones the hooks write.
            Self::Float(value) => BackendTerm::raw_domain_value(
                BackendSort::builtin(BuiltinSort::Float),
                value.clone(),
            ),
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
        }
    }

    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Int(a), Self::Int(b)) => a == b,
            (Self::Str(a), Self::Str(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => a.same(*b),
            (Self::FloatToken(a), Self::FloatToken(b)) => a == b,
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
    /// `Unspecified`), or the value is one the definition leaves to a reading k-rust applies
    /// only in an execution (a Float operation over two formats), so the fold must leave the
    /// application unfolded as unspecified.
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
    }
}

fn label(hook: &str) -> String {
    format!("hook_{}", hook.replace('.', "_"))
}

/// One module declaring the four hooked sorts and one function production per hook in the
/// table.
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
        })
    };
    let mut sentences = [
        ("Bool", "BOOL.Bool"),
        ("Int", "INT.Int"),
        ("String", "STRING.String"),
        ("Float", "FLOAT.Float"),
    ]
    .into_iter()
    .map(|(name, hook)| Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new(name),
        attributes: attributes(&[("hook", hook)]),
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

fn arguments(hook: &str) -> BoxedStrategy<Vec<Arg>> {
    match hook {
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
        // A backend bound on a result is never below the fold's `MAX_FOLDED_BITS` (asserted in
        // `constant_folding.rs`), so a value the backend refuses is one the fold must refuse too.
        Ok(BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })) => {
            Ok(Some(Expect::TooLarge))
        }
        Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented
            | UnsupportedHookReason::ArgumentOutOfRange { .. },
        )) => Ok(None),
        other => Err(format!("unexpected backend outcome {other:?}")),
    }
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

/// Whether `hook` is a Float-valued binary hook applied to a binary32 and a binary64 operand.
/// `domains.md` names no result format for it, and the backend's binary64 reading applies only
/// in an execution, so the fold, whose output proofs load too, must leave it unfolded as
/// unspecified. Comparisons need no format and are not included.
fn mixed_float_operation(hook: &str, arguments: &[Arg]) -> bool {
    if let [Arg::Float(a), Arg::Float(b)] = arguments
        && let (Some(a), Some(b)) = (standard_float(a), standard_float(b))
    {
        !matches!((a, b), (Fl::B32(_), Fl::B32(_)) | (Fl::B64(_), Fl::B64(_)))
            && HOOKS
                .iter()
                .any(|entry| entry.0 == hook && entry.2 == Kind::Float)
    } else {
        false
    }
}

/// Whether `hook` is `signFloat` applied to a NaN. The `NaN` literal is given no sign bit, and
/// the backend's `false` applies only in an execution, so the fold must leave it unfolded as
/// unspecified.
fn sign_of_a_nan(hook: &str, arguments: &[Arg]) -> bool {
    hook == "FLOAT.sign" && matches!(arguments, [Arg::Float(token)] if token.starts_with("NaN"))
}

/// The model for hooks the backend does not evaluate.
fn model_expectation(hook: &str, arguments: &[Arg]) -> Expect {
    let value = |out| Expect::Value(out);
    if mixed_float_operation(hook, arguments) {
        return Expect::Unspecified;
    }
    if let Some(libm) = libm_model(hook, arguments) {
        return value(Out::Float(libm));
    }
    match hook {
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
    let label = Label::new(label(hook));
    let application = folder
        .application(&label, &tokens)
        .ok_or("the fold does not read a constant hooked application")?;
    let folded = float::fold(
        folder.sorts,
        hook,
        &application.tokens,
        &application.result_sort,
    )
    .map(|token| {
        Some(Term::Token {
            token,
            sort: application.result_sort.clone(),
        })
    });
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
    // The backend computes k-rust's readings of a mixed-format operation (binary64) and of a
    // NaN's sign (false), values only an execution chooses and the fold must not write.
    let expected = if mixed_float_operation(hook, arguments) || sign_of_a_nan(hook, arguments) {
        Expect::Unspecified
    } else {
        backend.unwrap_or_else(|| model_expectation(hook, arguments))
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
    let main = resolved.module_id("MAIN").unwrap();
    let facts = EmittedDeclarations::new(views.sort_catalog(main), views.production_catalog(main));
    let folder = Folder::new(&views, main, &facts);
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

#[test]
fn constant_folding_agrees_with_the_backend_hooks() {
    assert!(HOOKS.iter().all(|(hook, _, _)| float::folds(hook)));
    let failures = disagreements(HOOKS);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
