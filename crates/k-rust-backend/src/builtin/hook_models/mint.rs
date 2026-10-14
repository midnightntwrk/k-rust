//! `MINT` against Rust's native fixed-width integers.
//!
//! A `MInt{W}` value is a `W`-bit pattern, read unsigned or in two's complement by the operation
//! (`domains.md`, "MInt"). The model computes each hook with the machine operations of a `W`-bit
//! integer: `u8`/`i8` to `u64`/`i64` for the native widths, and `u128`/`i128` masked to `W` bits
//! (signed readings by sign extension) for the others, so it shares no formula with the
//! evaluator, which reduces arbitrary-precision integers modulo `2^W`.

use std::sync::Arc;

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use k_rust_kore::names::{BuiltinSort, MINT_SORT};

use super::{Case, Draw, Env, Spec, Val, assert_reached, encode, evaluate, run, variable};
use crate::{
    builtin::{BuiltinError, BuiltinResult, UnsupportedHookReason},
    term::{
        DomainKind, FunctionType, Sort, Symbol, SymbolAttributes, SymbolType, Term, mint_width,
    },
};

const CASES: u32 = 4000;

/// The widths the model covers: those of Rust's native integers, and others it computes in
/// 128 bits. Widths above 128 are checked against an arbitrary-precision model below.
const WIDTHS: [u32; 9] = [8, 16, 32, 64, 1, 7, 65, 127, 128];

/// The total hooks whose arguments are all machine integers (`MINT.integer` takes its width from
/// the application's sort and is checked on applications below).
const TOTAL_HOOKS: [&str; 21] = [
    "MINT.svalue",
    "MINT.uvalue",
    "MINT.bitwidth",
    "MINT.add",
    "MINT.sub",
    "MINT.mul",
    "MINT.neg",
    "MINT.not",
    "MINT.and",
    "MINT.or",
    "MINT.xor",
    "MINT.eq",
    "MINT.ne",
    "MINT.ult",
    "MINT.ule",
    "MINT.ugt",
    "MINT.uge",
    "MINT.slt",
    "MINT.sle",
    "MINT.sgt",
    "MINT.sge",
];

/// The partial hooks: division and remainder are undefined at a zero divisor, and the shifts are
/// declared without `total` although every amount gives them a value.
const PARTIAL_HOOKS: [&str; 7] = [
    "MINT.udiv",
    "MINT.urem",
    "MINT.sdiv",
    "MINT.srem",
    "MINT.shl",
    "MINT.ashr",
    "MINT.lshr",
];

fn arity(hook: &str) -> usize {
    match hook {
        "MINT.svalue" | "MINT.uvalue" | "MINT.bitwidth" | "MINT.neg" | "MINT.not" => 1,
        _ => 2,
    }
}

pub(super) fn mint_sort(width: impl std::fmt::Display) -> Sort {
    Sort::application(MINT_SORT, vec![Sort::simple(format!("Sort{width}"))])
}

fn mint(width: u32, value: u128) -> Val {
    Val::MInt(u64::from(width), BigInt::from(value))
}

fn mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1 << width) - 1
    }
}

/// An operand of width `width`: an edge of the carrier (0, 1, the largest pattern, the least and
/// the greatest signed value), or a random pattern.
fn pattern(draw: &mut Draw<'_>, width: u32) -> u128 {
    let top = 1_u128 << (width - 1);
    let random = u128::from(draw.u64()) << 64 | u128::from(draw.u64());
    let value = match draw.below(8) {
        0 => 0,
        1 => 1,
        2 => mask(width),
        3 => top,
        4 => top - 1,
        _ => random,
    };
    value & mask(width)
}

/// A shift amount of width `width`: mostly near the width, where the result changes shape.
fn amount(draw: &mut Draw<'_>, width: u32) -> u128 {
    let width = u128::from(width);
    let value = match draw.below(4) {
        0 => draw.pick(&[0, 1, width - 1, width, width + 1]),
        1 => u128::from(draw.u64()) % width,
        _ => return pattern(draw, width as u32),
    };
    value & mask(width as u32)
}

fn mint_case(draw: &mut Draw<'_>, hooks: &[&'static str]) -> Case {
    let hook = draw.pick(hooks);
    let width = draw.pick(&WIDTHS);
    let mut env = Env::new();
    let mut arguments: Vec<Term> = Vec::new();
    for _ in 0..arity(hook) {
        let argument = if !arguments.is_empty() && draw.chance(2) {
            // The same argument twice: equality is reflexive whatever it denotes.
            arguments[0].clone()
        } else {
            let value = if !arguments.is_empty()
                && matches!(hook, "MINT.shl" | "MINT.ashr" | "MINT.lshr")
            {
                amount(draw, width)
            } else {
                pattern(draw, width)
            };
            draw.scalar(encode(&mint(width, value)), mint_sort(width), &mut env)
        };
        arguments.push(argument);
    }
    Case {
        hook,
        arguments,
        env,
    }
}

/// A hook's value on `W`-bit operands `a` and `b`, read as the native unsigned type `$u` and its
/// signed counterpart `$s`; the results are patterns in `u128`.
macro_rules! native {
    ($u:ty, $s:ty, $hook:expr, $width:expr, $a:expr, $b:expr) => {{
        let (a, b) = ($a as $u, $b as $u);
        let (sa, sb) = (a as $s, b as $s);
        native_result(
            $hook,
            $width,
            a as u128,
            sa as i128,
            [
                a.wrapping_add(b) as u128,
                a.wrapping_sub(b) as u128,
                a.wrapping_mul(b) as u128,
                a.wrapping_neg() as u128,
                (!a) as u128,
                (a & b) as u128,
                (a | b) as u128,
                (a ^ b) as u128,
            ],
            [a == b, a < b, a <= b, a > b, a >= b],
            [sa < sb, sa <= sb, sa > sb, sa >= sb],
        )
    }};
}

/// The model of a total hook from the native results: the unsigned and signed readings of the
/// first operand; the patterns of `+ - * -- ~ & | xor`; `== < <= > >=` unsigned; and
/// `< <= > >=` signed.
fn native_result(
    hook: &str,
    width: u32,
    unsigned: u128,
    signed: i128,
    patterns: [u128; 8],
    unsigned_comparisons: [bool; 5],
    signed_comparisons: [bool; 4],
) -> Val {
    let [add, sub, mul, neg, not, and, or, xor] = patterns;
    let [eq, ult, ule, ugt, uge] = unsigned_comparisons;
    let [slt, sle, sgt, sge] = signed_comparisons;
    match hook {
        "MINT.svalue" => Val::int(signed),
        "MINT.uvalue" => Val::int(unsigned),
        "MINT.add" => mint(width, add),
        "MINT.sub" => mint(width, sub),
        "MINT.mul" => mint(width, mul),
        "MINT.neg" => mint(width, neg),
        "MINT.not" => mint(width, not),
        "MINT.and" => mint(width, and),
        "MINT.or" => mint(width, or),
        "MINT.xor" => mint(width, xor),
        "MINT.eq" => Val::Bool(eq),
        "MINT.ne" => Val::Bool(!eq),
        "MINT.ult" => Val::Bool(ult),
        "MINT.ule" => Val::Bool(ule),
        "MINT.ugt" => Val::Bool(ugt),
        "MINT.uge" => Val::Bool(uge),
        "MINT.slt" => Val::Bool(slt),
        "MINT.sle" => Val::Bool(sle),
        "MINT.sgt" => Val::Bool(sgt),
        "MINT.sge" => Val::Bool(sge),
        other => panic!("no native model of {other}"),
    }
}

/// A partial hook's value on `W`-bit operands `a` and `b` read as `$u` and `$s`, `None` where it
/// is undefined. `wrapping_div` gives `MIN` for `MIN / -1`; `wrapping_shl` masks the amount, so
/// the checked shifts give the value of an amount of `W` or more.
macro_rules! native_partial {
    ($u:ty, $s:ty, $hook:expr, $a:expr, $b:expr) => {{
        let (a, b) = ($a as $u, $b as $u);
        let (sa, sb) = (a as $s, b as $s);
        let amount = u32::try_from(b).ok();
        match $hook {
            "MINT.udiv" => a.checked_div(b),
            "MINT.urem" => a.checked_rem(b),
            "MINT.sdiv" => (b != 0).then(|| sa.wrapping_div(sb) as $u),
            "MINT.srem" => (b != 0).then(|| sa.wrapping_rem(sb) as $u),
            "MINT.shl" => Some(amount.and_then(|amount| a.checked_shl(amount)).unwrap_or(0)),
            "MINT.lshr" => Some(amount.and_then(|amount| a.checked_shr(amount)).unwrap_or(0)),
            "MINT.ashr" => Some(
                amount
                    .and_then(|amount| sa.checked_shr(amount))
                    .unwrap_or(if sa < 0 { -1 } else { 0 }) as $u,
            ),
            other => panic!("no native model of {other}"),
        }
        .map(|pattern| pattern as u128)
    }};
}

/// A partial hook's value in 128 bits, masked to `width`.
fn wide_partial(hook: &str, width: u32, a: u128, b: u128) -> Option<u128> {
    let m = mask(width);
    let (sa, sb) = (sign_extend(a, width), sign_extend(b, width));
    let beyond = b >= u128::from(width);
    match hook {
        "MINT.udiv" => a.checked_div(b),
        "MINT.urem" => a.checked_rem(b),
        "MINT.sdiv" => (b != 0).then(|| sa.wrapping_div(sb) as u128 & m),
        "MINT.srem" => (b != 0).then(|| sa.wrapping_rem(sb) as u128 & m),
        "MINT.shl" => Some(if beyond { 0 } else { a << b & m }),
        "MINT.lshr" => Some(if beyond { 0 } else { a >> b }),
        "MINT.ashr" => Some(if beyond {
            if sa < 0 { m } else { 0 }
        } else {
            (sa >> b) as u128 & m
        }),
        other => panic!("no native model of {other}"),
    }
}

/// The two's-complement reading of the `width`-bit pattern `value`, by sign extension.
fn sign_extend(value: u128, width: u32) -> i128 {
    let shift = 128 - width;
    ((value << shift) as i128) >> shift
}

/// The model in 128 bits, masked to `width`.
fn wide(hook: &str, width: u32, a: u128, b: u128) -> Val {
    let m = mask(width);
    let (sa, sb) = (sign_extend(a, width), sign_extend(b, width));
    native_result(
        hook,
        width,
        a,
        sa,
        [
            a.wrapping_add(b) & m,
            a.wrapping_sub(b) & m,
            a.wrapping_mul(b) & m,
            a.wrapping_neg() & m,
            !a & m,
            a & b,
            a | b,
            a ^ b,
        ],
        [a == b, a < b, a <= b, a > b, a >= b],
        [sa < sb, sa <= sb, sa > sb, sa >= sb],
    )
}

fn operand(value: &Val) -> (u32, u128) {
    let Val::MInt(width, value) = value else {
        panic!("not a machine integer: {value:?}")
    };
    (
        u32::try_from(*width).expect("a modelled width"),
        value.to_u128().expect("a modelled pattern"),
    )
}

fn mint_model(hook: &str, inputs: &[Val]) -> Spec {
    let (width, a) = operand(&inputs[0]);
    if hook == "MINT.bitwidth" {
        return Spec::value(Val::int(width));
    }
    let b = inputs.get(1).map_or(0, |input| {
        let (other, b) = operand(input);
        assert_eq!(other, width, "operands of one width");
        b
    });
    if PARTIAL_HOOKS.contains(&hook) {
        let result = match width {
            8 => native_partial!(u8, i8, hook, a, b),
            16 => native_partial!(u16, i16, hook, a, b),
            32 => native_partial!(u32, i32, hook, a, b),
            64 => native_partial!(u64, i64, hook, a, b),
            _ => wide_partial(hook, width, a, b),
        };
        return Spec::partial(result.map(|pattern| mint(width, pattern)));
    }
    Spec::value(match width {
        8 => native!(u8, i8, hook, width, a, b),
        16 => native!(u16, i16, hook, width, a, b),
        32 => native!(u32, i32, hook, width, a, b),
        64 => native!(u64, i64, hook, width, a, b),
        _ => wide(hook, width, a, b),
    })
}

#[test]
fn total_mint_hooks_agree_with_native_fixed_width_arithmetic() {
    let tallies = run(CASES, &|draw| mint_case(draw, &TOTAL_HOOKS), &mint_model);
    assert_reached(
        &tallies,
        &TOTAL_HOOKS,
        &["MINT.bitwidth", "MINT.eq", "MINT.ne"],
    );
}

/// Division, remainder and shifts: a zero divisor gives `\bottom`, signed division truncates
/// toward zero with the remainder of the dividend's sign, `MIN /sMInt -1` wraps to `MIN`, and a
/// shift by `W` or more gives 0, or all sign bits for `>>aMInt`.
#[test]
fn partial_mint_hooks_agree_with_native_fixed_width_arithmetic() {
    let tallies = run(CASES, &|draw| mint_case(draw, &PARTIAL_HOOKS), &mint_model);
    assert_reached(&tallies, &PARTIAL_HOOKS, &[]);
}

// ---------------------------------------------------------------------------------------------
// A width above 128 bits, against arbitrary-precision integers.

/// The width of the arbitrary-precision model, beyond every native integer.
const WIDE: u32 = 200;

/// `value` modulo `2^width`, in `[0, 2^width)`.
fn floor_mod(value: &BigInt, width: u32) -> BigInt {
    let modulus = BigInt::from(1) << width;
    ((value % &modulus) + &modulus) % &modulus
}

/// An operand of `WIDE` bits: an edge of the carrier or a random pattern of four `u64` draws.
fn wide_pattern(draw: &mut Draw<'_>) -> BigInt {
    let modulus = BigInt::from(1) << WIDE;
    let top = BigInt::from(1) << (WIDE - 1);
    let value = match draw.below(8) {
        0 => BigInt::from(0),
        1 => BigInt::from(1),
        2 => &modulus - 1,
        3 => top,
        4 => top - 1,
        5 => BigInt::from(draw.pick(&[WIDE - 1, WIDE, WIDE + 1, 3])),
        _ => (0..4).fold(BigInt::from(0), |value, _| {
            value << 64 | BigInt::from(draw.u64())
        }),
    };
    floor_mod(&value, WIDE)
}

fn wide_case(draw: &mut Draw<'_>) -> Case {
    let hook = if draw.chance(3) {
        draw.pick(&PARTIAL_HOOKS)
    } else {
        draw.pick(&TOTAL_HOOKS)
    };
    let mut env = Env::new();
    let arguments = (0..arity(hook))
        .map(|_| {
            let value = Val::MInt(u64::from(WIDE), wide_pattern(draw));
            draw.scalar(encode(&value), mint_sort(WIDE), &mut env)
        })
        .collect();
    Case {
        hook,
        arguments,
        env,
    }
}

/// The model from the definitions, on integers: `u` read from the pattern, `s` by subtracting
/// `2^W` above the top bit, results reduced by the floored remainder, bitwise operations bit by
/// bit, signed division from the magnitudes and the signs, and shifts as products and floored
/// quotients by `2^k`, with amounts of `W` or more taken separately.
fn wide_model(hook: &str, inputs: &[Val]) -> Spec {
    let w = WIDE;
    let value = |input: &Val| match input {
        Val::MInt(width, value) if *width == u64::from(w) => value.clone(),
        other => panic!("not a {w}-bit machine integer: {other:?}"),
    };
    let a = value(&inputs[0]);
    let b = inputs.get(1).map_or_else(|| BigInt::from(0), value);
    let top = BigInt::from(1) << (w - 1);
    let signed = |x: &BigInt| {
        if *x >= top {
            x - (BigInt::from(1) << w)
        } else {
            x.clone()
        }
    };
    let (sa, sb) = (signed(&a), signed(&b));
    let word = |x: BigInt| Val::MInt(u64::from(w), floor_mod(&x, w));
    let bitwise = |op: fn(bool, bool) -> bool| {
        word((0..u64::from(w)).fold(BigInt::from(0), |acc, bit| {
            if op(a.bit(bit), b.bit(bit)) {
                acc | (BigInt::from(1) << bit)
            } else {
                acc
            }
        }))
    };
    let magnitude = |x: &BigInt| {
        if x.sign() == Sign::Minus {
            -x
        } else {
            x.clone()
        }
    };
    let negative = |x: &BigInt| x.sign() == Sign::Minus;
    let beyond = b >= BigInt::from(w);
    let power = || BigInt::from(1) << b.to_u32().expect("an amount below the width");
    let floored = |x: &BigInt, d: &BigInt| (x - floor_mod_by(x, d)) / d;
    Spec::partial(Some(match hook {
        "MINT.bitwidth" => Val::int(w),
        "MINT.svalue" => Val::Int(sa),
        "MINT.uvalue" => Val::Int(a),
        "MINT.add" => word(a + b),
        "MINT.sub" => word(a - b),
        "MINT.mul" => word(a * b),
        "MINT.neg" => word(-a),
        "MINT.not" => word((BigInt::from(1) << w) - 1 - a),
        "MINT.and" => bitwise(|x, y| x && y),
        "MINT.or" => bitwise(|x, y| x || y),
        "MINT.xor" => bitwise(|x, y| x != y),
        "MINT.eq" => Val::Bool(a == b),
        "MINT.ne" => Val::Bool(a != b),
        "MINT.ult" => Val::Bool(a < b),
        "MINT.ule" => Val::Bool(a <= b),
        "MINT.ugt" => Val::Bool(a > b),
        "MINT.uge" => Val::Bool(a >= b),
        "MINT.slt" => Val::Bool(sa < sb),
        "MINT.sle" => Val::Bool(sa <= sb),
        "MINT.sgt" => Val::Bool(sa > sb),
        "MINT.sge" => Val::Bool(sa >= sb),
        "MINT.udiv" | "MINT.urem" | "MINT.sdiv" | "MINT.srem" if b == BigInt::from(0) => {
            return Spec::bottom();
        }
        "MINT.udiv" => word(floored(&a, &b)),
        "MINT.urem" => word(floor_mod_by(&a, &b)),
        "MINT.sdiv" => {
            let quotient = floored(&magnitude(&sa), &magnitude(&sb));
            word(if negative(&sa) != negative(&sb) {
                -quotient
            } else {
                quotient
            })
        }
        "MINT.srem" => {
            let remainder = floor_mod_by(&magnitude(&sa), &magnitude(&sb));
            word(if negative(&sa) { -remainder } else { remainder })
        }
        "MINT.shl" if beyond => word(BigInt::from(0)),
        "MINT.shl" => word(a * power()),
        "MINT.lshr" if beyond => word(BigInt::from(0)),
        "MINT.lshr" => word(floored(&a, &power())),
        "MINT.ashr" if beyond => word(if negative(&sa) {
            BigInt::from(-1)
        } else {
            BigInt::from(0)
        }),
        "MINT.ashr" => word(floored(&sa, &power())),
        other => panic!("no model of {other}"),
    }))
}

/// The remainder of `x` floored by the positive `d`, in `[0, d)`.
fn floor_mod_by(x: &BigInt, d: &BigInt) -> BigInt {
    ((x % d) + d) % d
}

#[test]
fn mint_hooks_agree_with_an_arbitrary_precision_model_above_128_bits() {
    let tallies = run(CASES, &wide_case, &wide_model);
    let hooks = TOTAL_HOOKS
        .iter()
        .chain(&PARTIAL_HOOKS)
        .copied()
        .collect::<Vec<_>>();
    assert_reached(&tallies, &hooks, &["MINT.bitwidth"]);
}

// ---------------------------------------------------------------------------------------------
// Applications: the width of `Int2MInt` is its result sort's.

/// `Int2MInt{W}(argument)` as `domains.md` declares it, `W` the sort argument `width`.
fn int2mint(width: Sort, argument: Term) -> Term {
    int2mint_declared(FunctionType::Total, width, argument)
}

/// An application to `argument` of a function hooked `MINT.integer` at `MInt{width}`, declared
/// `total` or not.
fn int2mint_declared(totality: FunctionType, width: Sort, argument: Term) -> Term {
    let parameter = Sort::Variable("W".into());
    Term::application(
        Arc::new(Symbol {
            name: "LblInt2MInt".into(),
            sort_variables: vec!["W".into()],
            argument_sorts: vec![Sort::builtin(BuiltinSort::Int)],
            result_sort: Sort::application(MINT_SORT, vec![parameter]),
            attributes: hooked_function("MINT.integer", totality),
        }),
        vec![width],
        vec![argument],
    )
}

/// An application to `argument`, of sort `MInt{width}`, of a function hooked `MINT.bitwidth`,
/// declared `total` or not.
fn bitwidth_declared(totality: FunctionType, width: Sort, argument: Term) -> Term {
    let parameter = Sort::Variable("W".into());
    Term::application(
        Arc::new(Symbol {
            name: "LblbitwidthMInt".into(),
            sort_variables: vec!["W".into()],
            argument_sorts: vec![Sort::application(MINT_SORT, vec![parameter])],
            result_sort: Sort::builtin(BuiltinSort::Int),
            attributes: hooked_function("MINT.bitwidth", totality),
        }),
        vec![width],
        vec![argument],
    )
}

fn hooked_function(hook: &str, totality: FunctionType) -> SymbolAttributes {
    let mut attributes = SymbolAttributes::constructor().with_declared_function(true);
    attributes.symbol_type = SymbolType::Function(totality);
    attributes.hook = Some(hook.into());
    attributes
}

fn evaluated(term: &Term) -> BuiltinResult {
    crate::builtin::evaluate(term)
        .expect("not stopped")
        .expect("no argument failure")
}

fn int(value: impl Into<BigInt>) -> Term {
    encode(&Val::Int(value.into()))
}

/// The literal `text` of the machine-integer sort of `width`, built with the kind a sort hooked
/// `MINT.MInt` of that width has, so its text is canonical (the residue modulo `2^width`).
pub(super) fn mint_term(width: impl std::fmt::Display, text: &str) -> Term {
    let sort = mint_sort(width);
    let width = mint_width(&sort).expect("a machine-integer sort of a numeral width");
    Term::domain_value_of(DomainKind::MInt(width), sort, text)
}

/// Whether `result` leaves the application unevaluated as one whose value the definition does
/// not determine, shown defined (`Some(true)`) or not (`Some(false)`).
fn unspecified(result: &BuiltinResult) -> Option<bool> {
    match result {
        BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { defined, .. }) => {
            Some(*defined)
        }
        _ => None,
    }
}

#[test]
fn int2mint_reduces_its_argument_modulo_the_width_of_its_sort() {
    let big = BigInt::from(1) << 200_u32;
    for (argument, expected) in [
        (BigInt::from(0), "0p8"),
        (BigInt::from(-1), "255p8"),
        (BigInt::from(-100), "156p8"),
        (&big + 3, "3p8"),
        (-big, "0p8"),
    ] {
        assert_eq!(
            evaluated(&int2mint(Sort::simple("Sort8"), int(argument.clone()))),
            BuiltinResult::Value(mint_term(8, expected)),
            "Int2MInt({argument}) at MInt{{8}}"
        );
    }
    assert_eq!(
        evaluated(&int2mint(Sort::simple("Sort64"), int(-1))),
        BuiltinResult::Value(mint_term(64, &format!("{}p64", u64::MAX))),
    );
    // Without an applied symbol there is no result sort, so no width.
    assert_eq!(
        evaluate("MINT.integer", &[int(5)]),
        Ok(BuiltinResult::NotApplicable)
    );
}

#[test]
fn bitwidth_of_a_variable_is_the_width_of_its_sort() {
    assert_eq!(
        evaluate("MINT.bitwidth", &[variable("X", mint_sort(8))]),
        Ok(BuiltinResult::Value(int(8)))
    );
}

/// `MInt{0}` has one element, `0p0`: every conversion into it is that element, and its signed
/// and unsigned readings are 0.
#[test]
fn width_zero_has_one_element() {
    let zero = mint_term(0, "0p0");
    assert_eq!(
        evaluated(&int2mint(Sort::simple("Sort0"), int(5))),
        BuiltinResult::Value(zero.clone())
    );
    for (hook, expected) in [
        ("MINT.svalue", int(0)),
        ("MINT.uvalue", int(0)),
        ("MINT.bitwidth", int(0)),
        ("MINT.not", zero.clone()),
        ("MINT.neg", zero.clone()),
    ] {
        assert_eq!(
            evaluate(hook, std::slice::from_ref(&zero)),
            Ok(BuiltinResult::Value(expected)),
            "{hook}"
        );
    }
    for hook in ["MINT.add", "MINT.sub", "MINT.mul", "MINT.xor"] {
        assert_eq!(
            evaluate(hook, &[zero.clone(), zero.clone()]),
            Ok(BuiltinResult::Value(zero.clone())),
            "{hook}"
        );
    }
    for (hook, expected) in [("MINT.slt", false), ("MINT.sle", true), ("MINT.ult", false)] {
        assert_eq!(
            evaluate(hook, &[zero.clone(), zero.clone()]),
            Ok(BuiltinResult::Value(encode(&Val::Bool(expected)))),
            "{hook}"
        );
    }
}

/// A sort `MInt{Foo}` names no width, so the hooks' description gives no value of a conversion
/// into it, nor a width of its elements. Only the declaration says whether the application has
/// a value all the same: that of a function declared `total` has one in every model, which the
/// definition does not determine, so it is defined; that of a function declared without `total`,
/// or a hook evaluated without a declaration, is not shown defined. A sort `MInt{W}` whose
/// argument is a sort variable has a width that is not fixed yet, and the application waits for
/// it.
#[test]
fn a_sort_without_a_numeral_width_leaves_the_total_conversions_unspecified() {
    let foo = Sort::simple("SortFoo");
    let no_width = Sort::application(MINT_SORT, vec![foo.clone()]);
    assert_eq!(
        unspecified(&evaluated(&int2mint(foo.clone(), int(5)))),
        Some(true)
    );
    for (totality, defined) in [(FunctionType::Total, true), (FunctionType::Partial, false)] {
        let conversion = evaluated(&int2mint_declared(totality, foo.clone(), int(5)));
        assert_eq!(
            unspecified(&conversion),
            Some(defined),
            "Int2MInt, {totality:?}: {conversion:?}"
        );
        let width = evaluated(&bitwidth_declared(
            totality,
            foo.clone(),
            variable("X", no_width.clone()),
        ));
        assert_eq!(
            unspecified(&width),
            Some(defined),
            "bitwidthMInt, {totality:?}: {width:?}"
        );
    }
    let result = evaluate("MINT.bitwidth", &[variable("X", no_width)]).unwrap();
    assert_eq!(unspecified(&result), Some(false), "{result:?}");

    let parameter = Sort::Variable("W".into());
    assert_eq!(
        evaluated(&int2mint(parameter.clone(), int(5))),
        BuiltinResult::NotApplicable
    );
    let open = Sort::application(MINT_SORT, vec![parameter]);
    assert_eq!(
        evaluate("MINT.bitwidth", &[variable("X", open)]),
        Ok(BuiltinResult::NotApplicable)
    );
}

/// The operands of one application have one sort: literals of two widths are an ill-sorted
/// application, which no loaded definition holds.
#[test]
fn two_widths_in_one_application_are_an_unexpected_sort() {
    let result =
        crate::builtin::evaluate_hook("MINT.add", &[mint_term(8, "1p8"), mint_term(16, "1p16")])
            .expect("not stopped");
    assert!(
        matches!(result, Err(BuiltinError::UnexpectedSort { .. })),
        "{result:?}"
    );
}

/// A result whose canonical text would be a decimal of about `W` bits, above the bound on the
/// integers the backend computes, is refused before it is built.
#[test]
fn a_wrapped_result_wider_than_the_result_bound_is_too_large() {
    let width = 1_u64 << 25;
    let too_large = |result: &BuiltinResult| {
        matches!(
            result,
            BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })
        )
    };
    let one = mint_term(width, &format!("1p{width}"));
    let zero = mint_term(width, &format!("0p{width}"));
    for (hook, arguments) in [
        ("MINT.neg", vec![one.clone()]),
        ("MINT.not", vec![zero.clone()]),
        ("MINT.sub", vec![zero.clone(), one.clone()]),
    ] {
        let result = evaluate(hook, &arguments).unwrap();
        assert!(too_large(&result), "{hook}: {result:?}");
    }
    let result = evaluated(&int2mint(Sort::simple(format!("Sort{width}")), int(-1)));
    assert!(too_large(&result), "{result:?}");
    // Results that do not wrap are computed at any width.
    assert_eq!(
        evaluate("MINT.add", &[one.clone(), one.clone()]),
        Ok(BuiltinResult::Value(mint_term(
            width,
            &format!("2p{width}")
        )))
    );
    assert_eq!(
        evaluate("MINT.neg", std::slice::from_ref(&zero)),
        Ok(BuiltinResult::Value(zero))
    );
    assert_eq!(
        evaluated(&int2mint(Sort::simple(format!("Sort{width}")), int(7))),
        BuiltinResult::Value(mint_term(width, &format!("7p{width}")))
    );
}

/// In `MInt{0}` every divisor is the one element 0, so every division and remainder is
/// undefined, and every shift gives that element.
#[test]
fn width_zero_divisions_are_undefined_and_shifts_are_zero() {
    let zero = mint_term(0, "0p0");
    let arguments = [zero.clone(), zero.clone()];
    for hook in ["MINT.udiv", "MINT.urem", "MINT.sdiv", "MINT.srem"] {
        assert_eq!(
            evaluate(hook, &arguments),
            Ok(BuiltinResult::Bottom),
            "{hook}"
        );
    }
    for hook in ["MINT.shl", "MINT.ashr", "MINT.lshr"] {
        assert_eq!(
            evaluate(hook, &arguments),
            Ok(BuiltinResult::Value(zero.clone())),
            "{hook}"
        );
    }
}

/// `MIN /sMInt -1` is `MIN`: the quotient `2^(W-1)` has the pattern of `MIN`, as `bvsdiv` gives;
/// `MIN %sMInt -1` is 0.
#[test]
fn signed_division_of_the_least_value_by_minus_one_wraps() {
    for width in [8_u32, 127] {
        let least = BigInt::from(1) << (width - 1);
        let minus_one = (BigInt::from(1) << width) - 1;
        let min = mint_term(width, &format!("{least}p{width}"));
        let arguments = [
            min.clone(),
            mint_term(width, &format!("{minus_one}p{width}")),
        ];
        assert_eq!(
            evaluate("MINT.sdiv", &arguments),
            Ok(BuiltinResult::Value(min)),
            "width {width}"
        );
        assert_eq!(
            evaluate("MINT.srem", &arguments),
            Ok(BuiltinResult::Value(mint_term(
                width,
                &format!("0p{width}")
            ))),
            "width {width}"
        );
    }
}

/// A left shift whose result would be wider than the result bound is refused before it is built,
/// as `<<Int`'s is; a shift by the width or more is 0 at any width.
#[test]
fn a_left_shift_wider_than_the_result_bound_is_too_large() {
    let width = 1_u64 << 30;
    let one = mint_term(width, &format!("1p{width}"));
    let result = evaluate(
        "MINT.shl",
        &[
            one.clone(),
            mint_term(width, &format!("{}p{width}", 1_u64 << 29)),
        ],
    )
    .unwrap();
    assert!(
        matches!(
            result,
            BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })
        ),
        "{result:?}"
    );
    assert_eq!(
        evaluate(
            "MINT.shl",
            &[one.clone(), mint_term(width, &format!("{width}p{width}"))]
        ),
        Ok(BuiltinResult::Value(mint_term(
            width,
            &format!("0p{width}")
        )))
    );
    assert_eq!(
        evaluate("MINT.shl", &[one, mint_term(width, &format!("3p{width}"))]),
        Ok(BuiltinResult::Value(mint_term(
            width,
            &format!("8p{width}")
        )))
    );
}

/// At a width beyond `u64` a left shift still keeps only the bits below `W - amount`: an amount of
/// `W` or more, or one that moves every set bit out, gives 0; only a result that keeps a bit and
/// is wider than the bound is refused.
#[test]
fn a_left_shift_at_a_width_beyond_u64_keeps_the_bits_below_the_width() {
    let width = "18446744073709551616";
    let word = |value: &str| mint_term(width, &format!("{value}p{width}"));
    let zero = BuiltinResult::Value(word("0"));
    assert_eq!(
        evaluate("MINT.shl", &[word("1"), word(width)]),
        Ok(zero.clone())
    );
    assert_eq!(
        evaluate("MINT.shl", &[word("1"), word("18446744073709551617")]),
        Ok(zero.clone())
    );
    // An amount of `W - 1` keeps only bit 0, which `2` does not set.
    assert_eq!(
        evaluate("MINT.shl", &[word("2"), word("18446744073709551615")]),
        Ok(zero)
    );
    assert_eq!(
        evaluate("MINT.shl", &[word("1"), word("3")]),
        Ok(BuiltinResult::Value(word("8")))
    );
    let result = evaluate("MINT.shl", &[word("1"), word("9223372036854775808")]).unwrap();
    assert!(
        matches!(
            result,
            BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })
        ),
        "{result:?}"
    );
}

/// A hook result is the value its own text names: the term built from the result's residue is the
/// term the kinded constructor builds from the result's text, at widths below and above 128,
/// beyond `u64`, and at `MInt{0}`, for results that wrap and results that do not.
#[test]
fn a_hook_result_is_the_value_its_text_names() {
    let beyond_u64 = "18446744073709551616";
    let wide = (1_u64 << 20).to_string();
    for width in [
        "0",
        "1",
        "8",
        "64",
        "65",
        "128",
        "200",
        wide.as_str(),
        beyond_u64,
    ] {
        let word = |value: &str| mint_term(width, &format!("{value}p{width}"));
        for (hook, arguments) in [
            ("MINT.not", vec![word("0")]),
            ("MINT.neg", vec![word("1")]),
            ("MINT.add", vec![word("1"), word("1")]),
            ("MINT.sub", vec![word("0"), word("1")]),
            ("MINT.mul", vec![word("3"), word("5")]),
            ("MINT.xor", vec![word("6"), word("3")]),
        ] {
            let result = match evaluate(hook, &arguments) {
                Ok(BuiltinResult::Value(result)) => result,
                // A wrapped result at a width beyond the result bound is not built.
                Ok(BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge {
                    ..
                })) if width == beyond_u64 => {
                    continue;
                }
                other => panic!("{hook} at width {width}: {other:?}"),
            };
            let crate::term::TermKind::DomainValue { sort, value } = result.kind() else {
                panic!("{hook} at width {width}: {result:?}");
            };
            let width_kind = mint_width(sort).expect("a machine-integer sort");
            let parsed =
                Term::domain_value_of(DomainKind::MInt(width_kind), sort.clone(), value.clone());
            assert_eq!(result, parsed, "{hook} at width {width}");
        }
    }
}

/// A hook result is written from its residue: building it parses no decimal text, so its cost
/// is not quadratic in its length. `~MInt` of 0 at a width of `2^20` is a decimal of 315,653
/// digits whose parse alone used to dominate the hook (at `2^24`, about 15 of 17 seconds).
#[test]
fn a_hook_result_is_built_without_parsing_its_text() {
    let width = 1_u64 << 20;
    let zero = mint_term(width, &format!("0p{width}"));
    let one = mint_term(width, &format!("1p{width}"));
    let before = crate::term::mint_text_parses();
    for (hook, arguments) in [
        ("MINT.not", vec![zero.clone()]),
        ("MINT.neg", vec![one.clone()]),
        ("MINT.sub", vec![zero, one]),
    ] {
        let result = evaluate(hook, &arguments);
        assert!(
            matches!(result, Ok(BuiltinResult::Value(_))),
            "{hook}: {result:?}"
        );
    }
    assert_eq!(crate::term::mint_text_parses(), before);
}
