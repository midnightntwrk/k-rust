//! `MINT` against Rust's native fixed-width integers.
//!
//! A `MInt{W}` value is a `W`-bit pattern, read unsigned or in two's complement by the operation
//! (`domains.md`, "MInt"). The model computes each hook with the machine operations of a `W`-bit
//! integer: `u8`/`i8` to `u64`/`i64` for the native widths, and `u128`/`i128` masked to `W` bits
//! (signed readings by sign extension) for the others, so it shares no formula with the
//! evaluator, which reduces arbitrary-precision integers modulo `2^W`.

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::ToPrimitive;

use k_rust_kore::names::{BuiltinSort, MINT_SORT};

use super::{Case, Draw, Env, Spec, Val, assert_reached, encode, evaluate, run, variable};
use crate::{
    builtin::{BuiltinError, BuiltinResult, UnsupportedHookReason},
    term::{FunctionType, Sort, Symbol, SymbolAttributes, SymbolType, Term},
};

const CASES: u32 = 4000;

/// The widths the model covers: those of Rust's native integers, and others it computes in
/// 128 bits.
const WIDTHS: [u32; 8] = [8, 16, 32, 64, 1, 7, 65, 127];

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

fn mint_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&TOTAL_HOOKS);
    let width = draw.pick(&WIDTHS);
    let mut env = Env::new();
    let mut arguments: Vec<Term> = Vec::new();
    for _ in 0..arity(hook) {
        let argument = if !arguments.is_empty() && draw.chance(2) {
            // The same argument twice: equality is reflexive whatever it denotes.
            arguments[0].clone()
        } else {
            let value = pattern(draw, width);
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
    let tallies = run(CASES, &mint_case, &mint_model);
    assert_reached(
        &tallies,
        &TOTAL_HOOKS,
        &["MINT.bitwidth", "MINT.eq", "MINT.ne"],
    );
}

// ---------------------------------------------------------------------------------------------
// Applications: the width of `Int2MInt` is its result sort's.

/// `Int2MInt{W}(argument)` as `domains.md` declares it, `W` the sort argument `width`.
fn int2mint(width: Sort, argument: Term) -> Term {
    let parameter = Sort::Variable("W".into());
    let mut attributes = SymbolAttributes::constructor().with_declared_function(true);
    attributes.symbol_type = SymbolType::Function(FunctionType::Total);
    attributes.hook = Some("MINT.integer".into());
    Term::application(
        Arc::new(Symbol {
            name: "LblInt2MInt".into(),
            sort_variables: vec!["W".into()],
            argument_sorts: vec![Sort::builtin(BuiltinSort::Int)],
            result_sort: Sort::application(MINT_SORT, vec![parameter]),
            attributes,
        }),
        vec![width],
        vec![argument],
    )
}

fn evaluated(term: &Term) -> BuiltinResult {
    crate::builtin::evaluate(term)
        .expect("not stopped")
        .expect("no argument failure")
}

fn int(value: impl Into<BigInt>) -> Term {
    encode(&Val::Int(value.into()))
}

fn mint_term(width: impl std::fmt::Display, text: &str) -> Term {
    Term::domain_value(mint_sort(width), text)
}

fn unspecified(result: &BuiltinResult) -> bool {
    matches!(
        result,
        BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
    )
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

/// A sort `MInt{Foo}` names no width, so the value of a total conversion into it, and the width
/// of its elements, are not determined; a sort `MInt{W}` whose argument is a sort variable has a
/// width that is not fixed yet, and the application waits for it.
#[test]
fn a_sort_without_a_numeral_width_leaves_the_total_conversions_unspecified() {
    let foo = Sort::simple("SortFoo");
    assert!(unspecified(&evaluated(&int2mint(foo.clone(), int(5)))));
    let no_width = Sort::application(MINT_SORT, vec![foo]);
    let result = evaluate("MINT.bitwidth", &[variable("X", no_width)]).unwrap();
    assert!(unspecified(&result), "{result:?}");

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
