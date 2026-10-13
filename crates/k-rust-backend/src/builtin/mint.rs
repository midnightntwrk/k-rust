//! The `MINT` hooks: machine integers of a fixed width `W` (`domains.md`, "MInt").
//!
//! `MInt{W}` is "machine integers of arbitrary bit width represented in 2's complement": its
//! elements are the `2^W` bit patterns of width `W`, with no sign of their own. An operation reads
//! a pattern as its unsigned residue `u` in `[0, 2^W)`, or in two's complement as `s = u` when
//! `u < 2^(W-1)` and `s = u - 2^W` otherwise. A total operation on patterns that agrees with
//! `MInt2Unsigned` is arithmetic modulo `2^W`, and the declared `smt-hook`s (`bvadd`, `bvmul`,
//! `bvult`, `bvslt`, `bv2int`, `int2bv`, ...) state exactly these operations to a solver, so an
//! evaluator that disagreed with them would let the backend derive two values for one term.
//!
//! Division and remainder are partial: there is no quotient by zero, so a zero divisor is
//! undefined (`\bottom`). SMT-LIB gives `bvudiv`, `bvurem`, `bvsdiv` and `bvsrem` values at a zero
//! divisor, but that totalization is never read as a K value: a partial symbol's translation is
//! approximate, and every solver decision over a partial term is taken under its `\ceil`. Where a
//! quotient exists the `smt-hook`s fix its rounding: signed division truncates toward zero and
//! the remainder (`bvsrem`, not `bvsmod`) has the dividend's sign. `MIN /sMInt -1` has a value,
//! `MIN`: the quotient `2^(W-1)` has the pattern of `MIN`, and the result carries no sign. The
//! shifts read their amount unsigned and have a value for every amount: a shift by `W` or more
//! moves every bit out, giving 0, or all sign bits for `>>aMInt` (`bvshl`, `bvlshr`, `bvashr`).
//!
//! A domain value of `MInt{W}` holds its canonical text `<u>p<D>`, `D` the digits of the sort's
//! width argument (`Term::domain_value_of`), so the hooks read the residue from that text and
//! write their results in it.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, ToPrimitive, Zero};

use super::{
    BuiltinError, BuiltinResult, HookResult, MAX_INT_RESULT_BITS, UnsupportedHookReason, bool_term,
    describe_int, expect_arity, int_term, read_int, result_size_limit,
};
use crate::term::{DomainKind, MIntWidth, Sort, Term, TermKind, mint_width, mint_width_digits};

/// `total`: the application's symbol is declared `total`, which the conversions read at a sort
/// that names no width ([`no_width`]).
pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    result_sort: Option<&Sort>,
    total: bool,
) -> HookResult<BuiltinResult> {
    match hook {
        "MINT.integer" => integer(arguments, result_sort, total),
        "MINT.bitwidth" => bitwidth(arguments, total),
        "MINT.svalue" => reading(hook, arguments, |word| word.signed()),
        "MINT.uvalue" => reading(hook, arguments, |word| BigInt::from(word.residue.clone())),
        "MINT.add" => wrapping(hook, "+MInt", arguments, |left, right| left + right),
        "MINT.sub" => wrapping(hook, "-MInt", arguments, |left, right| left - right),
        "MINT.mul" => wrapping(hook, "*MInt", arguments, |left, right| left * right),
        "MINT.neg" => wrapping_unary(hook, "--MInt", arguments, |value| -value),
        "MINT.not" => wrapping_unary(hook, "~MInt", arguments, |value| -value - 1),
        "MINT.and" => bitwise(hook, arguments, |left, right| left & right),
        "MINT.or" => bitwise(hook, arguments, |left, right| left | right),
        "MINT.xor" => bitwise(hook, arguments, |left, right| left ^ right),
        "MINT.eq" => equality(hook, arguments, true),
        "MINT.ne" => equality(hook, arguments, false),
        "MINT.ult" => order(hook, arguments, Reading::Unsigned, Ordering::is_lt),
        "MINT.ule" => order(hook, arguments, Reading::Unsigned, Ordering::is_le),
        "MINT.ugt" => order(hook, arguments, Reading::Unsigned, Ordering::is_gt),
        "MINT.uge" => order(hook, arguments, Reading::Unsigned, Ordering::is_ge),
        "MINT.slt" => order(hook, arguments, Reading::Signed, Ordering::is_lt),
        "MINT.sle" => order(hook, arguments, Reading::Signed, Ordering::is_le),
        "MINT.sgt" => order(hook, arguments, Reading::Signed, Ordering::is_gt),
        "MINT.sge" => order(hook, arguments, Reading::Signed, Ordering::is_ge),
        "MINT.udiv" => unsigned_division(hook, arguments, |left, right| left / right),
        "MINT.urem" => unsigned_division(hook, arguments, |left, right| left % right),
        "MINT.sdiv" => signed_division(hook, "/sMInt", arguments, |left, right| left / right),
        "MINT.srem" => signed_division(hook, "%sMInt", arguments, |left, right| left % right),
        "MINT.shl" => shift_left(arguments),
        "MINT.lshr" => shift_right(hook, ">>lMInt", arguments, Reading::Unsigned),
        "MINT.ashr" => shift_right(hook, ">>aMInt", arguments, Reading::Signed),
        _ => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
    }
}

/// A literal of a machine-integer sort with a width: the sort, its width (`None` beyond `u64`),
/// and the unsigned residue in `[0, 2^W)`.
#[derive(Debug)]
struct Word {
    sort: Sort,
    width: Option<u64>,
    residue: BigUint,
}

impl Word {
    /// The width `W`, also beyond `u64`, where it is read from the sort's width digits.
    fn width_value(&self) -> BigUint {
        self.width.map_or_else(
            || {
                mint_width_digits(&self.sort)
                    .and_then(|digits| digits.parse().ok())
                    .expect("a literal's sort has a numeral width")
            },
            BigUint::from,
        )
    }

    /// The two's-complement reading: the residue, less `2^W` when its top bit (bit `W - 1`) is
    /// set. The single element of `MInt{0}` reads 0.
    fn signed(&self) -> BigInt {
        match self.width {
            Some(width) if width > 0 && self.residue.bits() == width => {
                BigInt::from(self.residue.clone()) - (BigInt::one() << width)
            }
            _ => BigInt::from(self.residue.clone()),
        }
    }
}

/// The width of a machine-integer sort as a literal's sort reads it: `Some(Some(w))` for `w`
/// bits, `Some(None)` beyond `u64`, and `None` when the sort has no literals (no numeral width,
/// a sort variable, or no machine-integer sort).
fn literal_width(sort: &Sort) -> Option<Option<u64>> {
    match mint_width(sort)? {
        MIntWidth::Bits(width) => Some(Some(width)),
        MIntWidth::Unrepresentable => Some(None),
        MIntWidth::NoWidth => None,
    }
}

/// The machine integer `term` denotes, when it is a domain value of a machine-integer sort with a
/// width: its canonical text is the decimal residue, `p`, and the digits of the sort's width.
fn read_mint(term: &Term) -> Option<Word> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    let width = literal_width(sort)?;
    let (residue, digits) = value.as_utf8().ok()?.split_once('p')?;
    if digits != mint_width_digits(sort)?
        || residue.is_empty()
        || !residue.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    let residue: BigUint = residue.parse().ok()?;
    if width.is_some_and(|width| residue.bits() > width) {
        return None;
    }
    Some(Word {
        sort: sort.clone(),
        width,
        residue,
    })
}

/// Both operands of a binary hook, when both are literals; literals of two sorts are an
/// ill-sorted application, which no loaded definition holds.
fn read_pair(hook: &str, arguments: &[Term]) -> HookResult<Option<(Word, Word)>> {
    expect_arity(hook, arguments, 2)?;
    let (Some(left), Some(right)) = (read_mint(&arguments[0]), read_mint(&arguments[1])) else {
        return Ok(None);
    };
    if left.sort != right.sort {
        return Err(BuiltinError::UnexpectedSort {
            hook: hook.into(),
            expected: left.sort,
            actual: right.sort,
        }
        .into());
    }
    Ok(Some((left, right)))
}

/// The literal of `sort` whose residue is `residue`, in canonical text.
fn word_term(sort: &Sort, residue: &BigUint) -> Term {
    let width = mint_width(sort).expect("a literal's sort has a width");
    let digits = mint_width_digits(sort).expect("a literal's sort has width digits");
    Term::domain_value_of(
        DomainKind::MInt(width),
        sort.clone(),
        format!("{residue}p{digits}"),
    )
}

/// The residue of `value` modulo `2^width` (no `width`: beyond `u64`), or `None` when computing
/// it needs `2^width` and `width` exceeds `limit` bits: a negative value wraps to `2^W` less its
/// magnitude's residue, a decimal of about `W` bits.
fn wrap(value: &BigInt, width: Option<u64>, limit: u64) -> Option<BigUint> {
    let magnitude = value.magnitude();
    let residue = match width {
        Some(width) if magnitude.bits() > width => magnitude & ((BigUint::one() << width) - 1u8),
        _ => magnitude.clone(),
    };
    if value.sign() != Sign::Minus || residue.is_zero() {
        return Some(residue);
    }
    let width = width.filter(|&width| width <= limit)?;
    Some((BigUint::one() << width) - residue)
}

/// The refusal of a result that wraps to a decimal of about `W` bits, above `limit`.
fn too_large(operation: &str, sort: &Sort, limit: u64) -> BuiltinResult {
    let digits = mint_width_digits(sort).unwrap_or("?");
    BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge {
        detail: format!("{operation} at width {digits} needs more than {limit} bits"),
    })
}

/// The bound on a result computed from operands of `bits` bits in all.
fn limit(bits: u64) -> u64 {
    result_size_limit(MAX_INT_RESULT_BITS, bits)
}

/// The outcome of `operation` at a machine-integer sort whose argument names no width
/// (`MInt{Foo}`): the hook's description is in terms of that width, so it gives the application
/// no value, and the application is left unevaluated.
///
/// Whether it has a value all the same is the declaration's statement, not the hook's. A symbol
/// declared `total` has a value in every model of the definition, which only leaves open which
/// one, so its application is defined and its `\ceil` holds. A symbol declared without `total`
/// states no value where its hook gives none, so nothing entails that its application is
/// defined, and its `\ceil` stays an open obligation.
fn no_width(operation: &str, total: bool) -> BuiltinResult {
    BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
        detail: format!("{operation} at a machine-integer sort whose argument names no width"),
        defined: total,
    })
}

/// `Int2MInt`: its argument modulo `2^W`, `W` the width of the application's sort. Without a
/// declared result sort there is no width, and at a sort whose width is a sort variable it is
/// not fixed yet; a sort `MInt{Foo}` has no width at all, so the description gives no value
/// there ([`no_width`]).
fn integer(
    arguments: &[Term],
    result_sort: Option<&Sort>,
    total: bool,
) -> HookResult<BuiltinResult> {
    expect_arity("MINT.integer", arguments, 1)?;
    let Some(sort) = result_sort else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let width = match mint_width(sort) {
        None => return Ok(BuiltinResult::NotApplicable),
        Some(MIntWidth::NoWidth) => return Ok(no_width("Int2MInt", total)),
        Some(MIntWidth::Bits(width)) => Some(width),
        Some(MIntWidth::Unrepresentable) => None,
    };
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let limit = limit(value.bits());
    Ok(match wrap(&value, width, limit) {
        Some(residue) => BuiltinResult::Value(word_term(sort, &residue)),
        None => too_large(&format!("Int2MInt({})", describe_int(&value)), sort, limit),
    })
}

/// `bitwidthMInt`: the width of its argument's sort, which every element of the sort has, so
/// any argument of a sort with a numeral width gives it. A sort `MInt{Foo}` has no width, so the
/// description gives no value there ([`no_width`]).
fn bitwidth(arguments: &[Term], total: bool) -> HookResult<BuiltinResult> {
    expect_arity("MINT.bitwidth", arguments, 1)?;
    let sort = arguments[0].sort();
    Ok(match mint_width(&sort) {
        None => BuiltinResult::NotApplicable,
        Some(MIntWidth::NoWidth) => no_width("bitwidthMInt", total),
        Some(MIntWidth::Bits(width)) => BuiltinResult::Value(int_term(BigInt::from(width))),
        Some(MIntWidth::Unrepresentable) => {
            let digits = mint_width_digits(&sort).expect("a numeral width has digits");
            BuiltinResult::Value(int_term(
                digits.parse().expect("width digits are a decimal numeral"),
            ))
        }
    })
}

/// `MInt2Signed` and `MInt2Unsigned`: a reading of a literal as an `Int`.
fn reading(
    hook: &str,
    arguments: &[Term],
    read: impl FnOnce(&Word) -> BigInt,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 1)?;
    Ok(read_mint(&arguments[0])
        .map(|word| int_term(read(&word)))
        .into())
}

/// A binary operation on the residues, reduced modulo `2^W`.
fn wrapping(
    hook: &str,
    operation: &str,
    arguments: &[Term],
    apply: impl FnOnce(BigInt, BigInt) -> BigInt,
) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_pair(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let limit = limit(left.residue.bits().saturating_add(right.residue.bits()));
    let value = apply(left.residue.into(), right.residue.into());
    Ok(match wrap(&value, left.width, limit) {
        Some(residue) => BuiltinResult::Value(word_term(&left.sort, &residue)),
        None => too_large(operation, &left.sort, limit),
    })
}

/// A unary operation on the residue, reduced modulo `2^W`.
fn wrapping_unary(
    hook: &str,
    operation: &str,
    arguments: &[Term],
    apply: impl FnOnce(BigInt) -> BigInt,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 1)?;
    let Some(word) = read_mint(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let limit = limit(word.residue.bits());
    let value = apply(word.residue.into());
    Ok(match wrap(&value, word.width, limit) {
        Some(residue) => BuiltinResult::Value(word_term(&word.sort, &residue)),
        None => too_large(operation, &word.sort, limit),
    })
}

/// `/uMInt` and `%uMInt`: floor division and remainder of the residues, undefined at a zero
/// divisor. Both results are below the dividend, so below `2^W`.
fn unsigned_division(
    hook: &str,
    arguments: &[Term],
    apply: impl FnOnce(&BigUint, &BigUint) -> BigUint,
) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_pair(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if right.residue.is_zero() {
        return Ok(BuiltinResult::Bottom);
    }
    Ok(BuiltinResult::Value(word_term(
        &left.sort,
        &apply(&left.residue, &right.residue),
    )))
}

/// `/sMInt` and `%sMInt`: the quotient truncated toward zero, and the remainder with the
/// dividend's sign, of the two's-complement readings, reduced modulo `2^W`; undefined at a zero
/// divisor. `MIN /sMInt -1` is the quotient `2^(W-1)` reduced, `MIN`.
fn signed_division(
    hook: &str,
    operation: &str,
    arguments: &[Term],
    apply: impl FnOnce(BigInt, BigInt) -> BigInt,
) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_pair(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if right.residue.is_zero() {
        return Ok(BuiltinResult::Bottom);
    }
    // A negative quotient or remainder needs a negative operand, whose residue has `W` bits, so
    // the bound is at least `2W` and its wrap is always computed; `wrap` checks it all the same.
    let limit = limit(left.residue.bits().saturating_add(right.residue.bits()));
    let value = apply(left.signed(), right.signed());
    Ok(match wrap(&value, left.width, limit) {
        Some(residue) => BuiltinResult::Value(word_term(&left.sort, &residue)),
        None => too_large(operation, &left.sort, limit),
    })
}

/// `<<MInt`: the residue times `2^amount`, modulo `2^W`, the amount read unsigned. Only the bits
/// below `W - amount` stay, so an amount of `W` or more gives 0 without computing `2^amount`. A
/// result wider than the bound on the integers the backend computes is refused before it is
/// built, as `<<Int`'s is.
fn shift_left(arguments: &[Term]) -> HookResult<BuiltinResult> {
    let Some((value, amount)) = read_pair("MINT.shl", arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let zero = || {
        Ok(BuiltinResult::Value(word_term(
            &value.sort,
            &BigUint::zero(),
        )))
    };
    // The bits that stay are those below `W - amount`: none for an amount of `W` or more.
    let width = value.width_value();
    if amount.residue >= width {
        return zero();
    }
    let room = width - &amount.residue;
    let kept = match room.to_u64() {
        Some(room) if value.residue.bits() > room => {
            &value.residue & ((BigUint::one() << room) - 1u8)
        }
        _ => value.residue.clone(),
    };
    if kept.is_zero() {
        return zero();
    }
    let limit = limit(value.residue.bits().saturating_add(amount.residue.bits()));
    let Some(shift) = amount
        .residue
        .to_u64()
        .filter(|shift| kept.bits().saturating_add(*shift) <= limit)
    else {
        return Ok(too_large("<<MInt", &value.sort, limit));
    };
    Ok(BuiltinResult::Value(word_term(
        &value.sort,
        &(kept << shift),
    )))
}

/// `>>lMInt` (`Unsigned`) and `>>aMInt` (`Signed`): the reading of the value divided by
/// `2^amount` and rounded down, modulo `2^W`, the amount read unsigned. An amount at least the
/// reading's bit length gives 0, or -1 (all sign bits) for a negative reading, without computing
/// `2^amount`.
fn shift_right(
    hook: &str,
    operation: &str,
    arguments: &[Term],
    reading: Reading,
) -> HookResult<BuiltinResult> {
    let Some((value, amount)) = read_pair(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let read = match reading {
        Reading::Unsigned => BigInt::from(value.residue.clone()),
        Reading::Signed => value.signed(),
    };
    let shifted = match amount.residue.to_u64() {
        Some(shift) if shift < read.bits() => read >> shift,
        _ if read.sign() == Sign::Minus => -BigInt::one(),
        _ => BigInt::zero(),
    };
    // Only a negative reading wraps, and its residue has `W` bits, so the bound is at least `2W`
    // and the wrap is always computed; `wrap` checks it all the same.
    let limit = limit(value.residue.bits().saturating_add(amount.residue.bits()));
    Ok(match wrap(&shifted, value.width, limit) {
        Some(residue) => BuiltinResult::Value(word_term(&value.sort, &residue)),
        None => too_large(operation, &value.sort, limit),
    })
}

/// A bitwise operation on the residues, whose result has no bit at or above `W`.
fn bitwise(
    hook: &str,
    arguments: &[Term],
    apply: impl FnOnce(&BigUint, &BigUint) -> BigUint,
) -> HookResult<BuiltinResult> {
    Ok(read_pair(hook, arguments)?
        .map(|(left, right)| word_term(&left.sort, &apply(&left.residue, &right.residue)))
        .into())
}

/// `==MInt` (`equal`) and `=/=MInt`: two literals are one element exactly when their residues
/// are equal, and an argument is equal to itself whatever it denotes.
fn equality(hook: &str, arguments: &[Term], equal: bool) -> HookResult<BuiltinResult> {
    if let Some((left, right)) = read_pair(hook, arguments)? {
        return Ok(BuiltinResult::Value(bool_term(
            (left.residue == right.residue) == equal,
        )));
    }
    Ok(if arguments[0] == arguments[1] {
        BuiltinResult::Value(bool_term(equal))
    } else {
        BuiltinResult::NotApplicable
    })
}

/// How an ordering reads a pattern: as its residue `u`, or in two's complement as `s`.
#[derive(Clone, Copy)]
enum Reading {
    Unsigned,
    Signed,
}

/// An ordering of two literals, comparing `u` or `s` by `reading`.
fn order(
    hook: &str,
    arguments: &[Term],
    reading: Reading,
    holds: fn(Ordering) -> bool,
) -> HookResult<BuiltinResult> {
    Ok(read_pair(hook, arguments)?
        .map(|(left, right)| {
            bool_term(holds(match reading {
                Reading::Unsigned => left.residue.cmp(&right.residue),
                Reading::Signed => left.signed().cmp(&right.signed()),
            }))
        })
        .into())
}
