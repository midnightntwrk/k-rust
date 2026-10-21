//! Int facts: what one guard conjunct states about one Int term, and the
//! evaluation of builtin Int operations on literals.
//!
//! A conjunct `bitRangeInt(t, o, l) ==Int v` or `t &Int m ==Int v` (literal
//! `o`, `l`, `m`) fixes bits of `t`'s two's complement, `t ==Int c` fixes its
//! value, and `c <=Int t`, `t <Int c` bound it. Facts about one term are
//! merged into [`IntFacts`], which answers whether some integer may have them
//! all; it answers "no" only when none can, so a reader that drops the
//! valuations or rule pairs it rules out stays sound. The overlap check of
//! transitions reads facts after unification (F2 amendment, clause 4); the
//! coverage lint reads them between the subjects of one guard valuation.
//!
//! Evaluating a builtin on literals is its definition, so [`evaluate_int`]
//! is exact wherever it answers.

use krs_ir::BuiltinOperation;

/// A builtin Int operation on literal operands, when its result is defined
/// and fits `i128`.
pub(crate) fn evaluate_int(operation: BuiltinOperation, values: &[i128]) -> Option<i128> {
    match (operation, values) {
        (BuiltinOperation::IntAdd, [left, right]) => left.checked_add(*right),
        (BuiltinOperation::IntSub, [left, right]) => left.checked_sub(*right),
        (BuiltinOperation::IntMul, [left, right]) => left.checked_mul(*right),
        (BuiltinOperation::IntBitAnd, [left, right]) => Some(left & right),
        (BuiltinOperation::IntShiftRight, [value, amount]) => {
            let amount = u32::try_from(*amount).ok()?;
            Some(if amount >= 128 {
                if *value < 0 { -1 } else { 0 }
            } else {
                value >> amount
            })
        }
        (BuiltinOperation::IntEDiv, [value, divisor]) if *divisor != 0 => {
            value.checked_div_euclid(*divisor)
        }
        (BuiltinOperation::IntMod, [value, divisor]) if *divisor != 0 => {
            value.checked_rem_euclid(*divisor)
        }
        (BuiltinOperation::IntBitRange, [value, index, length]) => {
            let index = u32::try_from(*index).ok()?;
            let length = u32::try_from(*length).ok()?;
            if length >= 127 {
                return None;
            }
            let shifted = if index >= 128 {
                if *value < 0 { -1 } else { 0 }
            } else {
                value >> index
            };
            Some(shifted.rem_euclid(1_i128 << length))
        }
        _ => None,
    }
}

/// `length` low one bits.
const fn low_ones(length: u32) -> u128 {
    if length >= 128 {
        u128::MAX
    } else {
        (1 << length) - 1
    }
}

/// One fact a guard conjunct states about an Int term.
#[derive(Clone, Copy, Debug)]
pub(crate) enum IntFact {
    /// The term equals the value.
    Equal(i128),
    /// The bits of the term's two's complement under `mask` are those of
    /// `value` (from `bitRangeInt(t, o, l) ==Int v` or `t &Int m ==Int v`).
    Bits { mask: u128, value: u128 },
    /// The term is at least the bound.
    AtLeast(i128),
    /// The term is below the bound.
    Below(i128),
}

impl IntFact {
    /// The fact `bitRangeInt(t, offset, length) ==Int value` states about
    /// `t`: `Some(Err(()))` when it cannot hold (`bitRangeInt` is
    /// non-negative and below `2^length`), `None` when it states no bit fact
    /// (a negative or empty range, or bits past the 128th).
    pub(crate) fn bit_range(offset: i128, length: i128, value: i128) -> Option<Result<Self, ()>> {
        let (Ok(offset), Ok(length)) = (u32::try_from(offset), u32::try_from(length)) else {
            return None;
        };
        if length == 0 || offset.checked_add(length).is_none_or(|end| end > 128) {
            return None;
        }
        let Ok(value) = u128::try_from(value) else {
            return Some(Err(()));
        };
        if length < 128 && value >> length != 0 {
            return Some(Err(()));
        }
        Some(Ok(Self::Bits {
            mask: low_ones(length) << offset,
            value: value << offset,
        }))
    }

    /// The fact `t &Int mask ==Int value` states about `t`: `Some(Err(()))`
    /// when it cannot hold (a bit of `value` outside a non-negative `mask`),
    /// `None` for a negative mask.
    pub(crate) fn masked(mask: i128, value: i128) -> Option<Result<Self, ()>> {
        let mask = u128::try_from(mask).ok()?;
        let Ok(value) = u128::try_from(value) else {
            return Some(Err(()));
        };
        if value & !mask != 0 {
            return Some(Err(()));
        }
        Some(Ok(Self::Bits { mask, value }))
    }
}

/// The facts of one term, merged.
#[derive(Default)]
pub(crate) struct IntFacts {
    equal: Option<i128>,
    unequal: bool,
    /// Bits known so far and their values; `clash` when a bit is required
    /// both 0 and 1.
    mask: u128,
    value: u128,
    clash: bool,
    at_least: Option<i128>,
    below: Option<i128>,
}

impl IntFacts {
    pub(crate) fn add(&mut self, fact: IntFact) {
        match fact {
            IntFact::Equal(value) => {
                if self.equal.is_some_and(|equal| equal != value) {
                    self.unequal = true;
                }
                self.equal = Some(value);
            }
            IntFact::Bits { mask, value } => {
                if (self.value ^ value) & self.mask & mask != 0 {
                    self.clash = true;
                }
                self.mask |= mask;
                self.value |= value & mask;
            }
            IntFact::AtLeast(bound) => {
                self.at_least = Some(self.at_least.map_or(bound, |known| known.max(bound)));
            }
            IntFact::Below(bound) => {
                self.below = Some(self.below.map_or(bound, |known| known.min(bound)));
            }
        }
    }

    /// Whether some integer may have every fact (necessary conditions only).
    pub(crate) fn satisfiable(&self) -> bool {
        if self.unequal || self.clash {
            return false;
        }
        if let (Some(at_least), Some(below)) = (self.at_least, self.below)
            && at_least >= below
        {
            return false;
        }
        if let Some(value) = self.equal {
            // Two's complement bits of `value`, as `bitRangeInt` and `&Int` read them.
            #[expect(
                clippy::cast_sign_loss,
                reason = "the two's complement bits are wanted"
            )]
            let bits = value as u128;
            if (bits ^ self.value) & self.mask != 0
                || self.at_least.is_some_and(|bound| value < bound)
                || self.below.is_some_and(|bound| value >= bound)
            {
                return false;
            }
        }
        // A non-negative term is at least the number its known one bits form.
        if self.at_least.is_some_and(|bound| bound >= 0)
            && let Some(below) = self.below
            && i128::try_from(self.value).map_or(true, |least| least >= below)
        {
            return false;
        }
        true
    }
}
