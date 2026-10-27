//! Exact integer readings of bounded literal shifts and finite nonnegative masks.
//!
//! These identities hold for all signed K Int values, with no machine width assumption.
//! The caller retains the original operand definedness. Unsupported amounts/ranks and resource
//! limits keep the existing scalar/opaque reading; a refused size is not undefinedness.

use num_bigint::{BigInt, Sign};

use super::{SExpr, TranslationError, TranslationState};
use crate::{
    builtin::read_int,
    term::{Sort, Symbol, Term},
};
use k_rust_kore::names::BuiltinSort;

#[cfg(test)]
mod tests;

/// Powers are at most about 1234 decimal digits. A mask has at most this many bit positions.
const AMOUNT_LIMIT: u32 = 4096;
/// Bound both output text and the work done for a sparse mask.
const RUN_LIMIT: usize = 64;

pub(super) struct Operation<'t> {
    operand: &'t Term,
    reading: Reading,
}

enum Reading {
    Projection {
        offset: u32,
        length: Option<u32>,
    },
    LeftShift(u32),
    Mask {
        value: BigInt,
        runs: Vec<(u32, u32)>,
        operation: MaskOperation,
    },
}

#[derive(Clone, Copy)]
enum MaskOperation {
    And,
    Or,
    Xor,
}

fn amount(term: &Term) -> Option<u32> {
    u32::try_from(read_int(term)?)
        .ok()
        .filter(|n| *n <= AMOUNT_LIMIT)
}

/// Maximal runs of set bits, from low to high. A run (o,l) reads
/// `2^o * ((x div 2^o) mod 2^l)`. This extracts the same two's-complement bits for negative x.
fn runs(value: &BigInt) -> Option<Vec<(u32, u32)>> {
    if value.sign() == Sign::Minus || value.bits() > u64::from(AMOUNT_LIMIT) {
        return None;
    }
    let mut result = Vec::new();
    let mut position = 0;
    while u64::from(position) < value.bits() {
        if !value.bit(u64::from(position)) {
            position += 1;
            continue;
        }
        let start = position;
        while value.bit(u64::from(position)) {
            position += 1;
        }
        if result.len() == RUN_LIMIT {
            return None;
        }
        result.push((start, position - start));
    }
    Some(result)
}

pub(super) fn read<'t>(
    symbol: &Symbol,
    sort: &Sort,
    arguments: &'t [Term],
) -> Option<Operation<'t>> {
    if !sort.is_builtin(BuiltinSort::Int)
        || !arguments
            .iter()
            .all(|a| a.sort().is_builtin(BuiltinSort::Int))
    {
        return None;
    }
    let (operand, reading) = match (symbol.attributes.hook.as_deref()?, arguments) {
        ("INT.bitRange", [x, offset, length]) => (
            x,
            Reading::Projection {
                offset: amount(offset)?,
                length: Some(amount(length)?),
            },
        ),
        ("INT.shr", [x, offset]) => (
            x,
            Reading::Projection {
                offset: amount(offset)?,
                length: None,
            },
        ),
        ("INT.shl", [x, offset]) => (x, Reading::LeftShift(amount(offset)?)),
        (hook @ ("INT.and" | "INT.or" | "INT.xor"), [left, right]) => {
            let mask = |term: &Term| {
                let value = read_int(term)?;
                let runs = runs(&value)?;
                Some((value, runs))
            };
            let (x, (value, runs)) = if let Some(mask) = mask(right) {
                (left, mask)
            } else {
                (right, mask(left)?)
            };
            let operation = match hook {
                "INT.and" => MaskOperation::And,
                "INT.or" => MaskOperation::Or,
                "INT.xor" => MaskOperation::Xor,
                _ => unreachable!("matched integer bit hook"),
            };
            (
                x,
                Reading::Mask {
                    value,
                    runs,
                    operation,
                },
            )
        }
        _ => return None,
    };
    Some(Operation { operand, reading })
}

fn power(exponent: u32) -> SExpr {
    SExpr::atom((BigInt::from(1u8) << exponent).to_string())
}

fn projection(mut operand: SExpr, offset: u32, length: Option<u32>) -> SExpr {
    if offset != 0 {
        operand = SExpr::application("div", vec![operand, power(offset)]);
    }
    if let Some(length) = length {
        operand = SExpr::application("mod", vec![operand, power(length)]);
    }
    operand
}

impl Operation<'_> {
    pub(super) fn translate(self, state: &mut TranslationState) -> Result<SExpr, TranslationError> {
        let operand = state.translate_term(self.operand)?;
        Ok(match self.reading {
            Reading::Projection { offset, length } => projection(operand, offset, length),
            Reading::LeftShift(0) => operand,
            Reading::LeftShift(amount) => SExpr::application("*", vec![operand, power(amount)]),
            Reading::Mask {
                value,
                runs,
                operation,
            } => {
                // OR/XOR use x both directly and through its intersection. Multiple runs share
                // it too. Bind composite operands once even in definition-free translation.
                let share = matches!(operand, SExpr::List(_))
                    && (runs.len() > 1 || !matches!(operation, MaskOperation::And));
                let binding = share.then(|| state.fresh_name());
                let x = binding
                    .as_ref()
                    .map(|name| SExpr::atom(name.clone()))
                    .unwrap_or_else(|| operand.clone());
                let parts = runs
                    .into_iter()
                    .map(|(offset, length)| {
                        let bits = projection(x.clone(), offset, Some(length));
                        if offset == 0 {
                            bits
                        } else {
                            SExpr::application("*", vec![power(offset), bits])
                        }
                    })
                    .collect::<Vec<_>>();
                let intersection = match parts.len() {
                    0 => SExpr::atom("0"),
                    1 => parts.into_iter().next().expect("one run"),
                    _ => SExpr::application("+", parts),
                };
                let result = match operation {
                    MaskOperation::And => intersection,
                    MaskOperation::Or | MaskOperation::Xor => {
                        let subtrahend = if matches!(operation, MaskOperation::Xor) {
                            SExpr::application("*", vec![SExpr::atom("2"), intersection])
                        } else {
                            intersection
                        };
                        SExpr::application(
                            "-",
                            vec![
                                SExpr::application("+", vec![x, SExpr::atom(value.to_string())]),
                                subtrahend,
                            ],
                        )
                    }
                };
                match binding {
                    Some(name) => SExpr::application(
                        "let",
                        vec![
                            SExpr::List(vec![SExpr::List(vec![SExpr::atom(name), operand])]),
                            result,
                        ],
                    ),
                    None => result,
                }
            }
        })
    }
}
