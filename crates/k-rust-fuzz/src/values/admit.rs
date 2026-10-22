//! Whether a value is one a hole's generator could have drawn (`admissible`): the rule the
//! guidance proposers share, so that the dictionary and the climb cannot drift apart.

use num_bigint::BigInt;
use num_traits::{Signed as _, Zero as _};

use super::{
    Constraints, GenerationBounds, MAX_GENERATED_LENGTH, MAX_VALUE_SIZE, Value, ValueSort,
    check_constraints,
};

/// Whether a hole of `sort` under `constraints` and `bounds` admits `value` as a value its
/// generator could have drawn: [`check_constraints`], then the generator's size rules (an
/// integer without a range lies within `int_bits` bits of zero, and with one bounded end within
/// `int_bits` bits of the admissible value nearest zero; a string, byte string or collection is
/// at most the generator's longest; a data term is within the depth bound; nested values follow
/// the rules of values drawn without constraints; and the whole value is within
/// [`MAX_VALUE_SIZE`]). The guidance proposers (the dictionary, the climb) propose only such
/// values.
pub(crate) fn admissible(
    value: &Value,
    sort: &ValueSort,
    constraints: &Constraints,
    bounds: &GenerationBounds,
) -> bool {
    check_constraints(value, sort, constraints).is_ok()
        && within_bounds(value, Some(constraints), bounds)
        && size(value) <= MAX_VALUE_SIZE
}

/// The generator's size rules for `value`: `constraints` are the hole's at the top and `None`
/// for nested values, which the generators draw without constraints.
fn within_bounds(
    value: &Value,
    constraints: Option<&Constraints>,
    bounds: &GenerationBounds,
) -> bool {
    let default = Constraints::default();
    let constraints = constraints.unwrap_or(&default);
    match value {
        Value::Int(number) => {
            let (min, max) = constraints.range.as_ref().map_or((None, None), |range| {
                (range.min.as_ref(), range.max.as_ref())
            });
            if min.is_some() && max.is_some() {
                return true;
            }
            let zero = BigInt::zero();
            let nearest = match (min, max) {
                (Some(min), _) if *min > zero => min.clone(),
                (_, Some(max)) if *max < zero => max.clone(),
                _ => zero,
            };
            (number - nearest).abs().bits() <= u64::from(bounds.int_bits)
        }
        Value::String(text) => length_within(text.chars().count(), constraints, bounds),
        Value::Bytes(bytes) => length_within(bytes.len(), constraints, bounds),
        Value::List(items) | Value::Set(items) => {
            length_within(items.len(), constraints, bounds)
                && items.iter().all(|item| within_bounds(item, None, bounds))
        }
        Value::Map(entries) => {
            length_within(entries.len(), constraints, bounds)
                && entries.iter().all(|(key, value)| {
                    within_bounds(key, None, bounds) && within_bounds(value, None, bounds)
                })
        }
        Value::Apply { .. } => data_depth(value) <= bounds.depth && data_within(value, bounds),
        Value::Bool(_) | Value::MInt { .. } | Value::Token { .. } => true,
    }
}

/// The size rules of a data value's builtin and collection leaves.
fn data_within(value: &Value, bounds: &GenerationBounds) -> bool {
    match value {
        Value::Apply { arguments, .. } => arguments
            .iter()
            .all(|argument| data_within(argument, bounds)),
        other => within_bounds(other, None, bounds),
    }
}

/// The most constructor applications on a path from `value`'s root.
fn data_depth(value: &Value) -> u32 {
    match value {
        Value::Apply { arguments, .. } => 1 + arguments.iter().map(data_depth).max().unwrap_or(0),
        _ => 0,
    }
}

/// Whether a length is within the generator's longest: the length range's maximum, or the
/// larger of its minimum and the default bound, at most [`MAX_GENERATED_LENGTH`].
fn length_within(length: usize, constraints: &Constraints, bounds: &GenerationBounds) -> bool {
    let range = constraints.length.unwrap_or_default();
    let min = range.min.unwrap_or(0);
    let max = range
        .max
        .unwrap_or_else(|| min.max(bounds.length))
        .min(MAX_GENERATED_LENGTH)
        .max(min);
    u64::try_from(length).is_ok_and(|length| length <= max)
}

/// The size of `value` in the units of [`MAX_VALUE_SIZE`]: one per constructor application or
/// leaf, plus one per 64 bits of an integer and one per character or byte of a string.
fn size(value: &Value) -> u128 {
    let words = |bits: u64| 1 + u128::from(bits / 64);
    match value {
        Value::Int(number) => words(number.bits()),
        Value::MInt { value, .. } => words(value.bits()),
        Value::String(text) => 1 + text.chars().count() as u128,
        Value::Bytes(bytes) => 1 + bytes.len() as u128,
        Value::Bool(_) | Value::Token { .. } => 1,
        Value::List(items) | Value::Set(items) => {
            items.iter().map(size).fold(1, u128::saturating_add)
        }
        Value::Map(entries) => entries
            .iter()
            .map(|(key, value)| size(key).saturating_add(size(value)))
            .fold(1, u128::saturating_add),
        Value::Apply { arguments, .. } => arguments.iter().map(size).fold(1, u128::saturating_add),
    }
}
