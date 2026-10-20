//! Hole values in a definition-independent form, their sorts and constraints, generators and
//! K-text printing (ARCHITECTURE 2.5, 3). Owner: FZ-03.
//!
//! A [`Value`] holds no backend term: an internalized `Term` belongs to one
//! `BackendDefinition`, and a differential campaign internalizes each value once per side
//! (ARCHITECTURE 2.3, R-14).

pub(crate) mod generator;
pub(crate) mod print;

use num_bigint::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

pub(crate) use generator::{Generator, ShrinkableValue, ValueRng};

/// A hole value, independent of any definition.
///
/// Its JSON form is canonical: integers are decimal strings and bytes are lowercase hex, so the
/// report's bytes do not depend on a number's size.
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Value {
    /// An `Int`.
    Int(#[serde(with = "decimal_int")] BigInt),
    /// A `Bool`.
    Bool(bool),
    /// A `String`: a sequence of Unicode scalar values.
    String(String),
    /// A `Bytes`.
    Bytes(#[serde(with = "hex_bytes")] Vec<u8>),
    /// An `MInt{width}`: an unsigned value below `2^width`.
    MInt {
        /// The width in bits.
        width: u32,
        /// The value.
        #[serde(with = "decimal_uint")]
        value: BigUint,
    },
    /// A token of a user token sort, admitted by an explicit override (ARCHITECTURE 2.4).
    Token {
        /// The token sort's name.
        sort: String,
        /// The token's text.
        text: String,
    },
    /// A `List`, in order.
    List(Vec<Value>),
    /// A `Set`; elements are kept sorted and distinct.
    Set(Vec<Value>),
    /// A `Map`; entries are kept sorted by key, with distinct keys.
    Map(Vec<(Value, Value)>),
    /// A constructor application of a data sort (M3; ARCHITECTURE 3, R-20).
    Apply {
        /// The constructor's KORE symbol name.
        symbol: String,
        /// The arguments, in order.
        arguments: Vec<Value>,
    },
}

/// The sort of values a hole takes, resolved from its declared sort and element sorts against
/// the baseline definition (ARCHITECTURE 2.4, 2.5, 3).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ValueSort {
    /// The hooked `Int` sort.
    Int,
    /// The hooked `Bool` sort.
    Bool,
    /// The hooked `String` sort.
    String,
    /// The hooked `Bytes` sort.
    Bytes,
    /// `MInt{width}`.
    MInt {
        /// The width in bits.
        width: u32,
    },
    /// A user token sort admitted by an override.
    Token {
        /// The sort's name.
        sort: String,
    },
    /// A `List` with a declared element sort.
    List {
        /// The element sort.
        element: Box<ValueSort>,
    },
    /// A `Set` with a declared element sort.
    Set {
        /// The element sort.
        element: Box<ValueSort>,
    },
    /// A `Map` with declared key and value sorts.
    Map {
        /// The key sort.
        key: Box<ValueSort>,
        /// The value sort.
        value: Box<ValueSort>,
    },
    /// A user data sort outside the program syntax closure (M3).
    Data {
        /// The sort's name.
        sort: String,
    },
}

/// Constraints a hole declaration may carry (ARCHITECTURE 2.5).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct Constraints {
    /// An inclusive integer range, for `Int` and `MInt` holes.
    pub range: Option<IntRange>,
    /// An inclusive length range for `String`, `Bytes`, `List`, `Set` and `Map` holes.
    pub length: Option<LengthRange>,
    /// Element sorts of a collection hole, since K collections hold `KItem`.
    pub elements: Option<ElementSorts>,
    /// An explicit choice set: the hole takes only these values.
    pub choices: Option<Vec<Value>>,
}

/// An inclusive integer range; an absent end is unbounded.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct IntRange {
    /// The least value.
    #[serde(default, with = "decimal_int_opt")]
    pub min: Option<BigInt>,
    /// The greatest value.
    #[serde(default, with = "decimal_int_opt")]
    pub max: Option<BigInt>,
}

/// An inclusive length range; an absent end takes the default bound.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct LengthRange {
    /// The least length.
    pub min: Option<u64>,
    /// The greatest length.
    pub max: Option<u64>,
}

/// Declared element sorts of a collection hole (`List<Int>`, `Map<Id, Int>`), as sort names of
/// the definition.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "collection", rename_all = "kebab-case")]
pub enum ElementSorts {
    /// The element sort of a `List` or `Set`.
    Elements {
        /// The element sort.
        element: String,
    },
    /// The key and value sorts of a `Map`.
    Entries {
        /// The key sort.
        key: String,
        /// The value sort.
        value: String,
    },
}

/// Default bounds of generated values; the report records the bounds used (ARCHITECTURE 2.5).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct GenerationBounds {
    /// The largest bit length of a generated integer without a range.
    pub int_bits: u32,
    /// The largest length of a generated string, byte string or collection without a length
    /// range.
    pub length: u64,
    /// The largest depth of a generated data-sort term.
    pub depth: u32,
}

impl Default for GenerationBounds {
    fn default() -> Self {
        Self {
            int_bits: 64,
            length: 16,
            depth: 4,
        }
    }
}

/// Resolve a hole's declared sort and element sorts against `definition` (the baseline's
/// internalized definition) into the sort of values it takes, applying the generator part of
/// the hole-sort rule (ARCHITECTURE 2.4, 3): a hooked sort without a generator, or a collection
/// without element sorts, is refused. The program-syntax closure and the token rule are
/// FZ-02's ([`crate::holes::check_hole_sort`]).
///
/// # Errors
///
/// The refusal, as [`crate::error::SortRefusal`].
pub(crate) fn resolve_value_sort(
    sort: &str,
    constraints: &Constraints,
    definition: &k_rust::k_rust_backend::definition::BackendDefinition,
) -> Result<ValueSort, crate::error::SortRefusal> {
    unimplemented!("FZ-03")
}

/// Check `value` against `sort` and `constraints` (ARCHITECTURE 2.5): its shape matches the
/// sort, integers lie in the range and below the width, lengths lie in the length range, and a
/// choice set contains it. Explicit assignments, anchors and shrink moves of non-proptest values
/// are checked with it; a violation makes a case `rejected` (ARCHITECTURE 5.3).
///
/// # Errors
///
/// A message naming the violated constraint.
pub(crate) fn check_constraints(
    value: &Value,
    sort: &ValueSort,
    constraints: &Constraints,
) -> Result<(), String> {
    unimplemented!("FZ-03")
}

/// Serialize a [`BigInt`] as a decimal string.
mod decimal_int {
    use num_bigint::BigInt;
    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    pub(super) fn serialize<S: Serializer>(
        value: &BigInt,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_str(value)
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<BigInt, D::Error> {
        String::deserialize(deserializer)?
            .parse()
            .map_err(D::Error::custom)
    }
}

/// Serialize an optional [`BigInt`] as an optional decimal string.
mod decimal_int_opt {
    use num_bigint::BigInt;
    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    #[expect(
        clippy::ref_option,
        reason = "serde's `with` passes a reference to the field"
    )]
    pub(super) fn serialize<S: Serializer>(
        value: &Option<BigInt>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        match value {
            Some(value) => serializer.collect_str(value),
            None => serializer.serialize_none(),
        }
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<BigInt>, D::Error> {
        Option::<String>::deserialize(deserializer)?
            .map(|text| text.parse().map_err(D::Error::custom))
            .transpose()
    }
}

/// Serialize a [`BigUint`] as a decimal string.
mod decimal_uint {
    use num_bigint::BigUint;
    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    pub(super) fn serialize<S: Serializer>(
        value: &BigUint,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_str(value)
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<BigUint, D::Error> {
        String::deserialize(deserializer)?
            .parse()
            .map_err(D::Error::custom)
    }
}

/// Serialize bytes as a lowercase hex string.
mod hex_bytes {
    use std::fmt::Write as _;

    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    pub(super) fn serialize<S: Serializer>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error> {
        let mut text = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            write!(text, "{byte:02x}").expect("writing to a String does not fail");
        }
        serializer.serialize_str(&text)
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<u8>, D::Error> {
        let text = String::deserialize(deserializer)?;
        if text.len() % 2 != 0 {
            return Err(D::Error::custom("odd number of hex digits"));
        }
        (0..text.len())
            .step_by(2)
            .map(|at| {
                text.get(at..at + 2)
                    .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                    .ok_or_else(|| D::Error::custom("invalid hex digit"))
            })
            .collect()
    }
}
