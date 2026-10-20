//! Hole values in a definition-independent form, their sorts and constraints, generators and
//! K-text printing (ARCHITECTURE 2.5, 3). Owner: FZ-03.
//!
//! A [`Value`] holds no backend term: an internalized `Term` belongs to one
//! `BackendDefinition`, and a differential campaign internalizes each value once per side
//! (ARCHITECTURE 2.3, R-14).
//!
//! A [`ValueSort`] is resolved once against the baseline definition by [`resolve_value_sort`]
//! and then carries everything generation and printing read from the definition (the collection
//! symbols of a collection sort, the constructor table of a data sort), so that
//! [`Generator::new`], [`print::print_k_text`] and [`print::to_kore`] need no definition.
//!
//! The module uses only `core` and `alloc` facilities (no I/O, clock, environment or hashing
//! state), as proptest's `no_std` build does.

pub(crate) mod generator;
pub(crate) mod print;
#[cfg(test)]
mod tests;

use k_rust::{
    k_rust_backend::{
        definition::BackendDefinition,
        term::{DomainKind, MIntWidth, Sort as BackendSort},
    },
    kast::parser::parse_sort,
    kompile::encode_kore_sort,
    kore::ast::Sort as KoreSort,
    names::{BuiltinSort, MINT_SORT},
};
use num_bigint::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

pub(crate) use generator::{Generator, ShrinkableValue, ValueRng};

use crate::error::SortRefusal;

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
/// the baseline definition (ARCHITECTURE 2.4, 2.5, 3) by [`resolve_value_sort`].
///
/// It is self-contained: what generating and printing a value need from the definition is
/// copied in at resolution (FZ-01 review S6).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ValueSort {
    /// `Int`, hooked `INT.Int` (KORE `SortInt`).
    Int,
    /// `Bool`, hooked `BOOL.Bool` (KORE `SortBool`).
    Bool,
    /// `String`, hooked `STRING.String` (KORE `SortString`).
    String,
    /// `Bytes`, hooked `BYTES.Bytes` (KORE `SortBytes`).
    Bytes,
    /// `MInt{width}`, hooked `MINT.MInt` (KORE `SortMInt{Sort<width>{}}`).
    MInt {
        /// The width in bits.
        width: u32,
    },
    /// A user token sort admitted by an override.
    Token {
        /// The sort's K name, as declared in the hole (`Id`).
        sort: String,
    },
    /// A sort hooked `LIST.List`, with a declared element sort.
    List {
        /// The sort's K name, as declared in the hole (`List`).
        sort: String,
        /// The sort's unit, element and concatenation symbols.
        symbols: CollectionSymbols,
        /// The element sort.
        element: Box<ValueSort>,
    },
    /// A sort hooked `SET.Set`, with a declared element sort.
    Set {
        /// The sort's K name, as declared in the hole (`Set`).
        sort: String,
        /// The sort's unit, element and concatenation symbols.
        symbols: CollectionSymbols,
        /// The element sort.
        element: Box<ValueSort>,
    },
    /// A sort hooked `MAP.Map`, with declared key and value sorts.
    Map {
        /// The sort's K name, as declared in the hole (`Map`).
        sort: String,
        /// The sort's unit, element (`_|->_`) and concatenation symbols.
        symbols: CollectionSymbols,
        /// The key sort.
        key: Box<ValueSort>,
        /// The value sort.
        value: Box<ValueSort>,
    },
    /// A user data sort outside the program syntax closure (M3).
    Data {
        /// The sort's K name, as declared in the hole (`Tx`).
        sort: String,
        /// The constructors of this sort (entry 0) and of every data sort their arguments
        /// reach. Filled by FZ-09 (M3); empty in M1, where a data hole draws only from a
        /// choice set.
        table: DataSorts,
    },
}

/// The KORE symbols a collection sort's values are built from: its `unit`, `element` and
/// `concat` hooks (`.List`, `ListItem`, `_List_` for the prelude's `List`).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct CollectionSymbols {
    /// The KORE sort name (`SortList`).
    pub kore_sort: String,
    /// The unit symbol (`Lbl'Stop'List`).
    pub unit: String,
    /// The element symbol (`LblListItem`, or `Lbl'UndsPipe'-'-GT-Unds'` for a map).
    pub element: String,
    /// The concatenation symbol (`Lbl'Unds'List'Unds'`).
    pub concat: String,
}

/// The constructor table of a data hole: the hole's sort is entry 0, and an argument of a data
/// sort names its entry by index, so that recursive sorts are finite (FZ-01 review S6).
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct DataSorts {
    /// The entries.
    pub sorts: Vec<DataSort>,
}

/// One data sort of a [`DataSorts`] table.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct DataSort {
    /// The KORE sort name.
    pub kore_sort: String,
    /// The constructors whose result sort is this sort or a subsort (ARCHITECTURE 3).
    pub constructors: Vec<DataConstructor>,
}

/// A constructor a data-sort value may be built with.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct DataConstructor {
    /// The KORE symbol name.
    pub symbol: String,
    /// The KORE name of the symbol's result sort; an application is injected from it to the
    /// entry's sort when they differ.
    pub result_kore_sort: String,
    /// The argument sorts, in order.
    pub arguments: Vec<ArgumentSort>,
}

/// The sort of a constructor's argument.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ArgumentSort {
    /// A sort with its own generator (a builtin or collection sort).
    Value(ValueSort),
    /// The data sort at this index of the table.
    Data(usize),
}

/// Constraints a hole declaration may carry (ARCHITECTURE 2.5).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct Constraints {
    /// An inclusive integer range, for `Int` and `MInt` holes (for `MInt`, of the unsigned
    /// value).
    pub range: Option<IntRange>,
    /// An inclusive length range for `String` (in code points), `Bytes`, `List`, `Set` and
    /// `Map` holes.
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
///
/// - An `Int` without a range lies within `int_bits` bits of zero (`|v| < 2^int_bits`); an
///   `Int` with one bounded end lies within `int_bits` bits of the range's value nearest zero.
///   A range with both ends is used whole.
/// - A `String`, `Bytes` or collection without a length range is at most `length` long; with a
///   minimum only, at most `max(min, length)` long.
/// - A data-sort term is at most `depth` constructors deep (M3).
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
    /// 64 bits (the machine-word boundaries that programs and guards test), length 16, depth 4.
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
/// the hole-sort rule (ARCHITECTURE 2.4, 3). The program-syntax closure and the token rule are
/// FZ-02's ([`crate::holes::check_hole_sort`]).
///
/// The kind of a sort is read from its hook and domain values
/// ([`BackendDefinition::domain_kind`]), never from its name:
///
/// - `Int`, `Bool`, `String`, `Bytes` and `MInt{W}` resolve to their builtin value sorts;
/// - a sort with domain values and no hook (`Id`) resolves to a token sort;
/// - a sort hooked `LIST.List`, `SET.Set` or `MAP.Map` resolves to a collection when the
///   constraints name element sorts of the right shape and they resolve, with the symbols its
///   `unit`, `element` and `concat` hooks name;
/// - a sort without hook and without domain values resolves to a data sort.
///
/// # Errors
///
/// - [`SortRefusal::Unknown`]: the text is not a sort, or the definition does not declare it;
/// - [`SortRefusal::NoGenerator`]: any other hooked sort (`Float`, `KVar`, IO handles, a
///   `MINT.MInt` sort without a width), and a sort hooked to a builtin of the list above under
///   another name (`syntax MyInt [hook(INT.Int)]`), whose KORE sort this milestone's printer does
///   not name;
/// - [`SortRefusal::Collection`]: a collection without element sorts, with element sorts of the
///   wrong shape, with an element sort that does not resolve, or whose sort lacks one of its
///   three symbols.
pub(crate) fn resolve_value_sort(
    sort: &str,
    constraints: &Constraints,
    definition: &BackendDefinition,
) -> Result<ValueSort, SortRefusal> {
    let text = sort.trim();
    let kast = parse_sort(text).map_err(|_| SortRefusal::Unknown)?;
    let kore = backend_sort(&encode_kore_sort(&kast));
    let BackendSort::Application { name, .. } = &kore else {
        return Err(SortRefusal::Unknown);
    };
    let info = definition.sorts().get(name).ok_or(SortRefusal::Unknown)?;
    let hook = info.hook.as_deref();
    let builtin = |builtin: BuiltinSort, resolved: ValueSort| {
        if kore.is_builtin(builtin) {
            Ok(resolved)
        } else {
            Err(SortRefusal::NoGenerator)
        }
    };
    match definition.domain_kind(&kore) {
        Some(DomainKind::Int) => builtin(BuiltinSort::Int, ValueSort::Int),
        Some(DomainKind::Bool) => builtin(BuiltinSort::Bool, ValueSort::Bool),
        Some(DomainKind::String) => builtin(BuiltinSort::String, ValueSort::String),
        Some(DomainKind::Bytes) => builtin(BuiltinSort::Bytes, ValueSort::Bytes),
        Some(DomainKind::MInt(MIntWidth::Bits(width))) if name.as_ref() == MINT_SORT => {
            u32::try_from(width)
                .map(|width| ValueSort::MInt { width })
                .map_err(|_| SortRefusal::NoGenerator)
        }
        Some(DomainKind::Token) if hook.is_none() => Ok(ValueSort::Token {
            sort: text.to_owned(),
        }),
        Some(_) => Err(SortRefusal::NoGenerator),
        None => match hook {
            None if !info.has_domain_values => Ok(ValueSort::Data {
                sort: text.to_owned(),
                table: DataSorts::default(),
            }),
            Some(hook @ ("LIST.List" | "SET.Set" | "MAP.Map")) => {
                resolve_collection(text, name, hook, constraints, definition)
            }
            _ => Err(SortRefusal::NoGenerator),
        },
    }
}

/// The collection sort `text` (KORE name `kore_name`, hooked `hook`) with the element sorts
/// `constraints` declares.
fn resolve_collection(
    text: &str,
    kore_name: &str,
    hook: &str,
    constraints: &Constraints,
    definition: &BackendDefinition,
) -> Result<ValueSort, SortRefusal> {
    let element = |sort: &str| {
        resolve_value_sort(sort, &Constraints::default(), definition)
            .map(Box::new)
            .map_err(|_| SortRefusal::Collection)
    };
    let namespace = hook
        .split_once('.')
        .map_or(hook, |(namespace, _)| namespace);
    let symbols = collection_symbols(kore_name, namespace, definition)?;
    let sort = text.to_owned();
    match (namespace, &constraints.elements) {
        ("LIST", Some(ElementSorts::Elements { element: name })) => Ok(ValueSort::List {
            sort,
            symbols,
            element: element(name)?,
        }),
        ("SET", Some(ElementSorts::Elements { element: name })) => Ok(ValueSort::Set {
            sort,
            symbols,
            element: element(name)?,
        }),
        ("MAP", Some(ElementSorts::Entries { key, value })) => Ok(ValueSort::Map {
            sort,
            symbols,
            key: element(key)?,
            value: element(value)?,
        }),
        _ => Err(SortRefusal::Collection),
    }
}

/// The symbols of result sort `kore_name` hooked `<namespace>.unit`, `.element` and `.concat`;
/// each must be unique.
fn collection_symbols(
    kore_name: &str,
    namespace: &str,
    definition: &BackendDefinition,
) -> Result<CollectionSymbols, SortRefusal> {
    let find = |operation: &str| {
        let hook = format!("{namespace}.{operation}");
        let mut found = definition.symbols().values().filter(|symbol| {
            symbol.attributes.hook.as_deref() == Some(hook.as_str())
                && matches!(&symbol.result_sort, BackendSort::Application { name, arguments }
                    if arguments.is_empty() && name.as_ref() == kore_name)
        });
        match (found.next(), found.next()) {
            (Some(symbol), None) => Ok(symbol.name.to_string()),
            _ => Err(SortRefusal::Collection),
        }
    };
    Ok(CollectionSymbols {
        kore_sort: kore_name.to_owned(),
        unit: find("unit")?,
        element: find("element")?,
        concat: find("concat")?,
    })
}

/// `sort` as the backend's sort type.
fn backend_sort(sort: &KoreSort) -> BackendSort {
    match sort {
        KoreSort::Variable(name) => BackendSort::Variable(name.as_str().into()),
        KoreSort::Application { name, arguments } => {
            BackendSort::application(name.as_str(), arguments.iter().map(backend_sort).collect())
        }
    }
}

/// Check that `constraints` suit `sort` and admit a value (ARCHITECTURE 2.5): a range only on
/// `Int` and `MInt` (for `MInt`, meeting `[0, 2^width)`), a length range only on `String`,
/// `Bytes` and collections, element sorts only on collections, ends in order, and a non-empty
/// choice set whose every member satisfies the other constraints. [`Generator::new`] calls it.
///
/// # Errors
///
/// A message naming the inconsistency, which the caller reports as
/// [`crate::CampaignError::InvalidConstraints`].
pub(crate) fn validate_constraints(
    sort: &ValueSort,
    constraints: &Constraints,
) -> Result<(), String> {
    if let Some(range) = &constraints.range {
        if let (Some(min), Some(max)) = (&range.min, &range.max)
            && min > max
        {
            return Err(format!("the range [{min}, {max}] is empty"));
        }
        match sort {
            ValueSort::Int => {}
            ValueSort::MInt { width } => {
                if mint_bounds(*width, range).is_none() {
                    return Err(format!(
                        "the range does not meet the values of MInt{{{width}}}, [0, 2^{width})"
                    ));
                }
            }
            _ => return Err("a range applies only to Int and MInt holes".to_owned()),
        }
    }
    if let Some(length) = constraints.length {
        if !matches!(
            sort,
            ValueSort::String
                | ValueSort::Bytes
                | ValueSort::List { .. }
                | ValueSort::Set { .. }
                | ValueSort::Map { .. }
        ) {
            return Err(
                "a length range applies only to String, Bytes, List, Set and Map holes".to_owned(),
            );
        }
        if let (Some(min), Some(max)) = (length.min, length.max)
            && min > max
        {
            return Err(format!("the length range [{min}, {max}] is empty"));
        }
    }
    if constraints.elements.is_some()
        && !matches!(
            sort,
            ValueSort::List { .. } | ValueSort::Set { .. } | ValueSort::Map { .. }
        )
    {
        return Err("element sorts apply only to List, Set and Map holes".to_owned());
    }
    if let Some(choices) = &constraints.choices {
        if choices.is_empty() {
            return Err("the choice set is empty".to_owned());
        }
        let others = Constraints {
            choices: None,
            ..constraints.clone()
        };
        for (index, choice) in choices.iter().enumerate() {
            check_constraints(choice, sort, &others)
                .map_err(|message| format!("choice {index}: {message}"))?;
        }
    }
    Ok(())
}

/// The unsigned values `[lo, hi]` of `MInt{width}` inside `range`, or `None` when none is.
fn mint_bounds(width: u32, range: &IntRange) -> Option<(BigUint, BigUint)> {
    let top = (BigUint::from(1u8) << width) - 1u8;
    let lo = match &range.min {
        Some(min) => BigUint::try_from(min).unwrap_or_default(),
        None => BigUint::default(),
    };
    let hi = match &range.max {
        Some(max) => BigUint::try_from(max).ok()?.min(top),
        None => top,
    };
    (lo <= hi).then_some((lo, hi))
}

/// Check `value` against `sort` and `constraints` (ARCHITECTURE 2.5): its shape matches the
/// sort, integers lie in the range and below the width, lengths lie in the length range, and a
/// choice set contains it. Explicit assignments, anchors and shrink moves of non-proptest values
/// are checked with it; a violation makes a case `rejected` (ARCHITECTURE 5.3).
///
/// The shape check is recursive: a collection's elements have the element sorts, a set's
/// elements and a map's keys are sorted and distinct, and a data value applies a constructor of
/// the sort's table to arguments of its argument sorts (when the table is filled, M3).
///
/// # Errors
///
/// A message naming the violated constraint.
pub(crate) fn check_constraints(
    value: &Value,
    sort: &ValueSort,
    constraints: &Constraints,
) -> Result<(), String> {
    check_shape(value, sort)?;
    if let Some(range) = &constraints.range {
        let number = match value {
            Value::Int(number) => number.clone(),
            Value::MInt { value, .. } => BigInt::from(value.clone()),
            _ => return Err("a range applies only to Int and MInt values".to_owned()),
        };
        if let Some(min) = &range.min
            && number < *min
        {
            return Err(format!("{number} is below the range's minimum {min}"));
        }
        if let Some(max) = &range.max
            && number > *max
        {
            return Err(format!("{number} is above the range's maximum {max}"));
        }
    }
    if let Some(length) = constraints.length {
        let count = match value {
            Value::String(text) => text.chars().count(),
            Value::Bytes(bytes) => bytes.len(),
            Value::List(items) | Value::Set(items) => items.len(),
            Value::Map(entries) => entries.len(),
            _ => {
                return Err(
                    "a length range applies only to String, Bytes, List, Set and Map values"
                        .to_owned(),
                );
            }
        };
        let count = u64::try_from(count).unwrap_or(u64::MAX);
        if let Some(min) = length.min
            && count < min
        {
            return Err(format!("length {count} is below the minimum {min}"));
        }
        if let Some(max) = length.max
            && count > max
        {
            return Err(format!("length {count} is above the maximum {max}"));
        }
    }
    if let Some(choices) = &constraints.choices
        && !choices.contains(value)
    {
        return Err("the value is not in the choice set".to_owned());
    }
    Ok(())
}

/// Check that `value` is a value of `sort`.
pub(crate) fn check_shape(value: &Value, sort: &ValueSort) -> Result<(), String> {
    match (value, sort) {
        (Value::Int(_), ValueSort::Int)
        | (Value::Bool(_), ValueSort::Bool)
        | (Value::String(_), ValueSort::String)
        | (Value::Bytes(_), ValueSort::Bytes) => Ok(()),
        (Value::MInt { width, value }, ValueSort::MInt { width: expected }) => {
            if width != expected {
                Err(format!("an MInt{{{width}}} value at MInt{{{expected}}}"))
            } else if value.bits() > u64::from(*width) {
                Err(format!("{value} does not fit in {width} bits"))
            } else {
                Ok(())
            }
        }
        (Value::Token { sort, text }, ValueSort::Token { sort: expected }) => {
            if sort != expected {
                Err(format!("a token of {sort} at {expected}"))
            } else if text.is_empty() {
                Err("an empty token".to_owned())
            } else {
                Ok(())
            }
        }
        (Value::List(items), ValueSort::List { element, .. }) => {
            items.iter().try_for_each(|item| check_shape(item, element))
        }
        (Value::Set(items), ValueSort::Set { element, .. }) => {
            if items.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err("a Set's elements are not sorted and distinct".to_owned());
            }
            items.iter().try_for_each(|item| check_shape(item, element))
        }
        (Value::Map(entries), ValueSort::Map { key, value, .. }) => {
            if entries.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
                return Err("a Map's keys are not sorted and distinct".to_owned());
            }
            entries.iter().try_for_each(|(entry_key, entry_value)| {
                check_shape(entry_key, key)?;
                check_shape(entry_value, value)
            })
        }
        (Value::Apply { .. }, ValueSort::Data { table, .. }) => {
            if table.sorts.is_empty() {
                Ok(())
            } else {
                check_data(value, table, 0)
            }
        }
        _ => Err("the value is not of the hole's sort".to_owned()),
    }
}

/// Check that `value` applies a constructor of entry `index` of `table` to arguments of its
/// argument sorts.
fn check_data(value: &Value, table: &DataSorts, index: usize) -> Result<(), String> {
    let Value::Apply { symbol, arguments } = value else {
        return Err("a data-sort argument is not a constructor application".to_owned());
    };
    let entry = table
        .sorts
        .get(index)
        .ok_or_else(|| format!("the data-sort table has no entry {index}"))?;
    let constructor = entry
        .constructors
        .iter()
        .find(|constructor| constructor.symbol == *symbol)
        .ok_or_else(|| format!("{symbol} is not a constructor of {}", entry.kore_sort))?;
    if constructor.arguments.len() != arguments.len() {
        return Err(format!(
            "{symbol} takes {} arguments, not {}",
            constructor.arguments.len(),
            arguments.len()
        ));
    }
    constructor
        .arguments
        .iter()
        .zip(arguments)
        .try_for_each(|(sort, argument)| match sort {
            ArgumentSort::Value(sort) => check_shape(argument, sort),
            ArgumentSort::Data(index) => check_data(argument, table, *index),
        })
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
    use core::fmt::Write as _;

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
