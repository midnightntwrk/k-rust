//! Hole values in a definition-independent form, their sorts and constraints, generators and
//! K-text printing (ARCHITECTURE 2.5, 3). Owner: FZ-03.
//!
//! A [`Value`] holds no backend term: an internalized `Term` belongs to one
//! `BackendDefinition`, and a differential campaign internalizes each value once per side
//! (ARCHITECTURE 2.3, R-14).
//!
//! A [`ValueSort`] is resolved once against the baseline definition by [`resolve_value_sort`]
//! (or [`TextSyntax::resolve`], which also attaches the definition's K-text syntax) and then
//! carries everything generation and printing read from the definition (the collection symbols of
//! a collection sort, the constructor table of a data sort, the shared [`TextSyntax`]), so that
//! [`Generator::new`], [`print::print_k_text`], [`print::to_kore`] and [`print::parse_k_text`]
//! need no definition.
//!
//! The module reads no I/O, clock, environment or hashing state, as proptest's `no_std` build
//! requires; the K-text syntax (`text.rs`) shares its parsers through `std::sync` and prints
//! with krs-unparse, which also does no I/O and builds for WebAssembly.

mod data;
#[cfg(test)]
mod data_tests;
pub(crate) mod generator;
pub(crate) mod print;
pub(crate) mod term;
#[cfg(test)]
mod test_definition;
#[cfg(test)]
mod tests;
pub mod text;

use k_rust::{
    k_rust_backend::{
        definition::BackendDefinition,
        term::{DomainKind, Sort as BackendSort},
    },
    kast::parser::parse_sort,
    kompile::encode_kore_sort,
    kore::ast::Sort as KoreSort,
};
use num_bigint::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

pub(crate) use generator::{Generator, ShrinkableValue, ValueRng};
pub use text::TextSyntax;

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
    /// A sort hooked to one of the builtins above under its own name
    /// (`syntax MyInt [hook(INT.Int)]`): its values are those of `base`, and their KORE domain
    /// values are at `kore_sort`.
    Renamed {
        /// The sort's K name (`MyInt`).
        sort: String,
        /// The sort's KORE name (`SortMyInt`).
        kore_sort: String,
        /// The builtin whose values the sort has (never itself `Renamed`).
        base: Box<ValueSort>,
    },
    /// A sort hooked `LIST.List`, with a declared element sort.
    List {
        /// The sort's K name, as declared in the hole (`List`).
        sort: String,
        /// The sort's unit, element and concatenation symbols.
        symbols: CollectionSymbols,
        /// The element sort.
        element: Box<ValueSort>,
        /// The definition's K-text syntax, which prints and reads the collection's values;
        /// `None` when the sort was resolved without one ([`resolve_value_sort`]).
        #[serde(skip)]
        text: Option<TextSyntax>,
    },
    /// A sort hooked `SET.Set`, with a declared element sort.
    Set {
        /// The sort's K name, as declared in the hole (`Set`).
        sort: String,
        /// The sort's unit, element and concatenation symbols.
        symbols: CollectionSymbols,
        /// The element sort.
        element: Box<ValueSort>,
        /// The definition's K-text syntax (see [`ValueSort::List`]).
        #[serde(skip)]
        text: Option<TextSyntax>,
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
        /// The definition's K-text syntax (see [`ValueSort::List`]).
        #[serde(skip)]
        text: Option<TextSyntax>,
    },
    /// A user data sort outside the program syntax closure (ARCHITECTURE 3).
    Data {
        /// The sort's K name, as declared in the hole (`Tx`).
        sort: String,
        /// The constructors of this sort (entry 0) and of every data sort their arguments
        /// reach, with their heights.
        table: DataSorts,
        /// The definition's K-text syntax, which prints and reads the sort's values; `None`
        /// when the sort was resolved without one ([`resolve_value_sort`]).
        #[serde(skip)]
        text: Option<TextSyntax>,
    },
}

impl ValueSort {
    /// The sort whose generator, constraints and value shapes this sort uses: `base` for a
    /// [`ValueSort::Renamed`] sort, the sort itself otherwise.
    #[must_use]
    pub fn generated(&self) -> &Self {
        match self {
            Self::Renamed { base, .. } => base,
            _ => self,
        }
    }
}

/// The kind of a collection sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CollectionKind {
    /// Hooked `LIST.List`.
    List,
    /// Hooked `SET.Set`.
    Set,
    /// Hooked `MAP.Map`.
    Map,
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
    /// The KORE argument sorts of the element symbol (`[SortKItem]` for `ListItem`, the key and
    /// value sorts for `_|->_`): an element is injected to them.
    pub element_arguments: Vec<String>,
}

/// The constructor table of a data hole: the hole's sort is entry 0, and an argument of a data
/// sort names its entry by index, so that recursive sorts are finite (FZ-01 review S6).
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct DataSorts {
    /// The entries.
    pub sorts: Vec<DataSort>,
}

/// One data sort of a [`DataSorts`] table (`values/data.rs` states how it is built).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct DataSort {
    /// The KORE sort name.
    pub kore_sort: String,
    /// The least height of a value of the sort (constructor applications nested on a path),
    /// or `None` when the generator can build none.
    pub height: Option<u32>,
    /// The admissible, inhabited constructors whose result sort is this sort or a subsort
    /// (ARCHITECTURE 3), lowest first.
    pub constructors: Vec<DataConstructor>,
    /// The subsorts that are not data sorts (builtin sorts with a generator, collections), whose
    /// values are values of this sort through an injection; each has height 0.
    pub subsorts: Vec<ArgumentSort>,
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
    /// The least height of an application (one more than the greatest least height of its data
    /// arguments); `None` only while the table is built.
    pub height: Option<u32>,
    /// The argument sorts, in order.
    pub arguments: Vec<ArgumentSort>,
}

/// The sort of a constructor's argument, or a non-data subsort of a data sort.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ArgumentSort {
    /// A builtin sort with its own generator (`Int`, `Bool`, `String`, `Bytes`, `MInt`, or one of
    /// them renamed).
    Value(ValueSort),
    /// The data sort at this index of the table.
    Data(usize),
    /// A collection sort whose element sorts the definition does not state: only its empty
    /// collection is generated.
    Empty(EmptyCollection),
}

/// A collection sort of which only the empty collection is generated.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct EmptyCollection {
    /// The collection's kind.
    pub kind: CollectionKind,
    /// The collection's symbols; the empty collection is the unit.
    pub symbols: CollectionSymbols,
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
/// - A data-sort term is at most `depth` constructor applications deep: every path from its root
///   meets at most `depth` applications (a builtin leaf or an empty collection adds none).
///
/// [`validate_bounds`] refuses bounds above [`MAX_INT_BITS`], [`MAX_GENERATED_LENGTH`] and
/// [`MAX_DEPTH`], and [`Generator::new`] keeps every value within [`MAX_VALUE_SIZE`], so that no
/// bound makes generation allocate without limit.
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

/// The largest `int_bits` bound: an unranged integer has at most this many bits (4096 bits is a
/// 512-byte number, beyond any machine word and any cryptographic size a guard tests).
pub const MAX_INT_BITS: u32 = 4096;

/// The cap on generated lengths: the largest `length` bound, the largest minimum of a length
/// range, and the length a length range's maximum is clamped to when values are generated.
/// A value is drawn whole before it runs, so a length beyond it would allocate without limit.
pub const MAX_GENERATED_LENGTH: u64 = 1 << 16;

/// The largest `depth` bound of data-sort terms.
pub const MAX_DEPTH: u32 = 16;

/// The size budget of one generated value: one unit per constructor application or leaf, plus
/// one per 64 bits of an integer and one per character or byte of a string. A data hole whose
/// largest value at the depth bound exceeds it is refused (the message names the depth that
/// fits); a collection's maximum length is lowered so that its elements' largest values fit.
/// The caps on each dimension alone ([`MAX_DEPTH`], [`MAX_GENERATED_LENGTH`]) do not bound a
/// value: a wide constructor grows exponentially with depth, and lengths multiply when
/// collections hold strings.
pub const MAX_VALUE_SIZE: u128 = 1 << 17;

/// The deepest value read back from KORE ([`print::parse_k_text`], the anchors) or checked
/// against its sort ([`check_constraints`]): the number of values on its longest path from the
/// value down (a builtin is 1 level, `leaf(0)` 2, a collection one more than its deepest
/// element). Both recurse once per level, and an anchor written by hand can be nested to any
/// depth, which the frontend reads, so a deeper value is refused rather than allowed to exhaust
/// the stack (FZ-G6+09 review N8). Generated values are at most [`MAX_DEPTH`] constructors deep;
/// this bound leaves room for hand-written anchors, such as a K user list (`List{Int, ","}`) of
/// a thousand items, and its recursion fits in a 2 MiB thread stack.
pub const MAX_VALUE_DEPTH: usize = 1024;

/// Check `bounds` against [`MAX_INT_BITS`], [`MAX_GENERATED_LENGTH`] and [`MAX_DEPTH`].
/// [`Generator::new`] calls it.
///
/// # Errors
///
/// A message naming the bound that exceeds its cap.
pub(crate) fn validate_bounds(bounds: &GenerationBounds) -> Result<(), String> {
    if bounds.int_bits > MAX_INT_BITS {
        return Err(format!(
            "the int-bits bound {} exceeds its cap, {MAX_INT_BITS}",
            bounds.int_bits
        ));
    }
    if bounds.length > MAX_GENERATED_LENGTH {
        return Err(format!(
            "the length bound {} exceeds its cap, {MAX_GENERATED_LENGTH}",
            bounds.length
        ));
    }
    if bounds.depth > MAX_DEPTH {
        return Err(format!(
            "the depth bound {} exceeds its cap, {MAX_DEPTH}",
            bounds.depth
        ));
    }
    Ok(())
}

impl Default for GenerationBounds {
    /// 64 bits, length 16, depth 4. A 64-bit window holds every machine-word boundary that
    /// programs and guards test (`2^31`, `2^63 - 1`, `-2^63`, ...); the generator draws them
    /// through its uniform choice of bit length, not as dedicated edge values (the edges of an
    /// unranged `Int` are `0`, `±1` and the window's ends `±(2^64 - 1)`).
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
/// The result carries no K-text syntax, so collection and data values resolved this way are
/// generated and converted to KORE but not printed or read as K text; [`TextSyntax::resolve`]
/// resolves with the syntax, and also leaves the program and cell sorts out of data tables.
///
/// The kind of a sort is read from its hook and domain values
/// ([`BackendDefinition::domain_kind`]), never from its name:
///
/// - `Int`, `Bool`, `String`, `Bytes` and `MInt{W}` resolve to their builtin value sorts, and a
///   sort hooked to one of them under another name (`syntax MyInt [hook(INT.Int)]`) to
///   [`ValueSort::Renamed`] with its KORE sort name;
/// - a sort with domain values and no hook (`Id`) resolves to a token sort;
/// - a sort hooked `LIST.List`, `SET.Set` or `MAP.Map` resolves to a collection when the
///   constraints name element sorts of the right shape and they resolve, with the symbols its
///   `unit`, `element` and `concat` hooks name;
/// - a sort without hook and without domain values resolves to a data sort with its constructor
///   table (`values/data.rs`).
///
/// # Errors
///
/// - [`SortRefusal::Unknown`]: the text is not a sort, or the definition does not declare it;
/// - [`SortRefusal::NoGenerator`]: any other hooked sort (`Float`, `KVar`, IO handles, a
///   `MINT.MInt` sort without a width), a parametric data sort, and a data sort of which no value
///   can be built from admissible constructors and inhabited argument sorts;
/// - [`SortRefusal::Collection`]: a collection without element sorts, with element sorts of the
///   wrong shape, or whose sort lacks one of its three symbols;
/// - [`SortRefusal::ElementRefused`]: a collection whose element, key or value sort is refused,
///   with that sort's own refusal.
pub(crate) fn resolve_value_sort(
    sort: &str,
    constraints: &Constraints,
    definition: &BackendDefinition,
) -> Result<ValueSort, SortRefusal> {
    resolve_with(sort, constraints, definition, None)
}

/// [`resolve_value_sort`], with the K-text syntax `text` attached to collection and data sorts
/// and its excluded sorts left out of data tables.
pub(super) fn resolve_with(
    sort: &str,
    constraints: &Constraints,
    definition: &BackendDefinition,
    text: Option<&TextSyntax>,
) -> Result<ValueSort, SortRefusal> {
    let text_sort = sort.trim();
    let kast = parse_sort(text_sort).map_err(|_| SortRefusal::Unknown)?;
    let kore = backend_sort(&encode_kore_sort(&kast));
    let BackendSort::Application { name, arguments } = &kore else {
        return Err(SortRefusal::Unknown);
    };
    let info = definition.sorts().get(name).ok_or(SortRefusal::Unknown)?;
    if let Some(builtin) = data::builtin_value_sort(&kore, definition) {
        return Ok(match builtin {
            ValueSort::Renamed {
                kore_sort, base, ..
            } => ValueSort::Renamed {
                sort: text_sort.to_owned(),
                kore_sort,
                base,
            },
            builtin => builtin,
        });
    }
    let hook = info.hook.as_deref();
    match definition.domain_kind(&kore) {
        Some(DomainKind::Token) if hook.is_none() => Ok(ValueSort::Token {
            sort: text_sort.to_owned(),
        }),
        Some(_) => Err(SortRefusal::NoGenerator),
        None => match hook {
            None if !info.has_domain_values => {
                // `K`, `KItem` and K's internal sorts are computations whatever the syntax.
                let internal = |name: &str| text::is_always_excluded(name);
                if internal(name) {
                    return Err(SortRefusal::Computation);
                }
                if !arguments.is_empty() || !info.parameters.is_empty() {
                    return Err(SortRefusal::NoGenerator);
                }
                if text.is_some_and(|text| text.is_excluded(name)) {
                    return Err(SortRefusal::ProgramSyntax);
                }
                let excluded =
                    |name: &str| text.map_or_else(|| internal(name), |text| text.is_excluded(name));
                Ok(ValueSort::Data {
                    sort: text_sort.to_owned(),
                    table: data::data_table(name, definition, &excluded)?,
                    text: text.cloned(),
                })
            }
            Some(hook @ ("LIST.List" | "SET.Set" | "MAP.Map")) => {
                resolve_collection(text_sort, name, hook, constraints, definition, text)
            }
            _ => Err(SortRefusal::NoGenerator),
        },
    }
}

/// The collection sort `text_sort` (KORE name `kore_name`, hooked `hook`) with the element sorts
/// `constraints` declares.
fn resolve_collection(
    text_sort: &str,
    kore_name: &str,
    hook: &str,
    constraints: &Constraints,
    definition: &BackendDefinition,
    text: Option<&TextSyntax>,
) -> Result<ValueSort, SortRefusal> {
    // A refused element sort refuses the collection with its own reason (FZ-G6+09 review N7).
    let element = |sort: &str| {
        resolve_with(sort, &Constraints::default(), definition, text)
            .map(Box::new)
            .map_err(|reason| SortRefusal::ElementRefused {
                element: sort.to_owned(),
                reason: Box::new(reason),
            })
    };
    let namespace = hook
        .split_once('.')
        .map_or(hook, |(namespace, _)| namespace);
    let symbols = collection_symbols(kore_name, namespace, definition)?;
    let sort = text_sort.to_owned();
    let text = text.cloned();
    match (namespace, &constraints.elements) {
        ("LIST", Some(ElementSorts::Elements { element: name })) => Ok(ValueSort::List {
            sort,
            symbols,
            element: element(name)?,
            text,
        }),
        ("SET", Some(ElementSorts::Elements { element: name })) => Ok(ValueSort::Set {
            sort,
            symbols,
            element: element(name)?,
            text,
        }),
        ("MAP", Some(ElementSorts::Entries { key, value })) => Ok(ValueSort::Map {
            sort,
            symbols,
            key: element(key)?,
            value: element(value)?,
            text,
        }),
        _ => Err(SortRefusal::Collection),
    }
}

/// The symbols of result sort `kore_name` hooked `<namespace>.unit`, `.element` and `.concat`;
/// each must be unique, and the element symbol's argument sorts closed.
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
            (Some(symbol), None) => Ok(symbol),
            _ => Err(SortRefusal::Collection),
        }
    };
    let element = find("element")?;
    let element_arguments = element
        .argument_sorts
        .iter()
        .map(|sort| match sort {
            BackendSort::Application { name, arguments } if arguments.is_empty() => {
                Ok(name.to_string())
            }
            _ => Err(SortRefusal::Collection),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CollectionSymbols {
        kore_sort: kore_name.to_owned(),
        unit: find("unit")?.name.to_string(),
        element: element.name.to_string(),
        concat: find("concat")?.name.to_string(),
        element_arguments,
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
/// choice set whose every member satisfies the other constraints. A length range's minimum
/// may not exceed [`MAX_GENERATED_LENGTH`] (its maximum is clamped to it when values are
/// generated). A renamed builtin takes the constraints of its base. [`Generator::new`] calls it.
///
/// # Errors
///
/// A message naming the inconsistency, which the caller reports as
/// [`crate::CampaignError::InvalidConstraints`].
pub(crate) fn validate_constraints(
    sort: &ValueSort,
    constraints: &Constraints,
) -> Result<(), String> {
    let sort = sort.generated();
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
    if let ValueSort::MInt { width } = sort
        && *width > MAX_INT_BITS
    {
        return Err(format!(
            "MInt{{{width}}} is wider than the cap on generated integers, {MAX_INT_BITS} bits"
        ));
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
        if let Some(min) = length.min
            && min > MAX_GENERATED_LENGTH
        {
            return Err(format!(
                "the minimum length {min} exceeds the cap on generated lengths, \
                 {MAX_GENERATED_LENGTH}"
            ));
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

/// Check that `value` is a value of `sort`, nested at most [`MAX_VALUE_DEPTH`] levels deep.
pub(crate) fn check_shape(value: &Value, sort: &ValueSort) -> Result<(), String> {
    check_shape_at(value, sort, 0)
}

/// The level below `level`, or a message when a value at `level` would be deeper than
/// [`MAX_VALUE_DEPTH`] (the check recurses once per level).
fn deeper(level: usize) -> Result<usize, String> {
    if level >= MAX_VALUE_DEPTH {
        Err(format!(
            "the value is nested deeper than {MAX_VALUE_DEPTH} levels, the most a checked value \
             may have"
        ))
    } else {
        Ok(level + 1)
    }
}

/// [`check_shape`] for a value at `level` levels below the value checked.
fn check_shape_at(value: &Value, sort: &ValueSort, level: usize) -> Result<(), String> {
    let below = deeper(level)?;
    match (value, sort.generated()) {
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
        (Value::List(items), ValueSort::List { element, .. }) => items
            .iter()
            .try_for_each(|item| check_shape_at(item, element, below)),
        (Value::Set(items), ValueSort::Set { element, .. }) => {
            if items.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err("a Set's elements are not sorted and distinct".to_owned());
            }
            items
                .iter()
                .try_for_each(|item| check_shape_at(item, element, below))
        }
        (Value::Map(entries), ValueSort::Map { key, value, .. }) => {
            if entries.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
                return Err("a Map's keys are not sorted and distinct".to_owned());
            }
            entries.iter().try_for_each(|(entry_key, entry_value)| {
                check_shape_at(entry_key, key, below)?;
                check_shape_at(entry_value, value, below)
            })
        }
        (_, ValueSort::Data { table, .. }) => {
            if table.sorts.is_empty() {
                // A table built by hand without entries admits only applications (a choice set
                // of a data hole resolved without a definition).
                if matches!(value, Value::Apply { .. }) {
                    Ok(())
                } else {
                    Err("the value is not of the hole's sort".to_owned())
                }
            } else {
                check_data_at(value, table, 0, level).map(|_| ())
            }
        }
        _ => Err("the value is not of the hole's sort".to_owned()),
    }
}

/// How a value of a data-sort entry is built: by a constructor of the entry, or as a value of
/// one of its non-data subsorts.
pub(crate) enum DataAlternative<'t> {
    /// An application of this constructor.
    Constructor(&'t DataConstructor),
    /// A value of this subsort, injected to the entry's sort.
    Subsort(&'t ArgumentSort),
}

/// Check that `value` is a value of entry `index` of `table`: an application of one of its
/// constructors to values of the argument sorts, or a value of one of its non-data subsorts.
/// Returns how the value is built.
pub(crate) fn check_data<'t>(
    value: &Value,
    table: &'t DataSorts,
    index: usize,
) -> Result<DataAlternative<'t>, String> {
    check_data_at(value, table, index, 0)
}

/// [`check_data`] for a value at `level` levels below the value checked.
fn check_data_at<'t>(
    value: &Value,
    table: &'t DataSorts,
    index: usize,
    level: usize,
) -> Result<DataAlternative<'t>, String> {
    let below = deeper(level)?;
    let entry = table
        .sorts
        .get(index)
        .ok_or_else(|| format!("the data-sort table has no entry {index}"))?;
    let Value::Apply { symbol, arguments } = value else {
        return entry
            .subsorts
            .iter()
            .find(|subsort| check_argument(value, subsort, table, level).is_ok())
            .map(DataAlternative::Subsort)
            .ok_or_else(|| format!("the value is not a value of {}", entry.kore_sort));
    };
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
        .try_for_each(|(sort, argument)| check_argument(argument, sort, table, below))?;
    Ok(DataAlternative::Constructor(constructor))
}

/// Check that `value`, at `level` levels below the value checked, is a value of the argument
/// sort `sort` of `table`.
fn check_argument(
    value: &Value,
    sort: &ArgumentSort,
    table: &DataSorts,
    level: usize,
) -> Result<(), String> {
    match sort {
        ArgumentSort::Value(sort) => check_shape_at(value, sort, level),
        ArgumentSort::Data(index) => check_data_at(value, table, *index, level).map(|_| ()),
        ArgumentSort::Empty(empty) => match (value, empty.kind) {
            (Value::List(items), CollectionKind::List)
            | (Value::Set(items), CollectionKind::Set)
                if items.is_empty() =>
            {
                Ok(())
            }
            (Value::Map(entries), CollectionKind::Map) if entries.is_empty() => Ok(()),
            _ => Err(format!(
                "only the empty collection is a value of {} here",
                empty.symbols.kore_sort
            )),
        },
    }
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
                    .filter(|pair| pair.bytes().all(|byte| byte.is_ascii_hexdigit()))
                    .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                    .ok_or_else(|| D::Error::custom("invalid hex digit"))
            })
            .collect()
    }
}
