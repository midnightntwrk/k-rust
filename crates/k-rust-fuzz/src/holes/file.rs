//! The flat `[[hole]]` form of a campaign file (ARCHITECTURE 2.2, 2.5), decoded into a
//! [`HoleDecl`] without any particular file format.
//!
//! `krust fuzz` reads it from its TOML campaign file and kink-flow from TOML it decodes by hand;
//! both go through [`HoleFile::into_decl`], so one hole means the same in either, with the same
//! refusals. [`HoleFile`] is a serde type: a front end deserializes it from whatever
//! self-describing data it holds. A `choices` entry is a [`HoleChoice`], an untagged value that
//! needs no format's value type; it becomes a [`Value`] at the hole's sort.
//!
//! The same hole written as JSON:
//!
//! ```
//! use k_rust_fuzz::holes::HoleFile;
//!
//! let hole: HoleFile = serde_json::from_str(
//!     r#"{ "name": "AMOUNT", "sort": "Int", "line": 4, "find": "amount = 250;",
//!          "literal": "250", "choices": [0, 250, { "int": "1000000000000000000000" }] }"#,
//! )
//! .unwrap();
//! // `program` defaults to the program's name; "$TX" would address the binding of `$TX`.
//! let decl = hole.into_decl(Some("transfer.imp")).unwrap();
//! assert_eq!(decl.constraints.choices.map(|choices| choices.len()), Some(3));
//! ```
//!
//! A client that decodes TOML by hand into `toml::Value` converts each `[[hole]]` table with
//! `toml::Value::try_into::<HoleFile>()`, which deserializes through serde as
//! `serde_json::from_value` does above; an unknown key is refused with serde's message
//! (``unknown field `x`, expected one of `name`, ...``), which the client may wrap in its own.
//! `krust-fuzz`'s campaign-file tests (`src/bin/krust-fuzz/campaign.rs`) show that route, and
//! that it decodes a hole file as `krust fuzz` does.

use num_bigint::{BigInt, BigUint};
use serde::{
    Deserialize, Deserializer,
    de::{self, IgnoredAny, MapAccess, Visitor, value::MapAccessDeserializer},
};

use super::{HoleDecl, HoleLocation, SpanAddress};
use crate::values::{Constraints, ElementSorts, IntRange, LengthRange, Value};

/// One `[[hole]]` (ARCHITECTURE 2.2, 2.5): a span of a program text, or a configuration
/// variable.
///
/// `C` is what a `choices` entry decodes to before it becomes a [`HoleChoice`]: the library's
/// own [`HoleChoice`] by default, or a front end's type that keeps its format's value until
/// [`HoleFile::into_decl`] names the hole in a refusal (as `krust-fuzz` keeps a TOML value).
#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct HoleFile<C = HoleChoice> {
    /// The hole's name.
    pub name: String,
    /// The hole's sort.
    pub sort: String,
    /// The addressed text: the program's name (the default) or `$NAME` for a binding's text.
    pub program: Option<String>,
    /// The one-based line of the span.
    pub line: Option<u32>,
    /// The one-based column, in characters, of the literal's first character on `line`, which
    /// places the literal without a unique `find`.
    pub column: Option<u32>,
    /// A text occurring once in the line or text and containing the literal; the literal
    /// itself by default.
    pub find: Option<String>,
    /// The hole's literal: its anchor value.
    pub literal: Option<String>,
    /// A configuration variable (without `$`) whose value is the hole, instead of a span.
    pub config_var: Option<String>,
    /// An inclusive integer range; each end an integer or a decimal string.
    pub range: Option<RangeFile>,
    /// An inclusive length range.
    pub length: Option<LengthRange>,
    /// Element sorts of a collection: `{ element = "Int" }` or `{ key = "Id", value = "Int" }`.
    pub elements: Option<ElementsFile>,
    /// The values the hole may take.
    pub choices: Option<Vec<C>>,
    /// Admit a sort the hole-sort rule refuses (ARCHITECTURE 2.4).
    pub allow_refused_sort: Option<bool>,
}

/// An integer range as written.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RangeFile {
    /// The least value.
    pub min: Option<IntText>,
    /// The greatest value.
    pub max: Option<IntText>,
}

/// An integer as written: an integer, or a decimal string for any size. Anything else is
/// refused with what a range bound may be (FZ-REPLAY-WHOLE N2), not with the name of this type.
#[derive(Debug)]
pub enum IntText {
    /// An integer.
    Integer(i64),
    /// A decimal string.
    Text(String),
}

impl<'de> Deserialize<'de> for IntText {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(IntTextVisitor)
    }
}

/// Decodes an [`IntText`] by the shape of the data.
struct IntTextVisitor;

impl Visitor<'_> for IntTextVisitor {
    type Value = IntText;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str(
            "a range bound: an integer, or a decimal string for a bound beyond 64 bits \
             (max = \"115792089237316195423570985008687907853269984665640564039457584007913129639935\")",
        )
    }

    fn visit_i64<E: de::Error>(self, value: i64) -> Result<IntText, E> {
        Ok(IntText::Integer(value))
    }

    fn visit_u64<E: de::Error>(self, value: u64) -> Result<IntText, E> {
        Ok(
            i64::try_from(value)
                .map_or_else(|_| IntText::Text(value.to_string()), IntText::Integer),
        )
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<IntText, E> {
        Ok(IntText::Text(value.to_owned()))
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<IntText, E> {
        Ok(IntText::Text(value))
    }
}

/// Element sorts as written.
#[derive(Debug, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum ElementsFile {
    /// A `List` or `Set` element sort.
    Elements {
        /// The element sort.
        element: String,
    },
    /// A `Map`'s key and value sorts.
    Entries {
        /// The key sort.
        key: String,
        /// The value sort.
        value: String,
    },
}

impl From<ElementsFile> for ElementSorts {
    fn from(elements: ElementsFile) -> Self {
        elements.into_sorts()
    }
}

impl ElementsFile {
    /// The constraint these element sorts declare.
    fn into_sorts(self) -> ElementSorts {
        match self {
            Self::Elements { element } => ElementSorts::Elements { element },
            Self::Entries { key, value } => ElementSorts::Entries { key, value },
        }
    }
}

/// A hole value as a campaign file writes it, untagged: an integer (an `Int`, or the unsigned
/// value of an `MInt{N}` hole), a boolean, a string, or a table in the library's value form
/// (`{ int = "123" }`, `{ list = [{ int = "1" }] }`, `{ token = { sort = "Id", text = "x" } }`).
///
/// An integer is 64-bit signed, as TOML's; a larger one is written in the table form. Anything
/// else (a float, an array, a table that is no value) is refused when it is deserialized.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HoleChoice {
    /// An integer.
    Integer(i64),
    /// A boolean.
    Boolean(bool),
    /// A string.
    String(String),
    /// A value in the library's form.
    Table(Value),
}

impl HoleChoice {
    /// The value this choice denotes at the hole's sort: an integer is an `MInt{N}` value at
    /// such a sort, and must then be non-negative, and an `Int` otherwise.
    ///
    /// # Errors
    ///
    /// A negative integer at an `MInt{N}` sort, with the message naming the sort.
    pub fn to_value(&self, sort: &str) -> Result<Value, String> {
        match self {
            Self::Integer(integer) => match machine_width(sort) {
                Some(width) => u64::try_from(*integer)
                    .map(|unsigned| Value::MInt {
                        width,
                        value: BigUint::from(unsigned),
                    })
                    .map_err(|_| format!("{integer} is negative; an {sort} value is unsigned")),
                None => Ok(Value::Int(BigInt::from(*integer))),
            },
            Self::Boolean(boolean) => Ok(Value::Bool(*boolean)),
            Self::String(text) => Ok(Value::String(text.clone())),
            Self::Table(value) => Ok(value.clone()),
        }
    }
}

/// A `choices` entry as a front end decoded it, made a [`HoleChoice`] when the hole is
/// declared, so that a refusal can name the hole.
pub trait IntoHoleChoice {
    /// The choice, or why the entry is no value (without the hole's name, which the caller
    /// adds).
    ///
    /// # Errors
    ///
    /// The entry is no value.
    fn into_hole_choice(self) -> Result<HoleChoice, String>;
}

impl IntoHoleChoice for HoleChoice {
    fn into_hole_choice(self) -> Result<HoleChoice, String> {
        Ok(self)
    }
}

impl<'de> Deserialize<'de> for HoleChoice {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(ChoiceVisitor)
    }
}

/// Decodes a [`HoleChoice`] by the shape of the data.
struct ChoiceVisitor;

impl<'de> Visitor<'de> for ChoiceVisitor {
    type Value = HoleChoice;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str(
            "a hole value: an integer, a boolean, a string, or a table in the value form; \
             write collections and other values as tables, such as { list = [{ int = \"1\" }] }",
        )
    }

    fn visit_bool<E: de::Error>(self, value: bool) -> Result<HoleChoice, E> {
        Ok(HoleChoice::Boolean(value))
    }

    fn visit_i64<E: de::Error>(self, value: i64) -> Result<HoleChoice, E> {
        Ok(HoleChoice::Integer(value))
    }

    fn visit_u64<E: de::Error>(self, value: u64) -> Result<HoleChoice, E> {
        i64::try_from(value).map(HoleChoice::Integer).map_err(|_| {
            E::custom(format!(
                "{value} is larger than a 64-bit signed integer; write it as {{ int = \"{value}\" }}"
            ))
        })
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<HoleChoice, E> {
        Ok(HoleChoice::String(value.to_owned()))
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<HoleChoice, E> {
        Ok(HoleChoice::String(value))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<HoleChoice, A::Error> {
        let value = Value::deserialize(MapAccessDeserializer::new(&mut map))?;
        // A value table has one key, the value's kind; the enum's decoder stops after it.
        if map.next_key::<IgnoredAny>()?.is_some() {
            return Err(de::Error::custom(
                "a value table has exactly one key, the value's kind (such as `int` or `list`)",
            ));
        }
        Ok(HoleChoice::Table(value))
    }
}

/// The width of an `MInt{N}` sort.
fn machine_width(sort: &str) -> Option<u32> {
    sort.strip_prefix("MInt{")?.strip_suffix('}')?.parse().ok()
}

impl<C: IntoHoleChoice> HoleFile<C> {
    /// The library declaration of this hole. `program` is the name a span hole addresses when
    /// it gives no `program` of its own (the campaign's program).
    ///
    /// # Errors
    ///
    /// The keys contradict one another (a `config-var` with span keys), a span hole lacks its
    /// `literal` or a program to address, a range end is no decimal integer, or a choice is no
    /// value at the hole's sort; each message names the hole.
    pub fn into_decl(self, program: Option<&str>) -> Result<HoleDecl, String> {
        let name = self.name;
        let span = self.literal.is_some()
            || self.find.is_some()
            || self.line.is_some()
            || self.column.is_some();
        let location = match (self.config_var, span) {
            (Some(variable), false) if self.program.is_none() => HoleLocation::ConfigVar {
                name: variable.strip_prefix('$').unwrap_or(&variable).to_owned(),
            },
            (Some(_), _) => {
                return Err(format!(
                    "hole `{name}`: `config-var` addresses a whole variable; it takes no \
                     `program`, `line`, `column`, `find` or `literal`"
                ));
            }
            (None, _) => {
                let literal = self.literal.ok_or_else(|| {
                    format!("hole `{name}`: give its `literal` (and `find`), or a `config-var`")
                })?;
                let program = self
                    .program
                    .or_else(|| program.map(str::to_owned))
                    .ok_or_else(|| {
                        format!("hole `{name}`: no program to address; give the hole a `program`")
                    })?;
                HoleLocation::Span(SpanAddress {
                    program,
                    line: self.line,
                    column: self.column,
                    find: self.find.unwrap_or_else(|| literal.clone()),
                    literal,
                })
            }
        };
        let range = self
            .range
            .map(|range| -> Result<IntRange, String> {
                Ok(IntRange {
                    min: range.min.map(|end| int_text(&end)).transpose()?,
                    max: range.max.map(|end| int_text(&end)).transpose()?,
                })
            })
            .transpose()
            .map_err(|message| format!("hole `{name}`: {message}"))?;
        let sort = self.sort;
        let choices = self
            .choices
            .map(|choices| {
                choices
                    .into_iter()
                    .map(|choice| choice.into_hole_choice()?.to_value(&sort))
                    .collect::<Result<Vec<_>, String>>()
            })
            .transpose()
            .map_err(|message| format!("hole `{name}`: {message}"))?;
        Ok(HoleDecl {
            name,
            sort,
            location,
            constraints: Constraints {
                range,
                length: self.length,
                elements: self.elements.map(ElementSorts::from),
                choices,
            },
            allow_refused_sort: self.allow_refused_sort.unwrap_or(false),
        })
    }
}

fn int_text(text: &IntText) -> Result<BigInt, String> {
    match text {
        IntText::Integer(value) => Ok(BigInt::from(*value)),
        IntText::Text(text) => text
            .parse()
            .map_err(|error| format!("`{text}` is not a decimal integer: {error}")),
    }
}

#[cfg(test)]
#[path = "file_tests.rs"]
mod tests;
