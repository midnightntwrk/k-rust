//! Inputs by name: the `#[k::init]` parameters of a definition, and the one encoding of a value
//! of a parameter as a document of the JSON data model, read at the parameter's declared type.
//!
//! A case is an assignment of one value to each declared input, by the `#[k::init]` parameter's
//! name. No input is special: the main parameter ([`Parameter::main`]) is the one a program file
//! binds when a front end is given one, and it can be bound by name as every other parameter is.
//! A value is written as K text parsed at the parameter's sort (`$text`, `$text-file`), or as
//! typed data that this module decodes into a [`Value`] at the parameter's declared type, element
//! types included. The encoding is the same for every front end: `krs run`'s inputs, a case file,
//! and a corpus tool that binds cases through `krs-exec`.
//!
//! # The encoding
//!
//! This section is the normative statement of the encoding.
//!
//! A *document* is a value of the JSON data model: null, a boolean, a number, a string, an array,
//! or an object. A TOML document is first converted to it ([`toml_document`]): integers and
//! booleans, strings, arrays and tables as themselves, a finite float as a number, a NaN or an
//! infinity as `{"$float": "NaN"}`, `{"$float": "Infinity"}` or `{"$float": "-Infinity"}`, and a
//! datetime is refused, since it has no reading as a term. A JSON text is read with duplicate
//! object keys refused ([`json_document`]); a TOML parser refuses them itself.
//!
//! A document is decoded at a *position*. A position is a declared type: a sort and, for a
//! collection, its element types (`Map<Int, Int>`, the type of the parameter or of an element
//! inside it). A position is *untyped* where the declared type says nothing: a `K` sort, the
//! elements of a collection whose element types are not declared (the field of a constructor
//! declared `List`, the elements of `$list`), and the field of a sort no KRS declaration names.
//!
//! Every document has at most one reading at a position. Shorthands are read only where the
//! position's type decides them; elsewhere a *tagged form* states the reading. Where a shorthand
//! has two readings at a position, the document is refused and the message names the tagged
//! form of each reading. The decoder refuses rather than guesses.
//!
//! ## Tagged forms
//!
//! A tagged form is an object with exactly one key, which starts with `$`; no Rust identifier
//! does, so a tag never collides with a constructor or field name. An object with a `$` key and
//! other keys is refused. A tagged form means the same at every position, and one whose term is
//! of a sort that is not at most the position's sort is refused.
//!
//! A map key is not a Rust identifier, and one that starts with `$` (a `String` or token key)
//! would make the object shorthand of a `Map` a tagged form: such a map is written in the pairs
//! form, `[["$x", 1]]`, and the refusal of the object says so.
//!
//! | form | value | where |
//! |---|---|---|
//! | `{"$text": "K text"}` | the text, parsed at the parameter's sort as `-c` parses it | a whole input only |
//! | `{"$text-file": "path"}` | the file's UTF-8 text, as `$text`; parse locations carry the file's name | a whole input only |
//! | `{"$file": "path"}` | a `Bytes` of the file's bytes, unchanged | anywhere `Bytes` fits |
//! | `{"$hex": "00ff1a"}` | a `Bytes` of the bytes the hex digits spell (an even count, either case, no separators) | anywhere `Bytes` fits |
//! | `{"$data-file": "path"}` | the document the file holds (`.json` or `.toml`, by extension), decoded at this position | anywhere |
//! | `{"$string": "text"}` | a `String` | anywhere |
//! | `{"$int": "-0x1f"}`, `{"$int": 31}` | an `Int`: a string by the integer grammar of the `Int` row below, or an integer | anywhere |
//! | `{"$float": 1.5}`, `{"$float": "1.5f"}` | a `Float`: a number read as at `Float` (below), or the value a K `Float` literal names | anywhere |
//! | `{"$token": "text"}` | a token of the position's sort, which is a token sort | a token sort |
//! | `{"$token": {"sort": "Id", "text": "x"}}` | a token of the named token sort | anywhere |
//! | `{"$list": [..]}`, `{"$set": [..]}`, `{"$seq": [..]}` | a `List`, a `Set`, a K sequence, of untyped elements | anywhere |
//! | `{"$map": [[key, value], ..]}` | a `Map` of untyped keys and values | anywhere |
//! | `{"$call": {"path::f": fields}}` | the application of the function `f` to its arguments | anywhere |
//!
//! A token's text, as `$token` or as a shorthand, is not checked against its sort's lexical
//! syntax: it denotes the domain value of that sort with that text, a term of the sort, even
//! where no K text of the definition spells it (`"top"` at a sort whose tokens match
//! `@[a-z]+`), while `$text` of the same text fails to parse.
//!
//! A path in `$file`, `$text-file` or `$data-file` is relative to the document that holds it
//! (the case file, or the data file that includes it), and the decoder reads no file itself: the
//! caller's [`InputFiles`] resolves and reads it. A `$data-file` that includes itself, directly
//! or through others, is refused naming the cycle.
//!
//! ## Constructors and functions
//!
//! A constructor is written `{"Name": fields}`, with `fields` an object by field name or an array
//! in declaration order (a tuple variant's fields are named `0`, `1`, ..), and `[]` or `{}` for
//! none; at a position of a declared sort a bare string `"Name"` is a nullary constructor.
//! `Name` is the declaration's path or a `::`-aligned suffix of it (`Register::A`, `A`), resolved
//! among the constructors whose result sort is at most the position's sort (among all
//! constructors at an untyped position); a name that selects several is refused naming them.
//! Each field is decoded at its declared sort, with no element types: a field declared `List` has
//! untyped elements.
//!
//! A function is applied with `$call`, its arguments written as a constructor's fields and
//! resolved among the function productions whose result sort is at most the position's sort. A
//! function written in the constructor form, and a constructor under `$call`, are refused: a
//! reader of a case sees which parts are data and which are computed. Any function may be applied,
//! partial and `internal` ones included, as the initializer's body may apply them; the
//! configuration holds the application, which the definition's equations evaluate when the first
//! state is simplified, before the first step.
//!
//! ## Shorthands
//!
//! | position | shorthands |
//! |---|---|
//! | `Int` | an integer; a string of an optional `-` and decimal digits, or of `0x`, `0o` or `0b` and digits of that base (for values beyond 64 bits, and for hex); a number with a fraction or an exponent is refused, since JSON delivers an integer beyond 64 bits as one and it would be rounded |
//! | `Bool` | `true`, `false` |
//! | `String` | a string |
//! | `Float` | a number, or a string that is a K `Float` literal; an integer is its binary64 value when binary64 holds it exactly and is refused otherwise; a number with a fraction or an exponent is its binary64 value, but one with an integral value of 2^64 or more, or of -2^63 or less, is refused, since a JSON reader delivers an integer it cannot hold as such a number, already rounded (write it as a K `Float` literal) |
//! | `Bytes` | an array of integers in `0..=255`; a bare string is refused, since its byte encoding is not determined |
//! | a token sort (`Id`, a `#[k::token]` sort) | a string, the token's text |
//! | `List<E>`, `Set<E>` | an array of documents at `E`; a `Set` with two elements that decode equal is refused |
//! | `Map<K, V>` | an object, each key read at `K` from its string (an `Int` by the integer grammar, a `String` verbatim, a `Bool` from `"true"` or `"false"`, a token's text, a nullary constructor's name) and each value at `V`; or an array of `[key, value]` pairs; two keys that decode equal are refused |
//! | a declared sort | a constructor form; a bare string: a nullary constructor, a token of a token sort at most it, or a `String` where `String` is at most it; a boolean where `Bool` is; a number where `Int` or `Float` is (below); an array or an object where a collection sort is, as at that sort with untyped elements |
//! | untyped | an integer (an `Int`), a boolean (a `Bool`), a number with a nonzero fraction (a `Float`), a constructor form, a tagged form; a bare string, an array, a number with an integral value written as a float, and any other object are refused as undetermined |
//!
//! At a declared sort that is no builtin, the document's JSON type decides the builtin, as at an
//! untyped position: a string is never an `Int` or a `Float` there, so `"12"` at `Val`, with
//! `Int` and `String` subsorts of `Val`, is the `String` `"12"` (an `Int` beyond 64 bits is
//! written `{"$int": ..}`). A number is an `Int` where `Int` is at most the sort and a `Float`,
//! read as at `Float`, where `Float` is and `Int` is not. Where both are, an integer is an `Int`,
//! a number with a nonzero fraction a `Float`, and a number with an integral value written as a
//! float (`2.0`) is refused as undetermined, since JSON delivers an integer beyond 64 bits so:
//! the `Float` is written `{"$float": 2.0}`. A map key, which is always a string, is read at its
//! sort by every reading of the strings the `Map` row lists, so `"12"` as a key at `Val` reads
//! as an `Int` and as a `String` and is refused; such a map is written in the pairs form.
//!
//! Two map keys or set elements that decode equal are refused because K's concatenation of two
//! maps that bind one key, or of two sets that share an element, has no value: keeping either
//! binding would accept a document that denotes no term, and would let `{"1": 2, "01": 3}` mean
//! a map that the text `1 |-> 2 1 |-> 3` does not.
//!
//! A decoded value is still checked where a parsed one is: the configuration assembler requires
//! its sort to be at most the variable's declared sort, and every part of a collection to fit the
//! declared element types. The decoder's own checks make the refusal earlier and name the
//! position inside the document.
//!
//! Not in the encoding: `$text` inside a value, sort-parametric productions (refused as
//! [`ValueIndex::ctor`] refuses them), and console input.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use k_rust::kast::Sort as KastSort;
use krs_ir::{BuiltinSort, CellSortArgument};
use krs_ir_levels::{DefinitionIr, DefinitionSentence, DefinitionSortRef};
use num_bigint::BigInt;
use serde_json::Value as Json;

use crate::values::{Decl, Float, SortRef, Value, ValueError, ValueIndex};
use crate::{ConfigValue, ProgramInput};

/// One `#[k::init]` parameter: an input of the definition, from the Definition IR.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Parameter {
    /// The Rust binding, the IR variable's id (`regs`).
    pub name: String,
    /// The K name of its configuration variable, without `$` (`REGS`).
    pub variable: String,
    /// The declared type, element types included.
    pub ty: InputType,
    /// Whether this is the main parameter, which a program file binds: the one marked
    /// `#[k::config_var(.., main)]`, or the one the computation cell reads when none is marked.
    pub main: bool,
}

impl Parameter {
    /// Whether a program file binds this parameter as the file's bytes: its declared type is
    /// exactly `Bytes`, the one type whose values are any bytes. Every other type, a sort `Bytes`
    /// is a subsort of included, reads a file as text, parsed at its sort, since only a parse
    /// says which of its values a file denotes.
    #[must_use]
    pub fn reads_file_bytes(&self) -> bool {
        self.ty.sort == SortRef::Builtin(BuiltinSort::Bytes) && self.ty.arguments.is_empty()
    }

    /// Why a program file that is not UTF-8 text binds this main parameter to nothing, where it
    /// does not read a file's bytes: the end of [`crate::ExecError::ProgramNotText`]'s message,
    /// for a caller that names the file itself.
    #[must_use]
    pub fn reads_file_text(&self) -> String {
        format!(
            "the main parameter `{}` (${}: {}) reads a file as text, parsed at its sort; only a main parameter of type exactly `Bytes` takes a file's bytes",
            self.name, self.variable, self.ty
        )
    }
}

/// The main input of a definition as its Definition IR declares it, read without compiling the
/// definition: what a front end needs to bind a program file that is text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MainVariable {
    /// The Rust binding (`entry`).
    pub name: String,
    /// The K name of its configuration variable, without `$` (`PGM`, `ENTRY`).
    pub variable: String,
    /// Whether a program file binds it as the file's bytes ([`Parameter::reads_file_bytes`]),
    /// where the Definition IR alone says so; `None` where only the compiled definition does.
    pub reads_file_bytes: Option<bool>,
}

/// The configuration variables of `definition`'s `#[k::init]`, in declaration order.
fn configuration_variables(
    definition: &DefinitionIr,
) -> impl Iterator<Item = &krs_ir::FixedConfigurationVariable<DefinitionSortRef>> {
    definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Configuration(configuration) => Some(configuration),
            _ => None,
        })
        .flat_map(|configuration| configuration.variables())
}

/// Whether a program file binds a parameter of the IR sort `sort` applied to `arguments` as the
/// file's bytes, as [`Parameter::reads_file_bytes`] says of the parameter [`parameters`] types
/// from it; `None` where that type is not a function of the IR sort.
///
/// [`parameters`] maps a builtin sort to itself with its arguments, and a declared sort to a
/// declared KRS sort or, for one no KRS declaration names, to the compiled definition's K sort of
/// the variable, which is that declared sort's own: K's `Bytes` is the builtin's sort, and a
/// definition declares each sort name once. Only where the sort, or one of its arguments, is a
/// cell sort or a sort parameter is the compiled K sort another than the IR names, and it can be
/// K's `Bytes`. So the type is exactly `Bytes` exactly when the IR sort is the builtin `Bytes`
/// with no arguments, except under a cell sort or a sort parameter, where only the compiled
/// definition answers.
fn file_reading(
    sort: &DefinitionSortRef,
    arguments: &[CellSortArgument<DefinitionSortRef>],
) -> Option<bool> {
    fn ir_typed(
        sort: &DefinitionSortRef,
        arguments: &[CellSortArgument<DefinitionSortRef>],
    ) -> bool {
        matches!(
            sort,
            DefinitionSortRef::Builtin(_) | DefinitionSortRef::Declared(_)
        ) && arguments
            .iter()
            .all(|argument| ir_typed(&argument.sort, &argument.arguments))
    }
    ir_typed(sort, arguments)
        .then(|| *sort == DefinitionSortRef::Builtin(BuiltinSort::Bytes) && arguments.is_empty())
}

/// The main parameter of `definition`'s `#[k::init]` ([`Parameter::main`]), from the Definition
/// IR alone; `None` when it has none.
#[must_use]
pub fn main_variable(definition: &DefinitionIr) -> Option<MainVariable> {
    configuration_variables(definition)
        .find(|variable| variable.is_main())
        .map(|variable| MainVariable {
            name: variable.id().as_str().to_owned(),
            variable: variable.external_name().to_owned(),
            reads_file_bytes: file_reading(variable.sort(), variable.arguments()),
        })
}

/// Whether `definition`'s `#[k::init]` has a parameter whose configuration variable's K name is
/// `variable` (without `$`), main or not, from the Definition IR alone.
#[must_use]
pub fn declares_variable(definition: &DefinitionIr, variable: &str) -> bool {
    configuration_variables(definition).any(|declared| declared.external_name() == variable)
}

impl fmt::Display for Parameter {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.name, self.ty)
    }
}

/// A declared type: a sort and, for a collection, its element types (`Map<Reg8, Int>`).
///
/// The sort `K` ([`BuiltinSort::KSequence`]) is the untyped position: it takes any term, and
/// the encoding reads no shorthand there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InputType {
    /// The sort.
    pub sort: SortRef,
    /// The element types of a collection, in order; empty for every other sort and for a
    /// collection declared without them.
    pub arguments: Vec<InputType>,
}

impl InputType {
    /// The untyped position.
    #[must_use]
    pub const fn untyped() -> Self {
        Self::of(SortRef::Builtin(BuiltinSort::KSequence))
    }

    /// The sort with no element types.
    #[must_use]
    pub const fn of(sort: SortRef) -> Self {
        Self {
            sort,
            arguments: Vec::new(),
        }
    }

    /// Whether the type says nothing about a document at it (`K`).
    #[must_use]
    pub fn is_untyped(&self) -> bool {
        self.sort == SortRef::Builtin(BuiltinSort::KSequence)
    }

    /// The type of element `index` of a collection of this type: its declared element type,
    /// or the untyped position when the collection declares none.
    fn element(&self, index: usize) -> Self {
        self.arguments
            .get(index)
            .cloned()
            .unwrap_or_else(Self::untyped)
    }
}

impl fmt::Display for InputType {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&ValueIndex::sort_name(&self.sort))?;
        if !self.arguments.is_empty() {
            formatter.write_str("<")?;
            for (index, argument) in self.arguments.iter().enumerate() {
                if index > 0 {
                    formatter.write_str(", ")?;
                }
                argument.fmt(formatter)?;
            }
            formatter.write_str(">")?;
        }
        Ok(())
    }
}

/// Where the decoder reads the files a document names (`$file`, `$text-file`, `$data-file`).
///
/// The decoder touches no filesystem: a front end resolves a path as its documents are placed
/// (a case file's directory, a manifest's directory under its containment rule).
pub trait InputFiles {
    /// The resolved name and the bytes of `path`, written in the document `from` (the resolved
    /// name an earlier read returned, for a path inside a data file), or in the top document
    /// (`None`).
    ///
    /// The resolved name identifies the file: parse locations carry it, and the cycle check of
    /// `$data-file` compares it.
    ///
    /// # Errors
    ///
    /// Returns why the file cannot be read, which the decoder reports at the path's position.
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String>;
}

/// The [`InputFiles`] of a document that names no file: every read is refused.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoFiles;

impl InputFiles for NoFiles {
    fn read(&mut self, _from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        Err(format!("`{path}`: this input reads no files"))
    }
}

/// A case document: `{"inputs": {name: value, ..}}`, TOML's `[inputs]` table, a value for each
/// input by name.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Case {
    /// Each input's name, a parameter's Rust name or its K name with or without `$`, and its
    /// document, by name.
    pub inputs: Vec<(String, Json)>,
}

impl Case {
    /// The case a TOML document states.
    ///
    /// # Errors
    ///
    /// Returns [`InputError`] for a text that is no TOML, a top-level key other than `inputs`,
    /// an `inputs` that is no table, and a value [`toml_document`] refuses.
    pub fn from_toml(text: &str) -> Result<Self, InputError> {
        let table = text.parse::<toml::Table>().map_err(|error| {
            InputError::document(format!("the case is no TOML document: {error}"))
        })?;
        Self::from_document(toml_document(&toml::Value::Table(table))?)
    }

    /// The case a JSON document states.
    ///
    /// # Errors
    ///
    /// Returns [`InputError`] for a text [`json_document`] refuses, a document that is no object,
    /// a top-level key other than `inputs`, and an `inputs` that is no object.
    pub fn from_json(text: &str) -> Result<Self, InputError> {
        Self::from_document(json_document(text)?)
    }

    fn from_document(document: Json) -> Result<Self, InputError> {
        let Json::Object(top) = document else {
            return Err(InputError::document(
                "a case is an object with the key `inputs`".to_owned(),
            ));
        };
        let mut inputs = None;
        for (key, value) in top {
            if key != "inputs" {
                return Err(InputError::document(format!(
                    "unknown key `{key}` in a case; a case has the key `inputs`"
                )));
            }
            inputs = Some(value);
        }
        let inputs = match inputs {
            Some(Json::Object(inputs)) => inputs.into_iter().collect(),
            Some(_) => {
                return Err(InputError::document(
                    "`inputs` is a table of the case's values by input name".to_owned(),
                ));
            }
            None => Vec::new(),
        };
        Ok(Self { inputs })
    }
}

/// Why a document is no value of its input: the input and its declared type, the position
/// inside the document (`["A"]`, `[3]`, `.Run.steps`, `$call(boot::map_rom).rom`), and the
/// reason.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InputError {
    /// The input's parameter, when the document is one input's.
    pub parameter: Option<String>,
    /// The parameter's declared type (`Map<Reg8, Int>`).
    pub declared: Option<String>,
    /// Where in the document; empty for the whole document.
    pub position: String,
    /// Why.
    pub message: String,
}

impl InputError {
    const fn document(message: String) -> Self {
        Self {
            parameter: None,
            declared: None,
            position: String::new(),
            message,
        }
    }
}

impl fmt::Display for InputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut prefixed = false;
        if let Some(parameter) = &self.parameter {
            write!(formatter, "input `{parameter}`")?;
            if let Some(declared) = &self.declared {
                write!(formatter, " ({declared})")?;
            }
            prefixed = true;
        }
        if !self.position.is_empty() {
            if prefixed {
                formatter.write_str(" ")?;
            }
            write!(formatter, "at `{}`", self.position)?;
            prefixed = true;
        }
        if prefixed {
            formatter.write_str(": ")?;
        }
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for InputError {}

/// A TOML value in the JSON data model, as the encoding reads TOML.
///
/// A finite float is a number; a NaN or an infinity is the tagged `$float` of its K literal, so
/// that numbers stay finite; a datetime is refused. The conversion matches the TOML value
/// itself rather than going through serde, which renders a datetime as a map with a private key.
///
/// # Errors
///
/// Returns [`InputError`] for a datetime, naming where it is.
pub fn toml_document(value: &toml::Value) -> Result<Json, InputError> {
    fn convert(value: &toml::Value, position: &mut Vec<String>) -> Result<Json, InputError> {
        Ok(match value {
            toml::Value::String(text) => Json::String(text.clone()),
            toml::Value::Integer(integer) => Json::from(*integer),
            toml::Value::Boolean(boolean) => Json::Bool(*boolean),
            toml::Value::Float(float) => {
                if let Some(number) = serde_json::Number::from_f64(*float) {
                    Json::Number(number)
                } else {
                    let literal = if float.is_nan() {
                        "NaN"
                    } else if float.is_sign_negative() {
                        "-Infinity"
                    } else {
                        "Infinity"
                    };
                    serde_json::json!({ "$float": literal })
                }
            }
            toml::Value::Datetime(_) => {
                return Err(InputError {
                    parameter: None,
                    declared: None,
                    position: position.concat(),
                    message: "a TOML datetime has no reading as a term".to_owned(),
                });
            }
            toml::Value::Array(items) => {
                let mut converted = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    position.push(format!("[{index}]"));
                    converted.push(convert(item, position)?);
                    position.pop();
                }
                Json::Array(converted)
            }
            toml::Value::Table(table) => {
                let mut converted = serde_json::Map::new();
                for (key, item) in table {
                    position.push(format!("[{}]", Json::String(key.clone())));
                    converted.insert(key.clone(), convert(item, position)?);
                    position.pop();
                }
                Json::Object(converted)
            }
        })
    }
    convert(value, &mut Vec::new())
}

/// A JSON text as a document, with a key repeated in one object refused: a repeated key would
/// otherwise keep only its last value, so the document would mean something its text does not
/// say. The nesting limit of `serde_json` applies.
///
/// # Errors
///
/// Returns [`InputError`] for a text that is no JSON, or an object with a repeated key.
pub fn json_document(text: &str) -> Result<Json, InputError> {
    use serde::de::DeserializeSeed as _;
    let mut deserializer = serde_json::Deserializer::from_str(text);
    let document = UniqueKeys
        .deserialize(&mut deserializer)
        .and_then(|document| deserializer.end().map(|()| document))
        .map_err(|error| InputError::document(format!("the document is no JSON: {error}")))?;
    Ok(document)
}

/// A JSON value with every object's keys distinct ([`json_document`]).
struct UniqueKeys;

impl<'de> serde::de::DeserializeSeed<'de> for UniqueKeys {
    type Value = Json;

    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Json, D::Error> {
        deserializer.deserialize_any(self)
    }
}

impl<'de> serde::de::Visitor<'de> for UniqueKeys {
    type Value = Json;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Json, E> {
        Ok(Json::Bool(value))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Json, E> {
        Ok(Json::from(value))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Json, E> {
        Ok(Json::from(value))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Json, E> {
        Ok(serde_json::Number::from_f64(value).map_or(Json::Null, Json::Number))
    }

    fn visit_str<E>(self, value: &str) -> Result<Json, E> {
        Ok(Json::String(value.to_owned()))
    }

    fn visit_string<E>(self, value: String) -> Result<Json, E> {
        Ok(Json::String(value))
    }

    fn visit_unit<E>(self) -> Result<Json, E> {
        Ok(Json::Null)
    }

    fn visit_none<E>(self) -> Result<Json, E> {
        Ok(Json::Null)
    }

    fn visit_seq<A: serde::de::SeqAccess<'de>>(self, mut sequence: A) -> Result<Json, A::Error> {
        let mut items = Vec::new();
        while let Some(item) = sequence.next_element_seed(UniqueKeys)? {
            items.push(item);
        }
        Ok(Json::Array(items))
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, mut map: A) -> Result<Json, A::Error> {
        let mut object = serde_json::Map::new();
        while let Some(key) = map.next_key::<String>()? {
            let value = map.next_value_seed(UniqueKeys)?;
            if object.contains_key(&key) {
                return Err(serde::de::Error::custom(format!(
                    "the key `{key}` is repeated in one object"
                )));
            }
            object.insert(key, value);
        }
        Ok(Json::Object(object))
    }
}

/// The parameters of `definition`'s `#[k::init]`, in declaration order, with their types named
/// by `values`; `declared` is the compiled definition's configuration variables, whose K sort
/// types a parameter whose IR sort no KRS declaration names.
pub(crate) fn parameters(
    definition: &DefinitionIr,
    values: &ValueIndex,
    declared: &BTreeMap<String, KastSort>,
) -> Vec<Parameter> {
    fn input_type(
        values: &ValueIndex,
        sort: &DefinitionSortRef,
        arguments: &[CellSortArgument<DefinitionSortRef>],
    ) -> Option<InputType> {
        Some(InputType {
            sort: values.sort_ref(sort)?,
            arguments: arguments
                .iter()
                .map(|argument| input_type(values, &argument.sort, &argument.arguments))
                .collect::<Option<_>>()?,
        })
    }
    let mut parameters = Vec::new();
    for sentence in definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
    {
        let DefinitionSentence::Configuration(configuration) = sentence else {
            continue;
        };
        for variable in configuration.variables() {
            let name = variable.external_name();
            // A sort no KRS declaration names (a cell sort) is read as the compiled definition
            // declares it, or untyped, where the assembler still checks the term's sort.
            let ty = input_type(values, variable.sort(), variable.arguments())
                .or_else(|| {
                    declared
                        .get(name)
                        .and_then(|sort| {
                            values.sort_of_kore(&crate::values::kore_sort_name(&sort.name))
                        })
                        .map(InputType::of)
                })
                .unwrap_or_else(InputType::untyped);
            parameters.push(Parameter {
                name: variable.id().as_str().to_owned(),
                variable: name.to_owned(),
                ty,
                main: variable.is_main(),
            });
        }
    }
    parameters
}

/// Why a document is no value at a position: where, and why; [`decode`]'s caller adds the input.
#[derive(Debug)]
pub(crate) struct Refusal {
    pub(crate) position: String,
    pub(crate) message: String,
}

/// What a whole input's document gives: K text to parse, or a value.
pub(crate) enum Decoded {
    /// `$text`.
    Text(String),
    /// `$text-file`, with the file's resolved name.
    TextFile(ProgramInput),
    /// Any other document.
    Value(Value),
}

impl From<Decoded> for ConfigValue {
    fn from(decoded: Decoded) -> Self {
        match decoded {
            Decoded::Text(text) => Self::Text(text),
            Decoded::TextFile(file) => Self::TextFile(file),
            Decoded::Value(value) => Self::Value(value),
        }
    }
}

/// Decode `document`, the whole value of an input declared `ty`.
pub(crate) fn decode(
    values: &ValueIndex,
    files: &mut dyn InputFiles,
    document: &Json,
    ty: &InputType,
) -> Result<Decoded, Refusal> {
    let mut decoder = Decoder {
        values,
        files,
        includes: Vec::new(),
        path: Vec::new(),
    };
    match tagged(document) {
        Ok(Some(("$text", body))) => {
            let Json::String(text) = body else {
                return Err(decoder.refuse("`$text` takes a string of K text"));
            };
            Ok(Decoded::Text(text.clone()))
        }
        Ok(Some(("$text-file", body))) => {
            let (name, bytes) = decoder.read_file("$text-file", body)?;
            let text = String::from_utf8(bytes)
                .map_err(|_| decoder.refuse(&format!("`$text-file` `{name}` is no UTF-8 text")))?;
            Ok(Decoded::TextFile(ProgramInput { name, text }))
        }
        Ok(_) => decoder.decode(document, ty).map(Decoded::Value),
        Err(message) => Err(decoder.refuse(&format!("{message}{}", decoder.dollar_key_hint(ty)))),
    }
}

/// The tag and body of a tagged form; `None` for any other document. An object with a `$` key
/// among others is no tagged form and no other form either.
fn tagged(document: &Json) -> Result<Option<(&str, &Json)>, String> {
    let Json::Object(object) = document else {
        return Ok(None);
    };
    if !object.keys().any(|key| key.starts_with('$')) {
        return Ok(None);
    }
    let mut entries = object.iter();
    match (entries.next(), entries.next()) {
        (Some((tag, body)), None) => Ok(Some((tag.as_str(), body))),
        _ => Err(format!(
            "a tagged form is an object with exactly one key; this one has {}",
            object
                .keys()
                .map(|key| format!("`{key}`"))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// A JSON number, as the encoding reads it.
enum Number {
    /// An integer JSON delivered exactly.
    Integer(BigInt),
    /// Any other number: one with a fraction or an exponent, or an integer beyond 64 bits.
    Float(f64),
}

fn number(number: &serde_json::Number) -> Number {
    if let Some(integer) = number.as_i64() {
        Number::Integer(integer.into())
    } else if let Some(integer) = number.as_u64() {
        Number::Integer(integer.into())
    } else {
        Number::Float(number.as_f64().unwrap_or(f64::NAN))
    }
}

/// The `Int` an integer string spells: an optional `-`, then decimal digits, or `0x`, `0o` or
/// `0b` and digits of that base.
pub(crate) fn parse_int(text: &str) -> Result<BigInt, String> {
    let refuse = || {
        format!(
            "`{text}` is no integer: write an optional `-` and decimal digits, or `0x`, `0o` or `0b` and digits of that base"
        )
    };
    let (negative, unsigned) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let (radix, digits) = if let Some(digits) = unsigned.strip_prefix("0x") {
        (16, digits)
    } else if let Some(digits) = unsigned.strip_prefix("0o") {
        (8, digits)
    } else if let Some(digits) = unsigned.strip_prefix("0b") {
        (2, digits)
    } else {
        (10, unsigned)
    };
    if digits.is_empty() || !digits.chars().all(|digit| digit.is_digit(radix)) {
        return Err(refuse());
    }
    let magnitude = BigInt::parse_bytes(digits.as_bytes(), radix).ok_or_else(refuse)?;
    Ok(if negative { -magnitude } else { magnitude })
}

/// The bytes hex digits spell: an even count, either case, no separators.
pub(crate) fn parse_hex(text: &str) -> Result<Vec<u8>, String> {
    if !text.len().is_multiple_of(2) || !text.chars().all(|digit| digit.is_ascii_hexdigit()) {
        return Err(format!(
            "`{text}` is no hex byte string: write an even count of hex digits, without separators"
        ));
    }
    Ok(text
        .as_bytes()
        .chunks(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair).expect("hex digits are ASCII");
            u8::from_str_radix(digits, 16).expect("two hex digits are a byte")
        })
        .collect())
}

/// The binary64 `Float` of an integer, when binary64 holds it exactly: when the bits from its
/// highest to its lowest set bit fit binary64's 53-bit significand and its highest bit is below
/// 2^1024.
fn float_of_integer(integer: &BigInt) -> Result<Float, String> {
    let magnitude = integer.magnitude();
    let bits = magnitude.bits();
    let trailing = magnitude.trailing_zeros().unwrap_or(0);
    if bits - trailing > 53 || bits > 1024 {
        return Err(format!(
            "{integer} is no binary64 value exactly; write the Float as a K literal string ({{\"$float\": \"{integer}.0\"}} rounds it)"
        ));
    }
    let significand = (magnitude >> trailing)
        .iter_u64_digits()
        .next()
        .unwrap_or(0);
    let exponent = i32::try_from(trailing).expect("a trailing zero count below 1024");
    #[expect(
        clippy::cast_precision_loss,
        reason = "the significand has at most 53 bits, which binary64 holds exactly"
    )]
    let float = significand as f64 * 2_f64.powi(exponent);
    Ok(Float::from_f64(
        if integer.sign() == num_bigint::Sign::Minus {
            -float
        } else {
            float
        },
    ))
}

/// The `Float` a JSON number denotes at a `Float` position: an integer JSON delivered exactly,
/// when binary64 holds it exactly; any other number its binary64 value, unless it is a float
/// that an integer outside the 64-bit integers rounds to (2^64 or more, -2^63 or less), which is
/// how a JSON reader delivers such an integer.
fn float_of_number(value: &serde_json::Number) -> Result<Float, String> {
    /// 2^64, the least positive integer a JSON reader delivers as a float.
    const ABOVE_U64: f64 = 18_446_744_073_709_551_616.0;
    /// -2^63, the least integer a JSON reader delivers exactly, and the float an integer just
    /// below it rounds to.
    const I64_MIN: f64 = -9_223_372_036_854_775_808.0;
    match number(value) {
        Number::Integer(integer) => float_of_integer(&integer),
        Number::Float(float) if float <= I64_MIN || float >= ABOVE_U64 => Err(format!(
            "{value} is a float that an integer beyond the 64-bit integers rounds to, which is how a JSON reader delivers such an integer; write the Float as a K literal string ({{\"$float\": \"..\"}})"
        )),
        Number::Float(float) => Ok(Float::from_f64(float)),
    }
}

/// One reading a shorthand has at a position.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Reading {
    Int,
    IntText,
    Bool,
    BoolText,
    Float,
    FloatText,
    String,
    Token(SortRef),
    Ctor(Decl),
    List,
    Set,
    Map,
    Bytes,
}

impl Reading {
    /// The tagged or qualified spelling that states this reading, for an ambiguity's message.
    fn spelling(&self) -> String {
        match self {
            Self::Int | Self::IntText => "an `Int` ({\"$int\": ..})".to_owned(),
            Self::Bool | Self::BoolText => "a `Bool` (`true` or `false`)".to_owned(),
            Self::Float | Self::FloatText => "a `Float` ({\"$float\": ..})".to_owned(),
            Self::String => "a `String` ({\"$string\": ..})".to_owned(),
            Self::Token(sort) => {
                let sort = ValueIndex::sort_name(sort);
                format!(
                    "a token of `{sort}` ({{\"$token\": {{\"sort\": \"{sort}\", \"text\": ..}}}})"
                )
            }
            Self::Ctor(decl) => format!("the constructor `{decl}` ({{\"{decl}\": ..}})"),
            Self::List => "a `List` ({\"$list\": [..]})".to_owned(),
            Self::Set => "a `Set` ({\"$set\": [..]})".to_owned(),
            Self::Map => "a `Map` ({\"$map\": [[key, value], ..]})".to_owned(),
            Self::Bytes => "a `Bytes` ({\"$hex\": ..})".to_owned(),
        }
    }
}

/// The decoding of one input's document.
struct Decoder<'a> {
    values: &'a ValueIndex,
    files: &'a mut dyn InputFiles,
    /// The resolved names of the data files being decoded, outermost first.
    includes: Vec<String>,
    /// The position inside the document, as segments (`["A"]`, `[3]`, `.Run.steps`).
    path: Vec<String>,
}

impl Decoder<'_> {
    fn refuse(&self, message: &str) -> Refusal {
        Refusal {
            position: self.path.concat(),
            message: message.to_owned(),
        }
    }

    fn at<T>(
        &mut self,
        segment: String,
        decode: impl FnOnce(&mut Self) -> Result<T, Refusal>,
    ) -> Result<T, Refusal> {
        self.path.push(segment);
        let result = decode(self);
        self.path.pop();
        result
    }

    /// `message`, refused at the position `segment` below the current one.
    fn refuse_at(&self, segment: &str, message: &str) -> Refusal {
        Refusal {
            position: format!("{}{segment}", self.path.concat()),
            message: message.to_owned(),
        }
    }

    /// The resolved name and bytes of the file a `tag` form's `body` names.
    fn read_file(&mut self, tag: &str, body: &Json) -> Result<(String, Vec<u8>), Refusal> {
        let Json::String(path) = body else {
            return Err(self.refuse(&format!("`{tag}` takes a path string")));
        };
        let from = self.includes.last().map(String::as_str);
        self.files
            .read(from, path)
            .map_err(|message| self.refuse(&format!("`{tag}` `{path}`: {message}")))
    }

    fn sort_le(&self, sub: &SortRef, sup: &SortRef) -> bool {
        self.values.is_subsort(sub, sup) == Some(true)
    }

    fn builtin_le(&self, builtin: BuiltinSort, sup: &SortRef) -> bool {
        self.sort_le(&SortRef::Builtin(builtin), sup)
    }

    /// At a position a `Map` fits, how a map whose key starts with `$` is written: an object
    /// with such a key is a tagged form, not the map shorthand.
    fn dollar_key_hint(&self, ty: &InputType) -> &'static str {
        if !ty.is_untyped() && self.builtin_le(BuiltinSort::Map, &ty.sort) {
            "; a map with a key that starts with `$` is written as an array of [key, value] pairs"
        } else {
            ""
        }
    }

    /// Decode `document` at `ty`, below a whole input.
    fn decode(&mut self, document: &Json, ty: &InputType) -> Result<Value, Refusal> {
        let tagged = tagged(document)
            .map_err(|message| self.refuse(&format!("{message}{}", self.dollar_key_hint(ty))))?;
        if let Some((tag, body)) = tagged {
            let value = self.tagged(tag, body, ty)?;
            return self.fitting(value, &format!("`{tag}`"), ty);
        }
        if ty.is_untyped() {
            return self.untyped(document);
        }
        let readings = self.readings(document, ty, false)?;
        self.read_one(document, ty, &readings)
    }

    /// `value`, which `what` gave, when its sort is at most `ty`'s.
    fn fitting(&self, value: Value, what: &str, ty: &InputType) -> Result<Value, Refusal> {
        if !ty.is_untyped()
            && let Some(sort) = self.values.value_sort(&value)
            && self.values.is_subsort(&sort, &ty.sort) == Some(false)
        {
            return Err(self.refuse(&format!(
                "{what} gives a value of sort {}, which is not at most {}",
                ValueIndex::sort_name(&sort),
                ValueIndex::sort_name(&ty.sort)
            )));
        }
        Ok(value)
    }

    fn untyped(&mut self, document: &Json) -> Result<Value, Refusal> {
        const FORMS: &str = "write a constructor form or a tagged form ($string, $int, $token, $float, $list, $set, $seq, $map, $hex, $file, $data-file, $call)";
        match document {
            Json::Bool(value) => Ok(Value::Bool(*value)),
            Json::Number(value) => match number(value) {
                Number::Integer(integer) => Ok(Value::Int(integer)),
                Number::Float(float) if float.fract() != 0.0 => Ok(Value::Float(Float::from_f64(float))),
                Number::Float(_) => Err(self.refuse(&format!(
                    "{value} is undetermined at an untyped position: JSON delivers an integer beyond 64 bits as a float, so a float with an integral value reads either way; write a Float as {{\"$float\": {value}}} and an Int as {{\"$int\": \"digits\"}}"
                ))),
            },
            Json::Object(object) if object.len() == 1 => {
                let (name, fields) = object.iter().next().expect("one entry");
                let decl = self.constructor(name, &InputType::untyped())?;
                self.construct(&decl, name, fields)
            }
            Json::String(text) => Err(self.refuse(&format!(
                "the string {} is undetermined at an untyped position (a K sort, or the elements of a collection without element types); {FORMS}",
                Json::String(text.clone())
            ))),
            Json::Array(_) => Err(self.refuse(&format!(
                "an array is undetermined at an untyped position; {FORMS}"
            ))),
            Json::Object(_) | Json::Null => Err(self.refuse(&format!(
                "this document is undetermined at an untyped position; {FORMS}"
            ))),
        }
    }

    /// The readings `document`, a shorthand, has at `ty`; `key` reads a map key's string.
    fn readings(
        &self,
        document: &Json,
        ty: &InputType,
        key: bool,
    ) -> Result<Vec<Reading>, Refusal> {
        let sort = &ty.sort;
        let is = |builtin: BuiltinSort| *sort == SortRef::Builtin(builtin);
        let mut readings = Vec::new();
        match document {
            Json::Bool(_) => {
                if self.builtin_le(BuiltinSort::Bool, sort) {
                    readings.push(Reading::Bool);
                }
            }
            Json::Number(value) => {
                // The JSON type decides between the numeric builtins: an integer is an `Int`
                // where `Int` fits, and any number a `Float` where only `Float` does.
                let int = self.builtin_le(BuiltinSort::Int, sort);
                let float = self.builtin_le(BuiltinSort::Float, sort);
                match number(value) {
                    Number::Integer(_) => {
                        if int {
                            readings.push(Reading::Int);
                        } else if float {
                            readings.push(Reading::Float);
                        }
                    }
                    Number::Float(written) => {
                        if float && (!int || written.fract() != 0.0) {
                            readings.push(Reading::Float);
                        } else if is(BuiltinSort::Int) {
                            return Err(self.refuse(&format!(
                                "{value} is no integer that JSON delivers exactly: an Int is written as an integer, and one beyond 64 bits as a string of its digits, so that it is not rounded"
                            )));
                        } else if float {
                            return Err(self.refuse(&format!(
                                "{value} is undetermined at {}: JSON delivers an integer beyond 64 bits as a float, so a float with an integral value reads as an Int or a Float; write a Float as {{\"$float\": {value}}} and an Int as an integer or {{\"$int\": \"digits\"}}",
                                ValueIndex::sort_name(sort)
                            )));
                        } else if int {
                            return Err(self.refuse(&format!(
                                "{value} is no integer that JSON delivers exactly: an Int is written as an integer, and one beyond 64 bits as {{\"$int\": \"digits\"}}, so that it is not rounded"
                            )));
                        }
                    }
                }
            }
            Json::String(text) => {
                if is(BuiltinSort::Int)
                    || (key && self.builtin_le(BuiltinSort::Int, sort) && parse_int(text).is_ok())
                {
                    readings.push(Reading::IntText);
                }
                if is(BuiltinSort::Float) {
                    readings.push(Reading::FloatText);
                }
                if key
                    && self.builtin_le(BuiltinSort::Bool, sort)
                    && matches!(text.as_str(), "true" | "false")
                {
                    readings.push(Reading::BoolText);
                }
                if self.builtin_le(BuiltinSort::String, sort) {
                    readings.push(Reading::String);
                }
                for token in self.values.token_sorts() {
                    if self.sort_le(token, sort) {
                        readings.push(Reading::Token(token.clone()));
                    }
                }
                if let Some(decl) = self.constructor_reading(text, ty)? {
                    readings.push(Reading::Ctor(decl));
                }
            }
            Json::Array(_) => {
                for (builtin, reading) in [
                    (BuiltinSort::List, Reading::List),
                    (BuiltinSort::Set, Reading::Set),
                    (BuiltinSort::Bytes, Reading::Bytes),
                    (BuiltinSort::Map, Reading::Map),
                ] {
                    if self.builtin_le(builtin, sort) {
                        readings.push(reading);
                    }
                }
            }
            Json::Object(object) => {
                if self.builtin_le(BuiltinSort::Map, sort) {
                    readings.push(Reading::Map);
                }
                if object.len() == 1 {
                    let name = object.keys().next().expect("one key");
                    if let Some(decl) = self.constructor_reading(name, ty)? {
                        readings.push(Reading::Ctor(decl));
                    }
                }
            }
            Json::Null => {}
        }
        Ok(readings)
    }

    /// The constructor `name` names at `ty`, if it names one; an ambiguous name is refused.
    fn constructor_reading(&self, name: &str, ty: &InputType) -> Result<Option<Decl>, Refusal> {
        match self.resolve(name, ty, false) {
            Ok(decl) => Ok(Some(decl)),
            Err(ValueError::AmbiguousName { name, candidates }) => Err(self.refuse(&format!(
                "`{name}` names several constructors of {}: {}; write one by a longer path",
                ValueIndex::sort_name(&ty.sort),
                candidates.join(", ")
            ))),
            Err(_) => Ok(None),
        }
    }

    /// Decode `document` by its one reading at `ty`, refusing none and several.
    fn read_one(
        &mut self,
        document: &Json,
        ty: &InputType,
        readings: &[Reading],
    ) -> Result<Value, Refusal> {
        match readings {
            [reading] => self.read(document, ty, reading),
            [] => Err(self.no_reading(document, ty)),
            several => {
                let spellings = several
                    .iter()
                    .map(Reading::spelling)
                    .collect::<Vec<_>>()
                    .join(", or ");
                Err(self.refuse(&format!(
                    "{} reads several ways at {}: as {spellings}; write the form of the one meant",
                    describe(document),
                    ValueIndex::sort_name(&ty.sort)
                )))
            }
        }
    }

    fn no_reading(&self, document: &Json, ty: &InputType) -> Refusal {
        let accepts = match &ty.sort {
            SortRef::Builtin(BuiltinSort::Int) => {
                "an integer, or a string of decimal, 0x, 0o or 0b digits".to_owned()
            }
            SortRef::Builtin(BuiltinSort::Bool) => "`true` or `false`".to_owned(),
            SortRef::Builtin(BuiltinSort::String) => "a string".to_owned(),
            SortRef::Builtin(BuiltinSort::Float) => {
                "a number, or a string that is a K Float literal".to_owned()
            }
            SortRef::Builtin(BuiltinSort::Bytes) => {
                "an array of integers in 0..=255, {\"$hex\": ..} or {\"$file\": ..}; a string has no determined byte encoding".to_owned()
            }
            SortRef::Builtin(BuiltinSort::List | BuiltinSort::Set) => "an array".to_owned(),
            SortRef::Builtin(BuiltinSort::Map) => {
                "an object by key, or an array of [key, value] pairs".to_owned()
            }
            sort if self.values.is_token_sort(sort) => "a string, the token's text".to_owned(),
            sort => {
                let mut names = self
                    .values
                    .productions()
                    .filter(|info| {
                        !info.function
                            && info
                                .result
                                .as_ref()
                                .is_some_and(|result| self.sort_le(result, sort))
                    })
                    .map(|info| info.decl.path().rsplit("::").next().unwrap_or("").to_owned())
                    .collect::<Vec<_>>();
                names.sort();
                names.dedup();
                let builtins = [
                    BuiltinSort::Int,
                    BuiltinSort::Bool,
                    BuiltinSort::String,
                    BuiltinSort::Float,
                    BuiltinSort::Bytes,
                    BuiltinSort::List,
                    BuiltinSort::Set,
                    BuiltinSort::Map,
                ]
                .into_iter()
                .filter(|builtin| self.builtin_le(*builtin, sort))
                .map(|builtin| ValueIndex::sort_name(&SortRef::Builtin(builtin)))
                .collect::<Vec<_>>();
                let builtins = if builtins.is_empty() {
                    String::new()
                } else {
                    format!(", or a value of its builtin subsorts {}", builtins.join(", "))
                };
                if names.is_empty() {
                    format!(
                        "a tagged form{builtins}; {} has no constructors",
                        ValueIndex::sort_name(sort)
                    )
                } else {
                    format!(
                        "a constructor form{builtins}; its constructors are {}",
                        names.join(", ")
                    )
                }
            }
        };
        let what = match document {
            Json::String(text) => match self.resolve(text, &InputType::untyped(), false) {
                Ok(decl) => format!(
                    "{}, the constructor `{decl}` of another sort,",
                    describe(document)
                ),
                Err(ValueError::WrongKind { decl, .. }) => {
                    return self.refuse(&format!(
                        "`{decl}` is a function; write {{\"$call\": {{\"{text}\": ..}}}} to apply it"
                    ));
                }
                Err(_) => describe(document),
            },
            Json::Object(object) if object.len() == 1 => {
                let name = object.keys().next().expect("one key");
                match self.resolve(name, &InputType::untyped(), false) {
                    Err(ValueError::WrongKind { decl, .. }) => {
                        return self.refuse(&format!(
                            "`{decl}` is a function; write {{\"$call\": {{\"{name}\": ..}}}} to apply it"
                        ));
                    }
                    Ok(decl) => format!("the constructor `{decl}`, of another sort,"),
                    Err(_) => format!("`{name}` names no constructor, and the object"),
                }
            }
            _ => describe(document),
        };
        self.refuse(&format!(
            "{what} is no value of {}; it takes {accepts}",
            ValueIndex::sort_name(&ty.sort)
        ))
    }

    /// Decode `document` by `reading` at `ty`.
    fn read(
        &mut self,
        document: &Json,
        ty: &InputType,
        reading: &Reading,
    ) -> Result<Value, Refusal> {
        let element = |index| {
            if ty.sort
                == SortRef::Builtin(match reading {
                    Reading::Set => BuiltinSort::Set,
                    Reading::Map => BuiltinSort::Map,
                    _ => BuiltinSort::List,
                })
            {
                ty.element(index)
            } else {
                InputType::untyped()
            }
        };
        let text = || match document {
            Json::String(text) => text.clone(),
            _ => String::new(),
        };
        match reading {
            Reading::Bool => Ok(Value::Bool(document.as_bool().unwrap_or_default())),
            Reading::BoolText => Ok(Value::Bool(text() == "true")),
            Reading::Int => match document {
                Json::Number(value) => match number(value) {
                    Number::Integer(integer) => Ok(Value::Int(integer)),
                    Number::Float(_) => Err(self.refuse("no integer")),
                },
                _ => Err(self.refuse("no integer")),
            },
            Reading::IntText => parse_int(&text())
                .map(Value::Int)
                .map_err(|message| self.refuse(&message)),
            Reading::Float => match document {
                Json::Number(value) => float_of_number(value)
                    .map(Value::Float)
                    .map_err(|message| self.refuse(&message)),
                _ => Err(self.refuse("no number")),
            },
            Reading::FloatText => Float::parse(&text())
                .map(Value::Float)
                .map_err(|error| self.refuse(&format!("no K Float literal: {error}"))),
            Reading::String => Ok(Value::String(text())),
            Reading::Token(sort) => Ok(Value::Token {
                sort: sort.clone(),
                text: text(),
            }),
            Reading::Ctor(decl) => match document {
                Json::String(name) => self.construct(decl, name, &Json::Array(Vec::new())),
                Json::Object(object) => {
                    let (name, fields) = object.iter().next().expect("one entry");
                    self.construct(decl, name, fields)
                }
                _ => Err(self.refuse("no constructor form")),
            },
            Reading::Bytes => self.bytes(document),
            Reading::List | Reading::Set => {
                let Json::Array(items) = document else {
                    return Err(self.refuse("no array"));
                };
                let element = element(0);
                let mut decoded = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    decoded.push(self.at(format!("[{index}]"), |decoder| {
                        decoder.decode(item, &element)
                    })?);
                }
                if *reading == Reading::List {
                    Ok(Value::List(decoded))
                } else {
                    self.set(decoded)
                }
            }
            Reading::Map => {
                let (key_type, value_type) = (element(0), element(1));
                match document {
                    Json::Object(object) => {
                        let mut entries = Vec::with_capacity(object.len());
                        for (written, item) in object {
                            let segment = format!("[{}]", Json::String(written.clone()));
                            let decoded_key = self.at(
                                format!("[key {}]", Json::String(written.clone())),
                                |decoder| decoder.map_key(written, &key_type),
                            )?;
                            let decoded_value = self
                                .at(segment.clone(), |decoder| decoder.decode(item, &value_type))?;
                            entries.push((segment, decoded_key, decoded_value));
                        }
                        self.map(entries)
                    }
                    Json::Array(pairs) => self.pairs(pairs, &key_type, &value_type),
                    _ => Err(self.refuse("no object")),
                }
            }
        }
    }

    /// A map key, written as the string `written`, at `ty`.
    fn map_key(&mut self, written: &str, ty: &InputType) -> Result<Value, Refusal> {
        let document = Json::String(written.to_owned());
        if ty.is_untyped() {
            return Err(self.refuse(&format!(
                "the key {document} is undetermined: the map declares no key type; write the map as {{\"$map\": [[key, value], ..]}}"
            )));
        }
        let readings = self.readings(&document, ty, true)?;
        let several = readings.len() > 1;
        self.read_one(&document, ty, &readings).map_err(|mut refusal| {
            if several {
                refusal.message.push_str(
                    "; an object key has no tagged form, so write the map as an array of [key, value] pairs",
                );
            }
            refusal
        })
    }

    fn pairs(
        &mut self,
        pairs: &[Json],
        key_type: &InputType,
        value_type: &InputType,
    ) -> Result<Value, Refusal> {
        let mut entries = Vec::with_capacity(pairs.len());
        for (index, pair) in pairs.iter().enumerate() {
            let Some([key, value]) = pair.as_array().map(Vec::as_slice) else {
                return Err(
                    self.refuse_at(&format!("[{index}]"), "a map entry is a [key, value] pair")
                );
            };
            let decoded_key = self.at(format!("[{index}][0]"), |decoder| {
                decoder.decode(key, key_type)
            })?;
            let decoded_value = self.at(format!("[{index}][1]"), |decoder| {
                decoder.decode(value, value_type)
            })?;
            entries.push((format!("[{index}]"), decoded_key, decoded_value));
        }
        self.map(entries)
    }

    /// The map of `entries`, each with the segment it was written at; equal keys are refused.
    fn map(&self, entries: Vec<(String, Value, Value)>) -> Result<Value, Refusal> {
        let mut map = BTreeMap::new();
        let mut written = BTreeMap::new();
        for (segment, key, value) in entries {
            if let Some(first) = written.get(&key) {
                return Err(self.refuse_at(&segment, &format!(
                    "this key decodes to the same value as the key at `{first}`; K's map of two bindings of one key has no value"
                )));
            }
            written.insert(key.clone(), segment);
            map.insert(key, value);
        }
        Ok(Value::Map(map))
    }

    /// The set of `items`; two equal items are refused.
    fn set(&self, items: Vec<Value>) -> Result<Value, Refusal> {
        let mut set = BTreeSet::new();
        let mut first = BTreeMap::new();
        for (index, item) in items.into_iter().enumerate() {
            if let Some(earlier) = first.get(&item) {
                return Err(self.refuse_at(&format!("[{index}]"), &format!(
                    "this element decodes to the same value as the element at index {earlier}; K's set of two equal elements has no value"
                )));
            }
            first.insert(item.clone(), index);
            set.insert(item);
        }
        Ok(Value::Set(set))
    }

    fn bytes(&self, document: &Json) -> Result<Value, Refusal> {
        let Json::Array(items) = document else {
            return Err(self.refuse("Bytes is an array of integers in 0..=255"));
        };
        let mut bytes = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            match item.as_u64().and_then(|byte| u8::try_from(byte).ok()) {
                Some(byte) => bytes.push(byte),
                None => {
                    return Err(self.refuse_at(
                        &format!("[{index}]"),
                        &format!("{item} is no byte (an integer in 0..=255)"),
                    ));
                }
            }
        }
        Ok(Value::Bytes(bytes))
    }

    /// The production `name` names at `ty`: among the functions (`function`) or the
    /// constructors whose result sort is at most `ty`'s sort, among all at an untyped position.
    fn resolve(&self, name: &str, ty: &InputType, function: bool) -> Result<Decl, ValueError> {
        let fits = |info: &&crate::values::CtorInfo| {
            ty.is_untyped()
                || info
                    .result
                    .as_ref()
                    .is_some_and(|result| self.sort_le(result, &ty.sort))
        };
        let of_kind = |wanted: bool| {
            self.values
                .productions()
                .filter(move |info| info.function == wanted)
                .filter(fits)
                .map(|info| &info.decl)
        };
        let kind = if function { "function" } else { "constructor" };
        match crate::values::resolve(kind, name, of_kind(function)) {
            Err(ValueError::UnknownName { .. })
                if crate::values::resolve(kind, name, of_kind(!function)).is_ok() =>
            {
                Err(ValueError::WrongKind {
                    decl: crate::values::resolve(kind, name, of_kind(!function))
                        .map(|decl| decl.to_string())
                        .unwrap_or_default(),
                    function: !function,
                })
            }
            result => result,
        }
    }

    /// The constructor `name` names at `ty`, refusing a function and a name that selects none or
    /// several.
    fn constructor(&self, name: &str, ty: &InputType) -> Result<Decl, Refusal> {
        self.resolve(name, ty, false).map_err(|error| match error {
            ValueError::WrongKind { decl, .. } => self.refuse(&format!(
                "`{decl}` is a function; write {{\"$call\": {{\"{name}\": ..}}}} to apply it"
            )),
            error => self.refuse(&error.to_string()),
        })
    }

    /// The application of `decl`, written `name`, to the fields `body` writes: an object by
    /// field name, or an array in declaration order.
    fn construct(&mut self, decl: &Decl, name: &str, body: &Json) -> Result<Value, Refusal> {
        let values = self.values;
        let info = values
            .info(decl)
            .ok_or_else(|| self.refuse(&format!("no production is declared at `{decl}`")))?;
        let (prefix, verb) = if info.function {
            (format!("$call({name})."), "arguments")
        } else {
            (format!(".{name}."), "fields")
        };
        let segment = |field: &str| format!("{prefix}{field}");
        let field_type = |index: usize| {
            info.field_sorts
                .get(index)
                .cloned()
                .flatten()
                .map_or_else(InputType::untyped, InputType::of)
        };
        let expected = || {
            info.fields
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        };
        let mut fields: Vec<(Arc<str>, Value)> = Vec::with_capacity(info.fields.len());
        match body {
            Json::Array(items) => {
                if items.len() != info.fields.len() {
                    return Err(self.refuse(&format!(
                        "`{decl}` has {} {verb} ({}), not {}",
                        info.fields.len(),
                        expected(),
                        items.len()
                    )));
                }
                for (index, (field, item)) in info.fields.iter().zip(items).enumerate() {
                    let ty = field_type(index);
                    let value = self.at(segment(field), |decoder| decoder.decode(item, &ty))?;
                    fields.push((field.clone(), value));
                }
            }
            Json::Object(object) => {
                let written = object.keys().cloned().collect::<Vec<_>>();
                let declared = info
                    .fields
                    .iter()
                    .map(ToString::to_string)
                    .collect::<BTreeSet<_>>();
                if written.len() != info.fields.len()
                    || written.iter().any(|field| !declared.contains(field))
                {
                    return Err(self.refuse(&format!(
                        "`{decl}` has the {verb} ({}), not ({})",
                        expected(),
                        written.join(", ")
                    )));
                }
                for (index, field) in info.fields.iter().enumerate() {
                    let ty = field_type(index);
                    let item = &object[field.as_ref()];
                    let value = self.at(segment(field), |decoder| decoder.decode(item, &ty))?;
                    fields.push((field.clone(), value));
                }
            }
            _ => {
                return Err(self.refuse(&format!(
                    "the {verb} of `{decl}` are an object by name or an array in declaration order ([] for none)"
                )));
            }
        }
        let fields = fields
            .iter()
            .map(|(field, value)| (field.as_ref(), value.clone()));
        let built = if info.function {
            values.call(decl.path(), fields)
        } else {
            values.ctor(decl.path(), fields)
        };
        built.map_err(|error| self.refuse(&error.to_string()))
    }

    /// The value of the tagged form `tag` with `body` at `ty`.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per tag keeps the table of tagged forms in one place"
    )]
    fn tagged(&mut self, tag: &str, body: &Json, ty: &InputType) -> Result<Value, Refusal> {
        let string = |decoder: &Self| match body {
            Json::String(text) => Ok(text.clone()),
            _ => Err(decoder.refuse(&format!("`{tag}` takes a string"))),
        };
        let array = |decoder: &Self| match body {
            Json::Array(items) => Ok(items.clone()),
            _ => Err(decoder.refuse(&format!("`{tag}` takes an array"))),
        };
        match tag {
            "$text" | "$text-file" => Err(self.refuse(&format!(
                "`{tag}` stands for a whole input, which is parsed at the input's sort; inside a value write the value's own form"
            ))),
            "$file" => {
                let (_, bytes) = self.read_file(tag, body)?;
                Ok(Value::Bytes(bytes))
            }
            "$hex" => parse_hex(&string(self)?)
                .map(Value::Bytes)
                .map_err(|message| self.refuse(&message)),
            "$data-file" => {
                let (name, bytes) = self.read_file(tag, body)?;
                if let Some(start) = self.includes.iter().position(|included| *included == name) {
                    let cycle = self.includes[start..]
                        .iter()
                        .chain([&name])
                        .map(|name| format!("`{name}`"))
                        .collect::<Vec<_>>()
                        .join(" includes ");
                    return Err(self.refuse(&format!("`$data-file` includes itself: {cycle}")));
                }
                let text = String::from_utf8(bytes)
                    .map_err(|_| self.refuse(&format!("`$data-file` `{name}` is no UTF-8 text")))?;
                let extension = std::path::Path::new(&name)
                    .extension()
                    .and_then(std::ffi::OsStr::to_str)
                    .unwrap_or_default();
                let document = if extension.eq_ignore_ascii_case("json") {
                    json_document(&text)
                } else if extension.eq_ignore_ascii_case("toml") {
                    text.parse::<toml::Table>()
                        .map_err(|error| InputError::document(format!("no TOML document: {error}")))
                        .and_then(|table| toml_document(&toml::Value::Table(table)))
                } else {
                    Err(InputError::document(
                        "a data file is `.json` or `.toml`, by its extension".to_owned(),
                    ))
                }
                .map_err(|error| {
                    let position = if error.position.is_empty() {
                        String::new()
                    } else {
                        format!(" at `{}`", error.position)
                    };
                    self.refuse(&format!("`$data-file` `{name}`{position}: {}", error.message))
                })?;
                self.includes.push(name.clone());
                let decoded = self.at(format!("$data-file({name})"), |decoder| decoder.decode(&document, ty));
                self.includes.pop();
                decoded
            }
            "$string" => Ok(Value::String(string(self)?)),
            "$int" => match body {
                Json::String(text) => parse_int(text)
                    .map(Value::Int)
                    .map_err(|message| self.refuse(&format!("`$int`: {message}"))),
                Json::Number(value) => match number(value) {
                    Number::Integer(integer) => Ok(Value::Int(integer)),
                    Number::Float(_) => Err(self.refuse(&format!(
                        "`$int`: {value} is no integer that JSON delivers exactly; write the Int as a string of its digits"
                    ))),
                },
                _ => Err(self.refuse("`$int` takes a string of digits or an integer")),
            },
            "$float" => match body {
                Json::Number(value) => float_of_number(value)
                    .map(Value::Float)
                    .map_err(|message| self.refuse(&format!("`$float`: {message}"))),
                Json::String(literal) => Float::parse(literal)
                    .map(Value::Float)
                    .map_err(|error| self.refuse(&format!("`$float`: no K Float literal: {error}"))),
                _ => Err(self.refuse("`$float` takes a number or a K Float literal string")),
            },
            "$token" => {
                let (sort, text) = match body {
                    Json::String(text) => {
                        if !self.values.is_token_sort(&ty.sort) {
                            return Err(self.refuse(&format!(
                                "{} is no token sort, so `$token` names its sort: {{\"$token\": {{\"sort\": .., \"text\": ..}}}}",
                                ValueIndex::sort_name(&ty.sort)
                            )));
                        }
                        (ty.sort.clone(), text.clone())
                    }
                    Json::Object(object)
                        if object.len() == 2
                            && object.get("sort").is_some_and(Json::is_string)
                            && object.get("text").is_some_and(Json::is_string) =>
                    {
                        let name = object["sort"].as_str().unwrap_or_default();
                        let sort = self
                            .values
                            .sort(name)
                            .map_err(|error| self.refuse(&format!("`$token`: {error}")))?;
                        if !self.values.is_token_sort(&sort) {
                            return Err(self.refuse(&format!("`$token`: {name} is no token sort")));
                        }
                        (sort, object["text"].as_str().unwrap_or_default().to_owned())
                    }
                    _ => {
                        return Err(self.refuse(
                            "`$token` takes the token's text, or {\"sort\": .., \"text\": ..}",
                        ));
                    }
                };
                Ok(Value::Token { sort, text })
            }
            "$list" | "$set" | "$seq" => {
                let items = array(self)?;
                let mut decoded = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    decoded.push(self.at(format!("{tag}[{index}]"), |decoder| {
                        decoder.decode(item, &InputType::untyped())
                    })?);
                }
                match tag {
                    "$list" => Ok(Value::List(decoded)),
                    "$seq" => Ok(Value::Seq(decoded)),
                    _ => self.at(tag.to_owned(), |decoder| decoder.set(decoded)),
                }
            }
            "$map" => {
                let pairs = array(self)?;
                self.at("$map".to_owned(), |decoder| {
                    decoder.pairs(&pairs, &InputType::untyped(), &InputType::untyped())
                })
            }
            "$call" => {
                let Json::Object(object) = body else {
                    return Err(self.refuse("`$call` takes {\"path::f\": arguments}"));
                };
                let mut entries = object.iter();
                let (Some((name, arguments)), None) = (entries.next(), entries.next()) else {
                    return Err(self.refuse("`$call` takes {\"path::f\": arguments}, one function"));
                };
                let decl = self.resolve(name, ty, true).map_err(|error| match error {
                    ValueError::WrongKind { decl, .. } => self.refuse(&format!(
                        "`{decl}` is a constructor; write it without $call: {{\"{name}\": ..}}"
                    )),
                    error => self.refuse(&format!("`$call`: {error}")),
                })?;
                self.construct(&decl, name, arguments)
            }
            other => Err(self.refuse(&format!(
                "unknown tag `{other}`; the tags are $text, $text-file, $file, $hex, $data-file, $string, $int, $float, $token, $list, $set, $seq, $map and $call{}",
                self.dollar_key_hint(ty)
            ))),
        }
    }
}

/// A short description of a document for a message.
fn describe(document: &Json) -> String {
    match document {
        Json::String(text) => format!("the string {}", Json::String(text.clone())),
        Json::Number(value) => format!("the number {value}"),
        Json::Bool(value) => format!("`{value}`"),
        Json::Array(_) => "the array".to_owned(),
        Json::Object(_) => "the object".to_owned(),
        Json::Null => "`null`".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::{Case, InputError, Json, json_document, parse_hex, parse_int, toml_document};
    use num_bigint::BigInt;

    /// The Definition IR says that a main parameter reads a file's bytes where its sort is the
    /// builtin `Bytes` with no arguments, and that it reads text under any other builtin or
    /// declared sort; under a cell sort or a sort parameter, at any depth, the compiled definition
    /// types the parameter and the IR gives no answer.
    #[test]
    fn the_ir_reads_a_file_as_bytes_only_for_exactly_the_builtin_bytes() {
        use krs_ir::{BuiltinSort, CellSortArgument};
        use krs_ir_levels::{DefinitionSortRef, SortParameterId, SymbolId};

        let symbol = |id: &str| SymbolId::new(id).unwrap();
        let argument = |sort: DefinitionSortRef| CellSortArgument {
            sort,
            arguments: Vec::new(),
        };
        let bytes = DefinitionSortRef::Builtin(BuiltinSort::Bytes);
        let int = DefinitionSortRef::Builtin(BuiltinSort::Int);
        let map = DefinitionSortRef::Builtin(BuiltinSort::Map);
        let declared = DefinitionSortRef::Declared(symbol("sort.op"));
        let cell = DefinitionSortRef::Cell(symbol("cell.rom"));
        let parameter = DefinitionSortRef::Parameter(SortParameterId::new("S"));
        assert_eq!(super::file_reading(&bytes, &[]), Some(true));
        assert_eq!(super::file_reading(&int, &[]), Some(false));
        assert_eq!(super::file_reading(&declared, &[]), Some(false));
        assert_eq!(
            super::file_reading(&map, &[argument(int.clone()), argument(bytes.clone())]),
            Some(false)
        );
        assert_eq!(super::file_reading(&cell, &[]), None);
        assert_eq!(super::file_reading(&parameter, &[]), None);
        assert_eq!(
            super::file_reading(&map, &[argument(int), argument(cell)]),
            None
        );
    }

    #[test]
    fn the_integer_grammar_reads_decimal_and_prefixed_digits_and_nothing_else() {
        for (text, value) in [
            ("0", "0"),
            ("-17", "-17"),
            ("007", "7"),
            ("0x1F", "31"),
            ("0xff", "255"),
            ("-0x10", "-16"),
            ("0o17", "15"),
            ("0b101", "5"),
            ("18446744073709551616", "18446744073709551616"),
            (
                "-340282366920938463463374607431768211456",
                "-340282366920938463463374607431768211456",
            ),
        ] {
            assert_eq!(
                parse_int(text),
                Ok(value.parse::<BigInt>().unwrap()),
                "{text}"
            );
        }
        for text in [
            "", "-", "+1", "1_000", " 1", "1 ", "0x", "0xg", "0b2", "1.0", "1e3", "0X1F", "--1",
        ] {
            assert!(parse_int(text).is_err(), "{text}");
        }
    }

    #[test]
    #[expect(
        clippy::cast_precision_loss,
        reason = "the integers cast are the ones binary64 holds exactly"
    )]
    fn an_integer_is_a_float_only_where_binary64_holds_it_exactly() {
        for exact in [0_i64, -3, 1 << 53, -(1 << 53), 1 << 60, i64::MIN] {
            assert_eq!(
                super::float_of_integer(&exact.into()).unwrap().to_f64(),
                Some(exact as f64),
                "{exact}"
            );
        }
        for inexact in [(1_i64 << 53) + 1, i64::MAX, -(1 << 60) - 1] {
            assert!(
                super::float_of_integer(&inexact.into()).is_err(),
                "{inexact}"
            );
        }
        // Beyond i64 as well: 2^63 and 2^64 are binary64 values, u64::MAX and 2^64 + 1 are not.
        assert_eq!(
            super::float_of_integer(&(1_u64 << 63).into())
                .unwrap()
                .to_f64(),
            Some(9_223_372_036_854_775_808.0)
        );
        assert_eq!(
            super::float_of_integer(&(BigInt::from(1) << 64))
                .unwrap()
                .to_f64(),
            Some(18_446_744_073_709_551_616.0)
        );
        assert!(super::float_of_integer(&u64::MAX.into()).is_err());
        assert!(super::float_of_integer(&((BigInt::from(1) << 64) + 1)).is_err());
        assert!(super::float_of_integer(&(BigInt::from(1) << 1024)).is_err());
    }

    #[test]
    fn a_number_at_float_is_refused_where_a_json_reader_may_have_rounded_it() {
        let float = |text: &str| {
            let Json::Number(number) = super::json_document(text).unwrap() else {
                panic!("{text} is a number");
            };
            super::float_of_number(&number).map(|float| float.to_f64())
        };
        assert_eq!(float("1.5"), Ok(Some(1.5)));
        assert_eq!(
            float("9223372036854775808"),
            Ok(Some(9_223_372_036_854_775_808.0))
        );
        assert_eq!(float("1e19"), Ok(Some(1e19)));
        assert!(float("9007199254740993").is_err());
        // An integer beyond 64 bits arrives rounded, and so does every float of its value.
        assert!(float("18446744073709551617").is_err());
        assert!(float("1.8446744073709552e19").is_err());
        assert!(float("-9223372036854775809").is_err());
        assert_eq!(
            float("-9223372036854775808"),
            Ok(Some(-9_223_372_036_854_775_808.0))
        );
    }

    #[test]
    fn hex_bytes_are_an_even_count_of_digits_of_either_case() {
        assert_eq!(parse_hex("00ff1A"), Ok(vec![0, 0xff, 0x1a]));
        assert_eq!(parse_hex(""), Ok(Vec::new()));
        for text in ["0", "0g", "00 ff", "0x00"] {
            assert!(parse_hex(text).is_err(), "{text}");
        }
    }

    #[test]
    fn toml_converts_to_the_json_data_model_keeping_non_finite_floats_tagged() {
        let table = r#"
            a = 1
            b = 1.5
            c = nan
            d = -inf
            e = "x"
            f = [true, { g = 2 }]
        "#
        .parse::<toml::Table>()
        .unwrap();
        assert_eq!(
            toml_document(&toml::Value::Table(table)).unwrap(),
            serde_json::json!({
                "a": 1, "b": 1.5, "c": {"$float": "NaN"}, "d": {"$float": "-Infinity"},
                "e": "x", "f": [true, {"g": 2}]
            })
        );
    }

    #[test]
    fn a_toml_datetime_is_refused_where_it_stands() {
        let table = "a = [1, 1979-05-27T07:32:00Z]"
            .parse::<toml::Table>()
            .unwrap();
        let error = toml_document(&toml::Value::Table(table)).unwrap_err();
        assert_eq!(error.position, "[\"a\"][1]");
        assert_eq!(
            error.to_string(),
            "at `[\"a\"][1]`: a TOML datetime has no reading as a term"
        );
    }

    #[test]
    fn a_json_object_with_a_repeated_key_is_refused() {
        assert_eq!(
            json_document(r#"{"a": [1, {"b": 2}]}"#).unwrap(),
            serde_json::json!({"a": [1, {"b": 2}]})
        );
        let error = json_document(r#"{"a": {"b": 1, "b": 2}}"#).unwrap_err();
        assert!(
            error
                .message
                .contains("the key `b` is repeated in one object"),
            "{error}"
        );
        assert!(json_document("[1] 2").is_err());
    }

    #[test]
    fn a_case_has_inputs_and_no_other_key() {
        let case = Case::from_toml("[inputs]\npc = 256\nregs = { A = 1 }\n").unwrap();
        assert_eq!(
            case.inputs,
            vec![
                ("pc".to_owned(), Json::from(256)),
                ("regs".to_owned(), serde_json::json!({"A": 1}))
            ]
        );
        assert_eq!(
            Case::from_json(r#"{"inputs": {"pc": 1}}"#)
                .unwrap()
                .inputs
                .len(),
            1
        );
        assert_eq!(Case::from_json("{}").unwrap(), Case::default());
        let unknown = Case::from_toml("[inputs]\n[expect]\n").unwrap_err();
        assert_eq!(
            unknown,
            InputError {
                parameter: None,
                declared: None,
                position: String::new(),
                message: "unknown key `expect` in a case; a case has the key `inputs`".to_owned(),
            }
        );
        assert!(Case::from_json(r#"{"inputs": [1]}"#).is_err());
        assert!(Case::from_json("[]").is_err());
    }
}
