//! The canonical document of a value: the document of the typed encoding that decodes back to
//! the value at its position ([`crate::inputs`], "The canonical document of a value", is the
//! normative statement), and its canonical text.
//!
//! The encoder asks the decoder's own judgements wherever a choice depends on the definition (a
//! constructor's shortest name, whether a shorthand or a nullary constructor's bare name has one
//! reading, a map key's spelling), so a document it writes is one the decoder reads by its
//! rules, never by a copy of them.

use std::fmt::{self, Write as _};

use krs_ir::BuiltinSort;
use num_bigint::BigInt;
use serde_json::Value as Json;

use crate::inputs::{self, InputError, InputType};
use crate::values::{Ctor, Float, SortRef, Value, ValueIndex, ieee_literal};

/// Why a value has no document at its position: the position of the part that has none, in the
/// notation of [`InputError`]'s positions (`.Run.log$list[2]`, empty for the whole value), what
/// the part is, and which rule of the encoding refuses it.
///
/// A value whose only parts without a document are [`EncodeErrorKind::Opaque`] parts and
/// [`EncodeErrorKind::Parametric`] applications is refused naming the first of them; a value
/// with a part of any other kind is refused naming the first such part, wherever the others
/// are, so that a part a value may hold by its nature never hides one that says the value is
/// not what its position admits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EncodeError {
    /// Where in the value.
    pub position: String,
    /// What has no document there.
    pub part: String,
    /// The rule that refuses it.
    pub kind: EncodeErrorKind,
}

/// The rule of the encoding by which a part has no document.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EncodeErrorKind {
    /// An `Opaque` part: a variable, an unevaluated application, a freezer or another
    /// constructor without a KRS declaration, a matching-logic connective.
    Opaque,
    /// The application of a parametric constructor, which no form of the encoding writes.
    Parametric,
    /// A part whose sort is not at most its position's.
    Sort,
    /// A domain value of a sort that is no token sort.
    NoTokenSort,
    /// A constructor or sort that the definition does not declare, or that no name selects.
    Unnamed,
}

impl EncodeErrorKind {
    /// Whether a part of this kind is one a state may hold by its nature (an `Opaque` part, a
    /// parametric application), as opposed to one that says the value is not what its
    /// position admits or that the definition has a value the encoding cannot spell.
    #[must_use]
    pub const fn is_inherent(self) -> bool {
        matches!(self, Self::Opaque | Self::Parametric)
    }
}

impl fmt::Display for EncodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.position.is_empty() {
            write!(formatter, "`{}`: ", self.position)?;
        }
        write!(
            formatter,
            "{} has no document in the typed encoding",
            self.part
        )
    }
}

impl std::error::Error for EncodeError {}

/// The canonical document of `value` at the position `ty`.
///
/// # Errors
///
/// Returns [`EncodeError`] for a value with no document there: an `Opaque` part, the
/// application of a parametric constructor, a part whose sort is not at most its position's, a
/// domain value of a sort that is no token sort, and a constructor or sort no name selects; a
/// part of an inherent kind only where the value has no part of another kind ([`EncodeError`]).
pub fn encode(values: &ValueIndex, value: &Value, ty: &InputType) -> Result<Json, EncodeError> {
    let mut encoder = Encoder {
        values,
        path: Vec::new(),
        inherent: None,
    };
    let document = encoder.encode(value, ty)?;
    match encoder.inherent {
        Some(error) => Err(error),
        None => Ok(document),
    }
}

/// The value `document` denotes at `ty`, read as a part of an input is (no `$text`, and no file
/// read): the decoding [`encode`] is the inverse of.
///
/// # Errors
///
/// Returns [`InputError`] with the declared type, the position in the document and the reason,
/// for a document that is no value at `ty`.
pub fn decode(values: &ValueIndex, document: &Json, ty: &InputType) -> Result<Value, InputError> {
    inputs::decode_value(values, document, ty).map_err(|refusal| InputError {
        parameter: None,
        declared: Some(ty.to_string()),
        position: refusal.position,
        message: refusal.message,
    })
}

/// The canonical text of `document`: compact JSON, with the members of each object ordered by
/// the bytes of their keys, whatever map type the JSON library was built with.
#[must_use]
pub fn canonical_text(document: &Json) -> String {
    let mut text = String::new();
    write_canonical(document, &mut text);
    text
}

fn write_canonical(document: &Json, text: &mut String) {
    match document {
        Json::Null => text.push_str("null"),
        Json::Bool(value) => text.push_str(if *value { "true" } else { "false" }),
        Json::Number(number) => text.push_str(&number.to_string()),
        Json::String(string) => write_string(string, text),
        Json::Array(items) => {
            text.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    text.push(',');
                }
                write_canonical(item, text);
            }
            text.push(']');
        }
        Json::Object(object) => {
            let mut members = object.iter().collect::<Vec<_>>();
            members.sort_unstable_by(|(left, _), (right, _)| left.as_bytes().cmp(right.as_bytes()));
            text.push('{');
            for (index, (key, item)) in members.into_iter().enumerate() {
                if index > 0 {
                    text.push(',');
                }
                write_string(key, text);
                text.push(':');
                write_canonical(item, text);
            }
            text.push('}');
        }
    }
}

/// A JSON string: `"` and `\` escaped, the control characters as `\b`, `\f`, `\n`, `\r`, `\t`
/// or `\u00XX` (lowercase), every other character as itself.
fn write_string(string: &str, text: &mut String) {
    text.push('"');
    for character in string.chars() {
        match character {
            '"' => text.push_str("\\\""),
            '\\' => text.push_str("\\\\"),
            '\u{8}' => text.push_str("\\b"),
            '\u{c}' => text.push_str("\\f"),
            '\n' => text.push_str("\\n"),
            '\r' => text.push_str("\\r"),
            '\t' => text.push_str("\\t"),
            control if u32::from(control) < 0x20 => {
                let _ = write!(text, "\\u{:04x}", u32::from(control));
            }
            other => text.push(other),
        }
    }
    text.push('"');
}

/// The K `Float` literal of `float` the encoding writes: the shortest decimal digits that read
/// back to a binary64 or binary32 value, with a `.`, a fractional digit and an exponent, and the
/// canonical literal of any other format.
fn float_literal(float: &Float) -> String {
    /// Rust's shortest round-trip `{:e}` text of a finite value (`1.5e0`, `1e300`, `-0e0`), its
    /// significand given a fractional digit.
    fn with_fraction(exponent_form: &str) -> String {
        let (significand, exponent) = exponent_form
            .split_once('e')
            .unwrap_or((exponent_form, "0"));
        if significand.contains('.') {
            format!("{significand}e{exponent}")
        } else {
            format!("{significand}.0e{exponent}")
        }
    }
    let written = if let Some(value) = float.to_f64() {
        ieee_literal(
            value.is_nan(),
            value.is_infinite(),
            value.is_sign_negative(),
            &with_fraction(&format!("{value:e}")),
            "",
        )
    } else if let Some(value) = float.to_f32() {
        ieee_literal(
            value.is_nan(),
            value.is_infinite(),
            value.is_sign_negative(),
            &with_fraction(&format!("{value:e}")),
            "f",
        )
    } else {
        return float.literal().to_owned();
    };
    // The shortest digits read back by construction; the canonical literal is the fallback
    // that reads back by definition, should a reading ever round otherwise.
    if Float::parse(&written).as_ref() == Ok(float) {
        written
    } else {
        float.literal().to_owned()
    }
}

/// What the application of a parametric constructor is, for its refusal.
fn parametric_part(ctor: &Ctor) -> String {
    let arguments = ctor
        .sort_args()
        .iter()
        .map(ValueIndex::sort_name)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "the application of the parametric constructor `{}` at the sort arguments {arguments}, which no form of the encoding writes,",
        ctor.decl()
    )
}

/// A one-member object, `{key: value}`.
fn tagged(key: &str, value: Json) -> Json {
    let mut object = serde_json::Map::new();
    object.insert(key.to_owned(), value);
    Json::Object(object)
}

/// The writing of one value's canonical document.
struct Encoder<'a> {
    values: &'a ValueIndex,
    /// The position inside the document, as the decoder spells its segments.
    path: Vec<String>,
    /// The first part of an inherent kind ([`EncodeErrorKind::is_inherent`]) met so far: the
    /// encoder goes on past it, so that a part of another kind later in the value is the one
    /// refused.
    inherent: Option<EncodeError>,
}

impl Encoder<'_> {
    fn refuse(&self, kind: EncodeErrorKind, part: String) -> EncodeError {
        EncodeError {
            position: self.path.concat(),
            part,
            kind,
        }
    }

    /// Record the part of an inherent kind at this position, unless one is recorded already,
    /// and stand in for its document with `null`, which no caller sees: [`encode`] returns the
    /// recorded refusal.
    fn inherent(&mut self, kind: EncodeErrorKind, part: String) -> Json {
        if self.inherent.is_none() {
            self.inherent = Some(self.refuse(kind, part));
        }
        Json::Null
    }

    fn at<T>(
        &mut self,
        segment: String,
        encode: impl FnOnce(&mut Self) -> Result<T, EncodeError>,
    ) -> Result<T, EncodeError> {
        self.path.push(segment);
        let result = encode(self);
        self.path.pop();
        result
    }

    /// `shorthand` where the decoder reads it one way at `ty`, else `tagged`.
    fn shorthand_or(&self, shorthand: Json, ty: &InputType, tagged: impl FnOnce() -> Json) -> Json {
        if inputs::sole_reading(self.values, &shorthand, ty) {
            shorthand
        } else {
            tagged()
        }
    }

    /// Refuse a value whose sort is not at most the sort of the typed position `ty`.
    fn check_sort(&self, value: &Value, ty: &InputType) -> Result<(), EncodeError> {
        let sort = self.values.value_sort(value);
        if ty.is_untyped()
            || sort
                .as_ref()
                .is_some_and(|sort| self.values.is_subsort(sort, &ty.sort) == Some(true))
        {
            return Ok(());
        }
        let sort = sort.map_or_else(
            || "no KRS sort".to_owned(),
            |sort| ValueIndex::sort_name(&sort),
        );
        Err(self.refuse(
            EncodeErrorKind::Sort,
            format!(
                "a value of {sort} at a position of sort {}, which it is not at most,",
                ValueIndex::sort_name(&ty.sort)
            ),
        ))
    }

    fn encode(&mut self, value: &Value, ty: &InputType) -> Result<Json, EncodeError> {
        if let Value::Opaque(pattern) = value {
            let part = self.values.opaque_part(pattern);
            return Ok(self.inherent(EncodeErrorKind::Opaque, part));
        }
        // A parametric constructor's result sort is a parameter, so this comes before the
        // position's check, which would name no sort.
        if let Value::Ctor(ctor) = value
            && !ctor.sort_args().is_empty()
        {
            return Ok(self.inherent(EncodeErrorKind::Parametric, parametric_part(ctor)));
        }
        self.check_sort(value, ty)?;
        let at = |builtin: BuiltinSort| ty.sort == SortRef::Builtin(builtin);
        Ok(match value {
            Value::Opaque(_) => unreachable!("refused above"),
            Value::Int(integer) => self.int(integer, ty, at(BuiltinSort::Int)),
            Value::Bool(boolean) => Json::Bool(*boolean),
            Value::String(string) => {
                let tag = || tagged("$string", Json::String(string.clone()));
                if at(BuiltinSort::String) {
                    self.shorthand_or(Json::String(string.clone()), ty, tag)
                } else {
                    tag()
                }
            }
            Value::Float(float) => {
                let literal = float_literal(float);
                let tag = || tagged("$float", Json::String(literal.clone()));
                if at(BuiltinSort::Float) {
                    self.shorthand_or(Json::String(literal.clone()), ty, tag)
                } else {
                    tag()
                }
            }
            Value::Bytes(bytes) => {
                let mut hex = String::with_capacity(bytes.len() * 2);
                for byte in bytes {
                    let _ = write!(hex, "{byte:02x}");
                }
                tagged("$hex", Json::String(hex))
            }
            Value::Token { sort, text } => self.token(sort, text, ty)?,
            Value::Seq(items) => tagged("$seq", self.untyped_items("$seq", items)?),
            Value::List(items) => {
                if at(BuiltinSort::List) {
                    let element = ty.element(0);
                    let mut documents = Vec::with_capacity(items.len());
                    for (index, item) in items.iter().enumerate() {
                        documents.push(self.at(format!("[{index}]"), |encoder| {
                            encoder.encode(item, &element)
                        })?);
                    }
                    Json::Array(documents)
                } else {
                    tagged("$list", self.untyped_items("$list", items)?)
                }
            }
            Value::Set(items) => {
                let (tag, element) = if at(BuiltinSort::Set) {
                    ("", ty.element(0))
                } else {
                    ("$set", InputType::untyped())
                };
                let mut documents = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    let document = self.at(format!("{tag}[{index}]"), |encoder| {
                        encoder.encode(item, &element)
                    })?;
                    documents.push((canonical_text(&document), document));
                }
                documents.sort_unstable_by(|(left, _), (right, _)| {
                    left.as_bytes().cmp(right.as_bytes())
                });
                let array = Json::Array(
                    documents
                        .into_iter()
                        .map(|(_, document)| document)
                        .collect(),
                );
                if tag.is_empty() {
                    array
                } else {
                    tagged(tag, array)
                }
            }
            Value::Map(entries) => self.map(entries, ty, at(BuiltinSort::Map))?,
            Value::Ctor(ctor) => self.ctor(ctor, ty)?,
        })
    }

    fn int(&self, integer: &BigInt, ty: &InputType, at_int: bool) -> Json {
        let small = i64::try_from(integer).ok();
        match (small, at_int) {
            (Some(small), _) => Json::from(small),
            (None, true) => self.shorthand_or(Json::String(integer.to_string()), ty, || {
                tagged("$int", Json::String(integer.to_string()))
            }),
            (None, false) => tagged("$int", Json::String(integer.to_string())),
        }
    }

    /// The documents of a tagged collection's items, untyped, at `tag[index]`.
    fn untyped_items(&mut self, tag: &str, items: &[Value]) -> Result<Json, EncodeError> {
        let mut documents = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            documents.push(self.at(format!("{tag}[{index}]"), |encoder| {
                encoder.encode(item, &InputType::untyped())
            })?);
        }
        Ok(Json::Array(documents))
    }

    fn token(&self, sort: &SortRef, text: &str, ty: &InputType) -> Result<Json, EncodeError> {
        if !self.values.is_token_sort(sort) {
            return Err(self.refuse(
                EncodeErrorKind::NoTokenSort,
                format!(
                    "the domain value {} of {}, which is no token sort,",
                    Json::String(text.to_owned()),
                    ValueIndex::sort_name(sort)
                ),
            ));
        }
        if ty.sort == *sort {
            return Ok(self.shorthand_or(Json::String(text.to_owned()), ty, || {
                tagged("$token", Json::String(text.to_owned()))
            }));
        }
        let mut body = serde_json::Map::new();
        body.insert("sort".to_owned(), Json::String(self.sort_name(sort)?));
        body.insert("text".to_owned(), Json::String(text.to_owned()));
        Ok(tagged("$token", Json::Object(body)))
    }

    /// The shortest name of `sort` that [`ValueIndex::sort`] resolves to it: a builtin's K name,
    /// a declared sort's shortest `::`-aligned suffix.
    fn sort_name(&self, sort: &SortRef) -> Result<String, EncodeError> {
        let path = match sort {
            SortRef::Builtin(builtin) => return Ok(builtin.k_name().to_owned()),
            SortRef::Declared(decl) => decl.path(),
        };
        shortest_suffix(path, |name| self.values.sort(name).as_ref() == Ok(sort)).ok_or_else(|| {
            self.refuse(
                EncodeErrorKind::Unnamed,
                format!("the sort {path}, which no name resolves to,"),
            )
        })
    }

    fn map(
        &mut self,
        entries: &std::collections::BTreeMap<Value, Value>,
        ty: &InputType,
        at_map: bool,
    ) -> Result<Json, EncodeError> {
        let (key_type, value_type) = if at_map {
            (ty.element(0), ty.element(1))
        } else {
            (InputType::untyped(), InputType::untyped())
        };
        if at_map && !key_type.is_untyped() {
            let spellings = entries
                .keys()
                .map(|key| {
                    self.key_spelling(key, &key_type)
                        .filter(|spelling| !spelling.starts_with('$'))
                })
                .collect::<Option<Vec<_>>>();
            if let Some(spellings) = spellings {
                let mut members = spellings
                    .into_iter()
                    .zip(entries.values())
                    .collect::<Vec<_>>();
                members.sort_unstable_by(|(left, _), (right, _)| {
                    left.as_bytes().cmp(right.as_bytes())
                });
                let mut object = serde_json::Map::new();
                for (spelling, item) in members {
                    let segment = format!("[{}]", Json::String(spelling.clone()));
                    let document = self.at(segment, |encoder| encoder.encode(item, &value_type))?;
                    object.insert(spelling, document);
                }
                let object = Json::Object(object);
                if inputs::sole_reading(self.values, &object, ty) {
                    return Ok(object);
                }
            }
        }
        let tag = if at_map { "" } else { "$map" };
        let mut keys = Vec::with_capacity(entries.len());
        for (index, key) in entries.keys().enumerate() {
            let document = self.at(format!("{tag}[{index}][0]"), |encoder| {
                encoder.encode(key, &key_type)
            })?;
            keys.push((canonical_text(&document), document));
        }
        let mut pairs = keys.into_iter().zip(entries.values()).collect::<Vec<_>>();
        pairs.sort_unstable_by(|((left, _), _), ((right, _), _)| {
            left.as_bytes().cmp(right.as_bytes())
        });
        let mut documents = Vec::with_capacity(pairs.len());
        for (index, ((_, key), item)) in pairs.into_iter().enumerate() {
            let document = self.at(format!("{tag}[{index}][1]"), |encoder| {
                encoder.encode(item, &value_type)
            })?;
            documents.push(Json::Array(vec![key, document]));
        }
        let array = Json::Array(documents);
        Ok(if at_map { array } else { tagged(tag, array) })
    }

    /// The object key that reads as `key` at `ty` and as nothing else, if one does.
    fn key_spelling(&self, key: &Value, ty: &InputType) -> Option<String> {
        let written = match key {
            Value::Int(integer) => integer.to_string(),
            Value::Bool(boolean) => boolean.to_string(),
            Value::String(string) => string.clone(),
            Value::Token { text, .. } => text.clone(),
            Value::Ctor(ctor) if ctor.fields().is_empty() && ctor.sort_args().is_empty() => {
                self.ctor_name(ctor, ty, false).ok()?
            }
            _ => return None,
        };
        (inputs::map_key(self.values, &written, ty).as_ref() == Some(key)).then_some(written)
    }

    /// The shortest name the decoder resolves to `ctor`'s declaration at `ty`.
    fn ctor_name(
        &self,
        ctor: &Ctor,
        ty: &InputType,
        function: bool,
    ) -> Result<String, EncodeError> {
        let decl = ctor.decl();
        shortest_suffix(decl.path(), |name| {
            inputs::names(self.values, name, ty, function, decl)
        })
        .ok_or_else(|| {
            self.refuse(
                EncodeErrorKind::Unnamed,
                format!(
                    "`{decl}`, which no name selects at {},",
                    ValueIndex::sort_name(&ty.sort)
                ),
            )
        })
    }

    /// How the constructor application `ctor` is written at `ty`: its name and its form.
    fn ctor_form(&self, ctor: &Ctor, ty: &InputType) -> Result<CtorForm, EncodeError> {
        let decl = ctor.decl();
        let info = self.values.info(decl).ok_or_else(|| {
            self.refuse(
                EncodeErrorKind::Unnamed,
                format!("`{decl}`, which the definition does not declare,"),
            )
        })?;
        let function = info.function;
        let name = self.ctor_name(ctor, ty, function)?;
        // The constructor form where it reads as the constructor alone; at a declared sort that
        // `Map` is at most, where an object is a map too, the tagged form `$ctor`.
        let tagged_ctor = !function
            && !ty.is_untyped()
            && !inputs::sole_reading(self.values, &tagged(&name, Json::Array(Vec::new())), ty);
        Ok(CtorForm {
            name,
            function,
            tagged: tagged_ctor,
        })
    }

    fn ctor(&mut self, ctor: &Ctor, ty: &InputType) -> Result<Json, EncodeError> {
        let form = self.ctor_form(ctor, ty)?;
        let field_types = self
            .values
            .info(ctor.decl())
            .map(|info| info.field_types.clone())
            .unwrap_or_default();
        let fields = ctor.fields();
        // The bare name where the decoder reads it as this constructor alone: at a declared
        // sort that neither `String` nor a token sort is at most, by the decoder's table.
        if !form.function
            && fields.is_empty()
            && let SortRef::Declared(_) = &ty.sort
            && inputs::sole_reading(self.values, &Json::String(form.name.clone()), ty)
        {
            return Ok(Json::String(form.name));
        }
        let prefix = form.prefix();
        let CtorForm {
            name,
            function,
            tagged: tag_ctor,
        } = form;
        let tuple = !fields.is_empty()
            && fields
                .iter()
                .enumerate()
                .all(|(index, (field, _))| field.as_ref() == index.to_string());
        let mut documents = Vec::with_capacity(fields.len());
        for (index, (field, item)) in fields.iter().enumerate() {
            let field_type = field_types
                .get(index)
                .cloned()
                .flatten()
                .unwrap_or_else(InputType::untyped);
            let document = self.at(format!("{prefix}{field}"), |encoder| {
                encoder.encode(item, &field_type)
            })?;
            documents.push((field.to_string(), document));
        }
        let body = if tuple || documents.is_empty() {
            Json::Array(
                documents
                    .into_iter()
                    .map(|(_, document)| document)
                    .collect(),
            )
        } else {
            Json::Object(documents.into_iter().collect())
        };
        let form = tagged(&name, body);
        Ok(if function {
            tagged("$call", form)
        } else if tag_ctor {
            tagged("$ctor", form)
        } else {
            form
        })
    }
}

/// How a constructor application is written at a position: its shortest name there, and its
/// form, which a field's position names ([`CtorForm::prefix`]).
struct CtorForm {
    name: String,
    /// The application of a function, written `$call`.
    function: bool,
    /// The tagged constructor form `$ctor`, where the plain form has another reading.
    tagged: bool,
}

impl CtorForm {
    /// The position of the form's fields, before a field's name: `.Name.`, `$ctor(Name).` or
    /// `$call(Name).`, as the decoder spells it.
    fn prefix(&self) -> String {
        let name = &self.name;
        if self.function {
            format!("$call({name}).")
        } else if self.tagged {
            format!("$ctor({name}).")
        } else {
            format!(".{name}.")
        }
    }
}

/// The position of the field at `position` of the constructor application `value` at the
/// position `ty`, relative to the value, as the encoder and the decoder spell it (`.Idles.count`,
/// `$ctor(Pair).a`, `$call(Boot).n`); `None` where `value` is no constructor application with
/// that field, or whose application has no document at `ty`: parametric, of a sort not at most
/// `ty`'s, or with no name there.
pub(crate) fn field_position(
    values: &ValueIndex,
    value: &Value,
    ty: &InputType,
    position: usize,
) -> Option<String> {
    let Value::Ctor(ctor) = value else {
        return None;
    };
    // A parametric constructor's application has no form ([`Encoder::encode`]).
    if !ctor.sort_args().is_empty() {
        return None;
    }
    let (field, _) = ctor.fields().get(position)?;
    let encoder = Encoder {
        values,
        path: Vec::new(),
        inherent: None,
    };
    encoder.check_sort(value, ty).ok()?;
    let form = encoder.ctor_form(ctor, ty).ok()?;
    Some(format!("{}{field}", form.prefix()))
}

/// The shortest `::`-aligned suffix of `path` that `selects`, the whole path last.
fn shortest_suffix(path: &str, selects: impl Fn(&str) -> bool) -> Option<String> {
    let segments = path.split("::").collect::<Vec<_>>();
    (1..=segments.len())
        .map(|count| segments[segments.len() - count..].join("::"))
        .find(|name| selects(name))
}

#[cfg(test)]
mod tests {
    use super::{canonical_text, decode, encode, float_literal};
    use crate::inputs::InputType;
    use crate::values::{Float, Value, map_sort_index, token_sort_index};
    use serde_json::json;

    /// A sort `T` with one nullary constructor, `named`.
    const TOKEN_SORT: &str = r"[]
        module MAIN
            sort SortT{} []
            symbol named{}() : SortT{} [constructor{}(), functional{}(), injective{}()]
        endmodule []";

    #[test]
    fn a_shorthand_with_a_second_reading_is_written_in_its_tagged_form() {
        // `t::T` is a token sort and the result sort of the constructor `t::S::Named`, so at
        // `T` the bare string "Named" reads as a token and as the constructor.
        let (index, sort) = token_sort_index(TOKEN_SORT, &[("named", "Named", &[][..])]);
        let ty = InputType::of(sort.clone());
        let token = |text: &str| Value::Token {
            sort: sort.clone(),
            text: text.to_owned(),
        };
        let named = index.ctor("Named", []).unwrap();
        assert!(decode(&index, &json!("Named"), &ty).is_err());
        for (value, document) in [
            (token("other"), json!("other")),
            (token("Named"), json!({"$token": "Named"})),
            (named, json!({"Named": []})),
        ] {
            assert_eq!(
                encode(&index, &value, &ty),
                Ok(document.clone()),
                "{value:?}"
            );
            assert_eq!(decode(&index, &document, &ty), Ok(value), "{document}");
        }
    }

    /// A sort `T` that `Map` is at most, with a nullary constructor `named` and a binary one
    /// `pair`.
    const MAP_SORT: &str = r"[]
        module MAIN
            sort SortT{} []
            sort SortMap{} []
            sort SortInt{} []
            symbol inj{From, To}(From) : To [sortInjection{}()]
            symbol named{}() : SortT{} [constructor{}(), functional{}(), injective{}()]
            symbol pair{}(SortInt{}, SortInt{}) : SortT{} [constructor{}(), functional{}(), injective{}()]
            axiom{R} \exists{R}(V:SortT{}, \equals{SortT{}, R}(V:SortT{}, inj{SortMap{}, SortT{}}(From:SortMap{}))) [subsort{SortMap{}, SortT{}}()]
        endmodule []";

    #[test]
    fn a_constructor_whose_object_form_also_reads_as_a_map_is_written_in_its_tagged_form() {
        // At `T`, which `Map` is at most, an object is also a map's object shorthand, so the
        // constructor form reads two ways and the tagged form `$ctor` states the constructor.
        let (index, sort) = map_sort_index(
            MAP_SORT,
            &[
                ("named", "Named", &[][..]),
                ("pair", "Pair", &["a", "b"][..]),
            ],
        );
        let ty = InputType::of(sort);
        let named = index.ctor("Named", []).unwrap();
        let pair = index
            .ctor(
                "Pair",
                [("a", Value::Int(1.into())), ("b", Value::Int(2.into()))],
            )
            .unwrap();
        let ambiguous = decode(&index, &json!({"Pair": {"a": 1, "b": 2}}), &ty).unwrap_err();
        assert!(
            ambiguous
                .message
                .contains(r#"{"$ctor": {"t::S::Pair": ..}}"#),
            "{ambiguous}"
        );
        for (value, document) in [
            // The bare name has one reading at `T`: neither `String` nor a token sort is at
            // most it.
            (named.clone(), json!("Named")),
            (pair.clone(), json!({"$ctor": {"Pair": {"a": 1, "b": 2}}})),
        ] {
            assert_eq!(
                encode(&index, &value, &ty),
                Ok(document.clone()),
                "{value:?}"
            );
            assert_eq!(decode(&index, &document, &ty), Ok(value), "{document}");
        }
        // `$ctor` means the same at every position; untyped, the constructor form is written.
        let untyped = InputType::untyped();
        assert_eq!(
            encode(&index, &pair, &untyped),
            Ok(json!({"Pair": {"a": 1, "b": 2}}))
        );
        for document in [
            json!({"$ctor": {"Pair": [1, 2]}}),
            json!({"$ctor": {"t::S::Pair": {"b": 2, "a": 1}}}),
        ] {
            assert_eq!(decode(&index, &document, &untyped), Ok(pair.clone()));
            assert_eq!(decode(&index, &document, &ty), Ok(pair.clone()));
        }
        assert_eq!(
            decode(&index, &json!({"$ctor": {"Named": []}}), &ty),
            Ok(named)
        );
        // A field's position names the tagged form it lies in.
        let field =
            decode(&index, &json!({"$ctor": {"Pair": {"a": "x", "b": 2}}}), &ty).unwrap_err();
        assert_eq!(field.position, "$ctor(Pair).a", "{field}");
        for (document, message) in [
            (
                json!({"$ctor": "Pair"}),
                r#"`$ctor` takes {"path::C": fields}"#,
            ),
            (
                json!({"$ctor": {"Pair": [1, 2], "Named": []}}),
                "one constructor",
            ),
            (json!({"$ctor": {"Other": []}}), "Other"),
        ] {
            let refusal = decode(&index, &document, &ty).unwrap_err();
            assert!(refusal.message.contains(message), "{document}: {refusal}");
        }
    }

    #[test]
    fn canonical_text_orders_members_by_key_bytes_and_writes_compact_json() {
        let document = json!({"b": [1, {"z": null, "a": true}], "a": "x\"\\\n\u{1}é", "B": -3});
        assert_eq!(
            canonical_text(&document),
            r#"{"B":-3,"a":"x\"\\\n\u0001é","b":[1,{"a":true,"z":null}]}"#
        );
        // The text a JSON reader reads back is the document.
        assert_eq!(
            serde_json::from_str::<serde_json::Value>(&canonical_text(&document)).unwrap(),
            document
        );
    }

    #[test]
    fn a_float_is_its_shortest_literal_that_reads_back() {
        for (value, literal) in [
            (1.5, "1.5e0"),
            (1.0, "1.0e0"),
            (1e300, "1.0e300"),
            (5e-324, "5.0e-324"),
            (-0.0, "-0.0e0"),
            (0.1, "1.0e-1"),
            (f64::NAN, "NaN"),
            (f64::INFINITY, "Infinity"),
            (f64::NEG_INFINITY, "-Infinity"),
        ] {
            let float = Float::from_f64(value);
            assert_eq!(float_literal(&float), literal, "{value}");
            assert_eq!(Float::parse(literal).unwrap(), float, "{literal}");
        }
        let single = Float::from_f32(1.5);
        assert_eq!(float_literal(&single), "1.5e0f");
        assert_eq!(Float::parse("1.5e0f").unwrap(), single);
        assert_eq!(float_literal(&Float::from_f32(f32::NAN)), "NaNf");
        // Another format is written as its canonical literal.
        let other = Float::parse("1.0p11x5").unwrap();
        assert_eq!(float_literal(&other), other.literal());
    }
}
