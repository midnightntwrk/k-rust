use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use sha2::{Digest as _, Sha256};
use std::collections::BTreeMap;
use std::fmt;
use unicode_normalization::is_nfc;

/// The exact portable JSON value domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SemanticJson {
    /// JSON null.
    Null,
    /// JSON boolean.
    Bool(bool),
    /// Signed 64-bit integer.
    Integer(i64),
    /// Unicode NFC string.
    String(String),
    /// Ordered array.
    Array(Vec<Self>),
    /// String-keyed object in Unicode code-point key order.
    Object(BTreeMap<String, Self>),
}

impl SemanticJson {
    /// Validates an in-memory value against the exact portable JSON domain.
    ///
    /// Text parsing already establishes this invariant. This check is also
    /// required for values assembled through the public enum variants, so an
    /// invalid string or object key can never reach encoding or hashing.
    pub fn validate(&self) -> Result<(), JsonFailure> {
        validate_at(self, "$".to_owned())
    }

    /// Constructs a validated semantic string.
    pub fn string(value: impl Into<String>) -> Result<Self, JsonFailure> {
        let value = Self::String(value.into());
        value.validate()?;
        Ok(value)
    }

    /// Constructs a validated semantic array.
    pub fn array(values: Vec<Self>) -> Result<Self, JsonFailure> {
        let value = Self::Array(values);
        value.validate()?;
        Ok(value)
    }

    /// Constructs a validated semantic object.
    pub fn object(values: BTreeMap<String, Self>) -> Result<Self, JsonFailure> {
        let value = Self::Object(values);
        value.validate()?;
        Ok(value)
    }

    /// Returns this value as an object.
    #[must_use]
    pub fn as_object(&self) -> Option<&BTreeMap<String, Self>> {
        match self {
            Self::Object(value) => Some(value),
            _ => None,
        }
    }

    /// Returns this value as an array.
    #[must_use]
    pub fn as_array(&self) -> Option<&[Self]> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }

    /// Returns this value as a string.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    /// Returns this value as a signed integer.
    #[must_use]
    pub const fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns this value as a boolean.
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    /// Converts into `serde_json::Value` after portable validation.
    pub fn to_serde_value(&self) -> Result<serde_json::Value, JsonFailure> {
        self.validate()?;
        Ok(self.to_serde_value_validated())
    }

    fn to_serde_value_validated(&self) -> serde_json::Value {
        match self {
            Self::Null => serde_json::Value::Null,
            Self::Bool(value) => serde_json::Value::Bool(*value),
            Self::Integer(value) => serde_json::Value::Number((*value).into()),
            Self::String(value) => serde_json::Value::String(value.clone()),
            Self::Array(values) => serde_json::Value::Array(
                values.iter().map(Self::to_serde_value_validated).collect(),
            ),
            Self::Object(values) => serde_json::Value::Object(
                values
                    .iter()
                    .map(|(key, value)| (key.clone(), value.to_serde_value_validated()))
                    .collect(),
            ),
        }
    }
}

const ERROR_MARKER: &str = "KINK_JSON:";

impl<'de> Deserialize<'de> for SemanticJson {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SemanticVisitor;

        impl<'de> Visitor<'de> for SemanticVisitor {
            type Value = SemanticJson;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a restricted portable JSON value")
            }

            fn visit_unit<E>(self) -> Result<Self::Value, E> {
                Ok(SemanticJson::Null)
            }

            fn visit_none<E>(self) -> Result<Self::Value, E> {
                Ok(SemanticJson::Null)
            }

            fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
                Ok(SemanticJson::Bool(value))
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
                Ok(SemanticJson::Integer(value))
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                i64::try_from(value)
                    .map(SemanticJson::Integer)
                    .map_err(|_| E::custom(format!("{ERROR_MARKER}integer-out-of-range")))
            }

            fn visit_f64<E>(self, _value: f64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Err(E::custom(format!("{ERROR_MARKER}floating-point-forbidden")))
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                self.visit_string(value.to_owned())
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if !is_nfc(&value) {
                    return Err(E::custom(format!("{ERROR_MARKER}non-nfc-string")));
                }
                Ok(SemanticJson::String(value))
            }

            fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = Vec::new();
                while let Some(value) = sequence.next_element::<SemanticJson>()? {
                    values.push(value);
                }
                Ok(SemanticJson::Array(values))
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = BTreeMap::new();
                while let Some(key) = map.next_key::<String>()? {
                    if !is_nfc(&key) {
                        return Err(de::Error::custom(format!("{ERROR_MARKER}non-nfc-string")));
                    }
                    if values.contains_key(&key) {
                        return Err(de::Error::custom(format!(
                            "{ERROR_MARKER}duplicate-object-key"
                        )));
                    }
                    let value = map.next_value::<SemanticJson>()?;
                    values.insert(key, value);
                }
                Ok(SemanticJson::Object(values))
            }
        }

        deserializer.deserialize_any(SemanticVisitor)
    }
}

/// Closed restricted-JSON failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsonFailureKind {
    /// The byte stream is not UTF-8 JSON.
    Syntax,
    /// The stream contains bytes after the first JSON value.
    TrailingData,
    /// An object repeats a key.
    DuplicateObjectKey,
    /// Floating point is outside the portable domain.
    FloatingPointForbidden,
    /// An integer does not fit signed 64-bit.
    IntegerOutOfRange,
    /// A string or key is not NFC.
    NonNfcString,
    /// A string contains a non-scalar surrogate encoding.
    SurrogateCodePoint,
    /// A host value is outside the exact portable domain.
    UnsupportedJsonType,
    /// An in-memory object key is not a string.
    NonStringObjectKey,
    /// An in-memory value is cyclic.
    CyclicJsonValue,
}

/// A typed JSON failure with a deterministic structural location when known.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsonFailure {
    kind: JsonFailureKind,
    location: String,
    detail: String,
}

impl JsonFailure {
    fn new(kind: JsonFailureKind, location: String, detail: impl Into<String>) -> Self {
        Self {
            kind,
            location,
            detail: detail.into(),
        }
    }

    fn from_serde(error: serde_json::Error) -> Self {
        let text = error.to_string();
        let kind = if text.contains("duplicate-object-key") {
            JsonFailureKind::DuplicateObjectKey
        } else if text.contains("floating-point-forbidden") {
            JsonFailureKind::FloatingPointForbidden
        } else if text.contains("integer-out-of-range") {
            JsonFailureKind::IntegerOutOfRange
        } else if text.contains("non-nfc-string") {
            JsonFailureKind::NonNfcString
        } else if text.contains("surrogate") {
            JsonFailureKind::SurrogateCodePoint
        } else if text.contains("trailing characters") {
            JsonFailureKind::TrailingData
        } else {
            JsonFailureKind::Syntax
        };
        Self {
            kind,
            location: "$".to_owned(),
            detail: text,
        }
    }

    /// Returns the decision-bearing reason.
    #[must_use]
    pub const fn kind(&self) -> JsonFailureKind {
        self.kind
    }

    /// Returns the deterministic structural location.
    #[must_use]
    pub fn location(&self) -> &str {
        &self.location
    }
}

impl fmt::Display for JsonFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{:?} at {}: {}",
            self.kind, self.location, self.detail
        )
    }
}

impl std::error::Error for JsonFailure {}

/// Parses exactly one restricted portable JSON value.
pub fn parse_json(bytes: &[u8]) -> Result<SemanticJson, JsonFailure> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    let value = SemanticJson::deserialize(&mut deserializer).map_err(JsonFailure::from_serde)?;
    deserializer.end().map_err(JsonFailure::from_serde)?;
    Ok(value)
}

fn validate_at(value: &SemanticJson, location: String) -> Result<(), JsonFailure> {
    match value {
        SemanticJson::Null | SemanticJson::Bool(_) | SemanticJson::Integer(_) => Ok(()),
        SemanticJson::String(value) => {
            if is_nfc(value) {
                Ok(())
            } else {
                Err(JsonFailure::new(
                    JsonFailureKind::NonNfcString,
                    location,
                    "in-memory string is not Unicode NFC",
                ))
            }
        }
        SemanticJson::Array(values) => {
            for (index, value) in values.iter().enumerate() {
                validate_at(value, format!("{location}[{index}]"))?;
            }
            Ok(())
        }
        SemanticJson::Object(values) => {
            for (key, value) in values {
                let key_location = format!("{location}[{}]", quoted_location_key(key));
                if !is_nfc(key) {
                    return Err(JsonFailure::new(
                        JsonFailureKind::NonNfcString,
                        key_location,
                        "in-memory object key is not Unicode NFC",
                    ));
                }
                validate_at(value, key_location)?;
            }
            Ok(())
        }
    }
}

fn quoted_location_key(value: &str) -> String {
    let mut encoded = String::new();
    write_string(value, &mut encoded);
    encoded
}

/// Returns the exact compact canonical JSON string.
pub fn canonical_json(value: &SemanticJson) -> Result<String, JsonFailure> {
    value.validate()?;
    let mut output = String::new();
    write_canonical(value, &mut output);
    Ok(output)
}

/// Returns the exact UTF-8 canonical JSON bytes.
pub fn canonical_json_bytes(value: &SemanticJson) -> Result<Vec<u8>, JsonFailure> {
    canonical_json(value).map(String::into_bytes)
}

fn write_canonical(value: &SemanticJson, output: &mut String) {
    match value {
        SemanticJson::Null => output.push_str("null"),
        SemanticJson::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
        SemanticJson::Integer(value) => output.push_str(&value.to_string()),
        SemanticJson::String(value) => write_string(value, output),
        SemanticJson::Array(values) => {
            output.push('[');
            for (index, value) in values.iter().enumerate() {
                if index != 0 {
                    output.push(',');
                }
                write_canonical(value, output);
            }
            output.push(']');
        }
        SemanticJson::Object(values) => {
            output.push('{');
            for (index, (key, value)) in values.iter().enumerate() {
                if index != 0 {
                    output.push(',');
                }
                write_string(key, output);
                output.push(':');
                write_canonical(value, output);
            }
            output.push('}');
        }
    }
}

fn write_string(value: &str, output: &mut String) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{0008}' => output.push_str("\\b"),
            '\t' => output.push_str("\\t"),
            '\n' => output.push_str("\\n"),
            '\u{000c}' => output.push_str("\\f"),
            '\r' => output.push_str("\\r"),
            '\u{0000}'..='\u{001f}' => {
                use fmt::Write as _;
                write!(output, "\\u{:04x}", u32::from(character))
                    .expect("writing to String cannot fail");
            }
            _ => output.push(character),
        }
    }
    output.push('"');
}

/// Lowercase SHA-256 over exact bytes.
#[must_use]
pub fn sha256_bytes(bytes: &[u8]) -> Digest {
    let result = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(64);
    for byte in result {
        use fmt::Write as _;
        write!(&mut encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    Digest(encoded)
}

/// A lowercase SHA-256 value.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Digest(String);

impl Digest {
    /// Validates the frozen lowercase representation.
    pub fn parse(value: &str) -> Result<Self, IdentityDigestError> {
        if value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            Ok(Self(value.to_owned()))
        } else {
            Err(IdentityDigestError::DigestSyntax)
        }
    }

    /// Returns the lowercase representation.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

/// A validated ASCII digest domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DigestDomain(String);

impl DigestDomain {
    /// Validates a nonempty printable-ASCII versioned domain.
    pub fn new(value: impl Into<String>) -> Result<Self, IdentityDigestError> {
        let value = value.into();
        if value.is_empty()
            || !value.is_ascii()
            || value.bytes().any(|byte| !(0x21..=0x7e).contains(&byte))
            || !value.contains("/v")
        {
            return Err(IdentityDigestError::DomainSyntax);
        }
        Ok(Self(value))
    }

    /// Returns the frozen domain spelling.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Digest-construction failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityDigestError {
    /// Digest text is not exactly lowercase SHA-256.
    DigestSyntax,
    /// The domain is not a printable ASCII versioned domain.
    DomainSyntax,
    /// A requested self-ID field is absent or not an object field.
    SelfIdProjection,
    /// The input is not a valid in-memory portable JSON value.
    InvalidSemanticJson,
}

impl fmt::Display for IdentityDigestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for IdentityDigestError {}

/// Computes `SHA256(UTF8(domain) || 0x00 || canonical-json(value))`.
pub fn digest(domain: &DigestDomain, value: &SemanticJson) -> Result<Digest, JsonFailure> {
    let canonical = canonical_json_bytes(value)?;
    let mut hasher = Sha256::new();
    hasher.update(domain.as_str().as_bytes());
    hasher.update([0]);
    hasher.update(canonical);
    let result = hasher.finalize();
    let mut encoded = String::with_capacity(64);
    for byte in result {
        use fmt::Write as _;
        write!(&mut encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    Ok(Digest(encoded))
}

/// Computes a self-ID after removing exactly one declared field.
pub fn digest_without_field(
    domain: &DigestDomain,
    value: &SemanticJson,
    field: &str,
) -> Result<Digest, IdentityDigestError> {
    value
        .validate()
        .map_err(|_| IdentityDigestError::InvalidSemanticJson)?;
    let SemanticJson::Object(fields) = value else {
        return Err(IdentityDigestError::SelfIdProjection);
    };
    if !fields.contains_key(field) {
        return Err(IdentityDigestError::SelfIdProjection);
    }
    let mut projection = fields.clone();
    projection.remove(field);
    digest(domain, &SemanticJson::Object(projection))
        .map_err(|_| IdentityDigestError::InvalidSemanticJson)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn domain() -> DigestDomain {
        DigestDomain::new("k-in-k/conformance-example/v1").expect("static domain is valid")
    }

    #[test]
    fn canonical_encoding_matches_frozen_profile() {
        let value = parse_json(br#"{"z":3,"a":1,"nested":{"b":true,"a":null}}"#)
            .expect("fixture JSON is valid");
        assert_eq!(
            canonical_json(&value).expect("parsed JSON is valid"),
            r#"{"a":1,"nested":{"a":null,"b":true},"z":3}"#
        );
        assert_eq!(
            digest(&domain(), &value)
                .expect("parsed JSON is valid")
                .as_str(),
            "db8088b7acdde2ae3335ca8e659dc29a1d7e36cb9b9084421b7e47f5fbd581b4"
        );
    }

    #[test]
    fn rejects_every_textual_domain_adversary() {
        let cases = [
            (
                br#"{"same":1,"same":2}"#.as_slice(),
                JsonFailureKind::DuplicateObjectKey,
            ),
            (
                br#"1.0"#.as_slice(),
                JsonFailureKind::FloatingPointForbidden,
            ),
            (
                br#"9223372036854775808"#.as_slice(),
                JsonFailureKind::IntegerOutOfRange,
            ),
            (b"1 true".as_slice(), JsonFailureKind::TrailingData),
            (b"\"e\xcc\x81\"".as_slice(), JsonFailureKind::NonNfcString),
        ];
        for (bytes, expected) in cases {
            assert_eq!(parse_json(bytes).expect_err("must reject").kind(), expected);
        }
    }

    #[test]
    fn uses_short_control_escapes_and_direct_utf8() {
        let value = parse_json("{\"日本語\":\"é\",\"c\":\"\\b\\t\\n\\f\\r\\u0001\"}".as_bytes())
            .expect("fixture JSON is valid");
        assert_eq!(
            canonical_json(&value).expect("parsed JSON is valid"),
            "{\"c\":\"\\b\\t\\n\\f\\r\\u0001\",\"日本語\":\"é\"}"
        );
    }

    #[test]
    fn rejects_invalid_in_memory_values_before_encoding_or_hashing() {
        let decomposed = "e\u{301}".to_owned();
        let nested = SemanticJson::Array(vec![SemanticJson::String(decomposed.clone())]);
        let error = canonical_json(&nested).expect_err("non-NFC value must not encode");
        assert_eq!(error.kind(), JsonFailureKind::NonNfcString);
        assert_eq!(error.location(), "$[0]");
        assert_eq!(
            digest(&domain(), &nested)
                .expect_err("non-NFC value must not hash")
                .kind(),
            JsonFailureKind::NonNfcString
        );

        let object = SemanticJson::Object(BTreeMap::from([(decomposed, SemanticJson::Integer(1))]));
        let error = canonical_json_bytes(&object).expect_err("non-NFC key must not encode");
        assert_eq!(error.kind(), JsonFailureKind::NonNfcString);
        assert_eq!(error.location(), "$[\"é\"]");
        assert_eq!(
            SemanticJson::object(BTreeMap::from([(
                "e\u{301}".to_owned(),
                SemanticJson::Null,
            )]))
            .expect_err("checked construction must reject")
            .kind(),
            JsonFailureKind::NonNfcString
        );

        let self_identified = SemanticJson::Object(BTreeMap::from([
            ("id".to_owned(), SemanticJson::String("0".repeat(64))),
            (
                "value".to_owned(),
                SemanticJson::String("e\u{301}".to_owned()),
            ),
        ]));
        assert_eq!(
            digest_without_field(&domain(), &self_identified, "id")
                .expect_err("self-ID hashing must validate before projection"),
            IdentityDigestError::InvalidSemanticJson
        );
        assert_eq!(
            self_identified
                .to_serde_value()
                .expect_err("serde conversion must preserve the boundary")
                .kind(),
            JsonFailureKind::NonNfcString
        );
    }
}
