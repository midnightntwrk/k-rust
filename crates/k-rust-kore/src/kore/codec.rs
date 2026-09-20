//! Detection and decoding of the three KORE pattern encodings. JSON conversion in both
//! directions uses the crate's depth-unbounded tree codec.

use std::{error::Error, fmt, str::Utf8Error};

use super::{ast::Pattern, binary, json, parser};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Encoding {
    Binary,
    Json,
    Text,
}

impl fmt::Display for Encoding {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Binary => "binary",
            Self::Json => "JSON",
            Self::Text => "text",
        })
    }
}

#[derive(Debug)]
pub struct DecodeError {
    pub encoding: Encoding,
    pub cause: Box<dyn Error + Send + Sync>,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} KORE: {}", self.encoding, self.cause)
    }
}

impl Error for DecodeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.cause.as_ref())
    }
}

pub fn sniff(input: &[u8]) -> Result<Encoding, Utf8Error> {
    if input.starts_with(b"\x7fKORE") {
        return Ok(Encoding::Binary);
    }
    let text = std::str::from_utf8(input)?;
    Ok(if text.trim_start().starts_with('{') {
        Encoding::Json
    } else {
        Encoding::Text
    })
}

pub fn decode_bytes(input: &[u8]) -> Result<Pattern, DecodeError> {
    let encoding = sniff(input).map_err(|error| DecodeError {
        encoding: Encoding::Text,
        cause: Box::new(error),
    })?;
    match encoding {
        Encoding::Binary => binary::decode_term(input).map_err(|error| DecodeError {
            encoding,
            cause: Box::new(error),
        }),
        Encoding::Json => json::from_str(std::str::from_utf8(input).expect("sniff checked UTF-8"))
            .map_err(|error| DecodeError {
                encoding,
                cause: Box::new(error),
            }),
        Encoding::Text => parser::parse_pattern(
            std::str::from_utf8(input).expect("sniff checked UTF-8"),
        )
        .map_err(|error| DecodeError {
            encoding,
            cause: Box::new(error),
        }),
    }
}

pub fn from_value(value: &serde_json::Value) -> Result<Pattern, json::Error> {
    json::from_str(&value.to_string())
}

pub use super::json::to_value;
