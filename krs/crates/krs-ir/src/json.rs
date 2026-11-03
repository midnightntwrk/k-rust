//! The canonical JSON encoding of KRS's serialized documents, and bounded JSON decoding for
//! recursive descriptor and Definition IR terms.

use serde::Serialize;
use serde::de::DeserializeOwned;
use std::io;
#[cfg(not(target_family = "wasm"))]
use std::thread;

/// Maximum structural JSON nesting accepted by KRS IR readers.
///
/// A term nested 256 constructors deep uses 778 JSON containers in the
/// descriptor protocol. This bound permits that case while keeping recursive
/// Serde deserialization within a finite stack budget.
pub const MAX_IR_JSON_DEPTH: usize = 1024;

/// Writes `value`'s canonical JSON encoding to `writer`: pretty JSON with one trailing newline.
///
/// This is the one definition of the encoding; [`to_canonical_string`] is it collected in
/// memory, so a digest computed by streaming into a hasher is the digest of the canonical bytes.
///
/// # Errors
///
/// Returns an error if `value` cannot be encoded (a map key that is not a string, or a
/// serializer that fails) or `writer` fails.
pub fn write_canonical<W: io::Write, T: Serialize + ?Sized>(
    mut writer: W,
    value: &T,
) -> serde_json::Result<()> {
    serde_json::to_writer_pretty(&mut writer, value)?;
    writer.write_all(b"\n").map_err(serde_json::Error::io)
}

/// Returns `value`'s canonical JSON encoding ([`write_canonical`]) as a string.
///
/// # Errors
///
/// Returns an error if `value` cannot be encoded.
pub fn to_canonical_string<T: Serialize + ?Sized>(value: &T) -> serde_json::Result<String> {
    let mut bytes = Vec::new();
    write_canonical(&mut bytes, value)?;
    // serde_json writes UTF-8 only, so this never fails.
    String::from_utf8(bytes)
        .map_err(|error| serde_json::Error::io(io::Error::new(io::ErrorKind::InvalidData, error)))
}

/// Decode IR JSON beyond `serde_json`'s default depth limit.
///
/// # Errors
///
/// Returns a JSON error if the input is malformed, exceeds the supported
/// nesting depth, or fails validation by the requested IR type.
pub fn from_slice<T: DeserializeOwned + Send>(bytes: &[u8]) -> serde_json::Result<T> {
    check_depth(bytes)?;
    // WASI does not provide the threads needed for a larger decode stack.
    #[cfg(target_family = "wasm")]
    {
        decode_unbounded(bytes)
    }
    #[cfg(not(target_family = "wasm"))]
    thread::scope(|scope| {
        thread::Builder::new()
            .name("krs-ir-json-decode".to_owned())
            .stack_size(64 * 1024 * 1024)
            .spawn_scoped(scope, || decode_unbounded(bytes))
            .map_err(serde_json::Error::io)?
            .join()
            .map_err(|_| {
                serde_json::Error::io(io::Error::other("IR JSON decode thread panicked"))
            })?
    })
}

fn decode_unbounded<T: DeserializeOwned>(bytes: &[u8]) -> serde_json::Result<T> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    deserializer.disable_recursion_limit();
    let value = T::deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

fn check_depth(bytes: &[u8]) -> serde_json::Result<()> {
    let mut depth = 0usize;
    let mut quoted = false;
    let mut escaped = false;
    for &byte in bytes {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    depth += 1;
                    if depth > MAX_IR_JSON_DEPTH {
                        return Err(serde_json::Error::io(io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!("IR JSON nesting exceeds {MAX_IR_JSON_DEPTH} containers"),
                        )));
                    }
                }
                b'}' | b']' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{MAX_IR_JSON_DEPTH, from_slice, to_canonical_string, write_canonical};

    #[test]
    fn canonical_encoding_is_pretty_json_with_one_trailing_newline() {
        let value = serde_json::json!({ "b": [1, { "c": null }], "a": "x" });
        let mut streamed = Vec::new();
        write_canonical(&mut streamed, &value).unwrap();
        let text = to_canonical_string(&value).unwrap();
        assert_eq!(text.as_bytes(), streamed);
        assert_eq!(
            text,
            format!("{}\n", serde_json::to_string_pretty(&value).unwrap())
        );
    }

    #[test]
    fn decodes_deep_json_and_bounds_stack_depth() {
        let deep = format!("{}0{}", "[".repeat(256), "]".repeat(256));
        let value: serde_json::Value = from_slice(deep.as_bytes()).unwrap();
        let mut cursor = &value;
        for _ in 0..256 {
            cursor = &cursor[0];
        }
        assert_eq!(cursor, &serde_json::json!(0));

        let too_deep = format!(
            "{}0{}",
            "[".repeat(MAX_IR_JSON_DEPTH + 1),
            "]".repeat(MAX_IR_JSON_DEPTH + 1)
        );
        let error = from_slice::<serde_json::Value>(too_deep.as_bytes()).unwrap_err();
        assert!(error.to_string().contains("IR JSON nesting exceeds 1024"));
    }

    #[test]
    fn quoted_brackets_do_not_count_as_nesting() {
        let value: String = from_slice(br#""\\\"[[{{[[""#).unwrap();
        assert_eq!(value, "\\\"[[{{[[");
    }
}
