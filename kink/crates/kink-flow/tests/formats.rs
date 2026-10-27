//! fz26 FZ-REPLAY-WHOLE (final review S2): the `kink-flow fuzz` document's version is tied to its
//! format, as k-rust-fuzz's `tests/formats.rs` ties the report's and the witness's versions to
//! theirs.
//!
//! The document is built as JSON values in `src/fuzz.rs`, not from types, so its shape is read
//! from that source's JSON literals: every object key a `json!` literal writes (`"stopped":`),
//! every key the code sets or reads by index (`document["stopped"]`), and every string the code
//! writes as a whole value (`json!("client-refused")`, `"kind": "reach"`), comments left out. A key, a `stopped`
//! value, a warning kind or a refusal reason added, renamed or removed moves it; a message's
//! wording does not. The document embeds a k-rust-fuzz report, so the pin also names the
//! report version it embeds. A shape or report version that changes without a bump of
//! [`FUZZ_VERSION`] fails here until the version is bumped and the digest re-pinned (a literal
//! that changes without changing the document, such as a key read and never written, is
//! re-pinned under the same version, with the reason beside the pin).
//!
//! Not read: keys and values another module of kink-flow builds (the admission's and kink's
//! confirmation documents, whose own schemas carry them). `KINK_FLOW_FORMATS_PRINT=1` prints
//! the digest and the literals.

use std::collections::BTreeSet;

use k_rust_fuzz::report::{REPORT_VERSION, digest_hex};
use kink_flow::fuzz::FUZZ_VERSION;

/// The document's shape at [`FUZZ_VERSION`] 4 (fz26 FZ-REPLAY-WHOLE: it embeds report version
/// 10), with the report version it embeds.
const DOCUMENT_SHAPE: (u32, u32, &str) = (
    4,
    10,
    "8ad12634d62d4f03d4c1867ccc255d247c6c9b24ce887da48c47fe58047f922e",
);

/// `source` without `//` comments, string literals kept whole.
fn without_comments(source: &str) -> String {
    let mut out = String::new();
    for line in source.lines() {
        let mut in_string = false;
        let mut escaped = false;
        let mut previous = None;
        let mut cut = line.len();
        for (index, character) in line.char_indices() {
            if in_string {
                if escaped {
                    escaped = false;
                } else if character == '\\' {
                    escaped = true;
                } else if character == '"' {
                    in_string = false;
                }
            } else if character == '"' && previous != Some('\'') {
                in_string = true;
            } else if character == '/' && previous == Some('/') {
                cut = index - 1;
                break;
            }
            previous = Some(character);
        }
        out.push_str(&line[..cut]);
        out.push('\n');
    }
    out
}

/// Whether `text` reads as a key or a value of the document: lowercase ASCII words joined by
/// `-` or `_`, as every key and enumerated value of it is.
fn is_token(text: &str) -> bool {
    !text.is_empty()
        && text.starts_with(|c: char| c.is_ascii_lowercase())
        && text
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' || c == '_')
}

/// The document's literals in `source`: `key:` for an object key or an index, `=value` for a
/// whole string value.
fn literals(source: &str) -> BTreeSet<String> {
    let source = without_comments(source);
    let mut found = BTreeSet::new();
    let bytes = source.as_bytes();
    let mut index = 0;
    while let Some(start) = source[index..].find('"').map(|at| index + at) {
        // A quote character (`'"'`) opens no string.
        if start > 0 && bytes[start - 1] == b'\'' && bytes.get(start + 1) == Some(&b'\'') {
            index = start + 1;
            continue;
        }
        let Some(length) = source[start + 1..].find('"') else {
            break;
        };
        let end = start + 1 + length;
        let text = &source[start + 1..end];
        let before = source[..start].trim_end();
        let after = source[end + 1..].trim_start();
        if is_token(text) {
            if (after.starts_with(':') && !after.starts_with("::"))
                || (before.ends_with('[') && after.starts_with(']'))
            {
                found.insert(format!("{text}:"));
            } else if (before.ends_with("json!(") && after.starts_with(')'))
                || (before.ends_with(':') && !before.ends_with("::"))
            {
                found.insert(format!("={text}"));
            }
        }
        // Past the literal, its escapes included.
        let mut cursor = start + 1;
        while cursor < bytes.len() && bytes[cursor] != b'"' {
            if bytes[cursor] == b'\\' {
                cursor += 1;
            }
            cursor += 1;
        }
        index = cursor + 1;
    }
    found
}

#[test]
fn the_fuzz_document_version_names_its_shape() {
    let source = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/fuzz.rs"))
        .expect("src/fuzz.rs reads");
    let found = literals(&source);
    for literal in [
        "stopped:",
        "attempts:",
        "=client-refused",
        "=budget",
        "action:",
    ] {
        assert!(found.contains(literal), "{literal}: {found:?}");
    }
    let digest = digest_hex(
        found
            .iter()
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
            .as_bytes(),
    );
    if std::env::var_os("KINK_FLOW_FORMATS_PRINT").is_some() {
        println!("document shape at version {FUZZ_VERSION}: {digest}\n  {found:?}");
    }
    let (version, report, pinned) = DOCUMENT_SHAPE;
    assert_eq!(
        version, FUZZ_VERSION,
        "FUZZ_VERSION moved to {FUZZ_VERSION}: re-pin the document's shape for the new version"
    );
    assert_eq!(
        report, REPORT_VERSION,
        "the embedded k-rust-fuzz report moved to version {REPORT_VERSION}, which changes the \
         document: bump FUZZ_VERSION and re-pin"
    );
    assert_eq!(
        digest, pinned,
        "the document's shape changed without a FUZZ_VERSION bump: bump it and re-pin \
         ({FUZZ_VERSION}, {REPORT_VERSION}, \"{digest}\"), or, when the document is unchanged, \
         re-pin under the same version and say why"
    );
}

/// The reader takes keys, indexed keys and whole string values, and leaves messages and comments.
#[test]
fn the_shape_reader_takes_keys_and_values() {
    let found = literals(
        "let d = json!({\"stopped\": null, \"kind\": \"kill\", \"action\": format!(\"no witness: {x}\")});\n\
         d[\"job\"][\"kind\"] = json!(\"reach\"); // \"commented\": 1\n\
         let path = \"a::b\"; let s = json!(\"Not a token\");\n",
    );
    let expected: BTreeSet<String> = ["stopped:", "kind:", "=kill", "action:", "job:", "=reach"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    assert_eq!(found, expected);
}
