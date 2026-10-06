// A KORE string literal is a sequence of code points (`kore-syntax.md`): `\xhh` is U+00hh. A
// `KoreString` stores them in UTF-8, or one byte per code point for a `Bytes` domain value.

use k_rust::kore::ast::KoreString;
use k_rust::kore::string::{LiteralEncoding, quote, quote_as, unquote, unquote_as};

#[test]
fn unquotes_kore_escapes() {
    let cases = [
        ("\"\"", Vec::new()),
        (r#"" ""#, b" ".to_vec()),
        (r#""foo""#, b"foo".to_vec()),
        (r#""\t""#, b"\t".to_vec()),
        (r#""\n""#, b"\n".to_vec()),
        (r#""\f""#, vec![0x0c]),
        (r#""\r""#, b"\r".to_vec()),
        (r#""\\""#, b"\\".to_vec()),
        (r#""\"""#, b"\"".to_vec()),
        (r#""\x80""#, "\u{80}".as_bytes().to_vec()),
        (r#""\xe9""#, "é".as_bytes().to_vec()),
        (r#""\x0f""#, vec![0x0f]),
        (r#""\x0F""#, vec![0x0f]),
        (r#""\u03b1""#, "α".as_bytes().to_vec()),
        (r#""\u03B1""#, "α".as_bytes().to_vec()),
        (r#""\U0001f642""#, "🙂".as_bytes().to_vec()),
        (r#""\U0001F642""#, "🙂".as_bytes().to_vec()),
        (r#""\x80\x80""#, "\u{80}\u{80}".as_bytes().to_vec()),
        (r#""\xc3\xa9""#, "Ã©".as_bytes().to_vec()),
        (r#""\u00e9""#, "é".as_bytes().to_vec()),
        (
            r#""a\u03b1\x80\U0001f642b""#,
            "aα\u{80}🙂b".as_bytes().to_vec(),
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(
            unquote(input).unwrap().as_bytes(),
            expected,
            "input: {input}"
        );
    }
}

#[test]
fn quotes_using_the_canonical_kore_form() {
    let cases = [
        ("", "\"\""),
        ("plain ASCII", r#""plain ASCII""#),
        ("\"\\\n\r\t\u{c}", r#""\"\\\n\r\t\f""#),
        ("\u{0}\u{f}\u{80}\u{ff}", r#""\x00\x0f\x80\xff""#),
        ("é", r#""\xe9""#),
        ("α", r#""\u03b1""#),
        ("🙂", r#""\U0001f642""#),
    ];

    for (input, expected) in cases {
        assert_eq!(
            quote(&KoreString::from(input)),
            expected,
            "input: {input:?}"
        );
    }
}

#[test]
fn round_trips_unicode_scalar_values() {
    for codepoint in 0..=0x10ffff {
        let Some(character) = char::from_u32(codepoint) else {
            continue;
        };
        let value = character.to_string();
        let value = KoreString::from(value);
        assert_eq!(unquote(&quote(&value)).unwrap(), value);
    }
}

/// A `Bytes` literal stores one byte per code point, every byte and an embedded NUL included;
/// a code point above U+00FF names no byte.
#[test]
fn round_trips_every_byte_and_embedded_nul_of_a_bytes_literal() {
    let value = KoreString::from(vec![0xff, 0x80, 0x00, b'A']);
    let encoded = quote_as(&value, LiteralEncoding::Bytes);
    assert_eq!(encoded, r#""\xff\x80\x00A""#);
    assert_eq!(unquote_as(&encoded, LiteralEncoding::Bytes).unwrap(), value);
    assert_eq!(
        unquote_as(r#""\u00e9""#, LiteralEncoding::Bytes).unwrap(),
        KoreString::from(vec![0xe9])
    );
    for input in [r#""\u0100""#, r#""\U0001f642""#, "\"α\""] {
        assert!(
            unquote_as(input, LiteralEncoding::Bytes).is_err(),
            "expected {input:?} to fail"
        );
    }
}

/// A payload stored as UTF-8 that is not UTF-8 (built by hand, not by a reader) is written with
/// each stray byte as the code point of its value.
#[test]
fn quotes_a_stray_byte_as_its_code_point() {
    assert_eq!(
        quote(&KoreString::from(vec![0xff, b'A', 0xc3, 0xa9])),
        r#""\xffA\xe9""#
    );
}

#[test]
fn rejects_unknown_escapes() {
    for input in [r#""\q""#, r#""\0""#] {
        let error = unquote(input).expect_err("unknown escapes must be rejected");
        assert_eq!(error.offset, 1, "input: {input}");
        assert_eq!(error.message, "unknown escape", "input: {input}");
    }
}

#[test]
fn rejects_raw_control_characters() {
    for input in ["\"a\nb\"", "\"a\rb\"", "\"a\tb\""] {
        let error = unquote(input).expect_err("raw control characters must be rejected");
        assert_eq!(error.offset, 1, "input: {input:?}");
        assert_eq!(error.message, "non-printable character in string");
    }
}

#[test]
fn rejects_malformed_escapes_and_invalid_scalars() {
    for input in [
        "",
        "x",
        r#""\x0""#,
        r#""\u123""#,
        r#""\U00110000""#,
        r#""\ud800""#,
    ] {
        assert!(unquote(input).is_err(), "expected {input:?} to fail");
    }
}
