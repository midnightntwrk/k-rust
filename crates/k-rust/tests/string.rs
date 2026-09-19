// Cases ported from pyk and expanded to pin reference KORE string behavior.

use k_rust::kore::ast::KoreString;
use k_rust::kore::string::{quote, unquote};

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
        (r#""\x80""#, vec![0x80]),
        (r#""\x0f""#, vec![0x0f]),
        (r#""\x0F""#, vec![0x0f]),
        (r#""\u03b1""#, "α".as_bytes().to_vec()),
        (r#""\u03B1""#, "α".as_bytes().to_vec()),
        (r#""\U0001f642""#, "🙂".as_bytes().to_vec()),
        (r#""\U0001F642""#, "🙂".as_bytes().to_vec()),
        (r#""\x80\x80""#, vec![0x80, 0x80]),
        (
            r#""a\u03b1\x80\U0001f642b""#,
            ["aα".as_bytes(), &[0x80], "🙂b".as_bytes()].concat(),
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
        ("\u{0}\u{f}\u{80}\u{ff}", r#""\x00\x0f\xc2\x80\xc3\xbf""#),
        ("α", r#""\xce\xb1""#),
        ("🙂", r#""\xf0\x9f\x99\x82""#),
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

#[test]
fn round_trips_invalid_utf8_and_embedded_nul() {
    let value = KoreString::from(vec![0xff, 0x80, 0x00, b'A']);
    let encoded = quote(&value);
    assert_eq!(encoded, r#""\xff\x80\x00A""#);
    assert_eq!(unquote(&encoded).unwrap(), value);
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
