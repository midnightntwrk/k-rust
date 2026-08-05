// Cases ported from pyk and expanded to pin scala-kore StringUtil compatibility.

use kore_rs::string::{quote, unquote};

#[test]
fn unquotes_kore_escapes() {
    let cases = [
        ("\"\"", ""),
        (r#"" ""#, " "),
        (r#""foo""#, "foo"),
        (r#""\t""#, "\t"),
        (r#""\n""#, "\n"),
        (r#""\f""#, "\u{c}"),
        (r#""\r""#, "\r"),
        (r#""\\""#, "\\"),
        (r#""\"""#, "\""),
        (r#""\x80""#, "\u{80}"),
        (r#""\x0f""#, "\u{f}"),
        (r#""\x0F""#, "\u{f}"),
        (r#""\u03b1""#, "α"),
        (r#""\u03B1""#, "α"),
        (r#""\U0001f642""#, "🙂"),
        (r#""\U0001F642""#, "🙂"),
        (r#""\x80\x80""#, "\u{80}\u{80}"),
        (r#""a\u03b1\x80\U0001f642b""#, "aα\u{80}🙂b"),
    ];

    for (input, expected) in cases {
        assert_eq!(unquote(input).as_deref(), Ok(expected), "input: {input}");
    }
}

#[test]
fn quotes_using_the_canonical_kore_form() {
    let cases = [
        ("", "\"\""),
        ("plain ASCII", r#""plain ASCII""#),
        ("\"\\\n\r\t\u{c}", r#""\"\\\n\r\t\f""#),
        ("\u{0}\u{f}\u{80}\u{ff}", r#""\x00\x0f\x80\xff""#),
        ("α", r#""\u03b1""#),
        ("🙂", r#""\U0001f642""#),
    ];

    for (input, expected) in cases {
        assert_eq!(quote(input), expected, "input: {input:?}");
    }
}

#[test]
fn round_trips_unicode_scalar_values() {
    for codepoint in 0..=0x10ffff {
        let Some(character) = char::from_u32(codepoint) else {
            continue;
        };
        let value = character.to_string();
        assert_eq!(unquote(&quote(&value)).as_deref(), Ok(value.as_str()));
    }
}

#[test]
fn matches_unknown_escape_compatibility() {
    assert_eq!(unquote(r#""\q""#).as_deref(), Ok("q"));
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
