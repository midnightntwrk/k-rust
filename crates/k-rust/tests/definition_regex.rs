use std::collections::BTreeMap;

use ::regex::Regex as RustRegex;
use indoc::indoc;
use k_rust::definition::regex;
use k_rust::definition::{
    Attributes, LOCATION_ATTRIBUTE, ProductionItem, SOURCE_ATTRIBUTE, Sentence, check_regexes,
};
use k_rust::diagnostic::DiagnosticCode;
use k_rust::kast::{Label, Sort};
use proptest::prelude::*;
use serde_json::{Value, json};

macro_rules! regex_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = $source;
            let parsed = regex::parse(source).unwrap();
            insta::with_settings!({
                description => format!("K regex:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(parsed);
            });
        }
    };
}

macro_rules! regex_error_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = $source;
            let error = regex::parse(source).unwrap_err();
            insta::with_settings!({
                description => format!("Invalid K regex:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(error);
            });
        }
    };
}

regex_snapshot!(
    anchors_precedence_and_repetition,
    "^({Digit}|[a-f])+x{2,4}$"
);
regex_snapshot!(classes_escapes_and_unicode, "[^\\n\\-🙂]");
regex_snapshot!(stacked_repetitions, "a?*+{2}{3,}{4,5}");
regex_snapshot!(nested_concatenation, "({Upper}{Lower})+|x(yz)?");
regex_snapshot!(
    actual_newline_character,
    indoc!(
        "
        a
        b
        "
    )
    .trim()
);

regex_error_snapshot!(empty_regex_error, "");
regex_error_snapshot!(unescaped_anchor_error, "a$b");
regex_error_snapshot!(invalid_identifier_error, "{lowercase}");
regex_error_snapshot!(empty_character_class_error, "[]");
regex_error_snapshot!(oversized_repetition_error, "a{999999999999}");

#[test]
fn java_compatible_printer_preserves_the_reference_anchor_bug_explicitly() {
    let start = regex::parse("^a").unwrap();
    let end = regex::parse("a$").unwrap();

    assert_eq!(start.to_java_string(), "^a$");
    assert_eq!(end.to_java_string(), "a");
    assert_eq!(start.to_source_string(), "^a");
    assert_eq!(end.to_source_string(), "a$");
}

#[test]
fn flex_printer_mangles_named_lexical_identifiers() {
    assert_eq!(regex::mangle_flex_identifier("Word"), "Word");
    assert_eq!(regex::mangle_flex_identifier("#Word"), "_Hash_Word");
    assert_eq!(
        regex::parse("{#Word}{Digit}").unwrap().to_flex_string(),
        "{_Hash_Word}{Digit}"
    );
}

#[test]
fn flex_printer_escapes_flex_pattern_characters() {
    for (character, expected) in [
        ('^', r"\^"),
        ('$', r"\$"),
        ('|', r"\|"),
        ('?', r"\?"),
        ('*', r"\*"),
        ('+', r"\+"),
        ('(', r"\("),
        (')', r"\)"),
        ('{', r"\{"),
        ('}', r"\}"),
        ('[', r"\["),
        (']', r"\]"),
        ('\\', r"\\"),
        ('.', r"\."),
        ('"', r#"\""#),
        ('/', r"\/"),
        ('<', r"\<"),
        ('>', r"\>"),
        (' ', r"\ "),
    ] {
        let body = regex::RegexBody::Char(character);
        assert_eq!(body.to_flex_string(), expected, "character {character:?}");
    }
}

#[test]
fn flex_printer_uses_character_class_escaping() {
    for (character, expected) in [
        ('^', r"\^"),
        ('-', r"\-"),
        ('\\', r"\\"),
        ('[', r"\["),
        (']', r"\]"),
        (' ', r"\ "),
        ('/', "/"),
    ] {
        let member = regex::CharClass::Char(character);
        assert_eq!(member.to_flex_string(), expected, "character {character:?}");
    }
}

#[test]
fn flex_printer_preserves_repetition_and_precedence() {
    assert_eq!(
        regex::parse("(ab|c)?d{2}e{3,}f{4,5}")
            .unwrap()
            .to_flex_string(),
        "(ab|c)?d{2}e{3,}f{4,5}"
    );
}

#[test]
fn flex_printer_groups_non_ascii_code_points_and_factors_classes() {
    assert_eq!(regex::parse("🙂+").unwrap().to_flex_string(), "(🙂)+");
    assert_eq!(
        regex::parse("[a🙂b🙁]").unwrap().to_flex_string(),
        "((🙂)|(🙁))|[ab]"
    );
    assert_eq!(regex::parse("[a-z]").unwrap().to_flex_string(), "[a-z]");
}

#[test]
fn flex_printer_applies_the_reference_anchor_rule() {
    assert_eq!(regex::parse("a").unwrap().to_flex_string(), "a");
    assert_eq!(regex::parse("^a").unwrap().to_flex_string(), "^a$");
    assert_eq!(regex::parse("a$").unwrap().to_flex_string(), "a");
    assert_eq!(regex::parse("^a$").unwrap().to_flex_string(), "^a$");
}

#[test]
fn rust_printer_treats_k_backslash_letters_as_literals() {
    let pattern = regex::parse(r"\d+").unwrap().to_flex_pattern().unwrap();
    let compiled = RustRegex::new(&format!(r"\A(?:{})\z", pattern.body)).unwrap();

    assert!(compiled.is_match("ddd"));
    assert!(!compiled.is_match("123"));
}

#[test]
fn rust_printer_escapes_rust_metacharacters() {
    for character in [
        '\\', '.', '+', '*', '?', '(', ')', '|', '[', ']', '{', '}', '^', '$', '#', '&', '-', '~',
    ] {
        let source = if character == '\\' {
            r"\\".to_owned()
        } else if matches!(
            character,
            '.' | '+' | '*' | '?' | '(' | ')' | '|' | '[' | ']' | '{' | '}' | '^' | '$'
        ) {
            format!(r"\{character}")
        } else {
            character.to_string()
        };
        let body = regex::parse(&source)
            .unwrap_or_else(|error| panic!("{source:?}: {error}"))
            .to_flex_pattern()
            .unwrap()
            .body;
        let compiled = RustRegex::new(&format!(r"\A(?:{body})\z"))
            .unwrap_or_else(|error| panic!("{source:?} -> {body:?}: {error}"));
        assert!(
            compiled.is_match(&character.to_string()),
            "{source:?} -> {body:?}"
        );
    }
}

#[test]
fn flex_pattern_applies_the_reference_anchor_rule() {
    let end_only = regex::parse("a$").unwrap().to_flex_pattern().unwrap();
    let start_only = regex::parse("^b").unwrap().to_flex_pattern().unwrap();

    assert!(!end_only.start_line && !end_only.end_line);
    assert!(start_only.start_line && start_only.end_line);
}

#[test]
fn rust_printer_rejects_unexpanded_lexical_references() {
    let error = regex::parse("{Name}")
        .unwrap()
        .to_flex_pattern()
        .unwrap_err();

    assert_eq!(error.name, "Name");
}

#[test]
fn pinned_java_anchor_and_union_cases_match() {
    for invalid in ["^", "$", "^$", "a^b", "a$b", "$a^", "|", "a|", "|a"] {
        assert!(regex::parse(invalid).is_err(), "{invalid}");
    }

    let start = regex::parse("^ab").unwrap();
    assert!(start.start_line);
    assert!(!start.end_line);
    let end = regex::parse("ab$").unwrap();
    assert!(!end.start_line);
    assert!(end.end_line);
    let both = regex::parse("^a$").unwrap();
    assert!(both.start_line && both.end_line);

    assert_eq!(regex::parse("\\^ab").unwrap().to_source_string(), "\\^ab");
    assert_eq!(regex::parse("a\\$b").unwrap().to_source_string(), "a\\$b");
    assert_eq!(regex::parse("a|b").unwrap().to_source_string(), "a|b");
    assert_eq!(regex::parse("ab|c").unwrap().to_source_string(), "ab|c");
}

#[test]
fn pinned_java_reference_corpus_round_trips() {
    // Curated directly from parser/outer/RegexTest.java at the README-pinned K commit.
    let corpus = [
        "#([a-fA-F0-9][a-fA-F0-9])*",
        "#\\(-*alloc[0-9]+(\\+0x[0-9a-fA-F]+)?-*\\)#",
        "%(@|[_a-zA-Z][_0-9a-zA-Z\\.]*)?",
        "(#.*)|[\\n \\t\\r]*",
        "([\\+\\-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+\\-]?[0-9]+)?",
        "(\\/\\*([^\\*]|(\\*+([^\\*\\/])))*\\*+\\/)",
        "({DecConstant}|{OctConstant}|{HexConstant})({IntSuffix}?)",
        "0x([0-9a-fA-F]{2})*",
        "C[A,D]{2,}R",
        "[A-Za-z'\\-][A-Za-z'0-9\\-]*",
        "[\\+\\-]?0x[0-9a-fA-F]+(_[0-9a-fA-F]+)*",
        "[\\\"]([^\\\"\\n\\r\\\\]|[\\\\][nrtf\\\"\\\\])*[\\\"]",
        "[a-zA-Z0-9\\+\\/=]+",
        "[a-zA-Z_#][A-Za-z_0-9]*",
        "\\$[0-9a-zA-Z!$%&'*+/<>?_`|~=:\\@\\^.\\-]+",
        "\\(;([^;]|(;+([^;\\)])))*;\\)",
        "`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`",
        "forall.[ab][#*]",
        "{EncodingPrefix}?\\\"{SCharSeq}?\\\"",
        "{IdentifierNonDigit}(({IdentifierNonDigit}|{Digit})*)",
        "🙁|🙂",
    ];
    for source in corpus {
        let parsed = regex::parse(source).unwrap_or_else(|error| panic!("{source}: {error}"));
        let printed = parsed.to_source_string();
        let reparsed = regex::parse(&printed).unwrap();
        assert_eq!(parsed, reparsed, "{source} -> {printed}");
        assert_eq!(printed, reparsed.to_source_string());
    }
}

#[test]
fn regex_checks_names_anchors_and_parse_errors() {
    let lexical = lexical("Anchor", "^a$", Attributes::default());
    let unknown = regex_production("{Missing}", Attributes::default());
    let invalid = regex_production("[]", located("invalid.k", 7));
    let local = [&lexical, &unknown, &invalid];
    let diagnostics = check_regexes(&local, &local);

    assert_eq!(diagnostics.len(), 3);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Named lexical syntax cannot contain line anchors."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Unrecognized lexical identifiers")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::InvalidRegex
            && diagnostic
                .message
                .contains("Character class cannot be empty")
            && diagnostic.source.as_deref() == Some("invalid.k")
    }));
}

#[test]
fn lexical_cycles_are_disjoint_and_rotate_to_the_earliest_source() {
    let a = lexical("A", "{B}", located("cycle.k", 20));
    let b = lexical("B", "{A}", located("cycle.k", 10));
    let c = lexical("C", "{C}", located("cycle.k", 30));
    let local = [&a, &b, &c];
    let diagnostics = check_regexes(&local, &local);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Circular dependency between lexical identifiers: [B, A]"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Circular dependency between lexical identifiers: [C]"
    }));
}

#[test]
fn ranges_and_unicode_match_check_regex() {
    let production = regex_production("[^é-zZ-A]x{5,2}", Attributes::default());
    let diagnostics = check_regexes(&[&production], &[&production]);

    assert_eq!(diagnostics.len(), 5);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Invalid character range 'Z-A'") })
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Invalid numeric range 'x{5,2}'")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("non-ASCII characters found in negated")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("non-ASCII characters found in character class range")
    }));
}

fn regex_source() -> impl Strategy<Value = String> {
    let atom = prop_oneof![
        "[a-zA-Z0-9_]".prop_map(|value| value),
        Just(".".to_owned()),
        "[A-Z][a-zA-Z0-9]{0,5}".prop_map(|name| format!("{{{name}}}")),
        ("[a-z]", "[a-z]").prop_map(|(start, end)| format!("[{start}-{end}]")),
        prop::sample::select(vec!['^', '$', '|', '?', '*', '+', '(', ')', '[', ']', '\\'])
            .prop_map(|character| format!("\\{character}")),
    ];
    let repeated =
        (atom, 0_u8..6, 0_u8..8, 0_u8..8).prop_map(|(atom, repeat, lower, upper)| match repeat {
            0 => atom,
            1 => format!("{atom}?"),
            2 => format!("{atom}*"),
            3 => format!("{atom}+"),
            4 => format!("{atom}{{{lower}}}"),
            _ => format!("{atom}{{{lower},{upper}}}"),
        });
    let concat = prop::collection::vec(repeated, 1..5).prop_map(|members| members.join(""));
    (
        any::<bool>(),
        prop::collection::vec(concat, 1..4),
        any::<bool>(),
    )
        .prop_map(|(start, members, end)| {
            format!(
                "{}{}{}",
                if start { "^" } else { "" },
                members.join("|"),
                if end { "$" } else { "" }
            )
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn generated_source_round_trips(source in regex_source()) {
        let parsed = regex::parse(&source).unwrap();
        let printed = parsed.to_source_string();
        let reparsed = regex::parse(&printed).unwrap();
        prop_assert_eq!(&parsed, &reparsed);
        prop_assert_eq!(printed, reparsed.to_source_string());
    }

    #[test]
    fn arbitrary_input_never_panics(source in any::<String>()) {
        let _ = regex::parse(&source);
    }
}

fn attrs(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn located(source: &str, line: u32) -> Attributes {
    attrs(&[
        (SOURCE_ATTRIBUTE, json!(source)),
        (LOCATION_ATTRIBUTE, json!([line, 1, line, 20])),
    ])
}

fn lexical(name: &str, regex: &str, attributes: Attributes) -> Sentence {
    Sentence::SyntaxLexical {
        name: name.into(),
        regex: regex.into(),
        attributes,
    }
}

fn regex_production(regex: &str, attributes: Attributes) -> Sentence {
    Sentence::Production {
        label: Some(Label::new("token")),
        parameters: Vec::new(),
        sort: Sort::new("Token"),
        items: vec![ProductionItem::regex(regex)],
        attributes,
    }
}
