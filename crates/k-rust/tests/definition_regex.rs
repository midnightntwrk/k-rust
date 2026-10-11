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
regex_error_snapshot!(unmatched_close_group_error, "a)");
regex_error_snapshot!(invalid_identifier_error, "{lowercase}");
regex_error_snapshot!(empty_character_class_error, "[]");
regex_error_snapshot!(oversized_repetition_error, "a{999999999999}");

#[test]
fn canonical_printer_keeps_each_anchor_as_written() {
    for (source, canonical) in [
        ("a", "a"),
        ("^a", "^a"),
        ("a$", "a$"),
        ("^a$", "^a$"),
        ("^a|b$", "^a|b$"),
        // The anchors apply to the whole top-level alternation, so the group is redundant.
        ("^(a|b)$", "^a|b$"),
    ] {
        assert_eq!(
            regex::parse(source).unwrap().to_canonical_string(),
            canonical,
            "{source}"
        );
    }
    // Distinct anchors are distinct regexes, so they have distinct canonical forms.
    let forms =
        ["a", "^a", "a$", "^a$"].map(|source| regex::parse(source).unwrap().to_canonical_string());
    assert_eq!(
        forms
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        4
    );
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
fn flex_printer_groups_non_ascii_code_points_and_encodes_classes() {
    assert_eq!(regex::parse("🙂+").unwrap().to_flex_string(), "(🙂)+");
    assert_eq!(
        regex::parse("[a🙂b🙁]").unwrap().to_flex_string(),
        r"([\x61-\x62]|\xF0\x9F\x99[\x81-\x82])"
    );
    assert_eq!(regex::parse("[a-z]").unwrap().to_flex_string(), "[a-z]");
    assert_eq!(
        regex::parse(".+").unwrap().to_flex_string(),
        concat!(
            r"([\x00-\x09\x0B-\x7F]|[\xC2-\xDF][\x80-\xBF]|\xE0[\xA0-\xBF][\x80-\xBF]",
            r"|[\xE1-\xEC][\x80-\xBF][\x80-\xBF]|\xED[\x80-\x9F][\x80-\xBF]",
            r"|[\xEE-\xEF][\x80-\xBF][\x80-\xBF]|\xF0[\x90-\xBF][\x80-\xBF][\x80-\xBF]",
            r"|[\xF1-\xF3][\x80-\xBF][\x80-\xBF][\x80-\xBF]|\xF4[\x80-\x8F][\x80-\xBF][\x80-\xBF])+"
        )
    );
}

#[test]
fn flex_name_keeps_classes_as_written() {
    assert_eq!(
        regex::parse("^[^a-z]+.[a🙂]$").unwrap().to_flex_name(),
        "^[^a-z]+.[a🙂]$"
    );
}

/// A Flex pattern as a pattern over bytes for Rust's regex engine: the Flex printer writes a
/// class, `.` and every byte outside ASCII in a syntax both engines read alike.
fn flex_as_byte_regex(body: &regex::RegexBody) -> ::regex::bytes::Regex {
    let flex = body.to_flex_string();
    ::regex::bytes::Regex::new(&format!(r"(?-u)\A(?:{flex})\z"))
        .unwrap_or_else(|error| panic!("{flex:?}: {error}"))
}

fn rust_character_regex(body: &regex::RegexBody) -> RustRegex {
    RustRegex::new(&format!(r"\A(?:{})\z", body.to_rust_string().unwrap())).unwrap()
}

/// Byte strings that encode no character: lone and stray continuation bytes, truncated, overlong
/// and surrogate encodings, a code point above U+10FFFF, and bytes no UTF-8 text holds.
const NOT_UTF8: [&[u8]; 9] = [
    b"\x80",
    b"\xC3",
    b"\xC0\x80",
    b"\xE0\x80\x80",
    b"\xED\xA0\x80",
    b"\xF4\x90\x80\x80",
    b"\xFF",
    b"\xC3\xA9\x80",
    b"\xF0\x9F\x99",
];

/// A generated scanner reads the UTF-8 bytes of its input, and the in-process scanner its
/// characters; a token is a sequence of characters, so a class or `.` in a Flex pattern must match
/// one whole character exactly where it matches that character in-process, never a part of one and
/// never a byte sequence that encodes no character.
#[test]
fn flex_printer_classes_match_whole_characters_as_the_in_process_pattern_does() {
    let mut characters = (0..=0x7F).filter_map(char::from_u32).collect::<Vec<_>>();
    characters.extend(
        [
            0x80, 0x81, 0xE9, 0xFC, 0xFF, 0x7FF, 0x800, 0x2028, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF,
            0x10000, 0x1F640, 0x1F641, 0x1F642, 0x1F643, 0x10FFFE, 0x10FFFF,
        ]
        .into_iter()
        .filter_map(char::from_u32),
    );
    let pairs = ['a', 'b', '\n', 'é', '\u{2028}', '🙂'];
    for source in [
        ".",
        "[^a-z]",
        r"[^\n]",
        "[a🙂b🙁]",
        "[^é]",
        "[^\u{7F}]",
        "[^\u{80}]",
        "[^\u{D7FF}]",
        "[^\u{E000}]",
        "[^\u{10FFFF}]",
        "[\u{80}-\u{7FF}]",
        "[é-🙂]",
        "[^\u{0}-\u{10FFFF}]",
        "[^a]{2}",
        "a.b",
        "(.|[^b])+",
    ] {
        let body = regex::parse(source).unwrap().body;
        let bytes = flex_as_byte_regex(&body);
        let characters_regex = rust_character_regex(&body);
        let texts = characters
            .iter()
            .map(char::to_string)
            .chain(
                pairs
                    .iter()
                    .flat_map(|first| pairs.iter().map(move |second| format!("{first}{second}"))),
            )
            .chain(characters.iter().map(|character| format!("a{character}b")));
        for text in texts {
            assert_eq!(
                bytes.is_match(text.as_bytes()),
                characters_regex.is_match(&text),
                "{source:?} on {text:?}"
            );
        }
        for not_utf8 in NOT_UTF8 {
            for text in [not_utf8.to_vec(), [b"a", not_utf8, b"b"].concat()] {
                assert!(!bytes.is_match(&text), "{source:?} on {text:?}");
            }
        }
    }
}

proptest! {
    #[test]
    fn flex_printer_classes_denote_the_characters_of_the_class(
        negated in any::<bool>(),
        members in prop::collection::vec(
            (any::<char>(), prop::option::of(0u32..0x2000)), 1..5),
        probes in prop::collection::vec(any::<char>(), 1..16),
    ) {
        let members = members
            .into_iter()
            .map(|(start, width)| match width.and_then(|width| char::from_u32(start as u32 + width)) {
                Some(end) => regex::CharClass::Range { start, end },
                None => regex::CharClass::Char(start),
            })
            .collect::<Vec<_>>();
        let body = regex::RegexBody::CharClass { negated, members: members.clone() };
        let bytes = flex_as_byte_regex(&body);
        let probes = probes.into_iter().chain(members.iter().flat_map(|member| match *member {
            regex::CharClass::Char(character) => vec![character],
            regex::CharClass::Range { start, end } => [start as u32, end as u32]
                .into_iter()
                .flat_map(|point| [point.wrapping_sub(1), point, point + 1])
                .filter_map(char::from_u32)
                .collect(),
        }));
        for probe in probes {
            let member = members.iter().any(|member| match *member {
                regex::CharClass::Char(character) => character == probe,
                regex::CharClass::Range { start, end } => (start..=end).contains(&probe),
            });
            prop_assert_eq!(
                bytes.is_match(probe.to_string().as_bytes()),
                member != negated,
                "{:?} on {:?}", body.to_flex_string(), probe
            );
        }
        for not_utf8 in NOT_UTF8 {
            prop_assert!(!bytes.is_match(not_utf8));
        }
    }
}

#[test]
fn flex_printer_keeps_each_anchor_as_written() {
    // A Flex rule's leading `^` and trailing `$` apply to the whole rule, alternation included,
    // which is the scope a K token regex's anchors have.
    for (source, flex) in [
        ("a", "a"),
        ("^a", "^a"),
        ("a$", "a$"),
        ("^a$", "^a$"),
        ("^a|b$", "^a|b$"),
        ("^(a|b)", "^a|b"),
        ("(a|b)$", "a|b$"),
    ] {
        assert_eq!(
            regex::parse(source).unwrap().to_flex_string(),
            flex,
            "{source}"
        );
    }
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
fn flex_pattern_carries_each_anchor_as_written() {
    for (source, start_line, end_line) in [
        ("a", false, false),
        ("^a", true, false),
        ("a$", false, true),
        ("^a$", true, true),
        ("^a|b", true, false),
        ("a|b$", false, true),
    ] {
        let pattern = regex::parse(source).unwrap().to_flex_pattern().unwrap();
        assert_eq!(
            (pattern.start_line, pattern.end_line),
            (start_line, end_line),
            "{source}"
        );
    }
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
fn misplaced_anchors_and_empty_alternatives_are_rejected_and_anchors_are_parsed() {
    for invalid in ["^", "$", "^$", "a^b", "a$b", "$a^", "|", "a|", "|a"] {
        assert!(regex::parse(invalid).is_err(), "{invalid}");
    }
    // An anchor is a property of the whole regex: inside a group or next to an inner `|` it is a
    // syntax error, not an anchor of that alternative.
    for invalid in [
        "(^a)", "(a$)", "a|^b", "a$|b", "(a|^b)", "(a$|b)", "^(^a)", "(a$)$", "^a|^b", "a$|b$",
    ] {
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

    assert_eq!(
        regex::parse("\\^ab").unwrap().to_canonical_string(),
        "\\^ab"
    );
    assert_eq!(
        regex::parse("a\\$b").unwrap().to_canonical_string(),
        "a\\$b"
    );
    assert_eq!(regex::parse("a|b").unwrap().to_canonical_string(), "a|b");
    assert_eq!(regex::parse("ab|c").unwrap().to_canonical_string(), "ab|c");
}

#[test]
fn token_regex_corpus_round_trips_through_the_canonical_printer() {
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
        let printed = parsed.to_canonical_string();
        let reparsed = regex::parse(&printed).unwrap();
        assert_eq!(parsed, reparsed, "{source} -> {printed}");
        assert_eq!(printed, reparsed.to_canonical_string());
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

#[test]
fn non_ascii_findings_merge_across_the_regexes_of_one_production() {
    let production = Sentence::Production {
        label: Some(Label::new("token")),
        parameters: Vec::new(),
        sort: Sort::new("Token"),
        items: vec![
            ProductionItem::regex("[^é-ü]"),
            ProductionItem::regex("[a-z]"),
            ProductionItem::regex("[^ü]x{3,1}[à-a]"),
        ],
        attributes: Attributes::default(),
    };
    let messages = check_regexes(&[&production], &[&production])
        .into_iter()
        .map(|diagnostic| diagnostic.message)
        .collect::<Vec<_>>();

    assert_eq!(
        messages,
        [
            "Invalid numeric range 'x{3,1}'. Start of range 3 is greater than end of range 1.",
            "Invalid character range 'à-a'. Start of range U+00E0 is greater than end of range U+0061.",
            "Unsupported non-ASCII characters found in negated character class: [é, ü]",
            "Unsupported non-ASCII characters found in character class range: [é, ü, à]",
        ]
    );
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
        let printed = parsed.to_canonical_string();
        let reparsed = regex::parse(&printed).unwrap();
        prop_assert_eq!(&parsed, &reparsed);
        prop_assert_eq!(printed, reparsed.to_canonical_string());
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
