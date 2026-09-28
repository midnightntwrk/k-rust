use k_rust_regex::{Issue, RegexBody, check, parse};

fn issues(source: &str) -> Vec<Issue> {
    check(&parse(source).unwrap_or_else(|error| panic!("{source}: {error}")))
}

fn messages(source: &str) -> Vec<String> {
    issues(source).iter().map(ToString::to_string).collect()
}

#[test]
fn leftover_input_names_the_offending_token() {
    for (source, index, message) in [
        ("a)", 1, "Unexpected token ')'. Did you mean '\\)'?"),
        ("ab)c", 2, "Unexpected token ')'. Did you mean '\\)'?"),
        ("(a))", 3, "Unexpected token ')'. Did you mean '\\)'?"),
        ("a$b", 1, "Unexpected token '$'. Did you mean '\\$'?"),
        ("a$)", 1, "Unexpected token '$'. Did you mean '\\$'?"),
    ] {
        let error = parse(source).unwrap_err();
        assert_eq!(
            (error.index, error.message.as_str()),
            (index, message),
            "{source}"
        );
    }
}

#[test]
fn parse_error_index_counts_chars_and_byte_index_counts_bytes() {
    let error = parse("éé)").unwrap_err();
    assert_eq!(error.index, 2);
    assert_eq!(error.byte_index(), 4);
    assert_eq!(&error.input[error.byte_index()..], ")");

    let at_end = parse("é\\").unwrap_err();
    assert_eq!(at_end.index, 2);
    assert_eq!(at_end.byte_index(), at_end.input.len());
}

#[test]
fn descending_char_range_is_reported_per_occurrence() {
    assert_eq!(
        issues("[z-a]b[Z-A]"),
        [
            Issue::DescendingCharRange {
                start: 'z',
                end: 'a'
            },
            Issue::DescendingCharRange {
                start: 'Z',
                end: 'A'
            },
        ]
    );
    assert_eq!(
        messages("[z-a]")[0],
        "Invalid character range 'z-a'. Start of range U+007A is greater than end of range U+0061."
    );
    assert!(issues("[a-a][a-z]").is_empty());
}

#[test]
fn descending_repeat_is_reported_with_its_operand() {
    assert_eq!(
        issues("(ab){3,1}"),
        [Issue::DescendingRepeat {
            body: parse("ab").unwrap().body,
            at_least: 3,
            at_most: 1,
        }]
    );
    assert_eq!(
        messages("x{5,2}"),
        ["Invalid numeric range 'x{5,2}'. Start of range 5 is greater than end of range 2."]
    );
    assert!(issues("x{2,2}x{0,}").is_empty());
}

#[test]
fn non_ascii_in_negated_class_merges_members_and_endpoints() {
    assert_eq!(
        issues("[^é][^a-ü]é[^é]"),
        [
            Issue::NonAsciiInNegatedClass(vec!['é', 'ü']),
            Issue::NonAsciiInClassRange(vec!['ü']),
        ]
    );
    assert_eq!(
        messages("[^éü]"),
        ["Unsupported non-ASCII characters found in negated character class: [é, ü]"]
    );
}

#[test]
fn non_ascii_range_endpoint_is_reported_in_any_class() {
    assert_eq!(
        messages("[é-ü][a-é]"),
        ["Unsupported non-ASCII characters found in character class range: [é, ü]"]
    );
    // A non-ASCII member of a plain class is expressible for a byte scanner.
    assert!(issues("[aé]é").is_empty());
}

#[test]
fn descending_issues_precede_non_ascii_issues() {
    assert_eq!(
        issues("[^é]x{3,1}[à-a]"),
        [
            Issue::DescendingRepeat {
                body: RegexBody::Char('x'),
                at_least: 3,
                at_most: 1,
            },
            Issue::DescendingCharRange {
                start: 'à',
                end: 'a'
            },
            Issue::NonAsciiInNegatedClass(vec!['é']),
            Issue::NonAsciiInClassRange(vec!['à']),
        ]
    );
}

#[test]
fn named_references_are_deduplicated_in_preorder() {
    let regex = parse("{B}({A}|{B})*{C}{A}").unwrap();
    assert_eq!(regex.body.named_references(), ["B", "A", "C"]);
    assert!(parse("[a-z]+").unwrap().body.named_references().is_empty());
    // Name resolution is definition-dependent, so check does not report references.
    assert!(check(&regex).is_empty());
}
