use indoc::indoc;
use k_rust::definition::{Location, Sentence};
use k_rust::inner::{NoParseInput, ParseError, RuleError};
use k_rust::kast::TermSpan;
use k_rust::outer::{
    LoadOptions, ResolvedSource, extract_fenced_k_code, extract_fenced_k_code_with_map,
    load_with_options,
};

#[test]
fn extracts_selected_fences_with_source_positions_intact() {
    let source = indoc! {r#"
        prose before
         ```k
         requires "base.md"
         ```
        ```{skip}
        module IGNORED endmodule
        ```
        ```{k enabled}
        module MAIN
          imports BASE
        endmodule
        ```
    "#};
    let extracted = extract_fenced_k_code(source, "k&!skip").unwrap();

    insta::with_settings!({
        description => format!("Markdown source:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(extracted);
    });
}

#[test]
fn extracted_ranges_map_back_to_raw_markdown_bytes() {
    let source = "π prose\n```k\nmodule MAIN\n  rule café => value\nendmodule\n```\ntail";
    let extracted = extract_fenced_k_code_with_map(source, "k").unwrap();
    let semantic_start = extracted.text.find("café => value").unwrap();
    let semantic_end = semantic_start + "café => value".len();
    let raw_start = source.find("café => value").unwrap();
    let raw_end = raw_start + "café => value".len();

    assert_eq!(
        extracted.offset_map.raw_range(semantic_start..semantic_end),
        Some(raw_start..raw_end)
    );
    assert_eq!(
        &extracted.text[semantic_start..semantic_end],
        &source[raw_start..raw_end]
    );
}

#[test]
fn loaded_rule_spans_resolve_to_raw_markdown_bytes() {
    let source = indoc! {r#"
        Documentation before the definition.

        ```k
        module MAIN
          syntax State ::= "start" [symbol(start)]
                         | "value" [symbol(value)]
          rule start => value
        endmodule
        ```

        Documentation after the definition.
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load_with_options(
        ResolvedSource::new("main.md", source),
        "MAIN",
        &mut resolver,
        &LoadOptions::default(),
    )
    .unwrap();
    let body = loaded
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .expect("the Markdown rule should be resolved");
    let span = body
        .metadata()
        .and_then(|metadata| metadata.span)
        .expect("the parsed rule body should retain its semantic span");
    let raw_range = loaded
        .source_table()
        .raw_range(span)
        .expect("the semantic span should resolve against raw Markdown");
    let extracted = extract_fenced_k_code(source, "k").unwrap();

    assert_eq!(&source[raw_range], &extracted[span.start..span.end]);
    assert_eq!(&extracted[span.start..span.end], "start => value");
}

#[test]
fn markdown_rule_failures_report_the_exact_unexpected_token_location() {
    let source = indoc! {r#"
        Prose before.

        ```k
        module MARKDOWN-RULE-ERROR
          syntax Start ::= "ok" "done" [symbol(start)]
          syntax Other ::= "bad" [symbol(bad)]
          rule ok bad
        endmodule
        ```
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let error = load_with_options(
        ResolvedSource::new("fixture.md", source),
        "MARKDOWN-RULE-ERROR",
        &mut resolver,
        &LoadOptions::default(),
    )
    .unwrap_err();
    let k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)) = error else {
        panic!("expected an inner rule parse error: {error:?}")
    };
    assert_eq!(error.source.as_deref(), Some("fixture.md"));
    assert_eq!(
        error.location,
        Some(Location {
            start_line: 7,
            start_column: 11,
            end_line: 7,
            end_column: 14,
        })
    );
    assert_eq!(
        error.error,
        ParseError::NoParse {
            position: 3,
            expected: vec!["\"done\"".into()].into(),
            input: NoParseInput::Token {
                value: "bad".into(),
            },
            previous: Some("ok".into()),
            notes: None,
            span: Some(TermSpan {
                source: k_rust::provenance::SourceId(0),
                start: extract_fenced_k_code(source, "k")
                    .unwrap()
                    .find("ok bad")
                    .unwrap()
                    + 3,
                end: extract_fenced_k_code(source, "k")
                    .unwrap()
                    .find("ok bad")
                    .unwrap()
                    + 6,
            }),
            work_limit: None,
        }
    );
}

/// The location of the rule failure in `source`, a Markdown definition of the module `MAIN`.
fn rule_failure_location(source: &str) -> Option<Location> {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let error = load_with_options(
        ResolvedSource::new("fixture.md", source),
        "MAIN",
        &mut resolver,
        &LoadOptions::default(),
    )
    .unwrap_err();
    let k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)) = error else {
        panic!("expected an inner rule parse error: {error:?}")
    };
    error.location
}

/// A Markdown definition's lines end where the definition text's do: a fence opens and closes on
/// a line that any line terminator ends, and every location after it counts the lines before it.
#[test]
fn markdown_lines_end_at_every_line_terminator() {
    let lines = [
        "Prose before.",
        "",
        "```k",
        "module MAIN",
        r#"  syntax Start ::= "ok" "done" [symbol(start)]"#,
        "```",
        "",
        "Prose between.",
        "",
        "```{k}",
        r#"  syntax Other ::= "bad" [symbol(bad)]"#,
        "  rule ok bad",
        "endmodule",
        "```",
        "Prose after.",
        "",
    ];
    let rule = Some(Location {
        start_line: 12,
        start_column: 11,
        end_line: 12,
        end_column: 14,
    });
    let with_newlines = lines.join("\n");
    let extracted_with_newlines = extract_fenced_k_code(&with_newlines, "k").unwrap();
    assert!(extracted_with_newlines.contains("module MAIN"));
    assert!(extracted_with_newlines.contains("rule ok bad"));
    assert_eq!(rule_failure_location(&with_newlines), rule);

    for terminator in [
        "\r\n", "\r", "\u{b}", "\u{c}", "\u{85}", "\u{2028}", "\u{2029}",
    ] {
        let source = lines.join(terminator);
        assert_eq!(
            extract_fenced_k_code(&source, "k").unwrap(),
            extracted_with_newlines.replace('\n', terminator),
            "{terminator:?}"
        );
        assert_eq!(rule_failure_location(&source), rule, "{terminator:?}");
    }

    // One file, three line ends: prose and the fences between the two blocks end in U+2028, the
    // first block in `\r`, the second in `\r\n`.
    let mixed = [
        lines[..2].join("\n"),
        lines[2..5].join("\r"),
        lines[5..10].join("\u{2028}"),
        lines[10..].join("\r\n"),
    ]
    .join("\u{2028}");
    let extracted = extract_fenced_k_code(&mixed, "k").unwrap();
    assert!(extracted.contains("module MAIN\r"));
    assert!(extracted.contains("rule ok bad\r\n"));
    assert_eq!(rule_failure_location(&mixed), rule);
}

/// Prose is replaced, not dropped: a `\r` that ends a prose line, a line before a fence or the last
/// line of a block is not joined with an `\n` after the characters between them into one `\r\n`,
/// so every location after it is on its line of the file.
#[test]
fn markdown_prose_keeps_every_line_end_of_the_file() {
    let syntax = concat!(
        "  syntax Start ::= \"ok\" \"done\" [symbol(start)]\n",
        "  syntax Other ::= \"bad\" [symbol(bad)]\n",
    );
    let cases = [
        // A lone `\r` inside a prose line that `\n` ends.
        (
            format!("Prose\rbefore.\n```k\nmodule MAIN\n{syntax}  rule ok bad\nendmodule\n```\n"),
            7,
        ),
        // A prose line ending in `\r` before an opening fence line ending in `\n`.
        (
            format!("Prose.\r```k\nmodule MAIN\n{syntax}  rule ok bad\nendmodule\n```\n"),
            6,
        ),
        // A block whose last line ends in `\r` before a closing fence line ending in `\n`.
        (
            format!(
                "```k\nmodule MAIN\n{}\r```\n\n```k\n  rule ok bad\nendmodule\n```\n",
                syntax.trim_end()
            ),
            8,
        ),
    ];
    for (source, line) in cases {
        let extracted = extract_fenced_k_code_with_map(&source, "k").unwrap();
        // Every character keeps its byte offset, and every `\r` and `\n` of the file is in the text.
        assert_eq!(extracted.text.len(), source.len(), "{source:?}");
        let line_ends = |text: &str| {
            text.char_indices()
                .filter(|(_, character)| matches!(character, '\r' | '\n'))
                .collect::<Vec<_>>()
        };
        assert_eq!(line_ends(&extracted.text), line_ends(&source), "{source:?}");
        let rule = extracted.text.find("ok bad").unwrap() + 3;
        assert_eq!(
            extracted.offset_map.raw_range(rule..rule + 3),
            Some(rule..rule + 3)
        );
        assert_eq!(&source[rule..rule + 3], "bad");
        assert_eq!(
            rule_failure_location(&source),
            Some(Location {
                start_line: line,
                start_column: 11,
                end_line: line,
                end_column: 14,
            }),
            "{source:?}"
        );
    }
}

#[test]
fn selector_supports_boolean_operators_grouping_and_both_tag_spellings() {
    let source = indoc! {r#"
        ```{.k a}
        selected-a
        ```
        ```{k b}
        selected-b
        ```
        ```other
        other
        ```
    "#};

    assert!(
        extract_fenced_k_code(source, "k&a")
            .unwrap()
            .contains("selected-a")
    );
    assert!(
        !extract_fenced_k_code(source, "k&a")
            .unwrap()
            .contains("selected-b")
    );
    let either = extract_fenced_k_code(source, "(a|b)&!other").unwrap();
    assert!(either.contains("selected-a"));
    assert!(either.contains("selected-b"));
    assert!(!either.contains("other"));
    assert!(
        extract_fenced_k_code(source, "*")
            .unwrap()
            .contains("other")
    );
}

#[test]
fn rejects_malformed_selectors_and_annotations() {
    assert!(extract_fenced_k_code("```k\nmodule M endmodule\n```", "k|").is_err());
    let malformed_braces =
        extract_fenced_k_code_with_map("```{k a\nmodule M endmodule\n```", "k").unwrap();
    assert!(!malformed_braces.text.contains("module M endmodule"));
    assert_eq!(malformed_braces.warnings.len(), 1);

    let malformed_words =
        extract_fenced_k_code_with_map("```k a\nmodule M endmodule\n```", "k").unwrap();
    assert!(!malformed_words.text.contains("module M endmodule"));
    assert_eq!(malformed_words.warnings.len(), 1);

    assert!(extract_fenced_k_code("```k:foo\nmodule M endmodule\n```", "k").is_err());
}

#[test]
fn loader_processes_markdown_requires_with_the_selected_tags() {
    let entry = indoc! {r#"
        Documentation.

        ```k
        requires "base.md"
        module MAIN
          imports BASE
        endmodule
        ```
    "#};
    let base = indoc! {r#"
        ```{k disabled}
        module WRONG endmodule
        ```

        ```{k enabled}
        module BASE
          syntax Value ::= "value" [symbol(value)]
        endmodule
        ```
    "#};
    let mut resolver = |_: &str, required: &str| match required {
        "base.md" => Ok(ResolvedSource::new("base.md", base)),
        _ => Err(format!("missing {required}")),
    };

    let loaded = load_with_options(
        ResolvedSource::new("main.md", entry),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            markdown_selector: "k&enabled|k&!disabled".into(),
            ..LoadOptions::default()
        },
    )
    .unwrap();

    assert!(loaded.resolved().module_id("MAIN").is_some());
    assert!(loaded.resolved().module_id("BASE").is_some());
    assert!(loaded.resolved().module_id("WRONG").is_none());
}
