use indoc::indoc;
use k_rust::definition::{SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE};
use k_rust::outer::{
    Sentence, check_brackets, check_list_declarations, extract_fenced_k_code, lower, parse,
};
use proptest::prelude::*;

macro_rules! assert_outer_value_snapshot {
    ($source:expr, $value:expr) => {{
        let source = $source;
        let value = $value;
        insta::with_settings!({
            description => format!("K source:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(value);
        });
    }};
}

macro_rules! outer_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = $source;
            let parsed = parse(concat!(stringify!($name), ".k"), source).unwrap();
            assert_outer_value_snapshot!(source, parsed);
        }
    };
}

outer_snapshot!(
    modules_and_imports,
    indoc! {r#"
    requires "domains.md"

    module COLLECTIONS [main]
      imports public BOOL
      imports private MAP
      syntax Exp
    endmodule
"#}
);

#[test]
fn lowering_preserves_bubble_content_offsets() {
    fn content_start_offset(source_name: &str, source: &str) -> usize {
        let lowered = lower(&parse(source_name, source).unwrap(), "MAIN").unwrap();
        let k_rust::definition::Sentence::Bubble { attributes, .. } =
            &lowered.main_module().unwrap().local_sentences[0]
        else {
            panic!("expected a lowered bubble");
        };
        attributes
            .get("contentStartOffset")
            .and_then(serde_json::Value::as_u64)
            .unwrap() as usize
    }

    let source = "module MAIN\n  rule nested(a, b) => c\nendmodule\n";
    assert_eq!(
        content_start_offset("offsets.k", source),
        source.find("nested(a, b)").unwrap(),
    );

    let markdown = "Prose is removed.\n```k\nmodule MAIN\n  rule md => value\nendmodule\n```\n";
    let extracted = extract_fenced_k_code(markdown, "k").unwrap();
    assert_ne!(
        markdown.find("md => value"),
        extracted.find("md => value"),
        "markdown establishes the raw/extracted offset distinction",
    );
    assert_eq!(
        content_start_offset("offsets.md", &extracted),
        extracted.find("md => value").unwrap(),
    );
}

#[test]
fn lowering_preserves_exact_sentence_byte_offsets() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | Exp "+" Exp [seqstrict, symbol(_+_)]
        endmodule
    "#};
    let strict_text = r#"Exp "+" Exp [seqstrict, symbol(_+_)]"#;
    let start = source.find(strict_text).unwrap();
    let lowered = lower(&parse("offsets.k", source).unwrap(), "MAIN").unwrap();
    let strict = lowered
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| sentence.attributes().get("seqstrict").is_some())
        .unwrap();

    assert_eq!(
        strict
            .attributes()
            .get(SENTENCE_START_OFFSET_ATTRIBUTE)
            .and_then(serde_json::Value::as_u64),
        Some(start as u64),
    );
    assert_eq!(
        strict
            .attributes()
            .get(SENTENCE_END_OFFSET_ATTRIBUTE)
            .and_then(serde_json::Value::as_u64),
        Some((start + strict_text.len()) as u64),
    );
}

#[test]
fn priority_separators_must_be_whole_tokens() {
    let parsed = parse(
        "priority.k",
        indoc! {r#"
            module PRIORITY
              syntax priority _|->_ > _Map_ .Map
            endmodule
        "#},
    )
    .unwrap();
    let Sentence::Priority(priority) = &parsed.modules[0].sentences[0] else {
        panic!("expected a syntax priority sentence");
    };

    assert_eq!(
        priority.groups,
        vec![
            vec!["_|->_".to_owned()],
            vec!["_Map_".to_owned(), ".Map".to_owned()],
        ]
    );
}

outer_snapshot!(
    syntax_declarations,
    indoc! {r#"
    module SYNTAX
      syntax {S} List{S}
      syntax NonEmpty = List
      syntax Id ::= r"[a-zA-Z][a-zA-Z0-9]*" [token]
      syntax Exps ::= List{Exp, ","} [klabel(exps)]
      syntax Exp ::= left: Exp "+" Exp [left, klabel(_+_)]
                   | name:Id
                   > "(" Exp ")" [bracket]
      syntax priority _*_ > _+_ _-_
      syntax left _+_ _-_
      syntax lexical Identifier = r"[a-z]+" [prec(1)]
    endmodule
"#}
);

outer_snapshot!(
    bubbles,
    indoc! {r#"
    module RULES
      rule [identity]: X + 0 => X [simplification]
      claim <k> P => Q </k> requires true [trusted]
      context HOLE + X
      context alias HERE [X] = HOLE
      configuration <k> $PGM:Exp </k>
    endmodule
"#}
);

#[test]
fn uppercase_bracketed_rule_rhs_is_not_parsed_as_attributes() {
    let source = "module MAIN\nrule gather(_, TYPES) => [ TYPES ]\nendmodule\n";
    let parsed = parse("bracketed-rhs.k", source).unwrap();
    let Sentence::Bubble(bubble) = &parsed.modules[0].sentences[0] else {
        panic!("expected rule bubble")
    };

    assert_eq!(bubble.content, "gather(_, TYPES) => [ TYPES ]");
    assert!(bubble.attributes.is_empty());
}

#[test]
fn preserves_edge_spaces_in_unquoted_attribute_values() {
    let source = "module MAIN\nsyntax Exp ::= \"x\" [symbol( x), smtlib(x )]\nendmodule\n";
    let parsed = parse("attribute-spaces.k", source).unwrap();
    let Sentence::Syntax(syntax) = &parsed.modules[0].sentences[0] else {
        panic!("expected syntax declaration")
    };
    let k_rust::outer::SyntaxBody::Productions(blocks) = &syntax.body else {
        panic!("expected syntax productions")
    };
    let attributes = &blocks[0].productions[0].attributes;

    assert_eq!(attributes[0].value.as_deref(), Some(" x"));
    assert_eq!(attributes[1].value.as_deref(), Some("x "));
}

#[test]
fn rejects_duplicate_attribute_keys_before_lowering_loses_them() {
    let source = "module MAIN\nsyntax Exp ::= \"x\" [symbol(first), symbol(second)]\nendmodule\n";
    let error = parse("duplicate-attribute.k", source).unwrap_err();

    assert_eq!(error.message, "duplicate attribute key \"symbol\"");
}

#[test]
fn generated_list_terminator_symbols_include_the_syntax_module() {
    let source = "module LIST-SYNTAX\nsyntax Items ::= List{Item, \"\"}\nendmodule\n";
    let definition = lower(&parse("list-symbol.k", source).unwrap(), "LIST-SYNTAX").unwrap();
    let symbol = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            k_rust::definition::Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name.starts_with(".List") => attributes.get_str("symbol"),
            _ => None,
        })
        .unwrap();

    assert_eq!(symbol, ".List{\"___LIST-SYNTAX\"}");
}

#[test]
fn generated_list_terminator_symbols_follow_explicit_list_symbols() {
    let source =
        "module LIST-SYNTAX\nsyntax Items ::= List{Item, \"\"} [symbol(items)]\nendmodule\n";
    let definition = lower(&parse("list-symbol.k", source).unwrap(), "LIST-SYNTAX").unwrap();
    let symbol = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            k_rust::definition::Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name.starts_with(".List") => attributes.get_str("symbol"),
            _ => None,
        })
        .unwrap();

    assert_eq!(symbol, ".List{\"items\"}");
}

outer_snapshot!(
    bubble_attributes_ignore_commented_brackets,
    indoc! {r#"
    module COMMENTS
      rule X => X [simplification]
      // rule Y => Y [anywhere]
      /* rule Z => Z [macro] */
    endmodule
"#}
);

#[test]
fn list_declaration_checks_match_the_frontend_categories() {
    let source = indoc! {r#"
        module LISTS
          syntax K ::= List{Exp, ","}
          syntax Loop ::= List{Loop, ","}
          syntax Exps ::= "[" List{Exp, ","} "]"
          syntax Good ::= NeList{Exp, ","}
        endmodule
    "#};
    let parsed = parse("lists.k", source).unwrap();

    assert_outer_value_snapshot!(source, check_list_declarations(&parsed));
}

#[test]
fn comments_and_escaped_literals_are_lexed_without_losing_spans() {
    let source = indoc! {r#"
        // file comment
        module TRIVIA /* module comment */
          syntax Text ::= "line\n\"quoted\"" // sentence comment
          rule X /* inside the bubble */ => X
        endmodule
    "#};
    let parsed = parse("trivia.k", source).unwrap();

    assert_outer_value_snapshot!(source, parsed);
}

#[test]
fn pinned_outer_corpus_families_parse_and_lower() {
    let source = include_str!("fixtures/outer/record-and-list.k");
    let parsed = parse("record-and-list.k", source).unwrap();
    let mut lowered = lower(&parsed, "OUTER-CORPUS").unwrap();
    for module in &mut lowered.modules {
        for sentence in &mut module.local_sentences {
            sentence
                .attributes_mut()
                .remove(SENTENCE_START_OFFSET_ATTRIBUTE);
            sentence
                .attributes_mut()
                .remove(SENTENCE_END_OFFSET_ATTRIBUTE);
        }
    }

    insta::with_settings!({
        description => format!("K source:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!("pinned_outer_corpus", parsed);
    });
    insta::with_settings!({
        description => format!("K source:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(
            "pinned_outer_lowering",
            lowered
        );
    });
}

#[test]
fn bracket_checks_run_before_lowering() {
    let source = indoc! {r#"
        module BRACKETS
          syntax Exp ::= "(" Int ")" [bracket]
                     | "[" Exp Exp "]" [bracket]
                     | "{" Exp "}" [bracket]
        endmodule
    "#};
    let parsed = parse("brackets.k", source).unwrap();

    let diagnostics = check_brackets(&parsed);
    assert_outer_value_snapshot!(source, diagnostics);
    assert!(lower(&parsed, "BRACKETS").is_err());
}

proptest! {
    #[test]
    fn arbitrary_source_never_panics(source in any::<String>()) {
        if let Ok(parsed) = parse("fuzz.k", &source) {
            let _ = lower(&parsed, "FUZZ");
        }
    }
}
