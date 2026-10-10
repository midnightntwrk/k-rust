use std::fmt::Write as _;

use indoc::indoc;
use k_rust::definition::{
    SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE, json as definition_json,
};
use k_rust::diagnostic::DiagnosticCode;
use k_rust::outer::{
    LoadOptions, Sentence, check_brackets, check_list_declarations, extract_fenced_k_code,
    load_structured, lower, parse,
};
use proptest::prelude::*;

#[test]
fn rejects_leading_zero_numeral_sorts_at_every_outer_sort_position() {
    for syntax in [
        "syntax MInt{08}",
        "syntax 08",
        "syntax Foo ::= MInt{08}",
        "syntax {08} MInt{08}",
        "syntax Alias = MInt{08}",
        "syntax MInt{08} = Foo",
    ] {
        let source = format!("module MAIN\n  {syntax}\nendmodule\n");
        let error = parse("leading-zero.k", &source).unwrap_err();
        assert_eq!(
            error.message, "numeral sort 08 is written with a leading zero; a width is spelled 8",
            "{syntax}"
        );
        assert_eq!(error.position.offset, source.find("08").unwrap());
        assert_eq!(error.position.line, 2);
    }
}

/// Snapshot `outline`, a text outline of what `source` parses or checks to, under the test's
/// name, with the source as the snapshot's description.
macro_rules! assert_outline_snapshot {
    ($source:expr, $outline:expr) => {{
        let source = $source;
        let outline: String = $outline;
        insta::with_settings!({
            description => format!("K source:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_snapshot!(outline);
        });
    }};
}

/// A test that `source` parses, with the [`outer_outline`] of its outer AST as the snapshot.
macro_rules! outer_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = $source;
            let parsed = parse(concat!(stringify!($name), ".k"), source).unwrap();
            assert_outline_snapshot!(source, outer_outline(&parsed));
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
fn imports_default_to_private_inside_a_private_module() {
    let parsed = parse(
        "private-module.k",
        "module PRIVATE [private]\n  imports BASE\nendmodule\n",
    )
    .unwrap();

    assert!(!parsed.modules[0].imports[0].public);
}

#[test]
fn explicit_public_import_inside_a_private_module_stays_public() {
    let parsed = parse(
        "private-module.k",
        "module PRIVATE [private]\n  imports public BASE\nendmodule\n",
    )
    .unwrap();

    assert!(parsed.modules[0].imports[0].public);
}

#[test]
fn sentence_boundaries_follow_outer_jj_token_rules() {
    let parsed = parse(
        "one-line-rules.k",
        "module M syntax Foo ::= \"a\" | \"b\" rule a => b rule b => a endmodule",
    )
    .unwrap();
    assert_eq!(parsed.modules[0].sentences.len(), 3);
    let bubbles = parsed.modules[0]
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Bubble(bubble) => Some(bubble.content.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(bubbles, ["a => b", "b => a"]);

    let parsed = parse(
        "one-line-syntax.k",
        "module M syntax Foo ::= \"c\" syntax Bar ::= \"d\" rule c => c endmodule",
    )
    .unwrap();
    assert_eq!(parsed.modules[0].sentences.len(), 3);
    assert!(matches!(
        parsed.modules[0].sentences.as_slice(),
        [
            Sentence::Syntax(_),
            Sentence::Syntax(_),
            Sentence::Bubble(_)
        ]
    ));

    let parsed = parse(
        "one-line-states.k",
        "module M syntax priority a > b rule x => y context alias [c]: HERE = HOLE context HOLE endmodule",
    )
    .unwrap();
    assert!(matches!(
        parsed.modules[0].sentences.as_slice(),
        [
            Sentence::Priority(_),
            Sentence::Bubble(k_rust::outer::Bubble {
                kind: k_rust::outer::BubbleKind::Rule,
                ..
            }),
            Sentence::Bubble(k_rust::outer::Bubble {
                kind: k_rust::outer::BubbleKind::ContextAlias,
                ..
            }),
            Sentence::Bubble(k_rust::outer::Bubble {
                kind: k_rust::outer::BubbleKind::Context,
                ..
            }),
        ]
    ));

    let parsed = parse(
        "no-string-state.k",
        "module M rule X => \"a syntax Foo endmodule",
    )
    .unwrap();
    let Sentence::Bubble(bubble) = &parsed.modules[0].sentences[0] else {
        panic!("expected a rule bubble")
    };
    assert_eq!(bubble.content, "X => \"a");
    assert!(matches!(
        parsed.modules[0].sentences[1],
        Sentence::Syntax(_)
    ));
}

#[test]
fn imports_are_rejected_after_the_first_sentence() {
    let error = parse(
        "imports-after-sentence.k",
        indoc! {r#"
            module BASE
              syntax Foo ::= "foo"
            endmodule
            module MAIN
              syntax Bar ::= "bar"
              imports BASE
              rule foo => .K
            endmodule
        "#},
    )
    .unwrap_err();

    assert_eq!(
        error.message,
        "unexpected `imports` after the first sentence"
    );
    assert_eq!((error.position.line, error.position.column), (6, 3));
}

#[test]
fn sentence_bubbles_use_longest_whitespace_delimited_tokens() {
    let parsed = parse(
        "bubble-tokens.k",
        indoc! {r#"
            module M
              rule first // syntax is comment text
                   => value rules rule( b//syntax rule second => value
            endmodule
        "#},
    )
    .unwrap();
    let bubbles = parsed.modules[0]
        .sentences
        .iter()
        .map(|sentence| match sentence {
            Sentence::Bubble(bubble) => bubble.content.as_str(),
            _ => panic!("expected only rule bubbles"),
        })
        .collect::<Vec<_>>();
    assert_eq!(bubbles.len(), 2);
    assert!(bubbles[0].contains("// syntax is comment text"));
    assert!(bubbles[0].contains("rules rule( b//syntax"));
    assert_eq!(bubbles[1], "second => value");

    let parsed = parse(
        "unclosed-comment.k",
        "module M rule X /* remains bubble text endmodule",
    )
    .unwrap();
    let Sentence::Bubble(bubble) = &parsed.modules[0].sentences[0] else {
        panic!("expected a rule bubble")
    };
    assert_eq!(bubble.content, "X /* remains bubble text");
}

#[test]
fn sentence_spans_end_at_the_last_token() {
    let source = indoc! {r#"
        module M
          syntax Foo ::= "x" // syntax comment
          syntax priority a > b // priority comment
          rule X => X // rule comment
        endmodule
    "#};
    let parsed = parse("sentence-spans.k", source).unwrap();
    let [
        Sentence::Syntax(syntax),
        Sentence::Priority(priority),
        Sentence::Bubble(rule),
    ] = parsed.modules[0].sentences.as_slice()
    else {
        panic!("expected syntax, priority, and rule sentences")
    };

    assert_eq!(syntax.span.end.offset, source.find(" // syntax").unwrap());
    let k_rust::outer::SyntaxBody::Productions(blocks) = &syntax.body else {
        panic!("expected a syntax production")
    };
    assert_eq!(blocks[0].span.end.offset, syntax.span.end.offset);
    assert_eq!(
        priority.span.end.offset,
        source.find(" // priority").unwrap()
    );
    assert_eq!(rule.span.end.offset, source.find(" // rule").unwrap());
    assert_eq!(rule.content_span.end.offset, rule.span.end.offset);
    assert_eq!(rule.content, "X => X");
}

#[test]
fn lowering_preserves_bubble_content_offsets() {
    fn content_start_offset(source_name: &str, source: &str) -> usize {
        let lowered = lower(&parse(source_name, source).unwrap(), "MAIN").unwrap();
        let k_rust::definition::Sentence::Bubble { attributes, .. } =
            &*lowered.main_module().unwrap().local_sentences[0]
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
      syntax lexical Identifier = r"[a-z]+"
    endmodule
"#}
);

#[test]
fn strict_outer_rejects_invalid_module_names() {
    for (source, invalid) in [
        ("module 1MAIN\n  syntax Foo ::= \"x\"\nendmodule\n", "1MAIN"),
        (
            "module MAIN\n  imports LIB-\n  syntax Foo ::= \"x\"\nendmodule\n",
            "LIB-",
        ),
        (
            "module public\n  syntax Foo ::= \"x\"\nendmodule\n",
            "public",
        ),
    ] {
        let error = parse("invalid-module-name.k", source).unwrap_err();
        assert_eq!(error.message, "invalid module name");
        assert_eq!(error.position.offset, source.find(invalid).unwrap());
    }
}

#[test]
fn strict_outer_accepts_identifier_boundaries() {
    let source = indoc! {r#"
        module M_1-2_X
          syntax #Foo
          syntax 123
          syntax Bar
          syntax Result ::= #foo(Bar) | #field:Bar
        endmodule
    "#};
    let parsed = parse("valid-outer-identifiers.k", source).unwrap();

    assert_eq!(parsed.modules[0].name, "M_1-2_X");
    let Sentence::Syntax(hash_sort) = &parsed.modules[0].sentences[0] else {
        panic!("expected #Foo declaration")
    };
    let Sentence::Syntax(numeric_sort) = &parsed.modules[0].sentences[1] else {
        panic!("expected numeric sort declaration")
    };
    assert_eq!(hash_sort.sort.name, "#Foo");
    assert_eq!(numeric_sort.sort.name, "123");
}

#[test]
fn strict_outer_rejects_invalid_sort_and_production_identifiers() {
    for (source, message, invalid) in [
        (
            "module MAIN\n  syntax foo ::= \"x\"\nendmodule\n",
            "invalid sort name",
            "foo",
        ),
        (
            "module MAIN\n  syntax Foo_Bar ::= \"x\"\nendmodule\n",
            "invalid sort name",
            "Foo_Bar",
        ),
        (
            "module MAIN\n  syntax Foo ::= bar\nendmodule\n",
            "invalid sort name",
            "bar",
        ),
        (
            "module MAIN\n  syntax Bar\n  syntax Foo ::= x_y:Bar\nendmodule\n",
            "invalid nonterminal name",
            "x_y",
        ),
        (
            "module MAIN\n  syntax Bar\n  syntax Foo ::= foo_bar(Bar)\nendmodule\n",
            "invalid production name",
            "foo_bar",
        ),
    ] {
        let error = parse("invalid-outer-identifier.k", source).unwrap_err();
        assert_eq!(error.message, message, "source:\n{source}");
        assert_eq!(
            error.position.offset,
            source.find(invalid).unwrap(),
            "source:\n{source}"
        );
    }
}

#[test]
fn strict_outer_accepts_named_and_parameterized_sort_ids() {
    let source = indoc! {r#"
        module MAIN
          syntax child:Child ::= "x"
          syntax lexical token:Token = r"x"
          syntax lexical Parametric{Parameter} = r"y"
          syntax newSort:NewSort = oldSort:OldSort
        endmodule
    "#};
    let parsed = parse("valid-named-sort-ids.k", source).unwrap();
    let [
        Sentence::Syntax(syntax),
        Sentence::Lexical(named_lexical),
        Sentence::Lexical(parameterized_lexical),
        Sentence::Syntax(synonym),
    ] = parsed.modules[0].sentences.as_slice()
    else {
        panic!("expected two syntax and two lexical declarations")
    };

    assert_eq!(syntax.sort.name, "Child");
    assert_eq!(syntax.name.as_deref(), Some("child"));
    assert_eq!(named_lexical.name, "Token");
    assert_eq!(parameterized_lexical.name, "Parametric");
    assert_eq!(synonym.sort.name, "NewSort");
    let k_rust::outer::SyntaxBody::Synonym { old_sort, .. } = &synonym.body else {
        panic!("expected a sort synonym")
    };
    assert_eq!(old_sort.name, "OldSort");
    assert_eq!(synonym.name, None);
}

#[test]
fn strict_outer_rejects_invalid_terminal_regex_list_and_require_strings() {
    for (source, message, marker, adjustment) in [
        (
            "module MAIN\n  syntax Foo ::= \"a\\q\"\nendmodule\n",
            r"invalid escape `\q` in string",
            r"\q",
            0,
        ),
        (
            "module MAIN\n  syntax Foo ::= \"a\nb\"\nendmodule\n",
            "newline in string",
            "\"a\nb\"",
            2,
        ),
        (
            "module MAIN\n  syntax Foo ::= r\"a\\q\" [token]\nendmodule\n",
            r"invalid escape `\q` in string",
            r"\q",
            0,
        ),
        (
            "module MAIN\n  syntax Foo ::= r\"a\nb\" [token]\nendmodule\n",
            "newline in string",
            "\"a\nb\"",
            2,
        ),
        (
            "module MAIN\n  syntax S\n  syntax Ss ::= List{S, \"a\\q\"}\nendmodule\n",
            r"invalid escape `\q` in string",
            r"\q",
            0,
        ),
        (
            "module MAIN\n  syntax S\n  syntax Ss ::= List{S, \"a\nb\"}\nendmodule\n",
            "newline in string",
            "\"a\nb\"",
            2,
        ),
        (
            "requires \"dep\\q.k\"\nmodule MAIN endmodule\n",
            r"invalid escape `\q` in string",
            r"\q",
            0,
        ),
        (
            "requires \"dep\n.k\"\nmodule MAIN endmodule\n",
            "newline in string",
            "\"dep\n.k\"",
            4,
        ),
    ] {
        let error = parse("invalid-string.k", source).unwrap_err();
        assert_eq!(
            error.message,
            message,
            "source bytes: {:?}",
            source.as_bytes()
        );
        assert_eq!(
            error.position.offset,
            source.find(marker).unwrap() + adjustment,
            "source bytes: {:?}",
            source.as_bytes()
        );
    }
}

#[test]
fn strict_outer_decodes_legal_strings_once_in_every_context() {
    let source = concat!(
        "requires \"raw\rpath.k\"\n",
        "requires \"escaped\\npath.k\"\n",
        "requires \"Q\\\"N\\nR\\rT\\tB\\\\C\rZ\"\n",
        "module MAIN\n",
        "  syntax S\n",
        "  syntax Term ::= \"Q\\\"N\\nR\\rT\\tB\\\\C\rZ\"\n",
        "  syntax Token ::= r\"a\\\\+Q\\\"N\\nR\\rT\\tB\\\\C\rZ\" [token]\n",
        "  syntax Ss ::= List{S, \"Q\\\"N\\nR\\rT\\tB\\\\C\rZ\"}\n",
        "endmodule\n",
    );
    let parsed = parse("valid-strings.k", source).unwrap();

    assert_eq!(parsed.requires[0].path, "raw\rpath.k");
    assert_eq!(parsed.requires[1].path, "escaped\npath.k");
    assert_eq!(parsed.requires[2].path, "Q\"N\nR\rT\tB\\C\rZ");
    let [
        Sentence::Syntax(_),
        Sentence::Syntax(terminal),
        Sentence::Syntax(regex),
        Sentence::Syntax(list),
    ] = parsed.modules[0].sentences.as_slice()
    else {
        panic!("expected four syntax declarations")
    };
    let k_rust::outer::SyntaxBody::Productions(terminal_blocks) = &terminal.body else {
        panic!("expected terminal production")
    };
    assert_eq!(
        terminal_blocks[0].productions[0].items,
        [k_rust::outer::ProductionItem::Terminal(
            "Q\"N\nR\rT\tB\\C\rZ".into()
        )]
    );
    let k_rust::outer::SyntaxBody::Productions(regex_blocks) = &regex.body else {
        panic!("expected regex production")
    };
    assert_eq!(
        regex_blocks[0].productions[0].items,
        [k_rust::outer::ProductionItem::Regex(
            "a\\+Q\"N\nR\rT\tB\\C\rZ".into()
        )]
    );
    let k_rust::outer::SyntaxBody::Productions(list_blocks) = &list.body else {
        panic!("expected list production")
    };
    let [k_rust::outer::ProductionItem::UserList { separator, .. }] =
        list_blocks[0].productions[0].items.as_slice()
    else {
        panic!("expected one user-list item")
    };
    assert_eq!(separator, "Q\"N\nR\rT\tB\\C\rZ");
}

#[test]
fn strict_outer_rejects_unsupported_production_forms() {
    for (source, message, invalid) in [
        (
            "module MAIN\n  syntax Foo ::= ()\nendmodule\n",
            "parenthesized production requires at least one sort",
            ")",
        ),
        (
            "module MAIN\n  syntax Bar\n  syntax Foo ::= foo(Bar) \"x\"\nendmodule\n",
            "function-style production must be the whole production",
            "\"x\"",
        ),
    ] {
        let error = parse("invalid-production-form.k", source).unwrap_err();
        assert_eq!(error.message, message);
        assert_eq!(error.position.offset, source.find(invalid).unwrap());
    }
}

#[test]
fn strict_outer_rejects_lexical_attributes_and_parameterized_list_elements() {
    for (source, message, invalid) in [
        (
            "module MAIN\n  syntax lexical Identifier = r\"[a-z]+\" [prec(1)]\nendmodule\n",
            "syntax lexical does not accept attributes",
            "[prec(1)]",
        ),
        (
            "module MAIN\n  syntax Ss ::= List{S{T}, \",\"}\nendmodule\n",
            "list element sort cannot have parameters",
            "{T},",
        ),
    ] {
        let error = parse("invalid-special-production.k", source).unwrap_err();
        assert_eq!(error.message, message);
        assert_eq!(error.position.offset, source.find(invalid).unwrap());
    }
}

#[test]
fn strict_outer_rejects_empty_and_numeric_sort_parameters() {
    for (source, message, invalid) in [
        (
            "module MAIN\n  syntax {} Foo ::= \"x\"\nendmodule\n",
            "sort parameter list requires at least one sort",
            "}",
        ),
        (
            "module MAIN\n  syntax Foo{} ::= \"x\"\nendmodule\n",
            "sort parameter list requires at least one sort",
            "}",
        ),
        (
            "module MAIN\n  syntax Foo ::= Bar{}\nendmodule\n",
            "sort parameter list requires at least one sort",
            "}",
        ),
        (
            "module MAIN\n  syntax Foo ::= 123{Bar}\nendmodule\n",
            "numeric sort cannot take parameters",
            "{Bar}",
        ),
    ] {
        let error = parse("invalid-sort-parameters.k", source).unwrap_err();
        assert_eq!(error.message, message);
        assert_eq!(error.position.offset, source.find(invalid).unwrap());
    }
}

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
fn bubble_attributes_and_labels_follow_make_string_sentence() {
    let source = indoc! {r#"
        module MAIN
          rule a => b[priority(50)]
          rule X => [Item]
          rule L => [x]
          rule Y => [other] [simplification]
          rule Z => PATH[0]
          rule [foo_bar]: a => b
          rule [foo-bar]: a => b
        endmodule
    "#};
    let parsed = parse("bubble-parts.k", source).unwrap();
    let bubbles = parsed.modules[0]
        .sentences
        .iter()
        .map(|sentence| match sentence {
            Sentence::Bubble(bubble) => bubble,
            _ => panic!("expected only rule bubbles"),
        })
        .collect::<Vec<_>>();

    assert_eq!(bubbles[0].content, "a => b");
    assert_eq!(bubbles[0].attributes[0].key, "priority");
    assert_eq!(bubbles[0].attributes[0].value.as_deref(), Some("50"));

    assert_eq!(bubbles[1].content, "X => [Item]");
    assert!(bubbles[1].attributes.is_empty());

    assert_eq!(bubbles[2].content, "L =>");
    assert_eq!(bubbles[2].attributes[0].key, "x");

    assert_eq!(bubbles[3].content, "Y => [other]");
    assert_eq!(bubbles[3].attributes[0].key, "simplification");

    assert_eq!(bubbles[4].content, "Z => PATH[0]");
    assert!(bubbles[4].attributes.is_empty());

    assert_eq!(bubbles[5].label, None);
    assert_eq!(bubbles[5].content, "[foo_bar]: a => b");
    assert_eq!(bubbles[6].label.as_deref(), Some("foo-bar"));
    assert_eq!(bubbles[6].content, "a => b");
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
fn attribute_strings_are_decoded_once_with_k_escapes() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "a" [format("\"%1\""), hook("INT.add"), foo("a\\b"), edge( x)]
        endmodule
    "#};
    let parsed = parse("attribute-strings.k", source).unwrap();
    let Sentence::Syntax(syntax) = &parsed.modules[0].sentences[0] else {
        panic!("expected syntax declaration")
    };
    let k_rust::outer::SyntaxBody::Productions(blocks) = &syntax.body else {
        panic!("expected syntax productions")
    };
    let attributes = &blocks[0].productions[0].attributes;

    assert_eq!(attributes[0].value.as_deref(), Some("\"%1\""));
    assert_eq!(attributes[1].value.as_deref(), Some("INT.add"));
    assert_eq!(attributes[2].value.as_deref(), Some(r"a\b"));
    assert_eq!(attributes[3].value.as_deref(), Some(" x"));

    let definition = lower(&parsed, "MAIN").unwrap();
    let lowered_attributes = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            k_rust::definition::Sentence::Production { attributes, .. } => Some(attributes),
            _ => None,
        })
        .expect("expected lowered production");
    assert_eq!(lowered_attributes.get_str("format"), Some("\"%1\""));
    assert_eq!(lowered_attributes.get_str("hook"), Some("INT.add"));
    assert_eq!(lowered_attributes.get_str("foo"), Some(r"a\b"));
    assert_eq!(lowered_attributes.get_str("edge"), Some(" x"));

    let invalid_escape = parse(
        "invalid-attribute-escape.k",
        "module MAIN\nsyntax Foo ::= \"a\" [foo(\"\\A\")]\nendmodule\n",
    )
    .unwrap_err();
    assert_eq!(
        invalid_escape.message,
        r"invalid escape `\A` in attribute string"
    );

    let raw_newline = parse(
        "newline-in-attribute-string.k",
        "module MAIN\nsyntax Foo ::= \"a\" [foo(\"a\nb\")]\nendmodule\n",
    )
    .unwrap_err();
    assert_eq!(raw_newline.message, "newline in attribute string");

    let unquoted_quote = parse(
        "quote-in-unquoted-attribute.k",
        "module MAIN\nsyntax Foo ::= \"a\" [foo(a\"b\")]\nendmodule\n",
    )
    .unwrap_err();
    assert_eq!(unquoted_quote.message, "quote in unquoted attribute value");
}

#[test]
fn rejects_duplicate_attribute_keys_before_lowering_loses_them() {
    let source = "module MAIN\nsyntax Exp ::= \"x\" [symbol(first), symbol(second)]\nendmodule\n";
    let error = parse("duplicate-attribute.k", source).unwrap_err();

    assert_eq!(error.message, "Duplicate attribute: symbol");
}

#[test]
fn attribute_parameters_follow_att_add_arity() {
    let parse_production = |attributes: &str| {
        let source = format!("module MAIN\n  syntax Foo ::= \"a\" {attributes}\nendmodule\n");
        parse("attribute-arity.k", &source)
    };

    for (attributes, message) in [
        (
            "[function(x)]",
            "Parameters for the attribute 'function' are forbidden.",
        ),
        (
            "[klabel]",
            "Parameters for the attribute 'klabel' are required.",
        ),
        (
            r#"[format("")]"#,
            "Parameters for the attribute 'format' are required.",
        ),
    ] {
        let error = parse_production(attributes).unwrap_err();
        assert_eq!(error.message, message, "attributes: {attributes}");
    }

    let error = parse(
        "attribute-arity.k",
        "module MAIN\n  syntax Foo [hook]\nendmodule\n",
    )
    .unwrap_err();
    assert_eq!(
        error.message,
        "Parameters for the attribute 'hook' are required."
    );

    for attributes in [
        "[symbol]",
        "[symbol(x)]",
        "[concrete]",
        "[concrete(X)]",
        "[strict]",
        "[strict(1)]",
        "[unknownkey(x)]",
    ] {
        parse_production(attributes)
            .unwrap_or_else(|error| panic!("{attributes} should parse: {error}"));
    }
}

#[test]
fn trailing_attribute_candidates_abort_on_fatal_attribute_errors() {
    let duplicate = parse(
        "duplicate-attribute-rule.k",
        "module MAIN\n  rule X => Y [concrete, concrete]\nendmodule\n",
    )
    .unwrap_err();
    assert_eq!(duplicate.message, "Duplicate attribute: concrete");

    let arity = parse(
        "forbidden-attribute-rule.k",
        "module MAIN\n  rule a() => .K [owise(1)]\nendmodule\n",
    )
    .unwrap_err();
    assert_eq!(
        arity.message,
        "Parameters for the attribute 'owise' are forbidden."
    );
}

#[test]
fn internal_keys_and_group_values_are_checked_on_user_source() {
    let internal = parse(
        "internal-attribute.k",
        "module MAIN\n  syntax Foo ::= \"a\" [userList(*), bracketLabel(foo)]\nendmodule\n",
    )
    .unwrap();
    let diagnostics = lower(&internal, "MAIN").unwrap_err();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::UnrecognizedAttribute);
    assert_eq!(
        diagnostics[0].message,
        "Unrecognized attributes: [bracketLabel, userList]"
    );

    let invalid_group = parse(
        "invalid-group.k",
        "module MAIN\n  syntax Foo ::= \"a\" [group(Foo)]\nendmodule\n",
    )
    .unwrap();
    let diagnostics = lower(&invalid_group, "MAIN").unwrap_err();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidAttribute);
    assert_eq!(
        diagnostics[0].message,
        "group(_) attribute expects a comma separated list of groups, each of which consists of a lower case letter followed by any number of alphanumeric or '-' characters."
    );

    let valid_group = parse(
        "valid-group.k",
        "module MAIN\n  syntax Foo ::= \"a\" [group(a, b-c)]\nendmodule\n",
    )
    .unwrap();
    lower(&valid_group, "MAIN").unwrap();
}

#[test]
fn structured_json_internal_keys_remain_accepted() {
    let parsed = parse(
        "structured-user-list.k",
        "module MAIN\n  syntax Item\n  syntax Items ::= List{Item, \",\"}\nendmodule\n",
    )
    .unwrap();
    let definition = lower(&parsed, "MAIN").unwrap();
    assert!(
        definition.modules[0]
            .local_sentences
            .iter()
            .any(|sentence| { sentence.attributes().get("userList").is_some() })
    );

    let encoded = definition_json::to_string(&definition).unwrap();
    let decoded = definition_json::from_str(&encoded).unwrap();
    let loaded = load_structured(decoded, &LoadOptions::default()).unwrap();
    assert!(
        loaded.definition().modules[0]
            .local_sentences
            .iter()
            .any(|sentence| sentence.attributes().get("userList").is_some())
    );
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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

#[test]
fn bracket_label_uses_the_declared_symbol() {
    let source = indoc! {r#"
        module BRACKET-LABELS
          syntax Exp ::= "(" Exp ")" [bracket, symbol( paren)]
                       > "[" Exp "]" [bracket]
                       > "{" Exp "}" [bracket, klabel(curly)]
        endmodule
    "#};
    let definition = lower(
        &parse("bracket-labels.k", source).expect("definition should parse"),
        "BRACKET-LABELS",
    )
    .expect("definition should lower");
    let sentences = &definition.main_module().unwrap().local_sentences;

    let bracket_label = |opening: &str| {
        sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                k_rust::definition::Sentence::Production {
                    items, attributes, ..
                } if items.first()
                    == Some(&k_rust::definition::ProductionItem::Terminal(
                        opening.into(),
                    )) =>
                {
                    attributes.get("bracketLabel")
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("missing bracket production beginning with {opening:?}"))
    };

    assert_eq!(
        bracket_label("("),
        &serde_json::json!({"node": "KLabel", "name": "paren", "params": []})
    );
    assert_eq!(
        bracket_label("["),
        &serde_json::json!({
            "node": "KLabel",
            "name": "[_]_BRACKET-LABELS_Exp_Exp",
            "params": []
        })
    );
    assert_eq!(
        bracket_label("{"),
        &serde_json::json!({
            "node": "KLabel",
            "name": "{_}_BRACKET-LABELS_Exp_Exp",
            "params": []
        })
    );

    let priorities = sentences.iter().find_map(|sentence| match &**sentence {
        k_rust::definition::Sentence::SyntaxPriority { priorities, .. } => Some(priorities),
        _ => None,
    });
    assert_eq!(
        priorities,
        Some(&vec![
            vec!["paren".into()],
            vec!["[_]_BRACKET-LABELS_Exp_Exp".into()],
            vec!["{_}_BRACKET-LABELS_Exp_Exp".into()],
        ])
    );
}

#[test]
fn priority_tags_resolve_through_context_tags() {
    let anonymous_source = include_str!("fixtures/reference/outer/priority-anonymous-tag/test.k");
    let anonymous = parse("priority-anonymous-tag.k", anonymous_source).unwrap();
    let diagnostics = lower(&anonymous, "PRIORITY-ANONYMOUS-TAG").unwrap_err();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::UndeclaredTag);
    assert_eq!(
        diagnostics[0].message,
        "Could not find any productions for tag: _*_"
    );
    assert_eq!(
        diagnostics[0].source.as_deref(),
        Some("priority-anonymous-tag.k")
    );
    let location = diagnostics[0].location.expect("priority sentence location");
    assert_eq!(
        (
            location.start_line,
            location.start_column,
            location.end_line,
            location.end_column,
        ),
        (4, 3, 4, 28)
    );
    let reference = include_str!("fixtures/reference/outer/priority-anonymous-tag/diagnostic.txt");
    assert!(reference.contains(&diagnostics[0].message));
    assert!(reference.contains("Location(4,3,4,28)"));

    let unknown_source = include_str!("fixtures/reference/outer/priority-unknown-tag/test.k");
    let unknown = parse("priority-unknown-tag.k", unknown_source).unwrap();
    let diagnostics = lower(&unknown, "PRIORITY-UNKNOWN-TAG").unwrap_err();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::UndeclaredTag);
    assert_eq!(
        diagnostics[0].message,
        "Could not find any productions for tag: nosuchtag"
    );
    assert_eq!(
        diagnostics[0].source.as_deref(),
        Some("priority-unknown-tag.k")
    );
    let location = diagnostics[0].location.expect("priority sentence location");
    assert_eq!(
        (
            location.start_line,
            location.start_column,
            location.end_line,
            location.end_column,
        ),
        (3, 3, 3, 32)
    );
    let reference = include_str!("fixtures/reference/outer/priority-unknown-tag/diagnostic.txt");
    assert!(reference.contains(&diagnostics[0].message));
    assert!(reference.contains("Location(3,3,3,32)"));

    let associativity_source = indoc! {r#"
        module ASSOCIATIVITY-UNKNOWN-TAG
          syntax Foo ::= "a" [symbol(a)]
          syntax left nosuchtag
        endmodule
    "#};
    let associativity = parse("associativity-unknown-tag.k", associativity_source).unwrap();
    let diagnostics = lower(&associativity, "ASSOCIATIVITY-UNKNOWN-TAG").unwrap_err();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::UndeclaredTag);
    assert_eq!(
        diagnostics[0].message,
        "Could not find any productions for tag: nosuchtag"
    );
    let location = diagnostics[0]
        .location
        .expect("associativity sentence location");
    assert_eq!(
        (
            location.start_line,
            location.start_column,
            location.end_line,
            location.end_column,
        ),
        (3, 3, 3, 24)
    );

    let valid_source = indoc! {r#"
        module TAGS
          syntax Exp ::= "foo" [symbol(foo)]
                       | "bar" [symbol(bar)]
                       | Exp "+" Exp
                       | Exp "*" Exp [group(mult)]
                       | "(" Exp ")" [bracket, symbol(paren)]
                       | Exp "-" Exp [klabel(minus)]
          syntax priority foo > bar
          syntax left _+__TAGS
          syntax right mult
          syntax non-assoc paren
          syntax priority minus > foo
        endmodule
    "#};
    let definition = lower(&parse("valid-tags.k", valid_source).unwrap(), "TAGS").unwrap();
    let sentences = &definition.main_module().unwrap().local_sentences;
    let priorities = sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            k_rust::definition::Sentence::SyntaxPriority { priorities, .. } => Some(priorities),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        priorities,
        vec![
            &vec![vec!["foo".to_owned()], vec!["bar".to_owned()]],
            &vec![
                vec!["_-__TAGS_Exp_Exp_Exp".to_owned()],
                vec!["foo".to_owned()],
            ],
        ]
    );

    let associativity_tags = |expected| {
        sentences.iter().find_map(|sentence| match &**sentence {
            k_rust::definition::Sentence::SyntaxAssociativity {
                associativity,
                tags,
                ..
            } if *associativity == expected => Some(tags),
            _ => None,
        })
    };
    assert_eq!(
        associativity_tags(k_rust::definition::Associativity::Left),
        Some(&vec!["_+__TAGS_Exp_Exp_Exp".to_owned()])
    );
    assert_eq!(
        associativity_tags(k_rust::definition::Associativity::Right),
        Some(&vec!["_*__TAGS_Exp_Exp_Exp".to_owned()])
    );
    assert_eq!(
        associativity_tags(k_rust::definition::Associativity::NonAssoc),
        Some(&vec!["paren".to_owned()])
    );
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

outer_snapshot!(
    bracket_rewrite_rhs_is_not_mistaken_for_attributes,
    indoc! {r#"
    module BRACKET-RHS
      rule X => [item]
      rule Y => [other] [simplification]
      rule Z => PATH[0]
    endmodule
"#}
);

/// A list declaration `S ::= List{E, sep}` is accepted only as a whole production whose sort
/// `S` is neither `K` nor its own element sort `E`: each of the other three shapes gets its own
/// diagnostic, and an `NeList` of another sort is accepted.
#[test]
fn list_declarations_of_k_of_their_own_element_or_inline_are_rejected() {
    let source = indoc! {r#"
        module LISTS
          syntax K ::= List{Exp, ","}
          syntax Loop ::= List{Loop, ","}
          syntax Exps ::= "[" List{Exp, ","} "]"
          syntax Good ::= NeList{Exp, ","}
        endmodule
    "#};
    let parsed = parse("lists.k", source).unwrap();

    assert_outline_snapshot!(
        source,
        diagnostics_outline(&check_list_declarations(&parsed))
    );
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

    assert_outline_snapshot!(source, outer_outline(&parsed));
}

#[test]
fn comments_can_touch_default_and_module_name_tokens() {
    let source = concat!(
        "module/* before module name */MAIN/* after module name */\n",
        "  imports/* before import name */LIB/* after import name */\n",
        "  syntax/* before named sort */child/* before colon */:/* before sort */Child",
        "/* after sort */ ::= field/* before field colon */:/* before field sort */Child\n",
        "  syntax/* before line sort */Line// after line sort\n",
        "endmodule\n",
    );
    let parsed = parse("adjacent-comments.k", source).unwrap();

    let module = &parsed.modules[0];
    assert_eq!(module.name, "MAIN");
    assert_eq!(module.imports[0].module, "LIB");
    let [Sentence::Syntax(named), Sentence::Syntax(line)] = module.sentences.as_slice() else {
        panic!("expected two syntax declarations")
    };
    assert_eq!(named.name.as_deref(), Some("child"));
    assert_eq!(named.sort.name, "Child");
    let k_rust::outer::SyntaxBody::Productions(blocks) = &named.body else {
        panic!("expected a production declaration")
    };
    let [k_rust::outer::ProductionItem::NonTerminal { name, sort }] =
        blocks[0].productions[0].items.as_slice()
    else {
        panic!("expected one named nonterminal")
    };
    assert_eq!(name.as_deref(), Some("field"));
    assert_eq!(sort.name, "Child");
    assert_eq!(line.sort.name, "Line");

    assert_eq!(module.span.start.offset, source.find("module").unwrap());
    assert_eq!(
        module.imports[0].span.end.offset,
        source.find("/* after import name */").unwrap()
    );
    assert_eq!(
        named.span.start.offset,
        source.find("syntax/* before named sort */").unwrap()
    );
    assert_eq!(
        named.span.end.offset,
        source.find("\n  syntax/* before line sort */Line").unwrap()
    );
}

#[test]
fn line_comments_follow_outer_jj_terminators() {
    for terminator in ["\r", "\r\n", "\n"] {
        let source =
            format!("module MAIN imports LIB// import comment{terminator} syntax Foo endmodule");
        let parsed = parse("line-comment.k", &source).unwrap();
        assert_eq!(parsed.modules[0].imports[0].module, "LIB");
        let [Sentence::Syntax(syntax)] = parsed.modules[0].sentences.as_slice() else {
            panic!("expected one syntax declaration")
        };
        assert_eq!(syntax.sort.name, "Foo");
    }

    assert!(
        parse(
            "unterminated-line-comment.k",
            "module MAIN endmodule// unterminated"
        )
        .is_err()
    );
}

#[test]
fn pinned_outer_corpus_families_parse_and_lower() {
    let source = include_str!("fixtures/outer/record-and-list.k");
    let parsed = parse("record-and-list.k", source).unwrap();
    let mut lowered = lower(&parsed, "OUTER-CORPUS").unwrap();
    for module in &mut lowered.modules {
        for sentence in &mut module.local_sentences {
            let sentence = k_rust::definition::sentence_mut(sentence);
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
        insta::assert_snapshot!("pinned_outer_corpus_outline", outer_outline(&parsed));
        insta::assert_snapshot!("pinned_outer_lowering_outline", lowered_outline(&lowered));
    });
}

/// A line-per-node outline of an outer AST that names each field it prints.
///
/// The outline is written field by field rather than derived from `Debug`, so a field added to
/// an AST struct leaves it unchanged until the field is printed here. Every enum is matched
/// without a wildcard, so a new variant must be given a spelling before the test compiles.
fn outer_outline(parsed: &k_rust::outer::SourceFile) -> String {
    use k_rust::outer::{BubbleKind, PriorityBlock, ProductionItem, SyntaxBody};

    let mut out = String::new();
    writeln!(out, "source {:?} id {}", parsed.source, parsed.source_id.0).unwrap();
    for require in &parsed.requires {
        writeln!(
            out,
            "requires {:?} {}",
            require.path,
            outer_span(&require.span)
        )
        .unwrap();
    }
    for module in &parsed.modules {
        writeln!(
            out,
            "module {}{} {}",
            module.name,
            outer_attributes(&module.attributes),
            outer_span(&module.span)
        )
        .unwrap();
        for import in &module.imports {
            let visibility = if import.public { "public" } else { "private" };
            writeln!(
                out,
                "  imports {visibility} {} {}",
                import.module,
                outer_span(&import.span)
            )
            .unwrap();
        }
        for sentence in &module.sentences {
            match sentence {
                Sentence::Syntax(syntax) => {
                    let name = syntax
                        .name
                        .as_ref()
                        .map(|name| format!(" name {name:?}"))
                        .unwrap_or_default();
                    write!(
                        out,
                        "  syntax{} {}{name}",
                        outer_sort_parameters(&syntax.parameters),
                        syntax.sort
                    )
                    .unwrap();
                    match &syntax.body {
                        SyntaxBody::Sort(attributes) => {
                            writeln!(
                                out,
                                "{} {}",
                                outer_attributes(attributes),
                                outer_span(&syntax.span)
                            )
                            .unwrap();
                        }
                        SyntaxBody::Synonym {
                            old_sort,
                            attributes,
                        } => {
                            writeln!(
                                out,
                                " = {old_sort}{} {}",
                                outer_attributes(attributes),
                                outer_span(&syntax.span)
                            )
                            .unwrap();
                        }
                        SyntaxBody::Productions(blocks) => {
                            writeln!(out, " ::= {}", outer_span(&syntax.span)).unwrap();
                            for PriorityBlock {
                                associativity,
                                productions,
                                span,
                            } in blocks
                            {
                                writeln!(
                                    out,
                                    "    block {} {}",
                                    outer_associativity(*associativity),
                                    outer_span(span)
                                )
                                .unwrap();
                                for production in productions {
                                    writeln!(
                                        out,
                                        "      production{} {}",
                                        outer_attributes(&production.attributes),
                                        outer_span(&production.span)
                                    )
                                    .unwrap();
                                    for item in &production.items {
                                        match item {
                                            ProductionItem::Terminal(text) => {
                                                writeln!(out, "        terminal {text:?}")
                                            }
                                            ProductionItem::Regex(regex) => {
                                                writeln!(out, "        regex {regex:?}")
                                            }
                                            ProductionItem::NonTerminal { name: None, sort } => {
                                                writeln!(out, "        nonterminal {sort}")
                                            }
                                            ProductionItem::NonTerminal {
                                                name: Some(name),
                                                sort,
                                            } => {
                                                writeln!(out, "        nonterminal {name}: {sort}")
                                            }
                                            ProductionItem::UserList {
                                                sort,
                                                separator,
                                                non_empty,
                                            } => {
                                                let list =
                                                    if *non_empty { "NeList" } else { "List" };
                                                writeln!(
                                                    out,
                                                    "        {list}{{{sort}, {separator:?}}}"
                                                )
                                            }
                                        }
                                        .unwrap();
                                    }
                                }
                            }
                        }
                    }
                }
                Sentence::Priority(priority) => {
                    let groups = priority
                        .groups
                        .iter()
                        .map(|group| format!("{group:?}"))
                        .collect::<Vec<_>>()
                        .join(" > ");
                    writeln!(out, "  priority {groups} {}", outer_span(&priority.span)).unwrap();
                }
                Sentence::Associativity(associativity) => {
                    writeln!(
                        out,
                        "  associativity {} {:?} {}",
                        outer_associativity(associativity.associativity),
                        associativity.tags,
                        outer_span(&associativity.span)
                    )
                    .unwrap();
                }
                Sentence::Lexical(lexical) => {
                    writeln!(
                        out,
                        "  lexical {} {:?}{} {}",
                        lexical.name,
                        lexical.regex,
                        outer_attributes(&lexical.attributes),
                        outer_span(&lexical.span)
                    )
                    .unwrap();
                }
                Sentence::Bubble(bubble) => {
                    let kind = match bubble.kind {
                        BubbleKind::Rule => "rule",
                        BubbleKind::Claim => "claim",
                        BubbleKind::Context => "context",
                        BubbleKind::ContextAlias => "context alias",
                        BubbleKind::Configuration => "configuration",
                    };
                    let label = bubble
                        .label
                        .as_ref()
                        .map(|label| format!(" [{label}]"))
                        .unwrap_or_default();
                    writeln!(
                        out,
                        "  {kind}{label} {:?}{} {}",
                        bubble.content,
                        outer_attributes(&bubble.attributes),
                        outer_span(&bubble.span)
                    )
                    .unwrap();
                    writeln!(out, "    content {}", outer_span(&bubble.content_span)).unwrap();
                }
            }
        }
    }
    out
}

fn outer_associativity(associativity: k_rust::outer::Associativity) -> &'static str {
    use k_rust::outer::Associativity;
    match associativity {
        Associativity::Left => "left",
        Associativity::Right => "right",
        Associativity::NonAssoc => "non-assoc",
        Associativity::Unspecified => "unspecified",
    }
}

fn outer_span(span: &k_rust::outer::Span) -> String {
    let k_rust::outer::Span { start, end } = span;
    format!(
        "@{}:{}..{}:{} (bytes {}..{})",
        start.line, start.column, end.line, end.column, start.offset, end.offset
    )
}

fn outer_sort_parameters(parameters: &[k_rust::kast::Sort]) -> String {
    if parameters.is_empty() {
        return String::new();
    }
    let parameters = parameters
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    format!(" {{{parameters}}}")
}

fn outer_attributes(attributes: &[k_rust::outer::Attribute]) -> String {
    if attributes.is_empty() {
        return String::new();
    }
    let attributes = attributes
        .iter()
        .map(|attribute| match &attribute.value {
            None => attribute.key.clone(),
            Some(value) => format!("{}({value:?})", attribute.key),
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(" [{attributes}]")
}

/// A line-per-sentence outline of a lowered definition that names each field it prints.
///
/// Like [`outer_outline`], it is written field by field so that a field added to a definition
/// struct leaves it unchanged until the field is printed here, and every enum is matched without
/// a wildcard. Attribute maps are printed whole, one entry per line with its JSON value, because
/// their keys are data rather than struct fields: an attribute that lowering adds, drops or
/// changes is part of the lowered meaning.
fn lowered_outline(definition: &k_rust::definition::Definition) -> String {
    use k_rust::definition::{Associativity, ProductionItem, Sentence as DefinitionSentence};

    let mut out = String::new();
    writeln!(out, "definition main {}", definition.main_module).unwrap();
    lowered_attributes(&mut out, "", &definition.attributes);
    for module in &definition.modules {
        writeln!(out, "module {}", module.name).unwrap();
        lowered_attributes(&mut out, "", &module.attributes);
        for import in &module.imports {
            let visibility = if import.public { "public" } else { "private" };
            writeln!(out, "  imports {visibility} {}", import.name).unwrap();
        }
        for sentence in &module.local_sentences {
            let sentence: &DefinitionSentence = sentence;
            match sentence {
                DefinitionSentence::SyntaxSort {
                    parameters, sort, ..
                } => {
                    writeln!(out, "  syntax{} {sort}", outer_sort_parameters(parameters))
                }
                DefinitionSentence::SortSynonym {
                    new_sort, old_sort, ..
                } => writeln!(out, "  syntax {new_sort} = {old_sort}"),
                DefinitionSentence::SyntaxLexical { name, regex, .. } => {
                    writeln!(out, "  lexical {name} {regex:?}")
                }
                DefinitionSentence::Production {
                    label,
                    parameters,
                    sort,
                    items,
                    ..
                } => {
                    let items = items
                        .iter()
                        .map(|item| match item {
                            ProductionItem::Terminal(text) => format!("{text:?}"),
                            ProductionItem::NonTerminal { sort, name: None } => sort.to_string(),
                            ProductionItem::NonTerminal {
                                sort,
                                name: Some(name),
                            } => format!("{name}: {sort}"),
                            ProductionItem::RegexTerminal {
                                precede_regex,
                                regex,
                                follow_regex,
                            } => format!(
                                "r{regex:?} (precede {precede_regex:?}, follow {follow_regex:?})"
                            ),
                        })
                        .collect::<Vec<_>>()
                        .join(" ");
                    let label = match label {
                        None => "no label".to_owned(),
                        Some(label) => format!(
                            "label {:?}{}",
                            label.name,
                            outer_sort_parameters(&label.parameters)
                        ),
                    };
                    writeln!(
                        out,
                        "  syntax{} {sort} ::= {items} ({label})",
                        outer_sort_parameters(parameters)
                    )
                }
                DefinitionSentence::SyntaxAssociativity {
                    associativity,
                    tags,
                    ..
                } => {
                    let associativity = match associativity {
                        Associativity::Left => "left",
                        Associativity::Right => "right",
                        Associativity::NonAssoc => "non-assoc",
                        Associativity::Unspecified => "unspecified",
                    };
                    writeln!(out, "  syntax associativity {associativity} {tags:?}")
                }
                DefinitionSentence::SyntaxPriority { priorities, .. } => {
                    let groups = priorities
                        .iter()
                        .map(|group| format!("{group:?}"))
                        .collect::<Vec<_>>()
                        .join(" > ");
                    writeln!(out, "  syntax priority {groups}")
                }
                DefinitionSentence::ContextAlias { body, requires, .. } => {
                    writeln!(out, "  context alias {body} requires {requires}")
                }
                DefinitionSentence::Context { body, requires, .. } => {
                    writeln!(out, "  context {body} requires {requires}")
                }
                DefinitionSentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                } => writeln!(out, "  rule {body} requires {requires} ensures {ensures}"),
                DefinitionSentence::Claim {
                    body,
                    requires,
                    ensures,
                    ..
                } => writeln!(out, "  claim {body} requires {requires} ensures {ensures}"),
                DefinitionSentence::Configuration { body, ensures, .. } => {
                    writeln!(out, "  configuration {body} ensures {ensures}")
                }
                DefinitionSentence::Bubble {
                    sentence_type,
                    contents,
                    ..
                } => writeln!(out, "  bubble {sentence_type} {contents:?}"),
            }
            .unwrap();
            lowered_attributes(&mut out, "  ", sentence.attributes());
        }
    }
    out
}

fn lowered_attributes(out: &mut String, indent: &str, attributes: &k_rust::definition::Attributes) {
    for (key, value) in attributes.wire_entries() {
        writeln!(out, "{indent}    {key} = {value}").unwrap();
    }
}

/// A line per diagnostic that names each field it prints, in the style of [`outer_outline`]:
/// a field added to `Diagnostic` leaves it unchanged until the field is printed here. The
/// severity and the code print their stable public spellings.
fn diagnostics_outline(diagnostics: &[k_rust::diagnostic::Diagnostic]) -> String {
    let mut out = String::new();
    for diagnostic in diagnostics {
        let location = match &diagnostic.location {
            None => "no location".to_owned(),
            Some(location) => format!(
                "@{}:{}..{}:{}",
                location.start_line, location.start_column, location.end_line, location.end_column
            ),
        };
        let inputs = diagnostic
            .input_addresses
            .iter()
            .map(|address| format!("{:?} {} #{}", address.input, address.module, address.index))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            out,
            "{} {} source {:?} {location} inputs [{inputs}]\n  {:?}",
            diagnostic.severity.as_str(),
            diagnostic.code.as_str(),
            diagnostic.source,
            diagnostic.message
        )
        .unwrap();
    }
    out
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
    assert_outline_snapshot!(source, diagnostics_outline(&diagnostics));
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
