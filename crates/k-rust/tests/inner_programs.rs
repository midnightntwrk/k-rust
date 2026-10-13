// The embedded standard prelude loads in the portable build to the same definition as in the
// z3-inference build (inner_rules::the_standard_prelude_loads_to_the_same_definition_in_both_builds).
// Fixtures gated on `z3-inference` below are gated for their own rules or pinned results, not for
// the prelude: parametric sort inference, an ambiguous forest outside the portable decision, or
// an assertion not yet checked against the portable build.

use indoc::indoc;
use k_rust::definition::{Definition, LabelHead, ResolvedDefinition};
use k_rust::inner::{NoParseInput, ParseError, ProgramError, ProgramParser, parse_program};
use k_rust::kast::{Sort, Term, TermSpan};
use k_rust::provenance::SourceId;

#[path = "support/line_anchors.rs"]
mod line_anchors;

fn lowered(source: &str, main_module: &str) -> Definition {
    let parsed = k_rust::outer::parse("program.k", source).expect("definition should parse");
    k_rust::outer::lower(&parsed, main_module).expect("definition should lower")
}

fn wasm_shaped_overloaded_lists() -> Definition {
    lowered(
        indoc! {r#"
            module MAIN
              syntax Type ::= "i32" [symbol(i32)]
              syntax Result ::= "(" "result" Type ")" [symbol(result)]
              syntax Instr ::= "i32.const" Int [symbol(const)]
              syntax Int ::= r"[0-9]+" [token]
              syntax BodyItem ::= Result | Instr
              syntax Stmt ::= Instr
              syntax Results ::= List{Result, ""} [overload(listStmt), symbol(results)]
              syntax Instrs ::= List{Instr, ""} [overload(listStmt), symbol(instrs)]
              syntax BodyItems ::= List{BodyItem, ""} [overload(listStmt), symbol(bodyItems)]
              syntax Stmts ::= List{Stmt, ""} [overload(listStmt), symbol(stmts)]
              syntax Stmts ::= Instrs
              syntax Defn ::= "(" "func" Results Instrs ")" [symbol(func)]
              syntax Item ::= Defn
              syntax Defns ::= List{Defn, ""} [overload(listModule), symbol(defns)]
              syntax Items ::= List{Item, ""} [overload(listModule), symbol(items)]
              syntax Module ::= "(" "module" Defns ")" [symbol(module)]
            endmodule
        "#},
        "MAIN",
    )
}

fn wasm_empty_function_overloaded_lists() -> Definition {
    lowered(
        indoc! {r#"
            module MAIN
              syntax EmptyStmt
              syntax Instr ::= EmptyStmt
              syntax Defn ::= EmptyStmt
              syntax Stmt ::= Instr | Defn
              syntax EmptyStmts ::= List{EmptyStmt, ""} [overload(listStmt), terminator-symbol(".List{\"listStmt\"}")]
              syntax Instrs ::= List{Instr, ""} [overload(listStmt), symbol(instrs)]
              syntax Defns ::= List{Defn, ""} [overload(listStmt), symbol(defns)]
              syntax Stmts ::= List{Stmt, ""} [overload(listStmt), symbol(stmts)]
              syntax Instrs ::= EmptyStmts
              syntax Defns ::= EmptyStmts
              syntax Stmts ::= Instrs | Defns
              syntax Defn ::= "(" "func" Instrs ")" [symbol(func)]
              syntax Module ::= "(" "module" Defns ")" [symbol(module)]
            endmodule
        "#},
        "MAIN",
    )
}

#[test]
fn parsed_production_ids_belong_to_the_resolved_definition_catalog() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax State ::= "a" [symbol(a)]
            endmodule
        "#},
        "MAIN",
    );
    let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
    let parsed = ProgramParser::from_resolved(&resolved, "MAIN")
        .expect("program parser should build")
        .parse(&Sort::new("State"), "a")
        .expect("program should parse");
    let production = parsed
        .typed_term()
        .metadata()
        .and_then(|metadata| metadata.production)
        .expect("parsed application should retain its production identity");
    assert_eq!(
        parsed
            .typed_term()
            .metadata()
            .and_then(|metadata| metadata.span),
        None,
        "legacy parsing must not fabricate an unknown source identity",
    );
    let module = resolved.module_id("MAIN").expect("module should exist");
    let catalog = resolved.production_catalog(module);
    let expected = catalog.productions_for(&LabelHead::new("a"));

    assert_eq!(expected.len(), 1);
    assert_eq!(production, catalog.identity(expected[0]));
}

#[test]
fn legacy_program_parser_omits_nested_spans_but_retains_productions() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax State ::= "f" "(" State ")" [symbol(f)]
                             | "a" [symbol(a)]
            endmodule
        "#},
        "MAIN",
    );
    let parsed = ProgramParser::new(&definition, "MAIN")
        .unwrap()
        .parse(&Sort::new("State"), "f(a)")
        .unwrap();
    let Term::Apply { arguments, .. } = parsed.typed_term().unannotated() else {
        panic!("expected an application")
    };

    for term in [parsed.typed_term(), &arguments[0]] {
        let metadata = term.metadata().expect("production metadata should remain");
        assert_eq!(metadata.span, None);
        assert!(metadata.production.is_some());
    }
}

#[test]
fn parse_program_records_the_callers_logical_source_identity() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax State ::= "a" [symbol(a)]
            endmodule
        "#},
        "MAIN",
    );
    let parsed = parse_program(&definition, "MAIN", &Sort::new("State"), "a", SourceId(7)).unwrap();

    assert_eq!(
        parsed
            .typed_term()
            .metadata()
            .and_then(|metadata| metadata.span),
        Some(k_rust::kast::TermSpan {
            source: SourceId(7),
            start: 0,
            end: 1,
        })
    );
}

#[test]
fn parse_program_exposes_the_structured_noparse_diagnostic() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Start ::= "ok" "done" [symbol(start)]
              syntax Other ::= "bad" [symbol(bad)]
            endmodule
        "#},
        "MAIN",
    );
    let error = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Start"),
        "ok bad",
        SourceId(7),
    )
    .unwrap_err();
    assert_eq!(
        error,
        ProgramError::Parse(k_rust::inner::ProgramParseError {
            module: "MAIN".into(),
            start_sort: Sort::new("Start"),
            item_attempt: None,
            error: Box::new(ParseError::NoParse {
                position: 3,
                expected: vec!["\"done\"".into()].into(),
                input: NoParseInput::Token {
                    value: "bad".into(),
                },
                previous: Some("ok".into()),
                notes: None,
                span: Some(TermSpan {
                    source: SourceId(7),
                    start: 3,
                    end: 6,
                }),
                work_limit: None,
            }),
        })
    );
    assert_eq!(
        error.to_string(),
        "could not parse program as Start with module \"MAIN\": Parse error: unexpected token 'bad' following token 'ok'."
    );

    let legacy = ProgramParser::new(&definition, "MAIN")
        .unwrap()
        .parse(&Sort::new("Start"), "ok bad")
        .unwrap_err();
    assert!(matches!(
        legacy.error.as_ref(),
        ParseError::NoParse {
            input: NoParseInput::Token { value },
            previous: Some(previous),
            span: None,
            ..
        } if value == "bad" && &**previous == "ok"
    ));
    assert_eq!(
        legacy.to_string(),
        "could not parse program as Start with module \"MAIN\": Parse error: unexpected token 'bad' following token 'ok'."
    );
}

#[test]
fn parses_a_user_sort_program_at_kitem_and_returns_the_bare_term() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").expect("program grammar should build");
    let concrete = parser
        .parse(&Sort::new("Int"), "1")
        .expect("the concrete sort should parse");
    let at_kitem = parser
        .parse(&Sort::new("KItem"), "1")
        .expect("KItem should include every user-sort program");

    assert_eq!(at_kitem, concrete);
    assert_eq!(at_kitem.typed_term().to_string(), r#"#token("1","Int")"#);
}

#[test]
fn parses_at_k_only_when_basic_k_is_visible() {
    let without_basic_k = lowered(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&without_basic_k, "MAIN").unwrap();
    let error = parser
        .parse(&Sort::new("K"), "1")
        .expect_err("K must not be synthesized over KItem");
    assert!(
        matches!(*error.error, ParseError::NoParse { .. }),
        "{error:?}"
    );

    let with_basic_k = lowered(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax K ::= KItem
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&with_basic_k, "MAIN").unwrap();
    let concrete = parser.parse(&Sort::new("Int"), "1").unwrap();
    let at_k = parser
        .parse(&Sort::new("K"), "1")
        .expect("visible BASIC-K syntax should connect K to KItem");
    assert_eq!(at_k, concrete);
}

#[test]
fn excludes_user_list_sorts_from_the_kitem_closure() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Id ::= r"[a-z]+" [token]
              syntax Ids ::= List{Id, ","} [symbol(ids)]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();
    let _ = parser
        .parse(&Sort::new("Ids"), "a,b")
        .expect("the list sort itself should remain parseable");
    let error = parser
        .parse(&Sort::new("KItem"), "a,b")
        .expect_err("user-list sorts are excluded from KItem's generated subsorts");
    assert!(
        matches!(*error.error, ParseError::NoParse { .. }),
        "{error:?}"
    );
}

#[test]
fn reference_singleton_nelist_at_kitem_is_a_reported_ambiguity() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax #LowerId ::= r"[a-z][a-zA-Z0-9]*" [prec(2), token]
              syntax Id ::= #LowerId [token]
              syntax Ids ::= NeList{Id, ","} [symbol(ids)]
              syntax Pgm ::= Ids
            endmodule
        "#},
        "MAIN",
    );
    let error = ProgramParser::new(&definition, "MAIN")
        .unwrap()
        .parse(&Sort::new("KItem"), "a")
        .expect_err("the bare Id and singleton Ids parses must remain ambiguous");

    match *error.error {
        ParseError::Ambiguous {
            ref alternatives, ..
        } => {
            assert_eq!(alternatives.len(), 2, "{alternatives:#?}");
            let productions = alternatives
                .iter()
                .filter_map(|alternative| alternative.production.as_deref())
                .collect::<Vec<_>>();
            assert!(
                productions
                    .iter()
                    .any(|production| production.contains("syntax Id ::= #LowerId [token]")),
                "{productions:#?}"
            );
            assert!(
                productions.iter().any(|production| {
                    production.contains("syntax Ids ::= Id \",\" Ids")
                        && production.contains("userList(+)")
                }),
                "{productions:#?}"
            );
        }
        ref other => panic!("expected the reference ambiguity, got {other:?}"),
    }
}

#[test]
fn reference_punctuation_token_argument_parses_as_kitem() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Aa ::= r"%[a-z]+" [prefer, token]
              syntax Bb ::= r"%[a-z]+" [token]
              syntax Foo ::= "foo" "(" KItem ")" [symbol(foo)]
            endmodule
        "#},
        "MAIN",
    );
    let parsed = ProgramParser::new(&definition, "MAIN")
        .unwrap()
        .parse(&Sort::new("Foo"), "foo(%abc)");
    assert_eq!(
        parsed
            .expect("the preferred punctuation token should inhabit KItem")
            .typed_term()
            .to_string(),
        r#"foo(#token("%abc","Aa"))"#
    );
}

#[test]
fn reference_kitem_start_sort_matches_the_concrete_sort() {
    let definition = lowered(
        include_str!("fixtures/reference/inner/programs/scan-c-syntax/scan-c.k"),
        "SCAN-C-SYNTAX",
    );
    let parser = ProgramParser::new(&definition, "SCAN-C-SYNTAX").unwrap();
    assert_eq!(
        parser.parse(&Sort::new("KItem"), "1").unwrap(),
        parser.parse(&Sort::new("Int"), "1").unwrap()
    );
}

#[test]
fn kitem_closure_includes_parametric_instantiations() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax MInt{6}
              syntax {N} MInt{N} ::= r"[0-9]+" [token]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();
    let mint_6 = Sort::with_parameters("MInt", vec![Sort::new("6")]);
    let at_kitem = parser.parse(&Sort::new("KItem"), "1");
    #[cfg(feature = "z3-inference")]
    assert_eq!(at_kitem.unwrap(), parser.parse(&mint_6, "1").unwrap());
    #[cfg(not(feature = "z3-inference"))]
    assert!(
        matches!(
            at_kitem.as_ref().unwrap_err().error.as_ref(),
            ParseError::Z3InferenceRequired {
                ambiguity: false,
                parametric_sorts: true,
            }
        ),
        "{at_kitem:?}; concrete sort: {mint_6}"
    );
}

macro_rules! program_snapshot {
    ($name:ident, $definition:expr, $module:expr, $sort:expr, $program:expr) => {
        #[test]
        fn $name() {
            let definition_source = indoc!($definition);
            let program_source = indoc!($program);
            let definition = lowered(definition_source, $module);
            let parsed = parse_program(
                &definition,
                $module,
                &Sort::new($sort),
                program_source,
                SourceId(0),
            )
            .expect("program should parse")
            .typed_term()
            .to_string();
            insta::with_settings!({
                description => format!(
                    "K definition:\n\n{definition_source}\nProgram ({sort}):\n\n{program_source}",
                    sort = $sort,
                ),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(parsed);
            });
        }
    };
}

program_snapshot!(
    resolves_syntax_priority,
    r#"
        module MAIN
          syntax Exp ::= Exp "*" Exp [left, symbol(mul)]
                       > Exp "+" Exp [left, symbol(add)]
                       | r"[0-9]+" [token]
        endmodule
    "#,
    "MAIN",
    "Exp",
    "1 + 2 * 3"
);

program_snapshot!(
    resolves_left_associativity,
    r#"
        module MAIN
          syntax Exp ::= Exp "+" Exp [left, symbol(add)]
                       | r"[0-9]+" [token]
        endmodule
    "#,
    "MAIN",
    "Exp",
    "1 + 2 + 3"
);

program_snapshot!(
    parses_user_lists_without_explicit_terminators,
    r#"
        module MAIN
          syntax Ints ::= List{Int, ","} [symbol(ints)]
          syntax Int ::= r"[0-9]+" [token]
        endmodule
    "#,
    "MAIN",
    "Ints",
    "0, 1, 2"
);

program_snapshot!(
    parses_empty_user_lists_in_surrounding_syntax,
    r#"
        module MAIN
          syntax Exp ::= Int "(" Ints ")" [symbol(call)]
          syntax Ints ::= List{Int, ","} [symbol(ints)]
          syntax Int ::= r"[0-9]+" [token]
        endmodule
    "#,
    "MAIN",
    "Exp",
    "0()"
);

program_snapshot!(
    uses_default_layout,
    r#"
        module MAIN
          syntax Int ::= Int "+" Int [left, symbol(add)]
                       | r"[0-9]+" [token]
        endmodule
    "#,
    "MAIN",
    "Int",
    "0 /* comment */ + 3"
);

program_snapshot!(
    uses_module_defined_layout,
    r#"
        module MAIN
          syntax #Layout ::= r"(;;[^\\n\\r]*)|([\\ \\n\\r\\t])"
          syntax Int ::= Int "+" Int [left, symbol(add)]
                       | r"[0-9]+" [token]
        endmodule
    "#,
    "MAIN",
    "Int",
    "0 + 3 ;; comment"
);

#[test]
fn reference_regex_backslash_d_is_a_literal_d() {
    let definition = lowered(include_str!("fixtures/reference/inner/regex/rx.k"), "RX");
    let parser =
        ProgramParser::new(&definition, "RX-SYNTAX").expect("program grammar should build");

    let parsed = parser
        .parse(&Sort::new("Pgm"), "ddd")
        .expect(r"K treats \d as the literal character d");
    assert!(
        parsed
            .typed_term()
            .to_string()
            .contains("#token(\"ddd\",\"Foo\")")
    );
    parser
        .parse(&Sort::new("Pgm"), "123")
        .expect_err(r"K does not treat \d as a digit character class");
}

#[test]
fn regex_line_anchors_constrain_where_a_token_starts_and_ends() {
    let definition = lowered(line_anchors::DEFINITION, "ANCHOR");
    let parser =
        ProgramParser::new(&definition, "ANCHOR-SYNTAX").expect("program grammar should build");

    for (program, accepted) in line_anchors::PROGRAMS {
        let result = parser.parse(&Sort::new("Pgm"), program);
        assert_eq!(result.is_ok(), accepted, "{program:?}: {result:?}");
    }
    for program in line_anchors::programs_with_a_token_at_a_buffer_boundary() {
        let result = parser.parse(&Sort::new("Pgm"), &program);
        assert!(result.is_ok(), "{} spaces: {result:?}", program.len() - 2);
    }
}

#[test]
fn regex_line_anchors_do_not_lengthen_a_token_in_the_longest_match_rule() {
    let definition = lowered(line_anchors::TIE_DEFINITION, "TIE");
    let parser =
        ProgramParser::new(&definition, "TIE-SYNTAX").expect("program grammar should build");

    for (program, accepted) in line_anchors::TIE_PROGRAMS {
        let result = parser.parse(&Sort::new("Pgm"), program);
        assert_eq!(result.is_ok(), accepted, "{program:?}: {result:?}");
    }
}

#[test]
fn regex_line_anchors_make_distinct_lexemes() {
    // `^a` and `^a$` (and `a` and `a$`) accept different token positions, so a scanner must not
    // treat them as one lexeme.
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Start ::= r"^a" [token]
              syntax Both ::= r"^a$" [token]
              syntax Plain ::= r"b" [token]
              syntax End ::= r"b$" [token]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").expect("program grammar should build");

    // Only inputs where one lexeme alone matches: where both match with the same length, the
    // scanner picks one token for both sorts.
    for (sort, program, accepted) in [
        ("Start", "a", true),
        ("Both", "a", false),
        ("Plain", "b", true),
        ("End", "b", false),
    ] {
        let result = parser.parse(&Sort::new(sort), program);
        assert_eq!(result.is_ok(), accepted, "{sort} {program:?}: {result:?}");
    }
}

#[test]
fn an_end_anchored_layout_that_matches_the_empty_string_is_rejected() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax #Layout ::= r" *$"
              syntax Foo ::= r"a" [token]
            endmodule
        "#},
        "MAIN",
    );
    let error = ProgramParser::new(&definition, "MAIN").unwrap_err();

    assert!(
        matches!(
            error,
            ProgramError::Grammar { ref error, .. }
                if matches!(error.as_ref(), ParseError::EmptyLayout)
        ),
        "{error:?}"
    );
}

#[test]
fn reference_rejects_rust_only_regex_syntax() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Foo ::= r"(?:a)" [token]
            endmodule
        "#},
        "MAIN",
    );
    let error = ProgramParser::new(&definition, "MAIN").unwrap_err();

    assert!(
        matches!(
            error,
            ProgramError::Grammar {
                ref error,
                ..
            } if matches!(error.as_ref(), ParseError::InvalidRegex { message, .. } if message.contains("Unexpected token '?'"))
        ),
        "{error:?}"
    );
}

#[test]
fn regex_terminals_do_not_depend_on_unrelated_lexical_declarations() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Foo ::= r"\\d+" [token]
              syntax lexical Unused = r"x"
              syntax Bar ::= r"\\d+" [token]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").expect("program grammar should build");

    for sort in ["Foo", "Bar"] {
        let _ = parser
            .parse(&Sort::new(sort), "ddd")
            .unwrap_or_else(|error| panic!("{sort} should parse literal d characters: {error}"));
        assert!(
            parser.parse(&Sort::new(sort), "123").is_err(),
            "{sort} unexpectedly treated K's \\d as a Rust digit class"
        );
    }
}

program_snapshot!(
    substitutes_imported_program_parsing_modules,
    r#"
        module BASE
          syntax Exp ::= "definition" [symbol(definitionSyntax)]
        endmodule

        module BASE-PROGRAM-PARSING
          syntax Exp ::= "program" [symbol(programSyntax)]
        endmodule

        module MAIN
          imports BASE
          syntax Start ::= Exp [symbol(start)]
        endmodule
    "#,
    "MAIN",
    "Start",
    "program"
);

program_snapshot!(
    uses_only_public_syntax_from_imported_modules,
    r#"
        module BASE
          syntax Exp ::= "visible" [symbol(visible)]
          syntax Exp ::= "hidden" [private, symbol(hidden)]
        endmodule

        module MAIN
          imports BASE
          syntax Start ::= Exp [symbol(start)]
        endmodule
    "#,
    "MAIN",
    "Start",
    "visible"
);

#[test]
fn rejects_an_empty_nonempty_user_list() {
    let definition_source = indoc! {r#"
        module MAIN
          syntax Exp ::= Int "[" Ints "]" [symbol(index)]
          syntax Ints ::= NeList{Int, ","} [symbol(ints)]
          syntax Int ::= r"[0-9]+" [token]
        endmodule
    "#};
    let definition = lowered(definition_source, "MAIN");
    let error =
        parse_program(&definition, "MAIN", &Sort::new("Exp"), "0[]", SourceId(0)).unwrap_err();
    assert!(
        matches!(
            error,
            ProgramError::Parse(ref error)
                if matches!(*error.error, ParseError::NoParse { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn treats_user_list_terminators_as_invisible_in_programs() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Id ::= r"[a-z]+" [token]
              syntax Ids ::= NeList{Id, ","} [symbol(ids)]
              syntax Pgm ::= Ids [symbol(pgm)]
              syntax Items ::= List{Id, ","} [symbol(items)]
              syntax ListPgm ::= Items [symbol(listPgm)]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").expect("program grammar should build");

    for source in ["a", "a, b"] {
        let _ = parser
            .parse(&Sort::new("Pgm"), source)
            .unwrap_or_else(|error| panic!("NeList program {source:?} should parse: {error}"));
    }
    for source in [".Ids", "a, .Ids", "a,"] {
        let error = parser
            .parse(&Sort::new("Pgm"), source)
            .expect_err("invalid NeList program should be rejected");
        assert!(
            matches!(*error.error, ParseError::NoParse { .. }),
            "{source:?}: {error:?}"
        );
    }

    let _ = parser
        .parse(&Sort::new("ListPgm"), "")
        .expect("List program should accept the empty list");
    for source in ["a", "a, b"] {
        let _ = parser
            .parse(&Sort::new("ListPgm"), source)
            .unwrap_or_else(|error| panic!("List program {source:?} should parse: {error}"));
    }
    let error = parser
        .parse(&Sort::new("ListPgm"), ".Items")
        .expect_err("list terminator should be invisible in programs");
    assert!(
        matches!(*error.error, ParseError::NoParse { .. }),
        "{error:?}"
    );
}

#[test]
fn reconstructs_a_singleton_nelist_through_a_transparent_start_sort() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Id ::= r"[a-z]+" [token]
              syntax Ids ::= NeList{Id, ","} [symbol(ids)]
              syntax Pgm ::= Ids
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").expect("program grammar should build");
    for (source, expected) in [
        ("a", r#"ids(#token("a","Id"),`.List{"ids"}`(.KList))"#),
        (
            "a,b",
            r#"ids(#token("a","Id"),ids(#token("b","Id"),`.List{"ids"}`(.KList)))"#,
        ),
    ] {
        let parsed = parser
            .parse(&Sort::new("Pgm"), source)
            .unwrap_or_else(|error| panic!("NeList program {source:?} should parse: {error}"));
        assert_eq!(parsed.typed_term().to_string(), expected);
    }
}

#[test]
fn rejects_a_trailing_separator_in_a_program_user_list() {
    // K's program grammar is `Ints ::= Ne#Ints | ""` with `Ne#Ints ::= Int "," Ne#Ints | Int`,
    // so the empty list is only the whole list, never the tail after a separator.
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Exp ::= Int "[" Ints "]" [symbol(index)]
              syntax Ints ::= List{Int, ","} [symbol(ints)]
              syntax Int ::= r"[0-9]+" [token]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();

    for source in ["0[]", "0[1]", "0[1,2]"] {
        let term = parser
            .parse(&Sort::new("Exp"), source)
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        let rendered = term.typed_term().to_string();
        assert!(rendered.contains("ints"), "{source}: {rendered}");
    }
    for source in ["0[1,]", "0[1,2,]", "0[,]"] {
        let error = parser.parse(&Sort::new("Exp"), source).unwrap_err();
        assert!(
            matches!(*error.error, ParseError::NoParse { .. }),
            "{source}: {error:?}"
        );
    }
}

#[test]
fn parses_empty_and_singleton_overloaded_user_lists() {
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Defn ::= "func" [symbol(func)]
              syntax Item ::= Defn
              syntax Defns ::= List{Defn, ""} [overload(listStmt), symbol(defns)]
              syntax Items ::= List{Item, ""} [overload(listStmt), symbol(items)]
              syntax Module ::= "(" "module" Defns ")" [symbol(module)]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();

    for source in ["(module)", "(module func)"] {
        let term = parser
            .parse(&Sort::new("Module"), source)
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        let rendered = term.typed_term().to_string();
        assert!(rendered.contains("defns"), "{source}: {rendered}");
        assert!(!rendered.contains("items"), "{source}: {rendered}");
    }
}

#[test]
fn parses_wasm_shaped_adjacent_overloaded_user_lists() {
    let definition = wasm_shaped_overloaded_lists();
    let parsed = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Module"),
        "(module (func (result i32) i32.const 1))",
        SourceId(0),
    )
    .unwrap();
    let rendered = parsed.typed_term().to_string();

    for label in ["module", "defns", "func", "results", "instrs"] {
        assert!(rendered.contains(label), "missing {label}: {rendered}");
    }
    assert!(!rendered.contains("bodyItems"), "{rendered}");
}

#[test]
fn preserves_outer_list_terminator_after_an_empty_inner_overloaded_list() {
    let definition = wasm_empty_function_overloaded_lists();
    {
        let rendered = parse_program(
            &definition,
            "MAIN",
            &Sort::new("Module"),
            "(module (func))",
            SourceId(0),
        )
        .expect("an empty function should parse uniquely inside its module")
        .typed_term()
        .to_string();

        for label in ["module", "defns", "func"] {
            assert!(rendered.contains(label), "missing {label}: {rendered}");
        }
        assert!(
            rendered.contains(r#".List{"defns"}"#),
            "the outer Defns list should retain its own terminator: {rendered}"
        );
        assert!(
            rendered.contains(r#".List{"listStmt"}"#),
            "the empty inner Instrs list should retain the shared terminator: {rendered}"
        );
    }
}

#[test]
fn reconstructs_a_root_sort_singleton_as_its_most_specific_list() {
    let definition = wasm_shaped_overloaded_lists();
    {
        let rendered = parse_program(
            &definition,
            "MAIN",
            &Sort::new("Stmts"),
            "i32.const 1",
            SourceId(0),
        )
        .expect("a root singleton should be reconstructed as a list")
        .typed_term()
        .to_string();

        assert!(rendered.contains("instrs"), "{rendered}");
        assert!(!rendered.contains("stmts"), "{rendered}");
        assert!(rendered.contains(".List"), "{rendered}");
    }
}

#[test]
fn parses_an_empty_program_at_a_root_list_sort() {
    let definition = wasm_shaped_overloaded_lists();
    {
        let rendered = parse_program(&definition, "MAIN", &Sort::new("Stmts"), "", SourceId(0))
            .expect("the empty list should parse at a root list sort")
            .typed_term()
            .to_string();

        assert!(rendered.contains(".List"), "{rendered}");
    }
}

#[test]
fn parses_multiple_defns_with_empty_inner_lists() {
    let definition = wasm_shaped_overloaded_lists();
    let rendered = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Module"),
        "(module (func) (func))",
        SourceId(0),
    )
    .expect("an outer list should accept multiple elements with empty inner lists")
    .typed_term()
    .to_string();

    assert_eq!(rendered.matches("func(").count(), 2, "{rendered}");
    assert!(rendered.contains("defns"), "{rendered}");
    assert!(!rendered.contains("items"), "{rendered}");
}

#[test]
fn program_parsing_is_layout_insensitive() {
    let definition = wasm_shaped_overloaded_lists();
    let compact = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Module"),
        "(module (func) (func))",
        SourceId(0),
    )
    .expect("compact program should parse")
    .typed_term()
    .to_string();
    let laid_out = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Module"),
        "( // open\n module // first function\n ( func ) // second function\n ( func ) // close\n )",
        SourceId(0),
    )
    .expect("layout and comments should not affect parsing")
    .typed_term().to_string();

    assert_eq!(compact, laid_out);
}

#[test]
fn rejects_programs_outside_the_grammar() {
    let definition = wasm_shaped_overloaded_lists();
    for (name, sort, source) in [
        ("unbalanced delimiters", "Module", "(module (func"),
        ("keyword as definition", "Module", "(module module)"),
        ("missing instruction argument", "Stmts", "i32.const"),
    ] {
        assert!(
            parse_program(&definition, "MAIN", &Sort::new(sort), source, SourceId(0),).is_err(),
            "{name} unexpectedly parsed: {source}"
        );
    }
}

#[test]
fn reports_a_missing_syntax_module_before_parsing() {
    let definition_source = indoc! {r#"
        module MAIN
          syntax Exp ::= "x"
        endmodule
    "#};
    let definition = lowered(definition_source, "MAIN");
    let error = ProgramParser::new(&definition, "MISSING").unwrap_err();
    assert_eq!(error, ProgramError::MissingModule("MISSING".into()));
}

#[test]
fn rejects_private_syntax_from_an_imported_module() {
    let definition_source = indoc! {r#"
        module BASE
          syntax Exp ::= "visible" [symbol(visible)]
          syntax Exp ::= "hidden" [private, symbol(hidden)]
        endmodule

        module MAIN
          imports BASE
          syntax Start ::= Exp [symbol(start)]
        endmodule
    "#};
    let definition = lowered(definition_source, "MAIN");
    let error = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Start"),
        "hidden",
        SourceId(0),
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            ProgramError::Parse(ref error)
                if matches!(*error.error, ParseError::NoParse { .. })
        ),
        "{error:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_named_field_projections_parse_in_programs() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --output-definition ref-kompiled && k/result/bin/kast --definition ref-kompiled --output kast 3.test
    // kast: `project:test(_,_,_)_TEST_Foo_Int_Int_Int:foo`(`test(_,_,_)_TEST_Foo_Int_Int_Int`(#token("5","Int"),#token("10","Int"),#token("15","Int")))
    // Reduced from regression-new/record-llvm 3.test and 4.test (`foo(test(5, 10, 15))`,
    // `bar(test(5, 10, 15))`): each named nonterminal of a production declares a field whose
    // projection is a function of the module, so a program, written in the module's syntax, may
    // apply it, and the program grammar has the field projections of every record-shaped
    // production. The sort projections `project:Sort`, like the sort predicates, serve rules
    // that narrow a term to a sort; the rule grammar adds them for every sort, and the program
    // grammar does not.
    let prelude = k_rust::builtin::embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = k_rust::outer::load_with_options(
        k_rust::outer::ResolvedSource::new(
            "test.k",
            include_str!("fixtures/reference/inner/record-projection/test.k"),
        ),
        "TEST",
        &mut resolver,
        &k_rust::outer::LoadOptions {
            implicit_sources: vec![prelude],
            ..k_rust::outer::LoadOptions::default()
        },
    )
    .expect("the definition loads with the prelude");
    let parser =
        ProgramParser::new(loaded.definition(), "TEST").expect("program grammar should build");
    let foo = parser
        .parse(&Sort::new("KItem"), "foo(test(5, 10, 15))")
        .expect("the foo projection is program syntax");
    assert_eq!(
        foo.typed_term().to_string(),
        "`project:test(_,_,_)_TEST_Foo_Int_Int_Int:foo`(`test(_,_,_)_TEST_Foo_Int_Int_Int`(#token(\"5\",\"Int\"),#token(\"10\",\"Int\"),#token(\"15\",\"Int\")))"
    );
    let bar = parser
        .parse(&Sort::new("Int"), "bar(test(5, 10, 15))")
        .expect("the bar projection parses at its field sort");
    assert!(
        bar.typed_term()
            .to_string()
            .starts_with("`project:test(_,_,_)_TEST_Foo_Int_Int_Int:bar`("),
        "{}",
        bar.typed_term()
    );
    let error = parser
        .parse(&Sort::new("KItem"), "project:Foo(test(5, 10, 15))")
        .expect_err("sort projections are not program syntax");
    assert!(
        matches!(*error.error, ParseError::NoParse { .. }),
        "{error:?}"
    );
}

#[test]
fn fu24_program_start_synonyms_denote_through_chains() {
    let definition = lowered(
        indoc! {r#"
            module M
              syntax S ::= "a"
              syntax B = S
              syntax A = B
            endmodule
        "#},
        "M",
    );
    let parser = ProgramParser::new(&definition, "M").unwrap();
    let canonical = parser.parse(&Sort::new("S"), "a").unwrap();
    for spelling in ["A", "B"] {
        let parsed = parser.parse(&Sort::new(spelling), "a").unwrap();
        assert_eq!(parsed.typed_term(), canonical.typed_term(), "{spelling}");
    }
    assert_eq!(
        parser
            .parse_for_presentation(&Sort::new("A"), "a")
            .unwrap()
            .term(),
        parser
            .parse_for_presentation(&Sort::new("S"), "a")
            .unwrap()
            .term(),
    );
    let error = parser.parse(&Sort::new("A"), "b").unwrap_err();
    assert_eq!(error.start_sort, Sort::new("A"));
}

#[test]
fn fu24_program_start_uses_privately_imported_synonyms() {
    let definition = lowered(
        indoc! {r#"
            module HIDDEN
              syntax S ::= "a"
              syntax P = S
            endmodule
            module M
              imports private HIDDEN
              syntax T ::= S
            endmodule
        "#},
        "M",
    );
    let parser = ProgramParser::new(&definition, "M").unwrap();
    assert_eq!(
        parser.parse(&Sort::new("P"), "a").unwrap().typed_term(),
        parser.parse(&Sort::new("S"), "a").unwrap().typed_term(),
    );
}

#[test]
fn fu24_program_start_sort_reports_the_denotation() {
    let definition = lowered(
        indoc! {r#"
            module M
              syntax S ::= "a"
              syntax B = S
              syntax A = B
            endmodule
        "#},
        "M",
    );
    let parser = ProgramParser::new(&definition, "M").unwrap();
    assert_eq!(parser.start_sort(&Sort::new("A")), &Sort::new("S"));
}

/// The number of applications on the path from `term` through first arguments, counted
/// without recursion.
fn first_argument_depth(term: &Term) -> usize {
    let mut depth = 0;
    let mut term = term;
    while let Term::Apply { arguments, .. } = term.unannotated() {
        depth += 1;
        let Some(first) = arguments.first() else {
            break;
        };
        term = first;
    }
    depth
}

/// A program is as deep as its author writes it, and every pass after recognition descends once
/// per level of its parse: the packed-forest and owned-tree disambiguation passes, sort
/// inference, lowering, and the drops of the forest and of what each pass discards. A numeral
/// 100,000 levels deep is parsed on a thread of 256 KiB of stack, and so are a program failing at
/// its bottom (a no-parse error) and one with a closing parenthesis too many; each pass continues
/// on a fresh stack segment where the thread's runs low. They once recursed on the caller's stack
/// and overflowed at about 4,000 levels of the 8 MiB main thread.
#[test]
fn programs_of_any_depth_are_parsed_on_a_small_stack() {
    const DEPTH: usize = 100_000;
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Nat ::= "z" | s(Nat)
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();
    let numeral = |leaf: &str, extra: &str| {
        format!("{}{leaf}{}{extra}", "s(".repeat(DEPTH), ")".repeat(DEPTH))
    };
    let (good, unknown, unbalanced) = (numeral("z", ""), numeral("q", ""), numeral("z", ")"));
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(move || {
            let parsed = parser.parse(&Sort::new("Nat"), &good).unwrap();
            assert_eq!(first_argument_depth(parsed.typed_term()), DEPTH + 1);
            let error = parser.parse(&Sort::new("Nat"), &unknown).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("unexpected character sequence 'q'"),
                "{error}"
            );
            let error = parser.parse(&Sort::new("Nat"), &unbalanced).unwrap_err();
            assert!(
                error.to_string().contains("unexpected token ')'"),
                "{error}"
            );
        })
        .expect("the worker should spawn")
        .join()
        .expect("the programs should parse or be refused");
}

/// A nesting of a parametric production is parsed on a small stack too, whether its instances
/// are read at the sort of their argument (`p(wrap(...(z)))`, every `wrap` a `Nat`) or at a sort
/// above it (`wrap(...(z))` as a `KItem`, where every level is a `wrap` at `KItem` and at
/// `Nat`). List completion instantiates each node from its children's sorts and once recursed
/// through the whole nesting below each node, on the caller's stack: about 4,000 levels
/// overflowed the 8 MiB main thread.
#[test]
fn parametric_nestings_of_any_depth_are_parsed_on_a_small_stack() {
    const DEPTH: usize = 10_000;
    let definition = lowered(
        indoc! {r#"
            module MAIN
              syntax Nat ::= "z" [symbol(z)]
              syntax {S} S ::= wrap(S) [symbol(wrap)]
              syntax KItem ::= p(Nat) [symbol(p)]
            endmodule
        "#},
        "MAIN",
    );
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();
    let nesting = format!("{}z{}", "wrap(".repeat(DEPTH), ")".repeat(DEPTH));
    let applied = format!("p({nesting})");
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(move || {
            let parsed = parser.parse(&Sort::new("KItem"), &applied).unwrap();
            assert_eq!(first_argument_depth(parsed.typed_term()), DEPTH + 2);
            let parsed = parser.parse(&Sort::new("KItem"), &nesting).unwrap();
            assert_eq!(first_argument_depth(parsed.typed_term()), DEPTH + 1);
        })
        .expect("the worker should spawn")
        .join()
        .expect("the programs should parse");
}

// Ground K values: `ProgramParser::for_ground_values` parses a cell's content with the program
// grammar of one module plus exactly `K ::= KItem`, `.K`, `K ~> K` and an avoided K bracket.

/// A definition loaded with the embedded prelude, as `krust kcompile` loads it, together with
/// its program grammar's resolution: what parsing, macro expansion, sort injection and KORE
/// conversion of a ground value need.
struct GroundFixture {
    grammar: k_rust::kompile::ProgramGrammar,
    main: String,
}

impl GroundFixture {
    fn load(source: &str, main: &str) -> Self {
        use k_rust::builtin::embedded;
        use k_rust::kompile::{CompilationBackend, ProgramGrammar};
        use k_rust::outer::{LoadOptions, ResolvedSource, load_with_options};
        let prelude = embedded("prelude.md").expect("embedded prelude should exist");
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("ground.k", source),
            main,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .expect("definition should load");
        let grammar =
            ProgramGrammar::new(&loaded.into_definition()).expect("program grammar should build");
        Self {
            grammar,
            main: main.to_owned(),
        }
    }

    fn resolved(&self) -> &ResolvedDefinition {
        self.grammar.resolved()
    }

    fn ground(&self, module: &str) -> ProgramParser {
        ProgramParser::for_ground_values(self.resolved(), module)
            .unwrap_or_else(|error| panic!("ground-value parser for {module}: {error}"))
    }

    fn plain(&self, module: &str) -> ProgramParser {
        ProgramParser::from_resolved(self.resolved(), module)
            .unwrap_or_else(|error| panic!("program parser for {module}: {error}"))
    }

    /// `text` parsed at `sort` by `parser`, expanded, placed at `sort` and converted to KORE.
    fn kore(&self, parser: &ProgramParser, sort: &str, text: &str) -> String {
        use k_rust::kompile::{
            MacroExpansionDefinition, SortInjector, term_to_kore_from_resolved_with_token_module,
        };
        let sort = Sort::new(sort);
        let parsed = parser
            .parse(&sort, text)
            .unwrap_or_else(|error| panic!("{text:?} at {sort} should parse: {error}"));
        let macros = MacroExpansionDefinition::prepare(self.grammar.definition())
            .expect("macros should prepare");
        let expanded = macros
            .expand_program(&self.main, parsed, &sort)
            .expect("the value should expand");
        let placed = SortInjector::new(self.resolved(), &self.main)
            .expect("injector should build")
            .inject(expanded.term(), &sort)
            .expect("the value should be placed");
        term_to_kore_from_resolved_with_token_module(
            self.resolved(),
            &self.main,
            parser.module(),
            &placed,
        )
        .expect("the value should convert")
        .to_string()
    }
}

/// The error of parsing `text` at `sort`, which must be an ambiguity.
fn ambiguity(parser: &ProgramParser, sort: &str, text: &str) -> String {
    let error = parser
        .parse(&Sort::new(sort), text)
        .expect_err(&format!("{text:?} at {sort} should be ambiguous"));
    assert!(
        matches!(*error.error, ParseError::Ambiguous { .. }),
        "{text:?} at {sort}: expected an ambiguity, got {error}"
    );
    error.to_string()
}

/// A definition with user lists (`Exps`, `Operands`), a constructor list (`Instrs`), `Id` and
/// `Int` tokens, a user `Exp` bracket, a user non-bracket `( .. )` production (`Wrapped`), an
/// `avoid` and a `prefer` one over sorts of their own (`AWrapped` over `Op2`, `PWrapped` over
/// `Pr`), a production ending in K (`push`), a K-sorted function (`kfun`), a user terminal
/// containing `~>` (`<~>`) and a regex token that can spell `.K` (`Field`).
const GROUND: &str = r#"
module GROUND-SYNTAX
  imports ID-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  syntax Field ::= r"\\.[A-Za-z]+" [token]
  syntax Exp ::= Id | Int
               | Id "(" Exps ")" [symbol(call)]
               | "(" Exp ")" [bracket]
               | Exp "+" Exp [symbol(plus), left]
               | Exp "<~>" Exp [symbol(swap)]
               | Exp Field [symbol(access)]
  syntax Exps ::= List{Exp, ","} [symbol(exps)]
  syntax Operand ::= "op" Int [symbol(op)]
  syntax Operands ::= List{Operand, ""} [symbol(operands)]
  syntax Wrapped ::= "(" Operand ")" [symbol(wrapped)]
  syntax Op2 ::= "op2" Int [symbol(op2)]
  syntax AWrapped ::= "(" Op2 ")" [symbol(awrapped), avoid]
  syntax Pr ::= "pr" Int [symbol(pr)]
  syntax PWrapped ::= "(" Pr ")" [symbol(pwrapped), prefer]
  syntax Instr ::= "trap" [symbol(trap)]
  syntax Instrs ::= ".Instrs" [symbol(instrsEmpty)] | Instr ";" Instrs [symbol(instrsCons)]
  syntax KItem ::= "push" K [symbol(push)]
  syntax K ::= kfun(Int) [function, symbol(kfun)]
endmodule
module GROUND
  imports GROUND-SYNTAX
  imports ID
  imports INT
  configuration <k> $PGM:K </k>
endmodule
module GROUND-KSEQ
  imports GROUND
  imports KSEQ
endmodule
module GROUND-K
  imports GROUND
  imports K
endmodule
module KSEQ-HELPER
  imports KSEQ
endmodule
module GROUND-VIA
  imports GROUND
  imports KSEQ-HELPER
endmodule
module GROUND-SPEC
  imports GROUND
  syntax Decl ::= "decl" Int [symbol(decl)]
  syntax Decls ::= List{Decl, ""} [symbol(decls)]
  syntax Instrs0 ::= List{Instr, ""} [symbol(instrs0)]
  syntax Spec ::= Decls Instrs0 [symbol(spec)]
endmodule
module GROUND-LIST-ITEM
  imports GROUND
  syntax KItem ::= Operands
endmodule
module GROUND-NESTED
  imports GROUND
  syntax Ty ::= "ty" Int [symbol(ty)]
  syntax Tys ::= List{Ty, ""} [symbol(tys)]
  syntax Tyss ::= List{Tys, ":"} [symbol(tyss)]
  syntax KItem ::= tyss(Tyss) [symbol(tyssItem)]
endmodule
"#;

fn ground_fixture() -> GroundFixture {
    GroundFixture::load(GROUND, "GROUND")
}

#[test]
fn ground_values_parse_sequences_over_user_lists() {
    let fixture = ground_fixture();
    let parser = fixture.ground("GROUND");
    let id =
        |name: &str| format!(r#"inj{{SortId{{}}, SortKItem{{}}}}(\dv{{SortId{{}}}}("{name}"))"#);
    let id_exp =
        |name: &str| format!(r#"inj{{SortId{{}}, SortExp{{}}}}(\dv{{SortId{{}}}}("{name}"))"#);
    let int_exp =
        |value: &str| format!(r#"inj{{SortInt{{}}, SortExp{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#);
    let exp = |pattern: String| format!("inj{{SortExp{{}}, SortKItem{{}}}}({pattern})");
    let plus = exp(format!("Lblplus{{}}({}, {})", int_exp("1"), int_exp("2")));
    let op = |value: &str| {
        format!(
            r#"inj{{SortOperand{{}}, SortKItem{{}}}}(Lblop{{}}(\dv{{SortInt{{}}}}("{value}")))"#
        )
    };
    let trap = "inj{SortInstr{}, SortKItem{}}(Lbltrap{}())".to_owned();
    let seq = |items: &[String]| {
        items
            .iter()
            .rev()
            .fold("dotk{}()".to_owned(), |tail, item| {
                format!("kseq{{}}({item}, {tail})")
            })
    };
    let empty_exps = r#"Lbl'Stop'List'LBraQuot'exps'QuotRBra'{}()"#;
    let call = |name: &str, arguments: &[&str]| {
        let list = arguments
            .iter()
            .rev()
            .fold(empty_exps.to_owned(), |tail, argument| {
                format!("Lblexps{{}}({}, {tail})", id_exp(argument))
            });
        exp(format!(
            r#"Lblcall{{}}(\dv{{SortId{{}}}}("{name}"), {list})"#
        ))
    };

    for (text, expected) in [
        ("x", seq(&[id("x")])),
        ("1 + 2", seq(std::slice::from_ref(&plus))),
        ("op 1", seq(&[op("1")])),
        (
            "f(x, y) ~> 1 + 2",
            seq(&[call("f", &["x", "y"]), plus.clone()]),
        ),
        ("trap ~> .K", seq(std::slice::from_ref(&trap))),
        (
            "trap ~> .Instrs",
            seq(&[
                trap.clone(),
                "inj{SortInstrs{}, SortKItem{}}(LblinstrsEmpty{}())".to_owned(),
            ]),
        ),
        ("trap ~> op 1", seq(&[trap.clone(), op("1")])),
        (".K", seq(&[])),
        ("x ~> .K ~> y", seq(&[id("x"), id("y")])),
        (
            "x <~> y ~> f(a)",
            seq(&[
                exp(format!("Lblswap{{}}({}, {})", id_exp("x"), id_exp("y"))),
                call("f", &["a"]),
            ]),
        ),
        ("(x ~> y) ~> x", seq(&[id("x"), id("y"), id("x")])),
        // A K-sorted function application is lowered as written, not evaluated.
        (
            "kfun(1) ~> x",
            format!(
                r#"append{{}}(Lblkfun{{}}(\dv{{SortInt{{}}}}("1")), {})"#,
                seq(&[id("x")])
            ),
        ),
    ] {
        assert_eq!(fixture.kore(&parser, "K", text), expected, "{text:?} at K");
    }

    // The added terminal `.K` takes precedence over an equal-length `Field` token at every start
    // sort, so `x.K` is not writable in a ground value; the longest match still reads `.Kx`.
    for sort in ["K", "KItem"] {
        let error = parser
            .parse(&Sort::new(sort), "x.K")
            .expect_err("`.K` is read as the terminal in a ground value");
        assert!(
            matches!(*error.error, ParseError::NoParse { .. }),
            "x.K at {sort}: {error}"
        );
    }
    assert_eq!(
        fixture.kore(&fixture.plain("GROUND"), "KItem", "x.K"),
        exp(format!(
            r#"Lblaccess{{}}({}, \dv{{SortField{{}}}}(".K"))"#,
            id_exp("x")
        )),
    );
    assert_eq!(
        fixture.kore(&parser, "K", "x.Kx ~> y"),
        seq(&[
            exp(format!(
                r#"Lblaccess{{}}({}, \dv{{SortField{{}}}}(".Kx"))"#,
                id_exp("x")
            )),
            id("y"),
        ]),
    );
}

/// A definition whose own `Exp` production reuses the terminal `~>`, with an `Exp` bracket and a
/// production over K on both sides.
const ARROW: &str = r#"
module ARROW
  imports ID-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  imports ID
  imports INT
  syntax Exp ::= Id | Int | Exp "~>" Exp [symbol(arrow), left] | "(" Exp ")" [bracket]
  syntax KItem ::= K "then" K [symbol(then)]
  configuration <k> $PGM:K </k>
endmodule
"#;

#[test]
fn the_k_bracket_only_groups_what_the_definition_does_not_read() {
    let fixture = ground_fixture();
    let parser = fixture.ground("GROUND");
    let op = |value: &str| format!(r#"Lblop{{}}(\dv{{SortInt{{}}}}("{value}"))"#);
    let item_op = |value: &str| format!("inj{{SortOperand{{}}, SortKItem{{}}}}({})", op(value));
    let wrapped = |value: &str| {
        format!(
            "inj{{SortWrapped{{}}, SortKItem{{}}}}(Lblwrapped{{}}({}))",
            op(value)
        )
    };
    let id =
        |name: &str| format!(r#"inj{{SortId{{}}, SortKItem{{}}}}(\dv{{SortId{{}}}}("{name}"))"#);
    let seq = |items: &[String]| {
        items
            .iter()
            .rev()
            .fold("dotk{}()".to_owned(), |tail, item| {
                format!("kseq{{}}({item}, {tail})")
            })
    };
    let int_exp =
        |value: &str| format!(r#"inj{{SortInt{{}}, SortExp{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#);
    let push = |argument: String| format!("Lblpush{{}}({argument})");

    // The definition's own `( .. )` production reads the text; the K bracket groups only what
    // nothing else reads.
    assert_eq!(fixture.kore(&parser, "K", "(op 1)"), seq(&[wrapped("1")]));
    assert_eq!(
        fixture.kore(&parser, "K", "(op 1) ~> op 2"),
        seq(&[wrapped("1"), item_op("2")])
    );
    assert_eq!(
        fixture.kore(&parser, "K", "(op 1 ~> op 2)"),
        seq(&[item_op("1"), item_op("2")])
    );
    assert_eq!(
        fixture.kore(&parser, "K", "(1 + 2)"),
        seq(&[format!(
            "inj{{SortExp{{}}, SortKItem{{}}}}(Lblplus{{}}({}, {}))",
            int_exp("1"),
            int_exp("2")
        )])
    );
    // A production ending in K: the structural preference reads the outer sequence.
    assert_eq!(
        fixture.kore(&parser, "K", "push (x ~> y)"),
        seq(&[push(seq(&[id("x"), id("y")]))])
    );
    assert_eq!(
        fixture.kore(&parser, "K", "push x ~> y"),
        seq(&[push(seq(&[id("x")])), id("y")])
    );

    // A definition's own `avoid` `( .. )` production competes with the avoided K bracket on
    // equal terms: both readings are avoided, so the item is an ambiguity at K and parses only
    // at its own sort's level.
    ambiguity(&parser, "K", "(op2 1)");
    ambiguity(&parser, "K", "((op2 1))");
    ambiguity(&parser, "K", "(op2 1) ~> op2 2");
    assert_eq!(
        fixture.kore(&parser, "KItem", "(op2 1)"),
        r#"inj{SortAWrapped{}, SortKItem{}}(Lblawrapped{}(Lblop2{}(\dv{SortInt{}}("1"))))"#
    );
    // A `prefer` one wins over the K bracket, which still groups a sequence.
    let pr = |value: &str| format!(r#"Lblpr{{}}(\dv{{SortInt{{}}}}("{value}"))"#);
    assert_eq!(
        fixture.kore(&parser, "K", "(pr 1)"),
        seq(&[format!(
            "inj{{SortPWrapped{{}}, SortKItem{{}}}}(Lblpwrapped{{}}({}))",
            pr("1")
        )])
    );
    assert_eq!(
        fixture.kore(&parser, "K", "(pr 1 ~> pr 2)"),
        seq(&[
            format!("inj{{SortPr{{}}, SortKItem{{}}}}({})", pr("1")),
            format!("inj{{SortPr{{}}, SortKItem{{}}}}({})", pr("2")),
        ])
    );

    // At K a `~>` is the sequence wherever a sequence may stand; the definition's own `~>`
    // production is read inside its own sort.
    let arrows = GroundFixture::load(ARROW, "ARROW");
    let parser = arrows.ground("ARROW");
    let id_exp =
        |name: &str| format!(r#"inj{{SortId{{}}, SortExp{{}}}}(\dv{{SortId{{}}}}("{name}"))"#);
    let arrow =
        |left: &str, right: &str| format!("Lblarrow{{}}({}, {})", id_exp(left), id_exp(right));
    assert_eq!(
        arrows.kore(&parser, "K", "a ~> b"),
        seq(&[id("a"), id("b")])
    );
    assert_eq!(arrows.kore(&parser, "Exp", "a ~> b"), arrow("a", "b"));
    assert_eq!(
        arrows.kore(&parser, "K", "(a ~> b) ~> c"),
        seq(&[
            format!("inj{{SortExp{{}}, SortKItem{{}}}}({})", arrow("a", "b")),
            id("c")
        ])
    );
    ambiguity(&parser, "K", "a ~> b ~> c");
    let then = |left: String, right: String| format!("Lblthen{{}}({left}, {right})");
    assert_eq!(
        arrows.kore(&parser, "K", "a ~> b then c"),
        seq(&[id("a"), then(seq(&[id("b")]), seq(&[id("c")]))])
    );
    assert_eq!(
        arrows.kore(&parser, "K", "a then b ~> c"),
        seq(&[then(seq(&[id("a")]), seq(&[id("b")])), id("c")])
    );
}

#[test]
fn ground_values_refuse_a_module_that_sees_k_top_sort() {
    let fixture = ground_fixture();
    for (module, via) in [
        ("GROUND-KSEQ", "KSEQ"),
        ("GROUND-K", "K"),
        ("GROUND-VIA", "KSEQ"),
    ] {
        let error = ProgramParser::for_ground_values(fixture.resolved(), module)
            .expect_err("a module that sees K-TOP-SORT is refused");
        assert_eq!(
            error,
            ProgramError::KSequenceModuleVisible {
                module: module.to_owned(),
                via: via.to_owned(),
            }
        );
        let message = error.to_string();
        for part in [
            format!("module {module:?} sees K-TOP-SORT through {via:?}"),
            "makes every user-list element ambiguous".to_owned(),
            format!("pass a module that does not import {via:?}"),
            "a module importing the syntax and main modules".to_owned(),
            "`from_resolved`".to_owned(),
        ] {
            assert!(message.contains(&part), "{message}");
        }
    }
    // Why: through K-TOP-SORT's `KItem ::= S`, an element of a user list reaches KItem both as
    // itself and as its one-element list.
    let with_kseq = fixture.plain("GROUND-KSEQ");
    for text in ["x", "op 1"] {
        let message = ambiguity(&with_kseq, "K", text);
        assert!(message.contains("userList"), "{text:?}: {message}");
    }
}

#[test]
fn program_parsers_keep_no_sequence_syntax() {
    let fixture = ground_fixture();
    let parser = fixture.plain("GROUND");
    for text in ["a ~> b", "trap ~> .K", "(a ~> b)"] {
        let error = parser
            .parse(&Sort::new("K"), text)
            .expect_err("a program grammar has no sequence syntax");
        assert!(
            matches!(*error.error, ParseError::NoParse { .. }),
            "{text:?}: {error}"
        );
    }
    // Without the `.K` terminal, the text is the definition's own `Field` token.
    assert_eq!(
        fixture.kore(&parser, "K", ".K"),
        r#"kseq{}(inj{SortField{}, SortKItem{}}(\dv{SortField{}}(".K")), dotk{}())"#
    );
}

/// Program tokens and layout only in the syntax module, an internal production only in the main
/// module, and neither module imports BASIC-K, so `K ::= KItem` comes from the ground grammar.
const SPLIT: &str = r#"
module SPLIT-COMMON
  syntax Word
  syntax Instr ::= "say" Word [symbol(say)]
endmodule
module SPLIT-SYNTAX
  imports SPLIT-COMMON
  syntax Word ::= r"[a-z]+" [token]
  syntax #Layout ::= r"[\\ \\n]"
endmodule
module SPLIT
  imports SPLIT-COMMON
  syntax Instr ::= "halt" [symbol(halt)]
  configuration <k> $PGM:K </k>
endmodule
module SPLIT-UNION
  imports SPLIT-SYNTAX
  imports SPLIT
endmodule
"#;

#[test]
fn ground_values_need_the_union_of_syntax_and_main_modules() {
    let fixture = GroundFixture::load(SPLIT, "SPLIT");
    let error = fixture
        .ground("SPLIT")
        .parse(&Sort::new("K"), "say hello ~> halt")
        .expect_err("the main module has no lexical syntax for the program token");
    assert!(
        matches!(*error.error, ParseError::NoParse { .. }),
        "{error}"
    );
    let union = fixture.ground("SPLIT-UNION");
    assert_eq!(
        fixture.kore(&union, "K", "say hello ~> halt"),
        r#"kseq{}(inj{SortInstr{}, SortKItem{}}(Lblsay{}(\dv{SortWord{}}("hello"))), kseq{}(inj{SortInstr{}, SortKItem{}}(Lblhalt{}()), dotk{}()))"#
    );
}

#[test]
fn nullable_list_productions_make_items_ambiguous() {
    let fixture = ground_fixture();
    // `Spec ::= Decls Instrs0` derives every instruction through two empty-or-one lists.
    let message = ambiguity(&fixture.ground("GROUND-SPEC"), "K", "trap");
    assert!(message.contains("syntax Spec ::="), "{message}");
    let message = ambiguity(&fixture.plain("GROUND-SPEC"), "KItem", "trap");
    assert!(message.contains("syntax Spec ::="), "{message}");
    let narrower = fixture.ground("GROUND");
    assert_eq!(
        fixture.kore(&narrower, "K", "trap"),
        "kseq{}(inj{SortInstr{}, SortKItem{}}(Lbltrap{}()), dotk{}())"
    );
    // Nested nullable lists: `tyss()` holds an empty `Tyss` or a `Tyss` of one empty `Tys`.
    ambiguity(&fixture.ground("GROUND-NESTED"), "K", "tyss()");
    ambiguity(&fixture.plain("GROUND-NESTED"), "KItem", "tyss()");

    // A list-sorted value is not an item, so it is no sequence element; a cell of the list sort
    // is parsed at that sort.
    let error = narrower
        .parse(&Sort::new("K"), "op 1 op 2 ~> trap")
        .expect_err("a list value is not an item of K");
    assert!(
        matches!(*error.error, ParseError::NoParse { .. }),
        "{error}"
    );
    let _ = narrower
        .parse(&Sort::new("Operands"), "op 1 op 2")
        .expect("a list value parses at its own sort");
    // A definition's own `KItem ::= Operands` makes each element ambiguous with its one-element
    // list, through either parser.
    ambiguity(&fixture.ground("GROUND-LIST-ITEM"), "K", "op 1");
    ambiguity(&fixture.plain("GROUND-LIST-ITEM"), "KItem", "op 1");
}
