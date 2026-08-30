use indoc::indoc;
use k_rust::definition::{Definition, LabelHead, ResolvedDefinition};
use k_rust::inner::{ParseError, ProgramError, ProgramParser, parse_program};
use k_rust::kast::{Sort, Term};
use k_rust::provenance::SourceId;

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

#[cfg(not(feature = "z3-inference"))]
fn assert_ambiguous_program_requires_z3(definition: &Definition, start_sort: &str, source: &str) {
    let error = parse_program(
        definition,
        "MAIN",
        &Sort::new(start_sort),
        source,
        SourceId(0),
    )
    .expect_err("an ambiguous program should require Z3 inference");
    assert!(
        matches!(
            error,
            ProgramError::Parse(ref error)
                if matches!(
                    *error.error,
                    ParseError::Z3InferenceRequired {
                        ambiguity: true,
                        parametric_sorts: false,
                    }
                )
        ),
        "{error:?}"
    );
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
        .metadata()
        .and_then(|metadata| metadata.production)
        .expect("parsed application should retain its production identity");
    assert_eq!(
        parsed.metadata().and_then(|metadata| metadata.span),
        None,
        "legacy parsing must not fabricate an unknown source identity",
    );
    let module = resolved.module_id("MAIN").expect("module should exist");
    let catalog = resolved.production_catalog(module);
    let expected = catalog.productions_for(&LabelHead::new("a"));

    assert_eq!(expected.len(), 1);
    assert_eq!(production.0, expected[0].0);
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
    let Term::Apply { arguments, .. } = parsed.unannotated() else {
        panic!("expected an application")
    };

    for term in [&parsed, &arguments[0]] {
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
        parsed.metadata().and_then(|metadata| metadata.span),
        Some(k_rust::kast::TermSpan {
            source: SourceId(7),
            start: 0,
            end: 1,
        })
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
        let rendered = term.to_string();
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
        let rendered = term.to_string();
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
    let rendered = parsed.to_string();

    for label in ["module", "defns", "func", "results", "instrs"] {
        assert!(rendered.contains(label), "missing {label}: {rendered}");
    }
    assert!(!rendered.contains("bodyItems"), "{rendered}");
}

#[test]
fn preserves_outer_list_terminator_after_an_empty_inner_overloaded_list() {
    let definition = wasm_empty_function_overloaded_lists();
    #[cfg(not(feature = "z3-inference"))]
    assert_ambiguous_program_requires_z3(&definition, "Module", "(module (func))");
    #[cfg(feature = "z3-inference")]
    {
        let rendered = parse_program(
            &definition,
            "MAIN",
            &Sort::new("Module"),
            "(module (func))",
            SourceId(0),
        )
        .expect("an empty function should parse uniquely inside its module")
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
    #[cfg(not(feature = "z3-inference"))]
    assert_ambiguous_program_requires_z3(&definition, "Stmts", "i32.const 1");
    #[cfg(feature = "z3-inference")]
    {
        let rendered = parse_program(
            &definition,
            "MAIN",
            &Sort::new("Stmts"),
            "i32.const 1",
            SourceId(0),
        )
        .expect("a root singleton should be reconstructed as a list")
        .to_string();

        assert!(rendered.contains("instrs"), "{rendered}");
        assert!(!rendered.contains("stmts"), "{rendered}");
        assert!(rendered.contains(".List"), "{rendered}");
    }
}

#[test]
fn parses_an_empty_program_at_a_root_list_sort() {
    let definition = wasm_shaped_overloaded_lists();
    #[cfg(not(feature = "z3-inference"))]
    assert_ambiguous_program_requires_z3(&definition, "Stmts", "");
    #[cfg(feature = "z3-inference")]
    {
        let rendered = parse_program(&definition, "MAIN", &Sort::new("Stmts"), "", SourceId(0))
            .expect("the empty list should parse at a root list sort")
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
    .to_string();
    let laid_out = parse_program(
        &definition,
        "MAIN",
        &Sort::new("Module"),
        "( // open\n module // first function\n ( func ) // second function\n ( func ) // close\n )",
        SourceId(0),
    )
    .expect("layout and comments should not affect parsing")
    .to_string();

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
