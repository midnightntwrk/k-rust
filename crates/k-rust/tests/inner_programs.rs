use indoc::indoc;
use k_rust::definition::{Definition, LabelHead, ResolvedDefinition};
use k_rust::inner::{ParseError, ProgramError, ProgramParser, parse_program};
use k_rust::kast::Sort;

fn lowered(source: &str, main_module: &str) -> Definition {
    let parsed = k_rust::outer::parse("program.k", source).expect("definition should parse");
    k_rust::outer::lower(&parsed, main_module).expect("definition should lower")
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
    let module = resolved.module_id("MAIN").expect("module should exist");
    let catalog = resolved.production_catalog(module);
    let expected = catalog.productions_for(&LabelHead::new("a"));

    assert_eq!(expected.len(), 1);
    assert_eq!(production.0, expected[0].0);
}

#[test]
fn deduplicates_overloaded_empty_list_parses_after_terminator_resolution() {
    let definition = lowered(
        indoc! {r#"
            module BASE
              syntax Padding ::= "padding" [private]
              syntax EmptyStmt
              syntax Instr ::= EmptyStmt
              syntax Defn ::= EmptyStmt
              syntax Stmt ::= Instr | Defn
              syntax EmptyStmts ::= List{EmptyStmt, ""}
                [overload(listStmt), terminator-symbol(".List{\"listStmt\"}")]
              syntax Instrs ::= List{Instr, ""} [overload(listStmt)]
              syntax Defns ::= List{Defn, ""} [overload(listStmt)]
              syntax Stmts ::= List{Stmt, ""} [overload(listStmt)]
              syntax Instrs ::= EmptyStmts
              syntax Defns ::= EmptyStmts
              syntax Stmts ::= Instrs | Defns
            endmodule

            module MAIN
              imports BASE
              syntax ModuleDecl ::= "(" "module" Defns ")" [symbol(module)]
            endmodule
        "#},
        "MAIN",
    );

    parse_program(&definition, "MAIN", &Sort::new("ModuleDecl"), "(module)")
        .expect("metadata-only parse duplicates should collapse");
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
    let error = parse_program(&definition, "MAIN", &Sort::new("Exp"), "0[]").unwrap_err();
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
    let error = parse_program(&definition, "MAIN", &Sort::new("Start"), "hidden").unwrap_err();
    assert!(
        matches!(
            error,
            ProgramError::Parse(ref error)
                if matches!(*error.error, ParseError::NoParse { .. })
        ),
        "{error:?}"
    );
}
