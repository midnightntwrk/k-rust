//! The library contract of `ConfigurationAssembler`: which grammar parses each input, how each
//! value is sorted and converted, the order of the configuration map, and structured errors.

use std::collections::BTreeMap;

use k_rust::{
    builtin::embedded,
    definition::{Attributes, Definition, ResolvedDefinition},
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ConfigurationError,
        ProgramGrammar, compile_loaded_definition, compile_search_pattern,
    },
    kore::printer::Printer,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

struct Compiled {
    frontend: Definition,
    execution: Definition,
    variables: BTreeMap<String, Sort>,
}

fn compiled(source: &str, main_module: &str) -> Compiled {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("test.k", source),
        main_module,
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
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            ..CompileOptions::default()
        },
    )
    .expect("definition should compile");
    Compiled {
        frontend: loaded.definition,
        execution: artifacts.execution_definition,
        variables: artifacts.configuration_variables,
    }
}

const DEFINITION: &str = r#"
module ENV-SORT
  syntax Env
endmodule

module ENV-PARSER
  imports ENV-SORT
  syntax Env ::= "selected" [symbol(selectedEnv)]
endmodule

module NAME-PARSER
  syntax Name [hook(STRING.String)]
  syntax Name ::= r"[\\\"][a-z]*[\\\"]" [token]
endmodule

module SYNTAX
  syntax Input ::= "go" [symbol(go)]
endmodule

module MAIN
  imports ENV-PARSER
  imports SYNTAX
  syntax Env ::= "main" [symbol(mainEnv)]
  syntax Name
  syntax Input ::= "done" [symbol(done)]
                 | "configMacro" [macro, symbol(configMacro)]
  syntax String [hook(STRING.String)]
  rule configMacro => done
  configuration <k> $PGM:Input </k>
                <env parser="ENV, ENV-PARSER"> $ENV:Env </env>
                <name parser="NAME, NAME-PARSER"> $NAME:Name </name>
                <any> $ANY:K </any>
                <state> $STATE:Input </state>
                <stdin> $STDIN:String </stdin>
endmodule
"#;

fn render(pattern: &k_rust::kore::ast::Pattern) -> String {
    Printer::compact().print_pattern(pattern)
}

fn entry(name: &str, value: &str) -> String {
    format!(
        r#"Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortKConfigVar{{}}, SortKItem{{}}}}(\dv{{SortKConfigVar{{}}}}("${name}")), {value})"#
    )
}

fn assembler<'g>(
    grammar: &'g ProgramGrammar,
    compiled: &'g Compiled,
) -> ConfigurationAssembler<'g> {
    ConfigurationAssembler::new(grammar, "MAIN", "SYNTAX", &compiled.variables)
}

fn bind_all_but(assembler: &mut ConfigurationAssembler<'_>, skipped: &str) {
    for (name, text) in [
        ("ENV", "selected"),
        ("NAME", "\"abc\""),
        ("ANY", "done"),
        ("STATE", "done"),
        ("STDIN", "\"text\""),
    ] {
        if name != skipped {
            assembler.bind(name, text).unwrap();
        }
    }
}

#[test]
fn every_input_is_parsed_expanded_injected_and_converted_by_its_own_grammar() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    assembler.program(&Sort::new("Input"), "go").unwrap();
    // Bound in an order other than name order: the map keeps the order of binding.
    assembler.bind("$STATE", "configMacro").unwrap();
    assembler.bind("ENV", "selected").unwrap();
    assembler.bind("NAME", "\"abc\"").unwrap();
    assembler.bind("ANY", "done").unwrap();
    assembler.bind("STDIN", "\"text\"").unwrap();
    let rendered = render(&assembler.finish().unwrap());

    let entries = [
        // The program is parsed with the syntax module.
        entry("PGM", "inj{SortInput{}, SortKItem{}}(Lblgo{}())"),
        // A macro in a value is expanded in the main module.
        entry("STATE", "inj{SortInput{}, SortKItem{}}(Lbldone{}())"),
        // The cell's parser attribute selects ENV-PARSER, whose production is the value.
        entry("ENV", "inj{SortEnv{}, SortKItem{}}(LblselectedEnv{}())"),
        // NAME-PARSER's STRING hook decodes its token although the main module has none.
        entry(
            "NAME",
            r#"inj{SortName{}, SortKItem{}}(\dv{SortName{}}("abc"))"#,
        ),
        // A K-sorted variable is one item, injected from its own sort.
        entry("ANY", "inj{SortInput{}, SortKItem{}}(Lbldone{}())"),
        // $STDIN has no parser attribute and is parsed as a String literal.
        entry(
            "STDIN",
            r#"inj{SortString{}, SortKItem{}}(\dv{SortString{}}("text"))"#,
        ),
    ];
    let mut position = 0;
    for expected in entries {
        let found = rendered[position..]
            .find(&expected)
            .unwrap_or_else(|| panic!("missing or out of order {expected} in {rendered}"));
        position += found + expected.len();
    }
    assert!(
        rendered.starts_with("LblinitGeneratedTopCell{}("),
        "{rendered}"
    );
    assert!(!rendered.contains("LblconfigMacro"), "{rendered}");
    assert!(!rendered.contains("kseq"), "{rendered}");
}

#[test]
fn the_parser_attribute_excludes_the_main_module_grammar() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    let error = assembler.bind("ENV", "main").unwrap_err();
    let ConfigurationError::Parse { variable, sort, .. } = &error else {
        panic!("unexpected error {error:?}");
    };
    assert_eq!(variable, "ENV");
    assert_eq!(sort, &Sort::new("Env"));
    assert!(
        error
            .to_string()
            .starts_with("could not parse configuration variable `$ENV` at sort Env: "),
        "{error}"
    );
}

#[test]
fn stream_defaults_follow_explicit_bindings_and_read_input_only_when_used() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    assembler.program(&Sort::new("Input"), "go").unwrap();
    bind_all_but(&mut assembler, "STDIN");
    assembler
        .bind_stream_defaults(false, false, || {
            Ok::<_, ConfigurationError>(b"from input".to_vec())
        })
        .unwrap();
    let rendered = render(&assembler.finish().unwrap());
    let state = rendered.find("\"$STATE\"").unwrap();
    let stdin = rendered.find("\"$STDIN\"").unwrap();
    assert!(state < stdin, "{rendered}");
    assert!(
        rendered.contains(r#"\dv{SortString{}}("from input")"#),
        "{rendered}"
    );

    // An explicit $STDIN is kept and the input is not read.
    assembler.program(&Sort::new("Input"), "go").unwrap();
    bind_all_but(&mut assembler, "");
    assembler
        .bind_stream_defaults(false, false, || -> Result<Vec<u8>, ConfigurationError> {
            panic!("input read although $STDIN is bound")
        })
        .unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(
        rendered.contains(r#"\dv{SortString{}}("text")"#),
        "{rendered}"
    );
}

#[test]
fn names_are_checked_before_the_value_is_parsed() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    assembler.bind("STATE", "done").unwrap();
    assert!(matches!(
        assembler.bind("$STATE", "not parsable"),
        Err(ConfigurationError::Duplicate { name }) if name == "STATE"
    ));
    assert!(matches!(
        assembler.bind("$", "done"),
        Err(ConfigurationError::EmptyName)
    ));
    assert!(matches!(
        assembler.bind("PGM", "not parsable"),
        Err(ConfigurationError::ProgramVariable)
    ));
    let error = assembler.bind("MISSING", "not parsable").unwrap_err();
    let ConfigurationError::UnknownVariable { name, available } = &error else {
        panic!("unexpected error {error:?}");
    };
    assert_eq!(name, "MISSING");
    assert_eq!(
        available,
        &["$ANY", "$ENV", "$NAME", "$STATE", "$STDIN"].map(String::from)
    );
    assert_eq!(
        error.to_string(),
        "definition has no configuration variable `$MISSING`; available variables: \
         $ANY, $ENV, $NAME, $STATE, $STDIN"
    );
}

#[test]
fn a_k_sorted_variable_denotes_one_item() {
    let compiled = compiled(DEFINITION, "MAIN");
    // Compilation records `$ANY:K` at `KItem`; a caller's own map may still say `K`.
    assert_eq!(compiled.variables["ANY"], Sort::new("KItem"));
    let variables = BTreeMap::from([("ANY".to_owned(), Sort::new("K"))]);
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "SYNTAX", &variables);
    let error = assembler.bind("ANY", "done ~> done").unwrap_err();
    assert!(
        matches!(&error, ConfigurationError::Parse { variable, sort, .. }
            if variable == "ANY" && sort == &Sort::new("K")),
        "{error:?}"
    );
    assembler.bind("ANY", "done").unwrap();
}

#[test]
fn a_failed_bind_leaves_the_configuration_unchanged() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    assert!(matches!(
        assembler.bind("STATE", "not parsable"),
        Err(ConfigurationError::Parse { .. })
    ));
    assembler.bind("STATE", "done").unwrap();
}

#[test]
fn finish_names_every_unbound_variable_and_the_program_first() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    assembler.bind("ENV", "selected").unwrap();
    assembler.bind("NAME", "\"abc\"").unwrap();
    let error = assembler.finish().unwrap_err();
    let ConfigurationError::Missing { names } = &error else {
        panic!("unexpected error {error:?}");
    };
    assert_eq!(
        names,
        &["$PGM", "$ANY", "$STATE", "$STDIN"].map(String::from)
    );
    assert_eq!(
        error.to_string(),
        "missing required configuration variables $PGM, $ANY, $STATE, $STDIN"
    );

    // Nothing was discarded: binding the rest completes the same configuration.
    assembler.program(&Sort::new("Input"), "go").unwrap();
    assert!(matches!(
        assembler.program(&Sort::new("Input"), "go"),
        Err(ConfigurationError::Duplicate { name }) if name == "PGM"
    ));
    assembler.bind("ANY", "done").unwrap();
    assembler.bind("STDIN", "\"text\"").unwrap();
    let error = assembler.finish().unwrap_err();
    assert_eq!(
        error.to_string(),
        "missing required configuration variable $STATE"
    );
    assembler.bind("STATE", "done").unwrap();
    assembler.finish().unwrap();
    // `clear` discards a partial configuration.
    bind_all_but(&mut assembler, "STATE");
    assembler.clear();
    bind_all_but(&mut assembler, "");
    assembler.program(&Sort::new("Input"), "go").unwrap();
    assembler.finish().unwrap();
    // A finished assembler starts the next configuration empty.
    assert!(matches!(
        assembler.finish(),
        Err(ConfigurationError::Missing { names }) if names.len() == 6
    ));
}

#[test]
fn a_program_is_bound_even_when_no_cell_reads_it() {
    let compiled = compiled(
        r#"
module MAIN
  syntax State ::= "ready" [symbol(ready)]
  configuration <k> ready </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assert_eq!(
        render(&assembler.finish().unwrap()),
        "LblinitGeneratedTopCell{}()"
    );
    assembler.program(&Sort::new("State"), "ready").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(rendered.contains("\"$PGM\""), "{rendered}");
}

#[test]
fn a_string_stream_without_string_syntax_reports_the_missing_parser_module() {
    let parsed = k_rust::outer::parse(
        "test.k",
        r#"
module MAIN
  syntax String [hook(STRING.String)]
endmodule
"#,
    )
    .unwrap();
    let frontend = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let variables = BTreeMap::from([("STDIN".to_owned(), Sort::new("String"))]);
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &variables);
    let error = assembler.bind("STDIN", "\"text\"").unwrap_err();
    let ConfigurationError::ParserModuleNotFound { variable, module } = &error else {
        panic!("unexpected error {error:?}");
    };
    assert_eq!(
        (variable.as_str(), module.as_str()),
        ("STDIN", "STRING-SYNTAX")
    );
    assert_eq!(
        error.to_string(),
        "parser module `STRING-SYNTAX` for configuration variable `$STDIN` was not found"
    );
}

#[test]
fn one_grammar_serves_the_assembler_and_a_search_pattern() {
    let compiled = compiled(DEFINITION, "MAIN");
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = assembler(&grammar, &compiled);
    assembler.program(&Sort::new("Input"), "go").unwrap();
    let execution = ResolvedDefinition::resolve(&compiled.execution).unwrap();
    compile_search_pattern(
        grammar.resolved(),
        &execution,
        "MAIN",
        "<k> done </k>",
        Attributes::default(),
    )
    .unwrap();
    bind_all_but(&mut assembler, "");
    assembler.finish().unwrap();
}
