//! The library contract of `ConfigurationAssembler`: which grammar parses each input, how each
//! value is sorted and converted, the order of the configuration map, and structured errors.

use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    builtin::embedded,
    definition::{Attributes, Definition, ResolvedDefinition},
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ConfigurationError,
        GroundCause, GroundInput, ProgramGrammar, SortInjectionError, UndeterminedCause,
        UndeterminedSite, compile_loaded_definition, compile_search_pattern,
    },
    kore::printer::Printer,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/shared.rs"]
mod shared;

struct Compiled {
    frontend: Definition,
    execution: Definition,
    kore: String,
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
        frontend: loaded.into_definition(),
        kore: artifacts.definition_kore,
        execution: artifacts.execution_definition,
        variables: artifacts.configuration_variables,
    }
}

/// `compiled(DEFINITION, "MAIN")`, compiled once per process and inference mode and shared by
/// the tests that only read it.
fn definition() -> Arc<Compiled> {
    static COMPILED: shared::Shared<Compiled> = shared::Shared::new();
    COMPILED.get(|| compiled(DEFINITION, "MAIN"))
}

/// `compiled(PHANTOM_CONFIGURATION, "MAIN")`, shared as [`definition`] is.
fn phantom_configuration() -> Arc<Compiled> {
    static COMPILED: shared::Shared<Compiled> = shared::Shared::new();
    COMPILED.get(|| compiled(PHANTOM_CONFIGURATION, "MAIN"))
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
        r#"Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortKConfigVar{{}}, SortKItem{{}}}}(\dv{{SortKConfigVar{{}}}}("${name}")), Lbl'Hash'KConfigValue{{}}(kseq{{}}({value}, dotk{{}}())))"#
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
    let compiled = definition();
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
    assert_eq!(rendered.matches("kseq{}(").count(), 6, "{rendered}");
}

#[test]
fn the_parser_attribute_excludes_the_main_module_grammar() {
    let compiled = definition();
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
    let compiled = definition();
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
    let compiled = definition();
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
fn a_k_sorted_variable_prefers_an_item_reading() {
    let compiled = definition();
    // The reader retains the declared K sort; item-only grammar still prefers its item reading.
    assert_eq!(compiled.variables["ANY"], Sort::new("K"));
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
    let compiled = definition();
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
    let compiled = definition();
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
    assert_eq!(rendered, "LblinitGeneratedTopCell{}()");
    assert!(!compiled.kore.contains("Lbl\'Hash\'KConfigValue"));
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
    let compiled = definition();
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

#[test]
fn a_reused_assembler_builds_what_a_fresh_one_builds() {
    // The parsed sort fixes this production's result parameter for every value. Reusing or
    // clearing the assembler must preserve those instances.
    let compiled = compiled(
        r#"
module MAIN
  syntax {S} S ::= "undef" [symbol(undef), function, total]
  syntax Foo ::= "foo" [symbol(foo)]
  configuration <k> $PGM:Foo </k> <x> $X:Foo </x> <y> $Y:K </y>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let build = |assembler: &mut ConfigurationAssembler<'_>| {
        assembler.program(&Sort::new("Foo"), "undef").unwrap();
        assembler.bind("X", "undef").unwrap();
        assembler.bind("Y", "undef").unwrap();
        render(&assembler.finish().unwrap())
    };
    let mut reused = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    let first = build(&mut reused);
    for (name, sort) in [("PGM", "Foo"), ("X", "Foo"), ("Y", "KItem")] {
        let value = format!("Lblundef{{Sort{sort}{{}}}}()");
        let value = if sort == "KItem" {
            value
        } else {
            format!("inj{{Sort{sort}{{}}, SortKItem{{}}}}({value})")
        };
        assert!(first.contains(&entry(name, &value)), "{first}");
    }
    assert!(!first.contains("SortParam"), "{first}");
    assert_eq!(build(&mut reused), first);
    // A configuration abandoned half-way leaves nothing behind either.
    reused.bind("X", "undef").unwrap();
    reused.clear();
    assert_eq!(build(&mut reused), first);
    let mut fresh = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assert_eq!(build(&mut fresh), first);
}

#[test]
fn a_program_result_parameter_is_fixed_by_its_read_sort() {
    let compiled = compiled(
        r#"
requires "domains.md"
module MAIN
  imports INT
  syntax {S} S ::= undef() [function, total, symbol(undef)]
  rule undef() => 0
  configuration <k> $PGM:Int </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("Int"), "undef()").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(
        rendered.contains(&entry(
            "PGM",
            "inj{SortInt{}, SortKItem{}}(Lblundef{SortInt{}}())"
        )),
        "{rendered}"
    );
    assert!(!rendered.contains("SortParam"), "{rendered}");
}

#[test]
fn a_program_read_at_k_is_instantiated_at_kitem() {
    let compiled = compiled(
        r#"
module MAIN
  syntax {S} S ::= undef() [function, total, symbol(undef)]
  configuration <k> $PGM:K </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("K"), "undef()").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(
        rendered.contains(&entry("PGM", "Lblundef{SortKItem{}}()")),
        "{rendered}"
    );
    assert!(!rendered.contains("SortK{}, SortKItem{}"), "{rendered}");
    assert!(!rendered.contains("SortParam"), "{rendered}");
}

const PHANTOM_CONFIGURATION: &str = r#"
requires "domains.md"
module MAIN
  imports INT
  syntax {S} Int ::= size() [function, total, symbol(size)]
  configuration <k> $PGM:Int </k> <x> $X:Int </x>
endmodule
"#;

fn assert_phantom_instance(error: ConfigurationError, expected_variable: &str) {
    let ConfigurationError::UndeterminedInstance {
        variable,
        error: injection,
    } = &error
    else {
        panic!("unexpected error {error:?}");
    };
    assert_eq!(variable, expected_variable);
    let SortInjectionError::UndeterminedInstance(instance) = injection.as_ref() else {
        panic!("unexpected injection error {injection:?}");
    };
    assert!(
        matches!(
            &instance.site,
            UndeterminedSite::Ground {
                input: GroundInput::Value,
                cause: GroundCause::Instance(UndeterminedCause::Phantom { label, parameter }),
            } if label == "size" && parameter == &Sort::new("S")
        ),
        "{instance:?}"
    );
    let message = error.to_string();
    assert!(message.contains(expected_variable), "{message}");
    assert!(message.contains("`size`"), "{message}");
    assert!(
        message.contains("occurs in neither its argument sorts nor its result sort"),
        "{message}"
    );
}

#[test]
fn a_phantom_program_instance_names_the_program_variable() {
    let compiled = phantom_configuration();
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    let error = assembler.program(&Sort::new("Int"), "size()").unwrap_err();
    assert_phantom_instance(error, "$PGM");
}

#[test]
fn a_phantom_configuration_instance_names_the_bound_variable() {
    let compiled = phantom_configuration();
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    let error = assembler.bind("$X", "size()").unwrap_err();
    assert_phantom_instance(error, "$X");
}

/// Brackets are concrete syntax, so `(size())` is the program `size()`. Read at `Foo`, its
/// parentheses parse both as `Foo`'s bracket over `size()` and as `Bar`'s bracket, which is one
/// reading once the brackets are erased. That reading's phantom parameter must not turn into a
/// choice between parses: the program is reported exactly as the unbracketed one.
#[test]
fn a_bracketed_phantom_program_instance_names_the_program_variable() {
    let compiled = compiled(
        r#"
module MAIN
  syntax Foo ::= Bar | "(" Foo ")" [bracket]
  syntax Bar ::= "(" Bar ")" [bracket]
  syntax {S} Bar ::= size() [function, total, symbol(size)]
  configuration <k> $PGM:Foo </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    for program in ["size()", "(size())", "((size()))"] {
        let error = assembler.program(&Sort::new("Foo"), program).unwrap_err();
        assert_phantom_instance(error, "$PGM");
    }
}

#[test]
fn a_phantom_value_diagnostic_offers_no_cast() {
    let compiled = phantom_configuration();
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    let program = assembler.program(&Sort::new("Int"), "size()").unwrap_err();
    let binding = assembler.bind("$X", "size()").unwrap_err();
    for error in [program, binding] {
        let message = error.to_string();
        assert!(message.contains("no sort cast can fix it"), "{message}");
        for forbidden in [
            "add a sort cast",
            "sentence sort variable",
            "only the sort of a predicate",
        ] {
            assert!(!message.contains(forbidden), "{message}");
        }
    }
}

#[test]
fn an_open_value_instance_names_the_read_sort() {
    let compiled = compiled(
        r#"module MAIN
  syntax Foo ::= "a" [symbol(a)]
  syntax {S} Foo ::= wrap(S) [symbol(wrap)]
  syntax {S} S ::= undef() [function, total, symbol(undef)]
  configuration <k> $PGM:Foo </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    let message = assembler
        .program(&Sort::new("Foo"), "wrap(undef())")
        .unwrap_err()
        .to_string();
    assert!(message.contains("read at"), "{message}");
    assert!(message.contains("wrap"), "{message}");
    assert!(
        !message.contains("only the sort of a predicate"),
        "{message}"
    );
    assert!(!message.contains("add a sort cast"), "{message}");
}

#[test]
fn a_program_read_at_k_selects_the_kitem_macro_instance() {
    let compiled = compiled(
        r#"
module MAIN
  syntax {S} S ::= m() [macro, symbol(m)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
  rule m():KItem => a
  rule m():K => b
  configuration <k> $PGM:K </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("K"), "m()").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(
        rendered.contains(&entry("PGM", "inj{SortFoo{}, SortKItem{}}(Lbla{}())")),
        "{rendered}"
    );
    assert!(!rendered.contains("Lblb"), "{rendered}");
}

#[test]
fn a_program_read_at_k_expands_its_only_kitem_rule() {
    let compiled = compiled(
        r#"
module MAIN
  syntax {S} S ::= m() [macro, symbol(m)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
  rule m():KItem => a
  configuration <k> $PGM:K </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("K"), "m()").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(
        rendered.contains(&entry("PGM", "inj{SortFoo{}, SortKItem{}}(Lbla{}())")),
        "{rendered}"
    );
    assert!(!rendered.contains("Lblm"), "{rendered}");
}

#[test]
fn a_value_takes_the_rule_of_its_emitted_instance() {
    let compiled = compiled(
        r#"
module MAIN
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax {S} S ::= id(S) [macro, symbol(id)]
  rule id(_:Foo):Foo => b
  configuration <k> $PGM:KItem </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("KItem"), "id(a)").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    assert!(
        rendered.contains(&entry("PGM", "inj{SortFoo{}, SortKItem{}}(Lblb{}())")),
        "{rendered}"
    );
    assert!(!rendered.contains("Lblid"), "{rendered}");
}

#[test]
fn a_rewrite_below_does_not_change_the_selected_rule() {
    let compiled = compiled(
        r#"
module MAIN
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | c() [macro, symbol(c)]
  syntax Bar ::= "z" [symbol(z)]
  syntax {S} S ::= m(Foo) [macro, symbol(m)]
  rule c() => a
  rule m(_):Bar => z
  rule m(X):KItem => X
  configuration <k> $PGM:KItem </k> <x> $X:KItem </x>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("KItem"), "m(c())").unwrap();
    assembler.bind("X", "m(c())").unwrap();
    let rendered = render(&assembler.finish().unwrap());
    for name in ["PGM", "X"] {
        assert!(
            rendered.contains(&entry(name, "inj{SortFoo{}, SortKItem{}}(Lbla{}())")),
            "{rendered}"
        );
    }
    assert!(!rendered.contains("Lblz"), "{rendered}");
}

#[test]
fn fu24_program_start_synonym_uses_the_denoted_instantiation_position() {
    let compiled = compiled(
        r#"
        module MAIN
          syntax S ::= "a" [symbol(a)]
          syntax A = S
          configuration <k> $PGM:S </k>
        endmodule
        "#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let assemble = |sort: &str| {
        let mut assembler =
            ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
        assembler.program(&Sort::new(sort), "a").unwrap();
        assembler.finish().unwrap()
    };
    assert_eq!(assemble("A"), assemble("S"));
}

#[test]
fn checked_log_configuration_transports_a_whole_k_value() {
    use k_rust::kore::{ast::Pattern, parser::parse_definition};
    use k_rust_backend::{
        builtin::BuiltinEffect,
        definition::BackendDefinition,
        externalize,
        simplify::{SimplificationOptions, simplify},
    };

    let compiled = compiled(
        r#"
module MAIN
  imports K-IO
  imports STRING
  configuration <k> $PGM:K </k>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler
        .program(&Sort::new("K"), r#"#log("hello from K")"#)
        .unwrap();
    let initial = assembler.finish().unwrap();
    let theory = parse_definition(&compiled.kore).unwrap();
    let backend = BackendDefinition::internalize(&theory, "MAIN").unwrap();
    // Checked admission requires every injection to follow the emitted theory's subsort paths.
    let input = backend
        .admit_unverified(&initial, &[])
        .internalize_term()
        .expect("checked initial configuration must have only licensed injections");
    let evaluated = simplify(&backend, &input, SimplificationOptions::default())
        .unwrap()
        .unwrap();
    assert_eq!(
        evaluated.effects,
        [BuiltinEffect::UserLog("hello from K".into())]
    );
    let result = externalize::term(&evaluated.term);
    fn k_cell(pattern: &Pattern) -> Option<&Pattern> {
        if let Pattern::Application { symbol, arguments } = pattern {
            if symbol.name == "Lbl'-LT-'k'-GT-'" {
                return arguments.first();
            }
            return arguments.iter().find_map(k_cell);
        }
        None
    }
    assert_eq!(
        render(k_cell(&result).expect("initialized k cell")),
        "dotk{}()"
    );
    println!("checked initial configuration: PASS; k cell = dotk{{}}(); log = hello from K (once)");
}

#[test]
fn a_malformed_program_is_rejected_even_when_no_cell_reads_it() {
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
    assert!(matches!(
        assembler.program(&Sort::new("State"), "malformed"),
        Err(ConfigurationError::Program(_))
    ));
    assert_eq!(
        render(&assembler.finish().unwrap()),
        "LblinitGeneratedTopCell{}()"
    );
}

#[test]
fn whole_k_values_and_items_initialize_program_and_other_k_cells() {
    use k_rust::kore::{ast::Pattern, parser::parse_definition};
    use k_rust_backend::{
        builtin::BuiltinEffect,
        definition::BackendDefinition,
        externalize,
        simplify::{SimplificationOptions, simplify},
    };
    let compiled = compiled(
        r#"
module MAIN
  imports K-IO
  imports STRING
  syntax K ::= KItem | K "~>" K [symbol(#KSequence), assoc]
  syntax K ::= ".K" [symbol(#EmptyK)]
  syntax P ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <k> $PGM:K </k> <x> $X:K </x>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let theory = parse_definition(&compiled.kore).unwrap();
    let backend = BackendDefinition::internalize(&theory, "MAIN").unwrap();
    let item_a = "kseq{}(inj{SortP{}, SortKItem{}}(Lbla{}()), dotk{}())";
    let sequence = "kseq{}(inj{SortP{}, SortKItem{}}(Lbla{}()), kseq{}(inj{SortP{}, SortKItem{}}(Lblb{}()), dotk{}()))";
    fn cell<'p>(pattern: &'p Pattern, label: &str) -> Option<&'p Pattern> {
        if let Pattern::Application { symbol, arguments } = pattern {
            if symbol.name == label {
                return arguments.first();
            }
            return arguments.iter().find_map(|argument| cell(argument, label));
        }
        None
    }
    for (start, text, expected, logs) in [
        ("P", "a", item_a, vec![]),
        ("K", "a ~> b", sequence, vec![]),
        ("K", ".K", "dotk{}()", vec![]),
        (
            "K",
            r#"#log("value")"#,
            "dotk{}()",
            vec![BuiltinEffect::UserLog("value".into()); 2],
        ),
    ] {
        let mut assembler =
            ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
        assembler.program(&Sort::new(start), text).unwrap();
        assembler.bind("X", text).unwrap();
        let initial = assembler.finish().unwrap();
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        k_rust::kompile::assert_frontend_pattern(&theory, "MAIN", &initial, "PGM and X K payloads");
        let input = backend
            .admit_unverified(&initial, &[])
            .internalize_term()
            .unwrap();
        let evaluated = simplify(&backend, &input, SimplificationOptions::default())
            .unwrap()
            .unwrap();
        assert_eq!(evaluated.effects, logs, "{text}");
        let result = externalize::term(&evaluated.term);
        for label in ["Lbl'-LT-'k'-GT-'", "Lbl'-LT-'x'-GT-'"] {
            assert_eq!(
                render(cell(&result, label).unwrap()),
                expected,
                "{text}: {label}"
            );
        }
        assert!(!render(&result).contains("KConfigValue"), "{result}");
    }
}

#[test]
fn boxed_non_k_values_and_stream_defaults_keep_their_declared_cell_contents() {
    use k_rust::kore::{ast::Pattern, parser::parse_definition};
    use k_rust_backend::{
        definition::BackendDefinition,
        externalize,
        simplify::{SimplificationOptions, simplify},
    };

    let compiled = compiled(
        r#"
module ENV-PARSER
  syntax Env ::= "selected" [symbol(selectedEnv)]
endmodule
module MAIN
  imports ENV-PARSER
  imports STRING
  syntax P ::= "a" [symbol(a)]
  configuration <k> $PGM:K </k>
                <env parser="ENV, ENV-PARSER"> $ENV:Env </env>
                <io> $IO:String </io>
                <stdin> $STDIN:String </stdin>
endmodule
"#,
        "MAIN",
    );
    let grammar = ProgramGrammar::new(&compiled.frontend).unwrap();
    let theory = parse_definition(&compiled.kore).unwrap();
    let backend = BackendDefinition::internalize(&theory, "MAIN").unwrap();
    let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &compiled.variables);
    assembler.program(&Sort::new("P"), "a").unwrap();
    assembler.bind("ENV", "selected").unwrap();
    assembler
        .bind_stream_defaults(false, false, || -> Result<Vec<u8>, ConfigurationError> {
            Ok(b"buffered input".to_vec())
        })
        .unwrap();
    let initial = assembler.finish().unwrap();
    let input = backend
        .admit_unverified(&initial, &[])
        .internalize_term()
        .unwrap();
    let evaluated = simplify(&backend, &input, SimplificationOptions::default())
        .unwrap()
        .unwrap();
    assert!(evaluated.effects.is_empty());
    let result = externalize::term(&evaluated.term);
    fn cell<'p>(pattern: &'p Pattern, label: &str) -> Option<&'p Pattern> {
        if let Pattern::Application { symbol, arguments } = pattern {
            if symbol.name == label {
                return arguments.first();
            }
            return arguments.iter().find_map(|argument| cell(argument, label));
        }
        None
    }
    for (label, expected) in [
        ("Lbl'-LT-'env'-GT-'", "LblselectedEnv{}()"),
        ("Lbl'-LT-'io'-GT-'", r#"\dv{SortString{}}("off")"#),
        (
            "Lbl'-LT-'stdin'-GT-'",
            r#"\dv{SortString{}}("buffered input")"#,
        ),
    ] {
        assert_eq!(render(cell(&result, label).unwrap()), expected, "{label}");
    }
    assert!(!render(&result).contains("KConfigValue"), "{result}");
}

#[test]
fn configuration_values_reject_unlicensed_macro_injections_atomically() {
    use k_rust::definition::{Sentence, sentence_mut};
    use k_rust::kast::{Label, Term};
    let base = compiled(
        r#"
module MAIN
  syntax P ::= "a" [symbol(a)] | "m" [macro, symbol(m)]
  rule m => a
  configuration <k> $PGM:K </k> <x> $X:K </x>
endmodule
"#,
        "MAIN",
    );
    let inj = |source: &str, target: &str, operand: Term| Term::Apply {
        label: Label::with_parameters("inj", vec![Sort::new(source), Sort::new(target)]),
        arguments: vec![operand],
    };
    for invalid in [
        inj("K", "KItem", Term::Sequence(vec![])),
        inj("KItem", "K", inj("P", "KItem", Term::apply("a", vec![]))),
        inj("P", "P", Term::apply("a", vec![])),
        inj(
            "P",
            "KItem",
            Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
        ),
    ] {
        let mut frontend = base.frontend.clone();
        let mut replaced = false;
        for module in &mut frontend.modules {
            for sentence in &mut module.local_sentences {
                let Sentence::Rule { body, .. } = sentence_mut(sentence) else {
                    continue;
                };
                if let Term::Rewrite { left, .. } = body.unannotated()
                    && matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "m")
                {
                    *body = Term::Rewrite {
                        left: left.clone(),
                        right: Box::new(invalid.clone()),
                    };
                    replaced = true;
                }
            }
        }
        assert!(replaced);
        let grammar = ProgramGrammar::new(&frontend).unwrap();
        let mut assembler = ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &base.variables);
        assert!(
            assembler.program(&Sort::new("P"), "m").is_err(),
            "{invalid}"
        );
        assert!(assembler.bind("X", "m").is_err(), "{invalid}");
        assembler.program(&Sort::new("P"), "a").unwrap();
        assembler.bind("X", "a").unwrap();
        let rendered = render(&assembler.finish().unwrap());
        for name in ["PGM", "X"] {
            assert!(
                rendered.contains(&entry(name, "inj{SortP{}, SortKItem{}}(Lbla{}())")),
                "{rendered}"
            );
        }
    }
}
