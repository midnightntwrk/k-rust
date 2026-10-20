//! Tests of the hole overlay and of assembly (FZ-02), on FZ-FIX's fixture definitions
//! (`tests/support`). The functions under test are crate-private, so these are unit tests.

#[path = "../../tests/support/mod.rs"]
mod support;

use std::sync::OnceLock;

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    builtin::embedded,
    k_rust_backend::definition::BackendDefinition,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{
        ast::{KoreString, Pattern, Sort as KoreSort, Symbol, Variable, VariableKind},
        codec,
        parser::parse_pattern,
        printer::Printer,
    },
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use num_bigint::BigInt;

use super::{
    HoleDecl, HoleLocation, HoleSite, InstantiatedProgram, PrintedValue, ResolvedHole,
    ResolvedHoles, RoundTripCheck, SpanAddress, SpanText, check_hole_sort, instantiate, resolve,
};
use crate::{
    BackendRoute,
    assemble::{ProgramAssembly, build_backend},
    error::{CampaignError, SortRefusal, SpanProblem},
    spec::{CompiledDefinition, ProgramInput, ProgramSource, ProgramText},
    values::{
        Constraints, ElementSorts, Value, ValueSort,
        print::{print_k_text, to_kore},
    },
};

const IMP_K: &str = include_str!("../../tests/data/imp/imp.k");
const STREAMS_K: &str = include_str!("../../tests/data/streams/streams.k");
const GO_PGM: &str = include_str!("../../tests/data/streams/go.pgm");
const VALUES_K: &str = include_str!("../../tests/data/values/values.k");
const TOY_K: &str = include_str!("../../tests/data/toy/toy.k");
const TOY_PGM: &str = include_str!("../../tests/data/toy/send.pgm");
const WRAPS_K: &str = include_str!("../../tests/data/wraps/wraps.k");
const ONE_PGM: &str = include_str!("../../tests/data/wraps/one.pgm");
const COMMUTE_IMP: &str = include_str!("../../tests/data/imp/commute.imp");
const LOOP_IMP: &str = include_str!("../../tests/data/imp/loop.imp");
const SUM_PGM: &str = include_str!("../../tests/data/unsigned/sum.pgm");
const SETTLE_PGM: &str = include_str!("../../tests/data/ledger/settle.pgm");
const SETTLE_TX: &str = include_str!("../../tests/data/ledger/settle.tx");

/// Compile a fixture the shared support module does not list, as `tests/support` compiles its
/// fixtures: the embedded prelude as an implicit source, the Rust backend's load options, then
/// `compile_loaded_definition`; the frontend definition is the loaded one, as krun keeps it.
fn compile(file: &str, source: &str, main_module: &str) -> CompiledDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(file, source),
        main_module,
        None,
        &mut resolver,
        &options,
    )
    .unwrap_or_else(|error| panic!("{file} does not load: {error:?}"));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{file} does not compile: {error}"));
    CompiledDefinition::from_artifacts(
        main_module,
        syntax_module,
        loaded.into_definition(),
        artifacts,
    )
    .unwrap_or_else(|error| panic!("{file}: {error}"))
}

fn values() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| compile("values/values.k", VALUES_K, "VALUES"))
}

fn toy() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| compile("toy/toy.k", TOY_K, "TOY"))
}

fn streams() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| compile("streams/streams.k", STREAMS_K, "STREAMS"))
}

fn wraps() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| compile("wraps/wraps.k", WRAPS_K, "WRAPS"))
}

fn imp() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::IMP.compiled().definition())
}

fn unsigned() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::UNSIGNED.compiled().definition())
}

fn ledger() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::LEDGER.compiled().definition())
}

fn backend_definition(definition: &CompiledDefinition) -> BackendDefinition {
    let BackendRoute::SourceExecution {
        execution_rewrite_order,
    } = &definition.route
    else {
        panic!("fixtures are compiled on krun's route");
    };
    Backend::internalize_source_definition(
        &definition.kore,
        &definition.main_module,
        execution_rewrite_order,
    )
    .expect("the fixture internalizes")
}

fn program(name: &str, text: &str, config_vars: &[(&str, &str)]) -> ProgramInput {
    ProgramInput::Source(ProgramSource {
        program: Some(ProgramText {
            name: name.to_owned(),
            text: text.to_owned(),
            start_sort: "Pgm".to_owned(),
        }),
        config_vars: config_vars
            .iter()
            .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
            .collect(),
    })
}

fn span(
    name: &str,
    sort: &str,
    program: &str,
    line: Option<u32>,
    find: &str,
    literal: &str,
) -> HoleDecl {
    HoleDecl {
        name: name.to_owned(),
        sort: sort.to_owned(),
        location: HoleLocation::Span(SpanAddress {
            program: program.to_owned(),
            line,
            find: find.to_owned(),
            literal: literal.to_owned(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    }
}

fn config_var(name: &str, sort: &str, variable: &str) -> HoleDecl {
    HoleDecl {
        location: HoleLocation::ConfigVar {
            name: variable.to_owned(),
        },
        ..span(name, sort, "", None, "", "")
    }
}

fn kore_variable(name: &str, sort: &str, variable: &str) -> HoleDecl {
    HoleDecl {
        location: HoleLocation::KoreVariable {
            name: variable.to_owned(),
        },
        ..span(name, sort, "", None, "", "")
    }
}

fn kore_sort(name: &str) -> KoreSort {
    KoreSort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

fn int_kore(value: i64) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortInt"),
        value: KoreString::from_bytes(value.to_string().into_bytes()),
    }
}

/// An `Int` value printed as a K literal and as its domain value.
fn int(value: i64) -> PrintedValue {
    PrintedValue {
        k_text: value.to_string(),
        kore: int_kore(value),
    }
}

fn printed(pattern: &Pattern) -> String {
    Printer::compact().print_pattern(pattern)
}

fn source_text(program: &InstantiatedProgram) -> &str {
    let InstantiatedProgram::Source {
        program: Some(program),
        ..
    } = program
    else {
        panic!("a source program with a text: {program:?}");
    };
    &program.text
}

fn resolve_ok(
    decls: &[HoleDecl],
    program: &ProgramInput,
    definition: &CompiledDefinition,
) -> ResolvedHoles {
    resolve(decls, program, definition, &backend_definition(definition))
        .unwrap_or_else(|error| panic!("the holes resolve: {error}"))
}

fn resolve_err(
    decls: &[HoleDecl],
    program: &ProgramInput,
    definition: &CompiledDefinition,
) -> CampaignError {
    match resolve(decls, program, definition, &backend_definition(definition)) {
        Ok(holes) => panic!("the holes resolve: {holes:?}"),
        Err(error) => error,
    }
}

fn span_error(hole: &str, problem: SpanProblem) -> CampaignError {
    CampaignError::HoleSpan {
        hole: hole.to_owned(),
        problem,
    }
}

#[test]
fn a_span_hole_with_context_resolves_to_its_literal() {
    let definition = imp();
    let program = program("imp/loop.imp", LOOP_IMP, &[]);
    let start = LOOP_IMP.find("n - 1;").expect("loop.imp decrements n") + "n - ".len();
    for decl in [
        span("ONE", "Int", "imp/loop.imp", None, "n - 1;", "1"),
        span("ONE", "Int", "imp/loop.imp", Some(6), "1", "1"),
    ] {
        let holes = resolve_ok(&[decl], &program, definition);
        let [hole] = holes.holes.as_slice() else {
            panic!("one hole: {holes:?}");
        };
        assert_eq!(
            hole.site,
            HoleSite::Span {
                text: SpanText::Program,
                start,
                end: start + 1
            }
        );
        assert_eq!(hole.anchor_text.as_deref(), Some("1"));
        assert_eq!(hole.anchor, Some(Value::Int(BigInt::from(1))));
        assert_eq!(hole.sort, ValueSort::Int);
        assert_eq!(hole.overridden, None);
    }
}

#[test]
fn a_span_that_is_not_exactly_one_literal_is_refused() {
    let definition = imp();
    let program = program("imp/loop.imp", LOOP_IMP, &[]);
    let cases = [
        // `1` occurs in `n = 10;` and in `n - 1;`.
        (
            span("ONE", "Int", "imp/loop.imp", None, "1", "1"),
            SpanProblem::FindCount(2),
        ),
        (
            span("N", "Int", "imp/loop.imp", None, "n = n - 1;", "n"),
            SpanProblem::LiteralCount(2),
        ),
        (
            span("X", "Int", "imp/loop.imp", None, "x = 7;", "7"),
            SpanProblem::FindCount(0),
        ),
        (
            span("ONE", "Int", "imp/loop.imp", Some(2), "1;", "1"),
            SpanProblem::FindCount(0),
        ),
        (
            span("ONE", "Int", "imp/loop.imp", Some(99), "1", "1"),
            SpanProblem::LineOutOfRange,
        ),
        (
            span("ONE", "Int", "imp/other.imp", None, "n - 1;", "1"),
            SpanProblem::UnknownProgram,
        ),
    ];
    for (decl, problem) in cases {
        let hole = decl.name.clone();
        assert_eq!(
            resolve_err(&[decl], &program, definition),
            span_error(&hole, problem)
        );
    }
}

#[test]
fn overlapping_spans_and_repeated_names_are_refused() {
    let definition = imp();
    let program = program("imp/commute.imp", COMMUTE_IMP, &[]);
    let x = span("X", "Int", "imp/commute.imp", None, "x = 3;", "3");
    assert_eq!(
        resolve_err(
            &[
                x.clone(),
                span("Y", "Int", "imp/commute.imp", None, "3;\ny", "3;")
            ],
            &program,
            definition
        ),
        CampaignError::OverlappingHoles {
            first: "X".to_owned(),
            second: "Y".to_owned(),
        }
    );
    assert_eq!(
        resolve_err(
            &[
                x.clone(),
                span("X", "Int", "imp/commute.imp", None, "y = 5;", "5")
            ],
            &program,
            definition
        ),
        CampaignError::DuplicateHole {
            hole: "X".to_owned()
        }
    );
}

#[test]
fn sorts_programs_are_written_in_are_refused() {
    let definition = imp();
    let program = program("imp/commute.imp", COMMUTE_IMP, &[]);
    let refusal = |sort: &str| {
        check_hole_sort(
            &span("H", sort, "imp/commute.imp", None, "x = 3;", "3"),
            &program,
            definition,
        )
    };
    for sort in ["AExp", "BExp", "Block", "Stmt", "Pgm", "Ids"] {
        assert_eq!(
            refusal(sort),
            Err(CampaignError::RefusedHoleSort {
                hole: "H".to_owned(),
                sort: sort.to_owned(),
                reason: SortRefusal::ProgramSyntax,
            }),
            "{sort}"
        );
    }
    // Builtin sorts are exempt from the closure rule although programs contain their literals.
    for sort in ["Int", "Bool", "Map"] {
        assert_eq!(refusal(sort), Ok(None), "{sort}");
    }
    for sort in [
        "K",
        "KItem",
        "TCell",
        "KCell",
        "StateCell",
        "GeneratedTopCell",
    ] {
        assert_eq!(
            refusal(sort),
            Err(CampaignError::RefusedHoleSort {
                hole: "H".to_owned(),
                sort: sort.to_owned(),
                reason: SortRefusal::Computation,
            }),
            "{sort}"
        );
    }
    assert_eq!(
        refusal("Nope"),
        Err(CampaignError::RefusedHoleSort {
            hole: "H".to_owned(),
            sort: "Nope".to_owned(),
            reason: SortRefusal::Unknown,
        })
    );
    // The sort rule refuses an `AExp` hole in `resolve` too.
    assert_eq!(
        resolve_err(
            &[span("H", "AExp", "imp/commute.imp", None, "x = 3;", "3")],
            &program,
            definition
        ),
        CampaignError::RefusedHoleSort {
            hole: "H".to_owned(),
            sort: "AExp".to_owned(),
            reason: SortRefusal::ProgramSyntax,
        }
    );
}

#[test]
fn an_id_hole_is_refused_unless_overridden() {
    let definition = imp();
    let program = program("imp/loop.imp", LOOP_IMP, &[]);
    let decl = span("V", "Id", "imp/loop.imp", None, "n = 10;", "n");
    let refused = CampaignError::RefusedHoleSort {
        hole: "V".to_owned(),
        sort: "Id".to_owned(),
        reason: SortRefusal::Token,
    };
    assert_eq!(
        check_hole_sort(&decl, &program, definition),
        Err(refused.clone())
    );
    assert_eq!(
        resolve_err(std::slice::from_ref(&decl), &program, definition),
        refused
    );
    let overridden = HoleDecl {
        allow_refused_sort: true,
        ..decl
    };
    assert_eq!(
        check_hole_sort(&overridden, &program, definition),
        Ok(Some(SortRefusal::Token))
    );
    let holes = resolve_ok(&[overridden], &program, definition);
    let [hole] = holes.holes.as_slice() else {
        panic!("one hole: {holes:?}");
    };
    assert_eq!(hole.overridden, Some(SortRefusal::Token));
    assert_eq!(
        hole.sort,
        ValueSort::Token {
            sort: "Id".to_owned()
        }
    );
    assert_eq!(
        hole.anchor,
        Some(Value::Token {
            sort: "Id".to_owned(),
            text: "n".to_owned()
        })
    );
}

#[test]
fn record_sorts_outside_the_program_closure_are_admitted() {
    let definition = ledger();
    let program = program(
        "ledger/settle.pgm",
        SETTLE_PGM,
        &[("TX", SETTLE_TX.trim_end())],
    );
    for sort in ["Tx", "Account", "Status"] {
        assert_eq!(
            check_hole_sort(&config_var("H", sort, "TX"), &program, definition),
            Ok(None),
            "{sort}"
        );
    }
    assert_eq!(
        check_hole_sort(&config_var("H", "Pgm", "TX"), &program, definition),
        Err(CampaignError::RefusedHoleSort {
            hole: "H".to_owned(),
            sort: "Pgm".to_owned(),
            reason: SortRefusal::ProgramSyntax,
        })
    );
}

#[test]
fn a_configuration_variable_hole_needs_a_binding_it_replaces() {
    let definition = ledger();
    let unbound = program("ledger/settle.pgm", SETTLE_PGM, &[]);
    let bound = program(
        "ledger/settle.pgm",
        SETTLE_PGM,
        &[("TX", SETTLE_TX.trim_end())],
    );
    assert_eq!(
        resolve_err(&[config_var("T", "Tx", "TX")], &unbound, definition),
        span_error("T", SpanProblem::UnknownConfigVar)
    );
    assert_eq!(
        resolve_err(&[config_var("T", "Tx", "NOPE")], &bound, definition),
        span_error("T", SpanProblem::UnknownConfigVar)
    );
}

#[test]
fn a_configuration_variable_hole_replaces_its_binding() {
    let definition = ledger();
    let program = program(
        "ledger/settle.pgm",
        SETTLE_PGM,
        &[("TX", SETTLE_TX.trim_end())],
    );
    // A data-sort anchor is not read before G-6, so the hole is built by hand.
    let holes = ResolvedHoles {
        holes: vec![ResolvedHole {
            decl: config_var("T", "Tx", "TX"),
            site: HoleSite::ConfigVar("TX".to_owned()),
            // `instantiate` reads only the site; the data sort's resolved form is FZ-03's.
            sort: ValueSort::Int,
            anchor_text: Some(SETTLE_TX.trim_end().to_owned()),
            anchor: None,
            overridden: None,
            refusals: Vec::new(),
        }],
    };
    let value = PrintedValue {
        k_text: "transfer(5, 0)".to_owned(),
        kore: int_kore(0),
    };
    let instantiated = instantiate(&program, &holes, &[value]);
    let InstantiatedProgram::Source {
        program: Some(text),
        config_vars,
    } = &instantiated
    else {
        panic!("a source program: {instantiated:?}");
    };
    assert_eq!(text.text, SETTLE_PGM);
    assert_eq!(
        config_vars,
        &[("TX".to_owned(), "transfer(5, 0)".to_owned())]
    );
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let configuration = printed(
        &assembly
            .assemble(definition, &instantiated)
            .expect("the instantiated program assembles"),
    );
    assert!(
        configuration.contains(r#"Lbltransfer{}(\dv{SortInt{}}("5"), \dv{SortInt{}}("0"))"#),
        "{configuration}"
    );
}

#[test]
fn a_span_hole_addresses_a_literal_inside_a_binding() {
    let definition = ledger();
    let program = program(
        "ledger/settle.pgm",
        SETTLE_PGM,
        &[("TX", SETTLE_TX.trim_end())],
    );
    let holes = resolve_ok(
        &[
            span("AMOUNT", "Int", "$TX", None, "transfer(30", "30"),
            span("FEE", "Int", "$TX", Some(1), "1)", "1"),
        ],
        &program,
        definition,
    );
    let [amount, fee] = holes.holes.as_slice() else {
        panic!("two holes: {holes:?}");
    };
    assert_eq!(
        amount.site,
        HoleSite::Span {
            text: SpanText::Binding("TX".to_owned()),
            start: "transfer(".len(),
            end: "transfer(30".len(),
        }
    );
    assert_eq!(fee.anchor, Some(Value::Int(BigInt::from(1))));
    assert_eq!(
        resolve_err(
            &[span("AMOUNT", "Int", "$NOPE", None, "30", "30")],
            &program,
            definition
        ),
        span_error("AMOUNT", SpanProblem::UnknownProgram)
    );
    // A span inside a binding overlaps a hole on the whole binding.
    assert_eq!(
        resolve_err(
            &[
                config_var("T", "Tx", "TX"),
                span("AMOUNT", "Int", "$TX", None, "30", "30"),
            ],
            &program,
            definition
        ),
        CampaignError::OverlappingHoles {
            first: "T".to_owned(),
            second: "AMOUNT".to_owned(),
        }
    );

    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .expect("the anchors parse back at their positions");
    let values = [int(7), int(-2)];
    let instantiated = instantiate(&program, &holes, &values);
    let InstantiatedProgram::Source {
        program: Some(text),
        config_vars,
    } = &instantiated
    else {
        panic!("a source program: {instantiated:?}");
    };
    assert_eq!(text.text, SETTLE_PGM);
    assert_eq!(
        config_vars,
        &[("TX".to_owned(), "transfer(7, -2)".to_owned())]
    );
    let built = assembly
        .assemble(definition, &instantiated)
        .expect("the instantiated program assembles");
    assert_eq!(check.check(&built, &values), Ok(()));
    assert!(check.check(&built, &[int(-2), int(7)]).is_err());
}

#[test]
fn every_free_template_variable_is_a_hole() {
    let definition = imp();
    let variable = |name: &str| {
        Pattern::Variable(Variable {
            kind: VariableKind::Element,
            name: name.to_owned(),
            sort: kore_sort("SortInt"),
        })
    };
    let template = ProgramInput::KoreTemplate(Pattern::Application {
        symbol: Symbol {
            name: "Lbl'UndsPlus'Int'Unds'".to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments: vec![variable("VarA"), variable("VarB")],
    });
    assert_eq!(
        resolve_err(&[kore_variable("A", "Int", "VarA")], &template, definition),
        span_error("VarB", SpanProblem::KoreVariable)
    );
    assert_eq!(
        resolve_err(
            &[
                kore_variable("A", "Int", "VarA"),
                kore_variable("B", "Int", "VarB"),
                kore_variable("C", "Int", "VarC"),
            ],
            &template,
            definition
        ),
        span_error("C", SpanProblem::KoreVariable)
    );
    let hole = |name: &str, variable: &str| ResolvedHole {
        decl: kore_variable(name, "Int", variable),
        site: HoleSite::KoreVariable(Variable {
            kind: VariableKind::Element,
            name: variable.to_owned(),
            sort: kore_sort("SortInt"),
        }),
        sort: ValueSort::Int,
        anchor_text: None,
        anchor: None,
        overridden: None,
        refusals: Vec::new(),
    };
    let holes = ResolvedHoles {
        holes: vec![hole("A", "VarA"), hole("B", "VarB")],
    };
    let InstantiatedProgram::Kore(pattern) = instantiate(&template, &holes, &[int(4), int(-9)])
    else {
        panic!("a KORE template instantiates to KORE");
    };
    assert_eq!(
        printed(&pattern),
        r#"Lbl'UndsPlus'Int'Unds'{}(\dv{SortInt{}}("4"), \dv{SortInt{}}("-9"))"#
    );
}

#[test]
fn a_negative_value_does_not_round_trip_where_literals_are_unsigned() {
    let definition = unsigned();
    let program = program("unsigned/sum.pgm", SUM_PGM, &[]);
    let holes = resolve_ok(
        &[span("N", "Int", "unsigned/sum.pgm", None, "+ 5", "5")],
        &program,
        definition,
    );
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .expect("the anchor parses back at its position");
    let mut reused = assembly.assembler(definition);
    for (value, round_trips) in [(9, true), (0, true), (-5, false), (123_456, true)] {
        let values = [int(value)];
        let instantiated = instantiate(&program, &holes, &values);
        assert_eq!(source_text(&instantiated), format!("print 7 + {value} ;\n"));
        // `-5` parses, as the negation `neg(5)`, so the case assembles and is then rejected.
        let built = reused
            .assemble(&instantiated)
            .expect("the instantiated program assembles");
        let checked = check.check(&built, &values);
        assert_eq!(checked.is_ok(), round_trips, "{value}: {checked:?}");
        if let Err(failure) = checked {
            assert_eq!(failure.hole, "N");
        }
    }

    // IMP's Int literals are signed, so the same value round-trips there.
    let definition = imp();
    let program = self::program("imp/commute.imp", COMMUTE_IMP, &[]);
    let holes = resolve_ok(
        &[span("X", "Int", "imp/commute.imp", None, "x = 3;", "3")],
        &program,
        definition,
    );
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .expect("the anchor parses back at its position");
    let values = [int(-5)];
    let built = assembly
        .assemble(definition, &instantiate(&program, &holes, &values))
        .expect("the instantiated program assembles");
    assert_eq!(check.check(&built, &values), Ok(()));
}

#[test]
fn an_anchor_that_is_not_a_value_of_its_sort_is_refused() {
    let definition = unsigned();
    let program = program("unsigned/sum.pgm", SUM_PGM, &[]);
    let error = resolve_err(
        &[span("N", "Int", "unsigned/sum.pgm", None, "7 + 5", "7 + 5")],
        &program,
        definition,
    );
    assert!(
        matches!(&error, CampaignError::AnchorDoesNotParse { hole, .. } if hole == "N"),
        "{error:?}"
    );
}

#[test]
fn the_program_and_definition_files_are_never_modified() {
    // The program and the definition are read from files, as a client reads them; every step a
    // case takes (resolve, locate, instantiate, assemble, execute) runs, and the files' bytes
    // and modification times are compared before and after.
    let directory =
        std::env::temp_dir().join(format!("k-rust-fuzz-fz02-files-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("the temporary directory is created");
    let definition_path = directory.join("imp.k");
    let program_path = directory.join("commute.imp");
    std::fs::write(&definition_path, IMP_K).expect("the definition is written");
    std::fs::write(&program_path, COMMUTE_IMP).expect("the program is written");
    let snapshot = |path: &std::path::Path| {
        (
            std::fs::read(path).expect("the file is read"),
            std::fs::metadata(path)
                .and_then(|metadata| metadata.modified())
                .expect("the file has a modification time"),
        )
    };
    let before = [snapshot(&definition_path), snapshot(&program_path)];

    // The code under test sees the files' real paths: the definition's source name, the
    // program's name (the file name its locations carry) and the spans' program.
    let definition_name = definition_path.to_string_lossy().into_owned();
    let program_name = program_path.to_string_lossy().into_owned();
    let source = std::fs::read_to_string(&definition_path).expect("the definition is read");
    let definition = compile(&definition_name, &source, "IMP");
    let text = std::fs::read_to_string(&program_path).expect("the program is read");
    let program = program(&program_name, &text, &[]);
    let holes = resolve_ok(
        &[
            span("X", "Int", &program_name, None, "x = 3;", "3"),
            span("Y", "Int", &program_name, Some(3), "5", "5"),
        ],
        &program,
        &definition,
    );
    let assembly = ProgramAssembly::new(&definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, &definition, &program, &holes)
        .expect("the anchors parse back at their positions");
    let values = [int(-7), int(11)];
    let instantiated = instantiate(&program, &holes, &values);
    assert_eq!(
        source_text(&instantiated),
        COMMUTE_IMP
            .replacen("x = 3;", "x = -7;", 1)
            .replacen("y = 5;", "y = 11;", 1)
    );
    let built = assembly
        .assemble(&definition, &instantiated)
        .expect("the instantiated program assembles");
    assert_eq!(check.check(&built, &values), Ok(()));
    // The swapped values are at the wrong positions.
    assert!(check.check(&built, &[int(11), int(-7)]).is_err());
    let mut backend = build_backend(&definition, BackendOptions::default()).expect("a backend");
    let result = backend
        .execute(ExecuteRequest::new(built))
        .expect("the case executes");
    assert!(!result.leaves.is_empty());

    let after = [snapshot(&definition_path), snapshot(&program_path)];
    let mut entries = std::fs::read_dir(&directory)
        .expect("the temporary directory is listed")
        .map(|entry| entry.expect("an entry").file_name())
        .collect::<Vec<_>>();
    entries.sort();
    std::fs::remove_dir_all(&directory).expect("the temporary directory is removed");
    assert_eq!(before, after);
    // Nothing was written next to them either.
    assert_eq!(entries, ["commute.imp", "imp.k"]);
}

#[test]
fn the_crate_source_writes_no_file() {
    // The crate's library code (tests excluded) names no filesystem write: the program and the
    // specification are never modified or copied (ARCHITECTURE 2.1).
    let forbidden = [
        "std::fs",
        "fs::",
        "File::",
        "OpenOptions",
        "create_dir",
        "remove_file",
        "remove_dir",
        "rename(",
        "set_permissions",
    ];
    let mut pending = vec![std::path::PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src"
    ))];
    let mut checked = 0;
    while let Some(path) = pending.pop() {
        if path.is_dir() {
            for entry in std::fs::read_dir(&path).expect("a source directory is listed") {
                pending.push(entry.expect("an entry").path());
            }
            continue;
        }
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        if path.extension().is_none_or(|extension| extension != "rs")
            || name == "tests.rs"
            || name.ends_with("_tests.rs")
            || name == "test_definition.rs"
        {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("a source file is read");
        // A file's own unit tests follow its `#[cfg(test)]` module.
        let library = text.split("#[cfg(test)]\nmod ").next().unwrap_or(&text);
        for (number, line) in library.lines().enumerate() {
            let code = line.split("//").next().unwrap_or("");
            for word in forbidden {
                assert!(
                    !code.contains(word),
                    "{}:{}: `{word}` in library code: {line}",
                    path.display(),
                    number + 1
                );
            }
        }
        checked += 1;
    }
    assert!(checked > 10, "the crate's sources were found");
}

/// What `krust krun streams.k go.pgm --main-module STREAMS --sort Pgm -c LIMIT=3 --io off
/// --depth 0 < /dev/null` prints (run once, at `fz26/G15` `c5ae476d9`): the configuration krun
/// builds, evaluated, before any rewrite step. `<in>` holds `"\n"`: krun buffers the empty
/// standard input to one newline.
const KRUN_STREAMS_DEPTH_0: &str = r#"Lbl'-LT-'generatedTop'-GT-'{}(
  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lblgo{}(\dv{SortInt{}}("5"))), dotk{}())),
  Lbl'-LT-'limit'-GT-'{}(\dv{SortInt{}}("3")),
  Lbl'-LT-'in'-GT-'{}(\dv{SortString{}}("\n")),
  Lbl'-LT-'io'-GT-'{}(\dv{SortString{}}("off")),
  Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)"#;

#[test]
fn a_case_binds_the_streams_as_krun_does_with_an_empty_standard_input() {
    let definition = streams();
    let program = program("streams/go.pgm", GO_PGM, &[("LIMIT", "3")]);
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let initial = assembly
        .assemble(
            definition,
            &instantiate(&program, &ResolvedHoles { holes: Vec::new() }, &[]),
        )
        .expect("the program assembles");
    // krun binds `$PGM`, then the `-c` values in order, then `$IO` and `$STDIN`; the
    // initializer's map keeps that order.
    let text = printed(&initial);
    let at = |key: &str| {
        text.find(&format!(r#"\dv{{SortKConfigVar{{}}}}("{key}")"#))
            .unwrap_or_else(|| panic!("{key} is bound: {text}"))
    };
    assert!(at("$PGM") < at("$LIMIT"), "{text}");
    assert!(at("$LIMIT") < at("$IO"), "{text}");
    assert!(at("$IO") < at("$STDIN"), "{text}");

    let mut backend = build_backend(definition, BackendOptions::default()).expect("a backend");
    let result = backend
        .execute(ExecuteRequest {
            max_depth: Some(0),
            ..ExecuteRequest::new(initial)
        })
        .expect("zero steps execute");
    let [leaf] = result.leaves.as_slice() else {
        panic!("one leaf: {result:#?}");
    };
    let state = codec::from_value(&leaf.state).expect("a KORE leaf");
    let expected = parse_pattern(KRUN_STREAMS_DEPTH_0).expect("krun's output parses");
    assert_eq!(printed(&state), printed(&expected));
}

#[test]
fn a_reused_assembler_gives_the_one_shot_configuration() {
    let definition = streams();
    let program = program("streams/go.pgm", GO_PGM, &[("LIMIT", "3")]);
    let empty = ResolvedHoles { holes: Vec::new() };
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let expected = assembly
        .assemble(definition, &instantiate(&program, &empty, &[]))
        .expect("the program assembles");
    let mut reused = assembly.assembler(definition);
    let broken = self::program("streams/go.pgm", "go ;", &[("LIMIT", "3")]);
    assert!(reused.assemble(&instantiate(&broken, &empty, &[])).is_err());
    for _ in 0..2 {
        let again = reused
            .assemble(&instantiate(&program, &empty, &[]))
            .expect("the program assembles");
        assert_eq!(printed(&again), printed(&expected));
    }
}

#[test]
fn under_start_sort_k_every_sort_of_the_syntax_module_is_program_syntax() {
    let definition = imp();
    for start in ["K", "KItem"] {
        let program = ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: "imp/commute.imp".to_owned(),
                text: COMMUTE_IMP.to_owned(),
                start_sort: start.to_owned(),
            }),
            config_vars: Vec::new(),
        });
        let refusal = |sort: &str| {
            check_hole_sort(
                &span("H", sort, "imp/commute.imp", None, "x = 3;", "3"),
                &program,
                definition,
            )
        };
        for sort in ["AExp", "BExp", "Stmt", "Pgm", "Ids"] {
            assert_eq!(
                refusal(sort),
                Err(CampaignError::RefusedHoleSort {
                    hole: "H".to_owned(),
                    sort: sort.to_owned(),
                    reason: SortRefusal::ProgramSyntax,
                }),
                "{start}: {sort}"
            );
        }
        assert_eq!(refusal("Int"), Ok(None), "{start}");
    }
}

fn with_elements(decl: HoleDecl, elements: ElementSorts) -> HoleDecl {
    HoleDecl {
        constraints: Constraints {
            elements: Some(elements),
            ..Constraints::default()
        },
        ..decl
    }
}

fn refused(sort: &str, reason: SortRefusal) -> Result<Option<SortRefusal>, CampaignError> {
    Err(CampaignError::RefusedHoleSort {
        hole: "H".to_owned(),
        sort: sort.to_owned(),
        reason,
    })
}

#[test]
fn the_sorts_a_value_may_contain_are_data_too() {
    let definition = imp();
    let program = program("imp/commute.imp", COMMUTE_IMP, &[]);
    let list = |element: &str| {
        with_elements(
            span("H", "List", "imp/commute.imp", None, "x = 3;", "3"),
            ElementSorts::Elements {
                element: element.to_owned(),
            },
        )
    };
    let check = |decl: &HoleDecl| check_hole_sort(decl, &program, definition);
    assert_eq!(check(&list("Int")), Ok(None));
    assert_eq!(
        check(&list("Stmt")),
        refused("List", SortRefusal::ProgramSyntax)
    );
    assert_eq!(check(&list("K")), refused("List", SortRefusal::Computation));
    assert_eq!(
        check(&list("KItem")),
        refused("List", SortRefusal::Computation)
    );
    assert_eq!(
        check(&list("List")),
        refused("List", SortRefusal::Computation)
    );
    assert_eq!(check(&list("Nope")), refused("List", SortRefusal::Unknown));
    let map = with_elements(
        span("H", "Map", "imp/commute.imp", None, "x = 3;", "3"),
        ElementSorts::Entries {
            key: "Id".to_owned(),
            value: "Int".to_owned(),
        },
    );
    assert_eq!(check(&map), refused("Map", SortRefusal::Token));
    // The override admits an element sort as it admits the hole's own sort.
    let overridden = HoleDecl {
        allow_refused_sort: true,
        ..list("AExp")
    };
    assert_eq!(check(&overridden), Ok(Some(SortRefusal::ProgramSyntax)));
    assert_eq!(
        check(&span(
            "H",
            "KResult",
            "imp/commute.imp",
            None,
            "x = 3;",
            "3"
        )),
        refused("KResult", SortRefusal::Computation)
    );

    // Data sorts of the semantic module, by what their constructors take.
    let definition = wraps();
    let program = self::program("wraps/one.pgm", ONE_PGM, &[]);
    let check = |sort: &str| {
        check_hole_sort(
            &span("H", sort, "wraps/one.pgm", None, "1", "1"),
            &program,
            definition,
        )
    };
    assert_eq!(check("Pair"), Ok(None));
    assert_eq!(check("Job"), refused("Job", SortRefusal::ProgramSyntax));
    assert_eq!(
        check("Nested"),
        refused("Nested", SortRefusal::ProgramSyntax)
    );
    assert_eq!(check("Sack"), refused("Sack", SortRefusal::Computation));
    assert_eq!(check("Stmt"), refused("Stmt", SortRefusal::ProgramSyntax));
}

#[test]
fn builtin_operations_over_k_do_not_make_every_sort_program_syntax() {
    // TOY is one module: the syntax module is the main module, which sees `size(Map)`,
    // `K ==K K` and the like through DOMAINS. The program sort reaches `Int` and stops there.
    let definition = toy();
    let program = program("toy/send.pgm", TOY_PGM, &[("TX", "tx(1, 2)")]);
    let check = |sort: &str| check_hole_sort(&config_var("H", sort, "TX"), &program, definition);
    assert_eq!(check("Tx"), Ok(None));
    assert_eq!(check("Pgm"), refused("Pgm", SortRefusal::ProgramSyntax));
}

#[test]
fn constructors_decide_what_a_value_contains() {
    let definition = wraps();
    let program = program("wraps/one.pgm", ONE_PGM, &[]);
    let decl = |sort: &str| span("H", sort, "wraps/one.pgm", None, "1", "1");
    let check = |sort: &str| check_hole_sort(&decl(sort), &program, definition);
    // A parametric constructor's argument may hold any sort.
    assert_eq!(check("Box"), refused("Box", SortRefusal::Computation));
    let overridden = HoleDecl {
        allow_refused_sort: true,
        ..decl("Box")
    };
    assert_eq!(
        check_hole_sort(&overridden, &program, definition),
        Ok(Some(SortRefusal::Computation))
    );
    // A helper function over a map builds no `Ledger` value.
    assert_eq!(check("Ledger"), Ok(None));
    // Every refusal is found, in the order of the sorts' names.
    let rule = super::sorts::SortRule::new(&program, definition).expect("the rule");
    let verdict = rule.verdict(&decl("Both")).expect("a verdict");
    assert_eq!(verdict.own, None);
    assert_eq!(
        verdict.contained,
        [
            ("Id".to_owned(), SortRefusal::Token),
            ("Stmt".to_owned(), SortRefusal::ProgramSyntax),
        ]
    );
}

#[test]
fn an_override_of_a_contained_token_sort_keeps_the_hole_a_value_of_its_sort() {
    let definition = values();
    let program = program("values/run.pgm", "run", &values_bindings(&[]));
    let decl = HoleDecl {
        allow_refused_sort: true,
        ..with_elements(
            config_var("M", "Map", "MAP"),
            ElementSorts::Entries {
                key: "Id".to_owned(),
                value: "Int".to_owned(),
            },
        )
    };
    let holes = resolve(
        &[decl],
        &program,
        definition,
        &backend_definition(definition),
    )
    .unwrap_or_else(|error| panic!("the hole resolves: {error}"));
    let [hole] = holes.holes.as_slice() else {
        panic!("one hole: {holes:?}");
    };
    assert!(
        matches!(hole.sort, ValueSort::Map { .. }),
        "{:?}",
        hole.sort
    );
    assert_eq!(hole.overridden, Some(SortRefusal::Token));
    assert_eq!(hole.refusals, [("Id".to_owned(), SortRefusal::Token)]);
}

/// The VALUES program's bindings, one per configuration variable, with `changes` replacing
/// some.
fn values_bindings<'a>(changes: &[(&'a str, &'a str)]) -> Vec<(&'a str, &'a str)> {
    [
        ("SHAPE", "circle(5)"),
        ("REC", "rec(1, unit, leaf(0))"),
        ("PAIR", "1 & 2"),
        ("WRAPPER", "wrap(3)"),
        ("ACCOUNT", "account(1, .Map)"),
        ("LIST", ".List"),
        ("SET", ".Set"),
        ("MAP", ".Map"),
    ]
    .into_iter()
    .map(|(name, value)| {
        changes
            .iter()
            .find(|(changed, _)| *changed == name)
            .copied()
            .unwrap_or((name, value))
    })
    .collect()
}

/// Resolve, locate, and check `value` for one configuration-variable hole of VALUES.
fn values_case(
    decl: HoleDecl,
    bindings: &[(&str, &str)],
    value: &Value,
) -> Result<(), super::RoundTripFailure> {
    let definition = values();
    let program = program("values/run.pgm", "run", bindings);
    let holes = resolve(
        &[decl],
        &program,
        definition,
        &backend_definition(definition),
    )
    .unwrap_or_else(|error| panic!("the hole resolves: {error}"));
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .unwrap_or_else(|error| panic!("the anchor is located: {error}"));
    let sort = &holes.holes[0].sort;
    let printed = [PrintedValue {
        k_text: print_k_text(value, sort).expect("the value prints"),
        kore: to_kore(value, sort).expect("the value has KORE"),
    }];
    let built = assembly
        .assemble(definition, &instantiate(&program, &holes, &printed))
        .expect("the case assembles");
    check.check(&built, &printed)
}

#[test]
fn a_case_value_of_another_own_sort_than_the_anchor_round_trips() {
    // The anchor is a `circle`; a `square` is injected to the position's sort from its own sort,
    // so the node above the position differs, and the value is still the intended one (D19).
    let int = |value: i64| Value::Int(BigInt::from(value));
    let square = Value::Apply {
        symbol: "Lblsquare".to_owned(),
        arguments: vec![int(4), Value::Bool(true)],
    };
    let circle = Value::Apply {
        symbol: "Lblcircle".to_owned(),
        arguments: vec![int(9)],
    };
    let shape = || config_var("S", "Shape", "SHAPE");
    let bindings = values_bindings(&[]);
    assert_eq!(values_case(shape(), &bindings, &square), Ok(()));
    assert_eq!(values_case(shape(), &bindings, &circle), Ok(()));
}

#[test]
fn set_and_map_anchors_in_another_order_are_located() {
    let int = |value: i64| Value::Int(BigInt::from(value));
    let set = || {
        with_elements(
            config_var("S", "Set", "SET"),
            ElementSorts::Elements {
                element: "Int".to_owned(),
            },
        )
    };
    let bindings = values_bindings(&[("SET", "SetItem(3) SetItem(1) SetItem(2)")]);
    assert_eq!(
        values_case(set(), &bindings, &Value::Set(vec![int(1), int(7)])),
        Ok(())
    );
    let map = || {
        with_elements(
            config_var("M", "Map", "MAP"),
            ElementSorts::Entries {
                key: "Int".to_owned(),
                value: "Int".to_owned(),
            },
        )
    };
    let bindings = values_bindings(&[("MAP", "2 |-> 20 1 |-> 10")]);
    assert_eq!(
        values_case(map(), &bindings, &Value::Map(vec![(int(5), int(50))])),
        Ok(())
    );
}

#[test]
fn a_template_hole_has_its_variable_sort() {
    let definition = imp();
    let template = ProgramInput::KoreTemplate(Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: "VarA".to_owned(),
        sort: kore_sort("SortInt"),
    }));
    assert_eq!(
        resolve_err(&[kore_variable("A", "Bool", "VarA")], &template, definition),
        span_error("A", SpanProblem::KoreVariable)
    );
}

#[test]
fn an_anchor_written_other_than_canonically_is_refused_with_its_spelling() {
    let definition = imp();
    for (text, literal) in [("int x;\nx = 07;\n", "07"), ("int x;\nx = +7;\n", "+7")] {
        let program = program("leading.imp", text, &[]);
        let holes = resolve_ok(
            &[span("X", "Int", "leading.imp", None, literal, literal)],
            &program,
            definition,
        );
        let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
        let Err(CampaignError::AnchorDoesNotParse { hole, message }) =
            RoundTripCheck::new(&assembly, definition, &program, &holes)
        else {
            panic!("`{literal}` is refused");
        };
        assert_eq!(hole, "X");
        assert!(
            message.contains(&format!("written `{literal}`")) && message.contains("canonically"),
            "{message}"
        );
    }
}

#[test]
fn a_literal_that_is_part_of_a_token_is_refused() {
    let definition = imp();
    let program = program("imp/loop.imp", LOOP_IMP, &[]);
    // `0` of `10`: the configuration changes in `\dv("10")`, which is not the anchor `0`.
    let holes = resolve_ok(
        &[span("Z", "Int", "imp/loop.imp", None, "n = 10;", "0")],
        &program,
        definition,
    );
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let error = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .err()
        .expect("the partial token is refused");
    assert!(
        matches!(&error, CampaignError::AnchorDoesNotParse { hole, message }
            if hole == "Z" && !message.contains("canonically")),
        "{error:?}"
    );
}

#[test]
fn backends_are_built_on_the_route_the_definition_names() {
    let definition = imp();
    build_backend(definition, BackendOptions::default()).expect("krun's route");
    let from_definition = CompiledDefinition {
        route: BackendRoute::FromDefinition,
        ..definition.clone()
    };
    build_backend(&from_definition, BackendOptions::default()).expect("kink's route");
}
