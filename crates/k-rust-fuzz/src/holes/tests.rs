//! Tests of the hole overlay and of assembly (FZ-02), on FZ-FIX's fixture definitions
//! (`tests/support`). The functions under test are crate-private, so these are unit tests.

#[path = "../../tests/support/mod.rs"]
mod support;

use std::sync::OnceLock;

use k_rust::{
    backend::{Backend, BackendOptions},
    k_rust_backend::definition::BackendDefinition,
    kast::Sort as KastSort,
    kompile::{ConfigurationAssembler, ConfigurationError},
    kore::{
        ast::{KoreString, Pattern, Sort as KoreSort, Symbol, Variable, VariableKind},
        printer::Printer,
    },
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
    values::{Constraints, Value, ValueSort},
};

const COMMUTE_IMP: &str = include_str!("../../tests/data/imp/commute.imp");
const LOOP_IMP: &str = include_str!("../../tests/data/imp/loop.imp");
const SUM_PGM: &str = include_str!("../../tests/data/unsigned/sum.pgm");
const SETTLE_PGM: &str = include_str!("../../tests/data/ledger/settle.pgm");
const SETTLE_TX: &str = include_str!("../../tests/data/ledger/settle.tx");

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
fn the_program_text_is_never_modified() {
    let definition = imp();
    let program = program("imp/commute.imp", COMMUTE_IMP, &[]);
    let holes = resolve_ok(
        &[
            span("X", "Int", "imp/commute.imp", None, "x = 3;", "3"),
            span("Y", "Int", "imp/commute.imp", Some(3), "5", "5"),
        ],
        &program,
        definition,
    );
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
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
        .assemble(definition, &instantiated)
        .expect("the instantiated program assembles");
    assert_eq!(check.check(&built, &values), Ok(()));
    // The swapped values are at the wrong positions.
    assert!(check.check(&built, &[int(11), int(-7)]).is_err());
    let ProgramInput::Source(ProgramSource {
        program: Some(text),
        ..
    }) = &program
    else {
        unreachable!("built as a source program");
    };
    assert_eq!(text.text.as_bytes(), COMMUTE_IMP.as_bytes());
}

#[test]
fn the_anchor_program_assembles_as_krun_assembles_it() {
    let definition = imp();
    let program = program("imp/commute.imp", COMMUTE_IMP, &[]);
    let holes = resolve_ok(
        &[span("X", "Int", "imp/commute.imp", None, "x = 3;", "3")],
        &program,
        definition,
    );
    let anchors = [int(3)];
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let built = assembly
        .assemble(definition, &instantiate(&program, &holes, &anchors))
        .expect("the anchor program assembles");

    // krun's order, spelled out on the public assembler (main.rs:2508-2552).
    let mut krun = ConfigurationAssembler::new(
        assembly.grammar(),
        definition.main_module.as_str(),
        definition.syntax_module.as_str(),
        &definition.configuration_variables,
    );
    krun.program_file(&KastSort::new("Pgm"), COMMUTE_IMP, "imp/commute.imp")
        .expect("the program parses");
    krun.bind_stream_defaults(false, false, || Ok::<_, ConfigurationError>(b"\n".to_vec()))
        .expect("the stream defaults bind");
    let expected = krun.finish().expect("the configuration assembles");
    assert_eq!(printed(&built), printed(&expected));

    // A reused assembler gives the same configuration, also after a program that fails.
    let mut reused = assembly.assembler(definition);
    let broken = self::program("imp/commute.imp", "int x; x = ;", &[]);
    let broken = instantiate(&broken, &ResolvedHoles { holes: Vec::new() }, &[]);
    assert!(reused.assemble(&broken).is_err());
    for _ in 0..2 {
        let again = reused
            .assemble(&instantiate(&program, &holes, &anchors))
            .expect("the anchor program assembles");
        assert_eq!(printed(&again), printed(&expected));
    }
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
