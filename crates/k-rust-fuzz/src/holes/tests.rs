//! Tests of the hole overlay and of assembly (FZ-02), on FZ-FIX's fixture definitions
//! (`tests/support`). The functions under test are crate-private, so these are unit tests.

use std::sync::OnceLock;

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    k_rust_backend::definition::BackendDefinition,
    kore::{
        ast::{KoreString, Pattern, Sort as KoreSort, Symbol, Variable, VariableKind},
        codec,
        parser::parse_pattern,
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
    support,
    values::{
        Constraints, ElementSorts, Value, ValueSort,
        print::{print_k_text, to_kore_with_sort},
    },
};

const IMP_K: &str = include_str!("../../tests/data/imp/imp.k");
const GO_PGM: &str = include_str!("../../tests/data/streams/go.pgm");
const TOY_PGM: &str = include_str!("../../tests/data/toy/send.pgm");
const ONE_PGM: &str = include_str!("../../tests/data/wraps/one.pgm");
const COMMUTE_IMP: &str = include_str!("../../tests/data/imp/commute.imp");
const LOOP_IMP: &str = include_str!("../../tests/data/imp/loop.imp");
const SUM_PGM: &str = include_str!("../../tests/data/unsigned/sum.pgm");
const SETTLE_PGM: &str = include_str!("../../tests/data/ledger/settle.pgm");
const SETTLE_TX: &str = include_str!("../../tests/data/ledger/settle.tx");
const ELEMENTS_PGM: &str = include_str!("../../tests/data/elements/sum.pgm");
const SYNTAXVARS_PGM: &str = include_str!("../../tests/data/syntaxvars/go.pgm");
const LOCATED_PGM: &str = include_str!("../../tests/data/located/sum.pgm");

fn values() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::VALUES.compiled().definition())
}

fn toy() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::TOY.compiled().definition())
}

fn streams() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::STREAMS.compiled().definition())
}

fn wraps() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::WRAPS.compiled().definition())
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

fn elements() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::ELEMENTS.compiled().definition())
}

fn syntaxvars() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::SYNTAXVARS.compiled().definition())
}

fn located() -> &'static CompiledDefinition {
    static DEFINITION: OnceLock<CompiledDefinition> = OnceLock::new();
    DEFINITION.get_or_init(|| support::LOCATED.compiled().definition())
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
        k_text: Some(value.to_string()),
        kore: int_kore(value),
        sort: kore_sort("SortInt"),
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
        assert!(hole.refusals.is_empty());
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
    assert_eq!(hole.refusals, [("Id".to_owned(), SortRefusal::Token)]);
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
            refusals: Vec::new(),
            constraints: Constraints::default(),
            narrowing: None,
        }],
    };
    let value = PrintedValue {
        k_text: Some("transfer(5, 0)".to_owned()),
        kore: int_kore(0),
        sort: kore_sort("SortInt"),
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
        refusals: Vec::new(),
        constraints: Constraints::default(),
        narrowing: None,
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
    let definition = support::compile_source(&definition_name, &source, "IMP");
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
    // specification are never modified or copied (ARCHITECTURE 2.1). The `krust-fuzz`
    // executable (`src/bin`) is not library code: it writes the report and witness files its
    // user names, never the program or the campaign file.
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
    let executable = std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/src/bin"));
    while let Some(path) = pending.pop() {
        if path == executable {
            continue;
        }
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
    assert_eq!(hole.refusals, [("Id".to_owned(), SortRefusal::Token)]);
    // The report records the refused sort, not the hole's own (`Map`), once per refusal.
    let record = |sort: &str, refusal: &str| crate::report::SortOverride {
        hole: "M".to_owned(),
        sort: sort.to_owned(),
        refusal: refusal.to_owned(),
    };
    assert_eq!(hole.sort_overrides(), [record("Id", "Token")]);
    let mut two = hole.clone();
    two.refusals
        .push(("Stmt".to_owned(), SortRefusal::ProgramSyntax));
    assert_eq!(
        two.sort_overrides(),
        [record("Id", "Token"), record("Stmt", "ProgramSyntax")]
    );
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
    let (kore, kore_sort) = to_kore_with_sort(value, sort).expect("the value has KORE");
    let printed = [PrintedValue {
        k_text: Some(print_k_text(value, sort).expect("the value prints")),
        kore,
        sort: kore_sort,
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

#[test]
fn a_value_of_another_length_round_trips_where_locations_are_recorded() {
    // Every `Exp` of LOCATED carries its line and columns, so a value printed longer or shorter
    // than its anchor moves the columns of the terms after it and around it; the whole-
    // configuration comparison (review R1) lets only those move.
    let definition = located();
    let program = program("located/sum.pgm", LOCATED_PGM, &[]);
    let holes = resolve_ok(
        &[span("N", "Int", "located/sum.pgm", None, "22", "22")],
        &program,
        definition,
    );
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .unwrap_or_else(|error| panic!("the hole is located: {error}"));
    assert!(
        printed(check.anchor_configuration()).contains("Lbl'Hash'location"),
        "the fixture records locations: {}",
        printed(check.anchor_configuration())
    );
    for value in [7, 12345, -5, 22] {
        let values = [int(value)];
        let built = assembly
            .assemble(definition, &instantiate(&program, &holes, &values))
            .expect("the case assembles");
        assert_eq!(check.check(&built, &values), Ok(()), "{value}");
    }
}

#[test]
fn a_collection_hole_declares_only_elements_its_element_production_takes() {
    // ELEMENTS' `Stmts` holds `Stmt`s and its `Ints` holds `Int`s, both hooked `LIST.List` and
    // reached from `Pgm` (review 2, N-a). A value of either is built from its own element
    // production, so its elements are of the sort that production takes.
    let definition = elements();
    let program = program("elements/sum.pgm", ELEMENTS_PGM, &[]);
    let list = |sort: &str, element: &str| {
        with_elements(
            span(
                "H",
                sort,
                "elements/sum.pgm",
                None,
                "int(1) int(2)",
                "int(1) int(2)",
            ),
            ElementSorts::Elements {
                element: element.to_owned(),
            },
        )
    };
    let check = |decl: &HoleDecl| check_hole_sort(decl, &program, definition);
    let not_held = |sort: &str, declared: &str, element: &str| {
        refused(
            sort,
            SortRefusal::ElementNotHeld {
                declared: declared.to_owned(),
                element: element.to_owned(),
            },
        )
    };
    assert_eq!(check(&list("Ints", "Int")), Ok(None));
    assert_eq!(
        check(&list("Stmts", "Int")),
        not_held("Stmts", "Int", "Stmt")
    );
    assert_eq!(
        check(&list("Ints", "Stmt")),
        not_held("Ints", "Stmt", "Int")
    );
    // No override admits an element the collection cannot hold.
    let overridden = HoleDecl {
        allow_refused_sort: true,
        ..list("Stmts", "Int")
    };
    assert_eq!(check(&overridden), not_held("Stmts", "Int", "Stmt"));
    // The elements it does hold are statements, which are program syntax.
    assert_eq!(
        check(&list("Stmts", "Stmt")),
        refused("Stmts", SortRefusal::ProgramSyntax)
    );
    // Resolution refuses the same way, before any value is generated.
    assert_eq!(
        resolve_err(&[list("Stmts", "Int")], &program, definition),
        CampaignError::RefusedHoleSort {
            hole: "H".to_owned(),
            sort: "Stmts".to_owned(),
            reason: SortRefusal::ElementNotHeld {
                declared: "Int".to_owned(),
                element: "Stmt".to_owned(),
            },
        }
    );
}

/// The SYNTAXVARS program and its bindings.
fn syntaxvars_program() -> ProgramInput {
    program(
        "syntaxvars/go.pgm",
        SYNTAXVARS_PGM,
        &[
            ("LIB", "lib 2"),
            ("LIB2", "lib2 loop ret 3"),
            ("EXT", "ext arg 4"),
            ("C", "circle(3)"),
            ("SHAPE", "square(4)"),
        ],
    )
}

#[test]
fn a_configuration_variable_read_with_the_syntax_module_is_program_syntax() {
    // `$LIB` is parsed with the syntax module (its cell's `parser` attribute), as the program
    // is, so `Lib` is a sort programs are written in, although `Pgm` does not reach it (review
    // 2, N-b). `$C` and `$SHAPE` are parsed with the main module: their sorts stay data.
    let definition = syntaxvars();
    let program = syntaxvars_program();
    let check = |sort: &str, variable: &str| {
        check_hole_sort(&config_var("H", sort, variable), &program, definition)
    };
    assert_eq!(
        check("Lib", "LIB"),
        refused("Lib", SortRefusal::ProgramSyntax)
    );
    assert_eq!(check("Circle", "C"), Ok(None));
    assert_eq!(check("Shape", "SHAPE"), Ok(None));
    // `$LIB2` has no `parser` attribute, so the main module reads it; but `Lib2` is declared in
    // the syntax module, so its values are terms of the program grammar whichever module reads
    // them, and so are those of `Body`, which they contain (HARD-A review, S2).
    assert_eq!(
        check("Lib2", "LIB2"),
        refused("Lib2", SortRefusal::ProgramSyntax)
    );
    assert_eq!(
        check("Body", "LIB2"),
        refused("Body", SortRefusal::ProgramSyntax)
    );
    // `$EXT` is read with a second grammar module its cell names: the sorts that grammar reaches
    // from `Ext` are program syntax too.
    assert_eq!(
        check("Ext", "EXT"),
        refused("Ext", SortRefusal::ProgramSyntax)
    );
    assert_eq!(
        check("Arg", "EXT"),
        refused("Arg", SortRefusal::ProgramSyntax)
    );
    assert_eq!(
        check("Pgm", "C"),
        refused("Pgm", SortRefusal::ProgramSyntax)
    );
}

#[test]
fn a_configuration_variable_hole_takes_values_of_the_variable_sort() {
    // A case's value replaces the whole binding, which is parsed at the variable's declared
    // sort: the hole's sort must be that sort or a subsort of it (review 2, under S2).
    let definition = syntaxvars();
    let program = syntaxvars_program();
    let mismatch = |hole: &str, variable_sort: &str| {
        span_error(hole, SpanProblem::ConfigVarSort(variable_sort.to_owned()))
    };
    // `$C:Circle` bound to `circle(3)`: a `Shape` hole would also generate squares.
    assert_eq!(
        resolve_err(&[config_var("C", "Shape", "C")], &program, definition),
        mismatch("C", "Circle")
    );
    assert_eq!(
        resolve_err(&[config_var("C", "Square", "C")], &program, definition),
        mismatch("C", "Circle")
    );
    // The variable's own sort, and a subsort of it, are admitted.
    let holes = resolve_ok(
        &[
            config_var("C", "Circle", "C"),
            config_var("S", "Square", "SHAPE"),
        ],
        &program,
        definition,
    );
    assert_eq!(holes.holes.len(), 2);
    // LEDGER's `$TX:Tx` with a hole of another record sort.
    let definition = ledger();
    let program = self::program(
        "ledger/settle.pgm",
        SETTLE_PGM,
        &[("TX", SETTLE_TX.trim_end())],
    );
    assert_eq!(
        resolve_err(&[config_var("T", "Account", "TX")], &program, definition),
        mismatch("T", "Tx")
    );
}

/// The narrowings `super::probe_negatives` gives `decls` on `definition` (FZ-INTGEN).
fn narrowings(
    decls: &[HoleDecl],
    program: &ProgramInput,
    definition: &CompiledDefinition,
) -> Vec<Option<super::Narrowing>> {
    let holes = resolve_ok(decls, program, definition);
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, program, &holes)
        .expect("the anchors parse back at their positions");
    super::probe_negatives(&holes, &check, &assembly, definition, program, "baseline")
        .expect("the probe runs")
}

fn ranged(mut decl: HoleDecl, min: Option<i64>, max: Option<i64>) -> HoleDecl {
    decl.constraints.range = Some(crate::values::IntRange {
        min: min.map(BigInt::from),
        max: max.map(BigInt::from),
    });
    decl
}

#[test]
fn an_unsigned_literal_position_narrows_an_int_hole_to_non_negative_values() {
    let definition = unsigned();
    let program = program("unsigned/sum.pgm", SUM_PGM, &[]);
    let decls = [
        span("A", "Int", "unsigned/sum.pgm", None, "7 +", "7"),
        span("B", "Int", "unsigned/sum.pgm", None, "+ 5", "5"),
    ];
    let found = narrowings(&decls, &program, definition);
    for (name, narrowing) in ["A", "B"].iter().zip(&found) {
        let narrowing = narrowing
            .as_ref()
            .unwrap_or_else(|| panic!("hole {name} is narrowed"));
        assert_eq!(narrowing.probe, "-1");
        assert_eq!(narrowing.side, "baseline");
        // `-1` reads as the negation `neg(1)`, an application, not the domain value -1.
        assert!(narrowing.found.contains("Lblneg"), "{narrowing:?}");
        assert!(
            narrowing.reason().contains("`-1`"),
            "{}",
            narrowing.reason()
        );
    }

    // The probe is the admissible negative value nearest zero.
    let found = narrowings(
        &[ranged(decls[1].clone(), Some(-50), Some(-7))],
        &program,
        definition,
    );
    assert_eq!(found[0].as_ref().map(|n| n.probe.as_str()), Some("-7"));

    // Bounds that admit no negative value, and a choice set, are not probed.
    let mut chosen = decls[1].clone();
    chosen.constraints.choices = Some(vec![Value::Int(BigInt::from(-3))]);
    let found = narrowings(
        &[ranged(decls[0].clone(), Some(0), None), chosen],
        &program,
        definition,
    );
    assert_eq!(found, vec![None, None]);
}

#[test]
fn narrowing_starts_the_range_at_zero_and_refuses_an_all_negative_range() {
    let definition = unsigned();
    let program = program("unsigned/sum.pgm", SUM_PGM, &[]);
    let decl = ranged(
        span("B", "Int", "unsigned/sum.pgm", None, "+ 5", "5"),
        Some(-40),
        Some(4),
    );
    let mut holes = resolve_ok(std::slice::from_ref(&decl), &program, definition);
    let assembly = ProgramAssembly::new(definition).expect("the grammar resolves");
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .expect("the anchor parses back");
    let found = super::probe_negatives(&holes, &check, &assembly, definition, &program, "mutant")
        .expect("the probe runs");
    holes.narrow(found.clone()).expect("the range keeps 0 .. 4");
    let hole = &holes.holes[0];
    assert_eq!(
        hole.constraints.range,
        Some(crate::values::IntRange {
            min: Some(BigInt::from(0)),
            max: Some(BigInt::from(4)),
        })
    );
    assert_eq!(
        hole.decl.constraints, decl.constraints,
        "the declaration is kept"
    );
    assert_eq!(hole.narrowing.as_ref().map(|n| n.side), Some("mutant"));
    // A second narrowing of a narrowed hole keeps the first.
    holes.narrow(found).expect("idempotent");
    assert_eq!(
        holes.holes[0].narrowing.as_ref().map(|n| n.side),
        Some("mutant")
    );

    let negative = ranged(decl, Some(-40), Some(-2));
    let mut holes = resolve_ok(std::slice::from_ref(&negative), &program, definition);
    let check = RoundTripCheck::new(&assembly, definition, &program, &holes)
        .expect("the anchor parses back");
    let found = super::probe_negatives(&holes, &check, &assembly, definition, &program, "baseline")
        .expect("the probe runs");
    let error = holes
        .narrow(found)
        .expect_err("no value of -40 .. -2 can be written");
    assert!(
        matches!(&error, CampaignError::InvalidConstraints { hole, message }
            if hole == "B" && message.contains("every value of its range is negative")),
        "{error}"
    );
}

#[test]
fn a_position_that_reads_negative_literals_is_not_narrowed() {
    // IMP's Int literals are signed: `-1` is one token, the domain value -1.
    let definition = imp();
    let program = program("imp/commute.imp", COMMUTE_IMP, &[]);
    let found = narrowings(
        &[span("X", "Int", "imp/commute.imp", None, "x = 3;", "3")],
        &program,
        definition,
    );
    assert_eq!(found, vec![None]);

    // Signed literals inside located expressions: the columns after the hole move, nothing
    // else does.
    let definition = located();
    let program = self::program("located/sum.pgm", LOCATED_PGM, &[]);
    let found = narrowings(
        &[span("Y", "Int", "located/sum.pgm", None, "22", "22")],
        &program,
        definition,
    );
    assert_eq!(found, vec![None]);

    // A configuration-variable hole replaces a whole binding, not a literal of program text,
    // and is never probed.
    let definition = streams();
    let program = self::program("streams/go.pgm", GO_PGM, &[("LIMIT", "3")]);
    let found = narrowings(&[config_var("L", "Int", "LIMIT")], &program, definition);
    assert_eq!(found, vec![None]);
}
