//! Plain `anywhere` heads in the fuzz engine (KRUST-ANYWHERE-HEAD; finding ANYWHERE-HEAD).
//!
//! SIMPLE's array lookup `_[_]` is declared `anywhere, function, value-production` and roots
//! two plain `anywhere` equations (`simple.md` 647 and 650), neither of which matches an
//! application whose receiver is an `Id`. So `a[4]`, stored in a function body (`var a[4];`
//! in `main`'s closure) or written by a program, is a normal form in every context and a value
//! of its sort: it exists (k-rust's `ground_defined`) and it is data. At TRIAL3's base every
//! such leaf was `not-ceil-free` (the stored attribute refuses every partial application) and
//! every such end not data (`_[_]` roots equations that are not overload equations), so no
//! array program could be judged.

mod support;

use std::sync::{Arc, OnceLock};

use k_rust::{
    backend::{
        Backend, BackendError, BackendOptions, ExecuteRequest, ExecutionStrategy, HaltReasonOutput,
        ResultModalityOutput,
    },
    diagnostic::DiagnosticCode,
    kast::Sort,
    kompile::{ConfigurationAssembler, ProgramGrammar},
};
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions,
    HoleDecl, HoleLocation, OutcomeClass, ProgramInput, ProgramSource, ProposerConfig, SpanAddress,
    Target, TargetKind,
    exec::UnjudgedReason,
    report::{FuzzReport, KillKind},
    spec::{CompiledDefinition, DEFAULT_REJECTION_CAP, ProgramText},
    target::{DifferentialTarget, PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;

const SIMPLE: &str = include_str!("data/simple/simple.md");
/// The rule of `sizeOf` (`simple.md:660`), which TRIAL3's mutation `sizeof-plus-one` edits.
const SIZEOF: &str = "rule sizeOf(array(_,N)) => N\n";

/// SIMPLE untyped with `source`'s text, compiled once per test binary and source.
fn compile(source: &str) -> Arc<CompiledDefinition> {
    Arc::new(support::compile_source_with(
        "simple/simple.md",
        source,
        "SIMPLE-UNTYPED",
        &[DiagnosticCode::CellCollectionVarWithoutInitial],
    ))
}

fn simple() -> Arc<CompiledDefinition> {
    static COMPILED: OnceLock<Arc<CompiledDefinition>> = OnceLock::new();
    Arc::clone(COMPILED.get_or_init(|| compile(SIMPLE)))
}

/// SIMPLE with `sizeOf` one too large (TRIAL3's `sizeof-plus-one`).
fn sizeof_plus_one() -> Arc<CompiledDefinition> {
    static COMPILED: OnceLock<Arc<CompiledDefinition>> = OnceLock::new();
    Arc::clone(COMPILED.get_or_init(|| {
        assert_eq!(SIMPLE.matches(SIZEOF).count(), 1);
        compile(&SIMPLE.replace(SIZEOF, "rule sizeOf(array(_,N)) => N +Int 1\n"))
    }))
}

/// SIMPLE with an added `anywhere` rule that rewrites an array access whose receiver is an
/// `Id`, which the baseline's `a[4]` is (review M7).
fn id_receiver_rule() -> Arc<CompiledDefinition> {
    static COMPILED: OnceLock<Arc<CompiledDefinition>> = OnceLock::new();
    Arc::clone(COMPILED.get_or_init(|| {
        compile(&SIMPLE.replace(
            SIZEOF,
            "rule sizeOf(array(_,N)) => N\n  rule _X:Id [ _N:Int ] => 0 [anywhere]\n",
        ))
    }))
}

/// The program `name` of `tests/data/simple`.
fn program(name: &'static str) -> (&'static str, &'static str) {
    let text = match name {
        "arraydecl.simple" => include_str!("data/simple/arraydecl.simple"),
        "array.simple" => include_str!("data/simple/array.simple"),
        "matrix.simple" => include_str!("data/simple/matrix.simple"),
        "exc.simple" => include_str!("data/simple/exc.simple"),
        "div.simple" => include_str!("data/simple/div.simple"),
        "join.simple" => include_str!("data/simple/join.simple"),
        "rdv.simple" => include_str!("data/simple/rdv.simple"),
        _ => panic!("no program {name}"),
    };
    (name, text)
}

/// An `Int` hole named `name` at `literal` in `find`, ranging over `min..=max`.
fn int_hole(
    name: &str,
    program: &str,
    find: &str,
    literal: &str,
    (min, max): (i64, i64),
) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            column: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints {
            range: Some(IntRange {
                min: Some(BigInt::from(min)),
                max: Some(BigInt::from(max)),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }
}

fn spec(
    baseline: Arc<CompiledDefinition>,
    mutant: Option<Arc<CompiledDefinition>>,
    (name, text, start_sort): (&str, &str, &str),
    holes: Vec<HoleDecl>,
    kind: TargetKind,
) -> CampaignSpec {
    CampaignSpec {
        definitions: Definitions { baseline, mutant },
        program: ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: name.into(),
                text: text.into(),
                start_sort: start_sort.into(),
            }),
            config_vars: Vec::new(),
        }),
        holes,
        target: Target {
            kind,
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 3,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

/// A differential campaign of SIMPLE against `mutant` on `program`, with the hole `SZ` on the
/// array size `var a[4];` over `range`.
fn sizes(mutant: Arc<CompiledDefinition>, program: &'static str, range: (i64, i64)) -> FuzzReport {
    let (name, text) = self::program(program);
    let report = Campaign::new(spec(
        simple(),
        Some(mutant),
        (name, text, "Stmt"),
        vec![int_hole("SZ", name, "var a[4];", "4", range)],
        TargetKind::Differential(DifferentialTarget::default()),
    ))
    .expect("the campaign is valid")
    .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    report
}

/// No case was left unjudged because a leaf is not shown to exist, or an end is not data.
fn assert_array_ends_judged(report: &FuzzReport) {
    for reasons in [
        &report.totals.unsupported_reasons,
        &report.totals.baseline_incomplete_reasons,
    ] {
        for reason in [
            UnjudgedReason::NotCeilFree,
            UnjudgedReason::MutantEndNotData,
            UnjudgedReason::BaselineEndNotData,
        ] {
            assert!(!reasons.contains_key(&reason), "{:?}", report.totals);
        }
    }
}

/// TRIAL3's `arraydecl` template (`var a[SZ]; print(sizeOf(a), "\n");`) against
/// `sizeof-plus-one`: at TRIAL3's base all 7 cases were `baseline-incomplete`, `not-ceil-free`
/// on `_[_]`, since the store keeps `main`'s closure, which holds `var a[SZ];`. Now the
/// baseline's ends are judged, and the mutant prints one more: an added end, killed.
#[test]
fn an_array_declaration_is_judged_and_sizeof_plus_one_is_killed() {
    let report = sizes(sizeof_plus_one(), "arraydecl.simple", (0, 6));
    assert_array_ends_judged(&report);
    let witness = report.witness().expect("a kill");
    assert_eq!(witness.first.kill, Some(KillKind::AddedEnd));
}

/// TRIAL3's `array` program, which stores `a[i] = i * i` and reads `a[2]` and `a[3]`: its
/// closure holds `a[i]`, `a[2]` and `a[3]` (receiver `a`), and `sizeof-plus-one` is killed on
/// it too.
#[test]
fn a_stored_and_read_array_element_is_judged_and_sizeof_plus_one_is_killed() {
    let report = sizes(sizeof_plus_one(), "array.simple", (4, 6));
    assert_array_ends_judged(&report);
    let witness = report.witness().expect("a kill");
    assert_eq!(witness.first.kill, Some(KillKind::AddedEnd));
}

/// Review M7: the mutant adds `X:Id[N] => 0 [anywhere]`, which reaches the baseline's stored
/// `a[SZ]`. The two definitions do not name the same values with `_[_]` any more: the
/// baseline's end is data in the baseline only, so no end is compared, and the change is never
/// a kill through it.
#[test]
fn a_mutant_whose_anywhere_rule_reaches_a_stored_array_access_is_never_killed_through_it() {
    let report = sizes(id_receiver_rule(), "arraydecl.simple", (0, 6));
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert!(
        report
            .totals
            .classes
            .keys()
            .all(|class| matches!(class, OutcomeClass::Unsupported | OutcomeClass::Rejected)),
        "{:?}",
        report.totals
    );
    assert_eq!(
        report.totals.unsupported_reasons.keys().collect::<Vec<_>>(),
        [&UnjudgedReason::BaselineEndNotData],
        "{:?}",
        report.totals
    );
}

/// Review M2: data implies existence. Every stuck end of SIMPLE's array, matrix, exception,
/// division and thread programs (one-header map keys only: locations and names) that is data
/// is shown to exist, and the array and matrix ends are data.
#[test]
fn every_simple_data_end_exists() {
    let compiled = simple();
    let BackendRoute::SourceExecution {
        execution_rewrite_order,
    } = &compiled.route
    else {
        panic!("an in-process compilation is on krun's route");
    };
    let definition = Backend::internalize_source_definition(
        &compiled.kore,
        &compiled.main_module,
        execution_rewrite_order,
    )
    .expect("SIMPLE internalizes");
    let mut backend =
        Backend::from_internalized(definition, BackendOptions::default()).expect("a backend");
    let grammar = ProgramGrammar::new(&compiled.frontend_definition).expect("a program grammar");
    let mut data_ends = Vec::new();
    for name in [
        "arraydecl.simple",
        "array.simple",
        "matrix.simple",
        "exc.simple",
        "div.simple",
        "join.simple",
        "rdv.simple",
    ] {
        let (_, text) = program(name);
        let mut assembler = ConfigurationAssembler::new(
            &grammar,
            &compiled.main_module,
            &compiled.syntax_module,
            &compiled.configuration_variables,
        );
        assembler
            .program_file(&Sort::new("Stmt"), text, name)
            .expect("the program parses");
        assembler
            .bind_stream_defaults(false, false, || {
                Ok::<_, k_rust::kompile::ConfigurationError>(b"\n".to_vec())
            })
            .expect("the streams bind");
        let initial = assembler.finish().expect("the configuration assembles");
        let result = backend
            .execute(ExecuteRequest {
                strategy: ExecutionStrategy::All,
                result_modality: ResultModalityOutput::StateSet,
                ..ExecuteRequest::new(initial)
            })
            .expect("the program runs");
        for leaf in result
            .leaves
            .iter()
            .filter(|leaf| leaf.reason == HaltReasonOutput::Stuck)
        {
            let state = k_rust::kore::codec::from_value(&leaf.state).expect("a KORE leaf");
            let (data, defined) = backend
                .with_solver_over(None, &[&state], |definition, _| {
                    let term = definition
                        .admit_unverified(&state, &[])
                        .internalize_term()
                        .expect("the leaf internalizes");
                    let data = definition.is_data(&term, &definition.data_heads());
                    Ok::<_, BackendError>((data, definition.ground_defined(&term)))
                })
                .expect("the backend selects its definition");
            assert!(!data || defined, "{name}: a data end is not shown to exist");
            if data {
                data_ends.push(name);
            }
        }
    }
    for name in ["arraydecl.simple", "array.simple", "matrix.simple"] {
        assert!(
            data_ends.contains(&name),
            "{name}: no data end ({data_ends:?})"
        );
    }
}

/// A small definition with a plain `anywhere` head `_[_]` and two guarded equations whose
/// right-hand side may be undefined (`100 /Int N`), so that the compiler declares `_[_]` a
/// partial `value-production` (with `N` as the right-hand side it would be `functional`, and
/// every application would exist by that declaration): `a[N] => 100 /Int N requires N >=Int 10`,
/// whose condition k-rust decides on a ground index, and `c[N] => 100 /Int N requires good(N)`,
/// where `good` is a total function with an equation for 10 only, so that `good(3)` is a value
/// of `Bool` no evaluation decides. `go(E)` stores `E` in `<s>`.
const BLOCK: &str = r#"
module BLOCK-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Exp ::= Int | "a" | "b" | "c" | Exp "[" Int "]"
  syntax Bool ::= good(Int) [function, total]
  syntax Pgm ::= go(Exp)
endmodule

module BLOCK
  imports BLOCK-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(E) => .K </k> <s> _ => E </s>
  rule good(10) => true
  rule a [ N ] => 100 /Int N requires N >=Int 10 [anywhere]
  rule c [ N ] => 100 /Int N requires good(N) [anywhere]
endmodule
"#;

/// Review M7: `at: any-state` reads k-rust's `ground_defined` on each reached state, which
/// discharges an application of the `value-production` head `_[_]` only where no equation can
/// reach it.
/// - `b[3]`: no equation matches, so it is a value, and the end holding it reaches
///   `<k> .K </k>`: a hit. At the base, the stored attribute refused it (`not-ceil-free`).
/// - `c[3]`: the equation `c[N]` matches and its condition `good(3)` is undecided, so the
///   application is reducible in some model and blocked here: it is not shown to exist, so the
///   end matches but the case is `unsupported` (`not-ceil-free`), never a hit.
/// - `a[3]`: the equation `a[N]` matches and its condition `3 >=Int 10` is false. Instance
///   normality ignores conditions, so this one is refused as well: lost precision, never a
///   wrong claim.
#[test]
fn any_state_reads_existence_of_a_plain_anywhere_application() {
    let compiled = Arc::new(support::compile_source("block.k", BLOCK, "BLOCK"));
    let run = |text: &str| {
        Campaign::new(spec(
            Arc::clone(&compiled),
            None,
            ("go.pgm", text, "Pgm"),
            vec![int_hole("N", "go.pgm", "3", "3", (3, 3))],
            TargetKind::Pattern(PatternTarget {
                pattern: "<k> .K </k>".into(),
                at: PatternAt::AnyState,
            }),
        ))
        .expect("the campaign is valid")
        .run(Budget::Cases(2), None)
    };
    let defined = run("go(b[3])");
    assert!(defined.witness().is_some(), "{:?}", defined.outcome);
    for text in ["go(c[3])", "go(a[3])"] {
        let blocked = run(text);
        assert!(blocked.witness().is_none(), "{text}: {:?}", blocked.outcome);
        assert_eq!(
            blocked
                .totals
                .unsupported_reasons
                .keys()
                .collect::<Vec<_>>(),
            [&UnjudgedReason::NotCeilFree],
            "{text}: {:?}",
            blocked.totals
        );
    }
}
