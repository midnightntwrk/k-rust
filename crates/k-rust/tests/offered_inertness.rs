//! Asking for the offered level of run coverage changes nothing but the level itself
//! (docs/compatibility.md, "Run coverage"): every run is the same with `collect_offered` on and
//! off, apart from `coverage.offered` and `Counter::CoverageOfferMatches`.
//!
//! The probes that compute the level match left-hand sides the run never tried against
//! subjects the run holds. A probe that leaked into the run (a fresh or renamed-apart name it
//! took, a diagnostic or its emission position, a path fact, a cache entry, a counter, another
//! coverage set) would change some output of some run, so the oracle compares every output of
//! every run of a corpus in pairs, offered on and off: each fixture of `run_coverage.rs` (the
//! `COVER` and `OFFER` definitions, ground, symbolic and constrained inputs) and the light IMP
//! corpus, under both strategies and both result modalities, by every execution route that
//! collects coverage: executed (plain, stopping at a branch, with a breadth bound of one,
//! assuming the state defined), executed observed, and, for ground inputs, executed with a
//! console. Both sides collect `applied` and `matched`, which must be equal too. Search, proof
//! and simplification do not take the option and open no collection, so no probe runs there.
//!
//! Every run is bounded (`MAX_WORK`, `MAX_DEPTH`, `MAX_BREADTH`): IMP's `strict` attributes
//! admit every evaluation order, and an unbounded run under strategy `all` enumerates every
//! interleaving. A bound that fires fires alike on both sides.
//!
//! The facade's states never hold a variable spelled like an internalized rule variable, so no
//! probe here renames a rule apart; the backend's oracle
//! (`k_rust_backend`'s `tests::coverage::asking_for_offered_changes_no_result_and_no_counter`)
//! runs states that do and compares the observed bindings, which name the renamed variables.
//!
//! A later finding of the same kind becomes an input here.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ObservedRequest,
        ResultModalityOutput,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::{ast::Pattern, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_kore::measure::{self, Counter, Snapshot};
use serde_json::Value;

const COVER: &str = include_str!("fixtures/coverage/cover.k");
const OFFER: &str = include_str!("fixtures/coverage/offer.k");
/// IMP of the K tutorial: the light corpus.
const IMP: &str = include_str!("fixtures/kink/imp-lesson-4.k");

const STRATEGIES: [ExecutionStrategy; 2] = [ExecutionStrategy::All, ExecutionStrategy::Any];
const MODALITIES: [ResultModalityOutput; 2] = [
    ResultModalityOutput::PathSet,
    ResultModalityOutput::StateSet,
];

const MAX_WORK: u64 = 400;
const MAX_DEPTH: u64 = 400;
const MAX_BREADTH: usize = 16;
const MAX_SIMPLIFICATION_ITERATIONS: usize = 100;

/// The KORE of `source` and its configuration for `program` at sort `sort`.
fn compile_in(source: &str, main: &str, sort: &str, program: &str) -> (String, Pattern) {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("inert.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler =
        ConfigurationAssembler::new(&grammar, main, main, &artifacts.configuration_variables);
    assembler.program(&Sort::new(sort), program).unwrap();
    (artifacts.definition_kore, assembler.finish().unwrap())
}

/// One input of a definition.
#[derive(Clone, Copy)]
enum Input {
    /// A program.
    Ground(&'static str),
    /// A program whose `777`s become the variable `X` (and `778`s the variable `?_Y`).
    Symbolic(&'static str),
    /// [`Input::Symbolic`] under the constraint `X >=Int 0`.
    Constrained(&'static str),
}

impl Input {
    fn pattern(self, source: &str, main: &str, sort: &str) -> (String, Pattern) {
        let program = match self {
            Input::Ground(program) | Input::Symbolic(program) | Input::Constrained(program) => {
                program
            }
        };
        let (kore, ground) = compile_in(source, main, sort, program);
        if let Input::Ground(_) = self {
            return (kore, ground);
        }
        let printed = Printer::compact().print_pattern(&ground);
        let symbolic = printed
            .replace("\\dv{SortInt{}}(\"777\")", "VarX:SortInt{}")
            .replace("\\dv{SortInt{}}(\"778\")", "Var'QuesUnds'Y:SortInt{}");
        assert_ne!(symbolic, printed, "{program}");
        let text = match self {
            Input::Constrained(_) => format!(
                "\\and{{SortGeneratedTopCell{{}}}}({symbolic}, \\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(Lbl'Unds-GT-Eqls'Int'Unds'{{}}(VarX:SortInt{{}}, \\dv{{SortInt{{}}}}(\"0\")), \\dv{{SortBool{{}}}}(\"true\")))"
            ),
            _ => symbolic,
        };
        (kore, parse_pattern(&text).unwrap())
    }

    fn name(self) -> String {
        match self {
            Input::Ground(program) => program.to_owned(),
            Input::Symbolic(program) => format!("{program} with X for 777"),
            Input::Constrained(program) => format!("{program} with X >=Int 0 for 777"),
        }
    }
}

/// Everything a run gives, with `coverage.offered` taken out, and its counters.
struct Outputs {
    responses: Vec<Value>,
    counters: Snapshot,
    /// Whether some response held an `offered` list longer than its `matched` one: a probe
    /// found an axiom the run never tried.
    offered_more: bool,
}

/// A response as JSON, an error as its message.
fn json<T: serde::Serialize>(response: Result<T, k_rust::backend::BackendError>) -> Value {
    match response {
        Ok(response) => serde_json::to_value(&response).unwrap(),
        Err(error) => Value::String(format!("error: {}", error.message())),
    }
}

/// Take `coverage.offered` out of `value`; whether it held more ids than `coverage.matched`.
fn without_offered(value: &mut Value) -> bool {
    let Some(coverage) = value.get_mut("coverage").and_then(Value::as_object_mut) else {
        return false;
    };
    let matched = coverage["matched"].as_array().map_or(0, Vec::len);
    coverage
        .remove("offered")
        .and_then(|offered| offered.as_array().map(Vec::len))
        .is_some_and(|offered| offered > matched)
}

/// Run `work` on a thread of its own and count it.
fn counted<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> (T, Snapshot) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let before = measure::snapshot();
            let result = work();
            (result, measure::snapshot().delta(&before))
        })
        .unwrap()
        .join()
        .unwrap()
}

/// Run `initial` over `kore` by every execution route that collects coverage, under one strategy
/// and modality, with `collect_offered` on or off.
#[allow(clippy::too_many_arguments)]
fn run(
    kore: &str,
    main: &str,
    initial: &Pattern,
    strategy: ExecutionStrategy,
    modality: ResultModalityOutput,
    console: bool,
    offered: bool,
) -> Outputs {
    let (kore, main, initial) = (kore.to_owned(), main.to_owned(), initial.clone());
    let (responses, counters) = counted(move || {
        let request = || ExecuteRequest {
            result_modality: modality,
            strategy,
            collect_coverage: true,
            collect_offered: offered,
            max_work: Some(MAX_WORK),
            max_depth: Some(MAX_DEPTH),
            max_breadth: Some(MAX_BREADTH),
            max_simplification_iterations: MAX_SIMPLIFICATION_ITERATIONS,
            ..ExecuteRequest::new(initial.clone())
        };
        let mut backend = Backend::new(&kore, &main, BackendOptions::default()).unwrap();
        let mut responses = vec![
            json(backend.execute(request())),
            json(backend.execute(ExecuteRequest {
                stop_at_branch: true,
                ..request()
            })),
            json(backend.execute(ExecuteRequest {
                max_breadth: Some(1),
                ..request()
            })),
            json(backend.execute(ExecuteRequest {
                assume_state_defined: true,
                ..request()
            })),
            json(backend.execute_observed(ObservedRequest {
                request: request(),
                rules: None,
            })),
        ];
        if console {
            use k_rust_backend::{
                rewrite::{ExecutionMode, ExecutionOptions, execute_with_io_state},
                transition::ExecutionIoState,
            };
            let definition = backend.select_definition(None).unwrap();
            let pattern = definition
                .admit_unverified(&initial, &[])
                .internalize_pattern()
                .unwrap();
            let mode = match strategy {
                ExecutionStrategy::All => ExecutionMode::All,
                _ => ExecutionMode::Any,
            };
            let mut result = execute_with_io_state(
                &definition,
                pattern,
                ExecutionOptions {
                    mode,
                    collect_coverage: true,
                    collect_offered: offered,
                    max_work: Some(MAX_WORK),
                    max_depth: MAX_DEPTH,
                    max_breadth: Some(MAX_BREADTH),
                    max_simplification_iterations: MAX_SIMPLIFICATION_ITERATIONS,
                    ..ExecutionOptions::default()
                },
                ExecutionIoState::new(Vec::new()),
            );
            let coverage = result.coverage.as_mut().expect("coverage was asked for");
            let more = coverage
                .offered
                .take()
                .is_some_and(|offered| offered.len() > coverage.matched.len());
            responses.push(Value::String(format!("{result:#?}")));
            return (responses, more);
        }
        (responses, false)
    });
    let (mut responses, mut offered_more) = responses;
    for response in &mut responses {
        offered_more |= without_offered(response);
    }
    Outputs {
        responses,
        counters,
        offered_more,
    }
}

/// The counters other than `Counter::CoverageOfferMatches` that differ between `on` and `off`.
fn differing(on: &Snapshot, off: &Snapshot) -> Vec<(&'static str, u64, u64)> {
    on.iter()
        .zip(off.iter())
        .filter(|((name, on), (_, off))| *name != Counter::CoverageOfferMatches.name() && on != off)
        .map(|((name, on), (_, off))| (name, on, off))
        .collect()
}

/// Run every input of `source` under every strategy and modality, offered on and off, and
/// require equal outputs and counters. Returns how many pairs ran and in how many a probe found
/// an axiom the run never tried.
fn assert_inert(
    case: &str,
    source: &str,
    main: &str,
    sort: &str,
    inputs: &[Input],
) -> (usize, usize) {
    let mut pairs = 0;
    let mut probing = 0;
    let mut warmed = false;
    for &input in inputs {
        let (kore, initial) = input.pattern(source, main, sort);
        let console = matches!(input, Input::Ground(_));
        for strategy in STRATEGIES {
            for modality in MODALITIES {
                let context = format!("{case}: {} under {strategy:?} {modality:?}", input.name());
                let run_once =
                    |offered| run(&kore, main, &initial, strategy, modality, console, offered);
                if !warmed {
                    run_once(true);
                    warmed = true;
                }
                let on = run_once(true);
                let off = run_once(false);
                assert_eq!(on.responses.len(), off.responses.len(), "{context}");
                for (index, (on, off)) in on.responses.iter().zip(&off.responses).enumerate() {
                    assert_eq!(on, off, "{context}, route {index}: offered on, then off");
                }
                assert!(!off.offered_more, "{context}: offered without asking");
                let counters = differing(&on.counters, &off.counters);
                assert!(
                    counters.is_empty(),
                    "{context}: counters (name, on, off) {counters:?}"
                );
                assert_eq!(
                    off.counters.get(Counter::CoverageOfferMatches),
                    0,
                    "{context}"
                );
                pairs += 1;
                probing += usize::from(on.offered_more);
            }
        }
    }
    eprintln!("{case}: {pairs} pairs, {probing} with an axiom offered beyond matched");
    (pairs, probing)
}

use Input::{Constrained, Ground, Symbolic};

#[test]
fn the_cover_fixtures() {
    let (pairs, probing) = assert_inert(
        "COVER",
        COVER,
        "COVER",
        "Prog",
        &[
            Ground("seq(load(addr(1), 0), halt)"),
            Ground("seq(ens(1), halt)"),
            Ground("seq(rhsp(1), halt)"),
            Ground("seq(eqreq(1), halt)"),
            Ground("seq(rej(5), halt)"),
            Ground("seq(ow(5), halt)"),
            Ground("seq(ru(1), halt)"),
            Ground("seq(ru(-1), halt)"),
            Ground("seq(rv(-1), halt)"),
            Ground("seq(pr(1), halt)"),
            Ground("seq(hk(1), halt)"),
            Ground("seq(d1(5), halt)"),
            Ground("seq(d1(-5), halt)"),
            Ground("nd"),
            Symbolic("seq(rej(777), halt)"),
            Symbolic("seq(ow(777), halt)"),
            Symbolic("seq(d1(777), halt)"),
            Symbolic("seq(eqreq(777), halt)"),
            Constrained("seq(ru(777), halt)"),
            Constrained("seq(rhsp(777), halt)"),
        ],
    );
    assert!(probing > 0 && probing <= pairs);
}

#[test]
fn the_offer_fixtures() {
    let (pairs, probing) = assert_inert(
        "OFFER",
        OFFER,
        "OFFER",
        "Prog",
        &[
            Ground("seq(pa(1), halt)"),
            Ground("seq(pb(1), halt)"),
            Ground("seq(pc(5), halt)"),
            Ground("seq(pd(0), halt)"),
            Ground("seq(pd(5), halt)"),
            Ground("seq(pe(3), halt)"),
            Ground("seq(pn(1), halt)"),
            Ground("seq(py(1), halt)"),
            Ground("seq(ph(1), halt)"),
            Ground("seq(pk(5), halt)"),
            Ground("seq(pk(-5), halt)"),
            Symbolic("seq(pe(777), halt)"),
            Symbolic("seq(pc(777), halt)"),
            Symbolic("seq(pd(777), halt)"),
            Symbolic("seq(pk(777), halt)"),
            Constrained("seq(pc(777), halt)"),
            Constrained("seq(pk(777), halt)"),
            Symbolic("seq(pz(777), val(778))"),
            Constrained("seq(pz(777), val(778))"),
        ],
    );
    assert!(probing > 0 && probing <= pairs);
}

#[test]
fn the_light_imp_corpus() {
    let (pairs, probing) = assert_inert(
        "IMP",
        IMP,
        "IMP",
        "Pgm",
        &[
            Ground("int n, sum; n = 3; sum = 0; while (!(n <= 0)) { sum = sum + n; n = n + -1; }"),
            Ground(
                "int i, m, n, q, r, s, t, x, y, z; m = 4; n = 2; \
                 while (n <= m) { i = 2; q = n/i; t = 1; \
                 while (i<=q && 1<=t) { x = i; y = q; z = 0; \
                 while (!(x <= 0)) { q = x/2; r = q + q + 1; if (r <= x) { z = z + y; } else {} \
                 x = q; y = y + y; } \
                 if (n <= z) { t = 0; } else { i = i + 1; q = n/i; } } \
                 if (1 <= t) { s = s + 1; } else {} n = n + 1; }",
            ),
            Ground("int a; a = 1 / 0;"),
            Ground("int a, b, c; a = 2 + 3; b = 7 / 2; c = -4;"),
            Ground(
                "int a, b; if (1 <= 2 && 2 <= 1) { a = 1; } else { a = 2; } \
                 if (2 <= 1 && 1 <= 2) { b = 1; } else { b = 2; }",
            ),
            Symbolic("int a, b; a = 777; if (a <= 0) { b = 1; } else { b = a / 2; }"),
        ],
    );
    assert!(probing > 0 && probing <= pairs);
}

/// The measurement the change records (run with `--ignored --nocapture`): for each program of the
/// IMP and FUN definitions of the compile corpus, the run's work, `coverage.offer_matches`, and
/// the counters that grow with matching, with `collect_offered` on and off (both collecting
/// `applied` and `matched`). IMP is `imp-semantics`'s `imp.k` (the worktree's `imp-semantics`
/// link) on its examples, and the light corpus of the K tutorial's IMP; FUN is the reference
/// fixture `fun-int-list-config`.
#[test]
#[ignore = "a measurement, not a check; needs the imp-semantics checkout"]
fn measure_offered_cost() {
    use std::path::Path;
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let imp_directory = manifest.join("../../imp-semantics/src/kimp/kdist/imp-semantics");
    let imp_source = std::fs::read_to_string(imp_directory.join("imp.k")).unwrap();
    let compile_with_files = |source: &str, main: &str, sort: &str, program: &str| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).map(Ok).unwrap_or_else(|| {
                std::fs::read_to_string(imp_directory.join(required))
                    .map_err(|error| format!("{required}: {error}"))
            })
        };
        let loaded = load_with_options(
            ResolvedSource::new("imp.k", source),
            main,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                ..CompilationBackend::Rust.load_options()
            },
        )
        .unwrap();
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        let frontend = loaded.into_definition();
        let grammar = ProgramGrammar::new(&frontend).unwrap();
        let mut assembler =
            ConfigurationAssembler::new(&grammar, main, main, &artifacts.configuration_variables);
        assembler.program(&Sort::new(sort), program).unwrap();
        (artifacts.definition_kore, assembler.finish().unwrap())
    };
    let mut cases = Vec::new();
    for example in [
        "sumto10.imp",
        "gcd.imp",
        "gcd-while.imp",
        "dangling-else.imp",
        "while-and-following.imp",
    ] {
        let program =
            std::fs::read_to_string(manifest.join("../../imp-semantics/examples").join(example))
                .unwrap();
        let (kore, initial) = compile_with_files(&imp_source, "IMP", "Stmt", &program);
        cases.push((
            format!("imp-semantics {example}"),
            kore,
            "IMP".to_owned(),
            initial,
        ));
    }
    for (index, program) in [
        "int n, sum; n = 3; sum = 0; while (!(n <= 0)) { sum = sum + n; n = n + -1; }",
        "int a, b, c; a = 2 + 3; b = 7 / 2; c = -4;",
        "int a, b; if (1 <= 2 && 2 <= 1) { a = 1; } else { a = 2; } \
         if (2 <= 1 && 1 <= 2) { b = 1; } else { b = 2; }",
    ]
    .into_iter()
    .enumerate()
    {
        let (kore, initial) = compile_in(IMP, "IMP", "Pgm", program);
        cases.push((
            format!("imp-lesson-4 #{index}"),
            kore,
            "IMP".to_owned(),
            initial,
        ));
    }
    let fun = std::fs::read_to_string(
        manifest.join("tests/fixtures/reference/kompile/fun-int-list-config/test.k"),
    )
    .unwrap();
    let (kore, initial) = compile_in(
        &fun,
        "FUN-INT-LIST-CONFIG",
        "KItem",
        "callFunIntListAndConfig()",
    );
    cases.push((
        "fun-int-list-config".to_owned(),
        kore,
        "FUN-INT-LIST-CONFIG".to_owned(),
        initial,
    ));

    for (name, kore, main, initial) in cases {
        for strategy in STRATEGIES {
            let mut line = format!("{name} {strategy:?}:");
            let mut sizes = Vec::new();
            for offered in [false, true] {
                let (kore, main, initial) = (kore.clone(), main.clone(), initial.clone());
                let (result, counters) = counted(move || {
                    let mut backend =
                        Backend::new(&kore, &main, BackendOptions::default()).unwrap();
                    backend
                        .execute(ExecuteRequest {
                            strategy,
                            collect_coverage: true,
                            collect_offered: offered,
                            max_work: Some(20_000),
                            ..ExecuteRequest::new(initial)
                        })
                        .unwrap()
                });
                let coverage = result.coverage.unwrap();
                sizes.push((
                    coverage.matched.len(),
                    coverage.offered.map(|list| list.len()),
                ));
                line.push_str(&format!(
                    " [offered {offered}: work {} expanded {} rule_attempts {} matching.problems {} equation_attempts {} offer_matches {}]",
                    result.work,
                    result.expanded,
                    counters.get(Counter::RewriteRuleAttempts),
                    counters.get(Counter::MatchingProblems),
                    counters.get(Counter::SimplifyEquationAttempts),
                    counters.get(Counter::CoverageOfferMatches),
                ));
            }
            eprintln!("{line} lists (matched, offered) {sizes:?}");
        }
    }
}
