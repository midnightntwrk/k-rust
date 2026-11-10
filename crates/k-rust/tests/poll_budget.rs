//! The bound of polls of an execution (`ExecuteRequest::max_polls`, docs/compatibility.md, "Poll
//! budget") through the facade: it stops a run whose work inside one step never ends, the count
//! and the stop are the same on a fresh `Backend` and on one that served other requests first
//! (Z3's caches and its prelude's check included), and the count is the same with or without the
//! work that only describes a run (coverage, a state match, a stop condition that evaluates).

use k_rust::{
    backend::{
        Backend, BackendOptions, CancelledResultOutput, ExecuteRequest, GuardCollection,
        HaltReasonOutput, KoreExecutionResult, ObservedRequest, StateMatchRequest, StopArrival,
        StopDecision,
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

/// `grow` evaluates a function whose equation applies itself to a growing argument forever,
/// `spin` one whose equation applies itself to the same argument forever; `run` counts down
/// through a recursive function and ends; `sym` branches on a symbolic argument, which asks the
/// solver, then ends (`sym(N)` with `N > 0` goes on to `tick(3)`), and `symgrow` branches
/// likewise and then grows forever where `N > 3`; `tick` steps down to `done` by a labelled
/// rule. `spin` and `swing` apply a function to the same argument forever, directly and through
/// another function.
const POLLS: &str = r#"
module POLLS
  imports INT
  syntax Pgm ::= grow(Int) | spin(Int) | swing(Int) | run(Int) | sym(Int) | symgrow(Int)
               | tick(Int) | done(Int)
  syntax Int ::= f(Int) [function] | loop(Int) [function] | count(Int) [function]
               | ping(Int) [function] | pong(Int) [function]
  rule f(N) => f(N +Int 1)
  rule loop(X) => loop(X)
  rule ping(X) => pong(X)
  rule pong(X) => ping(X)
  rule [count-step]: count(N) => count(N -Int 1) +Int 2 requires N >Int 0
  rule [count-base]: count(N) => 0 requires N <=Int 0
  rule grow(N) => done(f(N))
  rule spin(N) => done(loop(N))
  rule swing(N) => done(ping(N))
  rule run(N) => done(count(N))
  rule [sym-up]: sym(N) => tick(3) requires N >Int 0
  rule [sym-down]: sym(N) => done(0) requires N <=Int 0
  rule symgrow(N) => grow(0) requires N >Int 3
  rule symgrow(N) => done(N) requires N <=Int 3
  rule [tick]: tick(N) => tick(N -Int 1) requires N >Int 0
  rule tick(N) => done(N) requires N <=Int 0
endmodule
"#;

struct Fixture {
    kore: String,
    /// The definition, internalized apart from any `Backend`, for a stop condition's own
    /// evaluation.
    syntax: k_rust::kore::ast::Definition,
}

impl Fixture {
    fn new() -> Self {
        let kore = compile_definition();
        let syntax = k_rust::kore::parser::parse_definition(&kore).unwrap();
        Self { kore, syntax }
    }

    fn backend(&self) -> Backend {
        Backend::new(&self.kore, "POLLS", BackendOptions::DEFAULT).unwrap()
    }
}

fn load() -> k_rust::outer::LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("test.k", POLLS),
        "POLLS",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap()
}

fn compile_definition() -> String {
    let loaded = load();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

/// The initial configuration whose `$PGM` is `program`.
fn initial(program: &str) -> Pattern {
    let loaded = load();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler = ConfigurationAssembler::new(
        &grammar,
        "POLLS",
        "POLLS",
        &artifacts.configuration_variables,
    );
    assembler.program(&Sort::new("Pgm"), program).unwrap();
    assembler.finish().unwrap()
}

/// The initial configuration of `program(7)` with the argument made the variable `N`.
fn symbolic(program: &str) -> Pattern {
    let text = Printer::compact().print_pattern(&initial(&format!("{program}(7)")));
    let literal = r#"\dv{SortInt{}}("7")"#;
    assert_eq!(text.matches(literal).count(), 1, "{text}");
    parse_pattern(&text.replace(literal, "VarN:SortInt{}")).unwrap()
}

fn request(state: &Pattern, max_polls: Option<u64>) -> ExecuteRequest {
    ExecuteRequest {
        max_polls,
        ..ExecuteRequest::new(state.clone())
    }
}

fn run(backend: &mut Backend, state: &Pattern, max_polls: Option<u64>) -> KoreExecutionResult {
    backend.execute_kore(request(state, max_polls)).unwrap()
}

fn json(result: &KoreExecutionResult) -> serde_json::Value {
    serde_json::to_value(result).unwrap()
}

/// Requests that fill a backend's history: concrete runs, and symbolic ones whose branches ask
/// Z3, which fills its caches and checks its prelude.
fn serve_others(fixture: &Fixture, backend: &mut Backend) {
    for program in ["run(12)", "tick(3)", "grow(0)"] {
        let _ = run(backend, &initial(program), Some(5_000));
    }
    for program in ["sym", "symgrow"] {
        let _ = run(backend, &symbolic(program), Some(20_000));
    }
    let _ = fixture;
}

/// A function equation that applies itself to a growing argument forever is stopped by the
/// bound, not by a clock: the run ends with one `poll-bound` leaf, `Ok` under either
/// `cancelledResult`, and the stop is at the same count, with the same result, on a fresh
/// backend and on one that served other requests, symbolic ones that asked Z3 among them; a
/// symbolic run that asks Z3 before it grows forever stops alike on a fresh backend and after the
/// same request filled the solver's caches. One that applies itself to the same argument,
/// directly or through another function, is decided without the bound, at the same count fresh
/// and reused.
#[test]
fn the_bound_stops_a_step_that_never_ends_at_the_same_count_fresh_and_reused() {
    let fixture = Fixture::new();
    let mut reused = fixture.backend();
    serve_others(&fixture, &mut reused);
    // The equation that applies itself to the same argument, directly or through another
    // function, the backend decides without the bound: the first leaves its application
    // unevaluated, the second is an evaluation cycle.
    use HaltReasonOutput::{PollBound, SimplificationError, Stuck, Trivial};
    let cases = [
        (initial("grow(0)"), 3_000, vec![PollBound]),
        (symbolic("symgrow"), 3_000, vec![PollBound]),
        (initial("spin(1)"), 3_000, vec![Trivial, Stuck]),
        (initial("swing(1)"), 3_000, vec![SimplificationError]),
    ];
    for (state, bound, reasons) in cases {
        let fresh = run(&mut fixture.backend(), &state, Some(bound));
        let leaf = fresh.leaves.iter().find(|leaf| leaf.reason == PollBound);
        assert_eq!(
            fresh
                .leaves
                .iter()
                .map(|leaf| leaf.reason)
                .collect::<Vec<_>>(),
            reasons,
            "{:#?}",
            fresh.leaves
        );
        if let Some(leaf) = leaf {
            assert_eq!(
                leaf.detail.as_deref(),
                Some(format!("the run reached its bound of {bound} polls").as_str())
            );
            assert!(fresh.polls >= bound, "{} < {bound}", fresh.polls);
        } else {
            assert!(fresh.polls < bound, "{}", fresh.polls);
        }
        assert_eq!(json(&run(&mut reused, &state, Some(bound))), json(&fresh));
        // A second time on the reused backend, after the same request filled its caches.
        assert_eq!(json(&run(&mut reused, &state, Some(bound))), json(&fresh));
        let error_shape = reused
            .execute_kore(ExecuteRequest {
                cancelled_result: CancelledResultOutput::Error,
                ..request(&state, Some(bound))
            })
            .unwrap();
        assert_eq!(json(&error_shape), json(&fresh));
    }
}

/// A run that ends reports its count, the same fresh and reused, and the bound changes nothing
/// at the count (only the poll past it is refused) and stops it one poll short of it.
#[test]
fn a_terminating_run_counts_the_same_polls_fresh_and_reused_and_its_count_is_its_bound() {
    let fixture = Fixture::new();
    let mut reused = fixture.backend();
    serve_others(&fixture, &mut reused);
    for state in [initial("run(30)"), symbolic("sym"), symbolic("symgrow")] {
        let state = if state == symbolic("symgrow") {
            // Constrained to the branch that ends.
            let text = Printer::compact().print_pattern(&state);
            parse_pattern(&text.replace("VarN:SortInt{}", r#"\dv{SortInt{}}("2")"#)).unwrap()
        } else {
            state
        };
        let fresh = run(&mut fixture.backend(), &state, None);
        assert!(fresh.polls > 0);
        assert!(
            fresh
                .leaves
                .iter()
                .all(|leaf| leaf.reason != HaltReasonOutput::PollBound)
        );
        assert_eq!(json(&run(&mut reused, &state, None)), json(&fresh));
        assert_eq!(json(&run(&mut reused, &state, None)), json(&fresh));
        let at_count = run(&mut fixture.backend(), &state, Some(fresh.polls));
        assert_eq!(json(&at_count), json(&fresh));
        // A bound below the count stops the run at a later poll (the count may end on a charged
        // walk after the run's last poll, which no poll follows).
        let short = run(&mut fixture.backend(), &state, Some(fresh.polls / 2));
        assert_eq!(
            short.leaves.last().unwrap().reason,
            HaltReasonOutput::PollBound
        );
    }
}

/// The work that only describes a run is off its count: coverage (with its offered level, its
/// counts and its guard outcomes), a state match, and an in-process stop condition that runs a
/// long evaluation of its own at every arrival leave the run's count as it is without them, as
/// they leave its leaves.
#[test]
fn a_run_counts_the_same_polls_with_or_without_the_work_that_describes_it() {
    let fixture = Fixture::new();
    for state in [initial("run(30)"), initial("tick(4)"), symbolic("sym")] {
        let plain = run(&mut fixture.backend(), &state, None);
        let covered = fixture
            .backend()
            .execute_kore(ExecuteRequest {
                collect_coverage: true,
                collect_offered: true,
                collect_counts: true,
                collect_guards: Some(GuardCollection::new([
                    "POLLS.count-step",
                    "POLLS.count-base",
                    "POLLS.sym-up",
                    "POLLS.sym-down",
                    "POLLS.tick",
                ])),
                ..request(&state, None)
            })
            .unwrap();
        assert!(covered.coverage.is_some());
        assert_eq!(covered.polls, plain.polls);
        let matched = fixture
            .backend()
            .execute_kore(ExecuteRequest {
                match_states: Some(StateMatchRequest::new(initial("done(60)"))),
                ..request(&state, None)
            })
            .unwrap();
        assert!(matched.state_matches.is_some());
        assert_eq!(matched.polls, plain.polls);
        let observed = fixture
            .backend()
            .execute_observed_kore(ObservedRequest {
                request: request(&state, None),
                rules: None,
            })
            .unwrap();
        assert_eq!(observed.polls, plain.polls);
    }
    // A stop condition asked at each step of `tick` that fails: once without work, once after a
    // long evaluation of its own, whose polls are its own.
    let definition = Backend::internalize_definition(&fixture.syntax, "POLLS").unwrap();
    let count = fixture
        .kore
        .split("symbol ")
        .find_map(|declaration| {
            declaration
                .split_once('{')
                .map(|(name, _)| name)
                .filter(|name| name.starts_with("Lblcount"))
        })
        .unwrap();
    let evaluated = parse_pattern(&format!(r#"{count}{{}}(\dv{{SortInt{{}}}}("300"))"#)).unwrap();
    let evaluated = definition
        .admit_unverified(&evaluated, &[])
        .internalize_term()
        .unwrap();
    let state = initial("tick(4)");
    let stopped = ExecuteRequest {
        cut_point_rules: vec!["POLLS.tick".into()],
        ..request(&state, None)
    };
    let mut asked = 0;
    let mut idle = |_: &StopArrival<'_>| {
        asked += 1;
        StopDecision::Fails
    };
    let idle_result = fixture
        .backend()
        .execute_kore_with_condition(stopped.clone(), &mut idle)
        .unwrap();
    assert_eq!(asked, 4, "{idle_result:#?}");
    let mut busy = |_: &StopArrival<'_>| {
        let simplified =
            k_rust_backend::simplify::simplify(&definition, &evaluated, Default::default())
                .map_err(k_rust_backend::stop::Stop::into_cause)
                .unwrap()
                .unwrap();
        assert_eq!(
            Printer::compact().print_pattern(&k_rust_backend::externalize::term(&simplified.term)),
            r#"\dv{SortInt{}}("600")"#
        );
        StopDecision::Fails
    };
    let busy_result = fixture
        .backend()
        .execute_kore_with_condition(stopped, &mut busy)
        .unwrap();
    assert_eq!(json(&busy_result), json(&idle_result));
    let unasked = run(&mut fixture.backend(), &state, None);
    assert_eq!(busy_result.polls, unasked.polls);
}

/// Without the option nothing is bounded: a run reports its count, and its result is the one a
/// bound at least its count gives.
#[test]
fn without_a_bound_a_run_is_unbounded_and_reports_its_count() {
    let fixture = Fixture::new();
    let state = initial("run(30)");
    let mut backend = fixture.backend();
    let unbounded = run(&mut backend, &state, None);
    assert_eq!(unbounded.leaves.len(), 1);
    assert_eq!(unbounded.leaves[0].reason, HaltReasonOutput::Stuck);
    let wire = json(&unbounded);
    assert_eq!(wire["polls"], unbounded.polls);
    let larger = run(&mut backend, &state, Some(unbounded.polls * 2));
    assert_eq!(json(&larger), wire);
}
