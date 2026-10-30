//! Run coverage through the facade: an execute request that sets `collect_coverage` receives the
//! ids of the rules and equations the run applied, and of those whose condition it began to
//! decide for a matched instance, wherever the backend applied or decided them
//! (docs/compatibility.md, "Run coverage").
//!
//! Ids are resolved through `Backend::rule_catalog` as (label, id) pairs: equal sentences share
//! an id, so a map from id to label would keep only one of them.

use std::collections::BTreeSet;

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, HaltReasonOutput,
        ObservedRequest, ResultModalityOutput, RunCoverageOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_pattern},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/shared.rs"]
mod shared;

/// The fixture definition of the `applied` and `matched` tests, also run by `offered_inertness.rs`.
const SOURCE: &str = include_str!("fixtures/coverage/cover.k");

/// The KORE of `SOURCE`, compiled once per process and inference mode for every test here.
fn definition_kore() -> std::sync::Arc<String> {
    static KORE: shared::Shared<String> = shared::Shared::new();
    KORE.get(compile)
}

fn compile() -> String {
    compile_source("cover.k", SOURCE, "COVER")
}

/// The KORE of `source`, main module `main`.
fn compile_source(file: &str, source: &str, main: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(file, source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

/// A fresh backend over the shared definition, so no test observes another's backend state.
fn backend() -> Backend {
    Backend::new(&definition_kore(), "COVER", BackendOptions::default()).unwrap()
}

fn top(program: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortProg{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

fn seq(op: &str, argument: i64) -> String {
    format!("Lblseq{{}}(Lbl{op}{{}}({}), Lblhalt{{}}())", int(argument))
}

fn request(program: &str, modality: ResultModalityOutput) -> ExecuteRequest {
    ExecuteRequest {
        result_modality: modality,
        collect_coverage: true,
        ..ExecuteRequest::new(parse_pattern(&top(program)).unwrap())
    }
}

/// The (label, id) pairs of the catalog's axioms that have a label.
fn catalog(backend: &Backend) -> Vec<(String, String)> {
    backend
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .filter_map(|rule| rule.label.map(|label| (label, rule.id)))
        .collect()
}

/// What `ids` names: the label, without its module, of each `COVER` sentence with an id in
/// `ids`, and every other id as `other:<id>`, so that an exact comparison also catches an id the
/// run should not have recorded.
fn labels(catalog: &[(String, String)], ids: &[String]) -> BTreeSet<String> {
    labels_in("COVER.", catalog, ids)
}

/// [`labels`] for the sentences of the module whose labels start with `module`.
fn labels_in(module: &str, catalog: &[(String, String)], ids: &[String]) -> BTreeSet<String> {
    ids.iter()
        .flat_map(|id| {
            let cover = catalog
                .iter()
                .filter(|(label, other)| other == id && label.starts_with(module))
                .map(|(label, _)| label.trim_start_matches(module).to_owned())
                .collect::<Vec<_>>();
            if cover.is_empty() {
                vec![format!("other:{id}")]
            } else {
                cover
            }
        })
        .collect()
}

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|name| (*name).to_owned()).collect()
}

/// The `COVER` labels of a run's (applied, matched) sets.
fn covered(
    catalog: &[(String, String)],
    result: &ExecutionResult,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let coverage = result
        .coverage
        .as_ref()
        .expect("the request asked for coverage");
    (
        labels(catalog, &coverage.applied),
        labels(catalog, &coverage.matched),
    )
}

fn run(backend: &mut Backend, program: &str, modality: ResultModalityOutput) -> ExecutionResult {
    backend.execute(request(program, modality)).unwrap()
}

/// (1) The requires-equation reproducer: the rule and the equation its `requires` used are
/// applied, and no equation the run never evaluated is in either set.
#[test]
fn an_equation_used_in_a_rule_requires_is_applied() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let program = format!(
        "Lblseq{{}}(Lblload{{}}(Lbladdr{{}}({}), {}), Lblhalt{{}}())",
        int(1),
        int(0)
    );
    let result = run(&mut backend, &program, ResultModalityOutput::PathSet);
    let (applied, matched) = covered(&catalog, &result);
    assert_eq!(applied, names(&["load", "norm"]));
    assert_eq!(matched, names(&["load", "norm"]));
}

/// A program `seq(op(argument), halt)`, the sentences applied, those matched only, and the
/// halt reason of its one leaf when the case pins it.
type Case<'a> = (
    &'a str,
    i64,
    &'a [&'a str],
    &'a [&'a str],
    Option<HaltReasonOutput>,
);

/// (2) Where the backend applied or decided each sentence: a rule's `ensures`, a partial
/// right-hand side, another equation's `requires`, a refuted higher-priority rule, a refuted
/// `owise` competitor, an unconditional ceil equation deciding definedness, a ceil equation
/// that discharged a rule at load, and an equation step deciding the definedness of an operand
/// `#if` does not evaluate.
#[test]
fn every_place_an_equation_is_used_is_covered() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let cases: [Case; 9] = [
        ("ens", 1, &["ens", "normE"], &[], None),
        ("rhsp", 1, &["rhsp", "part"], &[], None),
        ("eqreq", 1, &["eqreq", "outer", "inner"], &[], None),
        ("rej", 5, &["rej", "normR"], &["rejHigh"], None),
        ("ow", 5, &["ow", "owf2", "owg"], &["owf1"], None),
        (
            "ru",
            1,
            &["ru", "puCeil"],
            &[],
            Some(HaltReasonOutput::Stuck),
        ),
        (
            "ru",
            -1,
            &["ru", "puCeil"],
            &[],
            Some(HaltReasonOutput::Trivial),
        ),
        (
            "rv",
            -1,
            &["rv", "pvCeil"],
            &[],
            Some(HaltReasonOutput::Stuck),
        ),
        // `#if` does not evaluate `pd(5)`; one step of `pdEq` decides that it is defined.
        ("d1", 5, &["d1", "pdEq"], &[], Some(HaltReasonOutput::Stuck)),
    ];
    for (op, argument, applied_only, matched_only, reason) in cases {
        let result = run(
            &mut backend,
            &seq(op, argument),
            ResultModalityOutput::PathSet,
        );
        if let Some(reason) = reason {
            let reasons = result
                .leaves
                .iter()
                .map(|leaf| leaf.reason)
                .collect::<Vec<_>>();
            assert_eq!(reasons, vec![reason], "{op}({argument})");
        }
        let (applied, matched) = covered(&catalog, &result);
        let expected_matched = names(applied_only)
            .union(&names(matched_only))
            .cloned()
            .collect::<BTreeSet<_>>();
        assert_eq!(applied, names(applied_only), "{op}({argument}): applied");
        assert_eq!(matched, expected_matched, "{op}({argument}): matched");
    }
}

/// (3) Collecting changes no other field of the result.
#[test]
fn collecting_coverage_changes_nothing_else() {
    let mut backend = backend();
    for program in [seq("rhsp", 1), seq("ru", -1), "Lblnd{}()".to_owned()] {
        for modality in [
            ResultModalityOutput::PathSet,
            ResultModalityOutput::StateSet,
        ] {
            let mut with = run(&mut backend, &program, modality);
            let without = backend
                .execute(ExecuteRequest {
                    collect_coverage: false,
                    ..request(&program, modality)
                })
                .unwrap();
            assert!(without.coverage.is_none());
            assert!(with.coverage.take().is_some());
            assert_eq!(
                serde_json::to_value(&with).unwrap(),
                serde_json::to_value(&without).unwrap(),
                "{program} {modality:?}"
            );
        }
    }
}

/// (4) The sets cover the paths whose leaves a state-set result merges away, so both
/// modalities give the same sets; a lower-priority rule whose group the step never reaches is
/// in neither set (the documented limit).
#[test]
fn the_sets_are_those_of_the_explored_tree_under_either_modality() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let state_set = run(&mut backend, "Lblnd{}()", ResultModalityOutput::StateSet);
    let path_set = run(&mut backend, "Lblnd{}()", ResultModalityOutput::PathSet);
    assert_eq!(state_set.leaves.len(), 1);
    assert_eq!(path_set.leaves.len(), 2);
    assert_eq!(state_set.coverage, path_set.coverage);
    let every = names(&["ndA", "ndB", "mid1", "mid2"]);
    assert_eq!(covered(&catalog, &state_set), (every.clone(), every));

    let result = run(&mut backend, &seq("pr", 1), ResultModalityOutput::PathSet);
    let (applied, matched) = covered(&catalog, &result);
    assert_eq!(applied, names(&["prHigh"]));
    assert_eq!(matched, names(&["prHigh"]));
}

/// (5) The sets do not depend on observation, on earlier requests to the backend, or on a
/// module being built by the request that first names it.
#[test]
fn the_sets_do_not_depend_on_observation_or_request_history() {
    let program = seq("ru", -1);
    let mut first = backend();
    let expected = run(&mut first, &program, ResultModalityOutput::PathSet).coverage;
    assert!(expected.is_some());
    let again = run(&mut first, &program, ResultModalityOutput::PathSet).coverage;
    assert_eq!(again, expected, "the same request twice on one backend");
    let fresh = run(&mut backend(), &program, ResultModalityOutput::PathSet).coverage;
    assert_eq!(fresh, expected, "a fresh backend");
    for rules in [None, Some(Vec::new())] {
        let observed = first
            .execute_observed(ObservedRequest {
                request: request(&program, ResultModalityOutput::PathSet),
                rules: rules.clone(),
            })
            .unwrap()
            .coverage;
        assert_eq!(observed, expected, "execute_observed with rules {rules:?}");
    }

    // A backend whose default module is another one builds `COVER` on the first request that
    // names it, discharging its rules' definedness then; the run's sets are the same.
    let mut lazy = Backend::new(&definition_kore(), "K", BackendOptions::default()).unwrap();
    let in_module = || ExecuteRequest {
        module_name: Some("COVER".to_owned()),
        ..request(&program, ResultModalityOutput::PathSet)
    };
    let built = lazy.execute(in_module()).unwrap().coverage;
    let reused = lazy.execute(in_module()).unwrap().coverage;
    assert_eq!(built, expected, "the request that builds the module");
    assert_eq!(reused, expected, "a later request");
    let rv = seq("rv", -1);
    let mut lazy = Backend::new(&definition_kore(), "K", BackendOptions::default()).unwrap();
    let built = lazy
        .execute(ExecuteRequest {
            module_name: Some("COVER".to_owned()),
            ..request(&rv, ResultModalityOutput::PathSet)
        })
        .unwrap()
        .coverage;
    let eager = run(&mut backend(), &rv, ResultModalityOutput::PathSet).coverage;
    assert_eq!(
        built, eager,
        "a load-time discharge is the same whichever request built it"
    );
}

/// (6) The wire form: no `coverage` key unless asked for; `collectCoverage` is read from JSON,
/// and the result lists are sorted, also through the observed JSON entry point.
#[test]
fn the_wire_form_reports_coverage_only_when_asked() {
    let mut backend = backend();
    let state = codec::to_value(&parse_pattern(&top(&seq("ens", 1))).unwrap()).unwrap();
    let parse = |text: String| serde_json::from_str::<serde_json::Value>(&text).unwrap();

    let plain =
        serde_json::from_value::<ExecuteRequest>(serde_json::json!({ "state": state })).unwrap();
    assert!(!plain.collect_coverage);
    let output = parse(backend.execute_json(plain).unwrap());
    assert!(output.get("coverage").is_none(), "{output}");

    let asking = || {
        serde_json::from_value::<ExecuteRequest>(serde_json::json!({
            "state": state,
            "collectCoverage": true,
        }))
        .unwrap()
    };
    let output = parse(backend.execute_json(asking()).unwrap());
    let coverage = serde_json::from_value::<RunCoverageOutput>(output["coverage"].clone()).unwrap();
    assert!(!coverage.applied.is_empty());
    assert!(coverage.applied.is_sorted() && coverage.matched.is_sorted());
    let observed = parse(
        backend
            .execute_observed_json(ObservedRequest {
                request: asking(),
                rules: None,
            })
            .unwrap(),
    );
    assert_eq!(observed["coverage"], output["coverage"]);
}

/// (7) A builtin hook evaluated in a right-hand side is not a sentence and is never recorded.
#[test]
fn a_hook_is_never_recorded() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let result = run(&mut backend, &seq("hk", 1), ResultModalityOutput::PathSet);
    assert!(
        result.leaves[0]
            .trace
            .iter()
            .any(|entry| entry.unique_id.starts_with("builtin:")),
        "the hook is evaluated on the path"
    );
    let coverage = result.coverage.as_ref().unwrap();
    assert!(
        coverage
            .applied
            .iter()
            .chain(&coverage.matched)
            .all(|id| !id.starts_with("builtin:")),
        "{coverage:?}"
    );
    assert_eq!(covered(&catalog, &result).0, names(&["hk"]));
}

/// The offered level (docs/compatibility.md, "Run coverage"): a request that sets
/// `collect_offered` beside `collect_coverage` also receives `offered`, the axioms whose
/// left-hand side matched a subject the backend scanned candidates for and which the scan never
/// tried, besides `matched`.
mod offered {
    use std::collections::BTreeSet;

    use k_rust::{
        backend::{
            Backend, BackendOptions, ExecuteRequest, ExecutionResult, ExecutionStrategy,
            ObservedRequest, ResultModalityOutput,
        },
        kore::{codec, parser::parse_pattern},
    };

    use super::{int, shared, top};

    /// Each `pX` operation exercises one recording site; `seq(op, P)` is the program shape of
    /// the `COVER` definition.
    const SOURCE: &str = include_str!("fixtures/coverage/offer.k");

    fn definition_kore() -> std::sync::Arc<String> {
        static KORE: shared::Shared<String> = shared::Shared::new();
        KORE.get(|| super::compile_source("offer.k", SOURCE, "OFFER"))
    }

    fn backend() -> Backend {
        Backend::new(&definition_kore(), "OFFER", BackendOptions::default()).unwrap()
    }

    fn catalog(backend: &Backend) -> Vec<(String, String)> {
        super::catalog(backend)
    }

    /// `seq(op(argument), halt)`, `argument` a literal or, for `None`, the variable `X`.
    fn program(op: &str, argument: Option<i64>) -> String {
        let argument = argument.map_or_else(|| "VarX:SortInt{}".to_owned(), int);
        format!("Lblseq{{}}(Lbl{op}{{}}({argument}), Lblhalt{{}}())")
    }

    fn request(
        program: &str,
        strategy: ExecutionStrategy,
        modality: ResultModalityOutput,
        offered: bool,
    ) -> ExecuteRequest {
        ExecuteRequest {
            result_modality: modality,
            strategy,
            collect_coverage: true,
            collect_offered: offered,
            ..ExecuteRequest::new(parse_pattern(&top(program)).unwrap())
        }
    }

    /// The `OFFER` labels of a run's (applied, matched, offered) lists.
    type Levels = (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>);

    fn levels(catalog: &[(String, String)], result: &ExecutionResult) -> Levels {
        let coverage = result.coverage.as_ref().expect("coverage was asked for");
        let offered = coverage.offered.as_ref().expect("offered was asked for");
        let labels = |ids: &[String]| super::labels_in("OFFER.", catalog, ids);
        (
            labels(&coverage.applied),
            labels(&coverage.matched),
            labels(offered),
        )
    }

    fn run(
        backend: &mut Backend,
        program: &str,
        strategy: ExecutionStrategy,
        modality: ResultModalityOutput,
    ) -> ExecutionResult {
        backend
            .execute(request(program, strategy, modality, true))
            .unwrap()
    }

    fn names(list: &[&str]) -> BTreeSet<String> {
        super::names(list)
    }

    /// Every program of the fixtures, with the strategies it runs under.
    fn fixtures() -> Vec<(String, ExecutionStrategy)> {
        let mut programs = Vec::new();
        for (op, argument) in [
            ("pa", Some(1)),
            ("pb", Some(1)),
            ("pc", Some(5)),
            ("pd", Some(0)),
            ("pd", Some(5)),
            ("pe", None),
            ("pe", Some(3)),
            ("py", Some(1)),
            ("ph", Some(1)),
            ("pk", Some(5)),
        ] {
            for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
                programs.push((program(op, argument), strategy));
            }
        }
        programs
    }

    /// (a) A rule of a priority group below the productive one, whose left-hand side matches the
    /// state, is offered and not matched; under either strategy.
    #[test]
    fn a_lower_priority_rule_that_matches_is_offered() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
            let result = run(
                &mut backend,
                &program("pa", Some(1)),
                strategy,
                ResultModalityOutput::PathSet,
            );
            assert_eq!(
                levels(&catalog, &result),
                (
                    names(&["aHigh"]),
                    names(&["aHigh"]),
                    names(&["aHigh", "aLow"])
                ),
                "{strategy:?}"
            );
        }
    }

    /// (b) An `owise` rule behind a productive rule of the default priority is offered only.
    #[test]
    fn an_owise_rule_behind_a_productive_rule_is_offered() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
            let result = run(
                &mut backend,
                &program("pb", Some(1)),
                strategy,
                ResultModalityOutput::PathSet,
            );
            assert_eq!(
                levels(&catalog, &result),
                (
                    names(&["bMain"]),
                    names(&["bMain"]),
                    names(&["bMain", "bOw"])
                ),
                "{strategy:?}"
            );
        }
    }

    /// Under strategy `any`, the rules of the productive priority after the one that took the
    /// state are offered; under `all` both apply.
    #[test]
    fn under_any_the_later_rule_of_the_productive_priority_is_offered() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        let result = run(
            &mut backend,
            &program("py", Some(1)),
            ExecutionStrategy::Any,
            ResultModalityOutput::PathSet,
        );
        let (applied, matched, offered) = levels(&catalog, &result);
        assert_eq!(applied, matched);
        assert_eq!(applied.len(), 1, "{applied:?}");
        assert_eq!(offered, names(&["yA", "yB"]));
        let result = run(
            &mut backend,
            &program("py", Some(1)),
            ExecutionStrategy::All,
            ResultModalityOutput::PathSet,
        );
        let both = names(&["yA", "yB"]);
        assert_eq!(
            levels(&catalog, &result),
            (both.clone(), both.clone(), both)
        );
    }

    /// (c) Of two equations of one group whose left-hand sides match, the one the scan tries
    /// first applies, and the other is offered and not matched.
    #[test]
    fn a_later_equation_of_the_applied_group_is_offered() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        let result = run(
            &mut backend,
            &program("pc", Some(5)),
            ExecutionStrategy::All,
            ResultModalityOutput::PathSet,
        );
        let (applied, matched, offered) = levels(&catalog, &result);
        let equations = names(&["fc1", "fc2"]);
        let used = applied
            .intersection(&equations)
            .cloned()
            .collect::<BTreeSet<_>>();
        assert_eq!(used.len(), 1, "{applied:?}");
        assert_eq!(matched, applied);
        assert_eq!(applied, &names(&["c"]) | &used);
        assert_eq!(offered, &names(&["c"]) | &equations);
    }

    /// (d) An `owise` equation behind an applied equation is offered; an equation whose
    /// left-hand side does not match the argument is not, while the `owise` one it lets apply is
    /// matched and applied.
    #[test]
    fn an_owise_equation_is_offered_behind_an_applied_one_only() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        let result = run(
            &mut backend,
            &program("pd", Some(0)),
            ExecutionStrategy::All,
            ResultModalityOutput::PathSet,
        );
        assert_eq!(
            levels(&catalog, &result),
            (
                names(&["d", "fd1"]),
                names(&["d", "fd1"]),
                names(&["d", "fd1", "fdOw"])
            )
        );
        let result = run(
            &mut backend,
            &program("pd", Some(5)),
            ExecutionStrategy::All,
            ResultModalityOutput::PathSet,
        );
        let (applied, matched, offered) = levels(&catalog, &result);
        assert_eq!(applied, names(&["d", "fdOw"]));
        assert_eq!(matched, names(&["d", "fdOw"]));
        assert_eq!(offered, names(&["d", "fdOw"]), "fd1 does not match fd(5)");
    }

    /// (e) A `concrete` equation with an empty `requires`, set aside on a symbolic argument with
    /// a lower group following, is offered and not matched; the lower group it blocks is offered
    /// too.
    #[test]
    fn a_set_aside_equation_is_offered() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        let result = run(
            &mut backend,
            &program("pe", None),
            ExecutionStrategy::All,
            ResultModalityOutput::PathSet,
        );
        assert_eq!(
            levels(&catalog, &result),
            (names(&["e"]), names(&["e"]), names(&["e", "feC", "feOw"]))
        );
    }

    /// (f) A rule whose left-hand side matches no explored state is in no list.
    #[test]
    fn a_rule_that_matches_no_explored_state_is_in_no_list() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        for (program, strategy) in fixtures() {
            for modality in [
                ResultModalityOutput::PathSet,
                ResultModalityOutput::StateSet,
            ] {
                let result = run(&mut backend, &program, strategy, modality);
                let (_, _, offered) = levels(&catalog, &result);
                assert!(!offered.contains("never"), "{program} {strategy:?}");
            }
        }
    }

    /// (g) `applied` within `matched` within `offered` on every fixture, the same lists under
    /// both result modalities, and for `execute` and `execute_observed`.
    #[test]
    fn the_levels_nest_and_do_not_depend_on_modality_or_observation() {
        let mut backend = backend();
        for (program, strategy) in fixtures() {
            let path_set = run(
                &mut backend,
                &program,
                strategy,
                ResultModalityOutput::PathSet,
            );
            let coverage = path_set.coverage.clone().unwrap();
            let offered = coverage.offered.clone().unwrap();
            let set = |ids: &[String]| ids.iter().cloned().collect::<BTreeSet<_>>();
            assert!(
                set(&coverage.applied).is_subset(&set(&coverage.matched)),
                "{program}"
            );
            assert!(
                set(&coverage.matched).is_subset(&set(&offered)),
                "{program}"
            );
            assert!(offered.is_sorted(), "{program}");
            let state_set = run(
                &mut backend,
                &program,
                strategy,
                ResultModalityOutput::StateSet,
            );
            assert_eq!(
                state_set.coverage, path_set.coverage,
                "{program} {strategy:?}"
            );
            for rules in [None, Some(Vec::new())] {
                let observed = backend
                    .execute_observed(ObservedRequest {
                        request: request(&program, strategy, ResultModalityOutput::PathSet, true),
                        rules,
                    })
                    .unwrap();
                assert_eq!(observed.coverage, path_set.coverage, "{program} observed");
            }
        }
    }

    /// (h) Asking for `offered` changes nothing but `coverage.offered`: the serialized result
    /// without it is byte for byte the result of the request without `collectOffered`, on a run
    /// that mints a fresh name, evaluates an implementation-chosen value (its mark and its
    /// diagnostic) and offers competitors at both steps; and on every other fixture.
    #[test]
    fn asking_for_offered_changes_nothing_else() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        let mut runs = fixtures();
        runs.insert(0, (program("ph", Some(1)), ExecutionStrategy::All));
        for (index, (program, strategy)) in runs.into_iter().enumerate() {
            for modality in [
                ResultModalityOutput::PathSet,
                ResultModalityOutput::StateSet,
            ] {
                let with = backend
                    .execute_json(request(&program, strategy, modality, true))
                    .unwrap();
                let without = backend
                    .execute_json(request(&program, strategy, modality, false))
                    .unwrap();
                let mut with = serde_json::from_str::<serde_json::Value>(&with).unwrap();
                let offered = with["coverage"]
                    .as_object_mut()
                    .unwrap()
                    .remove("offered")
                    .expect("offered is serialized when asked");
                assert!(offered.is_array());
                let without_value = serde_json::from_str::<serde_json::Value>(&without).unwrap();
                assert!(without_value["coverage"].get("offered").is_none());
                assert_eq!(
                    serde_json::to_string(&with).unwrap(),
                    serde_json::to_string(&without_value).unwrap(),
                    "{program} {strategy:?} {modality:?}"
                );
                if index == 0 {
                    // The premises of the fixture: a fresh name, a chosen value with its
                    // diagnostic, and competitors the scan never tried.
                    let text = with.to_string();
                    assert!(text.contains("implementation-chosen"), "{text}");
                    assert!(
                        with["implementationChosenValues"]
                            .as_array()
                            .is_some_and(|marks| !marks.is_empty()),
                        "{text}"
                    );
                    let result = backend
                        .execute(request(&program, strategy, modality, true))
                        .unwrap();
                    let (_, matched, offered) = levels(&catalog, &result);
                    let own = |labels: BTreeSet<String>| {
                        labels
                            .into_iter()
                            .filter(|label| !label.starts_with("other:"))
                            .collect::<BTreeSet<_>>()
                    };
                    assert_eq!(own(matched), names(&["hFresh", "hKeys"]));
                    assert_eq!(own(offered), names(&["hFresh", "hLow", "hKeys", "hOw"]));
                }
            }
        }
    }

    /// (i) `collectOffered` without `collectCoverage` is a request error, and the request
    /// refuses unknown fields, so a server that does not know `collectOffered` refuses it.
    #[test]
    fn offered_needs_coverage_and_is_read_from_the_wire() {
        let mut backend = backend();
        let state =
            codec::to_value(&parse_pattern(&top(&program("pa", Some(1)))).unwrap()).unwrap();
        let alone = serde_json::from_value::<ExecuteRequest>(serde_json::json!({
            "state": state,
            "collectOffered": true,
        }))
        .unwrap();
        assert!(alone.collect_offered && !alone.collect_coverage);
        let error = backend.execute(alone).unwrap_err();
        assert!(
            error.message().contains("collectOffered")
                && error.message().contains("collectCoverage"),
            "{}",
            error.message()
        );
        let unknown = serde_json::from_value::<ExecuteRequest>(serde_json::json!({
            "state": state,
            "collectCoverage": true,
            "collectOfferedLater": true,
        }));
        assert!(unknown.is_err(), "an unknown request field is refused");
        let plain = serde_json::from_value::<ExecuteRequest>(serde_json::json!({
            "state": state,
            "collectCoverage": true,
        }))
        .unwrap();
        assert!(!plain.collect_offered);
        let output: serde_json::Value =
            serde_json::from_str(&backend.execute_json(plain).unwrap()).unwrap();
        assert!(output["coverage"].get("offered").is_none(), "{output}");
        assert!(backend.capabilities().coverage_offered);
        let capabilities = serde_json::to_value(backend.capabilities()).unwrap();
        assert_eq!(capabilities["coverageOffered"], true);
    }

    /// (k) An equation the definedness decision of an unevaluated operand never tries, below the
    /// group it selected from, is offered and in neither other list.
    #[test]
    fn a_lower_equation_of_a_deferred_definedness_decision_is_offered() {
        let mut backend = backend();
        let catalog = catalog(&backend);
        let result = run(
            &mut backend,
            &program("pk", Some(5)),
            ExecutionStrategy::All,
            ResultModalityOutput::PathSet,
        );
        let (applied, matched, offered) = levels(&catalog, &result);
        assert_eq!(applied, names(&["k", "pdk50"]));
        assert_eq!(matched, names(&["k", "pdk50"]));
        assert_eq!(offered, names(&["k", "pdk50", "pdk60"]));
    }
}

/// The equation selection sites outside the term scans (`fixtures/coverage/probes/`): each one
/// offers the lower-priority equation it selected and never tried, which is in neither other
/// list. Each probe is a definition of its own, so that one the compiler refuses does not hide
/// the others.
mod probes {
    use std::collections::BTreeSet;

    use k_rust::{
        backend::{
            Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ResultModalityOutput,
        },
        kore::parser::parse_pattern,
    };

    use super::int;

    const CEIL: &str = include_str!("fixtures/coverage/probes/ceil.k");
    const PRED: &str = include_str!("fixtures/coverage/probes/pred.k");
    const DEF: &str = include_str!("fixtures/coverage/probes/def.k");
    /// A KORE definition: its `#Top` lemmas and its states are not written in K source.
    const TOP: &str = include_str!("fixtures/coverage/probes/top.kore");

    fn top(program: &str) -> String {
        format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
        )
    }

    /// The labels, without the module, of the (applied, matched, offered) lists of the run of
    /// `initial` over the KORE definition `kore` with main module `main`, under both strategies,
    /// which must agree.
    fn levels(
        kore: &str,
        main: &str,
        initial: &str,
    ) -> (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>) {
        let mut backend = Backend::new(kore, main, BackendOptions::default()).unwrap();
        let catalog = super::catalog(&backend);
        let module = format!("{main}.");
        let mut answers = [ExecutionStrategy::All, ExecutionStrategy::Any].map(|strategy| {
            let result = backend
                .execute(ExecuteRequest {
                    result_modality: ResultModalityOutput::PathSet,
                    strategy,
                    collect_coverage: true,
                    collect_offered: true,
                    max_work: Some(50),
                    ..ExecuteRequest::new(parse_pattern(initial).unwrap())
                })
                .unwrap();
            let coverage = result.coverage.unwrap();
            let labels = |ids: &[String]| {
                super::labels_in(&module, &catalog, ids)
                    .into_iter()
                    .filter(|label| !label.starts_with("other:"))
                    .collect::<BTreeSet<_>>()
            };
            (
                labels(&coverage.applied),
                labels(&coverage.matched),
                labels(&coverage.offered.unwrap()),
            )
        });
        assert_eq!(answers[0], answers[1], "{main} {initial}: All and Any");
        std::mem::take(&mut answers[0])
    }

    /// [`levels`] of `program`, a term of sort `Pgm`, over the K definition `source`.
    fn program_levels(
        source: &str,
        main: &str,
        program: &str,
    ) -> (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>) {
        let kore = super::compile_source(&format!("{}.k", main.to_lowercase()), source, main);
        levels(&kore, main, &top(program))
    }

    fn go(argument: &str) -> String {
        format!("Lblgo{{}}({argument})")
    }

    /// The predicate simplifier's ceil scan of `#Ceil(g(5))` applies `gTop` and never tries
    /// `gBottom`, at priority 60.
    #[test]
    fn the_ceil_scan_offers_its_lower_equation() {
        let (applied, matched, offered) = program_levels(CEIL, "CEIL", &go(&int(5)));
        assert!(
            applied.contains("gTop") && applied.contains("go"),
            "{applied:?}"
        );
        assert!(!matched.contains("gBottom"), "{matched:?}");
        assert!(offered.contains("gBottom"), "{offered:?}");
    }

    /// The predicate scan of `{h(5) #Equals 0}` applies `hTop` and never tries `hBottom`, at
    /// priority 60.
    #[test]
    fn the_predicate_scan_offers_its_lower_equation() {
        let (applied, matched, offered) = program_levels(PRED, "PRED", &go(&int(5)));
        assert!(
            applied.contains("hTop") && applied.contains("go"),
            "{applied:?}"
        );
        assert!(!matched.contains("hBottom"), "{matched:?}");
        assert!(offered.contains("hBottom"), "{offered:?}");
    }

    /// The `#Top` lemmas of the operand `tp(5)` of the term-level conjunction `5 #And tp(5)` in
    /// the state `done(5 #And tp(5))` of the KORE definition `TOP`: `tpHigh` drops it, and
    /// `tpLow`, at priority 60, is never tried.
    #[test]
    fn the_top_lemmas_offer_their_lower_lemma() {
        let (applied, matched, offered) = levels(
            TOP,
            "TOP",
            &format!(
                "Lbldone{{}}(\\and{{SortInt{{}}}}({}, Lbltp{{}}({})))",
                int(5),
                int(5)
            ),
        );
        assert!(applied.contains("tpHigh"), "{applied:?}");
        assert!(!matched.contains("tpLow"), "{matched:?}");
        assert!(offered.contains("tpLow"), "{offered:?}");
    }

    /// The definedness of the right-hand side `done(t(X))` takes the condition of `tCeil` and
    /// never tries `tBottom`, at priority 60.
    #[test]
    fn the_definedness_analysis_offers_its_lower_ceil_equation() {
        let (applied, matched, offered) = program_levels(DEF, "DEF", "Lbldef{}(VarX:SortInt{})");
        assert!(
            applied.contains("tCeil") && applied.contains("def"),
            "{applied:?}"
        );
        assert!(!matched.contains("tBottom"), "{matched:?}");
        assert!(offered.contains("tBottom"), "{offered:?}");
    }
}

/// The applied counts (`collect_counts`): how many times a run applied each rule and equation
/// of `applied`. The sets cannot tell a loop that ran three times from one that ran five; the
/// counts can.
mod counts {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    /// A loop that applies `step` once per unit of its argument, evaluating the function `dec`
    /// in each step's right-hand side, and `done` once at the end.
    const COUNT: &str = r"
module COUNT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= loop(Int)  [symbol(loop)]
endmodule

module COUNT
  imports COUNT-SYNTAX
  imports INT
  imports BOOL

  syntax Int ::= dec(Int)  [function, total, symbol(dec)]
  rule [dec]: dec(N) => N -Int 1

  configuration <k> $PGM:Pgm </k> <total> 0 </total>

  rule [step]: <k> loop(N) => loop(dec(N)) ... </k> <total> T => T +Int N </total>
    requires N >Int 0
  rule [done]: <k> loop(N) => .K ... </k> requires N <=Int 0
endmodule
";

    fn definition_kore() -> std::sync::Arc<String> {
        static KORE: shared::Shared<String> = shared::Shared::new();
        KORE.get(|| compile_source("count.k", COUNT, "COUNT"))
    }

    fn backend() -> Backend {
        Backend::new(&definition_kore(), "COUNT", BackendOptions::default()).unwrap()
    }

    fn state(n: i64) -> String {
        format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}(Lblloop{{}}({})), dotk{{}}())), Lbl'-LT-'total'-GT-'{{}}({}), Lbl'-LT-'generatedCounter'-GT-'{{}}({}))",
            int(n),
            int(0),
            int(0)
        )
    }

    fn counting(n: i64) -> ExecuteRequest {
        ExecuteRequest {
            result_modality: ResultModalityOutput::PathSet,
            collect_coverage: true,
            collect_counts: true,
            ..ExecuteRequest::new(parse_pattern(&state(n)).unwrap())
        }
    }

    /// The `COUNT` labels of a run's applied counts, and of its `applied` set.
    fn counted(
        backend: &Backend,
        result: &ExecutionResult,
    ) -> (BTreeMap<String, u64>, BTreeSet<String>) {
        let catalog = catalog(backend);
        let coverage = result
            .coverage
            .as_ref()
            .expect("the request asked for coverage");
        let counts = coverage
            .applied_counts
            .as_ref()
            .expect("the request asked for counts");
        let by_label = counts
            .iter()
            .flat_map(|(id, count)| {
                labels_in("COUNT.", &catalog, std::slice::from_ref(id))
                    .into_iter()
                    .map(move |label| (label, *count))
            })
            .collect();
        (by_label, labels_in("COUNT.", &catalog, &coverage.applied))
    }

    /// A loop of five applies `step` five times and `dec` in each of its right-hand sides, and
    /// `done` once; a loop of three has the same `applied` set and smaller counts. The keys of
    /// the counts are `applied`, every count at least 1.
    #[test]
    fn a_loop_counts_each_application_where_the_set_does_not_change() {
        let mut backend = backend();
        let five = backend.execute(counting(5)).unwrap();
        let three = backend.execute(counting(3)).unwrap();
        let (five_counts, five_applied) = counted(&backend, &five);
        let (three_counts, three_applied) = counted(&backend, &three);
        assert_eq!(five_applied, three_applied);
        assert_eq!(
            five_counts.keys().cloned().collect::<BTreeSet<_>>(),
            five_applied
        );
        for (label, count) in [("step", 5), ("dec", 5), ("done", 1)] {
            assert_eq!(
                five_counts.get(label),
                Some(&count),
                "{label}: {five_counts:?}"
            );
        }
        for (label, count) in [("step", 3), ("dec", 3), ("done", 1)] {
            assert_eq!(
                three_counts.get(label),
                Some(&count),
                "{label}: {three_counts:?}"
            );
        }
        let coverage = five.coverage.as_ref().unwrap();
        let counts = coverage.applied_counts.as_ref().unwrap();
        assert_eq!(
            counts.keys().cloned().collect::<Vec<_>>(),
            coverage.applied,
            "every applied id, and only those, is counted"
        );
        assert!(counts.values().all(|count| *count >= 1));
    }

    /// The counts are a function of the request: the same on a fresh backend, after other
    /// requests, and through `execute_observed`.
    #[test]
    fn the_counts_do_not_depend_on_request_history() {
        let expected = backend().execute(counting(5)).unwrap().coverage;
        let mut used = backend();
        used.execute(counting(3)).unwrap();
        used.execute(counting(7)).unwrap();
        assert_eq!(used.execute(counting(5)).unwrap().coverage, expected);
        let observed = used
            .execute_observed(ObservedRequest {
                request: counting(5),
                rules: None,
            })
            .unwrap()
            .coverage;
        assert_eq!(observed, expected);
    }

    /// Asking for counts changes nothing else in the result; the wire form has `appliedCounts`
    /// only when asked, and `collectCounts` without `collectCoverage` is refused.
    #[test]
    fn asking_for_counts_changes_nothing_else_and_the_wire_form_has_them_only_when_asked() {
        let mut backend = backend();
        let mut counted = backend.execute(counting(4)).unwrap();
        let plain = backend
            .execute(ExecuteRequest {
                collect_counts: false,
                ..counting(4)
            })
            .unwrap();
        let counts = counted.coverage.as_mut().unwrap().applied_counts.take();
        assert!(counts.is_some());
        assert_eq!(plain.coverage.as_ref().unwrap().applied_counts, None);
        assert_eq!(
            serde_json::to_value(&counted).unwrap(),
            serde_json::to_value(&plain).unwrap()
        );

        let state = codec::to_value(&parse_pattern(&state(2)).unwrap()).unwrap();
        let parse = |text: String| serde_json::from_str::<serde_json::Value>(&text).unwrap();
        let request = |fields: serde_json::Value| {
            let mut request = serde_json::json!({ "state": state });
            request
                .as_object_mut()
                .unwrap()
                .extend(fields.as_object().unwrap().clone());
            serde_json::from_value::<ExecuteRequest>(request).unwrap()
        };
        let without = parse(
            backend
                .execute_json(request(serde_json::json!({ "collectCoverage": true })))
                .unwrap(),
        );
        assert!(
            without["coverage"].get("appliedCounts").is_none(),
            "{without}"
        );
        let with = parse(
            backend
                .execute_json(request(
                    serde_json::json!({ "collectCoverage": true, "collectCounts": true }),
                ))
                .unwrap(),
        );
        let counts = with["coverage"]["appliedCounts"]
            .as_object()
            .expect("an object of counts");
        assert_eq!(
            counts.keys().cloned().collect::<Vec<_>>(),
            serde_json::from_value::<Vec<String>>(with["coverage"]["applied"].clone()).unwrap()
        );
        let refused = backend
            .execute_json(request(serde_json::json!({ "collectCounts": true })))
            .unwrap_err();
        assert!(
            refused
                .to_string()
                .contains("collectCounts requires collectCoverage"),
            "{refused}"
        );
    }
}

/// Discarded operands whose evaluation does not end (`k_rust_backend::deferred`): the equation of
/// `loopi()` is never applied, wherever the definedness of the operand a conditional discards is
/// decided, in the simplifier or in preparing a solver query that reads it (its domain reading,
/// `docs/compatibility.md`). No bounded step that decides a deferred atom applies it either: its
/// right-hand side is an application of `loopi` again, which decides nothing. A count above zero
/// is the start of the evaluation that does not end, cut off only by a budget.
mod discarded {
    use super::*;

    const LEAK: &str = r#"
module LEAK
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL
  syntax Exp ::= Int
               | "iteLoop" "(" ")" [symbol(iteLoop)]
               | "divLoop" "(" ")" [symbol(divLoop)]
               | "modLoop" "(" ")" [symbol(modLoop)]
               | "mapLoop" "(" ")" [symbol(mapLoop)]
  syntax Int ::= loopi() [function, symbol(loopi)]
  rule [loop]: loopi() => loopi() +Int 1
  configuration <k> $PGM:Exp </k>
  rule iteLoop() => #if true #then 1 #else loopi() #fi
  rule divLoop() => #if true #then 1 #else 1 /Int loopi() #fi
  rule modLoop() => #if true #then 1 #else 1 %Int loopi() #fi
  rule mapLoop() => #if true #then 1 #else size(loopi() |-> 1 2 |-> 2) #fi
endmodule
"#;

    #[test]
    fn no_equation_of_a_discarded_operand_is_applied_or_begun() {
        let kore = compile_source("leak.k", LEAK, "LEAK");
        let mut backend = Backend::new(&kore, "LEAK", BackendOptions::default()).unwrap();
        let catalog = catalog(&backend);
        let loop_id = &catalog
            .iter()
            .find(|(label, _)| label == "LEAK.loop")
            .expect("the labelled equation of loopi")
            .1;
        for program in ["iteLoop", "divLoop", "modLoop", "mapLoop"] {
            let state = format!(
                "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortExp{{}}, SortKItem{{}}}}(Lbl{program}{{}}()), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}({}))",
                int(0)
            );
            let result = backend
                .execute(ExecuteRequest {
                    collect_coverage: true,
                    collect_counts: true,
                    ..ExecuteRequest::new(parse_pattern(&state).unwrap())
                })
                .unwrap();
            let coverage = result.coverage.as_ref().expect("coverage was requested");
            let applied = coverage
                .applied_counts
                .as_ref()
                .expect("counts were requested")
                .get(loop_id)
                .copied()
                .unwrap_or(0);
            assert_eq!(applied, 0, "{program}");
        }
    }
}
