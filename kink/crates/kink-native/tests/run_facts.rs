//! Re-pin adoption A-1 (`draft/tasks/repin-58720d2e/ADOPTION.md`, sections 2.1-2.3 and 2.8): every
//! adapted run carries k-rust's run-level facts (`RunFacts`: the lists of open values read,
//! contradicted claims, allowance refusals and unsupported hooks, and the count of undecided
//! solver answers), and each non-empty list excludes the run, fail-closed, where no leaf shows
//! what the list holds. The fixtures are `testdata/k/a1/*.k`; the k-rust passages the rules rest
//! on are pinned by digest.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::{Path, PathBuf};
use std::time::Duration;

use k_rust::backend::{
    Backend, BackendDiagnosticOutput, BackendOptions, ContradictedClaimKind, ObservedInOutput,
};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_native::exclusion::{DefinitionExclusions, Exclusion};
use kink_native::execution::{
    AdaptedExecution, AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality,
    ResultRun, SolverProfile,
};
use kink_native::{NativeValidator, ValidatedDefinition};

/// `(symbol, contradicting equation, observing rule, ground, observed in)` of a record.
type Record = (
    Option<String>,
    String,
    Option<String>,
    bool,
    ObservedInOutput,
);

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The fixture `testdata/k/a1/<name>.k`, compiled, and its encoded main module (the upper-cased
/// name).
fn fixture(name: &str) -> (ValidatedDefinition, String) {
    let module = name.to_ascii_uppercase();
    let loaded = support::load_path(
        &Path::new(support::DIR).join(format!("a1/{name}.k")),
        &module,
    );
    let side = NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    (side, k_rust::kast::identifier::encode(&module))
}

fn budget() -> ExecutionBudget {
    ExecutionBudget {
        time: Duration::from_secs(60),
        max_simplification_iterations: 10_000,
        max_depth: Some(100),
        max_breadth: None,
    }
}

fn backend(side: &ValidatedDefinition, module: &str) -> Backend {
    Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .unwrap()
}

fn state(program: Pattern) -> Pattern {
    support::initial_state(program, "SortProg")
}

fn call(symbol: &str, argument: i64) -> Pattern {
    support::app(&format!("Lbl{symbol}"), vec![support::int(argument)])
}

/// One default result run (a state set, replaced by its path set where kink's exclusions read a
/// leaf's rule) of `program`.
fn run(side: &ValidatedDefinition, module: &str, program: Pattern) -> AdaptedExecution {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend(side, module), &state(program), budget())
        .unwrap()
}

/// How many of the leaf's own diagnostics are path facts: contradicted-claim records and marks.
fn path_facts(leaf: &AdaptedLeaf) -> usize {
    leaf.diagnostics
        .iter()
        .filter(|diagnostic| {
            matches!(
                diagnostic,
                BackendDiagnosticOutput::ContradictedClaim(_)
                    | BackendDiagnosticOutput::ImplementationChosenValue { .. }
            )
        })
        .count()
}

/// Whether the leaf's configuration holds the symbol `symbol`.
fn holds(leaf: &AdaptedLeaf, symbol: &str) -> bool {
    leaf.branch
        .state
        .to_string()
        .contains(&format!("\"name\":\"{symbol}\""))
}

/// Each record of the run's list, every one a `total` record.
fn records(execution: &AdaptedExecution) -> Vec<Record> {
    execution
        .facts()
        .contradicted_claims
        .iter()
        .map(|record| {
            assert_eq!(record.claim, ContradictedClaimKind::Total);
            (
                record.symbol.clone(),
                record.rule_label.clone().unwrap_or_default(),
                record.rewrite_rule_label.clone(),
                record.ground,
                record.observed_in,
            )
        })
        .collect()
}

/// The ground record of `td`'s `total`, contradicted by `tdeq` at `td(0)`.
fn td_record(module: &str, observing: Option<&str>, observed_in: ObservedInOutput) -> Record {
    (
        Some("Lbltd".to_owned()),
        format!("{module}.tdeq"),
        observing.map(|rule| format!("{module}.{rule}")),
        true,
        observed_in,
    )
}

/// The facts reach every run kink judges (ADOPTION.md A-1 deliverable 1): a result run (a state
/// set), a path-set result run, a stepped run (an observed path set) and the unobserved run of the
/// stepped request all list `sibtd`'s record on `sib(0)`, whose one leaf `done` carries none
/// (k-rust's own example, compat 1536: `sibok` covers every instance). A timed-out run has no
/// facts.
#[test]
fn every_adapted_run_carries_the_run_level_facts() {
    on_a_big_stack(|| {
        let (side, module) = fixture("a1claims");
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let initial = state(call("sib", 0));
        let expected = [td_record("A1CLAIMS", Some("sibtd"), ObservedInOutput::Run)];
        let state_set = adapter
            .execute(&mut backend(&side, &module), &initial, budget())
            .unwrap();
        assert_eq!(state_set.modality(), ResultModality::StateSet);
        let path_set = adapter
            .execute_result(
                &mut backend(&side, &module),
                &initial,
                budget(),
                ResultRun {
                    modality: ResultModality::PathSet,
                    max_work: None,
                },
            )
            .unwrap();
        let stepped = adapter
            .execute_steps(&mut backend(&side, &module), &initial, budget())
            .unwrap()
            .expect("the run is observable");
        for (name, execution) in [
            ("state set", &state_set),
            ("path set", &path_set),
            ("stepped", &stepped.adapted),
        ] {
            assert_eq!(records(execution), expected, "{name}");
            let [leaf] = execution.leaves() else {
                panic!("{name}: one leaf: {execution:?}")
            };
            assert!(holds(leaf, "Lbldone"), "{name}");
            assert_eq!(path_facts(leaf), 0, "{name}: {leaf:?}");
            assert_eq!(execution.facts().smt_unknowns, 0, "{name}");
        }
        let unobserved = adapter
            .execute_unobserved(&mut backend(&side, &module), &initial, budget())
            .unwrap();
        assert_eq!(&unobserved.facts, stepped.adapted.facts());
        let timed_out = adapter
            .execute(
                &mut backend(&side, &module),
                &initial,
                ExecutionBudget {
                    time: Duration::ZERO,
                    ..budget()
                },
            )
            .unwrap();
        assert!(timed_out.timed_out());
        assert_eq!(timed_out.facts(), &Default::default());
    });
}

/// The k-rust passages A-1's exclusions rest on (ADOPTION.md A-1 deliverable 7), by digest, at
/// `0068938b1` (`docs/compatibility.md`; re-pin P-1 of `draft/tasks/repin-0068938b`: the seven
/// passages are byte-identical to 8f8ad57c5's, and every one but 92 moved down 6 to 124 lines,
/// with round D's text and the correctness sweep's above them, so only the lines are re-pinned;
/// fz26 FZ-G7 then added 22 lines to "Run coverage", above two of them, which only moved again):
/// - 92: the run-level record keeps what the diagnostic channel drops (`allowanceRefusals`,
///   `unsupportedHooks`, of the run and of the load);
/// - 859: a result whose `allowanceRefusals` is empty is the result under every allowance of at
///   least as many bytes, so a refusal-free record may be reused on any host (decision 5 stands);
/// - 1653-1661: a record is a path fact; the load's records are on every run's list and on no
///   leaf; the list holds those of work that ended on no reported leaf; it is complete for ground
///   contradictions and says nothing about a symbolic run;
/// - 1901-1924: a mark is noted where the evaluator takes the value, kept through undone work and
///   memos; the run's list holds every mark, absorbed and vanished work included; the guarantee
///   for a run whose list is empty;
/// - 2481: a run under another allowance is outside the determinism contract when a bounded
///   `Bytes` hook may refuse;
/// - 2368-2371 (KINK-22 fact 1, "Work budget"): every leaf before the `work-bound` leaf is a leaf
///   of every run with a larger budget, at the same position, which the one-sided kill rests on;
/// - 2129-2134 (KINK-22 fact 2, "Search results"): a `state-set` result whose bound or undecided
///   leaves were all merged into an earlier stuck leaf of their configuration is complete, which
///   README route 3 rests on.
const A1_PASSAGES: [(usize, usize, &str); 7] = [
    (
        92,
        92,
        "72de04feec0bbb7c220d11713ecf4ce5c2acf01464c5a948448fdd73f7bdced8",
    ),
    (
        859,
        859,
        "8398220da3f64af5a820407732a493f31703b3c5821d1323aa8101011a864c52",
    ),
    (
        1653,
        1661,
        "61a132b02858ecd84dba10c1341bd64effab638b78bc5857102340a016d2edc0",
    ),
    (
        1901,
        1924,
        "309b843d88518f4bdec637057d724ba4726130237eedd1e63d228bba075c800c",
    ),
    (
        2481,
        2481,
        "7447a2082d4fdcd5cdfac1143465021b97160d5520cd5c10c84272a371253bc4",
    ),
    (
        2368,
        2371,
        "cdafee84ebdbccd1180f763b8b672650f6c6fa1319981c9b47b38cfcc3bdbf66",
    ),
    (
        2129,
        2134,
        "b7ea1c2b5ca5d494cd4245286fafe9a068b0ad4f9f6f18cef4a5a505cb73795e",
    ),
];

/// A re-pin that moves one of these passages fails here, and A-1's exclusions are read again
/// against the new text.
#[test]
fn the_passages_a1_rests_on_are_pinned() {
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root().join("../Cargo.toml")).unwrap()).unwrap();
    // kink is a part of k-rust's workspace (merge packet M-1): the manifest is k-rust's root one.
    let backend = root().join("..").join(
        manifest["workspace"]["dependencies"]["k-rust-backend"]["path"]
            .as_str()
            .expect("k-rust-backend is a path dependency"),
    );
    let text = std::fs::read_to_string(backend.join("../../docs/compatibility.md")).unwrap();
    let lines = text.split('\n').collect::<Vec<_>>();
    for (first, last, digest) in A1_PASSAGES {
        let passage = lines[first - 1..last].join("\n");
        assert_eq!(
            kink_patch::sha256(passage.as_bytes()).to_string(),
            digest,
            "compatibility.md {first}-{last}"
        );
    }
}

mod kink_tier {
    use super::*;

    /// ADOPTION.md section 2.2: a record on the run's list excludes the run (`contradicted-claim`)
    /// where no leaf shows it (before A-1 each of these runs was complete and compared):
    /// - `sib(0)`: a candidate a defined sibling covered (compat 1536);
    /// - `m(0)`: a state-set arrival absorbed during exploration, which rests on the record (`nfin`,
    ///   the `owise` rule `nother`'s undefined condition leaves applicable): the `fin` leaf comes from
    ///   the clean path through `p`.
    ///
    /// `r(0)` (the condition `td(0) >Int 0` read as false) is stuck with the record on its leaf, which
    /// before A-1 made the run incomplete. None of these is decision 2's leaf rule. The controls
    /// `sib(1)`, `sob(0)`, `rr(0)` and `m(1)` reach no contradiction and are not excluded.
    #[test]
    #[ignore = "kink"]
    fn a_contradicted_claim_on_the_run_list_excludes_the_run() {
        on_a_big_stack(|| {
            let (side, module) = fixture("a1claims");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert_eq!(exclusions.definition_exclusion(), None);
            for (symbol, observing, leaf_record) in [
                ("sib", "sibtd", false),
                ("m", "nother", false),
                ("r", "r", true),
            ] {
                let execution = run(&side, &module, call(symbol, 0));
                assert_eq!(execution.modality(), ResultModality::StateSet, "{symbol}");
                assert_eq!(
                    records(&execution),
                    [td_record(
                        "A1CLAIMS",
                        Some(observing),
                        ObservedInOutput::Run
                    )],
                    "{symbol}"
                );
                let [leaf] = execution.leaves() else {
                    panic!("{symbol}: one leaf: {execution:?}")
                };
                assert_eq!(leaf.halt, HaltClass::Stuck, "{symbol}");
                assert!(leaf.contradicted_total.is_none(), "{symbol}");
                assert_eq!(
                    path_facts(leaf),
                    usize::from(leaf_record),
                    "{symbol}: {leaf:?}"
                );
                assert!(!exclusions.contradiction_on_a_leaf(&execution), "{symbol}");
                assert_eq!(
                    exclusions.run_exclusion(&execution),
                    Some(Exclusion::ContradictedClaim),
                    "{symbol}"
                );
            }
            for (symbol, argument) in [("sib", 1), ("sob", 0), ("rr", 0), ("m", 1)] {
                let execution = run(&side, &module, call(symbol, argument));
                assert!(execution.facts().contradicted_claims.is_empty(), "{symbol}");
                assert_eq!(exclusions.run_exclusion(&execution), None, "{symbol}");
            }
        });
    }

    /// Decision D-6: a contradicted claim the load observed (`observedIn: load`; the load-time
    /// critical-pair check of `g`'s `anywhere` equations simplifies `ga`'s condition through `td(0)`)
    /// is on every run's list and on no leaf, so it excludes every test of the definition.
    #[test]
    #[ignore = "kink"]
    fn a_load_record_is_on_every_run_list_and_excludes_it() {
        on_a_big_stack(|| {
            let (side, module) = fixture("loadrec");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert_eq!(exclusions.definition_exclusion(), None);
            for argument in [1, 5] {
                let execution = run(&side, &module, call("go", argument));
                assert_eq!(
                    records(&execution),
                    [td_record("LOADREC", None, ObservedInOutput::Load)],
                    "{argument}"
                );
                assert_eq!(execution.facts().load_records().count(), 1);
                let [leaf] = execution.leaves() else {
                    panic!("one leaf: {execution:?}")
                };
                assert_eq!(path_facts(leaf), 0);
                assert!(!exclusions.contradiction_on_a_leaf(&execution));
                assert_eq!(
                    exclusions.run_exclusion(&execution),
                    Some(Exclusion::ContradictedClaim)
                );
            }
        });
    }

    /// A state set replaced by its path set (`tv(0)`: an undefined step naming the contradicted
    /// `total`, a `Trivial` leaf) keeps the facts: the record is on the replacement's list, and the
    /// leaf's contradiction is decision 2's leaf rule, the per-test case of admission.
    #[test]
    #[ignore = "kink"]
    fn a_replaced_state_set_keeps_its_facts() {
        on_a_big_stack(|| {
            let (side, module) = fixture("a1claims");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let execution = run(&side, &module, call("tv", 0));
            assert_eq!(execution.modality(), ResultModality::PathSet);
            assert_eq!(
                records(&execution),
                [td_record("A1CLAIMS", Some("tv"), ObservedInOutput::Run)]
            );
            let [leaf] = execution.leaves() else {
                panic!("one leaf: {execution:?}")
            };
            assert_eq!(leaf.halt, HaltClass::Trivial);
            assert!(leaf.contradicted_total.is_some());
            assert!(exclusions.contradiction_on_a_leaf(&execution));
            assert_eq!(
                exclusions.run_exclusion(&execution),
                Some(Exclusion::ContradictedClaim)
            );
        });
    }

    /// Re-pin adoption A-1b (review A-1-review-1 finding 6): the replacement keeps a fact only the
    /// state set it replaces reached. Under a work budget of 13 states (`testdata/k/a1/replace.k`,
    /// `s(0)`), the state set merges the diamond's second arrival at `c`, completes (the `Trivial`
    /// leaf `val(10 /Int 0)` and the stuck `done`) and lists `ytd`'s record; the path set of the same
    /// request explores the chain under `c` twice and stops at its `work-bound` leaf before it reaches
    /// `y`, so its own list is empty and alone it would be no excluded run. `execute_result` replaces
    /// the state set by that path set (the `Trivial` leaf), and the result must still list the record
    /// and so be excluded (`contradicted-claim`). Dropping the union in the replacement fails here.
    #[test]
    #[ignore = "kink"]
    fn a_replacement_keeps_a_fact_only_the_state_set_reached() {
        on_a_big_stack(|| {
            let (side, module) = fixture("replace");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert_eq!(exclusions.definition_exclusion(), None);
            let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
            let initial = state(call("s", 0));
            let bounded = |modality| ResultRun {
                modality,
                max_work: Some(13),
            };
            let expected = [td_record("REPLACE", Some("ytd"), ObservedInOutput::Run)];

            let state_set = adapter
                .execute_once(
                    &mut backend(&side, &module),
                    &initial,
                    budget(),
                    bounded(ResultModality::StateSet),
                )
                .unwrap();
            assert_eq!(state_set.modality(), ResultModality::StateSet);
            assert_eq!(records(&state_set), expected);
            let halts = state_set
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>();
            assert_eq!(
                halts,
                [HaltClass::Trivial, HaltClass::Stuck],
                "{state_set:?}"
            );

            let path_set = adapter
                .execute_once(
                    &mut backend(&side, &module),
                    &initial,
                    budget(),
                    bounded(ResultModality::PathSet),
                )
                .unwrap();
            assert_eq!(path_set.modality(), ResultModality::PathSet);
            assert!(records(&path_set).is_empty(), "{path_set:?}");
            let halts = path_set
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>();
            assert_eq!(
                halts,
                [HaltClass::Trivial, HaltClass::WorkBound],
                "{path_set:?}"
            );
            assert_eq!(exclusions.run_exclusion(&path_set), None);

            let replaced = adapter
                .execute_result(
                    &mut backend(&side, &module),
                    &initial,
                    budget(),
                    bounded(ResultModality::StateSet),
                )
                .unwrap();
            assert_eq!(replaced.modality(), ResultModality::PathSet);
            assert_eq!(replaced.leaves(), path_set.leaves());
            assert_eq!(records(&replaced), expected);
            assert_eq!(
                exclusions.run_exclusion(&replaced),
                Some(Exclusion::ContradictedClaim)
            );
        });
    }

    /// ADOPTION.md section 2.1: a value the definition leaves open is on the run's list where no leaf
    /// carries its mark: the absorbed state-set arrival of the diamond `a(1)` (only `cd` lists two
    /// keys; the `d` leaf comes from the path through `b`) and the vanished candidate `vk` of `v(1)`;
    /// and the initial state's normalization of `e(nk2(1))`, whose `nk2` equation lists two keys, is
    /// on it too (`nk1` lists one, a determined listing: no mark). Decision 1's census flags the
    /// definition (its sentences list keys) and stays the run's exclusion, `implementation-chosen-hook`,
    /// ahead of the list; with the census emptied, as re-pin adoption A-3 would leave it for k-rust's
    /// classes, the list excludes the same runs (`implementation-chosen-value`) and nothing else.
    #[test]
    #[ignore = "kink"]
    fn an_open_value_on_the_run_list_excludes_the_run_beside_the_census() {
        on_a_big_stack(|| {
            let (side, module) = fixture("marks");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert_eq!(
                exclusions.definition_exclusion(),
                Some(Exclusion::ImplementationChosenHook)
            );
            let mut without_census = exclusions.clone();
            without_census.implementation_chosen.clear();
            assert_eq!(without_census.definition_exclusion(), None);
            let nested = |function: &str| {
                support::app("Lble", vec![support::app(function, vec![support::int(1)])])
            };
            for (name, program, marked, leaf) in [
                ("diamond", call("a", 1), true, "Lbld"),
                ("vanished", call("v", 1), true, "Lbldone"),
                ("two keys", nested("Lblnk2"), true, "Lblval"),
                ("one key", nested("Lblnk1"), false, "Lblval"),
            ] {
                let execution = run(&side, &module, program);
                let listed = execution
                    .facts()
                    .implementation_chosen_values
                    .iter()
                    .map(|mark| (mark.hook.as_str(), mark.class.as_str()))
                    .collect::<Vec<_>>();
                let expected: &[(&str, &str)] = if marked {
                    &[("MAP.keys_list", "order")]
                } else {
                    &[]
                };
                assert_eq!(listed, expected, "{name}");
                let [only] = execution.leaves() else {
                    panic!("{name}: one leaf: {execution:?}")
                };
                assert!(holds(only, leaf), "{name}");
                if matches!(name, "diamond" | "vanished") {
                    assert_eq!(path_facts(only), 0, "{name}: {only:?}");
                }
                assert_eq!(
                    exclusions.run_exclusion(&execution),
                    Some(Exclusion::ImplementationChosenHook),
                    "{name}"
                );
                assert_eq!(
                    without_census.run_exclusion(&execution),
                    marked.then_some(Exclusion::ImplementationChosenValue),
                    "{name}"
                );
            }
        });
    }

    /// ADOPTION.md section 2.3: a refusal and an unsupported hook in a passed-over equation leave no
    /// diagnostic but are on the run's lists (compat 92). `run(2^40)`: the allowance refuses the
    /// padding on every host (twice a TiB exceeds any allowance), `fpad` is passed over and `fpos`
    /// gives `val(2)`: `allowance-refusal`. `runh(1)`: `countAllOccurrences("a", "")` is a value the
    /// definition does not determine, `hcount` is passed over and `hpos` gives `val(2)`:
    /// `unsupported-hook`. Neither hook is in decision 1's census. `run(1)` meets neither.
    #[test]
    #[ignore = "kink"]
    fn list_only_refusals_and_unsupported_hooks_exclude_the_run() {
        on_a_big_stack(|| {
            let (side, module) = fixture("refusals");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert_eq!(exclusions.definition_exclusion(), None);
            for (program, list, exclusion) in [
                (
                    call("run", 1 << 40),
                    "BYTES.padRight",
                    Exclusion::AllowanceRefusal,
                ),
                (
                    call("runh", 1),
                    "STRING.countAllOccurrences",
                    Exclusion::UnsupportedHook,
                ),
            ] {
                let execution = run(&side, &module, program);
                let facts = execution.facts();
                let listed = facts
                    .allowance_refusals
                    .iter()
                    .chain(&facts.unsupported_hooks)
                    .map(|entry| (entry.hook.as_str(), entry.observed_in))
                    .collect::<Vec<_>>();
                assert_eq!(listed, [(list, ObservedInOutput::Run)], "{list}");
                let [leaf] = execution.leaves() else {
                    panic!("{list}: one leaf: {execution:?}")
                };
                assert!(leaf.diagnostics.is_empty(), "{list}: {leaf:?}");
                assert!(
                    leaf.branch.state.to_string().contains(r#""value":"2""#),
                    "{list}"
                );
                assert_eq!(
                    exclusions.run_exclusion(&execution),
                    Some(exclusion),
                    "{list}"
                );
            }
            let control = run(&side, &module, call("run", 1));
            assert_eq!(control.facts(), &Default::default());
            assert_eq!(exclusions.run_exclusion(&control), None);
        });
    }
}
