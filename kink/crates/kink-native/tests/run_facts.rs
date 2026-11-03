//! Re-pin adoption A-1 (`draft/tasks/repin-58720d2e/ADOPTION.md`, sections 2.1-2.3 and 2.8): every
//! adapted run carries k-rust's run-level facts (`RunFacts`: the lists of open values read,
//! contradicted claims, allowance refusals and unsupported hooks, and the count of undecided
//! solver answers), and each non-empty list excludes the run, fail-closed, where no leaf shows
//! what the list holds. The fixtures are `testdata/k/a1/*.k`; the k-rust passages the rules rest
//! on are pinned by digest. Since CF-03 the facts also carry the `shortCircuitReadings` list as
//! the run's backend recorded it, and whether the run started from a ground state.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/passage.rs"]
mod passage;

use std::path::{Path, PathBuf};
use std::time::Duration;

use k_rust::backend::{
    Backend, BackendDiagnosticOutput, BackendOptions, ContradictedClaimKind, ObservedInOutput,
};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_native::exclusion::{
    DefinitionExclusions, Exclusion, state_references_implementation_chosen,
};
use kink_native::execution::{
    AdaptedExecution, AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality,
    ResultRun, RunFacts, SolverProfile,
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

/// One default result run (a state set) of `program`.
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
/// (k-rust's own example, compat 1544: `sibok` covers every instance). A timed-out run has no
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
/// fz26 FZ-G7 then added 22 lines to "Run coverage", above two of them, which only moved again, and
/// fz26 FZ-17 added 16 more there ("Applied counts"), which moved the same two down 16;
/// fz26 FZ-DATAEND added 6 lines to "Anywhere rules" (the data-term paragraph), above all but
/// 92 and 859, which moved those five down 6, re-pinned at the fz26 phase-5 integration by digest;
/// fz26 FZ-CONFLUENCE added 5 lines after "The contract states, and does not check" (the checked
/// hook premise), which moved the same five down 5, re-pinned by digest; the fz26 phase-6
/// integration (INT8) added FZ-EMPTYSORT's one line on sorts with no normal form to "Anywhere
/// rules", which moved the same five down 1, byte-identical, re-pinned by their text; round 3's
/// FZ-STATESET and FZ-STATESET-MATCH grew "Work budget" and the sections above the allowance
/// passage, which moved 2396-2399 down 12 and 2509 down 42, byte-identical, re-pinned by digest at
/// fz26 FZ-COMPARABLE-B's fix round, where the test was found red at main `d24fb2857`; fz26
/// FZ-FRESH added 12 lines after 1029, of which one, inside the mark passage, states where a
/// `fresh-association` mark is noted, so that passage alone is re-pinned by digest, at its own
/// lines; every other range after 1029 moved down 8 to 12 lines with the lines it named, which at
/// the branch base `16014aab4` already did not hold its pinned text, the test being red there
/// (MAIN-KINK-GATE-RED: those passages moved, byte-identical, and are not re-pinned here); its
/// fix round restated, in place, that sentence for the classification as built (an
/// association-open rule, every rule with two or more names among them, failing closed), so the
/// mark passage is re-pinned by digest again at the same lines; MAIN-KINK-GATE-RED's five moved
/// passages were re-pinned by digest before the kink hand-over (fz26 KINK-REPINS, main `602746a9d`:
/// 859 down 5, the other four down 22, byte-identical; the mark passage still at its lines)):
/// - 92: the run-level record keeps what the diagnostic channel drops (`allowanceRefusals`,
///   `unsupportedHooks`, of the run and of the load);
/// - 879: a result whose `allowanceRefusals` is empty is the result under every allowance of at
///   least as many bytes, so a refusal-free record may be reused on any host (decision 5 stands);
/// - 1710-1718: a record is a path fact; the load's records are on every run's list and on no
///   leaf; the list holds those of work that ended on no reported leaf; it is complete for ground
///   contradictions and says nothing about a symbolic run;
/// - 1961-1985: a mark is noted where the evaluator takes the value, and a `fresh-association`
///   mark where a rewrite step builds a candidate of an association-open rule (every rule with two
///   or more `!` names, and any whose compiled counter k-rust cannot read as an advance by 0 or 1:
///   fail closed, so the list only grows), kept through undone work and memos; the run's list holds every mark, absorbed and vanished work
///   included; the guarantee for a run whose list is empty (FZ-FRESH: the association of such a
///   rule's names with counter offsets is open, so a run on whose list it is not noted is the
///   same under every association, which A-1's exclusion of a non-empty list relies on);
/// - 2602: a run under another allowance is outside the determinism contract when a bounded
///   `Bytes` hook may refuse;
/// - 2459-2462 (KINK-22 fact 1, "Work budget"): every leaf before the `work-bound` leaf is a leaf
///   of every run with a larger budget, at the same position, which the one-sided kill rests on;
/// - 2190-2195 (KINK-22 fact 2, "Search results"): a `state-set` result whose bound or undecided
///   leaves were all merged into an earlier stuck leaf of their configuration is complete, which
///   README route 3 rests on.
///
/// kink27 INT1: the passages are byte-identical (same digests) and only moved, compatibility.md down 15 lines between 552 and 2367 (R1-PINS 1 line after 418, R1-BRACKET 14 lines of bracket exemption at 547-565), 17 from 2368 (R1-PINS 2 lines after 2367) and 18 after 2977 (R1-SOUND 1 line); re-pinned at their new lines.
///
/// Re-pin kink27 R2-PIN-BY-ANCHOR: each passage is located by its anchor and opening (`testdata/k/passage.rs`), not by line; every digest is unchanged, each passage found at 3ebd1f8f6 at the lines it was pinned at. Line numbers in the history above are those of the revisions it names.
///
/// GAP K1 re-pin of the mark passage (`draft/kink27/gap`, ticket K1): two sentences changed, and each only adds marks. A mark is noted where the evaluator takes the value or, for class `curve`, its `\bottom`; and the definedness check of a classified application no longer drops the mark of a `curve` or `outside-domain` application of a partial symbol, whose definedness is the pick. The list only grows, so A-1's exclusion of a run with a non-empty list excludes at least what it did, and the guarantee for a run whose list is empty (the passage's last sentence) is unchanged.
///
/// GAP K2 re-pin of the mark passage (ticket K2): only the guarantee sentence changed. The models it quantifies over no longer need to agree with k-rust's `\bottom` of a partial hook outside the inputs its description covers, which is now class `outside-domain`, taken only by an execution and marked there (the step that writes it, a condition or a discarded operand that reads its definedness, a list-update pattern whose match it refutes); they still agree with the two readings k-rust keeps (a literal's value where the literal rule leaves it open, the order of console effects of operands none of which is irrelevant). So the guarantee holds over more models, and the marks that make it hold only grow: A-1's exclusion of a run with a non-empty list excludes at least what it did, and a run whose list is empty has the same leaves in every model the guarantee named before, and in more.
///
/// GAP K2 fix round 1 re-pin of the mark passage (26 lines, one added): its first sentence now
/// names `outside-domain` beside `curve` as a class whose `\bottom` is noted, which K2's code
/// already did (`builtin::evaluate_composed` notes every classified outcome it takes, a `\bottom`
/// included), and a new sentence names the one mark site outside the evaluator K2 added, the
/// matcher's refutation of a list-update pattern (`outside-domain` on `LIST.update`, in
/// `Execution` at a partial symbol, attributed like the match it decides). Both describe marks
/// the code noted at K2's head; `BYTES.replaceAt`'s open outcomes (fix round 1) are noted at the
/// same evaluator site. So the list only grows: A-1's exclusion of a run with a non-empty list
/// excludes at least what it did, and the guarantee for a run whose list is empty is the K2
/// sentence, unchanged.
///
/// GAP integration C re-pin of the mark passage (K2 composed with K3, `draft/kink27/gap`): only
/// the guarantee sentence changed. K2 wrote it while a literal's value where the literal rules
/// leave it open was still a reading k-rust kept; K3 made that element class `literal`, which an
/// execution marks on every attempt of a rule or an equation holding such a literal and on every
/// leaf of a request holding one, and which no other route takes. So the sentence now names one
/// kept reading (the order of console effects of operands none of which is irrelevant) and says
/// that the open literal, like the outside-domain `\bottom`, is a pick an execution marks. The
/// guarantee holds over more models (they need not agree with k-rust's literal elements), and the
/// marks that make it hold only grow: A-1's exclusion of a run with a non-empty list excludes at
/// least what it did, and a run whose list is empty has the same leaves in every model the
/// guarantee named before, and in more. The digest is that of the integrated passage, the
/// composition of the K1, K2 and K3 texts.
///
/// GAP final fix round re-pin of the mark passage (text only, 483ad577 -> ed6562af): the
/// guarantee sentence names the order of console effects as k-rust's order ("not a value but an
/// order k-rust fixes"), as the rest of the document does, instead of as a reading k-rust keeps;
/// the models it quantifies over are the same (those that agree with the request's inputs and
/// with that order), and so are the marks, so A-1's exclusions read the same.
///
/// GAP A1 re-pin of the mark passage (`draft/kink27/gap`, ticket A1): two sentences changed, both
/// by dropping classes k-rust no longer has. The first now names `outside-domain` alone as the
/// class whose `\bottom` is noted (the BN128 `\bottom` of a non-point, which was `curve`, is
/// `outside-domain` now) and no longer names `read-count` in a backend execution with default
/// options; the definedness-check exception names `outside-domain` alone. The marks that go are
/// those of values that are now determined: a `#read`'s count, which is the file's and given by
/// k-rust's console contract (kink's requests have no console, so they never read one), the byte
/// conversions (one byte per code point, k-rust `docs/amendments.md` AM-1), a hex output's
/// letter case (lowercase, AM-2), a BN128 outcome on points (alt_bn128, AM-3) and `replaceAtBytes`
/// up to the end (AM-7). So a run's list loses exactly marks of values every model of the
/// definition read with those amendments gives alike, and the guarantee for a run whose list is
/// empty (the passage's last sentence, unchanged) holds over those models: A-1's exclusion of a
/// run with a non-empty list now admits runs that read only such values, which agree in every
/// such model. Whether kink adopts the amendments' models as its own is the premise this re-pin
/// rests on (GAP Phase 2's design; the kink session's to confirm).
const A1_PASSAGES: [passage::Passage; 7] = [
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "## Backend scope",
        opening: "The run-level record keeps what the diagnostic channel",
        lines: 1,
        digest: "72de04feec0bbb7c220d11713ecf4ce5c2acf01464c5a948448fdd73f7bdced8",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "## Resource bounds",
        opening: "The allowance is read once per process (`allowance.rs`",
        lines: 1,
        digest: "8398220da3f64af5a820407732a493f31703b3c5821d1323aa8101011a864c52",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "## A contradicted `total` attribute is named, not repaired",
        opening: "A record is a path fact, as an",
        lines: 9,
        digest: "61a132b02858ecd84dba10c1341bd64effab638b78bc5857102340a016d2edc0",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Marks in executions",
        opening: "A mark is noted where the evaluator takes",
        lines: 26,
        digest: "5715c6861e9feb6dde9d56d81e8d3a852a493b9b9ba900760f9e3f8ec423905b",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Execute",
        opening: "- a run compared with a run of",
        lines: 1,
        digest: "7447a2082d4fdcd5cdfac1143465021b97160d5520cd5c10c84272a371253bc4",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Work budget",
        opening: "Every leaf finished before the `work-bound` leaf is",
        lines: 4,
        digest: "cdafee84ebdbccd1180f763b8b672650f6c6fa1319981c9b47b38cfcc3bdbf66",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "## Search results",
        opening: "A leaf's halt can mean more than its",
        lines: 6,
        digest: "b7ea1c2b5ca5d494cd4245286fafe9a068b0ad4f9f6f18cef4a5a505cb73795e",
    },
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
    passage::assert_pinned(&backend.join("../.."), &A1_PASSAGES);
}

/// The k-rust passages CF-03's judgement of a run by its `shortCircuitReadings` list rests on
/// (kink-native `exclusion`, `Exclusion::ShortCircuitReading`): that the readings k-rust lists are
/// those that evaluate the deciding left operand, how an entry names the rule whose work used the
/// definedness (the per-rule clearance reads it), that a memo's reuse and a carried term are
/// attributed to the work they serve or that built them, and the guarantee of an empty list.
const CF03_PASSAGES: [passage::Passage; 4] = [
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Short-circuit readings",
        opening: "A reading that evaluates the right operand first",
        lines: 1,
        digest: "d6283bc6c04188189a1806c4c2d27217e7edd1fc0af3f151c3312d03993b2456",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Short-circuit readings",
        opening: "- `rewriteRuleId`, `rewriteRuleLabel`, `rewriteRuleOrigin`:",
        lines: 1,
        digest: "38b0d7aaf2d5490bbf25b9ceb926159311bd246a9c104c85b2cfb49d00f0bc75",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Short-circuit readings",
        opening: "An evaluation a memo serves lists its entries again",
        lines: 3,
        digest: "9e438a62173c6e27b36c358e8e86afe02a65732a5db292bc2101595293ee87d9",
    },
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "### Short-circuit readings",
        opening: "The guarantee: for a run that completes",
        lines: 1,
        digest: "8ea0b9d2fe7f0dbd7489ac0e0429b9b2794c919c9d7f9a6e76a5544833d794eb",
    },
];

/// A re-pin that moves one of these passages fails here, and CF-03's judgement is read again
/// against the new text.
#[test]
fn the_passages_the_short_circuit_judgement_rests_on_are_pinned() {
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root().join("../Cargo.toml")).unwrap()).unwrap();
    let backend = root().join("..").join(
        manifest["workspace"]["dependencies"]["k-rust-backend"]["path"]
            .as_str()
            .expect("k-rust-backend is a path dependency"),
    );
    passage::assert_pinned(&backend.join("../.."), &CF03_PASSAGES);
}

/// CF-03: every adapted run carries k-rust's `shortCircuitReadings` list, as its backend recorded
/// it: a result run, a path-set run, a stepped run and the unobserved run of the stepped request
/// of `go(0)` on `r0c/scrhs.k` each list the `undefined` reading of `10 /Int 0 >Int 0` after
/// `false andBool` under `go`, and say the run started from a ground state; from a symbolic state
/// the run is not ground. A result adapted as recorded by a backend without the capability has no
/// list, whatever its field holds, and one with it has the field's.
#[test]
fn the_run_facts_carry_the_short_circuit_readings_as_recorded() {
    use k_rust::backend::{ReadingOutcomeOutput, ResultModalityOutput, ShortCircuitReadingOutput};
    use kink_native::execution::RecordedRun;
    on_a_big_stack(|| {
        let loaded = support::load_path(&Path::new(support::DIR).join("r0c/scrhs.k"), "SCRHS");
        let side = NativeValidator::bind(loaded, CompileOptions::default())
            .compile_baseline()
            .unwrap();
        let module = k_rust::kast::identifier::encode("SCRHS");
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let initial = state(call("go", 0));
        let mut go = backend(&side, &module);
        assert!(go.capabilities().short_circuit_readings);
        assert_eq!(
            RecordedRun::of(&go, &initial),
            RecordedRun {
                short_circuit_readings: true,
                ground: true,
            }
        );
        let state_set = adapter.execute(&mut go, &initial, budget()).unwrap();
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
        let unobserved = adapter
            .execute_unobserved(&mut backend(&side, &module), &initial, budget())
            .unwrap();
        for (name, facts) in [
            ("state set", state_set.facts()),
            ("path set", path_set.facts()),
            ("stepped", stepped.adapted.facts()),
            ("unobserved", &unobserved.facts),
        ] {
            assert!(facts.ground, "{name}");
            let listed = facts.short_circuit_readings.as_ref().expect("a list");
            assert!(!listed.is_empty(), "{name}");
            for entry in listed {
                assert_eq!(
                    (
                        entry.operator.as_deref(),
                        entry.outcome,
                        entry.rewrite_rule_label.as_deref(),
                        entry.observed_in,
                    ),
                    (
                        Some("BOOL.and"),
                        ReadingOutcomeOutput::Undefined,
                        Some("SCRHS.go"),
                        ObservedInOutput::Run
                    ),
                    "{name}: {entry:?}"
                );
            }
        }
        let symbolic = adapter
            .execute(
                &mut backend(&side, &module),
                &state(support::app("Lblgo", vec![support::var("VarI", "SortInt")])),
                budget(),
            )
            .unwrap();
        assert!(!symbolic.facts().ground);
        let entry = ShortCircuitReadingOutput {
            operator: Some("BOOL.and".into()),
            outcome: ReadingOutcomeOutput::Undefined,
            head: None,
            operand: serde_json::Value::Null,
            rewrite_rule_id: None,
            rewrite_rule_label: None,
            rewrite_rule_origin: None,
            observed_in: ObservedInOutput::Run,
        };
        let result = || k_rust::backend::ExecutionResult {
            modality: ResultModalityOutput::StateSet,
            leaves: Vec::new(),
            effects: Vec::new(),
            discarded: Vec::new(),
            coverage: None,
            work: 0,
            expanded: 0,
            stack_stops: 0,
            smt_unknowns: 0,
            implementation_chosen_values: Vec::new(),
            contradicted_claims: Vec::new(),
            allowance_refusals: Vec::new(),
            unsupported_hooks: Vec::new(),
            short_circuit_readings: vec![entry.clone()],
            state_matches: None,
        };
        for (capability, expected) in [(true, Some(vec![entry.clone()])), (false, None)] {
            let adapted = ExecutionAdapter::adapt_result(
                result(),
                false,
                &budget(),
                Vec::new(),
                RecordedRun {
                    short_circuit_readings: capability,
                    ground: false,
                },
            )
            .unwrap();
            assert_eq!(adapted.facts().short_circuit_readings, expected);
            assert!(!adapted.facts().ground);
        }
    });
}

mod kink_tier {
    use super::*;

    /// ADOPTION.md section 2.2: a record on the run's list excludes the run (`contradicted-claim`)
    /// where no leaf shows it (before A-1 each of these runs was complete and compared):
    /// - `sib(0)`: a candidate a defined sibling covered (compat 1544);
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

    /// A state set with an undefined step naming the contradicted `total` (`tv(0)`, a `Trivial`
    /// leaf) stays the state set (fz26 KINK-PATHSET-FALLBACK) and keeps its own facts: the record
    /// is on its list, and the leaf's contradiction is decision 2's leaf rule, the per-test case
    /// of admission.
    #[test]
    #[ignore = "kink"]
    fn a_state_set_with_an_undefined_step_keeps_its_facts() {
        on_a_big_stack(|| {
            let (side, module) = fixture("a1claims");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            let execution = run(&side, &module, call("tv", 0));
            assert_eq!(execution.modality(), ResultModality::StateSet);
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

    /// Re-pin adoption A-1b (review A-1-review-1 finding 6), re-read for fz26
    /// KINK-PATHSET-FALLBACK: under a work budget of 13 states (`testdata/k/a1/replace.k`, `s(0)`),
    /// the state set merges the diamond's second arrival at `c`, completes (the `Trivial` leaf
    /// `val(10 /Int 0)` and the stuck `done`) and lists `ytd`'s record, so the result run is
    /// excluded (`contradicted-claim`) by its own list, with no union of two runs' facts. The path
    /// set of the same request explores the chain under `c` twice and stops at its `work-bound`
    /// leaf before it reaches `y`: its own list is empty, and alone it is no excluded run. Before
    /// the ticket the result run was that path set, with the state set's facts united into it.
    #[test]
    #[ignore = "kink"]
    fn a_work_bound_state_set_is_excluded_by_its_own_list() {
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
            let execute = |modality| {
                adapter
                    .execute_result(
                        &mut backend(&side, &module),
                        &initial,
                        budget(),
                        bounded(modality),
                    )
                    .unwrap()
            };
            let halts = |execution: &AdaptedExecution| {
                execution
                    .leaves()
                    .iter()
                    .map(|leaf| leaf.halt)
                    .collect::<Vec<_>>()
            };

            let state_set = execute(ResultModality::StateSet);
            assert_eq!(state_set.modality(), ResultModality::StateSet);
            assert_eq!(records(&state_set), expected);
            assert_eq!(
                halts(&state_set),
                [HaltClass::Trivial, HaltClass::Stuck],
                "{state_set:?}"
            );
            assert_eq!(
                exclusions.run_exclusion(&state_set),
                Some(Exclusion::ContradictedClaim)
            );

            let path_set = execute(ResultModality::PathSet);
            assert_eq!(path_set.modality(), ResultModality::PathSet);
            assert!(records(&path_set).is_empty(), "{path_set:?}");
            assert_eq!(
                halts(&path_set),
                [HaltClass::Trivial, HaltClass::WorkBound],
                "{path_set:?}"
            );
            assert_eq!(exclusions.run_exclusion(&path_set), None);
        });
    }

    /// ADOPTION.md section 2.1: a value the definition leaves open is on the run's list where no leaf
    /// carries its mark: the absorbed state-set arrival of the diamond `a(1)` (only `cd` lists two
    /// keys; the `d` leaf comes from the path through `b`) and the vanished candidate `vk` of `v(1)`;
    /// and the initial state's normalization of `e(nk2(1))`, whose `nk2` equation lists two keys, is
    /// on it too (`nk1` lists one, a determined listing: no mark). The list excludes exactly these
    /// runs (`implementation-chosen-value`). Re-pin kink27 R3-CENSUS-RUNLEVEL: k-rust's classes left
    /// decision 1's census, so the definition (whose sentences list keys) is no longer flagged and
    /// the list is each run's exclusion; before, the census excluded every run
    /// (`implementation-chosen-hook`, ahead of the list), `one key` included, and this test emptied
    /// the census by hand to read the list.
    #[test]
    #[ignore = "kink"]
    fn an_open_value_on_the_run_list_excludes_the_run() {
        on_a_big_stack(|| {
            let (side, module) = fixture("marks");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert_eq!(exclusions.definition_exclusion(), None);
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
            // A clean run lists nothing; its backend records the short-circuit readings (an empty
            // list, not no list), and the call starts from a ground state.
            let control = run(&side, &module, call("run", 1));
            assert_eq!(
                control.facts(),
                &RunFacts {
                    short_circuit_readings: Some(Vec::new()),
                    ground: true,
                    ..RunFacts::default()
                }
            );
            assert_eq!(exclusions.run_exclusion(&control), None);
        });
    }

    /// kink27 R3-CENSUS-RUNLEVEL: k-rust's classes are judged per run. k-rust takes a class value
    /// only where its evaluator classifies it and notes it on the run's `implementationChosenValues`
    /// list in an execution, wherever the run reads it (compat "Implementation-chosen hook values",
    /// pinned by `tests/exclusion.rs` `the_passages_the_census_leaves_to_the_run_list_are_pinned`),
    /// so the census reads none of them and `classes.k`, one rule per class, is not excluded as a
    /// whole. Each probe lists its class and is `implementation-chosen-value`: a rule's right-hand
    /// side (`keys`, `vals`, `s2l`, `choiceMap`, `choiceSet`, `mixed`, `mdiv`, `nan`, `mz`, `mx`,
    /// `b2s`), a literal the constant fold leaves unfolded (`lit`), a condition (`cond`), an
    /// equation (`eqn`), an equation's condition (`req`) and the initial state's normalization
    /// (`done(hex(255))`). Each control reads a determined value (one binding, one format, no NaN,
    /// no pair of signed zeros, no letter digit) and lists nothing; `req(9)` selects `isff`'s
    /// `owise` equation after a condition that read `"9"`. `rd(3)` applies `#read`, which a request
    /// without a console leaves unevaluated (`unsupported-hook`). A test's initial state that applies
    /// a class withheld outside an execution is not flagged as such
    /// (`state_references_implementation_chosen`): the seed's normalization runs inside the run.
    /// Fix round 1 (review should-fix 3 and 4), the positive controls of that check: a state
    /// applying `#read` (a census hook, which without a console takes no value and notes no mark;
    /// its count is no class since GAP A1) or `Float2String` (a run-list hook) is flagged, and the run from `done(#read(0, 3))`
    /// lists `IO.read` on `unsupportedHooks` and no class value.
    /// GAP K1: `nan`, `mz` and `mx` reach their zero as `1.0 -Float 1.0` from N = 1 (+0.0 by
    /// `fp.sub`; their controls are N = 2), where they converted `Int2Float(0, 53, 11)`, whose sign
    /// no text fixes, so k-rust marked that conversion too (`float-rounding`) and each probe listed
    /// two marks; each now lists its own class alone. K1's Float classes have probes: `i2f`
    /// converts 2^24 + 1 (no binary32 element holds it) and 0 (both zeros hold it) to binary32,
    /// `float-rounding`, against the control 2^24, which binary32 holds; `rt` takes the square root
    /// of 2 (not exact, `float-rounding`) and of -4 (no described value, `outside-domain`), against
    /// the exact root of 4. Its other classes have no probe here, since their hooks are still on
    /// the census (until GK-1), which would exclude `classes.k` as a whole.
    /// GAP A2 (`docs/amendments.md` AM-4, AM-5): `Int2Float` is IEEE 754's conversion under
    /// roundTiesToEven, 2^24 + 1 a tie to the even 2^24 and 0 the positive zero, and the square
    /// root of 2 is correctly rounded, so `i2f(16777217)`, `i2f(0)` and `rt(2)` read determined
    /// values and list nothing, as their controls do; `rt(-4)` keeps its `outside-domain` mark.
    #[test]
    #[ignore = "kink"]
    fn every_k_rust_class_is_judged_per_run() {
        on_a_big_stack(|| {
            let (side, module) = fixture("classes");
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert!(
                exclusions.implementation_chosen.is_empty(),
                "{:?}",
                exclusions.implementation_chosen
            );
            assert_eq!(exclusions.definition_exclusion(), None);
            let base2string = ("STRING.base2string", "letter-case");
            let probes = [
                ("keys", 1, Some(("MAP.keys_list", "order"))),
                ("vals", 1, Some(("MAP.values", "order"))),
                ("s2l", 1, Some(("SET.set2list", "order"))),
                ("choiceMap", 1, Some(("MAP.choice", "item"))),
                ("choiceSet", 1, Some(("SET.choice", "item"))),
                ("mixed", 1, Some(("FLOAT.add", "float-destination"))),
                ("mdiv", 1, Some(("FLOAT.div", "float-destination"))),
                ("nan", 1, Some(("FLOAT.sign", "nan-sign"))),
                ("mz", 1, Some(("FLOAT.min", "signed-zero"))),
                ("mx", 1, Some(("FLOAT.max", "signed-zero"))),
                ("b2s", 255, Some(base2string)),
                ("lit", 0, Some(base2string)),
                ("cond", 255, Some(base2string)),
                ("eqn", 255, Some(base2string)),
                ("req", 255, Some(base2string)),
                ("rt", -4, Some(("FLOAT.root", "outside-domain"))),
                ("keysOne", 1, None),
                ("choiceOne", 1, None),
                ("same", 1, None),
                ("nan", 2, None),
                ("mz", 2, None),
                ("mx", 2, None),
                ("b2s", 9, None),
                ("cond", 9, None),
                ("eqn", 9, None),
                ("req", 9, None),
                ("i2f", 16_777_216, None),
                ("i2f", 16_777_217, None),
                ("i2f", 0, None),
                ("rt", 4, None),
                ("rt", 2, None),
            ];
            let mut failures = Vec::new();
            let mut judge =
                |name: String, execution: &AdaptedExecution, mark: Option<(&str, &str)>| {
                    let listed = execution
                        .facts()
                        .implementation_chosen_values
                        .iter()
                        .map(|mark| (mark.hook.clone(), mark.class.clone()))
                        .collect::<Vec<_>>();
                    let expected = mark
                        .iter()
                        .map(|(hook, class)| ((*hook).to_owned(), (*class).to_owned()))
                        .collect::<Vec<_>>();
                    let exclusion = exclusions.run_exclusion(execution);
                    eprintln!("{name}: {listed:?} {exclusion:?}");
                    if listed != expected
                        || exclusion != mark.map(|_| Exclusion::ImplementationChosenValue)
                    {
                        failures.push(format!("{name}: {listed:?} {exclusion:?}"));
                    }
                };
            for (symbol, argument, mark) in probes {
                let execution = run(&side, &module, call(symbol, argument));
                judge(format!("{symbol}({argument})"), &execution, mark);
            }
            // The initial state's normalization: the seed evaluates `hex(255)` inside the run.
            let seeded = k_rust::kore::parser::parse_pattern(
                r#"Lbldone{}(inj{SortString{}, SortKItem{}}(Lblhex{}(\dv{SortInt{}}("255"))))"#,
            )
            .unwrap();
            let execution = run(&side, &module, seeded);
            judge("done(hex(255))".to_owned(), &execution, Some(base2string));
            // `#read` without a console: unsupported, not a class value.
            let execution = run(&side, &module, call("rd", 3));
            let facts = execution.facts();
            let unsupported = facts
                .unsupported_hooks
                .iter()
                .map(|entry| entry.hook.as_str())
                .collect::<Vec<_>>();
            eprintln!(
                "rd(3): {facts:?} {:?}",
                exclusions.run_exclusion(&execution)
            );
            if !facts.implementation_chosen_values.is_empty()
                || unsupported != ["IO.read"]
                || exclusions.run_exclusion(&execution) != Some(Exclusion::UnsupportedHook)
            {
                failures.push(format!(
                    "rd(3): {facts:?} {:?}",
                    exclusions.run_exclusion(&execution)
                ));
            }
            // A state written with `Base2String` itself is no initial-state exclusion; one written
            // with `#read` or `Float2String` is (the check's positive controls).
            let written = |name: &str, arguments: &str| {
                k_rust::kore::parser::parse_pattern(&format!(
                    r#"Lbldone{{}}(inj{{{SORT}, SortKItem{{}}}}({name}{{}}({arguments})))"#,
                    SORT = if name.contains("read") {
                        "SortIOString{}"
                    } else {
                        "SortString{}"
                    },
                ))
                .unwrap()
            };
            let (flags, read) = backend(&side, &module)
                .with_solver(None, |definition, _| {
                    let symbol_of = |hook: &str| {
                        definition
                            .symbols()
                            .values()
                            .find(|symbol| symbol.attributes.hook.as_deref() == Some(hook))
                            .unwrap_or_else(|| panic!("{hook} is declared"))
                            .name
                            .to_string()
                    };
                    let int = |value: &str| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
                    let float = format!(
                        "{}{{}}({}, {}, {})",
                        symbol_of("FLOAT.int2float"),
                        int("1"),
                        int("53"),
                        int("11")
                    );
                    let read = written(
                        &symbol_of("IO.read"),
                        &format!("{}, {}", int("0"), int("3")),
                    );
                    let flags = [
                        (
                            "Base2String(255, 16)",
                            written(
                                &symbol_of("STRING.base2string"),
                                &format!("{}, {}", int("255"), int("16")),
                            ),
                            false,
                        ),
                        ("#read(0, 3)", read.clone(), true),
                        (
                            "Float2String(Int2Float(1, 53, 11))",
                            written(&symbol_of("STRING.float2string"), &float),
                            true,
                        ),
                    ]
                    .map(|(name, written, expected)| {
                        (
                            name,
                            state_references_implementation_chosen(definition, &state(written)),
                            expected,
                        )
                    });
                    Ok::<_, k_rust::backend::BackendError>((flags, read))
                })
                .unwrap();
            for (name, flagged, expected) in flags {
                eprintln!("done({name}) flags the initial state: {flagged}");
                if flagged != expected {
                    failures.push(format!("done({name}) flags the initial state: {flagged}"));
                }
            }
            let execution = run(&side, &module, read);
            let facts = execution.facts();
            let unsupported = facts
                .unsupported_hooks
                .iter()
                .map(|entry| entry.hook.as_str())
                .collect::<Vec<_>>();
            eprintln!(
                "done(#read(0, 3)): {facts:?} {:?}",
                exclusions.run_exclusion(&execution)
            );
            if !facts.implementation_chosen_values.is_empty()
                || unsupported != ["IO.read"]
                || exclusions.run_exclusion(&execution) != Some(Exclusion::UnsupportedHook)
            {
                failures.push(format!(
                    "done(#read(0, 3)): {facts:?} {:?}",
                    exclusions.run_exclusion(&execution)
                ));
            }
            assert!(failures.is_empty(), "{failures:#?}");
        });
    }
}
