//! Each fixture of `tests/data` does what `tests/data/README.md` says: it compiles in-process
//! in the portable build, and its programs run through the public `Backend::execute` to the
//! halt, the final configuration and the record the README promises.
//!
//! These tests judge the fixtures, not the fuzz engine: they use only k-rust's public API.

mod support;

use k_rust::{
    backend::{
        Backend, BackendDiagnosticOutput, CompiledRuleKind, ContradictedClaimKind,
        ContradictedClaimOutput, ExecuteRequest, ExecutionLeaf, ExecutionResult, ExecutionStrategy,
        HaltReasonOutput, ObservedInOutput, ResultModalityOutput,
    },
    kore::{ast::Pattern, codec, printer::Printer},
};
use support::{
    CHOSEN, CHOSEN_KILL, COIN, COIN_FUNC, COIN_KILL, COIN_LAYOUT, COIN_PRIO, COIN_SWAPPED,
    Compiled, IMP, LEDGER, LOADCLAIM, RULES, TAINT, UNSIGNED,
};

/// A path-set request with coverage, as a campaign case makes one (ARCHITECTURE.md §5.1).
fn request(initial: &Pattern, strategy: ExecutionStrategy) -> ExecuteRequest {
    ExecuteRequest {
        strategy,
        result_modality: ResultModalityOutput::PathSet,
        collect_coverage: true,
        ..ExecuteRequest::new(initial.clone())
    }
}

fn execute(backend: &mut Backend, request: ExecuteRequest) -> ExecutionResult {
    backend.execute(request).expect("the request executes")
}

/// Run `initial` with every path on `krun`'s route.
fn run_all(compiled: &Compiled, initial: &Pattern) -> ExecutionResult {
    execute(
        &mut compiled.source_backend(),
        request(initial, ExecutionStrategy::All),
    )
}

/// Assemble `text`, the program `file` of `compiled` with one literal replaced.
fn variant(compiled: &Compiled, file: &str, find: &str, replace: &str) -> Pattern {
    let program = compiled.fixture.program(file);
    assert_eq!(program.text.matches(find).count(), 1, "{find} in {file}");
    let text = program.text.replacen(find, replace, 1);
    compiled
        .assemble(program.file, &text, program.bindings)
        .unwrap_or_else(|error| panic!("{text} does not assemble: {error}"))
}

fn printed(leaf: &ExecutionLeaf) -> String {
    Printer::compact().print_pattern(&codec::from_value(&leaf.state).expect("a KORE leaf"))
}

/// The one leaf of `result`.
fn only_leaf(result: &ExecutionResult) -> &ExecutionLeaf {
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one leaf: {result:#?}");
    };
    leaf
}

fn cell(name: &str, content: &str) -> String {
    format!("Lbl'-LT-'{name}'-GT-'{{}}({content})")
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

const EMPTY_K: &str = "Lbl'-LT-'k'-GT-'{}(dotk{}())";

/// The run-level half of a clean leaf (ARCHITECTURE.md §5.2): no stack stop, no undecided
/// solver answer, no allowance refusal and no unsupported hook, in the run or in the load.
fn assert_clean_run(result: &ExecutionResult) {
    assert_eq!(result.stack_stops, 0, "{result:#?}");
    assert_eq!(result.smt_unknowns, 0, "{result:#?}");
    assert!(result.allowance_refusals.is_empty(), "{result:#?}");
    assert!(result.unsupported_hooks.is_empty(), "{result:#?}");
}

/// A clean natural end of `result`: a `stuck` leaf with an empty `<k>`, no constraint and no
/// diagnostic, in a run with no run-level fact that would make a leaf unclean.
fn assert_natural_end(result: &ExecutionResult, leaf: &ExecutionLeaf) -> String {
    assert_clean_run(result);
    let state = printed(leaf);
    assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{state}");
    assert!(state.contains(EMPTY_K), "{state}");
    assert!(
        !state.contains("\\and{") && !state.contains("\\equals{"),
        "a constrained leaf: {state}"
    );
    assert!(leaf.diagnostics.is_empty(), "{:#?}", leaf.diagnostics);
    state
}

/// The one leaf of `result`, a clean natural end.
fn natural_end(result: &ExecutionResult) -> String {
    assert_natural_end(result, only_leaf(result))
}

/// The entry `name |-> value` of IMP's `<state>`, printed.
fn binding(name: &str, value: i64) -> String {
    format!(
        "Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortId{{}}, SortKItem{{}}}}(\\dv{{SortId{{}}}}(\"{name}\")), inj{{SortInt{{}}, SortKItem{{}}}}({}))",
        int(value)
    )
}

/// The marks of a leaf, as `(hook, class)`.
fn marks(leaf: &ExecutionLeaf) -> Vec<(String, String)> {
    leaf.diagnostics
        .iter()
        .filter_map(|diagnostic| match diagnostic {
            BackendDiagnosticOutput::ImplementationChosenValue { hook, class } => {
                Some((hook.clone(), class.clone()))
            }
            _ => None,
        })
        .collect()
}

/// The unique id of the rule labelled `label` in `compiled`'s main module.
fn rule_id(compiled: &Compiled, label: &str) -> String {
    let full = format!("{}.{label}", compiled.main_module());
    let catalog = compiled.source_backend().rule_catalog(None).unwrap();
    let entries = catalog
        .iter()
        .filter(|entry| entry.label.as_deref() == Some(full.as_str()))
        .collect::<Vec<_>>();
    let [entry] = entries.as_slice() else {
        panic!("expected one rule {full}: {catalog:#?}");
    };
    entry.id.clone()
}

#[test]
fn imp_programs_end_naturally_and_div_gets_stuck_mid_program() {
    let imp = IMP.compiled();
    let commute = run_all(imp, &imp.initial("imp/commute.imp"));
    let state = natural_end(&commute);
    assert!(state.contains(&binding("a", 8)), "{state}");
    assert!(state.contains(&binding("b", 8)), "{state}");

    // A natural end with three `<state>` entries.
    let le = run_all(imp, &imp.initial("imp/le.imp"));
    let state = natural_end(&le);
    for (name, value) in [("x", 3), ("y", 5), ("r", 1)] {
        assert!(state.contains(&binding(name, value)), "{state}");
    }
    let counterexample = run_all(imp, &variant(imp, "imp/le.imp", "x = 3;", "x = 7;"));
    let state = natural_end(&counterexample);
    assert!(state.contains(&binding("r", 0)), "{state}");
    // Negative literals are Int tokens in IMP.
    let negative = run_all(imp, &variant(imp, "imp/le.imp", "y = 5;", "y = -5;"));
    let state = natural_end(&negative);
    assert!(state.contains(&binding("y", -5)), "{state}");

    let div = run_all(imp, &imp.initial("imp/div.imp"));
    let state = natural_end(&div);
    assert!(state.contains(&binding("q", 5)), "{state}");
    let stuck = run_all(imp, &variant(imp, "imp/div.imp", "y = 2;", "y = 0;"));
    let leaf = only_leaf(&stuck);
    let state = printed(leaf);
    assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{state}");
    assert!(!state.contains(EMPTY_K), "{state}");
    // Stuck at the division `10 / 0`, which the guarded rule refuses.
    let redex = format!(
        "Lbl'UndsSlshUnds'{{}}(inj{{SortInt{{}}, SortAExp{{}}}}({}), inj{{SortInt{{}}, SortAExp{{}}}}({}))",
        int(10),
        int(0)
    );
    assert!(state.contains(&redex), "{state}");
    assert_clean_run(&stuck);
    assert!(leaf.diagnostics.is_empty(), "{:#?}", leaf.diagnostics);
}

#[test]
fn imp_loop_ends_naturally_unbounded_and_halts_at_a_small_depth_or_work_bound() {
    let imp = IMP.compiled();
    let initial = imp.initial("imp/loop.imp");
    let unbounded = run_all(imp, &initial);
    let leaf = only_leaf(&unbounded);
    let state = assert_natural_end(&unbounded, leaf);
    assert!(state.contains(&binding("s", 55)), "{state}");
    assert!(state.contains(&binding("n", 0)), "{state}");
    assert!(leaf.depth > 20, "{}", leaf.depth);

    let mut depth = request(&initial, ExecutionStrategy::All);
    depth.max_depth = Some(20);
    let bounded = execute(&mut imp.source_backend(), depth);
    assert_eq!(only_leaf(&bounded).reason, HaltReasonOutput::DepthBound);

    let mut work = request(&initial, ExecutionStrategy::All);
    work.max_work = Some(20);
    let bounded = execute(&mut imp.source_backend(), work);
    assert_eq!(only_leaf(&bounded).reason, HaltReasonOutput::WorkBound);
}

#[test]
fn unsigned_parses_a_negative_literal_as_a_negation() {
    let unsigned = UNSIGNED.compiled();
    let sum = run_all(unsigned, &unsigned.initial("unsigned/sum.pgm"));
    let state = natural_end(&sum);
    let printed_out = |value| {
        cell(
            "out",
            &format!(
                "LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}))",
                int(value)
            ),
        )
    };
    assert!(state.contains(&printed_out(12)), "{state}");

    // `-5` is not a token: the configuration holds `neg(5)`, never the domain value -5.
    let negative = variant(unsigned, "unsigned/sum.pgm", "5", "-5");
    let configuration = Printer::compact().print_pattern(&negative);
    assert!(configuration.contains("Lblneg{}("), "{configuration}");
    assert!(configuration.contains(&int(5)), "{configuration}");
    assert!(!configuration.contains(&int(-5)), "{configuration}");
    let state = natural_end(&run_all(unsigned, &negative));
    assert!(state.contains(&printed_out(2)), "{state}");
}

#[test]
fn chosen_marks_the_listing_order_of_two_keys_or_elements_and_not_of_one() {
    let chosen = CHOSEN.compiled();
    for (file, hook) in [
        ("chosen/keys.pgm", "MAP.keys_list"),
        ("chosen/set.pgm", "SET.set2list"),
    ] {
        let result = run_all(chosen, &chosen.initial(file));
        let leaf = only_leaf(&result);
        let state = printed(leaf);
        assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{file}: {state}");
        assert!(state.contains(EMPTY_K), "{file}: {state}");
        assert_eq!(
            marks(leaf),
            [(hook.to_owned(), "order".to_owned())],
            "{file}"
        );
        assert_eq!(result.implementation_chosen_values.len(), 1, "{file}");
    }
    let one_key = run_all(
        chosen,
        &variant(chosen, "chosen/keys.pgm", "(1, 2)", "(1, 1)"),
    );
    natural_end(&one_key);
    assert!(one_key.implementation_chosen_values.is_empty());
}

#[test]
fn chosen_kill_adds_an_end_that_reads_the_open_order_only_for_distinct_keys() {
    let chosen = CHOSEN.compiled();
    let kill = CHOSEN_KILL.compiled();
    let one_end = |compiled: &Compiled, initial: &Pattern| {
        let result = run_all(compiled, initial);
        let leaf = only_leaf(&result);
        assert_eq!(leaf.reason, HaltReasonOutput::Stuck);
        (printed(leaf), marks(leaf))
    };
    let list = |values: &[i64]| {
        values
            .iter()
            .map(|value| {
                format!(
                    "LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}))",
                    int(*value)
                )
            })
            .collect::<Vec<_>>()
    };
    let keys_mark = vec![("MAP.keys_list".to_owned(), "order".to_owned())];
    // Distinct keys: both sides marked, ends differ.
    let (baseline, baseline_marks) = one_end(chosen, &chosen.initial("chosen/keys.pgm"));
    let (mutant, mutant_marks) = one_end(kill, &kill.initial("chosen/keys.pgm"));
    assert_eq!(
        (baseline_marks, mutant_marks),
        (keys_mark.clone(), keys_mark)
    );
    assert_ne!(baseline, mutant);
    for item in list(&[1, 2]) {
        assert!(mutant.contains(&item), "{mutant}");
    }
    // Equal keys: neither side marked, and the mutant ends with [1, 1] where the baseline
    // ends with [1].
    let equal = |compiled| variant(compiled, "chosen/keys.pgm", "(1, 2)", "(1, 1)");
    let (baseline, baseline_marks) = one_end(chosen, &equal(chosen));
    let (mutant, mutant_marks) = one_end(kill, &equal(kill));
    assert!(baseline_marks.is_empty() && mutant_marks.is_empty());
    let item = &list(&[1])[0];
    assert_eq!(baseline.matches(item.as_str()).count(), 1, "{baseline}");
    assert_eq!(mutant.matches(item.as_str()).count(), 2, "{mutant}");
    natural_end(&run_all(kill, &equal(kill)));
}

#[test]
fn rules_div_is_an_undefined_step_that_is_covered_and_check_reaches_a_failing_guard() {
    let rules = RULES.compiled();
    let div_id = rule_id(rules, "div");

    let defined = run_all(rules, &rules.initial("rules/div.pgm"));
    let state = natural_end(&defined);
    assert!(state.contains(&cell("out", &int(5))), "{state}");

    let undefined = run_all(rules, &variant(rules, "rules/div.pgm", "2)", "0)"));
    let leaf = only_leaf(&undefined);
    assert_eq!(leaf.reason, HaltReasonOutput::Trivial, "{}", printed(leaf));
    assert_eq!(leaf.rule_id.as_deref(), Some(div_id.as_str()));
    let coverage = undefined.coverage.as_ref().expect("coverage was asked for");
    assert!(coverage.applied.contains(&div_id), "{coverage:#?}");

    // With `div` as the only stop rule (the `fired` mode without run-to-completion), the
    // undefined step is still `trivial` and the defined one halts `terminal`.
    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        let stop_at_div = |initial: &Pattern| {
            let mut request = request(initial, strategy);
            request.terminal_rules = vec![div_id.clone()];
            execute(&mut rules.source_backend(), request)
        };
        let undefined = stop_at_div(&variant(rules, "rules/div.pgm", "2)", "0)"));
        let leaf = only_leaf(&undefined);
        assert_eq!(leaf.reason, HaltReasonOutput::Trivial, "{strategy:?}");
        assert_eq!(leaf.rule_id.as_deref(), Some(div_id.as_str()));
        let defined = stop_at_div(&rules.initial("rules/div.pgm"));
        assert_eq!(
            only_leaf(&defined).reason,
            HaltReasonOutput::Terminal,
            "{strategy:?}"
        );
    }

    let hit_id = rule_id(rules, "check-hit");
    let miss_id = rule_id(rules, "check-miss");
    let check = run_all(rules, &rules.initial("rules/check.pgm"));
    let state = natural_end(&check);
    assert!(state.contains(&cell("out", &int(0))), "{state}");
    let coverage = check.coverage.as_ref().expect("coverage was asked for");
    assert!(coverage.matched.contains(&hit_id), "{coverage:#?}");
    assert!(!coverage.applied.contains(&hit_id), "{coverage:#?}");
    assert!(coverage.applied.contains(&miss_id), "{coverage:#?}");
    let hit = run_all(rules, &variant(rules, "rules/check.pgm", "7", "42"));
    let state = natural_end(&hit);
    assert!(state.contains(&cell("out", &int(1))), "{state}");

    let twice = run_all(rules, &rules.initial("rules/twice.pgm"));
    let state = natural_end(&twice);
    assert!(state.contains(&cell("out", &int(42))), "{state}");
}

#[test]
fn rules_catalog_holds_a_shared_identity_a_non_executable_rule_and_an_equation() {
    let rules = RULES.compiled();
    let catalog = rules.source_backend().rule_catalog(None).unwrap();
    let entry = |label: &str| {
        let full = format!("RULES.{label}");
        catalog
            .iter()
            .find(|entry| entry.label.as_deref() == Some(full.as_str()))
            .unwrap_or_else(|| panic!("no {full}: {catalog:#?}"))
    };
    let (a, b) = (entry("twin-a"), entry("twin-b"));
    assert_eq!(a.id, b.id);
    assert!(a.shared_identity && b.shared_identity);
    assert!(!entry("dormant").executable);
    assert_eq!(entry("double").kind, CompiledRuleKind::FunctionEquation);
    for label in ["div", "check-hit", "check-miss", "twice"] {
        let rule = entry(label);
        assert_eq!(rule.kind, CompiledRuleKind::Rewrite, "{label}");
        assert!(rule.executable && !rule.shared_identity, "{label}");
    }

    // A rewrite rule marked `non-executable` in caller KORE, loaded from the KORE alone.
    let edited = rules
        .backend_with_non_executable("check-hit")
        .rule_catalog(None)
        .unwrap();
    let dormant = edited
        .iter()
        .find(|entry| entry.label.as_deref() == Some("RULES.check-hit"))
        .expect("check-hit is in the edited catalog");
    assert_eq!(dormant.kind, CompiledRuleKind::Rewrite);
    assert!(!dormant.executable && !dormant.shared_identity);
    let definition = rules.definition_with_non_executable("check-hit");
    assert_eq!(definition.route, k_rust_fuzz::BackendRoute::FromDefinition);
    assert_ne!(
        k_rust::backend::execution_digest(&definition.kore).unwrap(),
        rules.digest()
    );
}

/// The `<out>` values of the leaves of `result`, which must all be natural ends.
fn ends(result: &ExecutionResult) -> Vec<i64> {
    let mut ends = result
        .leaves
        .iter()
        .map(|leaf| {
            let state = assert_natural_end(result, leaf);
            (-20..=20)
                .find(|value| state.contains(&cell("out", &int(*value))))
                .unwrap_or_else(|| panic!("no small <out> in {state}"))
        })
        .collect::<Vec<_>>();
    ends.sort_unstable();
    ends
}

fn one_path(compiled: &Compiled, backend: &mut Backend, file: &str) -> Vec<i64> {
    ends(&execute(
        backend,
        request(&compiled.initial(file), ExecutionStrategy::Any),
    ))
}

#[test]
fn coin_single_paths_differ_while_sets_of_ends_agree_and_kill_adds_an_end() {
    let coin = COIN.compiled();
    let layout = COIN_LAYOUT.compiled();
    let swapped = COIN_SWAPPED.compiled();
    let prio = COIN_PRIO.compiled();
    let kill = COIN_KILL.compiled();

    for mutant in [coin, layout, swapped] {
        let result = run_all(mutant, &mutant.initial("coin/flip.pgm"));
        assert_eq!(ends(&result), [3, 4], "{}", mutant.fixture.file);
    }
    assert_eq!(ends(&run_all(prio, &prio.initial("coin/flip.pgm"))), [4]);
    assert_eq!(ends(&run_all(kill, &kill.initial("coin/flip.pgm"))), [3, 4]);
    let killed = run_all(kill, &variant(kill, "coin/flip.pgm", "3", "11"));
    assert_eq!(ends(&killed), [13]);
    let baseline = run_all(coin, &variant(coin, "coin/flip.pgm", "3", "11"));
    assert_eq!(ends(&baseline), [11, 12]);

    // Layout changes nothing the backend reads; writing the rules in another order changes the
    // KORE's sentence order (so the digest) and the rewrite order.
    assert_eq!(layout.digest(), coin.digest());
    assert_eq!(
        layout.artifacts.execution_rewrite_order,
        coin.artifacts.execution_rewrite_order
    );
    assert_ne!(swapped.digest(), coin.digest());
    assert_ne!(
        swapped.artifacts.execution_rewrite_order,
        coin.artifacts.execution_rewrite_order
    );
    assert_ne!(prio.digest(), coin.digest());
    assert_ne!(kill.digest(), coin.digest());

    // Strategy `any` follows the first rule in source order, on krun's route and from the KORE
    // alone (whose sentences keep the source order), so the baseline and the swapped mutant
    // end differently on one path.
    assert_eq!(
        one_path(coin, &mut coin.source_backend(), "coin/flip.pgm"),
        [3]
    );
    assert_eq!(
        one_path(swapped, &mut swapped.source_backend(), "coin/flip.pgm"),
        [4]
    );
    assert_eq!(
        one_path(coin, &mut coin.kore_backend(), "coin/flip.pgm"),
        [3]
    );
    assert_eq!(
        one_path(swapped, &mut swapped.kore_backend(), "coin/flip.pgm"),
        [4]
    );
}

#[test]
fn coin_count_is_complete_unbounded_and_incomplete_under_a_small_depth_bound() {
    let coin = COIN.compiled();
    let initial = coin.initial("coin/count.pgm");
    assert_eq!(ends(&run_all(coin, &initial)), [0]);
    // `count(3)` ends only from `max_depth` 5 (N + 2): at 4 its leaf is still `depth-bound`.
    for (depth, reason) in [
        (3, HaltReasonOutput::DepthBound),
        (4, HaltReasonOutput::DepthBound),
        (5, HaltReasonOutput::Stuck),
    ] {
        let mut bounded = request(&initial, ExecutionStrategy::All);
        bounded.max_depth = Some(depth);
        let result = execute(&mut coin.source_backend(), bounded);
        assert_eq!(only_leaf(&result).reason, reason, "max_depth {depth}");
    }
}

#[test]
fn coin_func_adds_an_end_that_holds_an_unevaluated_total_function() {
    let func = COIN_FUNC.compiled();
    assert_eq!(ends(&run_all(func, &func.initial("coin/flip.pgm"))), [3, 4]);
    let hidden = run_all(func, &variant(func, "coin/flip.pgm", "3", "11"));
    let state = natural_end(&hidden);
    assert!(
        state.contains(&cell("out", &format!("Lblopaque{{}}({})", int(11)))),
        "{state}"
    );
    assert_ne!(func.digest(), COIN.compiled().digest());
}

#[test]
fn ledger_settles_a_transfer_bound_to_a_record_sorted_configuration_variable() {
    let ledger = LEDGER.compiled();
    assert_eq!(
        ledger
            .configuration_variables()
            .get("TX")
            .map(|sort| sort.name.as_str()),
        Some("Tx")
    );
    let settled = run_all(ledger, &ledger.initial("ledger/settle.pgm"));
    let state = natural_end(&settled);
    assert!(state.contains(&cell("status", "Lblapplied{}()")), "{state}");
    assert!(
        state.contains(&format!("Lblaccount{{}}({}, {})", int(1), int(69))),
        "{state}"
    );

    let program = ledger.fixture.program("ledger/settle.pgm");
    let overdraft = ledger
        .assemble(program.file, program.text, &[("TX", "transfer(100, 1)")])
        .unwrap();
    let refused = run_all(ledger, &overdraft);
    let state = natural_end(&refused);
    assert!(state.contains(&cell("status", "Lblrefused{}()")), "{state}");
}

/// The one record of the LOADCLAIM load: `td`'s `total` attribute, contradicted by its equation
/// `tdeq` at the ground input 0, observed when the definition was loaded.
fn assert_load_record(records: &[ContradictedClaimOutput]) {
    let [record] = records else {
        panic!("expected one record: {records:#?}");
    };
    assert_eq!(record.claim, ContradictedClaimKind::Total, "{record:#?}");
    assert_eq!(record.symbol.as_deref(), Some("Lbltd"), "{record:#?}");
    assert_eq!(
        record.rule_label.as_deref(),
        Some("LOADCLAIM.tdeq"),
        "{record:#?}"
    );
    assert!(record.ground, "{record:#?}");
    assert_eq!(record.observed_in, ObservedInOutput::Load, "{record:#?}");
}

#[test]
fn loadclaim_lists_the_load_s_contradicted_claim_on_no_leaf() {
    let loadclaim = LOADCLAIM.compiled();
    for (initial, out) in [
        (loadclaim.initial("loadclaim/go.pgm"), 0),
        (variant(loadclaim, "loadclaim/go.pgm", "7", "101"), 1),
    ] {
        for (route, mut backend) in [
            ("source", loadclaim.source_backend()),
            ("kore", loadclaim.kore_backend()),
        ] {
            for max_work in [None, Some(50)] {
                let mut request = request(&initial, ExecutionStrategy::All);
                request.max_work = max_work;
                let result = execute(&mut backend, request);
                let state = natural_end(&result);
                assert!(
                    state.contains(&cell("out", &int(out))),
                    "{route} {max_work:?}: {state}"
                );
                assert_load_record(&result.contradicted_claims);
            }
        }
    }
}

#[test]
fn taint_ends_with_an_empty_k_on_leaves_that_are_not_clean() {
    let taint = TAINT.compiled();
    let out = |content: &str| cell("out", &format!("kseq{{}}({content}, dotk{{}}())"));
    let item = |value: i64| format!("inj{{SortInt{{}}, SortKItem{{}}}}({})", int(value));

    // A present key evaluates; a missing one leaves `find` unevaluated on a stuck leaf, beside an
    // undefined step under `\not ⌈find(...)⌉`.
    let found = run_all(taint, &taint.initial("taint/get.pgm"));
    let state = natural_end(&found);
    assert!(state.contains(&out(&item(10))), "{state}");
    let missing = run_all(taint, &variant(taint, "taint/get.pgm", "1", "2"));
    assert_clean_run(&missing);
    let [undefined, stuck] = missing.leaves.as_slice() else {
        panic!("expected two leaves: {missing:#?}");
    };
    assert_eq!(undefined.reason, HaltReasonOutput::Trivial);
    assert_eq!(undefined.rule_label.as_deref(), Some("TAINT.get"));
    let state = printed(stuck);
    assert_eq!(stuck.reason, HaltReasonOutput::Stuck, "{state}");
    assert!(state.contains(EMPTY_K), "{state}");
    assert!(state.contains("Lblfind{}("), "{state}");
    // Unconstrained and without diagnostics: only its term's partial application, which makes
    // the internalized term not `ceil_free`, keeps it from being clean. Its sibling is the
    // undefined step over the instances where `find` is undefined.
    assert!(!state.contains("\\and{"), "{state}");
    assert!(stuck.diagnostics.is_empty(), "{:#?}", stuck.diagnostics);
    assert!(
        printed(undefined).contains("\\not{"),
        "{}",
        printed(undefined)
    );

    // The hooked lookup of a missing key is an undefined step instead.
    let looked = run_all(taint, &taint.initial("taint/look.pgm"));
    natural_end(&looked);
    let undefined = run_all(taint, &variant(taint, "taint/look.pgm", "1", "2"));
    assert_eq!(only_leaf(&undefined).reason, HaltReasonOutput::Trivial);

    // `guard(0)` refutes `td(0) >Int 0` through the contradicted `total` claim of `td`, and the
    // owise rule's natural end carries the run's record.
    let guarded = run_all(taint, &taint.initial("taint/guard.pgm"));
    let state = natural_end(&guarded);
    assert!(state.contains(&out(&item(1))), "{state}");
    assert!(guarded.contradicted_claims.is_empty(), "{guarded:#?}");
    let refuted = run_all(taint, &variant(taint, "taint/guard.pgm", "5", "0"));
    let leaf = only_leaf(&refuted);
    let state = printed(leaf);
    assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{state}");
    assert!(state.contains(EMPTY_K), "{state}");
    assert!(state.contains(&out(&item(0))), "{state}");
    let records = leaf
        .diagnostics
        .iter()
        .filter_map(|diagnostic| match diagnostic {
            BackendDiagnosticOutput::ContradictedClaim(record) => Some(record),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [record] = records.as_slice() else {
        panic!("expected one record on the leaf: {:#?}", leaf.diagnostics);
    };
    assert_eq!(record.claim, ContradictedClaimKind::Total, "{record:#?}");
    assert_eq!(record.symbol.as_deref(), Some("Lbltd"), "{record:#?}");
    assert_eq!(record.observed_in, ObservedInOutput::Run, "{record:#?}");
    assert_clean_run(&refuted);
}

#[test]
fn every_fixture_converts_to_a_campaign_definition_and_program() {
    for fixture in &support::ALL {
        let compiled = fixture.compiled();
        let definition = compiled.definition();
        assert_eq!(definition.main_module, fixture.main_module);
        assert_eq!(
            definition.syntax_module,
            format!("{}-SYNTAX", fixture.main_module)
        );
        assert_eq!(
            definition.route,
            k_rust_fuzz::BackendRoute::SourceExecution {
                execution_rewrite_order: compiled.artifacts.execution_rewrite_order.clone(),
            }
        );
        assert_eq!(
            compiled
                .definition_on(k_rust_fuzz::BackendRoute::FromDefinition)
                .route,
            k_rust_fuzz::BackendRoute::FromDefinition
        );
        for program in fixture.programs {
            let source = compiled.program_source(program.file);
            let text = source.program.expect("every fixture program binds $PGM");
            assert_eq!(
                (text.name.as_str(), text.text.as_str()),
                (program.file, program.text)
            );
            let expected = program
                .bindings
                .iter()
                .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(source.config_vars, expected);
            compiled.initial(program.file);
        }
    }
}
