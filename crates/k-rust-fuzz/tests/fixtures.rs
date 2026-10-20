//! Each fixture of `tests/data` does what `tests/data/README.md` says: it compiles in-process
//! in the portable build, and its programs run through the public `Backend::execute` to the
//! halt, the final configuration and the record the README promises.
//!
//! These tests judge the fixtures, not the fuzz engine: they use only k-rust's public API.

mod support;

use k_rust::{
    backend::{
        Backend, BackendDiagnosticOutput, CompiledRuleKind, ExecuteRequest, ExecutionLeaf,
        ExecutionResult, ExecutionStrategy, HaltReasonOutput, ObservedInOutput,
        ResultModalityOutput,
    },
    kore::{ast::Pattern, codec, printer::Printer},
};
use support::{
    CHOSEN, COIN, COIN_KILL, COIN_LAYOUT, COIN_PRIO, COIN_SWAPPED, Compiled, IMP, LEDGER,
    LOADCLAIM, RULES, UNSIGNED,
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

/// A natural end: a `stuck` leaf with an empty `<k>`, no constraint and no diagnostic.
fn assert_natural_end(leaf: &ExecutionLeaf) -> String {
    let state = printed(leaf);
    assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{state}");
    assert!(state.contains(EMPTY_K), "{state}");
    assert!(leaf.diagnostics.is_empty(), "{:#?}", leaf.diagnostics);
    state
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
    let state = assert_natural_end(only_leaf(&commute));
    assert!(state.contains(&binding("a", 8)), "{state}");
    assert!(state.contains(&binding("b", 8)), "{state}");

    let le = run_all(imp, &imp.initial("imp/le.imp"));
    let state = assert_natural_end(only_leaf(&le));
    assert!(state.contains(&binding("r", 1)), "{state}");
    let counterexample = run_all(imp, &variant(imp, "imp/le.imp", "x = 3;", "x = 7;"));
    let state = assert_natural_end(only_leaf(&counterexample));
    assert!(state.contains(&binding("r", 0)), "{state}");
    // Negative literals are Int tokens in IMP.
    let negative = run_all(imp, &variant(imp, "imp/le.imp", "y = 5;", "y = -5;"));
    let state = assert_natural_end(only_leaf(&negative));
    assert!(state.contains(&binding("y", -5)), "{state}");

    let div = run_all(imp, &imp.initial("imp/div.imp"));
    let state = assert_natural_end(only_leaf(&div));
    assert!(state.contains(&binding("q", 5)), "{state}");
    let stuck = run_all(imp, &variant(imp, "imp/div.imp", "y = 2;", "y = 0;"));
    let leaf = only_leaf(&stuck);
    let state = printed(leaf);
    assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{state}");
    assert!(!state.contains(EMPTY_K), "{state}");
    assert!(leaf.diagnostics.is_empty(), "{:#?}", leaf.diagnostics);
}

#[test]
fn imp_loop_ends_naturally_unbounded_and_halts_at_a_small_depth_or_work_bound() {
    let imp = IMP.compiled();
    let initial = imp.initial("imp/loop.imp");
    let unbounded = run_all(imp, &initial);
    let leaf = only_leaf(&unbounded);
    let state = assert_natural_end(leaf);
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
    let state = assert_natural_end(only_leaf(&sum));
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
    let state = assert_natural_end(only_leaf(&run_all(unsigned, &negative)));
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
    assert_natural_end(only_leaf(&one_key));
    assert!(one_key.implementation_chosen_values.is_empty());
}

#[test]
fn rules_div_is_an_undefined_step_that_is_covered_and_check_reaches_a_failing_guard() {
    let rules = RULES.compiled();
    let div_id = rule_id(rules, "div");

    let defined = run_all(rules, &rules.initial("rules/div.pgm"));
    let state = assert_natural_end(only_leaf(&defined));
    assert!(state.contains(&cell("out", &int(5))), "{state}");

    let undefined = run_all(rules, &variant(rules, "rules/div.pgm", "2)", "0)"));
    let leaf = only_leaf(&undefined);
    assert_eq!(leaf.reason, HaltReasonOutput::Trivial, "{}", printed(leaf));
    assert_eq!(leaf.rule_id.as_deref(), Some(div_id.as_str()));
    let coverage = undefined.coverage.as_ref().expect("coverage was asked for");
    assert!(coverage.applied.contains(&div_id), "{coverage:#?}");

    let hit_id = rule_id(rules, "check-hit");
    let miss_id = rule_id(rules, "check-miss");
    let check = run_all(rules, &rules.initial("rules/check.pgm"));
    let state = assert_natural_end(only_leaf(&check));
    assert!(state.contains(&cell("out", &int(0))), "{state}");
    let coverage = check.coverage.as_ref().expect("coverage was asked for");
    assert!(coverage.matched.contains(&hit_id), "{coverage:#?}");
    assert!(!coverage.applied.contains(&hit_id), "{coverage:#?}");
    assert!(coverage.applied.contains(&miss_id), "{coverage:#?}");
    let hit = run_all(rules, &variant(rules, "rules/check.pgm", "7", "42"));
    let state = assert_natural_end(only_leaf(&hit));
    assert!(state.contains(&cell("out", &int(1))), "{state}");

    let twice = run_all(rules, &rules.initial("rules/twice.pgm"));
    let state = assert_natural_end(only_leaf(&twice));
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
}

/// The `<out>` values of the leaves of `result`, which must all be natural ends.
fn ends(result: &ExecutionResult) -> Vec<i64> {
    let mut ends = result
        .leaves
        .iter()
        .map(|leaf| {
            let state = assert_natural_end(leaf);
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
    let mut bounded = request(&initial, ExecutionStrategy::All);
    bounded.max_depth = Some(3);
    let result = execute(&mut coin.source_backend(), bounded);
    assert_eq!(only_leaf(&result).reason, HaltReasonOutput::DepthBound);
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
    let state = assert_natural_end(only_leaf(&settled));
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
    let state = assert_natural_end(only_leaf(&refused));
    assert!(state.contains(&cell("status", "Lblrefused{}()")), "{state}");
}

#[test]
fn loadclaim_lists_the_load_s_contradicted_claim_on_no_leaf() {
    let loadclaim = LOADCLAIM.compiled();
    for (initial, out) in [
        (loadclaim.initial("loadclaim/go.pgm"), 0),
        (variant(loadclaim, "loadclaim/go.pgm", "7", "101"), 1),
    ] {
        let result = run_all(loadclaim, &initial);
        let state = assert_natural_end(only_leaf(&result));
        assert!(state.contains(&cell("out", &int(out))), "{state}");
        assert!(!result.contradicted_claims.is_empty(), "{result:#?}");
        for record in &result.contradicted_claims {
            assert_eq!(record.observed_in, ObservedInOutput::Load, "{record:#?}");
        }
    }
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
            assert_eq!(source.config_vars.len(), program.bindings.len());
            compiled.initial(program.file);
        }
    }
}
