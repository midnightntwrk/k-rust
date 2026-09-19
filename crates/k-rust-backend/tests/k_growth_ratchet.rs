//! CB-20 ratchet: term construction per step must not grow with the length of the `<k>` cell.
//!
//! The fixture rewrites the head of a `kseq` chain and pushes one inert item behind it on every
//! step, so the configuration grows by one item per step while the changed part stays constant.
//! `term.constructed` per late step is compared with `term.constructed` per early step.

const _: () = assert!(cfg!(feature = "measure"));

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, Pattern, execute},
};
use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{Counter, Snapshot, snapshot},
};

const K_GROWTH: &str = include_str!("fixtures/k-growth.kore");

/// Additive slack of the `late <= early + c` assertions (one rebuilt head plus its item).
const STEP_SLACK: u64 = 32;

fn definition(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    definition
        .internalize_pattern(&parse_pattern(source).expect("pattern should parse"), &[])
        .expect("pattern should internalize")
}

fn expected_state(depth: u64) -> String {
    let mut rest = "dotk{}()".to_owned();
    for index in 0..depth {
        rest = format!("kseq{{}}(inert{{}}(\\dv{{SortInt{{}}}}(\"{index}\")), {rest})");
    }
    format!("k{{}}(kseq{{}}(head{{}}(\\dv{{SortInt{{}}}}(\"{depth}\")), {rest}))")
}

/// Run the push rule `depth` times from `k(kseq(head(0), dotk))` and return the counter delta.
fn execute_k_growth(definition: &BackendDefinition, depth: u64) -> Snapshot {
    let initial = pattern(
        definition,
        r#"k{}(kseq{}(head{}(\dv{SortInt{}}("0")), dotk{}()))"#,
    );
    let before = snapshot();
    let result = execute(
        definition,
        initial,
        ExecutionOptions {
            max_depth: depth,
            ..ExecutionOptions::default()
        },
    );
    let delta = snapshot().delta(&before);
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(result.leaves[0].depth, depth);
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(definition, &expected_state(depth)).term
    );
    delta
}

/// The work of the one extra step between depth `depth` and `depth + 1`.
fn one_step(definition: &BackendDefinition, depth: u64) -> Snapshot {
    let at = execute_k_growth(definition, depth);
    let next = execute_k_growth(definition, depth + 1);
    next.delta(&at)
}

#[test]
fn k_growth_constructed_terms_per_step_stay_flat_as_the_k_cell_grows() {
    let definition = definition(K_GROWTH);
    let early = one_step(&definition, 8);
    let late = one_step(&definition, 64);
    for counter in [
        Counter::RewriteSteps,
        Counter::RewriteRuleAttempts,
        Counter::RewriteRulesApplied,
        Counter::MatchingPairs,
        Counter::SimplifyRounds,
        Counter::SimplifyEquationAttempts,
        Counter::TermConstructed,
    ] {
        eprintln!(
            "{}: step 8->9 = {}, step 64->65 = {}",
            counter.name(),
            early.get(counter),
            late.get(counter)
        );
    }
    assert_eq!(early.get(Counter::RewriteSteps), 1);
    assert_eq!(late.get(Counter::RewriteSteps), 1);
    assert_eq!(early.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(late.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(late.get(Counter::SmtQueries), 0);
    // Matching and simplification rounds are already flat; construction is what grows today.
    assert!(late.get(Counter::MatchingPairs) <= early.get(Counter::MatchingPairs) + STEP_SLACK);
    assert!(late.get(Counter::SimplifyRounds) <= early.get(Counter::SimplifyRounds) + STEP_SLACK);
    assert!(
        late.get(Counter::TermConstructed) <= early.get(Counter::TermConstructed) + STEP_SLACK,
        "term.constructed per step: {} at depth 64 versus {} at depth 8",
        late.get(Counter::TermConstructed),
        early.get(Counter::TermConstructed)
    );
}

#[test]
fn k_growth_total_construction_grows_at_most_linearly_with_depth() {
    let definition = definition(K_GROWTH);
    let at_32 = execute_k_growth(&definition, 32);
    let at_64 = execute_k_growth(&definition, 64);
    eprintln!(
        "term.constructed: {} at depth 32, {} at depth 64",
        at_32.get(Counter::TermConstructed),
        at_64.get(Counter::TermConstructed)
    );
    assert!(
        at_64.get(Counter::TermConstructed) <= 2 * at_32.get(Counter::TermConstructed) + 16,
        "{} constructed terms at depth 64 versus {} at depth 32",
        at_64.get(Counter::TermConstructed),
        at_32.get(Counter::TermConstructed)
    );
}
