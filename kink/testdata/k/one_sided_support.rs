//! Re-pin L1-2-fix-1 (L1-2 review minor 2): the explanation a one-sided kill must have when the
//! unbounded two-sided run of the same mutant and test does not compare.
//!
//! The one-sided rule reads a clean, ground, stuck leaf `L` of a work-bound mutant run that the
//! baseline's complete set lacks. The principle is per path (Sebastien, 2026-10-17; root README,
//! "What a kill trusts"): a contradiction or a non-value terminal on another path of the mutant
//! run does not void `L`, one on `L`'s own path does. So where the unbounded run is `unknown`, a
//! one-sided kill is explained only when that run finished (no timeout, no stack stop, no bound,
//! no undecided or diagnosed leaf), its incompleteness is a contradicted claim or a terminal that
//! is not a value, each on a leaf other than the killing one, and every candidate killing leaf of
//! the bounded run is a clean stuck leaf of the unbounded run with the same decided value.
#![allow(dead_code)]

use k_rust::backend::{Backend, BackendError, BackendOptions};
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_campaign::{ExecutionFailureKind, OracleOutcome, TestRun};
use kink_native::ValidatedDefinition;
use kink_native::bridge::{BridgeContext, paths_from_execution_values, work_bound_stuck_terminals};
use kink_native::exclusion::DefinitionExclusions;
use kink_native::execution::{
    AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality, ResultRun,
    SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_pattern::{ExecutionTerminalKind, SymbolSorts};

/// Why the unbounded run of an explained one-sided kill does not compare, leaf by leaf, and the
/// killing leaves, each as `leaf:<ordinal of the unbounded run>`.
#[derive(Debug)]
pub struct Explanation {
    /// Every leaf of the unbounded run that makes it incomplete or no evidence: `leaf:<i>
    /// contradicted <symbol>`, `leaf:<i> undefined step (contradicted-claim run)` or `leaf:<i>
    /// not a value`.
    pub offenders: Vec<String>,
    /// The unbounded run's leaves that the bounded run's candidate killing leaves are.
    pub killing: Vec<String>,
}

fn diagnosed(leaf: &AdaptedLeaf) -> bool {
    // Re-pin probe P-1 (k-rust 58720d2e5; KINK-18/2, head 16e88a6d4, merge 7d4c588f9; k-rust's
    // draft answers-add3 section 2.1 "Contradicted claims"): a leaf whose step is undefined
    // through a contradicted `total` claim now also carries that claim's `contradicted-claim`
    // record as a diagnostic. The record restates the leaf's own `contradicted_total`, which the
    // explanation reads as that leaf's offence, so it is not read as another diagnosis; any other
    // diagnostic, a record of another claim or symbol included, still is.
    let restates_contradicted_total = |diagnostic: &k_rust::backend::BackendDiagnosticOutput| {
        matches!(
            diagnostic,
            k_rust::backend::BackendDiagnosticOutput::ContradictedClaim(record)
                if record.claim == k_rust::backend::ContradictedClaimKind::Total
                    && leaf
                        .contradicted_total
                        .as_ref()
                        .is_some_and(|total| record.symbol.as_ref() == Some(&total.symbol))
        )
    };
    leaf.diagnostics
        .iter()
        .any(|diagnostic| !restates_contradicted_total(diagnostic))
        || leaf
            .candidate_diagnostics
            .iter()
            .any(|diagnostics| !diagnostics.is_empty())
        || !leaf.remainder_diagnostics.is_empty()
}

fn ordinal(key: Option<&str>) -> Option<usize> {
    key?.strip_prefix("leaf:")?.parse().ok()
}

/// Explains the one-sided kill of slot `slot` of the test `initial` on the claim-free mutant
/// `compiled` (its main module `module`, encoded) under the work budget `max_work`, whose
/// unbounded two-sided run was `unbounded` (with `slot`, one argument); `Err` says what is not explained. It re-runs both
/// runs as the campaign runner does (state sets, whatever their leaves) and bridges them with the
/// mutant's own decider.
pub fn explain_one_sided_kill(
    compiled: &ValidatedDefinition,
    module: &str,
    initial: &Pattern,
    budget: ExecutionBudget,
    max_work: u64,
    (unbounded, slot): (&TestRun, usize),
    classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind,
) -> Result<Explanation, String> {
    let contradicted_run = match unbounded {
        TestRun::Failed(ExecutionFailureKind::ContradictedClaim) => true,
        TestRun::Compared(outcomes) if outcomes.get(slot) == Some(&OracleOutcome::Unknown) => false,
        other => return Err(format!("the unbounded run is {other:?}, not unknown")),
    };
    let kore = &compiled.artifacts().definition_kore;
    let sorts = SymbolSorts::from_definition(&parse_definition(kore).map_err(|e| e.to_string())?);
    let collections_trusted =
        DefinitionExclusions::of_validated(compiled, module)?.collections_trusted();
    let mut backend = Backend::new(kore, module.to_owned(), BackendOptions::default())
        .map_err(|e| e.to_string())?;
    let adapter = ExecutionAdapter::with_profile(SolverProfile::of(&backend));
    let mut run = |max_work| {
        adapter
            .execute_result(
                &mut backend,
                initial,
                budget,
                ResultRun {
                    modality: ResultModality::StateSet,
                    max_work,
                },
            )
            .map_err(|e| format!("{e:?}"))
    };
    let full = run(None)?;
    let bounded = run(Some(max_work))?;
    if full.timed_out() || full.stack_stops() != 0 {
        return Err(format!(
            "the unbounded run timed out ({}) or met stack stops ({})",
            full.timed_out(),
            full.stack_stops()
        ));
    }
    if let Some((index, leaf)) = full.leaves().iter().enumerate().find(|(_, leaf)| {
        diagnosed(leaf)
            || !matches!(
                leaf.halt,
                HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
            )
    }) {
        return Err(format!(
            "unbounded leaf:{index} is {:?} (diagnosed: {})",
            leaf.halt,
            diagnosed(leaf)
        ));
    }
    let context = BridgeContext {
        test_id: "explain",
        classify,
        sorts: &sorts,
    };
    let (paths, killing) = backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(initial))
                    .trusting_collections(collections_trusted);
            let value = |term: &Pattern| decider.terminal_value(term);
            Ok::<_, BackendError>((
                paths_from_execution_values(&full, &context, &value),
                work_bound_stuck_terminals(&bounded, &context, &value),
            ))
        })
        .map_err(|e| e.to_string())?;
    let paths = paths.map_err(|e| format!("the unbounded run does not bridge: {e:?}"))?;
    let mut offenders = Vec::new();
    for (index, leaf) in full.leaves().iter().enumerate() {
        if let Some(claim) = &leaf.contradicted_total {
            offenders.push(format!("leaf:{index} contradicted {}", claim.symbol));
        } else if leaf.halt == HaltClass::Trivial && contradicted_run {
            offenders.push(format!(
                "leaf:{index} undefined step (contradicted-claim run)"
            ));
        }
    }
    for path in paths.paths.iter().filter(|path| !path.complete) {
        let index = ordinal(path.path_key.as_deref()).ok_or("an unkeyed path")?;
        // Re-pin probe P-1 (k-rust 58720d2e5; KINK-18/2, see `diagnosed`): the contradicted
        // leaf's `contradicted-claim` record makes its bridged path an incomplete `BackendLimit`
        // one; that incompleteness is the contradiction already counted above, not another.
        if full.leaves()[index].contradicted_total.is_some() {
            continue;
        }
        if full.leaves()[index].halt != HaltClass::Stuck {
            return Err(format!(
                "unbounded leaf:{index} incomplete: {:?}",
                path.stop
            ));
        }
        offenders.push(format!("leaf:{index} not a value"));
    }
    if offenders.is_empty() {
        return Err("the unbounded run has no contradicted or non-value leaf".into());
    }
    if killing.is_empty() {
        return Err(format!(
            "the bounded run (max_work {max_work}) gives no one-sided terminal"
        ));
    }
    let mut killing_leaves = Vec::new();
    for terminal in &killing {
        let found = paths.paths.iter().find(|path| {
            path.complete
                && path
                    .execution_terminal
                    .as_ref()
                    .is_some_and(|clean| clean.state == terminal.state)
        });
        let Some(index) = found.and_then(|path| ordinal(path.path_key.as_deref())) else {
            return Err(format!(
                "a killing terminal is no complete leaf of the unbounded run: {}",
                terminal.state
            ));
        };
        let leaf = &full.leaves()[index];
        let key = format!("leaf:{index}");
        if leaf.halt != HaltClass::Stuck
            || leaf.contradicted_total.is_some()
            || offenders.iter().any(|offender| {
                offender
                    .split_whitespace()
                    .next()
                    .is_some_and(|at| at == key)
            })
        {
            return Err(format!("the killing {key} is not a clean stuck leaf"));
        }
        killing_leaves.push(key);
    }
    Ok(Explanation {
        offenders,
        killing: killing_leaves,
    })
}
