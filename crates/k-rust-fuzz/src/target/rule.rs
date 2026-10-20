//! Rule targets: resolution against the backend's rule catalog and the per-mode reach judgement
//! (ARCHITECTURE 4.2).
//!
//! A rule target is judged by the id the catalog gives the rule, so the id must name that rule's
//! steps and nothing else. Coverage and traces record ids, not sentences: an id shared by two
//! entries, the generated id `UNKNOWN`, or a non-executable entry would let coverage of another
//! sentence, or of no step at all, count as reaching the target. An equation's id is in coverage
//! `applied` whenever a rewrite rule's load-time definedness discharge used it, which the run
//! never evaluated (`kb/coverage.rs:15-19`, `:71-72`), so equation targets are refused in M1.

use std::collections::BTreeSet;

use k_rust::backend::{CompiledRuleKind, CompiledRuleOutput, HaltReasonOutput, RunCoverageOutput};

use super::{RuleMode, RuleRef};
use crate::{
    error::TargetProblem,
    exec::{CaseResult, TargetNeeds},
};

/// Resolve `rule` to the unique id of one catalog entry, refusing the entries whose coverage may
/// come from another sentence or from use the run never made (ARCHITECTURE 4.2).
///
/// - `Label` matches the entry whose label is the given text; when none is, the entries whose
///   label is `<module>.<text>`, so `div` names `RULES.div` when no other module has a `div`.
/// - `UniqueId` matches the entries with that id.
/// - `Source` matches the entries with an origin written in that source (the catalog's
///   `Source(path)` text, the path inside it, or a suffix of that path at a `/`) whose location
///   starts on that line.
///
/// Entries matching one reference that carry different ids are an ambiguity; entries that carry
/// one id are that id's entries, which `shared_identity` flags when there are several.
pub(crate) fn resolve_rule(
    catalog: &[CompiledRuleOutput],
    rule: &RuleRef,
) -> Result<String, TargetProblem> {
    let matching: Vec<&CompiledRuleOutput> = match rule {
        RuleRef::Label(label) => {
            let exact: Vec<_> = catalog
                .iter()
                .filter(|entry| entry.label.as_deref() == Some(label.as_str()))
                .collect();
            if exact.is_empty() {
                catalog
                    .iter()
                    .filter(|entry| {
                        entry.label.as_deref().is_some_and(|written| {
                            written
                                .strip_suffix(label.as_str())
                                .is_some_and(|module| module.ends_with('.'))
                        })
                    })
                    .collect()
            } else {
                exact
            }
        }
        RuleRef::UniqueId(id) => catalog.iter().filter(|entry| entry.id == *id).collect(),
        RuleRef::Source { source, line } => catalog
            .iter()
            .filter(|entry| {
                entry.origins.iter().any(|origin| {
                    origin
                        .source
                        .as_deref()
                        .is_some_and(|written| source_matches(written, source))
                        && origin
                            .location
                            .as_deref()
                            .and_then(start_line)
                            .is_some_and(|start| start == *line)
                })
            })
            .collect(),
    };
    let ids: BTreeSet<&str> = matching.iter().map(|entry| entry.id.as_str()).collect();
    if ids.len() > 1 {
        return Err(TargetProblem::AmbiguousRule(
            ids.into_iter().map(str::to_owned).collect(),
        ));
    }
    let Some(entry) = matching.first() else {
        return Err(TargetProblem::UnknownRule);
    };
    if entry.id == "UNKNOWN" {
        return Err(TargetProblem::UnknownId);
    }
    if entry.shared_identity || matching.len() > 1 {
        return Err(TargetProblem::SharedIdentity);
    }
    if !entry.executable {
        return Err(TargetProblem::NotExecutable);
    }
    if entry.kind != CompiledRuleKind::Rewrite {
        return Err(TargetProblem::Equation);
    }
    Ok(entry.id.clone())
}

/// Whether the catalog's source text `written` (`Source(path)`) names the source `given`: the
/// text itself, its path, or a suffix of the path that starts after a `/`.
fn source_matches(written: &str, given: &str) -> bool {
    let path = written
        .strip_prefix("Source(")
        .and_then(|path| path.strip_suffix(')'))
        .unwrap_or(written);
    written == given
        || path == given
        || path
            .strip_suffix(given)
            .is_some_and(|directory| directory.ends_with('/'))
}

/// The first line of a catalog location `Location(start_line,start_column,end_line,end_column)`.
fn start_line(location: &str) -> Option<u32> {
    let numbers = location.strip_prefix("Location(")?.strip_suffix(')')?;
    let mut parts = numbers.split(',').map(|part| part.trim().parse::<u32>());
    let line = parts.next()?.ok()?;
    (parts.count() == 3).then_some(line)
}

/// What every request of a rule target needs (ARCHITECTURE 5.1).
///
/// `fired` without run-to-completion makes the rule the request's only terminal rule: a path
/// ends where the rule fires, so its `terminal` leaf is that firing's successor and names the
/// rule without a trace (T-14). Under run-to-completion the path continues past the firing, so
/// the leaf's trace is asked for. The coverage modes read coverage, which every request
/// collects.
pub(crate) fn rule_needs(id: &str, mode: RuleMode, run_to_completion: bool) -> TargetNeeds {
    match (mode, run_to_completion) {
        (RuleMode::Fired, false) => TargetNeeds {
            terminal_rules: vec![id.to_owned()],
            ..TargetNeeds::default()
        },
        (RuleMode::Fired, true) => TargetNeeds {
            trace: true,
            ..TargetNeeds::default()
        },
        (RuleMode::Covered | RuleMode::ConditionReached, _) => TargetNeeds::default(),
    }
}

/// For each leaf of `result`, whether it reaches the rule `id` in `mode` (ARCHITECTURE 4.2).
///
/// - `fired`: the leaf's trace has a `Rewrite` entry of the rule, or, without run-to-completion,
///   the leaf halted `terminal`, which only the target's rule can cause because it is the
///   request's only terminal rule ([`rule_needs`]).
/// - `covered` and `condition-reached`: the run's coverage `applied`, respectively `matched`,
///   holds the rule. Coverage is a fact of the whole run, not of one leaf (ARCHITECTURE 5.3,
///   D13). A run with one leaf is that leaf's path, so the leaf reaches the target exactly when
///   the coverage holds the rule. A run with several leaves (all paths, or several right-hand
///   side alternatives on one path) cannot attribute its coverage to one of them, so a hit may
///   rest on none of them unless every leaf could carry it: when every leaf qualifies (it is
///   clean and, under run-to-completion, a natural end) every leaf reaches; otherwise only the
///   leaves that do not qualify do, which is "reached on a leaf that cannot carry a hit" for
///   [`crate::exec::classify`] and never a hit.
///
/// Whether the leaf is clean is not decided here: a reaching leaf that is not clean is
/// classified, never a hit (ARCHITECTURE 5.3).
pub(crate) fn rule_reached(
    id: &str,
    mode: RuleMode,
    run_to_completion: bool,
    result: &CaseResult,
) -> Vec<bool> {
    let covered = |list: fn(&RunCoverageOutput) -> &Vec<String>| {
        result
            .coverage
            .as_ref()
            .is_some_and(|coverage| list(coverage).iter().any(|entry| entry == id))
    };
    match mode {
        RuleMode::Fired => result
            .leaves
            .iter()
            .map(|leaf| {
                leaf.rewrites.iter().any(|entry| entry == id)
                    || (!run_to_completion && leaf.halt == HaltReasonOutput::Terminal)
            })
            .collect(),
        RuleMode::Covered => run_reached(
            covered(|coverage| &coverage.applied),
            run_to_completion,
            result,
        ),
        RuleMode::ConditionReached => run_reached(
            covered(|coverage| &coverage.matched),
            run_to_completion,
            result,
        ),
    }
}

/// The per-leaf reach of a run-level fact `holds` (ARCHITECTURE 5.3, D13); see
/// [`rule_reached`].
fn run_reached(holds: bool, run_to_completion: bool, result: &CaseResult) -> Vec<bool> {
    if !holds {
        return vec![false; result.leaves.len()];
    }
    if result.leaves.len() <= 1 {
        return vec![true; result.leaves.len()];
    }
    let qualifies: Vec<bool> = result
        .leaves
        .iter()
        .map(|leaf| leaf.is_clean() && (!run_to_completion || leaf.natural_end))
        .collect();
    if qualifies.iter().all(|qualifies| *qualifies) {
        qualifies
    } else {
        qualifies.into_iter().map(|qualifies| !qualifies).collect()
    }
}

/// The rule's condition was entered and it built no successor: in coverage `matched`, not in
/// `applied` (ARCHITECTURE 6.2). `false` without coverage.
pub(crate) fn blocked(id: &str, coverage: Option<&RunCoverageOutput>) -> bool {
    coverage.is_some_and(|coverage| {
        coverage.matched.iter().any(|entry| entry == id)
            && !coverage.applied.iter().any(|entry| entry == id)
    })
}
