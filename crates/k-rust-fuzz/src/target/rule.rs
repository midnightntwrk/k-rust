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

use k_rust::backend::{CompiledRuleKind, CompiledRuleOutput, RunCoverageOutput};

use super::{RuleMode, RuleRef};
use crate::{
    error::TargetProblem,
    exec::{self, CaseResult, TargetNeeds},
};

/// Resolve `rule` to the unique id of one catalog entry, refusing the entries whose coverage may
/// come from another sentence or from use the run never made (ARCHITECTURE 4.2).
///
/// - `Label` matches the entry whose label is the given text; when none is, the entries whose
///   label is `<module>.<text>`, so `div` names `RULES.div` when no other module has a `div`.
/// - `UniqueId` matches the entries with that id.
/// - `Source` matches the entries with an origin written in that source (the catalog's
///   `Source(path)` text, the path inside it, or a suffix of that path at a `/`; failing all
///   of those, an absolute path that ends with `/` and the catalog's relative path) whose
///   location starts on that line. Equal written axioms are one catalog entry with all their origins and one id, so a
///   reference to one position also counts firings of an identical sentence at another
///   position: the two have the same meaning, but a claim about the position names both.
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
        RuleRef::Source { source, line } => {
            let at = |matches: fn(&str, &str) -> bool| -> Vec<&CompiledRuleOutput> {
                catalog
                    .iter()
                    .filter(|entry| {
                        entry.origins.iter().any(|origin| {
                            origin
                                .source
                                .as_deref()
                                .is_some_and(|written| matches(catalog_path(written), source))
                                && origin
                                    .location
                                    .as_deref()
                                    .and_then(start_line)
                                    .is_some_and(|start| start == *line)
                        })
                    })
                    .collect()
            };
            let named = at(source_names);
            if named.is_empty() && source.starts_with('/') {
                at(absolute_source_names)
            } else {
                named
            }
        }
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
    // The permanent refusal first: an equation stays refused in M1 whatever its attributes.
    if entry.kind != CompiledRuleKind::Rewrite {
        return Err(TargetProblem::Equation);
    }
    if entry.id == "UNKNOWN" {
        return Err(TargetProblem::UnknownId);
    }
    if entry.shared_identity || matching.len() > 1 {
        return Err(TargetProblem::SharedIdentity);
    }
    if !entry.executable {
        return Err(TargetProblem::NotExecutable);
    }
    Ok(entry.id.clone())
}

/// The path inside the catalog's source text `Source(path)`, or the text itself.
fn catalog_path(written: &str) -> &str {
    written
        .strip_prefix("Source(")
        .and_then(|path| path.strip_suffix(')'))
        .unwrap_or(written)
}

/// `long` ends with `short` right after a `/`.
fn ends_at_directory(long: &str, short: &str) -> bool {
    long.strip_suffix(short)
        .is_some_and(|rest| rest.ends_with('/'))
}

/// Whether the catalog path `path` is the source `given`: the same path, its `Source(path)`
/// text, or `given` is a suffix of it that starts after a `/`.
fn source_names(path: &str, given: &str) -> bool {
    path == given || format!("Source({path})") == given || ends_at_directory(path, given)
}

/// Whether the relative catalog path `path` is the absolute source `given`: `given` ends with
/// `/` and `path`, which the compiler recorded relative to where it ran. Used only when no entry
/// is [`source_names`]' match, so a relative `lib/rules.k` never names `Source(rules.k)`.
fn absolute_source_names(path: &str, given: &str) -> bool {
    !path.starts_with('/') && ends_at_directory(given, path)
}

/// The first line of a catalog location `Location(start_line,start_column,end_line,end_column)`.
fn start_line(location: &str) -> Option<u32> {
    let numbers = location.strip_prefix("Location(")?.strip_suffix(')')?;
    let mut parts = numbers.split(',').map(|part| part.trim().parse::<u32>());
    let line = parts.next()?.ok()?;
    (parts.count() == 3).then_some(line)
}

/// What every request of a rule target needs (ARCHITECTURE 5.1, 5.3; D16, D18).
///
/// `fired` is judged from each leaf's trace, so it always asks for traces. Without
/// run-to-completion it also makes the rule the request's only terminal rule, in both path
/// modes, as an early stop: a path whose firing step has a single successor ends there, as a
/// `terminal` leaf whose trace ends with the rule's `Rewrite` entry, so what follows the firing
/// (a loop, a bound, an undefined step) cannot hide it. The backend applies a stop rule only on a
/// step with a single successor, so a firing at a branching step does not stop its path, and the
/// trace finds it. Under all paths the stop rule moves sibling candidates' facts onto the
/// successor, which is conservative. The coverage modes read coverage, which every request
/// collects.
pub(crate) fn rule_needs(id: &str, mode: RuleMode, run_to_completion: bool) -> TargetNeeds {
    match mode {
        RuleMode::Fired => TargetNeeds {
            trace: true,
            terminal_rules: if run_to_completion {
                Vec::new()
            } else {
                vec![id.to_owned()]
            },
            ..TargetNeeds::default()
        },
        RuleMode::Covered | RuleMode::ConditionReached => TargetNeeds::default(),
    }
}

/// For each leaf of `result`, whether it reaches the rule `id` in `mode` (ARCHITECTURE 4.2).
///
/// - `fired`: the leaf's trace has a `Rewrite` entry of the rule. A `terminal` halt decides
///   nothing by itself: the early stop of [`rule_needs`] ends the trace with the rule's entry.
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
/// A `work-bound`, `timeout` or `cancelled` leaf is never marked from coverage, in any mode
/// (`classify`'s cut-leaf contract, review 2 S1). Its state is the stopped, unnormalised state
/// the worklist held, and the step that built it is in coverage although its result may
/// normalize to `\bottom`: that step reached no configuration. Such a leaf reaches only when
/// its [`crate::exec::LeafReport::rewrites`], which leave that step out, hold the rule. A step
/// that applied the rule entered its condition, so this also stands for `matched`. Without
/// traces (the coverage modes ask for none) the list is empty, and the leaf takes its halt's
/// class.
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
            .map(|leaf| leaf.rewrites.iter().any(|entry| entry == id))
            .collect(),
        RuleMode::Covered => run_reached(
            id,
            covered(|coverage| &coverage.applied),
            run_to_completion,
            result,
        ),
        RuleMode::ConditionReached => run_reached(
            id,
            covered(|coverage| &coverage.matched),
            run_to_completion,
            result,
        ),
    }
}

/// The per-leaf reach of a run-level fact `holds` about the rule `id` (ARCHITECTURE 5.3, D13);
/// see [`rule_reached`], which also states why a stopped leaf reaches only from its rewrites.
fn run_reached(id: &str, holds: bool, run_to_completion: bool, result: &CaseResult) -> Vec<bool> {
    let from_coverage = if !holds {
        vec![false; result.leaves.len()]
    } else if result.leaves.len() <= 1 {
        vec![true; result.leaves.len()]
    } else {
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
    };
    result
        .leaves
        .iter()
        .zip(from_coverage)
        .map(|(leaf, from_coverage)| {
            if exec::stopped_state(leaf.halt) {
                leaf.rewrites.iter().any(|entry| entry == id)
            } else {
                from_coverage
            }
        })
        .collect()
}

/// The rule's condition was entered and it built no successor: in coverage `matched`, not in
/// `applied` (ARCHITECTURE 6.2). `false` without coverage.
pub(crate) fn blocked(id: &str, coverage: Option<&RunCoverageOutput>) -> bool {
    coverage.is_some_and(|coverage| {
        coverage.matched.iter().any(|entry| entry == id)
            && !coverage.applied.iter().any(|entry| entry == id)
    })
}
