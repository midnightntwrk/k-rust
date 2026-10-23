//! Rule targets: resolution against the backend's rule catalog and the per-mode reach judgement
//! (ARCHITECTURE 4.2).
//!
//! A rule target is judged by the id the catalog gives the rule, so the id must name that rule's
//! steps and nothing else. Coverage and traces record ids, not sentences: an id shared by two
//! entries, the generated id `UNKNOWN`, or a non-executable entry would let coverage of another
//! sentence, or of no step at all, count as reaching the target. An equation's id is in coverage
//! `applied` whenever a rewrite rule's load-time definedness discharge used it, which the run
//! never evaluated (`kb/coverage.rs:15-19`, `:71-72`), so equation targets are refused in M1.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::{
    CompiledRuleKind, CompiledRuleOriginOutput, CompiledRuleOutput, RunCoverageOutput,
};

use super::{RuleLocation, RuleMode, RuleName, RuleRef, rule_names};
use crate::{
    error::{TargetProblem, UnknownRule},
    exec::{self, CaseResult, TargetNeeds},
};

/// How many candidates a refusal of an unknown reference lists.
const CANDIDATES: usize = 5;

/// Resolve `rule` to the unique id of one catalog entry, refusing the entries whose coverage may
/// come from another sentence or from use the run never made (ARCHITECTURE 4.2).
///
/// - `Label` matches the entry whose label is the given text; when none is, the entries whose
///   label is `<module>.<text>`, so `div` names `RULES.div` when no other module has a `div`.
/// - `UniqueId` matches the entries with that id.
/// - `Source` first resolves its source to exactly one catalog file ([`files_named`]: the
///   whole path; else a suffix of paths after a `/`; else, for an absolute source, the relative
///   paths it ends with), refusing a source that names several files whatever the line
///   ([`TargetProblem::AmbiguousSource`]). It then matches the entries with an origin in that
///   file whose location spans the line, from its first line to its last. A rule is a span of
///   its source
///   and rules do not nest, so a line inside a rule names that rule; two sentences written on
///   one line are an ambiguity. Equal written axioms are one catalog entry with all their
///   origins and one id, so a reference to one position also counts firings of an identical
///   sentence at another position: the two have the same meaning, but a claim about the
///   position names both.
///
/// Entries matching one reference that carry different ids are an ambiguity; entries that carry
/// one id are that id's entries, which `shared_identity` flags when there are several. A
/// reference no entry matches is refused with candidates ([`UnknownRule`]).
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
            let files = catalog_files(catalog);
            match files_named(&files, source)[..] {
                [] => Vec::new(),
                [file] => written_in(catalog, file, Some(*line)),
                ref several => {
                    return Err(TargetProblem::AmbiguousSource {
                        source: source.clone(),
                        files: several
                            .iter()
                            .map(|file| shortest_reference(&files, file))
                            .collect(),
                    });
                }
            }
        }
    };
    let ids: BTreeSet<&str> = matching.iter().map(|entry| entry.id.as_str()).collect();
    if ids.len() > 1 {
        let mut names = rule_names(catalog);
        return Err(TargetProblem::AmbiguousRule(
            ids.into_iter()
                .filter_map(|id| names.remove_entry(id))
                .collect(),
        ));
    }
    let Some(entry) = matching.first() else {
        return Err(TargetProblem::UnknownRule(Box::new(unknown(catalog, rule))));
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

/// The entries of `catalog` with an origin written in the catalog file `file` whose location
/// spans `line`, or with any location when `line` is `None`.
fn written_in<'a>(
    catalog: &'a [CompiledRuleOutput],
    file: &str,
    line: Option<u32>,
) -> Vec<&'a CompiledRuleOutput> {
    catalog
        .iter()
        .filter(|entry| {
            entry.origins.iter().any(|origin| {
                origin_in(origin, file) && line.is_none_or(|line| spans(origin, line))
            })
        })
        .collect()
}

/// Whether `origin` is written in the catalog file `file`.
fn origin_in(origin: &CompiledRuleOriginOutput, file: &str) -> bool {
    origin
        .source
        .as_deref()
        .is_some_and(|written| catalog_path(written) == file)
}

/// Whether `origin`'s location spans `line`.
fn spans(origin: &CompiledRuleOriginOutput, line: u32) -> bool {
    origin
        .location
        .as_deref()
        .and_then(span)
        .is_some_and(|(start, end)| start <= line && line <= end)
}

/// The distinct files `catalog`'s origins are written in, as the catalog records them (the
/// path inside `Source(path)`).
pub(super) fn catalog_files(catalog: &[CompiledRuleOutput]) -> BTreeSet<&str> {
    catalog
        .iter()
        .flat_map(|entry| &entry.origins)
        .filter_map(|origin| origin.source.as_deref().map(catalog_path))
        .collect()
}

/// The files of `files` (catalog paths) that the source `given` names, in path order:
/// - the file whose path is `given`, or whose `Source(path)` text is: a whole path names its
///   file alone;
/// - failing that, every file whose path ends with `given` right after a `/`;
/// - failing that, for an absolute `given`, every relative path that `given` ends with right
///   after a `/` (the compiler recorded it relative to where it ran).
///
/// More than one file is an ambiguity of the reference, whatever line it names: the line of a
/// rule in one file may be a comment or lie between rules in the other.
pub(super) fn files_named<'a>(files: &BTreeSet<&'a str>, given: &str) -> Vec<&'a str> {
    let exact: Vec<&str> = files
        .iter()
        .copied()
        .filter(|path| *path == given || format!("Source({path})") == given)
        .collect();
    if !exact.is_empty() {
        return exact;
    }
    let suffix: Vec<&str> = files
        .iter()
        .copied()
        .filter(|path| ends_at_directory(path, given))
        .collect();
    if !suffix.is_empty() || !given.starts_with('/') {
        return suffix;
    }
    files
        .iter()
        .copied()
        .filter(|path| !path.starts_with('/') && ends_at_directory(given, path))
        .collect()
}

/// The shortest reference to the catalog file `path` that names it alone among `files`
/// ([`files_named`]): its shortest suffix that starts after a `/`, or the whole path.
pub(super) fn shortest_reference(files: &BTreeSet<&str>, path: &str) -> String {
    path.char_indices()
        .filter(|(_, character)| *character == '/')
        .map(|(index, _)| &path[index + 1..])
        .filter(|suffix| !suffix.is_empty())
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .find(|suffix| files_named(files, suffix) == [path])
        .unwrap_or(path)
        .to_owned()
}

/// What `catalog` offers in place of `rule`, which no entry matches ([`UnknownRule`]).
fn unknown(catalog: &[CompiledRuleOutput], rule: &RuleRef) -> UnknownRule {
    let names = rule_names(catalog);
    let with_names = |ids: Vec<&str>| -> Vec<(String, RuleName)> {
        let mut seen = BTreeSet::new();
        ids.into_iter()
            .filter(|id| seen.insert(*id))
            .filter_map(|id| names.get(id).map(|name| (id.to_owned(), name.clone())))
            .take(CANDIDATES)
            .collect()
    };
    let starting_with = |prefix: &str| -> Vec<&str> {
        let prefix = prefix.to_ascii_lowercase();
        names
            .keys()
            .filter(|id| !prefix.is_empty() && id.starts_with(&prefix))
            .map(String::as_str)
            .collect()
    };
    let mut unknown = UnknownRule {
        reference: rule.clone(),
        candidates: Vec::new(),
        unlabelled: 0,
        sources: Vec::new(),
    };
    match rule {
        RuleRef::Label(label) => {
            let mut near: Vec<(usize, &str, &str)> = catalog
                .iter()
                .filter_map(|entry| {
                    let written = entry.label.as_deref()?;
                    let distance = label_distance(label, written)?;
                    Some((distance, written, entry.id.as_str()))
                })
                .collect();
            near.sort_unstable();
            let mut ids: Vec<&str> = near.into_iter().map(|(_, _, id)| id).collect();
            // An id cut short (`5ac0f147`) is not a label; the ids it starts.
            if label.len() >= 4 && label.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                ids.extend(starting_with(label));
            }
            unknown.candidates = with_names(ids);
            unknown.unlabelled = catalog
                .iter()
                .filter(|entry| {
                    entry.kind == CompiledRuleKind::Rewrite
                        && entry.executable
                        && entry.label.is_none()
                        && entry.id != "UNKNOWN"
                })
                .map(|entry| entry.id.as_str())
                .collect::<BTreeSet<_>>()
                .len();
        }
        RuleRef::UniqueId(id) => unknown.candidates = with_names(starting_with(id)),
        RuleRef::Source { source, line } => {
            let files = catalog_files(catalog);
            let in_files = files_named(&files, source);
            if in_files.is_empty() {
                unknown.sources = catalog
                    .iter()
                    .filter(|entry| entry.kind == CompiledRuleKind::Rewrite)
                    .flat_map(|entry| &entry.origins)
                    .filter_map(|origin| origin.source.as_deref().map(catalog_path))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .map(|path| shortest_reference(&files, path))
                    .collect();
            } else {
                // The entries written nearest the line, listed in the order they are written.
                let mut near: Vec<(u32, u32, &str)> = catalog
                    .iter()
                    .filter_map(|entry| {
                        entry
                            .origins
                            .iter()
                            .filter(|origin| in_files.iter().any(|file| origin_in(origin, file)))
                            .filter_map(|origin| origin.location.as_deref().and_then(span))
                            .map(|(start, end)| {
                                let distance = if *line < start {
                                    start - line
                                } else {
                                    line.saturating_sub(end)
                                };
                                (distance, start, entry.id.as_str())
                            })
                            .min()
                    })
                    .collect();
                near.sort_unstable();
                near.truncate(CANDIDATES);
                near.sort_unstable_by_key(|(_, start, id)| (*start, *id));
                unknown.candidates = with_names(near.into_iter().map(|(_, _, id)| id).collect());
            }
        }
    }
    unknown
}

/// How far the label `given` is from the catalog label `written`, when it is near enough to
/// list: the edit distance, ignoring case, to `written` or to `written` without its module,
/// when it is at most a third of the given label's length (at least 2), or 0 when the label
/// contains the given text or the given text contains the label without its module (of three
/// characters or more).
fn label_distance(given: &str, written: &str) -> Option<usize> {
    let given = given.to_lowercase();
    let written = written.to_lowercase();
    let bare = written
        .split_once('.')
        .map_or(written.as_str(), |(_, bare)| bare);
    if !given.is_empty() && (written.contains(&given) || bare.len() >= 3 && given.contains(bare)) {
        return Some(0);
    }
    let distance = edit_distance(&given, &written).min(edit_distance(&given, bare));
    (distance <= (given.chars().count() / 3).max(2)).then_some(distance)
}

/// The Levenshtein distance between `left` and `right`, by characters.
fn edit_distance(left: &str, right: &str) -> usize {
    let right: Vec<char> = right.chars().collect();
    let mut previous: Vec<usize> = (0..=right.len()).collect();
    for (row, left) in left.chars().enumerate() {
        let mut current = Vec::with_capacity(right.len() + 1);
        current.push(row + 1);
        for (column, right) in right.iter().enumerate() {
            let substitution = previous[column] + usize::from(left != *right);
            current.push(
                substitution
                    .min(previous[column + 1] + 1)
                    .min(current[column] + 1),
            );
        }
        previous = current;
    }
    previous[right.len()]
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

/// The first and last lines of a catalog location
/// `Location(start_line,start_column,end_line,end_column)`; a last line before the first is
/// read as the first.
fn span(location: &str) -> Option<(u32, u32)> {
    let numbers = location.strip_prefix("Location(")?.strip_suffix(')')?;
    let parts = numbers
        .split(',')
        .map(|part| part.trim().parse::<u32>().ok())
        .collect::<Option<Vec<u32>>>()?;
    let [start, _, end, _] = parts[..] else {
        return None;
    };
    Some((start, end.max(start)))
}

/// The source locations of `entry`'s origins ([`RuleLocation`]), each file's reference taken
/// from `references` (catalog path to [`shortest_reference`]).
pub(super) fn locations(
    entry: &CompiledRuleOutput,
    references: &BTreeMap<&str, String>,
) -> Vec<RuleLocation> {
    entry
        .origins
        .iter()
        .filter_map(|origin| {
            let (line, end_line) = origin.location.as_deref().and_then(span)?;
            let source = catalog_path(origin.source.as_deref()?);
            Some(RuleLocation {
                source: source.to_owned(),
                reference: references
                    .get(source)
                    .cloned()
                    .unwrap_or_else(|| source.to_owned()),
                line,
                end_line,
            })
        })
        .collect()
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
#[cfg(test)]
pub(crate) fn rule_reached(
    id: &str,
    mode: RuleMode,
    run_to_completion: bool,
    result: &CaseResult,
) -> Vec<bool> {
    rule_reached_ends(id, mode, run_to_completion, false, result)
}

/// [`rule_reached`], where under `run_to_completion` and `data_end` a leaf qualifies to carry a
/// run-level coverage fact only when its end is also data ([`crate::Target::data_end`]).
pub(crate) fn rule_reached_ends(
    id: &str,
    mode: RuleMode,
    run_to_completion: bool,
    data_end: bool,
    result: &CaseResult,
) -> Vec<bool> {
    let qualifies = |leaf: &crate::exec::LeafReport| {
        leaf.is_clean()
            && (!run_to_completion
                || (leaf.natural_end && (!data_end || leaf.data_end == Some(true))))
    };
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
        RuleMode::Covered => {
            run_reached(id, covered(|coverage| &coverage.applied), qualifies, result)
        }
        RuleMode::ConditionReached => {
            run_reached(id, covered(|coverage| &coverage.matched), qualifies, result)
        }
    }
}

/// The per-leaf reach of a run-level fact `holds` about the rule `id` (ARCHITECTURE 5.3, D13);
/// see [`rule_reached`], which also states why a stopped leaf reaches only from its rewrites.
/// A leaf `qualifies` when it could carry a hit.
fn run_reached(
    id: &str,
    holds: bool,
    qualifies: impl Fn(&crate::exec::LeafReport) -> bool,
    result: &CaseResult,
) -> Vec<bool> {
    let from_coverage = if !holds {
        vec![false; result.leaves.len()]
    } else if result.leaves.len() <= 1 {
        vec![true; result.leaves.len()]
    } else {
        let qualifies: Vec<bool> = result.leaves.iter().map(qualifies).collect();
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
