//! The rule windows family (depth above 1; module documentation of [`crate::coverage`], "Rule
//! windows"): its universe, read from the definition's may-follow graph before any program runs,
//! its items before [`super::derive`] names them, and their derived part.

use super::{
    ARGUED, FIRED, HEATING, RULE, at_of, ids, listed, measure, position, rule_status, without,
};
use crate::results::{BaselineRunner, ProgramRow, ResultClass};
use k_rust::definition::Sentence;
use kink_corpus::admission::AdmissionRefusal;
use kink_native::coverage::MayFollow;
use kink_patch::SentenceRef;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The status of a window some comparable program's run took.
pub const COVERED: &str = "covered";
/// The status of a window no comparable program's run took.
pub const OPEN: &str = "open";
/// The kind of a rule windows item.
pub const WINDOW: &str = "window";

/// The universe of the rule windows family of depth `depth`: the may-follow graph of the
/// specification's authored rewrite rules (kink-native `coverage::may_follow`), restricted to the
/// authored `rule` sentences in the scope every family shares ([`super::scope::Scope`]), and the
/// number of its windows of each length `2..=depth`. Both are functions of the definition and
/// the front end's marks, computed before any program runs.
pub(super) struct Universe {
    graph: MayFollow,
    nodes: BTreeSet<SentenceRef>,
    /// The number of windows of each length from 2, saturating.
    by_length: Vec<u64>,
}

impl Universe {
    /// The universe of `spec` at `depth` under `scope`, or why the definition could not be read.
    pub(super) fn of(
        spec: &crate::admit::AdmittedSpec,
        scope: &super::scope::Scope<'_>,
        depth: usize,
    ) -> Result<Self, String> {
        let definition = spec.definition.as_ref().map_err(Clone::clone)?;
        let authors = kink_native::coverage::RuleAuthors::of(&spec.compiled);
        let graph = kink_native::coverage::may_follow(definition, &authors);
        let nodes = graph
            .sentences()
            .filter(|at| {
                spec.loaded.baseline.sentence(at).is_some_and(|sentence| {
                    matches!(sentence, Sentence::Rule { .. })
                        && scope.excludes(at, sentence).is_none()
                })
            })
            .cloned()
            .collect::<BTreeSet<_>>();
        // The walks of `k` rules from each node, for k = 1, 2, ...: a window is a walk.
        let mut from = nodes
            .iter()
            .map(|at| (at, 1_u64))
            .collect::<BTreeMap<_, _>>();
        let mut by_length = Vec::new();
        for _ in 2..=depth {
            from = nodes
                .iter()
                .map(|at| {
                    let walks = graph
                        .successors(at)
                        .iter()
                        .filter_map(|next| from.get(next))
                        .fold(0_u64, |sum, walks| sum.saturating_add(*walks));
                    (at, walks)
                })
                .collect();
            by_length.push(
                from.values()
                    .fold(0_u64, |sum, walks| sum.saturating_add(*walks)),
            );
        }
        Ok(Self {
            graph,
            nodes,
            by_length,
        })
    }

    /// The number of obligations, saturating.
    pub(super) fn obligations(&self) -> u64 {
        self.by_length
            .iter()
            .fold(0, |sum, count| sum.saturating_add(*count))
    }

    /// The counts by length as words: `2: 12, 3: 40`.
    fn counted(&self) -> String {
        self.by_length
            .iter()
            .enumerate()
            .map(|(index, count)| format!("length {}: {count}", index + 2))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// The refusal of a universe larger than `max` (`[coverage] max_obligations`), with its
    /// counts, or `None`.
    pub(super) fn refusal(&self, max: u64) -> Option<AdmissionRefusal> {
        let obligations = self.obligations();
        (obligations > max).then(|| AdmissionRefusal {
            stage: "coverage".into(),
            reason: "max-obligations".into(),
            detail: format!(
                "the rule windows family has {obligations} obligations ({}; the may-follow graph \
                 has {} rules and {} edges), more than [coverage] max_obligations = {max}: lower \
                 the depth, or raise max_obligations to count them",
                self.counted(),
                self.nodes.len(),
                self.edges(),
            ),
        })
    }

    /// The edges between nodes.
    fn edges(&self) -> usize {
        self.nodes
            .iter()
            .map(|at| {
                self.graph
                    .successors(at)
                    .iter()
                    .filter(|next| self.nodes.contains(*next))
                    .count()
            })
            .sum()
    }
}

/// The value of a sentence a window item names: `{module, index}`.
fn sentence(at: &SentenceRef) -> Value {
    json!({"module": at.module, "index": at.index})
}

/// The rule windows family before [`derive`] (module documentation of [`crate::coverage`], "Rule
/// windows"), from `universe`, the comparable programs' records (`rows`, in manifest order) and
/// the rules family's items as the front end annotated them (`rules`), which give the node order
/// (sentence order) and which single rules are covered (fired).
///
/// Each item is a window of the universe, by length then in the rules' order: its `rules`
/// (`{module, index}` each), its `length`, the comparable programs whose record holds it
/// (`covered_by`) and the others (`uncounted`), whether it is on the frontier (`frontier`: not
/// covered, while the window of its first `length - 1` rules is, a single rule being covered when
/// it fired), and, on the frontier, `pattern`: the configuration a step of its last rule but one
/// can leave that its last rule can match (kink-native `MayFollow::unified`), printed as K, or
/// null where the printer cannot print it. `outside_universe` lists the windows of the rules a
/// comparable program's record holds that the graph does not: the graph is an
/// over-approximation, so the list is empty unless it failed, and its windows are not counted.
pub(super) fn family(
    universe: &Universe,
    depth: usize,
    rows: &[ProgramRow],
    programs: &[crate::manifest::Program],
    rules: &[Value],
    runner: &BaselineRunner<'_>,
) -> Value {
    let order = rules
        .iter()
        .filter(|rule| rule["kind"] != HEATING)
        .filter_map(at_of)
        .filter(|at| universe.nodes.contains(at))
        .collect::<Vec<_>>();
    let fired = rules
        .iter()
        .filter(|rule| rule["kind"] != HEATING && rule_status(rule) == Some(FIRED))
        .filter_map(at_of)
        .collect::<BTreeSet<_>>();
    // Per window the records hold, the comparable programs and then the others.
    let mut taken = BTreeMap::<Vec<SentenceRef>, [Vec<&str>; 2]>::new();
    for (program, row) in programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        let slot = usize::from(!ResultClass::can_kill(&record["class"]));
        for window in record["coverage"]["windows"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let window = window
                .as_array()
                .into_iter()
                .flatten()
                .map(at_of)
                .collect::<Option<Vec<_>>>();
            let Some(window) = window.filter(|window| (2..=depth).contains(&window.len())) else {
                continue;
            };
            let lists = taken.entry(window).or_default();
            if !lists[slot].contains(&program.id.as_str()) {
                lists[slot].push(&program.id);
            }
        }
    }
    // The windows of each length, in the rules' order: a window's extensions follow it.
    let mut items = Vec::new();
    let mut level = order.iter().map(|at| vec![at.clone()]).collect::<Vec<_>>();
    let mut covered_windows = fired
        .iter()
        .map(|at| vec![at.clone()])
        .collect::<BTreeSet<_>>();
    let mut patterns = BTreeMap::<(SentenceRef, SentenceRef), Value>::new();
    let mut universe_windows = BTreeSet::new();
    for _ in 2..=depth {
        let mut next = Vec::new();
        let mut covered_here = BTreeSet::new();
        for prefix in &level {
            let last = prefix.last().expect("a window has a rule");
            for successor in order
                .iter()
                .filter(|at| universe.graph.successors(last).contains(*at))
            {
                let mut window = prefix.clone();
                window.push(successor.clone());
                let [covered_by, uncounted] = taken.get(&window).cloned().unwrap_or_default();
                let covered = !covered_by.is_empty();
                let frontier = !covered && covered_windows.contains(prefix);
                let pattern = if frontier {
                    patterns
                        .entry((last.clone(), successor.clone()))
                        .or_insert_with(|| {
                            universe
                                .graph
                                .unified(last, successor)
                                .map(|pattern| runner.end_reader().print(&pattern, usize::MAX))
                                .filter(|printed| printed["rendering"] == "k")
                                .map_or(Value::Null, |printed| printed["text"].clone())
                        })
                        .clone()
                } else {
                    Value::Null
                };
                if covered {
                    covered_here.insert(window.clone());
                }
                items.push(json!({
                    "kind": WINDOW,
                    "length": window.len(),
                    "rules": window.iter().map(sentence).collect::<Vec<_>>(),
                    "covered_by": covered_by,
                    "uncounted": uncounted,
                    "frontier": frontier,
                    "pattern": pattern,
                }));
                universe_windows.insert(window.clone());
                next.push(window);
            }
        }
        covered_windows = covered_here;
        level = next;
    }
    let outside = taken
        .iter()
        .filter(|(window, lists)| {
            !lists[0].is_empty()
                && window.iter().all(|at| universe.nodes.contains(at))
                && !universe_windows.contains(*window)
        })
        .map(|(window, lists)| {
            json!({
                "rules": window.iter().map(sentence).collect::<Vec<_>>(),
                "covered_by": lists[0],
            })
        })
        .collect::<Vec<_>>();
    json!({
        "tier": 1,
        "depth": depth,
        "nodes": universe.nodes.len(),
        "edges": universe.edges(),
        "items": items,
        "outside_universe": outside,
    })
}

/// The rule windows family of a document whose definition could not be read: no universe, and
/// why.
pub(super) fn unread(depth: usize, reason: &str) -> Value {
    json!({"tier": 1, "depth": depth, "items": [], "outside_universe": [], "reason": reason})
}

/// What [`derive`] gives the document's derivation: `(covered, obligations)` (`None` without a
/// universe) and the family's targets, in item order.
pub(super) struct Derived {
    pub(super) counts: Option<(usize, usize)>,
    pub(super) targets: Vec<Value>,
}

/// Fill the derived part of the rule windows family `family` ([`family`]): each item's `id`
/// (`window:<rule>,<rule>,...`, each rule by the name its id gives it), `rule_ids`, `status`,
/// `obligation`, `covered` and `touched_only_by`, the counts and the measure, and a target per
/// open window on the frontier. `rules` are the rules family's items as [`super::derive`] named
/// them, `argued` the `[[coverage.argued]]` entries.
///
/// A window no entry names, whose sub-window (a contiguous part of it, a single rule included) an
/// entry argues while no program covers it, is `argued` too, with `argued_by` naming that item:
/// a path that takes the window takes each of its parts as consecutive steps, so the argument that
/// no path takes the part is one that no path takes the window.
pub(super) fn derive(
    family: &mut Value,
    rules: &[Value],
    argued: &BTreeMap<String, String>,
) -> Derived {
    let none = Derived {
        counts: None,
        targets: Vec::new(),
    };
    if !family.is_object() {
        return none;
    }
    let by_sentence = rules
        .iter()
        .filter(|rule| rule["kind"] == RULE)
        .filter_map(|rule| Some((at_of(rule)?, rule)))
        .collect::<BTreeMap<_, _>>();
    // A rule argued while open: the windows that contain it are argued by it.
    let argued_rules = by_sentence
        .iter()
        .filter_map(|(at, rule)| {
            let id = rule["id"].as_str()?;
            (rule["covered"] == false && argued.contains_key(id)).then(|| (at.clone(), id))
        })
        .collect::<BTreeMap<_, _>>();
    let Some(items) = family.get_mut("items").and_then(Value::as_array_mut) else {
        return none;
    };
    let mut targets = Vec::new();
    let mut by_length = BTreeMap::<u64, [usize; 2]>::new();
    let mut covered_count = 0;
    let mut frontier_count = 0;
    // The windows argued while open, by their sentences.
    let mut argued_windows = BTreeMap::<Vec<SentenceRef>, String>::new();
    for item in items.iter_mut() {
        let window = item["rules"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(at_of)
            .collect::<Vec<_>>();
        let names = window
            .iter()
            .map(|at| {
                by_sentence
                    .get(at)
                    .and_then(|rule| rule["id"].as_str())
                    .map_or_else(
                        || format!("{}#{}", at.module, at.index),
                        |id| id.strip_prefix("rule:").unwrap_or(id).to_owned(),
                    )
            })
            .collect::<Vec<_>>();
        let id = format!("window:{}", names.join(","));
        let covered_by = ids(&item["covered_by"]);
        let covered = !covered_by.is_empty();
        let length = item["length"].as_u64().unwrap_or(0);
        let counts = by_length.entry(length).or_default();
        counts[0] += 1;
        counts[1] += usize::from(covered);
        covered_count += usize::from(covered);
        if let Some(object) = item.as_object_mut() {
            for derived in [
                "argument",
                "argument_needless",
                "unargued_status",
                "argued_by",
            ] {
                object.remove(derived);
            }
        }
        item["id"] = json!(id);
        item["rule_ids"] = json!(
            names
                .iter()
                .map(|name| format!("rule:{name}"))
                .collect::<Vec<_>>()
        );
        item["obligation"] = json!(true);
        item["covered"] = json!(covered);
        item["status"] = json!(if covered { COVERED } else { OPEN });
        item["touched_only_by"] = json!(if covered {
            Vec::new()
        } else {
            without(ids(&item["uncounted"]), &[])
        });
        if covered {
            continue;
        }
        if argued.contains_key(&id) {
            argued_windows.insert(window.clone(), id.clone());
        }
        // A part argued while open argues this window: the rules first, then the shorter
        // windows, which precede this one in item order.
        let by_part = window
            .iter()
            .find_map(|at| argued_rules.get(at).map(|id| (*id).to_owned()))
            .or_else(|| {
                (2..window.len()).find_map(|length| {
                    window
                        .windows(length)
                        .find_map(|part| argued_windows.get(part).cloned())
                })
            });
        if !argued.contains_key(&id)
            && let Some(by) = by_part
        {
            argued_windows.insert(window.clone(), by.clone());
            item["unargued_status"] = json!(OPEN);
            item["status"] = json!(ARGUED);
            item["argued_by"] = json!(by);
            item["argument"] = json!(argued.get(&by).cloned().unwrap_or_default());
            continue;
        }
        if item["frontier"] != true {
            continue;
        }
        frontier_count += 1;
        let (prefix, last) = window.split_at(window.len() - 1);
        let last_rule = by_sentence.get(&last[0]).copied().unwrap_or(&Value::Null);
        let (file, line) = position(last_rule);
        let (prefix_names, last_name) = names.split_at(names.len() - 1);
        let (text, programs) = if prefix.len() == 1 {
            let first = by_sentence.get(&prefix[0]).copied().unwrap_or(&Value::Null);
            (
                format!(
                    "a case whose run takes a step of {} right after a step of {}",
                    last_name[0], prefix_names[0]
                ),
                ids(&first["fired_by"]),
            )
        } else {
            // The programs that took the prefix: the item of the window of the first rules.
            (
                format!(
                    "a case whose run takes a step of {} right after the steps {}",
                    last_name[0],
                    listed(prefix_names)
                ),
                Vec::new(),
            )
        };
        targets.push((
            window[..window.len() - 1].to_vec(),
            json!({
                "family": "rule_windows",
                "item": id,
                "text": text,
                "file": file,
                "line": line,
                "programs": programs,
                "pattern": item["pattern"],
                "fuzz": null,
            }),
        ));
    }
    // A longer window's target names the programs that took its prefix.
    let prefix_programs = items
        .iter()
        .filter(|item| item["covered"] == true)
        .map(|item| {
            (
                item["rules"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(at_of)
                    .collect::<Vec<_>>(),
                item["covered_by"].clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let targets = targets
        .into_iter()
        .map(|(prefix, mut target)| {
            if prefix.len() > 1
                && let Some(programs) = prefix_programs.get(&prefix)
            {
                target["programs"] = programs.clone();
            }
            target
        })
        .collect::<Vec<_>>();
    let obligations = items.len();
    let argued_count = items.iter().filter(|item| item["status"] == ARGUED).count();
    let mut lengths = Map::new();
    for (length, [obligations, covered]) in by_length {
        lengths.insert(
            length.to_string(),
            json!({"obligations": obligations, "covered": covered}),
        );
    }
    family["obligations"] = json!(obligations);
    family["covered"] = json!(covered_count);
    family["measure"] = measure(covered_count, obligations);
    family["counts"] = json!({
        "covered": covered_count,
        "open": obligations - covered_count - argued_count,
        "argued": argued_count,
        "frontier": frontier_count,
        "by_length": lengths,
    });
    Derived {
        counts: if family["reason"].is_string() {
            None
        } else {
            Some((covered_count, obligations))
        },
        targets,
    }
}
