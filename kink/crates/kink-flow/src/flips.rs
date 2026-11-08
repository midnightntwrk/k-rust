//! The flips family of `coverage` (tier 2): condition flips a front end derives from the
//! definition's source, each run by the kill search `run` makes, and each reported as an
//! obligation the corpus distinguishes or not (README, "kink-flow coverage").
//!
//! A flip negates one condition atom (or toggles one bit of an encoding) in a closed set of
//! sentences that the atom keeps apart, so the flipped definition is one the source language
//! admits. Generating the flips needs the source language's guard families, and admitting each
//! needs its judge: a front end supplies the list ([`DerivedList`], through
//! [`crate::cli::FrontEnd::derived`]). kink-flow's own front end reads K alone, so it derives
//! none and says why ([`DERIVES_NONE`]).
//!
//! # Each obligation's status
//!
//! - `refused`: the front end's judge, or kink-flow's resolution or admission of the patch,
//!   refused the flip, with the reason. Either is a disagreement between the generator and an
//!   admission, which a definition's tests pin to zero.
//! - `unreached`: no comparable program reached any occurrence of the flipped atom (below), so
//!   the corpus cannot distinguish the flip, and no mutant runs.
//! - `distinguished`: the kill search killed the mutant, with its `killer`: the coverage lock's
//!   recorded killer while it still kills, else the first killing program in the search's order
//!   ([`crate::lock`]; `recorded_killer`, and `killer_change` saying why the killer is not the
//!   recorded one).
//! - `undistinguished`: the search ran the mutant on every comparable program and none
//!   distinguished it. Under `[observe]`, a flip some program of which agreed only up to its
//!   baseline's observation horizons has `horizon`, as the run row's (each such program, each
//!   channel's horizon with why it opened), so the obligation says that it rests on a prefix.
//! - `equivalent`: kink proves no program can distinguish the mutant (an `equivalent` or
//!   `unkillable` row), so it is no obligation a program can meet.
//! - `unknown`: the search gave no verdict (`unknown`, `timeout`, or a corpus error), with kink's
//!   reason where one holds for the whole search, and each executed program's cause (`causes`).
//!
//! These are not kink's `killed` and `survived`: an `unreached` status rests on a deduction, not
//! on runs, and the family reports what the corpus covers, not mutation verdicts. The measure is
//! distinguished over the obligations less the refused and equivalent ones.
//!
//! # The unreached deduction
//!
//! Each derived flip names the occurrences it changes ([`Occurrence`]): a node of a sentence's
//! condition ([`Reach::Operand`], a Boolean atom), or a sentence's match ([`Reach::Match`], an
//! arm of a bit encoding, whose fixed bits are its pattern). An occurrence is reached when some
//! comparable program's cached baseline record shows it:
//!
//! - an operand node is reached when it took an outcome (`true`, `false` or `undefined`) in the
//!   sentence's guard row ([`crate::guards::row_guard`]);
//! - a match is reached when the sentence was entered at the front end's level: its templates
//!   matched where the front end reads them (`krs.matched_by`), else its left-hand side matched.
//!
//! An occurrence is undecided, and counts as reached, where the records cannot say it was not
//! evaluated: a node a program left undecided, a guard a program left undecided or stopped in,
//! or the solver refuted (the solver reads every atom of the condition, past the nodes the
//! solver-free evaluation reached); a program whose recorded coverage is not complete (it covers
//! only what its run explored before it stopped); and an occurrence the guard rows do not place
//! (no rule item, no guard, an unreadable skeleton, no node at the path). A flip with no
//! occurrence named is undecided too.
//!
//! A flip is `unreached` when it names occurrences and none is reached or undecided. Why that is
//! sound: the flip changes only those occurrences, in place, and leaves every operand before
//! each unchanged, so a run of the mutant reaches the same positions with the same states as
//! the baseline's. By induction on the steps of a comparable program's baseline run, which never
//! evaluates an occurrence, the mutant's run takes the same steps: every guard verdict and every
//! function value it uses agree. For a bit flip the closed set S of arms has a domain the toggle
//! maps onto itself, so an input that no arm of S matched in the baseline matches no arm of S
//! in the mutant either. So every comparable program agrees on the mutant, and the corpus does
//! not distinguish it; no run would say more. The deduction asks nothing of kink's admission of
//! the mutant, which only the search asks.

use crate::mutation::{EditSpec, Mutation};
/// The sentence an occurrence names, re-exported for front ends that build the list.
pub use kink_patch::SentenceRef;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The flips family's reason under a front end that derives no list (kink-flow's own).
pub const DERIVES_NONE: &str = "the front end derives no condition flips: generating them needs \
     the source language's guard families, and admitting each needs its judge of the flipped \
     source, which a K specification alone does not give";

/// The flips family's reason under `--tier 1`, which runs no mutant.
pub const FLIPS_TIER_ONE: &str = "--tier 1 runs no mutant: the family shows only how many \
     obligations it has, and no status, since a status read from the cache alone would depend \
     on what the cache holds";

/// The status of a flip the search killed.
pub const DISTINGUISHED: &str = "distinguished";
/// The status of a flip the search ran on every comparable program without a kill.
pub const UNDISTINGUISHED: &str = "undistinguished";
/// The status of a flip no comparable program reached, deduced with no run.
pub const UNREACHED: &str = "unreached";
/// The status of a flip the search gave no verdict.
pub const UNKNOWN: &str = "unknown";
/// The status of a flip a judge or kink-flow's admission refused.
pub const REFUSED: &str = "refused";
/// The status of a flip kink proves no program distinguishes.
pub const EQUIVALENT: &str = "equivalent";

/// The statuses, in the order the counts list them.
pub const STATUSES: [&str; 6] = [
    DISTINGUISHED,
    UNDISTINGUISHED,
    UNREACHED,
    UNKNOWN,
    REFUSED,
    EQUIVALENT,
];

/// What a front end derives for the flips family.
#[derive(Clone, Copy, Debug)]
pub enum Derived<'a> {
    /// No list, and why: the family has `run: false` and this reason.
    None(&'a str),
    /// The flips family's obligations.
    Flips(&'a DerivedList),
}

impl Default for Derived<'_> {
    /// kink-flow's own: no list ([`DERIVES_NONE`]).
    fn default() -> Self {
        Self::None(DERIVES_NONE)
    }
}

/// A front end's derived flips: every obligation, and the flips its generator does not generate.
///
/// The list must be a function of the definition, so the flips that are not obligations are
/// decided before any run: kink-flow moves an entry that changes a sentence outside the scope
/// every coverage family shares (a claim helper, a simplification, a rule with no coverage
/// signal; [`crate::coverage`], "Families") to `not_generated` wherever a list enters
/// ([`scoped`]), so the scope holds for any front end's list.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DerivedList {
    /// Every obligation, in the front end's order, which must be a function of the definition.
    pub entries: Vec<DerivedEntry>,
    /// The flips not generated, each the front end's value (`{reason, ...}`), shown apart and
    /// never counted; kink-flow adds the entries outside the coverage scope ([`scoped`]).
    pub not_generated: Vec<Value>,
    /// Why the list is empty, when it is.
    pub none: Option<String>,
}

/// One flip obligation.
#[derive(Clone, Debug, PartialEq)]
pub struct DerivedEntry {
    /// The flip's identity, unique in the list and stable while the definition's families are;
    /// the mutation id its run uses.
    pub id: String,
    /// `flip` (a Boolean atom negated) or `bitflip` (a bit of an encoding toggled).
    pub operator: String,
    /// The atom as an author reads it, for targets (`self.halted`, `bit 0 of op`).
    pub text: String,
    /// The front end's presentation of the atom, shown as given.
    pub atom: Value,
    /// Every occurrence the flip changes; the unreached deduction reads them.
    pub occurrences: Vec<Occurrence>,
    /// The front end's judgement.
    pub judged: Judged,
}

/// A front end's judgement of a flip.
#[derive(Clone, Debug, PartialEq)]
pub enum Judged {
    /// Admitted: the K patch of the specification's sources, in a mutation list's edit format.
    Admitted {
        /// The edits.
        edits: Vec<EditSpec>,
    },
    /// Refused, with the judge's first refusal.
    Refused {
        /// The refusal's reason.
        reason: String,
        /// What the refusal says to do next.
        next: Option<String>,
        /// What the refusal is about.
        detail: String,
    },
}

/// One place a flip changes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Occurrence {
    /// The baseline sentence (module and index, as the rules family's items name it).
    pub sentence: SentenceRef,
    /// What of the sentence the flip changes.
    pub reach: Reach,
}

/// What of a sentence a flip changes, which decides when the corpus reached it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Reach {
    /// A node of the sentence's condition, by its path in the rule item's `guard.operands`.
    Operand {
        /// The node's display path (`0.1`).
        path: String,
    },
    /// The sentence's match: its pattern (a template's fixed bits, a literal).
    Match,
}

impl DerivedEntry {
    /// The flip as a list's mutation, with no misunderstanding: the generator's rule is its
    /// justification. `None` for a refused flip.
    #[must_use]
    pub fn mutation(&self) -> Option<Mutation> {
        match &self.judged {
            Judged::Admitted { edits } => Some(Mutation {
                id: self.id.clone(),
                misunderstanding: String::new(),
                edits: edits.clone(),
            }),
            Judged::Refused { .. } => None,
        }
    }
}

/// `list` with every entry that changes a sentence outside the coverage scope moved to
/// `not_generated` ([`outside_scope`]), after the front end's own, in the list's order: such an
/// entry is never resolved, run or counted, so no mutant is spent on a flip no family counts.
pub(crate) fn scoped(
    list: &DerivedList,
    spec: &crate::admit::AdmittedSpec,
    scope: &crate::coverage::scope::Scope<'_>,
) -> DerivedList {
    let mut scoped = DerivedList {
        entries: Vec::new(),
        not_generated: list.not_generated.clone(),
        none: list.none.clone(),
    };
    for entry in &list.entries {
        match outside_scope(entry, spec, scope) {
            Some(value) => scoped.not_generated.push(value),
            None => scoped.entries.push(entry.clone()),
        }
    }
    scoped
}

/// The `not_generated` value of `entry` where one of its occurrences names a sentence outside
/// the coverage scope (the first such, in occurrence order, gives the reason): `{reason, id,
/// atom, sentences, pair, detail}`, `reason` the exclusion's status (`claim-helper`,
/// `out-of-scope`, `no-coverage-signal`) and `sentences` the labels of the sentences it changes
/// (a sentence with none named `<module>#<index>`); `None` where every occurrence is in scope.
pub(crate) fn outside_scope(
    entry: &DerivedEntry,
    spec: &crate::admit::AdmittedSpec,
    scope: &crate::coverage::scope::Scope<'_>,
) -> Option<Value> {
    let (at, excluded) = entry.occurrences.iter().find_map(|occurrence| {
        let excluded = scope.excludes_at(spec, &occurrence.sentence)?;
        Some((&occurrence.sentence, excluded))
    })?;
    let name = |sentence: &SentenceRef| -> String {
        let label = spec
            .loaded
            .baseline
            .sentence(sentence)
            .and_then(|sentence| match sentence {
                k_rust::definition::Sentence::Rule { attributes, .. } => attributes
                    .string(k_rust::definition::AttributeKey::Label)
                    .map(str::to_owned),
                _ => None,
            });
        label.unwrap_or_else(|| format!("{}#{}", sentence.module, sentence.index))
    };
    let mut sentences = Vec::new();
    for occurrence in &entry.occurrences {
        let name = name(&occurrence.sentence);
        if !sentences.contains(&name) {
            sentences.push(name);
        }
    }
    let first = name(at);
    Some(json!({
        "reason": excluded.status(),
        "id": entry.id,
        "atom": entry.atom,
        "sentences": sentences,
        "pair": null,
        "detail": format!(
            "`{}` changes {first}, which is no obligation of any coverage family ({}: {})",
            entry.id,
            excluded.status(),
            excluded.reason()
        ),
    }))
}

/// The program ids of a JSON list, each a string or a `{program}` object.
fn ids(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.as_str().or_else(|| entry["program"].as_str()))
        .map(str::to_owned)
        .collect()
}

/// `programs` in order, each once.
fn unique(programs: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    programs
        .into_iter()
        .filter(|program| seen.insert(program.clone()))
        .collect()
}

/// The programs that leave every operand of `guard` undecided for the deduction: a guard a
/// program left undecided, stopped in or the solver refuted, and a node a program left
/// undecided (module documentation).
fn guard_undecided(guard: &Value) -> Vec<String> {
    let mut programs = ids(&guard["undecided_by"]);
    programs.extend(ids(&guard["stopped_by"]));
    programs.extend(ids(&guard["solver_refuted_by"]));
    for operand in guard["operands"].as_array().into_iter().flatten() {
        programs.extend(ids(&operand["undecided_by"]));
    }
    unique(programs)
}

/// What the records say of one occurrence: the occurrence's value, with `reached_by` (the
/// comparable programs that reached it), `undecided_by` (those that may have), `true_by` and
/// `false_by` for an operand node (the values the corpus reached), and `unplaced` (why the
/// guard rows do not place it, or null). `item` is the rule item of the occurrence's sentence,
/// annotated by the front end; `incomplete` the comparable programs whose recorded coverage is
/// not complete.
#[must_use]
pub fn occurrence_value(
    occurrence: &Occurrence,
    item: Option<&Value>,
    incomplete: &[String],
) -> Value {
    let mut value = json!({
        "module": occurrence.sentence.module,
        "index": occurrence.sentence.index,
        "reach": match occurrence.reach {
            Reach::Operand { .. } => "operand",
            Reach::Match => "match",
        },
        "path": match &occurrence.reach {
            Reach::Operand { path } => Some(path),
            Reach::Match => None,
        },
        "reached_by": [],
        "undecided_by": incomplete,
        "unplaced": null,
    });
    let unplaced = |mut value: Value, reason: &str| {
        value["unplaced"] = json!(reason);
        value
    };
    let Some(item) = item else {
        return unplaced(
            value,
            "the sentence is no rule of the specification's rules family",
        );
    };
    let guard = &item["guard"];
    match &occurrence.reach {
        Reach::Operand { path } => {
            if !guard.is_object() {
                return unplaced(value, "the sentence has no guard row");
            }
            if let Some(reason) = guard["operands_reason"].as_str() {
                return unplaced(value, reason);
            }
            let Some(operand) = guard["operands"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|operand| operand["path"] == path.as_str())
            else {
                return unplaced(value, "the condition's skeleton has no node at the path");
            };
            let (true_by, false_by) = (ids(&operand["true_by"]), ids(&operand["false_by"]));
            let mut reached = true_by.clone();
            reached.extend(false_by.iter().cloned());
            reached.extend(ids(&operand["undefined_by"]));
            value["reached_by"] = json!(unique(reached));
            value["true_by"] = json!(true_by);
            value["false_by"] = json!(false_by);
            let mut undecided = incomplete.to_vec();
            undecided.extend(guard_undecided(guard));
            value["undecided_by"] = json!(unique(undecided));
        }
        Reach::Match => {
            let templated = guard["krs"]["templates"].is_object();
            let entered = if templated {
                &item["krs"]["matched_by"]
            } else {
                &item["matched_by"]
            };
            value["reached_by"] = json!(ids(entered));
            if templated {
                let mut undecided = incomplete.to_vec();
                undecided.extend(guard_undecided(guard));
                value["undecided_by"] = json!(unique(undecided));
            }
        }
    }
    value
}

/// Whether a flip whose occurrences' values ([`occurrence_value`]) are `occurrences` is
/// unreached: it names one, and none is reached, undecided or unplaced.
#[must_use]
pub fn unreached(occurrences: &[Value]) -> bool {
    !occurrences.is_empty()
        && occurrences.iter().all(|occurrence| {
            ids(&occurrence["reached_by"]).is_empty()
                && ids(&occurrence["undecided_by"]).is_empty()
                && occurrence["unplaced"].is_null()
        })
}

/// A flip item's status, reason and verdict fields from its run row (a row of the run
/// document): `killed` is `distinguished`, `survived` `undistinguished`, `equivalent` and
/// `unkillable` `equivalent`, `invalid-mutation` and `not-admitted` `refused` (kink-flow's
/// admission), and every other status `unknown`. `kink_status` keeps kink's status, and
/// `horizon` the row's (a survivor's agreements up to a horizon, null where it has none). An
/// `unknown` flip's `causes` are the search's own record of what stopped each comparison: one
/// `{program, cause}` per executed program with a cause, in the search's order (empty for every
/// other status), since the row's `reason` names a cause only where one holds for the whole
/// search.
pub fn fill_from_row(item: &mut Value, row: &Value) {
    let kink = row["status"].as_str().unwrap_or_default();
    let status = match kink {
        "killed" => DISTINGUISHED,
        "survived" => UNDISTINGUISHED,
        "equivalent" | "unkillable" => EQUIVALENT,
        crate::search::INVALID_MUTATION | "not-admitted" => REFUSED,
        _ => UNKNOWN,
    };
    item["status"] = json!(status);
    item["kink_status"] = json!(kink);
    item["reason"] = row["reason"].clone();
    item["detail"] = row.get("detail").cloned().unwrap_or(Value::Null);
    if status == REFUSED {
        item["judge"] = json!("kink-flow");
    }
    item["digest"] = row["digest"].clone();
    item["killer"] = row["killer"].clone();
    item["killer_source"] = row["killer_source"].clone();
    item["recorded_killer"] = row["recorded_killer"].clone();
    item["killer_change"] = row["killer_change"].clone();
    item["witnesses"] = row["witnesses"].clone();
    item["horizon"] = row.get("horizon").cloned().unwrap_or(Value::Null);
    let executed = row["executed"].as_array().map_or(&[][..], Vec::as_slice);
    item["causes"] = json!(if status == UNKNOWN {
        executed
            .iter()
            .filter(|entry| entry["cause"].is_string())
            .map(|entry| json!({"program": entry["program"], "cause": entry["cause"]}))
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    });
    item["live_runs"] = json!(
        executed
            .iter()
            .filter(|entry| entry["cached"] != true)
            .count()
    );
    item["calls"] = json!(row["calls"].as_array().map_or(0, Vec::len));
}

/// A flip item before its run or deduction: its identity, its operator and atom, and its
/// occurrences' values; every verdict field null and no run.
#[must_use]
pub fn item_value(entry: &DerivedEntry, occurrences: Vec<Value>) -> Value {
    json!({
        "id": entry.id,
        "operator": entry.operator,
        "text": entry.text,
        "atom": entry.atom,
        "occurrences": occurrences,
        "sentences": [],
        "status": null,
        "kink_status": null,
        "judge": null,
        "reason": null,
        "next": null,
        "detail": null,
        "digest": null,
        "killer": null,
        "killer_source": null,
        "recorded_killer": null,
        "killer_change": null,
        "witnesses": null,
        "horizon": null,
        "causes": [],
        "waits_on": [],
        "live_runs": 0,
        "calls": 0,
    })
}

/// The counts of a flips family's items by status, with `not_generated`.
#[must_use]
pub fn counts(items: &[Value], not_generated: usize) -> Value {
    let mut counts = BTreeMap::new();
    for status in STATUSES {
        counts.insert(
            status.to_owned(),
            json!(items.iter().filter(|item| item["status"] == status).count()),
        );
    }
    counts.insert("not_generated".to_owned(), json!(not_generated));
    Value::Object(counts.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn operand(path: &str) -> Occurrence {
        Occurrence {
            sentence: SentenceRef {
                module: "M".into(),
                index: 3,
            },
            reach: Reach::Operand { path: path.into() },
        }
    }

    fn item(guard: Value) -> Value {
        json!({"module": "M", "index": 3, "matched_by": ["p"], "guard": guard})
    }

    fn guard(operands: Value) -> Value {
        json!({"undecided_by": [], "stopped_by": [], "solver_refuted_by": [],
               "operands_reason": null, "operands": operands})
    }

    fn node(path: &str, true_by: &[&str], false_by: &[&str], undecided: &[&str]) -> Value {
        json!({"path": path, "kind": "atom", "true_by": true_by, "false_by": false_by,
               "undefined_by": [],
               "undecided_by": undecided.iter().map(|p| json!({"program": p, "causes": ["symbolic"]}))
                   .collect::<Vec<_>>()})
    }

    #[test]
    fn a_node_no_program_reached_is_unreached() {
        let rule = item(guard(json!([
            node("0.0", &["p"], &[], &[]),
            node("0.1", &[], &[], &[]),
        ])));
        let value = occurrence_value(&operand("0.1"), Some(&rule), &[]);
        assert!(unreached(&[value]));
        let value = occurrence_value(&operand("0.0"), Some(&rule), &[]);
        assert_eq!(value["true_by"], json!(["p"]));
        assert!(!unreached(&[value]));
    }

    #[test]
    fn an_undecided_node_counts_as_reached_for_every_operand_of_its_guard() {
        let rule = item(guard(json!([
            node("0.0", &[], &[], &["q"]),
            node("0.1", &[], &[], &[]),
        ])));
        let value = occurrence_value(&operand("0.1"), Some(&rule), &[]);
        assert_eq!(value["undecided_by"], json!(["q"]));
        assert!(!unreached(&[value]));
        let mut solver = guard(json!([node("0.0", &[], &[], &[])]));
        solver["solver_refuted_by"] = json!(["s"]);
        let value = occurrence_value(&operand("0.0"), Some(&item(solver)), &[]);
        assert!(!unreached(&[value]));
    }

    #[test]
    fn an_occurrence_the_rows_do_not_place_counts_as_reached() {
        let rule = item(guard(json!([node("0", &[], &[], &[])])));
        for (occurrence, item) in [
            (operand("0.4"), Some(&rule)),
            (operand("0"), None),
            (operand("0"), Some(&json!({"module": "M", "index": 3}))),
        ] {
            let value = occurrence_value(&occurrence, item, &[]);
            assert!(value["unplaced"].is_string(), "{value:#}");
            assert!(!unreached(&[value]));
        }
        let mut unreadable = guard(json!([]));
        unreadable["operands_reason"] = json!("no skeleton");
        let value = occurrence_value(&operand("0"), Some(&item(unreadable)), &[]);
        assert_eq!(value["unplaced"], "no skeleton");
        assert!(!unreached(&[]), "a flip that names no occurrence runs");
    }

    #[test]
    fn incomplete_coverage_counts_as_reached() {
        let rule = item(guard(json!([node("0", &[], &[], &[])])));
        let value = occurrence_value(&operand("0"), Some(&rule), &["t".to_owned()]);
        assert!(!unreached(&[value]));
    }

    /// An undistinguished flip whose run row rests on a horizon carries it, and a coverage
    /// rendering writes it with each channel's opening; a distinguished flip has none.
    #[test]
    fn an_undistinguished_flip_carries_and_renders_its_horizon() {
        let horizon = json!([{"program": "run",
                              "horizon": {"clock": {"elements": 16, "opening": "bound"}}}]);
        let mut item = json!({"id": "f"});
        fill_from_row(
            &mut item,
            &json!({"status": "survived", "reason": null, "horizon": horizon}),
        );
        assert_eq!(item["status"], UNDISTINGUISHED);
        assert_eq!(item["horizon"], horizon);
        let document = json!({"schema": crate::coverage::COVERAGE_SCHEMA,
                              "families": {"flips": {"run": true, "items": [item]}}});
        let text = crate::verdicts::verdicts(&document).unwrap();
        assert!(
            text.contains(
                "horizon = [{ program = \"run\", channel = \"clock\", elements = 16, \
                 opening = \"bound\" }]"
            ),
            "{text}"
        );
        let mut killed = json!({"id": "g"});
        fill_from_row(&mut killed, &json!({"status": "killed", "killer": "run"}));
        assert_eq!(killed["horizon"], Value::Null);
    }

    #[test]
    fn a_match_is_reached_by_the_front_ends_match_where_it_reads_templates() {
        let at = Occurrence {
            sentence: SentenceRef {
                module: "M".into(),
                index: 3,
            },
            reach: Reach::Match,
        };
        let plain = json!({"matched_by": ["p"]});
        assert!(!unreached(&[occurrence_value(&at, Some(&plain), &[])]));
        let mut templated = item(guard(json!([])));
        templated["guard"]["krs"] = json!({"templates": {"matched_by": []}});
        templated["krs"] = json!({"matched_by": []});
        assert!(unreached(&[occurrence_value(&at, Some(&templated), &[])]));
    }
}
