//! The invariants of argued obligations (`[[coverage.invariant]]`): how a front end resolves one
//! to the definition's terms ([`InvariantResolver`]), and the connection `coverage` checks for
//! each argued item that names one ([`connections`]; module documentation of
//! [`crate::coverage`], "Argued obligations").
//!
//! # Resolution
//!
//! An invariant names a `Bool` function and the cells it reads, one per parameter, in the
//! spellings of the corpus's front end. The front end resolves them to the function's KORE symbol
//! and each cell's KORE path, the cell symbols from the configuration's top cell down to it
//! ([`ResolvedInvariant`]), before any check runs. kink-flow's own front end reads K
//! ([`KInvariants`]): the function by its K label, the cells by their K names. A function the
//! definition does not hold, a cell its configuration does not have, and a cell that is or lies
//! below a `*` or `?` cell (applied in each instance the function would give several answers, not
//! one) or that is or lies below an unobservable cell (whose content no use of the definition may
//! read) are unresolved; so is a function that is not one, that has sort parameters, or whose
//! parameters are not one per cell. A function whose result is not `Bool` is refused apart: an
//! invariant holds or does not at a state.
//!
//! # The connection
//!
//! An argued item names an obligation of a rewrite rule, and a run covers it with one of the
//! facts of a run's records that `fuzz --cover` searches for (`crate::fuzz_goal`): a guard node
//! reached with a truth, a guard outcome, or a firing. Each fact is a valuation of one compiled
//! axiom at its left-hand side (kink-native [`kink_native::invariant::Valuation`]): a node reached
//! with its truth, the condition held or refuted, and for a `rule:` item the left-hand side alone
//! where the rule was never matched (the obligation is then to reach a state it matches) and the
//! condition held where it was matched and never fired (a rule fires only where it holds). The
//! connection asks of each fact whether the invariant and the valuation have no model at that
//! left-hand side (kink-native [`kink_native::invariant::connection`]). The item's obligation is
//! the disjunction of its facts, so it is excluded wherever the invariant holds exactly when each
//! fact is:
//!
//! - `holds` when every fact is connected;
//! - `fails` when one is not: kink-native shows a state the axiom matches where the invariant
//!   holds and the fact does, so the invariant does not exclude the item;
//! - `undecided` otherwise, with the first undecided fact's cause, and for an item with no fact
//!   of a run's records (none can be checked).
//!
//! The whole decision runs on the input backend's definition, the one every program runs on, with
//! the corpus's solver budget. Each `Unknown` the solver answers is counted (`smt_unknown`).
//!
//! # The cache
//!
//! Each answer is kept in the connection memo ([`crate::memo::connection_key`]) under the
//! execution digest, the axiom, the valuation, the function's symbol and the cells' paths, kink's
//! build and the solver: the question is built from those alone. An answer cut short by a stop is
//! not kept, and neither is any answer of a run whose build cannot be named. `--verify` reads and
//! writes no record. A connection whose every answer was read from the memo is `cached`.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::path::Path;

use k_rust::backend::{Backend, BackendError};
use k_rust::definition::configuration::CellMultiplicity;
use k_rust::k_rust_backend::definition::BackendDefinition;
use k_rust::k_rust_backend::smt::SmtSolver;
use k_rust::k_rust_backend::term::SymbolType;
use k_rust::kast::Label;
use k_rust::kompile::encode_kore_label;
use k_rust::names::BuiltinSort;
use k_rust_fuzz::target::{CoverageFact, RuleRef};
use kink_campaign::CellLayout;
use kink_corpus::admission::AdmissionRefusal;
use kink_native::invariant::{Connection, Invariant as Asked, Undecided, Valuation, connection};
use serde_json::{Map, Value, json};

use super::{ARGUED, HEATING, MATCHED};
use crate::admit::AdmittedSpec;
use crate::digest::ExecutionDigest;
use crate::manifest::{FlowManifest, Invariant};
use crate::memo;

/// The status of a connection every fact of whose item is connected.
pub const CONNECTION_HOLDS: &str = "holds";
/// The status of a connection one fact of whose item is not connected.
pub const CONNECTION_FAILS: &str = "fails";
/// The status of a connection neither shown to hold nor to fail.
pub const CONNECTION_UNDECIDED: &str = "undecided";

/// An invariant resolved to the definition's terms (module documentation, "Resolution").
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInvariant {
    /// The function's KORE symbol.
    pub symbol: String,
    /// Each cell, in parameter order, as the KORE cell symbols from the configuration's top cell
    /// down to it.
    pub cells: Vec<Vec<String>>,
    /// What else the invariant's checks are about, in the front end's terms, which the
    /// invariant's `identity` gains (a KRS front end's Definition IR digest and the function's
    /// full path, for one); empty for kink-flow's K front end, whose terms the symbol and the
    /// cell paths already are.
    pub identity: Map<String, Value>,
}

/// Why a front end does not resolve an invariant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InvariantRefusal {
    /// The function or a cell is not one the definition has, or not one an invariant can read
    /// (`invariant-unresolved`); the payload is the front end's message.
    Unresolved(String),
    /// The function's result is not `Bool` (`invariant-not-bool`); the payload says so.
    NotBool(String),
}

/// How a front end resolves an invariant's function and cells, as its corpora spell them, to the
/// definition's KORE symbol and cell paths (module documentation, "Resolution").
pub trait InvariantResolver {
    /// `invariant` of the admitted specification `spec`, resolved.
    ///
    /// # Errors
    ///
    /// An [`InvariantRefusal`] naming the cause.
    fn resolve(
        &self,
        spec: &AdmittedSpec,
        invariant: &Invariant,
    ) -> Result<ResolvedInvariant, InvariantRefusal>;
}

/// kink-flow's own front end's resolver: the function by its K label, each cell by its K name
/// (module documentation, "Resolution").
#[derive(Clone, Copy, Debug, Default)]
pub struct KInvariants;

impl InvariantResolver for KInvariants {
    fn resolve(
        &self,
        spec: &AdmittedSpec,
        invariant: &Invariant,
    ) -> Result<ResolvedInvariant, InvariantRefusal> {
        let unresolved = InvariantRefusal::Unresolved;
        let definition = spec
            .definition
            .as_ref()
            .map_err(|reason| unresolved(format!("the definition cannot be read: {reason}")))?;
        let label = &invariant.function;
        let symbol = encode_kore_label(&Label::new(label.as_str())).name;
        let declared = definition.symbols().get(symbol.as_str()).ok_or_else(|| {
            unresolved(format!(
                "the definition declares no symbol of the K label `{label}`"
            ))
        })?;
        if !matches!(declared.attributes.symbol_type, SymbolType::Function(_)) {
            return Err(unresolved(format!(
                "`{label}` is not a function; an invariant is a function of the cells it reads"
            )));
        }
        if !declared.sort_variables.is_empty() {
            return Err(unresolved(format!(
                "`{label}` is a parametric function; an invariant is a function of the cells it \
                 reads"
            )));
        }
        if !declared.result_sort.is_builtin(BuiltinSort::Bool) {
            return Err(InvariantRefusal::NotBool(format!(
                "`{label}` returns {}, not Bool; an invariant holds or does not at a state",
                declared.result_sort.name()
            )));
        }
        let parameters = declared.argument_sorts.len();
        if parameters != invariant.cells.len() {
            return Err(unresolved(format!(
                "`{label}` takes {parameters} parameter{}, but the invariant reads {} cell{}: \
                 one parameter per cell, in order",
                if parameters == 1 { "" } else { "s" },
                invariant.cells.len(),
                if invariant.cells.len() == 1 { "" } else { "s" },
            )));
        }
        let layout = CellLayout::of(&spec.compiled)
            .map_err(|refusal| unresolved(format!("the configuration's cells: {refusal}")))?;
        let cells = invariant
            .cells
            .iter()
            .map(|name| cell_path(&layout, name).map_err(unresolved))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ResolvedInvariant {
            symbol,
            cells,
            identity: Map::new(),
        })
    }
}

/// The KORE path of the cell `name` of `layout`, or why an invariant cannot read it.
fn cell_path(layout: &CellLayout, name: &str) -> Result<Vec<String>, String> {
    let cell = layout
        .cell(name)
        .ok_or_else(|| format!("the configuration has no cell `{name}`"))?;
    let mut path = std::iter::once(cell)
        .chain(layout.ancestors(cell))
        .collect::<Vec<_>>();
    path.reverse();
    for &at in &path {
        let holder = &layout.cells()[at];
        let several = match holder.multiplicity {
            CellMultiplicity::One => None,
            CellMultiplicity::Optional => Some("optional"),
            CellMultiplicity::Star => Some("repeated"),
        };
        if let Some(several) = several {
            return Err(format!(
                "the cell `{name}` is or is below the {several} cell `{}`: applied in each \
                 instance an invariant would give several answers, not one",
                holder.name
            ));
        }
        if holder.unobservable {
            return Err(format!(
                "the cell `{name}` is or is below the unobservable cell `{}`, whose content no \
                 use of the definition may read",
                holder.name
            ));
        }
    }
    Ok(path
        .into_iter()
        .map(|at| layout.cells()[at].kore_symbol.clone())
        .collect())
}

/// The `[[coverage.invariant]]` tables of `manifest` resolved by `resolver` (`None`: the front end
/// resolves none) for `spec`, by name, each with its `identity` (`{definition, symbol, cells}`
/// and the resolver's own members, `definition` the execution digest `execution`); or the refusal
/// at stage `coverage`: `invariant-unsupported-front-end` without a resolver, else
/// `invariant-unresolved` naming every table that does not resolve (and those whose result is not
/// `Bool`), else `invariant-not-bool` naming each table whose function's result is not `Bool`.
pub(super) fn resolve(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    resolver: Option<&(dyn InvariantResolver + Sync)>,
    execution: &ExecutionDigest,
) -> Result<BTreeMap<String, (ResolvedInvariant, Value)>, AdmissionRefusal> {
    let invariants = &manifest.coverage.invariants;
    let refusal = |reason: &str, detail: String| AdmissionRefusal {
        stage: "coverage".into(),
        reason: reason.into(),
        detail,
    };
    let Some(resolver) = resolver else {
        return Err(refusal(
            "invariant-unsupported-front-end",
            format!(
                "[[coverage.invariant]] declares {}, and this front end resolves no invariant's \
                 function and cells to the definition's terms, so no argument resting on one \
                 can be checked: remove the tables and the entries' `invariant`",
                invariants
                    .iter()
                    .map(|invariant| format!("`{}`", invariant.name))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ));
    };
    let mut resolved = BTreeMap::new();
    let mut unresolved = Vec::new();
    let mut not_bool = Vec::new();
    for invariant in invariants {
        match resolver.resolve(spec, invariant) {
            Ok(found) => {
                let mut identity = json!({
                    "definition": execution.value(),
                    "symbol": found.symbol,
                    "cells": found.cells,
                });
                for (key, value) in &found.identity {
                    identity[key] = value.clone();
                }
                resolved.insert(invariant.name.clone(), (found, identity));
            }
            Err(InvariantRefusal::Unresolved(message)) => {
                unresolved.push(format!("`{}`: {message}", invariant.name));
            }
            Err(InvariantRefusal::NotBool(message)) => {
                not_bool.push(format!("`{}`: {message}", invariant.name));
            }
        }
    }
    let joined = |what: &[String]| what.join("; ");
    if !unresolved.is_empty() {
        let mut detail = format!(
            "[[coverage.invariant]] names what the definition does not resolve: {}",
            joined(&unresolved)
        );
        if !not_bool.is_empty() {
            detail.push_str(&format!(
                "; and a function whose result is not Bool: {}",
                joined(&not_bool)
            ));
        }
        return Err(refusal("invariant-unresolved", detail));
    }
    if !not_bool.is_empty() {
        return Err(refusal(
            "invariant-not-bool",
            format!(
                "[[coverage.invariant]] names a function whose result is not Bool: {}",
                joined(&not_bool)
            ),
        ));
    }
    Ok(resolved)
}

/// A valuation as a connection memo key and a document state it: `matches`, `held`, `refuted`,
/// or `{path, truth}` of a reached node.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Fact {
    Matches,
    Held,
    Refuted,
    Reached(Vec<u32>, bool),
}

impl Fact {
    fn value(&self) -> Value {
        match self {
            Self::Matches => json!("matches"),
            Self::Held => json!("held"),
            Self::Refuted => json!("refuted"),
            Self::Reached(path, truth) => json!({"path": path, "truth": truth}),
        }
    }

    fn valuation(&self) -> Valuation<'_> {
        match self {
            Self::Matches => Valuation::Matches,
            Self::Held => Valuation::Held,
            Self::Refuted => Valuation::Refuted,
            Self::Reached(path, truth) => Valuation::Reached {
                path,
                truth: *truth,
            },
        }
    }

    /// The valuation in words, for a failure's detail.
    fn text(&self) -> String {
        match self {
            Self::Matches => "its left-hand side matches".to_owned(),
            Self::Held => "its condition holds".to_owned(),
            Self::Refuted => "its condition is refuted".to_owned(),
            Self::Reached(path, truth) => format!(
                "the node {} of its condition is reached and {truth}",
                path.iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(".")
            ),
        }
    }
}

/// The facts of a run's records that cover the argued item `item` of family `family` of the
/// derived document `probe`, each as an axiom and its valuation (module documentation, "The
/// connection"), or why none can be read.
fn facts(
    probe: &Value,
    spec: &AdmittedSpec,
    family: &str,
    item: &Value,
) -> Result<Vec<(String, Fact)>, String> {
    let mut facts = Vec::new();
    let mut add = |axiom: &RuleRef, fact: Fact| {
        if let RuleRef::UniqueId(axiom) = axiom {
            let entry = (axiom.clone(), fact);
            if !facts.contains(&entry) {
                facts.push(entry);
            }
        }
    };
    if family == "requirements" {
        for fact in
            crate::fuzz_goal::requirement_facts(probe, spec, item).map_err(|(_, detail)| detail)?
        {
            match fact {
                CoverageFact::GuardNode { rule, node, truth } => {
                    add(&rule, Fact::Reached(node, truth));
                }
                CoverageFact::GuardOutcome { rule, held } => {
                    add(&rule, if held { Fact::Held } else { Fact::Refuted });
                }
                _ => {}
            }
        }
    } else {
        // A rule matched and never fired is covered where its condition holds; one never matched
        // where its left-hand side matches first.
        let status = item.get("unargued_status").unwrap_or(&item["status"]);
        let matched = status == MATCHED;
        let fired = crate::fuzz_goal::rule_facts(spec, item).map_err(|(_, detail)| detail)?;
        debug_assert!(item["kind"] != HEATING || fired.len() <= 1);
        for fact in fired {
            if let CoverageFact::Fired { rule, .. } = fact {
                add(&rule, if matched { Fact::Held } else { Fact::Matches });
            }
        }
    }
    Ok(facts)
}

/// One answer of the connection question of a fact: kink-native's, or the memo's record of one.
struct Answer {
    /// `connected`, `not-connected` or `undecided`.
    answer: &'static str,
    /// An undecided answer's cause.
    reason: Option<String>,
    /// The `Unknown`s the solver answered for it.
    unknowns: usize,
    /// Whether it was read from the memo.
    cached: bool,
}

impl Answer {
    fn of(connection: &Connection, unknowns: usize) -> Self {
        let (answer, reason) = match connection {
            Connection::Connected => ("connected", None),
            Connection::NotConnected => ("not-connected", None),
            Connection::Undecided(cause) => ("undecided", Some(cause.to_string())),
        };
        Self {
            answer,
            reason,
            unknowns,
            cached: false,
        }
    }

    fn record(&self) -> Value {
        json!({"answer": self.answer, "reason": self.reason, "smt_unknown": self.unknowns})
    }

    fn from_record(record: &Value) -> Option<Self> {
        let answer = match record["answer"].as_str()? {
            "connected" => "connected",
            "not-connected" => "not-connected",
            "undecided" => "undecided",
            _ => return None,
        };
        Some(Self {
            answer,
            reason: record["reason"].as_str().map(str::to_owned),
            unknowns: usize::try_from(record["smt_unknown"].as_u64()?).ok()?,
            cached: true,
        })
    }
}

/// What [`connections`] asks of one argued item: its id, its invariant's name, and its facts.
struct Question {
    item: String,
    invariant: String,
    facts: Result<Vec<(String, Fact)>, String>,
}

/// The connection of each argued item of the derived document `probe` whose entry names an
/// invariant of `resolved` (module documentation, "The connection"), by item id:
/// `{invariant, connection: {status, axioms, reason, model, cached, smt_unknown}}`, asked on
/// `backend` and kept in the cache directory `cache` under the execution digest `execution`
/// (`verify`: no record read or written). An item a program covers, or that is no obligation, is
/// argued by no entry and asks nothing.
///
/// # Errors
///
/// `invariant-unresolved` at stage `coverage` where kink-native cannot read an invariant at one
/// of an item's axioms (a cell the left-hand side does not hold, a cell whose sort the parameter
/// does not admit), naming each such item.
#[expect(
    clippy::too_many_arguments,
    reason = "the inputs of one connection check, each named by the cache key"
)]
pub(super) fn connections(
    probe: &Value,
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    resolved: &BTreeMap<String, (ResolvedInvariant, Value)>,
    backend: &mut Backend,
    execution: &ExecutionDigest,
    cache: &Path,
    verify: bool,
) -> Result<Value, AdmissionRefusal> {
    let mut questions = Vec::new();
    for entry in &manifest.coverage.argued {
        let Some(invariant) = &entry.invariant else {
            continue;
        };
        let found = ["rules", "requirements"].into_iter().find_map(|family| {
            probe["families"][family]["items"]
                .as_array()?
                .iter()
                .find(|item| item["id"] == entry.item.as_str() && item["status"] == ARGUED)
                .map(|item| (family, item))
        });
        let Some((family, item)) = found else {
            continue;
        };
        questions.push(Question {
            item: entry.item.clone(),
            invariant: invariant.clone(),
            facts: facts(probe, spec, family, item),
        });
    }
    if questions.is_empty() {
        return Ok(json!({}));
    }
    let build = kink_campaign::kink_build().ok().filter(|_| !verify);
    let store = kink_corpus::Store::new(cache.to_path_buf());
    let execution = execution.value();
    let ask = |definition: &BackendDefinition, solver: &dyn SmtSolver| {
        let mut checks = Map::new();
        let mut refused = Vec::new();
        for question in &questions {
            let Some((invariant, _)) = resolved.get(&question.invariant) else {
                continue;
            };
            let asked = Asked {
                symbol: &invariant.symbol,
                cells: &invariant.cells,
            };
            let connection = match &question.facts {
                Err(reason) => undecided(&format!(
                    "no fact of a run's records covers the item: {reason}"
                )),
                Ok(facts) => {
                    let mut answers = Vec::new();
                    let mut unread = None;
                    for (axiom, fact) in facts {
                        let key = build.map(|build| {
                            memo::connection_key(
                                &execution,
                                build,
                                manifest.budget,
                                axiom,
                                &fact.value(),
                                &invariant.symbol,
                                &invariant.cells,
                            )
                        });
                        let path = key.as_ref().map(|key| memo::connection_path(cache, key));
                        if let (Some(key), Some(path)) = (&key, &path)
                            && let Some(answer) = memo::read_connection(path, key)
                                .as_ref()
                                .and_then(Answer::from_record)
                        {
                            answers.push((axiom, fact, answer));
                            continue;
                        }
                        let unknowns = Cell::new(0);
                        match connection(
                            definition,
                            solver,
                            axiom,
                            fact.valuation(),
                            Some(asked),
                            &unknowns,
                        ) {
                            Ok(connection) => {
                                let answer = Answer::of(&connection, unknowns.get());
                                if let (Some(key), Some(path)) = (&key, &path)
                                    && connection != Connection::Undecided(Undecided::Stopped)
                                {
                                    memo::write_connection(&store, path, key, &answer.record());
                                }
                                answers.push((axiom, fact, answer));
                            }
                            Err(refusal) => {
                                unread = Some(format!("at the axiom {axiom}: {refusal}"));
                                break;
                            }
                        }
                    }
                    if let Some(unread) = unread {
                        refused.push(format!(
                            "`{}` under the invariant `{}`, {unread}",
                            question.item, question.invariant
                        ));
                        continue;
                    }
                    combined(&question.invariant, &answers)
                }
            };
            checks.insert(
                question.item.clone(),
                json!({"invariant": question.invariant, "connection": connection}),
            );
        }
        Ok::<_, BackendError>((checks, refused))
    };
    match backend.with_solver(None, ask) {
        Ok((_, refused)) if !refused.is_empty() => Err(AdmissionRefusal {
            stage: "coverage".into(),
            reason: "invariant-unresolved".into(),
            detail: format!(
                "[[coverage.invariant]] cannot be read at the left-hand side of an argued item's \
                 rule: {}",
                refused.join("; ")
            ),
        }),
        Ok((checks, _)) => Ok(Value::Object(checks)),
        // The backend asked nothing: every connection is undecided, with its cause.
        Err(error) => Ok(Value::Object(
            questions
                .iter()
                .map(|question| {
                    (
                        question.item.clone(),
                        json!({
                            "invariant": question.invariant,
                            "connection": undecided(&format!("the backend asked nothing: {error}")),
                        }),
                    )
                })
                .collect(),
        )),
    }
}

/// An undecided connection that asked nothing, for `reason`.
fn undecided(reason: &str) -> Value {
    json!({
        "status": CONNECTION_UNDECIDED,
        "axioms": [],
        "reason": reason,
        "model": null,
        "cached": false,
        "smt_unknown": 0,
    })
}

/// The connection of an item from the answers of its facts (module documentation, "The
/// connection"): `fails` where one is not connected, `undecided` where one is undecided, else
/// `holds`; an item with no fact is `undecided`.
fn combined(invariant: &str, answers: &[(&String, &Fact, Answer)]) -> Value {
    if answers.is_empty() {
        return undecided("no fact of a run's records covers the item");
    }
    let failed = answers
        .iter()
        .filter(|(_, _, answer)| answer.answer == "not-connected")
        .map(|(axiom, fact, _)| format!("the axiom {axiom}, where {}", fact.text()))
        .collect::<Vec<_>>();
    let first_undecided = answers
        .iter()
        .find_map(|(_, _, answer)| answer.reason.clone());
    let (status, reason) = if !failed.is_empty() {
        (
            CONNECTION_FAILS,
            Some(format!(
                "a state that {} satisfies the invariant `{invariant}`, so the invariant does \
                 not exclude the item",
                failed.join(", and ")
            )),
        )
    } else if let Some(reason) = first_undecided {
        (CONNECTION_UNDECIDED, Some(reason))
    } else {
        (CONNECTION_HOLDS, None)
    };
    json!({
        "status": status,
        "axioms": answers
            .iter()
            .map(|(axiom, fact, answer)| json!({
                "axiom": axiom,
                "valuation": fact.value(),
                "answer": answer.answer,
                "reason": answer.reason,
                "cached": answer.cached,
            }))
            .collect::<Vec<_>>(),
        "reason": reason,
        "model": null,
        "cached": answers.iter().all(|(_, _, answer)| answer.cached),
        "smt_unknown": answers.iter().map(|(_, _, answer)| answer.unknowns).sum::<usize>(),
    })
}
