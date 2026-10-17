//! Mutant consistency: a mutant is only meaningful as a theory that has models (re-pin
//! R0c-fix-3, `draft/tasks/repin-501f18b9`; decisions log 2026-10-17, "inconsistent mutants").
//!
//! Claim removal (kink-patch `ClaimSupport::withdraw`) makes a mutant's claims backed. It cannot
//! make a mutant's equations agree: `function` is part of the symbol, and a function has at most
//! one value for each input. When an edit makes two equations of one function apply to the same
//! input with different values (a changed guard literal, a dropped `owise` or `priority`), the
//! mutant has no model, and k-rust's verdict on it is the order in which it lists the equations,
//! not the definition's. Such a mutant is invalid, like one that does not compile: kink-campaign
//! refuses it as `inconsistent-mutant`, outside the score, never killed or survived.
//!
//! [`mutant_consistency`] decides it with k-rust's own load-time critical-pair check
//! (`k_rust_backend::confluence`, k-rust 501f18b9 `docs/compatibility.md`, "Anywhere rules"),
//! run on the claim-free mutant through
//! `BackendDefinition::value_claims_in_scope(CheckScope::All)`, the scope k-rust documents as "a
//! report of every pair that does not join". The check classifies each root pair (two executable
//! equations of one index and priority group, an `owise` group being its own priority, and an
//! equation with itself when a map or set pattern matches one subject in several ways) and each
//! inner pair, as separated by priority, refuted by the two `requires` (simplified with every
//! claim withheld), joined by innermost steps valid on every instance, or not joined. Not joined
//! covers every answer short of a proof: the reducts differ, a condition is neither refuted nor
//! decided, the `ensures` differ, the unifier meets a shape it does not decide, a join step is
//! refused, or the join runs out of its budget. Each of these, for a pair with an equation of a
//! checked head, refuses the mutant, naming the pair; so do k-rust's reports of a checked
//! equation the evaluator never applies as written, and a precondition row that puts an
//! equation outside the check (an equation indexed at a collection or a bare variable, an
//! overload equation of another shape, a family with no least common overload, an equation
//! headed by a constructor, and a pinned injective symbol). k-rust's premise, which this check
//! adds to kink's trust list: "M_NF is a model of the definition when evaluation terminates, which
//! every evaluation assumes, and the critical pairs of the executable equations join, which the
//! backend checks"; that is, k-rust's critical-pair checker decides joinability correctly.
//!
//! The checked heads are the symbols the patch redefines and every symbol whose equations reach
//! one ([`kink_patch::Withdrawal::affected`]): an unchanged pair of a symbol that reaches an
//! edited one can stop joining, since its reducts and conditions are normalized with the edited
//! equations. Every other pair is the baseline's and is normalized with the baseline's equations
//! alone, so it joins in the mutant exactly when it does in the baseline: the baseline's
//! equations stay a trusted premise, and the baseline is not checked.
//!
//! Two properties of k-rust's check need care, and each is closed here:
//!
//! - A definition that declares no equation head (an `anywhere` production that is not a
//!   declared function) and no overloaded symbol that can be withdrawn "has no pair checked: no
//!   pair can change a claim" (`compatibility.md`, the paragraph after "the load classifies only
//!   the pairs that can change a claim"), in either scope. That is most definitions kink mutates.
//!   kink therefore checks a copy of the mutant's KORE with one more declaration: a sort
//!   [`PROBE_SORT`] and a nullary equation head [`PROBE_SYMBOL`] (`anywhere`, no equation, so it
//!   appears in no equation, no pair and no step). The copy's executable equations, sorts and
//!   overload families are the mutant's, so every pair of the mutant is classified, and
//!   classified as k-rust classifies it in any definition with an equation head. kink also checks
//!   that the check ran: it must have classified at least as many pairs as the copy has root
//!   pairs (two equations of one index and priority group); otherwise the mutant is refused.
//! - A simplification of the check that runs out of native stack decides nothing, and then "the
//!   verdict is a function of the definition only when [`condition_stack_stops`] is zero"; a
//!   nonzero count refuses the mutant. Budget stops are a function of the definition, and a
//!   condition they cut short is not refuted, so they only leave a pair not joined.
//!
//! [`condition_stack_stops`]: k_rust_backend::confluence::CheckCounts::condition_stack_stops

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust::kast::identifier::{encode, encode_label};
use k_rust::kore::parser::parse_definition;
use k_rust_backend::{
    confluence::{CheckScope, UnjoinedPair, ViolationKind},
    definition::BackendDefinition,
    rule::{Concreteness, ConstraintKind, RewriteRule, TermIndex},
};

use crate::ValidatedDefinition;

/// The version of the consistency check: a mutant's admission depends on it, so every cache of
/// mutant outcomes names it (kink-flow's tier-1 context).
pub const MUTANT_CONSISTENCY_VERSION: &str = "kink-native/mutant-consistency/v1";

/// The sort of the equation head kink adds to the checked copy (see the module documentation).
pub const PROBE_SORT: &str = "SortKinkMutantConsistencyProbe";

/// The equation head kink adds to the checked copy: `anywhere`, nullary, with no equation.
pub const PROBE_SYMBOL: &str = "LblkinkMutantConsistencyProbe";

/// One pair of equations that k-rust's critical-pair check does not show to join (or one
/// equation it reports on its own), with its reason.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UnjoinedEquations {
    /// The equation whose left-hand side holds the overlap: its rule label, else its written
    /// position, else its unique id.
    pub first: String,
    /// The equation applied at the overlap, named alike (`first` again for a report on one
    /// equation or a self pair).
    pub second: String,
    /// The overlap position in `first`'s left-hand side, as argument indexes; empty for the root.
    pub position: Vec<usize>,
    /// k-rust's reason, as it prints it.
    pub reason: String,
}

impl UnjoinedEquations {
    /// The record of the pair in a report: `{first, second, position, reason}`.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        serde_json::json!({
            "first": self.first,
            "second": self.second,
            "position": self.position,
            "reason": self.reason,
        })
    }
}

impl fmt::Display for UnjoinedEquations {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} / {}", self.first, self.second)?;
        if !self.position.is_empty() {
            write!(formatter, " at {:?}", self.position)?;
        }
        write!(formatter, ": {}", self.reason)
    }
}

/// Why a mutant is not shown to be a theory with models.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Inconsistency {
    /// Pairs of a checked head's equations that k-rust's check does not show to join.
    Unjoined(Vec<UnjoinedEquations>),
    /// The check could not be run, or its verdict is not a function of the definition.
    Unchecked(String),
}

impl Inconsistency {
    /// The pairs to record, an unchecked mutant as one entry naming why.
    #[must_use]
    pub fn pairs(&self) -> Vec<UnjoinedEquations> {
        match self {
            Self::Unjoined(pairs) => pairs.clone(),
            Self::Unchecked(why) => vec![UnjoinedEquations {
                first: String::new(),
                second: String::new(),
                position: Vec::new(),
                reason: format!("the consistency check did not run: {why}"),
            }],
        }
    }
}

impl fmt::Display for Inconsistency {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unjoined(pairs) => {
                let pairs = pairs.iter().map(ToString::to_string).collect::<Vec<_>>();
                write!(formatter, "not shown to join: {}", pairs.join("; "))
            }
            Self::Unchecked(why) => write!(formatter, "the consistency check did not run: {why}"),
        }
    }
}

/// Whether the claim-free mutant `side` is shown to be a theory with models where its edit can
/// change one: every pair with an equation of a symbol of `heads` (K labels; `None` for every
/// symbol, when the edit's effect is not known symbol by symbol) joins by k-rust's critical-pair
/// check (see the module documentation).
///
/// # Errors
///
/// Returns the pairs not shown to join, or why the check could not decide.
pub fn mutant_consistency(
    side: &ValidatedDefinition,
    heads: Option<&BTreeSet<String>>,
) -> Result<(), Inconsistency> {
    if heads.is_some_and(BTreeSet::is_empty) {
        return Ok(());
    }
    let definition = checked_copy(side).map_err(Inconsistency::Unchecked)?;
    let heads = heads.map(|heads| heads.iter().map(|label| encode_label(label)).collect());
    check(&definition, heads.as_ref())
}

/// The mutant's definition with the probe sort and equation head added to its main module.
fn checked_copy(side: &ValidatedDefinition) -> Result<BackendDefinition, String> {
    let kore = &side.artifacts().definition_kore;
    if kore.contains(PROBE_SORT) || kore.contains(PROBE_SYMBOL) {
        return Err(format!(
            "the definition already names {PROBE_SORT} or {PROBE_SYMBOL}"
        ));
    }
    let mut parsed = parse_definition(kore).map_err(|e| e.to_string())?;
    let main = encode(&side.definition().main_module);
    let probe = parse_definition(&format!(
        "[] module KINKPROBE sort {PROBE_SORT}{{}} [] \
         symbol {PROBE_SYMBOL}{{}}() : {PROBE_SORT}{{}} [anywhere{{}}()] endmodule []"
    ))
    .map_err(|e| e.to_string())?;
    let sentences = probe
        .modules
        .into_iter()
        .next()
        .ok_or("the probe module did not parse")?
        .sentences;
    parsed
        .modules
        .iter_mut()
        .find(|module| module.name == main)
        .ok_or_else(|| format!("no main module {main} in the compiled KORE"))?
        .sentences
        .extend(sentences);
    BackendDefinition::internalize_for_source_execution(
        &parsed,
        &main,
        &side.artifacts().execution_rewrite_order,
    )
    .map_err(|e| e.to_string())
}

/// k-rust's check of every pair of `definition`, read for the KORE symbols `heads`.
fn check(
    definition: &BackendDefinition,
    heads: Option<&BTreeSet<String>>,
) -> Result<(), Inconsistency> {
    let claims = definition.value_claims_in_scope(CheckScope::All);
    let counts = claims.counts();
    if counts.condition_stack_stops > 0 {
        return Err(Inconsistency::Unchecked(format!(
            "{} simplifications of the check ran out of native stack",
            counts.condition_stack_stops
        )));
    }
    let mut index_of = BTreeMap::new();
    let mut root_pairs = 0;
    for (index, priorities) in definition.function_theory() {
        for rules in priorities.values() {
            for rule in rules {
                index_of.insert(rule.attributes.unique_id.clone(), index.clone());
            }
            let executable = rules.iter().filter(|rule| !symbolic(rule)).count();
            root_pairs += executable * executable.saturating_sub(1) / 2;
        }
    }
    if counts.pairs < root_pairs {
        return Err(Inconsistency::Unchecked(format!(
            "k-rust classified {} pairs of the {root_pairs} root pairs",
            counts.pairs
        )));
    }
    if let Some(heads) = heads {
        // A head kink-patch names must be a symbol of the compiled definition, or its pairs
        // would be read under no name.
        let missing = heads
            .iter()
            .filter(|head| !definition.symbols().contains_key(head.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        if !missing.is_empty() {
            return Err(Inconsistency::Unchecked(format!(
                "the heads {missing:?} are not symbols of the compiled definition"
            )));
        }
    }
    let checked_symbol = |name: &str| heads.is_none_or(|heads| heads.contains(name));
    let checked = |rule: &RewriteRule| match index_of.get(&rule.attributes.unique_id) {
        Some(TermIndex::Symbol(name)) => checked_symbol(name),
        // An equation not indexed at a symbol (at a conjunction, a domain value, a collection or
        // a bare variable) could be offered at a head's application: read it as every head's.
        _ => true,
    };
    let mut pairs = claims
        .unjoined()
        .iter()
        .filter(|pair| checked(&pair.first) || checked(&pair.second))
        .map(unjoined)
        .collect::<BTreeSet<_>>();
    for violation in claims.violations() {
        let outside = match &violation.kind {
            // An equation the check cannot pair with a head's equations (offered everywhere, or
            // at a collection): every head is unchecked.
            ViolationKind::IndexedAt(_) => true,
            ViolationKind::OverloadShape(symbol)
            | ViolationKind::PinnedByInjectiveTotal(symbol) => checked_symbol(symbol),
            ViolationKind::NoLeastCommonOverload(left, right) => {
                checked_symbol(left) || checked_symbol(right)
            }
            ViolationKind::ConstructorHeaded(_) | ViolationKind::InjectionHeaded => {
                violation.rule.as_deref().is_none_or(checked)
            }
        };
        if outside {
            let name = violation.rule.as_deref().map_or_else(String::new, name);
            pairs.insert(UnjoinedEquations {
                first: name.clone(),
                second: name,
                position: Vec::new(),
                reason: format!("outside the check: {}", violation.kind),
            });
        }
    }
    if pairs.is_empty() {
        Ok(())
    } else {
        Err(Inconsistency::Unjoined(pairs.into_iter().collect()))
    }
}

/// Whether k-rust's check skips `rule`: restricted to symbolic instances, it is never a step on
/// a ground term (`confluence.rs` `symbolic`).
fn symbolic(rule: &RewriteRule) -> bool {
    match &rule.attributes.concreteness {
        Concreteness::Unconstrained => false,
        Concreteness::All(kind) => *kind == ConstraintKind::Symbolic,
        Concreteness::Some(constraints) => constraints
            .values()
            .any(|kind| *kind == ConstraintKind::Symbolic),
    }
}

fn unjoined(pair: &UnjoinedPair) -> UnjoinedEquations {
    UnjoinedEquations {
        first: name(&pair.first),
        second: name(&pair.second),
        position: pair.position.clone(),
        reason: pair.reason.to_string(),
    }
}

/// An equation's name: its rule label, else its written position, else its unique id.
fn name(rule: &RewriteRule) -> String {
    rule.attributes
        .label
        .clone()
        .or_else(|| {
            rule.attributes
                .origins
                .first()
                .and_then(k_rust_backend::rule::RuleOrigin::written_position)
        })
        .unwrap_or_else(|| rule.attributes.unique_id.clone())
}
