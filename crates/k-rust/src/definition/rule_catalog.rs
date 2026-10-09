//! ```toml algorithm
//! id = "definition.catalog.rule"
//! name = "rule-catalog construction"
//! sites = ["RuleCatalog", "RuleCatalog::new", "RuleCatalog::from_visible", "collect_unique"]
//! variable = "n = visible rule-like sentences; l = local sentences; eq = sentence-equivalence cost; k_i = sentences in SentenceKey bucket i"
//! counters = ["KompileSentenceEquivalenceChecks"]
//!
//! [[cost]]
//! mode = "one catalog"
//! bound = "O((n + l) log (n + l) + sum k_i^2 x eq)"
//! ```
//!
//! Rule catalogs collect unique rule-like sentences and build declaration-order views by kind and label.
//! Construction compares a sentence only with those of its `SentenceKey`; `Counter::KompileSentenceEquivalenceChecks` counts its equivalence calls.
//!
//! Deterministic rule, claim, and context views for a resolved module.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::Sentence;
use super::attribute_keys::AttributeKey;
use super::catalog::{LabelHead, ProductionCatalog};
use super::equivalence::{EquivalenceAccumulator, dedup_by_equivalence};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::kast::{InternalLabel, Label, Term};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClaimId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContextId(pub usize);

#[derive(Clone, Debug)]
pub struct RuleCatalog<'a> {
    rules: Vec<&'a Sentence>,
    local_rules: BTreeSet<RuleId>,
    rules_by_label: BTreeMap<LabelHead, Vec<RuleId>>,
    claims: Vec<&'a Sentence>,
    local_claims: BTreeSet<ClaimId>,
    contexts: Vec<&'a Sentence>,
    macro_labels: BTreeSet<LabelHead>,
}

impl<'a> RuleCatalog<'a> {
    pub fn new(
        visible_sentences: impl IntoIterator<Item = &'a Sentence>,
        local_sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Self {
        let visible = visible_sentences.into_iter().collect::<Vec<_>>();
        let local = local_sentences.into_iter().collect::<Vec<_>>();
        let rules = collect_unique(&visible, |sentence| {
            matches!(sentence, Sentence::Rule { .. })
        });
        let claims = collect_unique(&visible, |sentence| {
            matches!(sentence, Sentence::Claim { .. })
        });
        let contexts = collect_unique(&visible, |sentence| {
            matches!(sentence, Sentence::Context { .. })
        });

        let local = EquivalenceAccumulator::from_sentences(local);
        let local_rules = local_ids(&rules, &local, RuleId);
        let local_claims = local_ids(&claims, &local, ClaimId);

        let mut rules_by_label = BTreeMap::<LabelHead, Vec<RuleId>>::new();
        let mut macro_labels = BTreeSet::new();
        for (index, rule) in rules.iter().enumerate() {
            let id = RuleId(index);
            let label = LabelHead::from(&match_rule_label(rule));
            rules_by_label.entry(label.clone()).or_default().push(id);
            if rule.attributes().has_any(&AttributeKey::MACRO_LIKE) {
                macro_labels.insert(label);
            }
        }

        Self {
            rules,
            local_rules,
            rules_by_label,
            claims,
            local_claims,
            contexts,
            macro_labels,
        }
    }

    pub fn from_visible(sentences: impl IntoIterator<Item = &'a Sentence>) -> Self {
        Self::new(sentences, std::iter::empty())
    }

    pub fn rules(&self) -> impl ExactSizeIterator<Item = (RuleId, &'a Sentence)> + '_ {
        self.rules
            .iter()
            .enumerate()
            .map(|(index, rule)| (RuleId(index), *rule))
    }

    pub fn rule(&self, id: RuleId) -> &'a Sentence {
        self.rules[id.0]
    }

    pub fn local_rule_ids(&self) -> &BTreeSet<RuleId> {
        &self.local_rules
    }

    pub fn local_rules(&self) -> impl ExactSizeIterator<Item = (RuleId, &'a Sentence)> + '_ {
        self.local_rules
            .iter()
            .copied()
            .map(|id| (id, self.rule(id)))
    }

    /// Rules by the head of the label [`match_rule_label`] gives them. A loaded rule's label
    /// carries no sort parameter, so the head is its identity.
    pub fn rules_by_label(&self) -> &BTreeMap<LabelHead, Vec<RuleId>> {
        &self.rules_by_label
    }

    /// The rules whose matched label has the head of `label`, whatever its sort parameters.
    pub fn rules_for(&self, label: &Label) -> &[RuleId] {
        self.rules_by_label
            .get(&LabelHead::from(label))
            .map_or(&[], Vec::as_slice)
    }

    pub fn claims(&self) -> impl ExactSizeIterator<Item = (ClaimId, &'a Sentence)> + '_ {
        self.claims
            .iter()
            .enumerate()
            .map(|(index, claim)| (ClaimId(index), *claim))
    }

    pub fn claim(&self, id: ClaimId) -> &'a Sentence {
        self.claims[id.0]
    }

    pub fn local_claim_ids(&self) -> &BTreeSet<ClaimId> {
        &self.local_claims
    }

    pub fn local_claims(&self) -> impl ExactSizeIterator<Item = (ClaimId, &'a Sentence)> + '_ {
        self.local_claims
            .iter()
            .copied()
            .map(|id| (id, self.claim(id)))
    }

    pub fn contexts(&self) -> impl ExactSizeIterator<Item = (ContextId, &'a Sentence)> + '_ {
        self.contexts
            .iter()
            .enumerate()
            .map(|(index, context)| (ContextId(index), *context))
    }

    pub fn context(&self, id: ContextId) -> &'a Sentence {
        self.contexts[id.0]
    }

    /// The heads of the labels of macro-like rules.
    pub fn macro_labels(&self) -> &BTreeSet<LabelHead> {
        &self.macro_labels
    }

    pub fn all_macro_labels(&self, productions: &ProductionCatalog<'_>) -> BTreeSet<LabelHead> {
        self.macro_labels
            .union(productions.macro_labels())
            .cloned()
            .collect()
    }

    pub fn rule_lhs_has_macro_label(
        &self,
        rule: RuleId,
        productions: &ProductionCatalog<'_>,
    ) -> bool {
        let Sentence::Rule { body, .. } = self.rule(rule) else {
            unreachable!()
        };
        let Term::Rewrite { left, .. } = body.unannotated() else {
            return false;
        };
        let Term::Apply { label, .. } = left.unannotated() else {
            return false;
        };
        productions.macro_labels().contains(&LabelHead::from(label))
    }
}

impl ResolvedDefinition {
    pub fn rule_catalog(&self, module: ModuleId) -> RuleCatalog<'_> {
        RuleCatalog::new(
            self.sentences(module),
            self.module(module)
                .local_sentences
                .iter()
                .map(std::sync::Arc::as_ref),
        )
    }
}

/// The symbol that heads a rule; under `#withConfig`, the head of its first argument, or of that
/// argument's left-hand side when it is a rewrite.
///
/// This is the one reading of the symbol that heads a rule. An alias `P #as V` matches exactly
/// the terms `P` matches and binds `V` to the whole term, so it is peeled wherever the head is
/// read: `f(X) #as V => r` is headed by `f`, like `f(X) => r`.
pub fn match_rule_label(rule: &Sentence) -> Label {
    let Sentence::Rule { body, .. } = rule else {
        panic!("match_rule_label requires a rule")
    };
    matched_term_label(body)
        .cloned()
        .unwrap_or_else(|| Label::new(""))
}

/// `term` without its annotations and the aliases around it.
fn unaliased(term: &Term) -> &Term {
    let mut term = term.unannotated();
    while let Term::As { pattern, .. } = term {
        term = pattern.unannotated();
    }
    term
}

fn matched_term_label(term: &Term) -> Option<&Label> {
    if let Term::Apply { label, arguments } = unaliased(term) {
        if label.is(InternalLabel::WithConfig) {
            match arguments.first().map(unaliased) {
                Some(Term::Apply { label, .. }) => return Some(label),
                Some(Term::Rewrite { left, .. }) => {
                    if let Term::Apply { label, .. } = unaliased(left) {
                        return Some(label);
                    }
                }
                _ => {}
            }
        }
        return Some(label);
    }
    if let Term::Rewrite { left, .. } = unaliased(term)
        && let Term::Apply { label, .. } = unaliased(left)
    {
        return Some(label);
    }
    None
}

fn collect_unique<'a>(
    sentences: &[&'a Sentence],
    predicate: impl Fn(&Sentence) -> bool,
) -> Vec<&'a Sentence> {
    dedup_by_equivalence(
        sentences
            .iter()
            .copied()
            .filter(|sentence| predicate(sentence)),
    )
}

/// The ids of the entries of `visible` equivalent to a local sentence. Equivalent sentences
/// have equal keys, so each entry is compared only with the local sentences of its key.
fn local_ids<Id: Ord>(
    visible: &[&Sentence],
    local: &EquivalenceAccumulator<'_>,
    id: impl Fn(usize) -> Id,
) -> BTreeSet<Id> {
    visible
        .iter()
        .enumerate()
        .filter(|(_, sentence)| local.find(sentence).is_some())
        .map(|(index, _)| id(index))
        .collect()
}
