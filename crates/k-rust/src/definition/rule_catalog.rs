//! Deterministic rule, claim, and context views for a resolved module.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::Sentence;
use super::catalog::{ProductionCatalog, is_macro};
use super::ordering::{compare_sentences, sentence_equivalent};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::kast::{Label, Term};

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
    sorted_rules: Vec<RuleId>,
    rules_by_label: BTreeMap<Label, Vec<RuleId>>,
    claims: Vec<&'a Sentence>,
    local_claims: BTreeSet<ClaimId>,
    contexts: Vec<&'a Sentence>,
    macro_labels: BTreeSet<Label>,
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

        let local_rules = local_ids(&rules, &local, RuleId);
        let local_claims = local_ids(&claims, &local, ClaimId);
        let mut sorted_rules = (0..rules.len()).map(RuleId).collect::<Vec<_>>();
        sorted_rules.sort_by(|left, right| {
            compare_sentences(rules[left.0], rules[right.0])
                .expect("rules always have Scala ordering")
                .then(left.cmp(right))
        });

        let mut rules_by_label = BTreeMap::<Label, Vec<RuleId>>::new();
        let mut macro_labels = BTreeSet::new();
        for (index, rule) in rules.iter().enumerate() {
            let id = RuleId(index);
            let label = match_rule_label(rule);
            rules_by_label.entry(label.clone()).or_default().push(id);
            if is_macro(rule.attributes()) {
                macro_labels.insert(label);
            }
        }

        Self {
            rules,
            local_rules,
            sorted_rules,
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

    pub fn sorted_rule_ids(&self) -> &[RuleId] {
        &self.sorted_rules
    }

    pub fn sorted_rules(&self) -> impl ExactSizeIterator<Item = (RuleId, &'a Sentence)> + '_ {
        self.sorted_rules
            .iter()
            .copied()
            .map(|id| (id, self.rule(id)))
    }

    pub fn rules_by_label(&self) -> &BTreeMap<Label, Vec<RuleId>> {
        &self.rules_by_label
    }

    pub fn rules_for(&self, label: &Label) -> &[RuleId] {
        self.rules_by_label.get(label).map_or(&[], Vec::as_slice)
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

    pub fn macro_labels(&self) -> &BTreeSet<Label> {
        &self.macro_labels
    }

    pub fn all_macro_labels(&self, productions: &ProductionCatalog<'_>) -> BTreeSet<Label> {
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
        let Term::Rewrite { left, .. } = body else {
            return false;
        };
        let Term::Apply { label, .. } = left.as_ref() else {
            return false;
        };
        productions.macro_labels().contains(label)
    }
}

impl ResolvedDefinition {
    pub fn rule_catalog(&self, module: ModuleId) -> RuleCatalog<'_> {
        RuleCatalog::new(
            self.sentences(module),
            self.module(module).local_sentences.iter(),
        )
    }
}

/// Scala's `Module.matchKLabel`, including its two `#withConfig` cases.
pub fn match_rule_label(rule: &Sentence) -> Label {
    let Sentence::Rule { body, .. } = rule else {
        panic!("match_rule_label requires a rule")
    };
    matched_term_label(body)
        .cloned()
        .unwrap_or_else(|| Label::new(""))
}

fn matched_term_label(term: &Term) -> Option<&Label> {
    if let Term::Apply { label, arguments } = term {
        if label.name == "#withConfig" {
            match arguments.first() {
                Some(Term::Apply { label, .. }) => return Some(label),
                Some(Term::Rewrite { left, .. }) => {
                    if let Term::Apply { label, .. } = left.as_ref() {
                        return Some(label);
                    }
                }
                _ => {}
            }
        }
        return Some(label);
    }
    if let Term::Rewrite { left, .. } = term
        && let Term::Apply { label, .. } = left.as_ref()
    {
        return Some(label);
    }
    None
}

fn collect_unique<'a>(
    sentences: &[&'a Sentence],
    predicate: impl Fn(&Sentence) -> bool,
) -> Vec<&'a Sentence> {
    let mut collected: Vec<&'a Sentence> = Vec::new();
    for &sentence in sentences {
        if predicate(sentence)
            && !collected
                .iter()
                .any(|existing| sentence_equivalent(existing, sentence))
        {
            collected.push(sentence);
        }
    }
    collected
}

fn local_ids<Id: Ord>(
    visible: &[&Sentence],
    local: &[&Sentence],
    id: impl Fn(usize) -> Id,
) -> BTreeSet<Id> {
    visible
        .iter()
        .enumerate()
        .filter(|(_, sentence)| {
            local
                .iter()
                .any(|local| sentence_equivalent(sentence, local))
        })
        .map(|(index, _)| id(index))
        .collect()
}
