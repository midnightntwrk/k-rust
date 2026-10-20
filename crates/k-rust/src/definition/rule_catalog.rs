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
use crate::kast::{GeneratedLabel, InternalLabel, Label, Term};

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
/// This is [`RuleHead::of`]'s label, or the empty label when the head is not an application.
pub fn match_rule_label(rule: &Sentence) -> Label {
    let Sentence::Rule { body, .. } = rule else {
        panic!("match_rule_label requires a rule")
    };
    RuleHead::of(body)
        .label()
        .cloned()
        .unwrap_or_else(|| Label::new(""))
}

/// Whether a rule body has a rewrite at its top (under `#withConfig`'s first argument when the
/// body is one), or none.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeadShape {
    /// `L => R`: the head is read from `L`.
    TopRewrite,
    /// No rewrite at the top: the head is read from the body itself.
    NoRewrite,
}

/// The one reading of "which symbol does this rule define": the root of the left-hand side of
/// a rule body's top rewrite, or of the body when it has none.
///
/// A rule's defining symbol is a property of its left-hand pattern. An alias `P #as V` denotes
/// exactly the terms `P` denotes and binds `V` to the matched term, so it constrains nothing
/// beyond naming the subject: `f(X) #as V => R` has the instances of `f(X) => R[f(X)/V]` and is
/// headed by `f`, like it. Every root alias, and every annotation, is therefore looked through
/// ([`peel_aliases`]). Under `#withConfig(E, C)` the head is that of `E`, with `C` as the
/// rule's configuration context, when `E` is headed by an application; otherwise the body is
/// read as written.
///
/// Every classification keyed on the defining head (function equation versus rewrite of the
/// computation cell, macro rule, `anywhere` equation, the number of rules of a symbol,
/// dependency edges) reads it here, so two stages cannot classify one rule differently. A
/// caller that needs a top rewrite tests [`Self::shape`] explicitly; an injection head `inj`
/// is the head itself, and [`Self::injected`] reads its argument for a caller that wants it.
#[derive(Clone, Copy, Debug)]
pub struct RuleHead<'a> {
    /// The left-hand side as written, root aliases and annotations included: the body itself
    /// when it has no top rewrite.
    pub left: &'a Term,
    /// `left` without its root aliases: the root pattern, annotations kept so its metadata
    /// (the production it resolves to, its sort) can be read.
    pub root: &'a Term,
    /// The right-hand side of the top rewrite; `None` for [`HeadShape::NoRewrite`].
    pub right: Option<&'a Term>,
    /// The configuration context `C` of a `#withConfig(E, C)` body.
    pub context: Option<&'a Term>,
}

impl<'a> RuleHead<'a> {
    /// The head of the rule body `body`.
    pub fn of(body: &'a Term) -> Self {
        if let Term::Apply { label, arguments } = unaliased(body)
            && label.is(InternalLabel::WithConfig)
            && let Some(first) = arguments.first()
        {
            let inner = Self::without_context(first);
            if inner.label().is_some() {
                return Self {
                    context: arguments.get(1),
                    ..inner
                };
            }
        }
        Self::without_context(body)
    }

    fn without_context(body: &'a Term) -> Self {
        match unaliased(body) {
            Term::Rewrite { left, right } => Self {
                left,
                root: peel_aliases(left),
                right: Some(right.as_ref()),
                context: None,
            },
            Term::Apply { .. }
            | Term::Variable { .. }
            | Term::Token { .. }
            | Term::InjectedLabel(_)
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => Self {
                left: body,
                root: peel_aliases(body),
                right: None,
                context: None,
            },
        }
    }

    pub fn shape(&self) -> HeadShape {
        if self.right.is_some() {
            HeadShape::TopRewrite
        } else {
            HeadShape::NoRewrite
        }
    }

    /// The root application: the annotated root term, its label and its arguments.
    pub fn application(&self) -> Option<(&'a Term, &'a Label, &'a [Term])> {
        match self.root.unannotated() {
            Term::Apply { label, arguments } => Some((self.root, label, arguments.as_slice())),
            Term::Variable { .. }
            | Term::Token { .. }
            | Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => None,
        }
    }

    /// The label of the root application.
    pub fn label(&self) -> Option<&'a Label> {
        self.application().map(|(_, label, _)| label)
    }

    /// The names of the variables the root aliases of [`Self::left`] bind, outermost first:
    /// `V` and `W` for `(P #as W) #as V`. A semantic cast around an alias is looked through
    /// (`P #as V:S` binds `V`); an alias that is not a variable names nothing.
    pub fn root_alias_variables(&self) -> Vec<&'a str> {
        let mut names = Vec::new();
        let mut term = self.left;
        while let Term::As { pattern, alias } = term.unannotated() {
            let mut variable = alias.unannotated();
            if let Term::Apply { label, arguments } = variable
                && matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
                && let [argument] = arguments.as_slice()
            {
                variable = argument.unannotated();
            }
            if let Term::Variable { name, .. } = variable {
                names.push(name.as_str());
            }
            term = pattern;
        }
        names
    }

    /// When the root is an injection `inj(A)`, the label of `A`'s root application (aliases
    /// looked through): the symbol a rule written at an injected position is a rule of.
    pub fn injected(&self) -> Option<&'a Label> {
        let (_, label, arguments) = self.application()?;
        if !label.is(crate::names::WellKnownSymbol::Inj) {
            return None;
        }
        match unaliased(arguments.first()?) {
            Term::Apply { label, .. } => Some(label),
            Term::Variable { .. }
            | Term::Token { .. }
            | Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => None,
        }
    }
}

/// `term` without the aliases at its root, keeping the annotations of the pattern they alias:
/// `(P #as V) #as W` is `P`.
pub fn peel_aliases(mut term: &Term) -> &Term {
    while let Term::As { pattern, .. } = term.unannotated() {
        term = pattern;
    }
    term
}

/// `term` without its annotations and the aliases around it.
fn unaliased(term: &Term) -> &Term {
    peel_aliases(term).unannotated()
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
