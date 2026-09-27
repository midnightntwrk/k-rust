//! Trusted claims of a definition, and their withdrawal from a mutant.
//!
//! k-rust takes some attributes as axioms and never checks them: on a production `total`,
//! `functional`, `injective`, `smt-hook` and `smtlib`; on a rule `preserves-definedness`; and
//! the lemmas, `simplification` and `smt-lemma` rules; and a non-trivial `ensures` on an
//! equation. They are claims about what terms
//! denote. The baseline's author vouches for them. A mutant inherits them, although its
//! patch may have changed what they are about.
//!
//! What a term denotes is fixed by the equational part of a definition: the equations of each
//! symbol (function rules, `anywhere` rules and macro rules headed by it), the claims, and
//! the sorts and constructors that make up each sort's values. Rewrite rules are transitions
//! and never change what a term denotes, and neither do contexts or reachability claims.
//! So a claim about a symbol `f` is true or false by the equations of the symbols `f`'s
//! equations mention, transitively, and by the claims about those symbols; a claim of a rule
//! (its `preserves-definedness`, or the lemma it states) by the rule's own terms and by the
//! same closure over the symbols it mentions.
//!
//! [`ClaimSupport`] names that relation over one baseline. A patch *redefines* a symbol when
//! it edits, deletes or inserts an equation headed by it (in the baseline or in the mutant)
//! or edits a claim of its production. When a patch's effect on the equational part is not
//! known this precisely (it edits a production otherwise, a sort, a configuration, or a rule
//! whose head cannot be read), every symbol counts as redefined. A claim is *supported* in
//! the mutant when no symbol of its closure is redefined and the patch left its own sentence
//! alone: then every sentence and claim it rests on is the baseline's, and it holds in the
//! mutant exactly as in the baseline. Every other claim of the mutant is withdrawn when an
//! attribute removal can withdraw it, and otherwise is *unsupported*: a claim the patch
//! itself writes (a hypothesis that withdrawing would undo), and a lemma, whose removal
//! would change the rule rather than the trust in it.
//!
//! An equation's open `ensures` is assumed wherever the equation applies, whether the equation
//! is a lemma or a definition. An equation's non-trivial `ensures` is therefore a claim of the
//! equation, supported by its sentence and by the equations of every symbol it mentions.
//!
//! The lambdas k-rust generates for `#let` and `#fun` are not claims of the written definition.
//! They are generated when the mutant is compiled, after the patch, and a lambda is declared
//! `total` only when its pattern is a variable and its body is built from constructors, `total`
//! functions and such lambdas (k-rust KK-71). Its claim is thus derived from the mutant's own
//! body, and it rests on the claims of the functions that body calls, which this relation
//! already withdraws when their support is touched.
//!
//! Withdrawing is sound: removing an axiom that holds only weakens the theory, and one that
//! may not hold can no longer make it inconsistent. The withdrawn definition is an ordinary
//! original-relative patch result: the patch's own edits and a `RemoveAttribute` per
//! withdrawn claim (a claim a replacement sentence carries over from the sentence it replaces
//! is dropped from the replacement instead).

use crate::apply::{Mutant, SentenceOrigin, apply};
use crate::failure::PatchFailure;
use crate::{Baseline, Edit, Patch, SentenceRef};
use k_rust::definition::{AttributeKey, Definition, Sentence};
use k_rust::kast::Term;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

/// Production attributes that assert a property of the symbol's equations.
const SYMBOL_CLAIMS: [AttributeKey; 5] = [
    AttributeKey::Total,
    AttributeKey::Functional,
    AttributeKey::Injective,
    AttributeKey::SmtHook,
    AttributeKey::Smtlib,
];

/// Rule attributes that assert a property of the rule, withdrawn by removing the attribute.
const RULE_CLAIMS: [AttributeKey; 1] = [AttributeKey::PreservesDefinedness];

/// Rule attributes that make the rule a lemma about other rules rather than a definition.
const LEMMAS: [AttributeKey; 2] = [AttributeKey::Simplification, AttributeKey::SmtLemma];

/// One trusted claim of a mutant: an attribute or a non-trivial equation `ensures`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Claim {
    /// The mutant sentence's origin: a baseline sentence or the patch's inserting edit.
    pub origin: SentenceOrigin,
    pub key: String,
    pub value: Value,
}

/// The claims a patch leaves unsupported, and the patch that withdraws those it can.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Withdrawal {
    /// Claims whose support the patch touched, removed from the withdrawn definition.
    pub withdrawn: Vec<Claim>,
    /// Claims the patch itself writes, and lemmas or equation `ensures` whose support it
    /// touched. No definition with only supported claims exists for such a mutant.
    pub unsupported: Vec<Claim>,
    patch: Option<Patch>,
}

impl Withdrawal {
    /// Whether every trusted claim left in the withdrawn definition is a baseline claim whose
    /// support the patch did not touch.
    #[must_use]
    pub fn trusted(&self) -> bool {
        self.unsupported.is_empty()
    }

    /// The original-relative patch whose result withdraws [`Self::withdrawn`]: the patch's
    /// own edits and one `RemoveAttribute` per withdrawn claim. `None` when nothing is
    /// withdrawn, so the patch's own result is the withdrawn definition.
    #[must_use]
    pub const fn patch(&self) -> Option<&Patch> {
        self.patch.as_ref()
    }
}

/// How a rule sentence takes part in the equational theory.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Role {
    /// An equation of the symbol: a function, `anywhere` or macro rule headed by it.
    Equation(String),
    /// A lemma (`simplification`, `smt-lemma`): a claim, never a definition.
    Lemma,
    /// A transition, which never changes what a term denotes.
    Rewrite,
    /// An `anywhere` or macro rule whose head symbol cannot be read.
    Unknown,
}

/// The support relation of one baseline's trusted claims.
#[derive(Clone, Debug)]
pub struct ClaimSupport {
    /// Labels whose applications are equationally defined: a production with `function` or a
    /// macro-like attribute.
    defined: BTreeSet<String>,
    /// For each symbol, the symbols whose equations mention it.
    dependents: BTreeMap<String, BTreeSet<String>>,
}

impl ClaimSupport {
    /// Reads every equation of `baseline`, the prelude's included.
    #[must_use]
    pub fn new(baseline: &Baseline) -> Self {
        let definition = baseline.definition();
        let defined = defined_labels(definition);
        let mut dependents = BTreeMap::<String, BTreeSet<String>>::new();
        for (_, sentence) in sentences(definition) {
            if let Role::Equation(head) = role(sentence, &defined) {
                for mentioned in mentions(sentence) {
                    dependents
                        .entry(mentioned)
                        .or_default()
                        .insert(head.clone());
                }
            }
        }
        Self {
            defined,
            dependents,
        }
    }

    /// The claims of `patch`'s mutant that the patch leaves unsupported, and the withdrawing
    /// patch.
    ///
    /// # Errors
    ///
    /// Returns the failure of applying `patch` to `baseline`.
    pub fn withdraw(&self, baseline: &Baseline, patch: &Patch) -> Result<Withdrawal, PatchFailure> {
        let mutant = apply(baseline, patch)?;
        let edits = patch.edits();
        let touched = touched_sentences(edits);
        let redefined = self.redefined(baseline, &mutant, edits, &touched);
        let affected = redefined.map(|redefined| self.affected(redefined));
        let is_affected = |symbols: &BTreeSet<String>| {
            affected
                .as_ref()
                .is_none_or(|affected| symbols.iter().any(|symbol| affected.contains(symbol)))
        };

        let mut withdrawal = Withdrawal::default();
        let mut removals = Vec::new();
        let mut stripped = BTreeMap::<usize, Vec<String>>::new();
        for (at, origin) in mutant.origins() {
            let Some(sentence) = sentence_at(mutant.definition(), at) else {
                continue;
            };
            let attributes = sentence.attributes();
            let claim = |key: AttributeKey| {
                attributes.value(key).map(|value| Claim {
                    origin: origin.clone(),
                    key: key.as_str().to_owned(),
                    value: value.clone(),
                })
            };
            let baseline_at = match origin {
                SentenceOrigin::Baseline(at) => Some(at),
                SentenceOrigin::Inserted { .. } => None,
            };
            let writes = |key: AttributeKey| {
                baseline_at.is_some_and(|at| writes_attribute(edits, at, key.as_str()))
            };
            match sentence {
                Sentence::Production { label, .. } => {
                    for key in SYMBOL_CLAIMS {
                        let Some(claim) = claim(key) else { continue };
                        if writes(key) {
                            withdrawal.unsupported.push(claim);
                        } else if label
                            .as_ref()
                            .is_none_or(|label| is_affected(&BTreeSet::from([label.name.clone()])))
                        {
                            removals.push(removal(baseline_at, &claim));
                            withdrawal.withdrawn.push(claim);
                        }
                    }
                }
                Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Context { .. }
                | Sentence::ContextAlias { .. } => {
                    let replaced = baseline_at.and_then(|at| replacing_edit(edits, at));
                    let edited = baseline_at.is_none_or(|at| touched.contains(at));
                    let unsupported = edited || is_affected(&mentions(sentence));
                    if let Sentence::Rule { ensures, .. } = sentence
                        && matches!(role(sentence, &self.defined), Role::Equation(_))
                        && !trivial_ensures(ensures)
                        && unsupported
                    {
                        withdrawal.unsupported.push(Claim {
                            origin: origin.clone(),
                            key: "ensures".to_owned(),
                            value: Value::String(ensures.to_string()),
                        });
                    }
                    for claim in LEMMAS.into_iter().filter_map(claim) {
                        if unsupported {
                            withdrawal.unsupported.push(claim);
                        }
                    }
                    for key in RULE_CLAIMS {
                        let Some(claim) = claim(key) else { continue };
                        let inherited = |at: &SentenceRef| {
                            baseline
                                .sentence(at)
                                .and_then(|original| original.attributes().value(key))
                                == Some(&claim.value)
                        };
                        match (baseline_at, replaced) {
                            // A new sentence's claim is the patch's own.
                            (None, _) => withdrawal.unsupported.push(claim),
                            (Some(at), Some(edit)) if inherited(at) => {
                                stripped.entry(edit).or_default().push(claim.key.clone());
                                withdrawal.withdrawn.push(claim);
                            }
                            (Some(_), Some(_)) => withdrawal.unsupported.push(claim),
                            (Some(_), None) if writes(key) => withdrawal.unsupported.push(claim),
                            (Some(at), None) if unsupported => {
                                removals.push(removal(Some(at), &claim));
                                withdrawal.withdrawn.push(claim);
                            }
                            (Some(_), None) => {}
                        }
                    }
                }
                _ => {}
            }
        }
        if !withdrawal.withdrawn.is_empty() {
            let mut edits = edits.to_vec();
            for (index, keys) in stripped {
                if let Edit::ReplaceSentence { replacement, .. } = &mut edits[index] {
                    for key in keys {
                        replacement.attributes_mut().remove(&key);
                    }
                }
            }
            edits.extend(removals);
            withdrawal.patch = Some(Patch::new(edits).expect("a nonempty patch"));
        }
        Ok(withdrawal)
    }

    /// The symbols `edits` redefine, or `None` when their effect on the equational part is not
    /// known symbol by symbol.
    fn redefined(
        &self,
        baseline: &Baseline,
        mutant: &Mutant,
        edits: &[Edit],
        touched: &BTreeSet<&SentenceRef>,
    ) -> Option<BTreeSet<String>> {
        let mut redefined = BTreeSet::new();
        // The symbol a rule is an equation of, or `None` when that cannot be read.
        let head = |sentence: &Sentence| match role(sentence, &self.defined) {
            Role::Equation(head) => Some(Some(head)),
            Role::Unknown => None,
            Role::Lemma | Role::Rewrite => Some(None),
        };
        for at in touched {
            let sentence = baseline.sentence(at)?;
            match sentence {
                Sentence::Rule { .. } => redefined.extend(head(sentence)?),
                Sentence::Claim { .. }
                | Sentence::Context { .. }
                | Sentence::ContextAlias { .. } => {}
                Sentence::Production { .. } => {
                    // Only a claim edit keeps the sort's values and the symbol's kind.
                    if !edits.iter().all(|edit| match edit {
                        Edit::AddAttribute {
                            at: edited, key, ..
                        }
                        | Edit::RemoveAttribute {
                            at: edited, key, ..
                        }
                        | Edit::ReplaceAttribute {
                            at: edited, key, ..
                        } => edited != *at || is_symbol_claim(key),
                        Edit::DeleteSentence { at: edited } => edited != *at,
                        _ => true,
                    }) {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        for (at, origin) in mutant.origins() {
            let edited = match origin {
                SentenceOrigin::Baseline(original) => touched.contains(original),
                SentenceOrigin::Inserted { .. } => true,
            };
            if edited {
                let sentence = sentence_at(mutant.definition(), at)?;
                match sentence {
                    Sentence::Rule { .. } => redefined.extend(head(sentence)?),
                    Sentence::Production { label, .. } => {
                        redefined.insert(label.as_ref()?.name.clone());
                    }
                    _ => {}
                }
            }
        }
        Some(redefined)
    }

    /// Every symbol whose equations reach a redefined symbol, the redefined ones included.
    fn affected(&self, redefined: BTreeSet<String>) -> BTreeSet<String> {
        let mut affected = BTreeSet::new();
        let mut pending = redefined.into_iter().collect::<Vec<_>>();
        while let Some(symbol) = pending.pop() {
            if let Some(dependents) = self.dependents.get(&symbol) {
                pending.extend(dependents.difference(&affected).cloned());
            }
            affected.insert(symbol);
        }
        affected
    }
}

/// The default `ensures true` asserts no property of an equation's result.
fn trivial_ensures(ensures: &Term) -> bool {
    matches!(ensures.unannotated(), Term::Token { token, sort } if token == "true" && sort.name == "Bool")
}

fn is_symbol_claim(key: &str) -> bool {
    SYMBOL_CLAIMS.iter().any(|claim| claim.as_str() == key)
}

fn removal(at: Option<&SentenceRef>, claim: &Claim) -> Edit {
    Edit::RemoveAttribute {
        at: at.expect("a baseline sentence").clone(),
        key: claim.key.clone(),
        expected: claim.value.clone(),
    }
}

/// The baseline sentences an edit replaces, edits a term or attribute of, or deletes.
fn touched_sentences(edits: &[Edit]) -> BTreeSet<&SentenceRef> {
    edits
        .iter()
        .filter_map(|edit| match edit {
            Edit::ReplaceTerm { at, .. } => Some(&at.sentence),
            Edit::ReplaceSentence { at, .. }
            | Edit::DeleteSentence { at }
            | Edit::AddAttribute { at, .. }
            | Edit::RemoveAttribute { at, .. }
            | Edit::ReplaceAttribute { at, .. } => Some(at),
            Edit::InsertSentence { .. } => None,
        })
        .collect()
}

/// Whether an edit adds or replaces the attribute `key` of `at`.
fn writes_attribute(edits: &[Edit], at: &SentenceRef, key: &str) -> bool {
    edits.iter().any(|edit| match edit {
        Edit::AddAttribute {
            at: edited,
            key: written,
            ..
        }
        | Edit::ReplaceAttribute {
            at: edited,
            key: written,
            ..
        } => edited == at && written == key,
        _ => false,
    })
}

/// The index of the edit that replaces `at` as a whole.
fn replacing_edit(edits: &[Edit], at: &SentenceRef) -> Option<usize> {
    edits.iter().position(
        |edit| matches!(edit, Edit::ReplaceSentence { at: replaced, .. } if replaced == at),
    )
}

fn sentences(definition: &Definition) -> impl Iterator<Item = (SentenceRef, &Sentence)> {
    definition.modules.iter().flat_map(|module| {
        module
            .local_sentences
            .iter()
            .enumerate()
            .filter_map(|(index, sentence)| {
                let index = u32::try_from(index).ok()?;
                Some((SentenceRef::new(module.name.clone(), index), &**sentence))
            })
    })
}

fn sentence_at<'a>(definition: &'a Definition, at: &SentenceRef) -> Option<&'a Sentence> {
    definition
        .modules
        .iter()
        .find(|module| module.name == at.module)?
        .local_sentences
        .get(usize::try_from(at.index).ok()?)
        .map(|sentence| &**sentence)
}

fn defined_labels(definition: &Definition) -> BTreeSet<String> {
    sentences(definition)
        .filter_map(|(_, sentence)| match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has(AttributeKey::Function)
                || attributes.has_any(&AttributeKey::MACRO_LIKE) =>
            {
                Some(label.name.clone())
            }
            _ => None,
        })
        .collect()
}

fn role(sentence: &Sentence, defined: &BTreeSet<String>) -> Role {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return Role::Rewrite;
    };
    if attributes.has_any(&LEMMAS) {
        return Role::Lemma;
    }
    let left = match body.unannotated() {
        Term::Rewrite { left, .. } => left,
        body => body,
    };
    let equational =
        attributes.has(AttributeKey::Anywhere) || attributes.has_any(&AttributeKey::MACRO_LIKE);
    match head(left) {
        Some(head) if equational || defined.contains(head) => Role::Equation(head.to_owned()),
        Some(_) => Role::Rewrite,
        None if equational => Role::Unknown,
        None => Role::Rewrite,
    }
}

/// The symbol at the top of a left-hand side, through annotations, as-patterns and casts.
fn head(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::As { pattern, .. } => head(pattern),
        Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
            head(arguments.first()?)
        }
        Term::Apply { label, .. } => Some(&label.name),
        _ => None,
    }
}

/// Every symbol a rule-like sentence's terms apply.
fn mentions(sentence: &Sentence) -> BTreeSet<String> {
    let terms: Vec<&Term> = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => vec![body, requires],
        _ => Vec::new(),
    };
    let mut symbols = BTreeSet::new();
    let mut pending = terms;
    while let Some(term) = pending.pop() {
        match term.unannotated() {
            Term::InjectedLabel(label) => {
                symbols.insert(label.name.clone());
            }
            Term::Apply { label, arguments } => {
                symbols.insert(label.name.clone());
                pending.extend(arguments);
            }
            Term::Rewrite { left, right } => pending.extend([&**left, &**right]),
            Term::As { pattern, alias } => pending.extend([&**pattern, &**alias]),
            Term::Sequence(items) => pending.extend(items),
            Term::Variable { .. } | Term::Token { .. } | Term::Annotated { .. } => {}
        }
    }
    symbols
}
