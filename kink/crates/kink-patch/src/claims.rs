//! Trusted claims of a definition, and their removal from a mutant.
//!
//! k-rust takes some attributes and axioms as true and never checks them (its "contract", k-rust
//! 0068938b1 `docs/compatibility.md` 1136, and [`TRUSTED_CLAIMS`] with a citation for each): on a
//! production `total`, `functional`, `injective`, `smt-hook` and `smtlib`; on a rule
//! `preserves-definedness` and `smt-lemma`; the `simplification` lemmas; a non-trivial `ensures`
//! of a function equation; that an equation restricted by `concrete` or `symbolic` is a theorem
//! of the executable equations; and that a hooked symbol's equations agree with its hook. They
//! are claims about what terms denote, which the baseline's author vouches for.
//!
//! The principle (Sebastien, 2026-10-17): a claim is the spec author's assertion about the
//! definition they wrote. When a mutation edits part of the definition, every claim whose truth
//! depends on the edited part is no longer backed by anyone, and the mutant must not carry it.
//! kink builds each mutant with those claims removed ([`ClaimSupport::withdraw`], the one
//! function every route that builds a mutant goes through), so the mutant is a consistent theory
//! that k-rust executes without trusting them. The baseline keeps all its claims: the author's
//! claims about the unedited specification stay a trusted premise.
//!
//! What a term denotes is fixed by the equational part of a definition: the equations of each
//! symbol (function rules, `anywhere` rules and macro rules headed by it, an `smt-lemma` among
//! them unless it is a `simplification`), the claims, and the sorts and constructors that make
//! up each sort's values. Rewrite rules are transitions and never change what a term denotes,
//! and neither do contexts or reachability claims. So a claim about a symbol `f` is true or false
//! by the equations of the symbols `f`'s equations mention (left side, right side, `requires`
//! and `ensures`), transitively, and by the claims about those symbols; a claim of a rule (its
//! `preserves-definedness`, or the lemma it states) by the rule's own terms and by the same
//! closure over the symbols it mentions.
//!
//! [`ClaimSupport`] names that relation over one baseline. A patch *redefines* a symbol when
//! it edits, deletes or inserts an equation headed by it (in the baseline or in the mutant)
//! or edits a claim of its production: these are the edited symbols E, read from the head of
//! each edited sentence as k-rust reads it (under `#withConfig`, the rule form `[[ F ]] C` of a
//! function rule with configuration context, the head of `F`; re-pin R0c-fix-4). This is the
//! source reading of the edit; kink-native reads the compiled definitions against it
//! ([`ClaimSupport::effect`]), and a compiled equation of a touched sentence whose head is not in
//! E refuses the mutant ([`UNREAD_EQUATION_CLAIM`]). A symbol *reaches* E when one of its equations applies a symbol of E
//! or a symbol that reaches E (the reverse call-graph closure). The equations read are the
//! written ones and those kompile generates that link symbols: each member of an
//! `overload(key)` family reaches every other (the overload axiom `g(inj(x)) = inj(l(x))` is an
//! equation of the greater `g` that mentions the lesser `l`), and a production with `unit(u)`
//! reaches `u` (its unit axiom mentions `u`); subsort axioms link sorts, not symbols (re-pin
//! R0c-fix-3, `generated_links`). When a patch's effect on the
//! equational part is not known this precisely (it edits a production otherwise, a sort, a
//! configuration, or a rule whose head cannot be read), every symbol counts as redefined. A
//! claim is *supported* in the mutant when no symbol of its closure is redefined and the patch
//! left its own sentence alone: then every sentence and claim it rests on is the baseline's,
//! and it holds in the mutant exactly as in the baseline. An edit of a rewrite rule only
//! redefines nothing, so it removes only that rule's own claims.
//!
//! Every other claim is removed from the mutant ([`Withdrawal::withdrawn`]): the symbol claims of
//! every symbol in E or reaching E (a `RemoveAttribute`), the `preserves-definedness` and
//! `smt-lemma` attributes of every rule that is edited or mentions such a symbol, and every
//! `simplification` lemma that mentions one (a `DeleteSentence`: a lemma is a claim as a whole,
//! and removing an axiom only weakens the theory). A claim that no removal takes away without
//! changing the definition is *unsupported* ([`Withdrawal::unsupported`]), and the mutant is
//! refused rather than built with it: a claim the patch itself writes (removing it would undo
//! the mutant), a lemma the patch edits or inserts, an equation's non-trivial `ensures` (k-rust
//! reads an `ensures` that is false as an undefined application, so dropping it changes what the
//! equation says), a `concrete` or `symbolic` equation, and an equation of a hooked symbol.
//!
//! The lambdas k-rust generates for `#let` and `#fun` are not claims of the written definition.
//! They are generated when the mutant is compiled, after the patch, and a lambda is declared
//! `total` only when its pattern is a variable and its body is built from constructors, `total`
//! functions and such lambdas (k-rust KK-71). Its claim is thus derived from the mutant's own
//! body, and it rests on the claims of the functions that body calls, which this relation
//! already withdraws when their support is touched. Likewise kompile derives `constructor`,
//! `injective` freeness and a value production's `functional` from the mutant's own sentences.
//!
//! Withdrawing is sound: removing an axiom that holds only weakens the theory, and one that
//! may not hold can no longer make it inconsistent. The withdrawn definition is an ordinary
//! original-relative patch result: the patch's own edits, a `RemoveAttribute` per withdrawn
//! attribute and a `DeleteSentence` per withdrawn lemma (a claim a replacement sentence carries
//! over from the sentence it replaces is dropped from the replacement instead).

use crate::apply::{Mutant, SentenceOrigin, apply};
use crate::failure::PatchFailure;
use crate::{Baseline, Edit, Patch, SentenceRef};
use k_rust::definition::{AttributeKey, Definition, Sentence};
use k_rust::kast::{InternalLabel, Term};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

/// The version of the claim-removal algorithm ([`ClaimSupport::withdraw`]): a mutant's identity
/// depends on it, so kink's semantics identity names it (kink-campaign `identity`), on which every
/// store keys. v2
/// (re-pin R0c-fix-3): the reach follows kompile's generated overload and unit axioms. v3 (re-pin
/// R0c-fix-4): a rule written with configuration context (`[[ F ]] C`) is read as an equation of
/// `F`'s head.
pub const CLAIM_REMOVAL_VERSION: &str = "kink-patch/claim-removal/v3";

/// One kind of claim k-rust trusts, how kink removes it from a mutant, and where k-rust 0068938b1
/// says it is trusted (paths relative to `crates/` or `docs/` of the k-rust tree).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TrustedClaim {
    /// The attribute key, or `ensures`, `concrete-equation` or `hooked-equation`.
    pub claim: &'static str,
    pub removal: ClaimRemoval,
    pub citation: &'static str,
}

/// How kink takes a trusted claim away from a mutant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClaimRemoval {
    /// `RemoveAttribute` on the sentence (or dropped from a replacing sentence).
    Attribute,
    /// `DeleteSentence`: the sentence is a lemma, a claim as a whole.
    Sentence,
    /// No removal keeps the definition: the mutant is refused (unsupported).
    Refused,
}

/// Every claim k-rust 0068938b1 trusts in a definition it executes, with its removal (the set
/// judged at 501f18b9; the cited passages are byte-identical there but the `total` one, which
/// names more contradictions since KINK-18/2-3, re-pin P-1 of repin-58720d2e, and since UNDEF/1
/// reads a `#Bottom` or refuted-`ensures` successor as an undefined step rather than a vacuous
/// state, re-pin P-1 of repin-0068938b). Not claims:
/// `constructor` (kompile drops a source `constructor` and derives freeness itself,
/// `k-rust/src/kompile/module_to_kore.rs` 1512-1523 and 1539-1545), a value production's
/// `functional` (derived from its equations, `compatibility.md` 1188-1191), `trusted` (on
/// reachability claims, which execution never reads, `compatibility.md` 2313), the `assoc`,
/// `unit` and `idem` axioms of a function (emitted but never used by the backend, which
/// evaluates it by its equations, `compatibility.md` 1566; `comm` is not emitted on a function)
/// and kompile's generated lambdas (KK-71). A rewrite rule's `ensures` is the rule's meaning,
/// and `freshGenerator`, `impure`, `memo` and `no-evaluators` are not consistency axioms.
/// Termination and the SMT prelude stay premises. kink-patch's test `trusted_claims_are_pinned`
/// pins this list against the constants the removal uses and the cited passages' digests.
pub const TRUSTED_CLAIMS: &[TrustedClaim] = &[
    TrustedClaim {
        claim: "total",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md 1171, 1686-1696; backend-port.md 323",
    },
    TrustedClaim {
        claim: "functional",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md 1208, 1688; backend-port.md 323",
    },
    TrustedClaim {
        claim: "injective",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md 1221 (a user-written injective is an axiom)",
    },
    TrustedClaim {
        claim: "smt-hook",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md 2992; backend-port.md 316; k-rust-backend/src/smt.rs 230",
    },
    TrustedClaim {
        claim: "smtlib",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md 2991-2993; k-rust-backend/src/smt.rs 230",
    },
    TrustedClaim {
        claim: "preserves-definedness",
        removal: ClaimRemoval::Attribute,
        citation: "backend-port.md 323",
    },
    TrustedClaim {
        claim: "smt-lemma",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md 2992; backend-port.md 316; k-rust-backend/src/smt.rs 230, 1867-1878",
    },
    TrustedClaim {
        claim: "simplification",
        removal: ClaimRemoval::Sentence,
        citation: "compatibility.md 1171, 1427, 1606",
    },
    TrustedClaim {
        claim: "ensures",
        removal: ClaimRemoval::Refused,
        citation: "backend-port.md 342; compatibility.md 1093 (a false ensures makes the application bottom)",
    },
    TrustedClaim {
        claim: "concrete-equation",
        removal: ClaimRemoval::Refused,
        citation: "compatibility.md 1171 (concrete or symbolic equations are theorems of the executable equations)",
    },
    TrustedClaim {
        claim: "hooked-equation",
        removal: ClaimRemoval::Refused,
        citation: "compatibility.md 1173 (a hooked symbol's equations are paired with the builtin it denotes)",
    },
];

/// Production attributes that assert a property of the symbol's equations: the
/// [`ClaimRemoval::Attribute`] rows of [`TRUSTED_CLAIMS`] on a production.
pub const SYMBOL_CLAIMS: [AttributeKey; 5] = [
    AttributeKey::Total,
    AttributeKey::Functional,
    AttributeKey::Injective,
    AttributeKey::SmtHook,
    AttributeKey::Smtlib,
];

/// Rule attributes that assert a property of the rule, withdrawn by removing the attribute: the
/// [`ClaimRemoval::Attribute`] rows of [`TRUSTED_CLAIMS`] on a rule.
pub const RULE_CLAIMS: [AttributeKey; 2] =
    [AttributeKey::PreservesDefinedness, AttributeKey::SmtLemma];

/// The rule attribute that makes the rule a lemma about other rules rather than a definition: the
/// [`ClaimRemoval::Sentence`] row of [`TRUSTED_CLAIMS`].
pub const LEMMA: AttributeKey = AttributeKey::Simplification;

/// Attributes that restrict when an equation is used, not what it states: k-rust trusts such an
/// equation to be a theorem of the executable equations (the `concrete-equation` row of
/// [`TRUSTED_CLAIMS`]).
pub const CONCRETENESS: [AttributeKey; 2] = [AttributeKey::Concrete, AttributeKey::Symbolic];

/// The claim key of an equation's non-trivial `ensures` (the `ensures` row of
/// [`TRUSTED_CLAIMS`]).
pub const ENSURES_CLAIM: &str = "ensures";

/// The claim key of a hooked symbol's equation, trusted to agree with its hook (the
/// `hooked-equation` row of [`TRUSTED_CLAIMS`]).
pub const HOOKED_EQUATION_CLAIM: &str = "hooked-equation";

/// The key under which a mutant records a sentence its patch touches that k-rust compiles to an
/// equation of a symbol the source reading does not redefine (re-pin R0c-fix-4; the value names
/// the compiled head). The claims resting on that symbol cannot be told from the source, so the
/// patch's effect is unknown and the mutant is refused as unsupported. It is kink's own refusal
/// key, not a claim k-rust trusts, and not a row of [`TRUSTED_CLAIMS`].
pub const UNREAD_EQUATION_CLAIM: &str = "unread-equation";

/// One trusted claim of a mutant: an attribute or a non-trivial equation `ensures`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Claim {
    /// The mutant sentence's origin: a baseline sentence or the patch's inserting edit.
    pub origin: SentenceOrigin,
    pub key: String,
    pub value: Value,
}

/// The claims a patch leaves unbacked: those removed from the mutant, those no removal can take
/// away, and the patch that builds the claim-free mutant.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Withdrawal {
    /// Claims whose support the patch touched, removed from the withdrawn definition: an
    /// attribute removed, or a lemma (key `simplification`) deleted.
    pub withdrawn: Vec<Claim>,
    /// Claims the patch itself writes, lemmas it edits or inserts, and an equation's `ensures`,
    /// `concrete` or `symbolic` restriction or hook agreement whose support it touched. No
    /// definition with only supported claims exists for such a mutant: it is refused.
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

/// The source reading of a patch's effect on the equational part ([`ClaimSupport::effect`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SourceEffect {
    /// The symbols the patch redefines (E, K labels), or `None` when its effect on the
    /// equational part is not known symbol by symbol.
    pub redefined: Option<BTreeSet<String>>,
    /// The redefined symbols and every symbol whose equations reach one, or `None` with
    /// `redefined`: the symbols whose claims [`ClaimSupport::withdraw`] removes.
    pub affected: Option<BTreeSet<String>>,
    /// The baseline sentences the patch replaces, deletes, or edits a term or attribute of.
    pub touched: BTreeSet<SentenceRef>,
}

/// How a rule sentence takes part in the equational theory.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Role {
    /// An equation of the symbol: a function, `anywhere` or macro rule headed by it (an
    /// `smt-lemma` that is not a `simplification` included: k-rust loads it as an equation).
    Equation(String),
    /// A lemma (`simplification`): a claim, never a definition.
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
    /// Labels whose production carries a `hook`: their equations are trusted to agree with it.
    hooked: BTreeSet<String>,
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
        for (mentioned, head) in generated_links(definition) {
            dependents.entry(mentioned).or_default().insert(head);
        }
        Self {
            defined,
            hooked: hooked_labels(definition),
            dependents,
        }
    }

    /// The claims `patch`'s edit leaves unbacked: those removed from the mutant
    /// ([`Withdrawal::withdrawn`]) with the patch that builds the claim-free mutant, and those no
    /// removal can take away ([`Withdrawal::unsupported`], which refuse the mutant). The one
    /// function by which kink builds a mutant (see the module documentation).
    ///
    /// # Errors
    ///
    /// Returns the failure of applying `patch` to `baseline`.
    pub fn withdraw(&self, baseline: &Baseline, patch: &Patch) -> Result<Withdrawal, PatchFailure> {
        let mutant = apply(baseline, patch)?;
        let edits = patch.edits();
        let touched = touched_sentences(edits);
        let redefined = self.redefined(baseline, &mutant, edits, &touched);
        let affected = redefined.map(|redefined| self.closure(redefined));
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
                    let label_affected = label
                        .as_ref()
                        .is_none_or(|label| is_affected(&BTreeSet::from([label.name.clone()])));
                    for key in SYMBOL_CLAIMS {
                        let Some(claim) = claim(key) else { continue };
                        if writes(key) {
                            withdrawal.unsupported.push(claim);
                        } else if label_affected {
                            removals.push(removal(baseline_at, &claim));
                            withdrawal.withdrawn.push(claim);
                        }
                    }
                    // A production's `concrete` or `symbolic` restricts every equation of it.
                    if label_affected {
                        withdrawal
                            .unsupported
                            .extend(CONCRETENESS.into_iter().filter_map(claim));
                    }
                }
                Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Context { .. }
                | Sentence::ContextAlias { .. } => {
                    let replaced = baseline_at.and_then(|at| replacing_edit(edits, at));
                    let edited = baseline_at.is_none_or(|at| touched.contains(at));
                    let unsupported = edited || is_affected(&mentions(sentence));
                    let equation = match (sentence, role(sentence, &self.defined)) {
                        (Sentence::Rule { .. }, Role::Equation(head)) => Some(head),
                        _ => None,
                    };
                    if let (Some(head), Sentence::Rule { ensures, .. }) = (&equation, sentence)
                        && unsupported
                    {
                        if !trivial_ensures(ensures) {
                            withdrawal.unsupported.push(Claim {
                                origin: origin.clone(),
                                key: ENSURES_CLAIM.to_owned(),
                                value: Value::String(ensures.to_string()),
                            });
                        }
                        withdrawal
                            .unsupported
                            .extend(CONCRETENESS.into_iter().filter_map(claim));
                        if self.hooked.contains(head) {
                            withdrawal.unsupported.push(Claim {
                                origin: origin.clone(),
                                key: HOOKED_EQUATION_CLAIM.to_owned(),
                                value: Value::String(head.clone()),
                            });
                        }
                    }
                    if let Some(lemma) = claim(LEMMA)
                        && matches!(sentence, Sentence::Rule { .. })
                    {
                        // A lemma is a claim as a whole: one the patch writes stays the patch's
                        // own and refuses the mutant; one resting on a redefined symbol goes.
                        if edited {
                            withdrawal.unsupported.push(lemma);
                        } else if unsupported {
                            removals.push(Edit::DeleteSentence {
                                at: baseline_at.expect("an unedited baseline lemma").clone(),
                            });
                            withdrawal.withdrawn.push(lemma);
                        }
                        continue;
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
            withdrawal.patch = Some(
                Patch::new(edits)
                    .expect("a nonempty patch")
                    .pinned(baseline)?,
            );
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

    /// The symbols whose equations `patch` can change the meaning of: the symbols it redefines
    /// and every symbol whose equations reach one, the set whose claims [`Self::withdraw`]
    /// removes. `None` when the patch's effect on the equational part is not known symbol by
    /// symbol, so every symbol counts. kink-native's mutant consistency check reads the pairs
    /// of these symbols' equations (re-pin R0c-fix-3).
    ///
    /// # Errors
    ///
    /// Returns the failure of applying `patch` to `baseline`.
    pub fn affected(
        &self,
        baseline: &Baseline,
        patch: &Patch,
    ) -> Result<Option<BTreeSet<String>>, PatchFailure> {
        Ok(self.effect(baseline, patch)?.affected)
    }

    /// The source reading of `patch`'s effect on the equational part: the symbols it redefines,
    /// those it can change the meaning of ([`Self::affected`]) and the baseline sentences it
    /// touches. kink-native reads the compiled definitions against it (re-pin R0c-fix-4): the
    /// compiled equations a touched sentence gives must be headed by a redefined symbol, and the
    /// symbols whose compiled equations differ join the checked set.
    ///
    /// # Errors
    ///
    /// Returns the failure of applying `patch` to `baseline`.
    pub fn effect(&self, baseline: &Baseline, patch: &Patch) -> Result<SourceEffect, PatchFailure> {
        let mutant = apply(baseline, patch)?;
        let edits = patch.edits();
        let touched = touched_sentences(edits);
        let redefined = self.redefined(baseline, &mutant, edits, &touched);
        Ok(SourceEffect {
            affected: redefined.clone().map(|redefined| self.closure(redefined)),
            redefined,
            touched: touched.into_iter().cloned().collect(),
        })
    }

    /// Every symbol whose equations reach a redefined symbol, the redefined ones included.
    fn closure(&self, redefined: BTreeSet<String>) -> BTreeSet<String> {
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

/// The links of the axioms kompile generates rather than the author writes, as (mentioned symbol,
/// symbol whose axiom mentions it) pairs (re-pin R0c-fix-3, R0c-fix-2 review major 2). k-rust
/// 501f18b9 `k-rust/src/kompile/module_to_kore/axioms.rs` `generated_axioms` emits subsort
/// (injection) axioms, which link sorts, not symbols; per-symbol functional, no-confusion and
/// no-junk axioms; the algebraic axioms of a production, whose `unit(u)` axiom mentions the unit
/// symbol `u`; and an overload axiom `g(inj(x1), ..., inj(xn)) = inj(l(x1, ..., xn))` for every
/// lesser `l` and greater `g` of one `overload(key)` family (`compatibility.md` 196, 943, 966),
/// which is an equation of `g` that mentions `l`. Each member of a family is linked to every
/// other, both ways: the family counts as one symbol for the reach, which covers the
/// lesser-to-greater axioms whatever the sort order, and is fail-closed beyond it.
fn generated_links(definition: &Definition) -> Vec<(String, String)> {
    let mut families = BTreeMap::<String, BTreeSet<String>>::new();
    let mut links = Vec::new();
    for (_, sentence) in sentences(definition) {
        let Sentence::Production {
            label: Some(label),
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if let Some(key) = attributes.string(AttributeKey::Overload) {
            families
                .entry(key.to_owned())
                .or_default()
                .insert(label.name.clone());
        }
        if let Some(unit) = attributes.string(AttributeKey::Unit) {
            links.push((unit.to_owned(), label.name.clone()));
        }
    }
    for members in families.values() {
        for mentioned in members {
            for head in members {
                if mentioned != head {
                    links.push((mentioned.clone(), head.clone()));
                }
            }
        }
    }
    links
}

fn hooked_labels(definition: &Definition) -> BTreeSet<String> {
    sentences(definition)
        .filter_map(|(_, sentence)| match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has(AttributeKey::Hook) => Some(label.name.clone()),
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
    if attributes.has(LEMMA) {
        return Role::Lemma;
    }
    let left = matched_term(body);
    let equational =
        attributes.has(AttributeKey::Anywhere) || attributes.has_any(&AttributeKey::MACRO_LIKE);
    match head(left) {
        Some(head) if equational || defined.contains(head) => Role::Equation(head.to_owned()),
        Some(_) => Role::Rewrite,
        None if equational => Role::Unknown,
        None => Role::Rewrite,
    }
}

/// The term whose head heads a rule body: the left-hand side of the body's rewrite, and under
/// `#withConfig` (a function rule written with configuration context, `rule [[ F ]] C`, which
/// k-rust compiles to an equation of `F`'s head) its first argument, or that argument's
/// left-hand side when it is a rewrite. This is k-rust 501f18b9's one reading of the symbol that
/// heads a rule (`k_rust::definition::rule_catalog::match_rule_label`, "under `#withConfig`, the
/// head of its first argument"), through annotations and as-patterns (re-pin R0c-fix-4, R0c-fix-3
/// review critical 2).
fn matched_term(body: &Term) -> &Term {
    match unaliased(body) {
        Term::Apply { label, arguments } if label.is(InternalLabel::WithConfig) => {
            arguments.first().map_or(body, rewrite_left)
        }
        _ => rewrite_left(body),
    }
}

/// The left-hand side of `term` when it is a rewrite, else `term`.
fn rewrite_left(term: &Term) -> &Term {
    match unaliased(term) {
        Term::Rewrite { left, .. } => left,
        _ => term,
    }
}

/// `term` without its annotations and the as-patterns around it.
fn unaliased(term: &Term) -> &Term {
    let mut term = term.unannotated();
    while let Term::As { pattern, .. } = term {
        term = pattern.unannotated();
    }
    term
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
