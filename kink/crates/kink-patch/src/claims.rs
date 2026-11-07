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
use crate::{Baseline, Edit, POSITION_KEYS, Patch, SentenceRef};
use k_rust::definition::{AttributeKey, Definition, PartialOrder, Sentence, compute_subsorts};
use k_rust::kast::{InternalLabel, Label, Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::names::BuiltinSort;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

/// The version of the claim-removal algorithm ([`ClaimSupport::withdraw`]): a mutant's identity
/// depends on it, so kink's semantics identity names it (kink-campaign `identity`), on which every
/// store keys. v2
/// (re-pin R0c-fix-3): the reach follows kompile's generated overload and unit axioms. v3 (re-pin
/// R0c-fix-4): a rule written with configuration context (`[[ F ]] C`) is read as an equation of
/// `F`'s head.
pub const CLAIM_REMOVAL_VERSION: &str = "kink-patch/claim-removal/v3";

/// The version of the weakening test ([`ClaimSupport::weakening`]): whether a mutation is
/// `unkillable` is a verdict this algorithm decides, so kink's semantics identity names it
/// (kink-campaign `identity`), on which every store keys. v1: kink27 R5-WEAKENING. v2 (its fix
/// round 1): a label is a conjunction only when it denotes conjunction in every model (a
/// `function` hooked `BOOL.and` or `BOOL.andThen`, not macro-like, heading no rule outside the
/// builtin catalog), so a macro production hooked `BOOL.and` no longer makes an edit a narrowing.
/// v3: a replacement by an instance of the sentence (a narrower pattern or `requires`,
/// [`ClaimSupport::weakening`]) is a narrowing, and a lemma may be narrowed.
pub const WEAKENING_VERSION: &str = "kink-patch/weakening/v3";

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
/// `k-rust/src/kompile/module_to_kore.rs` `symbol_attributes`), a value production's
/// `functional` (derived from its equations, `compatibility.md` "Anywhere rules"), `trusted` (on
/// reachability claims, which execution never reads, `compatibility.md` "Undefined instances of
/// the initial configuration"), the `assoc`, `unit` and `idem` axioms of a function (emitted but
/// never used by the backend, which evaluates it by its equations, `compatibility.md` "User
/// productions with `assoc`, `comm`, `idem` or `unit`"; `comm` is not emitted on a function)
/// and kompile's generated lambdas (KK-71). A rewrite rule's `ensures` is the rule's meaning,
/// and `freshGenerator`, `impure`, `memo` and `no-evaluators` are not consistency axioms.
/// Termination and the SMT prelude stay premises.
/// The `smt-hook`, `smtlib` and `smt-lemma` rows trust the definition's SMT reading: each
/// `smt-hook` is exact where its symbol is defined, and each `smt-lemma` axiom holds of the
/// definition. Since k-rust's GAP K15 that trust is all a solver answer needs: the solver states
/// each atom with its operands' definedness, so a solver `Unsat`, `Valid` or `Refuted` is a K
/// answer whatever form the predicates have (`compatibility.md` "Solver decisions over partial
/// operations"); before K15 an `Unsat` refuted only predicates whose partial terms had their
/// definedness explicit in them. The definedness-explicit predicates k-rust returns (leaf
/// constraints, residuals, kprove leaves) support refutation under any reading of the
/// `smt-hook`s that is exact where their symbols are defined, and validity, or dropping a
/// conjunct as valid, only under a reading that states each atom with its operands'
/// definedness, as k-rust's solver does (GAP K26, the same section); kink asks every solver
/// question of k-rust's solver (`SmtSolver::is_sat`). kink-patch's test
/// `trusted_claims_are_pinned` pins this list against the constants the removal uses and the
/// cited passages' digests.
/// Citations name a file and the heading (or item) that holds the passage, which is how the test
/// locates each pinned passage (kink27 R2-PIN-BY-ANCHOR).
pub const TRUSTED_CLAIMS: &[TrustedClaim] = &[
    TrustedClaim {
        claim: "total",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md \"Anywhere rules\", \"A contradicted `total` attribute is named, not repaired\"; backend-port.md \"Final search depth cuts\"",
    },
    TrustedClaim {
        claim: "functional",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md \"Anywhere rules\", \"A contradicted `total` attribute is named, not repaired\"; backend-port.md \"Final search depth cuts\"",
    },
    TrustedClaim {
        claim: "injective",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md \"Anywhere rules\" (a user-written injective is an axiom)",
    },
    TrustedClaim {
        claim: "smt-hook",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md \"Solver decisions over partial operations\"; backend-port.md \"Final search depth cuts\"; k-rust-backend/src/smt.rs Exactness",
    },
    TrustedClaim {
        claim: "smtlib",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md \"Solver decisions over partial operations\"; k-rust-backend/src/smt.rs Exactness",
    },
    TrustedClaim {
        claim: "preserves-definedness",
        removal: ClaimRemoval::Attribute,
        citation: "backend-port.md \"Final search depth cuts\"",
    },
    TrustedClaim {
        claim: "smt-lemma",
        removal: ClaimRemoval::Attribute,
        citation: "compatibility.md \"Solver decisions over partial operations\"; backend-port.md \"Final search depth cuts\"; k-rust-backend/src/smt.rs Exactness, smt_lemmas",
    },
    TrustedClaim {
        claim: "simplification",
        removal: ClaimRemoval::Sentence,
        citation: "compatibility.md \"Anywhere rules\", \"Function applications on a left-hand side\", \"User productions with `assoc`, `comm`, `idem` or `unit`\"",
    },
    TrustedClaim {
        claim: "ensures",
        removal: ClaimRemoval::Refused,
        citation: "backend-port.md \"Final search depth cuts\"; compatibility.md \"Anywhere rules\" (a false ensures makes the application bottom)",
    },
    TrustedClaim {
        claim: "concrete-equation",
        removal: ClaimRemoval::Refused,
        citation: "compatibility.md \"Anywhere rules\" (concrete or symbolic equations are theorems of the executable equations)",
    },
    TrustedClaim {
        claim: "hooked-equation",
        removal: ClaimRemoval::Refused,
        citation: "compatibility.md \"Anywhere rules\" (a hooked symbol's equations are paired with the builtin it denotes)",
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

/// A patch that only weakens the baseline's theory ([`ClaimSupport::weakening`]): every model of
/// the baseline is a model of the mutant, so no execution can tell them apart.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Weakening {
    /// The edited sentences, in the patch's edit order.
    pub equations: Vec<WeakenedSentence>,
}

/// One baseline sentence a weakening patch deletes or narrows.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WeakenedSentence {
    pub at: SentenceRef,
    /// The K label of the function the equation defines; `None` for a `simplification` lemma.
    pub head: Option<String>,
    pub kind: WeakeningKind,
}

/// How a weakening patch edits one sentence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WeakeningKind {
    /// The equation or lemma is deleted.
    Deleted,
    /// The equation or lemma is replaced by an instance of itself: a narrower pattern or
    /// `requires`, with the same value on every instance it still covers.
    Narrowed,
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
    /// Labels of productions with `function` and no macro-like attribute: the heads whose
    /// equations [`Self::weakening`] may find deleted or narrowed.
    functions: BTreeSet<String>,
    /// Labels of productions with an `overload` attribute: kompile's overload axiom ties a
    /// family's equations together, so [`Self::weakening`] leaves them to execution.
    overloaded: BTreeSet<String>,
    /// Labels that denote conjunction in every model: the conjunctions [`Self::weakening`]
    /// flattens a `requires` through ([`conjunction_labels`]).
    conjunctions: BTreeSet<String>,
    /// What the instance test reads of the baseline's main module ([`Self::instance`]).
    instances: InstanceFacts,
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
        let labels_where = |keep: &dyn Fn(&k_rust::definition::Attributes) -> bool| {
            sentences(definition)
                .filter_map(|(_, sentence)| match sentence {
                    Sentence::Production {
                        label: Some(label),
                        attributes,
                        ..
                    } if keep(attributes) => Some(label.name.clone()),
                    _ => None,
                })
                .collect::<BTreeSet<_>>()
        };
        Self {
            functions: labels_where(&|attributes| {
                attributes.has(AttributeKey::Function)
                    && !attributes.has_any(&AttributeKey::MACRO_LIKE)
            }),
            overloaded: labels_where(&|attributes| attributes.has(AttributeKey::Overload)),
            conjunctions: conjunction_labels(definition, &defined),
            instances: InstanceFacts::new(definition),
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

    /// Whether `patch` only weakens the baseline's theory, and how: `Some` when every edit deletes
    /// an equation of a `function` head or a `simplification` lemma, or replaces one by an
    /// instance of itself (a `requires` that implies the original's, [`Self::narrows`], or a
    /// narrower pattern, [`Self::instance`]), and no equation of an edited head that the patch
    /// keeps ranks after an edited equation of it. `None` for every other patch.
    ///
    /// An equation `l => r requires c ensures e` of a head `f` at rank p (`priority(N)` gives N,
    /// `owise` [`k_rust::names::OWISE_RULE_PRIORITY`], else
    /// [`k_rust::names::DEFAULT_RULE_PRIORITY`]) is the axiom: for every valuation of its
    /// variables, if no equation of `f` of a smaller rank applies to `l` and `c` is true, then
    /// `l = r` and `e`. Universal instantiation by a substitution σ whose terms each denote one
    /// element of their variable's sort gives the same axiom over `σl`, `σc`, `σr` and `σe`, and a
    /// `requires` with every conjunct of `σc` among its conjuncts implies `σc`; the instance keeps
    /// the attributes, so its rank and the equations ranked before it are the original's. So a
    /// narrowed axiom holds in every model of the baseline. A deleted axiom is gone; every other
    /// axiom is literally the baseline's, since what could change for it is only the set of
    /// equations of its head ranked before it, and the rank condition keeps that set. A lemma
    /// is a claim, and deleting it or replacing it by an instance claims less. So every axiom and
    /// claim of the mutant is one of the baseline's or entailed by one, and every model of the
    /// baseline is a model of the mutant: no program can kill it.
    ///
    /// Fail closed: a rule with `anywhere` or a macro-like attribute (deleting the last
    /// `anywhere` rule of a symbol makes it a constructor, whose no-confusion the baseline need
    /// not satisfy; a macro rule is expanded into other sentences), a head of an `overload`
    /// family (kompile's overload axiom ties the family's equations), a replacement that is no
    /// instance the syntactic tests find, and any edit of a rewrite rule (a configuration no rule
    /// rewrites is an end, so a narrowed rule changes the ends of a run in every model), a
    /// production or anything else.
    #[must_use]
    pub fn weakening(&self, baseline: &Baseline, patch: &Patch) -> Option<Weakening> {
        let mut equations = Vec::new();
        for edit in patch.edits() {
            let (at, replacement) = match edit {
                Edit::DeleteSentence { at } => (at, None),
                Edit::ReplaceSentence { at, replacement } => (at, Some(replacement)),
                _ => return None,
            };
            let sentence = baseline.sentence(at)?;
            let head = self.weakenable(sentence)?;
            let kind = match replacement {
                None => WeakeningKind::Deleted,
                Some(replacement)
                    if self.narrows(sentence, replacement)
                        || self.instance(sentence, replacement) =>
                {
                    WeakeningKind::Narrowed
                }
                Some(_) => return None,
            };
            equations.push(WeakenedSentence {
                at: at.clone(),
                head,
                kind,
            });
        }
        if equations.is_empty() {
            return None;
        }
        // The rank condition: for each edited head, no kept equation of it ranks after the
        // smallest rank among its edited equations. A narrowed equation keeps its attributes, so
        // the baseline's ranks are the mutant's.
        let mut smallest = BTreeMap::<&str, u8>::new();
        for weakened in &equations {
            if let Some(head) = &weakened.head {
                let rank = rule_rank(baseline.sentence(&weakened.at)?)?;
                let entry = smallest.entry(head.as_str()).or_insert(rank);
                *entry = (*entry).min(rank);
            }
        }
        let deleted = equations
            .iter()
            .filter(|weakened| weakened.kind == WeakeningKind::Deleted)
            .map(|weakened| &weakened.at)
            .collect::<BTreeSet<_>>();
        for (at, sentence) in sentences(baseline.definition()) {
            let Role::Equation(head) = role(sentence, &self.defined) else {
                continue;
            };
            let Some(&edited) = smallest.get(head.as_str()) else {
                continue;
            };
            if !deleted.contains(&at) && rule_rank(sentence)? > edited {
                return None;
            }
        }
        Some(Weakening { equations })
    }

    /// The labels of the functions some of whose baseline equations `patch` edits: the heads of
    /// the equations it deletes, replaces, or edits a term or attribute of (kink27 R5-WEAKENING
    /// fix round 1). An application of one of them that a mutant's state holds unreduced is one
    /// whose value the edit can have left open; any other application is unreduced in the
    /// baseline as well, or open for a reason the edit does not name. A lemma or an `anywhere`
    /// or macro rule whose head cannot be read names no head.
    #[must_use]
    pub fn edited_equation_heads(&self, baseline: &Baseline, patch: &Patch) -> BTreeSet<String> {
        touched_sentences(patch.edits())
            .into_iter()
            .filter_map(|at| match role(baseline.sentence(at)?, &self.defined) {
                Role::Equation(head) => Some(head),
                Role::Lemma | Role::Rewrite | Role::Unknown => None,
            })
            .collect()
    }

    /// The head of a rule whose deletion can weaken the theory: `Some(None)` for a
    /// `simplification` lemma, `Some(Some(f))` for an equation of a `function` head `f` outside
    /// every `overload` family with no `anywhere` or macro-like attribute, `None` otherwise.
    fn weakenable(&self, sentence: &Sentence) -> Option<Option<String>> {
        let Sentence::Rule { attributes, .. } = sentence else {
            return None;
        };
        if attributes.has(AttributeKey::Anywhere) || attributes.has_any(&AttributeKey::MACRO_LIKE) {
            return None;
        }
        match role(sentence, &self.defined) {
            Role::Lemma => Some(None),
            Role::Equation(head)
                if self.functions.contains(&head) && !self.overloaded.contains(&head) =>
            {
                Some(Some(head))
            }
            _ => None,
        }
    }

    /// Whether `replacement` is the rule `original` with a `requires` that implies the
    /// original's, decided syntactically: the same body and `ensures` (term equality ignores
    /// annotations), the same attributes without the position keys, and every conjunct of the
    /// original `requires` a conjunct of the replacement's ([`Self::conjuncts`]). Sound because
    /// a conjunction (`andBool`, `andThenBool`, or another label that denotes conjunction in
    /// every model, [`conjunction_labels`]) is `true` only when both operands are `true`; it
    /// misses a narrowing that rewrites a guard (`W -Int 1` to `W -Int 2`).
    fn narrows(&self, original: &Sentence, replacement: &Sentence) -> bool {
        let (
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            },
            Sentence::Rule {
                body: new_body,
                requires: new_requires,
                ensures: new_ensures,
                attributes: new_attributes,
            },
        ) = (original, replacement)
        else {
            return false;
        };
        if body != new_body
            || ensures != new_ensures
            || positionless(attributes) != positionless(new_attributes)
        {
            return false;
        }
        let narrower = self.conjuncts(new_requires);
        self.conjuncts(requires)
            .iter()
            .all(|conjunct| narrower.contains(conjunct))
    }

    /// Whether `replacement` is an instance of the rule `original` under a substitution σ,
    /// decided syntactically: the one-way match of `original`'s body against
    /// `replacement`'s with `replacement`'s variables held fixed gives σ (unique when it exists),
    /// σ of the original's `ensures` is the replacement's, every conjunct of σ of the original's
    /// `requires` is a conjunct of the replacement's ([`Self::conjuncts`]), and the attributes
    /// are equal without the position keys. A sorted variable `x:S` (a semantic cast of a
    /// variable, written or inserted by sort inference) is one variable occurrence, matched as a
    /// whole; each later occurrence of `x` must meet the same term, variables compared by name.
    /// An anonymous variable (`_`, `?_`, `!_`, `@_`) binds nothing and meets only an equal term,
    /// its cast and sort included, and every variable of the original's `requires` and `ensures`
    /// must be bound by its body.
    ///
    /// σ maps a variable to itself (same name, sort and written sort), or a variable written with
    /// its sort, `x:S` at some occurrence ([`written_sorts`]), to a constructor term whose root
    /// sort is S or a subsort of it ([`InstanceFacts::constructor_sort`]): built from tokens,
    /// variables and labels whose one production is a constructor, it denotes one element of S
    /// under every valuation, so the instance holds in every model of the original. Fail closed
    /// when σ moves a variable and either sentence holds a construct compilation expands or
    /// resolves by the shape of the terms below it ([`InstanceFacts::expands`]), or the rule
    /// carries `concrete` or `symbolic`, which name the variables σ may replace: the instance of
    /// the text need not be the instance of the axiom it compiles to. A variable written without
    /// its sort, or with a cast over another sort of its own, bound to anything but itself fails
    /// closed too, as does a wildcard against anything but itself: its sort in the baseline's
    /// axiom is not read here. The test is iterative, as sentences can be deep.
    fn instance(&self, original: &Sentence, replacement: &Sentence) -> bool {
        let (
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            },
            Sentence::Rule {
                body: new_body,
                requires: new_requires,
                ensures: new_ensures,
                attributes: new_attributes,
            },
        ) = (original, replacement)
        else {
            return false;
        };
        if positionless(attributes) != positionless(new_attributes) {
            return false;
        }
        let (Some(sorts), Some(new_sorts)) = (written_sorts(original), written_sorts(replacement))
        else {
            return false;
        };
        let mut sigma = BTreeMap::new();
        if !match_terms(body, new_body, &mut sigma, true)
            || !match_terms(ensures, new_ensures, &mut sigma, false)
        {
            return false;
        }
        let narrower = self.conjuncts(new_requires);
        let entailed = self.conjuncts(requires).into_iter().all(|conjunct| {
            narrower
                .iter()
                .any(|candidate| match_terms(conjunct, candidate, &mut sigma, false))
        });
        if !entailed {
            return false;
        }
        let mut moved = false;
        for (name, term) in &sigma {
            if occurrence(term).is_some_and(|found| {
                found.name == *name
                    && new_sorts.sort(name) == sorts.sort(name)
                    && new_sorts.written(name) == sorts.written(name)
            }) {
                continue;
            }
            moved = true;
            let (Some(sort), Some(root)) = (
                sorts.written(name),
                self.instances.constructor_sort(term, &new_sorts),
            ) else {
                return false;
            };
            if !self.instances.at_most(&root, sort) {
                return false;
            }
        }
        !moved
            || !(attributes.has(AttributeKey::Concrete)
                || attributes.has(AttributeKey::Symbolic)
                || self.instances.expands(original)
                || self.instances.expands(replacement))
    }

    /// The conjuncts of a `requires`: through annotations, each application of a conjunction
    /// label with two operands is replaced by its operands, and the token `true` (the
    /// `requires` of a rule written without one, and the unit of a conjunction) is dropped.
    fn conjuncts<'a>(&self, requires: &'a Term) -> Vec<&'a Term> {
        let mut conjuncts = Vec::new();
        let mut pending = vec![requires];
        while let Some(term) = pending.pop() {
            match term.unannotated() {
                Term::Apply { label, arguments }
                    if arguments.len() == 2 && self.conjunctions.contains(&label.name) =>
                {
                    pending.extend(arguments.iter().rev());
                }
                Term::Token { token, sort } if token == "true" && sort.name == "Bool" => {}
                _ => conjuncts.push(term),
            }
        }
        conjuncts
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

/// `attributes` without the position keys.
fn positionless(attributes: &k_rust::definition::Attributes) -> k_rust::definition::Attributes {
    let mut attributes = attributes.clone();
    for key in POSITION_KEYS {
        attributes.remove(key.as_str());
    }
    attributes
}

/// What the instance test ([`ClaimSupport::instance`]) reads of a baseline, from the sentences of
/// its main module and the modules it imports, transitively.
#[derive(Clone, Debug)]
struct InstanceFacts {
    /// Every label with a production, and the result sort of that production when the label has
    /// exactly one and it is a constructor: no sort parameter, no `function`, macro-like, `hook`
    /// or `binder` attribute, not a cast, and no `anywhere` rule headed by the label (an
    /// `anywhere` rule is an equation of its head). Each such label is a total symbol that no
    /// equation reduces, so an application of it to terms that each denote one element denotes
    /// one element.
    labels: BTreeMap<String, Option<Sort>>,
    /// Labels with a macro-like or `binder` production: compilation expands an application of
    /// one, or binds its variables, by the terms below it.
    expanded: BTreeSet<String>,
    /// The subsort order the text declares (k-rust's `compute_subsorts` over the main module's
    /// sentences), or `None` when it has a cycle: then only equal sorts are related.
    subsorts: Option<PartialOrder<Sort>>,
}

impl InstanceFacts {
    fn new(definition: &Definition) -> Self {
        let sentences = main_module_sentences(definition);
        let mut anywhere_heads = BTreeSet::new();
        let mut unread_anywhere = false;
        for sentence in &sentences {
            if let Sentence::Rule {
                body, attributes, ..
            } = sentence
                && attributes.has(AttributeKey::Anywhere)
            {
                match head(matched_term(body)) {
                    Some(head) => {
                        anywhere_heads.insert(head.to_owned());
                    }
                    None => unread_anywhere = true,
                }
            }
        }
        let mut labels = BTreeMap::<String, Option<Sort>>::new();
        let mut expanded = BTreeSet::new();
        for sentence in &sentences {
            let Sentence::Production {
                label: Some(label),
                parameters,
                sort,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            let expanding = attributes.has_any(&AttributeKey::MACRO_LIKE)
                || attributes.has(AttributeKey::Binder);
            if expanding {
                expanded.insert(label.name.clone());
            }
            let constructor = !unread_anywhere
                && !expanding
                && parameters.is_empty()
                && label.parameters.is_empty()
                && !attributes.has(AttributeKey::Function)
                && !attributes.has(AttributeKey::Hook)
                && !excluded_label(label)
                && !anywhere_heads.contains(&label.name);
            labels
                .entry(label.name.clone())
                .and_modify(|entry| *entry = None)
                .or_insert_with(|| constructor.then(|| sort.clone()));
        }
        Self {
            labels,
            expanded,
            subsorts: compute_subsorts(sentences.iter().copied(), false).ok(),
        }
    }

    /// Whether every element of `lesser` is one of `greater`: the sorts are equal, or the text
    /// declares `lesser` below `greater` (K's injections compose, `inj{S,R}(inj{S',S}(t))` being
    /// `inj{S',R}(t)`), or `greater` is `KItem` and compilation declares `lesser` a subsort of it.
    /// Parametric sorts, and every sort under a cyclic order, are related only when equal; no
    /// sort is a subsort of `K`, since a K item is a `K` as a one-element sequence.
    fn at_most(&self, lesser: &Sort, greater: &Sort) -> bool {
        if lesser == greater {
            return true;
        }
        let Some(subsorts) = &self.subsorts else {
            return false;
        };
        if !lesser.parameters.is_empty()
            || !greater.parameters.is_empty()
            || greater.is_builtin(BuiltinSort::K)
        {
            return false;
        }
        if greater.is_builtin(BuiltinSort::KItem) {
            return lesser.has_implicit_kitem_subsort();
        }
        subsorts.less_than(lesser, greater)
    }

    /// The root sort of `term` when it is a constructor term of the replacement whose variables
    /// carry `sorts`: a sorted variable written with its sort, a token, or an application of a
    /// label whose one production is a constructor ([`Self::labels`]), with every subterm a
    /// token, a named variable or such an application. An anonymous variable is refused, since
    /// each of its occurrences is another variable.
    fn constructor_sort(&self, term: &Term, sorts: &WrittenSorts) -> Option<Sort> {
        let root = if let Some(found) = occurrence(term) {
            sorts.written(found.name)?.clone()
        } else {
            match term.unannotated() {
                Term::Token { sort, .. } => sort.clone(),
                Term::Apply { label, .. } => self.labels.get(&label.name)?.clone()?,
                _ => return None,
            }
        };
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            if let Some(found) = occurrence(term) {
                if anonymous(found.name) {
                    return None;
                }
                continue;
            }
            match term.unannotated() {
                Term::Token { .. } => {}
                Term::Apply { label, arguments }
                    if self.labels.get(&label.name).is_some_and(Option::is_some) =>
                {
                    pending.extend(arguments);
                }
                _ => return None,
            }
        }
        Some(root)
    }

    /// Whether `sentence` holds a construct compilation expands or resolves by the shape of the
    /// terms below it, so that the instance of its text need not be the instance of its axiom: a
    /// macro-like or `binder` label, a cast other than a variable's sort, `#withConfig`, `#let`,
    /// `#fun`, a generated label, an injected label, a label without a production, or a `?`,
    /// `!` or `@` variable.
    fn expands(&self, sentence: &Sentence) -> bool {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } = sentence
        else {
            return true;
        };
        let mut pending = vec![body, requires, ensures];
        while let Some(term) = pending.pop() {
            if let Some(found) = occurrence(term) {
                if found.name.starts_with(['?', '!', '@']) {
                    return true;
                }
                continue;
            }
            match term.unannotated() {
                Term::InjectedLabel(_) => return true,
                Term::Apply { label, arguments } => {
                    if excluded_label(label)
                        || self.expanded.contains(&label.name)
                        || !self.labels.contains_key(&label.name)
                    {
                        return true;
                    }
                    pending.extend(arguments);
                }
                Term::Rewrite { left, right } => pending.extend([&**left, &**right]),
                Term::As { pattern, alias } => pending.extend([&**pattern, &**alias]),
                Term::Sequence(items) => pending.extend(items),
                Term::Variable { .. } | Term::Token { .. } | Term::Annotated { .. } => {}
            }
        }
        false
    }
}

/// Whether `label` is one compilation resolves by the terms below it: a semantic or syntactic
/// cast, another generated label (a projection, a `#let` or `#fun` lambda), `#withConfig`,
/// `#let` or `#fun`.
fn excluded_label(label: &Label) -> bool {
    label.generated().is_some()
        || [
            InternalLabel::WithConfig,
            InternalLabel::Let,
            InternalLabel::Fun2,
            InternalLabel::Fun3,
            InternalLabel::OuterCast,
            InternalLabel::SyntacticCast,
            InternalLabel::SyntacticCastBraced,
        ]
        .into_iter()
        .any(|internal| label.is(internal))
}

/// The sentences of `definition`'s main module and of every module it imports, transitively.
fn main_module_sentences(definition: &Definition) -> Vec<&Sentence> {
    let modules = definition
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut seen = BTreeSet::new();
    let mut pending = vec![definition.main_module.as_str()];
    let mut sentences = Vec::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name) {
            continue;
        }
        if let Some(module) = modules.get(name) {
            sentences.extend(module.local_sentences.iter().map(|sentence| &**sentence));
            pending.extend(module.imports.iter().map(|import| import.name.as_str()));
        }
    }
    sentences
}

/// One occurrence of a variable: `x`, or `x` under a semantic cast to `S` (`x:S`).
struct Occurrence<'t> {
    name: &'t str,
    /// The variable's sort at this occurrence: the cast's, unless the variable carries another
    /// one under it (sort inference narrowed it), else the variable's own.
    sort: Option<Sort>,
    /// `S` when the text writes `x:S` here and `S` is the variable's sort: the cast spans more
    /// text than the variable (the casts sort inference inserts span none), and the variable
    /// carries no other sort under it. A variable whose own sort differs from its written cast
    /// has no written sort here (fail closed): the text does not say which of the two its axiom
    /// quantifies over.
    written: Option<Sort>,
}

/// The variable occurrence `term` is, through annotations.
fn occurrence(term: &Term) -> Option<Occurrence<'_>> {
    let mut span = None;
    let mut term = term;
    while let Term::Annotated {
        term: inner,
        metadata,
    } = term
    {
        span = metadata.span.or(span);
        term = inner;
    }
    match term {
        Term::Variable { name, sort } => Some(Occurrence {
            name,
            sort: sort.clone(),
            written: None,
        }),
        Term::Apply { label, arguments } if arguments.len() == 1 => {
            let cast = label.semantic_cast_sort()?;
            let variable = &arguments[0];
            let Term::Variable { name, sort: under } = variable.unannotated() else {
                return None;
            };
            let variable_span = match variable {
                Term::Annotated { metadata, .. } => metadata.span,
                _ => None,
            };
            let spans_more = matches!(
                (span, variable_span),
                (Some(cast_span), Some(variable_span))
                    if cast_span.source == variable_span.source
                        && cast_span.start <= variable_span.start
                        && cast_span.end >= variable_span.end
                        && (cast_span.start, cast_span.end) != (variable_span.start, variable_span.end)
            );
            let written = (spans_more && under.as_ref().is_none_or(|under| *under == cast))
                .then(|| cast.clone());
            Some(Occurrence {
                name,
                written,
                sort: Some(under.clone().unwrap_or(cast)),
            })
        }
        _ => None,
    }
}

/// Whether a variable name is anonymous as written (`_`, `?_`, `!_`, `@_`): each occurrence is
/// another variable. A name such as `_X` is a named variable, each of its occurrences the same
/// one ([`k_rust::kast::binding::is_unresolved_anonymous`]).
fn anonymous(name: &str) -> bool {
    k_rust::kast::binding::is_unresolved_anonymous(name)
}

/// The sort of each named variable of a rule, and the sort its text writes for it.
struct WrittenSorts {
    sorts: BTreeMap<String, Option<Sort>>,
    written: BTreeMap<String, Sort>,
}

impl WrittenSorts {
    fn sort(&self, name: &str) -> Option<&Sort> {
        self.sorts.get(name)?.as_ref()
    }

    fn written(&self, name: &str) -> Option<&Sort> {
        self.written.get(name)
    }
}

/// The sorts of the named variables of the rule `sentence`; `None` when a name carries two
/// sorts, or the sentence is no rule (fail closed).
fn written_sorts(sentence: &Sentence) -> Option<WrittenSorts> {
    let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = sentence
    else {
        return None;
    };
    let mut sorts = WrittenSorts {
        sorts: BTreeMap::new(),
        written: BTreeMap::new(),
    };
    let mut pending = vec![body, requires, ensures];
    while let Some(term) = pending.pop() {
        if let Some(found) = occurrence(term) {
            if anonymous(found.name) {
                continue;
            }
            let known = sorts.sorts.entry(found.name.to_owned()).or_insert(None);
            match (&*known, found.sort) {
                (Some(known), Some(sort)) if *known != sort => return None,
                (None, Some(sort)) => *known = Some(sort),
                _ => {}
            }
            if let Some(written) = found.written {
                sorts.written.insert(found.name.to_owned(), written);
            }
            continue;
        }
        match term.unannotated() {
            Term::Apply { arguments, .. } => pending.extend(arguments),
            Term::Rewrite { left, right } => pending.extend([&**left, &**right]),
            Term::As { pattern, alias } => pending.extend([&**pattern, &**alias]),
            Term::Sequence(items) => pending.extend(items),
            Term::InjectedLabel(_)
            | Term::Variable { .. }
            | Term::Token { .. }
            | Term::Annotated { .. } => {}
        }
    }
    Some(sorts)
}

/// The one-way match of `original` against `replacement`, the replacement's variables held
/// fixed, extending `sigma` (each named variable of the original to the replacement's term at
/// its first occurrence) when `bind`, else only reading it. Annotations are transparent; each
/// later occurrence of a variable must meet the same term ([`same_by_name`]). An anonymous
/// variable binds nothing, so it meets only an equal term (its name, its cast and its sort, by
/// [`Term`]'s equality): `_:Nat` against `_:KItem` or `_` would widen the sentence, not
/// instantiate it.
fn match_terms<'r>(
    original: &Term,
    replacement: &'r Term,
    sigma: &mut BTreeMap<String, &'r Term>,
    bind: bool,
) -> bool {
    let mut pending = vec![(original, replacement)];
    while let Some((original, replacement)) = pending.pop() {
        if let Some(found) = occurrence(original) {
            if anonymous(found.name) {
                if original != replacement {
                    return false;
                }
            } else if let Some(bound) = sigma.get(found.name) {
                if !same_by_name(bound, replacement) {
                    return false;
                }
            } else if bind {
                sigma.insert(found.name.to_owned(), replacement);
            } else {
                return false;
            }
            continue;
        }
        if !same_node(original, replacement, &mut pending) {
            return false;
        }
    }
    true
}

/// Whether two terms of the replacement are the same term, each variable occurrence compared
/// by its name. Two occurrences of an anonymous variable are two variables, never the same.
fn same_by_name(left: &Term, right: &Term) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (occurrence(left), occurrence(right)) {
            (Some(left), Some(right)) if left.name == right.name && !anonymous(left.name) => {
                continue;
            }
            (Some(_), _) | (_, Some(_)) => return false,
            (None, None) => {}
        }
        if !same_node(left, right, &mut pending) {
            return false;
        }
    }
    true
}

/// Whether two terms that are no variable occurrences have the same node, through annotations,
/// pushing their pairs of children onto `pending`.
fn same_node<'o, 'r>(
    left: &'o Term,
    right: &'r Term,
    pending: &mut Vec<(&'o Term, &'r Term)>,
) -> bool {
    match (left.unannotated(), right.unannotated()) {
        (
            Term::Rewrite { left: l, right: r },
            Term::Rewrite {
                left: l2,
                right: r2,
            },
        ) => {
            pending.extend([(&**l, &**l2), (&**r, &**r2)]);
        }
        (
            Term::As { pattern, alias },
            Term::As {
                pattern: pattern2,
                alias: alias2,
            },
        ) => pending.extend([(&**pattern, &**pattern2), (&**alias, &**alias2)]),
        (Term::Sequence(items), Term::Sequence(items2)) if items.len() == items2.len() => {
            pending.extend(items.iter().zip(items2));
        }
        (
            Term::Apply { label, arguments },
            Term::Apply {
                label: label2,
                arguments: arguments2,
            },
        ) if label == label2 && arguments.len() == arguments2.len() => {
            pending.extend(arguments.iter().zip(arguments2));
        }
        (
            Term::Token { token, sort },
            Term::Token {
                token: token2,
                sort: sort2,
            },
        ) => {
            return token == token2 && sort == sort2;
        }
        (Term::InjectedLabel(label), Term::InjectedLabel(label2)) => return label == label2,
        _ => return false,
    }
    true
}

/// The rank of a rule among the equations of its head: its `priority`, else
/// [`k_rust::names::OWISE_RULE_PRIORITY`] for `owise`, else the default rank. `None` for a
/// `priority` the reading does not accept (fail closed).
fn rule_rank(sentence: &Sentence) -> Option<u8> {
    let attributes = sentence.attributes();
    if let Some(priority) = attributes.string(AttributeKey::Priority) {
        k_rust::names::rule_priority(priority)
    } else if attributes.has(AttributeKey::Owise) {
        Some(k_rust::names::OWISE_RULE_PRIORITY)
    } else {
        Some(k_rust::names::DEFAULT_RULE_PRIORITY)
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

/// The labels that denote conjunction in every model of `definition`: each production with the
/// label is a `function` hooked `BOOL.and` or `BOOL.andThen` with no macro-like attribute, and no
/// rule outside the builtin catalog is headed by it.
///
/// The hook alone does not fix what an application denotes. A macro-like production is expanded
/// by its rules into whatever they say before anything runs (`rule A &&& _ => notBool A` makes
/// `c &&& true` mean `notBool c`), and an equation of the label, `macro`, `anywhere` or function
/// rule, is an axiom about it that the hook need not satisfy. Without either, the label's only
/// meaning is the hook's, and `a ∧ b` is true only when both operands are, which is what the
/// conjunct test needs. The builtin catalog's equations of `andBool` and `andThenBool` (`true
/// andBool B => B` and the like) are laws of conjunction, so they leave its meaning the hook's.
/// A weakening's edits only delete rules or replace one by a rule with the same body, so the
/// mutant's rules headed by a label are among the baseline's: reading the baseline decides
/// both. A rule with `anywhere` or a macro-like attribute whose head cannot be read could be
/// headed by any label, so one outside the catalog leaves no label a conjunction (fail closed).
fn conjunction_labels(definition: &Definition, defined: &BTreeSet<String>) -> BTreeSet<String> {
    let builtin_source_prefixes = CompileOptions::default().builtin_source_prefixes;
    let builtin = |sentence: &Sentence| {
        sentence.attributes().source().is_some_and(|source| {
            builtin_source_prefixes
                .iter()
                .any(|prefix| source.starts_with(prefix))
        })
    };
    let mut conjunctions = BTreeSet::new();
    let mut refused = BTreeSet::new();
    for (_, sentence) in sentences(definition) {
        match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } => {
                let conjunction = attributes.has(AttributeKey::Function)
                    && !attributes.has_any(&AttributeKey::MACRO_LIKE)
                    && matches!(
                        attributes.string(AttributeKey::Hook),
                        Some("BOOL.and" | "BOOL.andThen")
                    );
                if conjunction {
                    conjunctions.insert(label.name.clone());
                } else {
                    refused.insert(label.name.clone());
                }
            }
            Sentence::Rule { body, .. } if !builtin(sentence) => match head(matched_term(body)) {
                Some(head) => {
                    refused.insert(head.to_owned());
                }
                None if role(sentence, defined) == Role::Unknown => return BTreeSet::new(),
                None => {}
            },
            _ => {}
        }
    }
    conjunctions.retain(|label| !refused.contains(label));
    conjunctions
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
