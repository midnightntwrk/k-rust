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
//! [`admit_mutant`] decides it with k-rust's own load-time critical-pair check
//! (`k_rust_backend::confluence`, k-rust 501f18b9 `docs/compatibility.md`, "Anywhere rules"),
//! run on the claim-free mutant through
//! `BackendDefinition::value_claims_in_scope(CheckScope::All)`, the scope k-rust documents as "a
//! report of every pair that does not join". The check classifies each root pair (two executable
//! equations of one index and priority group, an `owise` group being its own priority, and an
//! equation with itself when a map or set pattern matches one subject in several ways) and each
//! inner pair (root pairs are formed within one priority group, k-rust 58720d2e5; an overlap over
//! a sort with no normal form is no longer separated, k-rust FZ-EMPTYSORT), as refuted by the two
//! `requires` (simplified
//! with every claim withheld; since KINK-20/3 also by the integer bounds of one-term comparisons
//! with literals), joined by innermost steps valid on every instance, or not joined. Not joined
//! covers every answer short of a proof: the reducts differ, a condition is neither refuted nor
//! decided, the `ensures` differ, the unifier meets a shape it does not decide, a join step is
//! refused, or the join runs out of its budget. The join steps are those of the executable
//! equations and of the witness equations the check adopts (k-rust FZ-EMPTYJOIN-WITNESS: each
//! interprets a stuck partial application at an element of a sort with no normal form, proposed
//! by a first pass and adopted only when a second pass with them loses no pair and joins more). Each of these, for a pair with an equation of a
//! checked head, refuses the mutant, naming the pair; so do k-rust's reports of a checked
//! equation the evaluator never applies as written, and a precondition row that puts an
//! equation outside the check (an equation indexed at a collection or a bare variable, whatever
//! its head; an overload equation of another shape, a family with no least common overload and a
//! pinned injective symbol, of a checked symbol; an equation headed by a constructor or an
//! injection, when that equation is checked or the row names none). A constructor-headed or
//! injection-headed equation that is not checked refuses nothing, and k-rust classifies none of
//! its overlaps, so one below the root of a checked left-hand side is a residual k-rust reading
//! that no K source is known to give (re-pin R0-tail, R0c-fix-4 review minor 3).
//!
//! k-rust's premise, which this check adds to kink's trust list (k-rust `docs/compatibility.md`,
//! "Anywhere rules", since FZ-EMPTYJOIN-WITNESS): the definition's equations "have `M+` as a
//! model when the executable equations and the witness equations the check adopts terminate
//! innermost over the signature with the added constants (A1+), and their critical pairs join,
//! which the backend checks". `M+` is read by the normal forms of innermost evaluation by those
//! equations over the signature with one fresh constant in each sort that does not have an
//! element in every model; it agrees with `M_NF` on every term free of the constants, and its
//! carriers are nonempty. So kink trusts that k-rust's critical-pair checker decides joinability
//! in `M+` correctly, and A1+, which k-rust states as a premise of its own and does not check: it
//! implies that evaluation terminates, but follows neither from that nor from the termination of
//! the executable equations on open terms. A mutant whose check reports nothing for the checked
//! heads (and the baseline's for the rest) has `M+` as a model under A1+; a model is all its
//! admission needs.
//!
//! What an edit changes is a fact about the compiled definitions, which k-rust executes, so it is
//! read there ([`admit_mutant`], re-pin R0c-fix-4): some equations have no source sentence of
//! their own (the `#lambda` equations kompile generates for a `#let` or `#fun`), and some source
//! forms compile to equations of a symbol their written head does not name (a function rule with
//! configuration context, `rule [[ F ]] C`, loaded as `#withConfig(F, C)`). The changed indexes
//! are those of the claim-free mutant's function theory whose equations differ from the
//! baseline's ([`CompiledEquations`]: compared without their unique ids, origins and the claims
//! claim removal handles; an index on one side only counts; the simplification and ceil lemmas
//! are compared alike, and a changed predicate lemma checks every head). The checked heads are every index
//! whose equations reach a changed one over either compiled theory (an equation reaches the
//! symbols it applies in its sides and conditions; an overload family is linked both ways),
//! together with kink-patch's source reading ([`kink_patch::ClaimSupport::affected`]): an
//! unchanged pair of a symbol that reaches a changed one can stop joining, since its reducts and
//! conditions are normalized with the changed equations. A changed or reached index that is not
//! a symbol checks every head.
//!
//! The witness equations are part of what an edit changes (fz26 KINK-WITNESS), and they are read
//! from the full checks the gate reads ([`crate::data::DataFacts::witnesses`]), so the witnesses
//! kink compares are those its verdict was computed with. The mutant's check therefore runs before
//! the reach. An index whose witnesses differ from the baseline's (compared as equations are, the
//! check having renamed their variables canonically) is changed, and a witness reaches the symbols
//! it applies as an equation of its head does: a pair that joined through a baseline witness the
//! mutant lacks, or through one only the mutant has, is checked wherever its equations reach the
//! witness's head. A flip of the pass the check adopts between the baseline and the mutant
//! ([`crate::data::DataFacts::witness_pass_adopted`]) changes the equations every pair was joined
//! with, so it checks every head, and the mutant is refused as inconsistent if any pair is not
//! joined, before kink-campaign compares the findings outside the checked heads. Every other pair is the baseline's and is normalized with the
//! baseline's equations alone, so it joins in the mutant exactly when it does in the baseline.
//! kink checks that rather than arguing it (fz26 KINK-BASELINE-FINDINGS): every finding of the
//! mutant's full check outside the checked heads must be the baseline's, by name and unique ids
//! ([`crate::data::DataFacts::differs_outside`]; kink-campaign refuses a difference as
//! `mutant-findings`), and a baseline with a finding no name assumes leaves no end data
//! ([`crate::data::data_ends`]; every mutation `baseline-findings`).
//!
//! The source reading is kept as a fail-closed cross-check, since claim removal reads it: every
//! compiled equation that a rule the patch touches or inserts gives, on either side, must be
//! headed by a symbol kink-patch reads as redefined, or by a generated lambda (its only trusted
//! claim, `total`, is k-rust's judgement of its body on the claim-free mutant, `resolve_fun`'s
//! `equation_right_is_defined`, which reads only the claims that mutant keeps); and no other
//! generated `total` symbol may have changed equations. Otherwise the claims the edit leaves
//! unbacked are not known ([`MutantFailure::UnreadEquations`]), and kink-campaign refuses the
//! mutant as `unsupported-claims`.
//!
//! Two properties of k-rust's check need care, and each is closed here:
//!
//! - A definition that declares no equation head (an `anywhere` production that is not a
//!   declared function) and no overloaded symbol that can be withdrawn has no pair checked by the
//!   load's own scope (`CheckScope::Gate`'s early return, `compatibility.md`, the paragraph after
//!   "the load classifies only the pairs that can change a claim"). That is most definitions kink
//!   mutates. `CheckScope::All` has no such return (k-rust-backend `confluence.rs`: the shortcut is
//!   taken under `Gate` only), so the check reads the mutant's full check, which kink computes
//!   once per load on the backend the mutant runs on (`Backend::from_definition`'s selected
//!   definition; [`crate::data::DataFacts`], fz26 KINK-BASELINE-FINDINGS): before that ticket it
//!   checked a source-route copy with an added equation head, which the full scope does not need.
//!   kink also checks that the check ran on the whole definition: it must have read every
//!   executable equation, skipped no candidate pair, and classified at least as many pairs as the
//!   definition has root pairs (two equations of one index and priority group); otherwise the
//!   mutant is refused. k-rust reports these counts for the whole definition only, so the guard
//!   does not show, group by group, that every root, self and inner pair was classified; it shows
//!   that no early return fired, since every definition has root pairs of its own or the
//!   prelude's.
//! - A simplification of the check that runs out of native stack decides nothing, and then "the
//!   verdict is a function of the definition only when [`condition_stack_stops`] is zero"; a
//!   nonzero count refuses the mutant. Budget stops are a function of the definition, and a
//!   condition they cut short is not refuted, so they only leave a pair not joined.
//!
//! [`condition_stack_stops`]: k_rust_backend::confluence::CheckCounts::condition_stack_stops

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust::definition::Sentence;
use k_rust::kast::identifier::{decode_label, encode, encode_label};
use k_rust::kast::{GeneratedLabel, Label};
use k_rust::kore::parser::parse_definition;
use k_rust::provenance::InputSpace;
use k_rust_backend::{
    confluence::UnjoinedPair,
    data_term::Finding,
    definition::BackendDefinition,
    rule::{PredicateRewriteRule, RewriteRule, RuleRhs, TermIndex, term_index},
    term::{FunctionType, SymbolType, Term},
};
use kink_patch::{SentenceOrigin, SentenceRef, SourceEffect};

use crate::ValidatedDefinition;
use crate::data::DataFacts;

/// The version of the consistency check: a mutant's admission depends on it, so kink's semantics
/// identity names it (kink-campaign `identity`), on which every store keys. v2 (re-pin
/// R0c-fix-4): the guard also reads the equation and skipped-pair counts. v3 (k-rust
/// FZ-CONFLUENCE): k-rust pairs the equations at evaluated hooks with the hooks' written meanings
/// (a hook pair is read for its first equation only) and refutes more overlaps (equality classes,
/// linear integer arithmetic, deferred unifier equations, disjunctions), so a mutant whose guards
/// those refute is admitted and one whose equation disagrees with its hook is refused.
pub const MUTANT_CONSISTENCY_VERSION: &str = "kink-native/mutant-consistency/v3";

/// The version of the reading of a mutant's effect from the compiled definitions
/// ([`admit_mutant`]: the compiled changed-index diff, its reverse reach and the cross-check of
/// the source reading, re-pin R0c-fix-4). A mutant's admission depends on it, so kink's
/// semantics identity names it (kink-campaign `identity`).
pub const MUTANT_EFFECT_VERSION: &str = "kink-native/mutant-effect/v1";

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

/// The executable equations of one compiled side, read as the check compares and reaches them
/// (re-pin R0c-fix-4): for each index and priority group of k-rust's function theory, the
/// equations without the attributes that do not change what they state; for each symbol, the
/// indexes whose equations mention it; and for each equation, the sentences that wrote it.
#[derive(Clone, Debug)]
pub struct CompiledEquations {
    theory: BTreeMap<TermIndex, BTreeMap<u8, Vec<RewriteRule>>>,
    /// The simplification and ceil lemmas by index (k-rust's `simplification_theory` and
    /// `ceil_theory`), read alike: a changed lemma about a symbol changes how its terms are
    /// simplified, which a join of a pair that reaches it may read.
    lemmas: [BTreeMap<TermIndex, BTreeMap<u8, Vec<RewriteRule>>>; 2],
    /// The lemmas whose left-hand side is a predicate, by priority, read alike.
    predicate_lemmas: BTreeMap<u8, Vec<PredicateRewriteRule>>,
    /// For each symbol, the indexes whose equations apply it in their left-hand side, right-hand
    /// side, `requires` or `ensures`, and the members of its overload family.
    dependents: BTreeMap<String, BTreeSet<TermIndex>>,
    equations: Vec<AuthoredEquation>,
    /// The K labels of the side's source productions, KORE-encoded.
    source_labels: BTreeSet<String>,
    /// The compiled symbols declared `total`.
    total: BTreeSet<String>,
}

/// One compiled equation, its index, its name and the sentences behind it.
#[derive(Clone, Debug)]
struct AuthoredEquation {
    index: TermIndex,
    name: String,
    authors: Vec<Author>,
}

/// A sentence behind a compiled equation, as the mutant's origins map it back.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Author {
    Baseline(SentenceRef),
    Inserted(usize),
    /// A Compile address that names no sentence of the side, or a mutant sentence without an
    /// origin (never expected; read as touched).
    Unresolved,
}

impl CompiledEquations {
    /// The equations of the compiled side `side` (internalized again from its KORE).
    ///
    /// # Errors
    ///
    /// Returns why the side's KORE did not internalize.
    pub fn of(side: &ValidatedDefinition) -> Result<Self, String> {
        let parsed =
            parse_definition(&side.artifacts().definition_kore).map_err(|e| e.to_string())?;
        let definition = BackendDefinition::internalize_for_source_execution(
            &parsed,
            &encode(&side.definition().main_module),
            &side.artifacts().execution_rewrite_order,
        )
        .map_err(|e| e.to_string())?;
        Ok(Self::read(&definition, side))
    }

    fn read(definition: &BackendDefinition, side: &ValidatedDefinition) -> Self {
        let authors = authors(side);
        let mut theory = BTreeMap::<TermIndex, BTreeMap<u8, Vec<RewriteRule>>>::new();
        let mut dependents = BTreeMap::<String, BTreeSet<TermIndex>>::new();
        let mut equations = Vec::new();
        for (index, priorities) in definition.function_theory() {
            for (priority, rules) in priorities {
                for rule in rules {
                    theory
                        .entry(index.clone())
                        .or_default()
                        .entry(*priority)
                        .or_default()
                        .push(meaning(rule));
                    for symbol in mentioned(rule) {
                        dependents.entry(symbol).or_default().insert(index.clone());
                    }
                    if let Some((greater, lesser)) = &rule.attributes.overload {
                        for (from, to) in [(greater, lesser), (lesser, greater)] {
                            dependents
                                .entry(from.to_string())
                                .or_default()
                                .insert(TermIndex::Symbol(to.clone()));
                        }
                    }
                    equations.push(AuthoredEquation {
                        index: index.clone(),
                        name: name(rule),
                        authors: authors
                            .get(&rule.attributes.unique_id)
                            .cloned()
                            .unwrap_or_default(),
                    });
                }
            }
        }
        let lemmas = [definition.simplification_theory(), definition.ceil_theory()].map(|theory| {
            theory
                .iter()
                .map(|(index, priorities)| {
                    let priorities = priorities
                        .iter()
                        .map(|(priority, rules)| {
                            (*priority, rules.iter().map(|r| meaning(r)).collect())
                        })
                        .collect();
                    (index.clone(), priorities)
                })
                .collect()
        });
        let predicate_lemmas = definition
            .predicate_simplification_theory()
            .iter()
            .map(|(priority, rules)| {
                let rules = rules
                    .iter()
                    .map(|rule| {
                        let mut rule = PredicateRewriteRule::clone(rule);
                        rule.attributes.unique_id = String::new();
                        rule.attributes.origins = Vec::new();
                        rule.attributes.preserves_definedness = false;
                        rule.attributes.smt_lemma = false;
                        rule
                    })
                    .collect();
                (*priority, rules)
            })
            .collect();
        let source_labels = side
            .definition()
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
            .filter_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label), ..
                } => Some(encode_label(&label.name)),
                _ => None,
            })
            .collect();
        let total = definition
            .symbols()
            .iter()
            .filter(|(_, symbol)| {
                symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total)
            })
            .map(|(name, _)| name.to_string())
            .collect();
        Self {
            theory,
            lemmas,
            predicate_lemmas,
            dependents,
            equations,
            source_labels,
            total,
        }
    }

    /// Whether `symbol` (a KORE name) is a lambda kompile generated for a `#let` or `#fun`, and
    /// no source production of this side declares it.
    fn generated_lambda(&self, symbol: &str) -> bool {
        !self.source_labels.contains(symbol)
            && decode_label(symbol).is_ok_and(|label| {
                matches!(
                    Label::new(label).generated(),
                    Some(GeneratedLabel::Lambda { .. })
                )
            })
    }
}

/// The equation without the attributes that do not change what it states: its unique id and
/// origins (source positions and sentence places), the claims claim removal handles
/// (`preserves-definedness`, `smt-lemma`), and the load's record of a rewrite rule's definedness
/// discharge (empty on an equation).
fn meaning(rule: &RewriteRule) -> RewriteRule {
    let mut rule = rule.clone();
    rule.attributes.unique_id = String::new();
    rule.attributes.origins = Vec::new();
    rule.attributes.preserves_definedness = false;
    rule.attributes.smt_lemma = false;
    rule.computed_attributes.discharged_by = Default::default();
    rule
}

/// Every symbol an equation applies, in its left-hand side, right-hand side, `requires` and
/// `ensures` (collections' entries included).
fn mentioned(rule: &RewriteRule) -> BTreeSet<String> {
    let mut symbols = BTreeSet::new();
    let mut term = |term: &Term| {
        term.visit_symbols(&mut |symbol| {
            symbols.insert(symbol.name.to_string());
        })
    };
    term(&rule.lhs);
    match &rule.rhs {
        RuleRhs::Term(rhs) => term(rhs),
        RuleRhs::Disjunction(alternatives) => {
            for alternative in alternatives {
                term(&alternative.term);
                for predicate in alternative.ensures.iter() {
                    predicate.visit_terms(&mut term);
                }
            }
        }
        RuleRhs::Predicates(predicates) => {
            for predicate in predicates {
                predicate.visit_terms(&mut term);
            }
        }
        RuleRhs::Top | RuleRhs::Bottom => {}
    }
    for predicate in rule.requires.iter().chain(rule.ensures.iter()) {
        predicate.visit_terms(&mut term);
    }
    symbols
}

/// For each emitted rule id of `side`, the rule sentences behind it: its Compile addresses that
/// name a rule, mapped back to the baseline through a mutant's origins. A rule is the only
/// sentence whose role the source reading decides (a production's edit is a claim edit or an
/// unknown effect, and a configuration's or a sort's is an unknown effect), so the addresses of
/// other sentences are not read.
fn authors(side: &ValidatedDefinition) -> BTreeMap<String, Vec<Author>> {
    let definition = side.definition();
    let sentence = |module: &str, index: u32| {
        definition
            .modules
            .iter()
            .find(|candidate| candidate.name == module)
            .and_then(|module| module.local_sentences.get(usize::try_from(index).ok()?))
    };
    side.artifacts()
        .sentence_provenance
        .iter()
        .map(|(id, provenance)| {
            let authors = provenance
                .input_addresses
                .iter()
                .filter(|address| address.input == InputSpace::Compile)
                .filter_map(|address| {
                    let at = SentenceRef::new(address.module.clone(), address.index);
                    match sentence(&address.module, address.index).map(|s| &**s) {
                        None => return Some(Author::Unresolved),
                        Some(Sentence::Rule { .. }) => {}
                        Some(_) => return None,
                    }
                    Some(match side.origins() {
                        None => Author::Baseline(at),
                        Some(origins) => match origins.get(&at) {
                            Some(SentenceOrigin::Baseline(original)) => {
                                Author::Baseline(original.clone())
                            }
                            Some(SentenceOrigin::Inserted { edit }) => Author::Inserted(*edit),
                            None => Author::Unresolved,
                        },
                    })
                })
                .collect();
            (id.clone(), authors)
        })
        .collect()
}

/// A compiled equation that a sentence the patch touches gives, headed by a symbol the source
/// reading does not redefine (or a generated `total` symbol whose equations the patch changes):
/// the patch's effect on the claims is not known.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnreadEquation {
    /// The touched sentence: a baseline sentence, or the patch's inserting edit; `None` for an
    /// equation whose author could not be resolved, or a generated symbol's.
    pub origin: Option<SentenceOrigin>,
    /// The compiled head (KORE), or the index's kind when it is not a symbol.
    pub head: String,
    /// The equation, named as in [`UnjoinedEquations`].
    pub equation: String,
}

impl fmt::Display for UnreadEquation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} is an equation of {}",
            self.equation, self.head
        )
    }
}

/// Why a mutant is refused before it runs ([`admit_mutant`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MutantFailure {
    /// The compiled definitions show an effect the source reading does not name, so the claims
    /// the edit leaves unbacked are not known: kink-campaign refuses it as `unsupported-claims`.
    UnreadEquations(Vec<UnreadEquation>),
    /// The mutant is not shown to be a theory with models: `inconsistent-mutant`.
    Inconsistent(Inconsistency),
    /// The mutant's own KORE does not internalize (without the probe head either), so no test
    /// could run on it: kink-campaign's infrastructure failure, as when its runtime cannot be
    /// prepared.
    Uninternalizable(String),
}

/// What the compiled definitions say a mutant's edit changes ([`admit_mutant`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CompiledEffect {
    /// The indexes whose equations differ between the baseline and the claim-free mutant (KORE
    /// symbol names, or the index kind).
    pub changed: BTreeSet<String>,
    /// The symbols whose pairs were read (KORE names), `None` for every symbol.
    pub checked: Option<BTreeSet<String>>,
}

/// Whether the claim-free mutant `side` may run (re-pin R0c-fix-3, R0c-fix-4): the compiled
/// definitions agree with the source reading `source` of the patch's effect, and the mutant is
/// shown to be a theory with models where its edit can change one.
///
/// What the edit changes is read from the compiled definitions, which k-rust executes, and the
/// source reading is a fail-closed cross-check (see the module documentation):
///
/// - changed indexes: every index of the claim-free mutant's function theory whose equations
///   differ from `baseline`'s (compared without unique ids, origins and the claims claim removal
///   handles), an index present on one side only included, and every index of its simplification
///   and ceil lemmas that differs alike (a changed predicate lemma checks every head);
/// - checked heads: the reverse reach of the changed indexes over both compiled theories (an
///   equation reaches the symbols it applies, and an overload family is linked both ways),
///   together with the source reading's affected symbols; `None` (every head) when the source
///   reading is unknown or a changed or reached index is not a symbol;
/// - every compiled equation that a sentence the patch touches (or inserts) gives, on either
///   side, is headed by a symbol the source reading redefines, or by a lambda kompile generated
///   for a `#let` or `#fun` (its `total` is derived from the claim-free mutant's own body); and
///   no other generated `total` symbol has changed equations. Otherwise
///   [`MutantFailure::UnreadEquations`].
///
/// The compiled diff is always computed: an empty source reading never admits a mutant without it.
///
/// The witness equations of both sides' full checks are read with them (fz26 KINK-WITNESS): an
/// index whose witnesses differ from `baseline_facts`' (compared as the equations are, so up to
/// the canonical renaming of their variables) is changed, a witness reaches the symbols it
/// applies as an equation of its head does, and a flip of the adopted pass between the two
/// checks ([`DataFacts::witness_pass_adopted`]) checks every head.
///
/// This loads `side` on kink's route itself ([`loaded_definition`]) and reads its full check
/// with no name assumed, before anything is reached; kink-campaign's runner, which loads the
/// mutant once for its runs and its facts, calls [`admit_mutant_with`].
///
/// # Errors
///
/// Returns why the mutant is refused.
pub fn admit_mutant(
    baseline: &CompiledEquations,
    baseline_facts: &DataFacts,
    side: &ValidatedDefinition,
    source: &SourceEffect,
) -> Result<CompiledEffect, MutantFailure> {
    let definition = loaded_definition(side).map_err(MutantFailure::Uninternalizable)?;
    let facts = DataFacts::of(&definition, &[]);
    admit_mutant_with(baseline, baseline_facts, side, source, &definition, &facts)
}

/// The definition a backend loads `side` as on kink's route (`Backend::from_definition` of its
/// compiled KORE for its main module, then the selected definition), on this thread: the
/// definition the side's runs execute on and its full check reads.
///
/// # Errors
///
/// Returns why the side's KORE does not parse, load or internalize.
pub fn loaded_definition(
    side: &ValidatedDefinition,
) -> Result<std::sync::Arc<BackendDefinition>, String> {
    let parsed = parse_definition(&side.artifacts().definition_kore).map_err(|e| e.to_string())?;
    let mut backend = k_rust::backend::Backend::from_definition(
        parsed,
        encode(&side.definition().main_module),
        k_rust::backend::BackendOptions::default(),
    )
    .map_err(|e| e.to_string())?;
    backend.select_definition(None).map_err(|e| e.to_string())
}

/// [`admit_mutant`] on the claim-free mutant `side` loaded as `definition` (the definition its
/// runs execute on, [`loaded_definition`]), whose full check is `facts` (computed on
/// `definition`, with any names: the gate reads assumed findings as unjoined all the same), the
/// baseline's being `baseline_facts` (computed alike on the baseline's load). The mutant's check
/// is thus run before its effect is reached: its witnesses are part of that effect.
///
/// # Errors
///
/// Returns why the mutant is refused.
pub fn admit_mutant_with(
    baseline: &CompiledEquations,
    baseline_facts: &DataFacts,
    side: &ValidatedDefinition,
    source: &SourceEffect,
    definition: &BackendDefinition,
    facts: &DataFacts,
) -> Result<CompiledEffect, MutantFailure> {
    let unchecked = |why: String| MutantFailure::Inconsistent(Inconsistency::Unchecked(why));
    let mutant = CompiledEquations::read(definition, side);

    let unread = unread_equations(baseline, &mutant, source);
    if !unread.is_empty() {
        return Err(MutantFailure::UnreadEquations(unread));
    }

    let mut changed = changed_indexes(&baseline.theory, &mutant.theory);
    for (base, edited) in baseline.lemmas.iter().zip(&mutant.lemmas) {
        changed.extend(changed_indexes(base, edited));
    }
    // fz26 KINK-WITNESS: the full check joins pairs with the witness equations it adopts, so a
    // head whose witnesses differ is changed like one whose equations differ, and a pair that
    // joined through the baseline's witness is checked wherever it reaches that head. A flip of
    // the adopted pass changes which equations every pair was joined with: every head is checked.
    changed.extend(changed_indexes(
        &witness_theory(baseline_facts),
        &witness_theory(facts),
    ));
    let witness_pass_flipped =
        baseline_facts.witness_pass_adopted() != facts.witness_pass_adopted();
    // A changed predicate lemma is about no one symbol: every head is checked.
    let predicate_lemmas_changed = baseline.predicate_lemmas != mutant.predicate_lemmas;
    let generated = changed
        .iter()
        .filter_map(|index| match index {
            TermIndex::Symbol(symbol)
                if mutant.total.contains(&**symbol)
                    && !mutant.source_labels.contains(&**symbol)
                    && !mutant.generated_lambda(symbol) =>
            {
                Some(UnreadEquation {
                    origin: None,
                    head: symbol.to_string(),
                    equation: "a generated total symbol's equations".to_owned(),
                })
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if !generated.is_empty() {
        return Err(MutantFailure::UnreadEquations(generated));
    }

    let reached = reach(
        &changed,
        &[
            &baseline.dependents,
            &mutant.dependents,
            &witness_dependents(baseline_facts),
            &witness_dependents(facts),
        ],
    );
    let source_heads = source.affected.as_ref().map(|affected| {
        affected
            .iter()
            .map(|label| encode_label(label))
            .collect::<BTreeSet<_>>()
    });
    if let Some(heads) = &source_heads {
        // A head kink-patch names must be a symbol of the compiled definition, or its pairs
        // would be read under no name.
        let missing = heads
            .iter()
            .filter(|head| !definition.symbols().contains_key(head.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        if !missing.is_empty() {
            return Err(unchecked(format!(
                "the heads {missing:?} are not symbols of the compiled definition"
            )));
        }
    }
    let checked = match source_heads {
        Some(mut heads)
            if !predicate_lemmas_changed
                && !witness_pass_flipped
                && reached
                    .iter()
                    .all(|index| matches!(index, TermIndex::Symbol(_))) =>
        {
            heads.extend(reached.iter().filter_map(|index| match index {
                TermIndex::Symbol(symbol) => Some(symbol.to_string()),
                _ => None,
            }));
            Some(heads)
        }
        _ => None,
    };
    let effect = CompiledEffect {
        changed: changed.iter().map(index_name).collect(),
        checked,
    };
    if effect.checked.as_ref().is_some_and(BTreeSet::is_empty) {
        // No symbol's equations differ, none reaches one, and the source reading redefines
        // none: every pair is the baseline's.
        return Ok(effect);
    }
    check(facts, effect.checked.as_ref()).map_err(MutantFailure::Inconsistent)?;
    Ok(effect)
}

/// The indexes whose equations differ between two theories, an index of one only included.
fn changed_indexes(
    baseline: &BTreeMap<TermIndex, BTreeMap<u8, Vec<RewriteRule>>>,
    mutant: &BTreeMap<TermIndex, BTreeMap<u8, Vec<RewriteRule>>>,
) -> BTreeSet<TermIndex> {
    baseline
        .keys()
        .chain(mutant.keys())
        .filter(|index| baseline.get(*index) != mutant.get(*index))
        .cloned()
        .collect()
}

/// The compiled equations of a touched (or inserted) sentence that the source reading does not
/// explain, on either side.
fn unread_equations(
    baseline: &CompiledEquations,
    mutant: &CompiledEquations,
    source: &SourceEffect,
) -> Vec<UnreadEquation> {
    let Some(redefined) = &source.redefined else {
        // Every symbol already counts as redefined.
        return Vec::new();
    };
    let redefined = redefined
        .iter()
        .map(|label| encode_label(label))
        .collect::<BTreeSet<_>>();
    let mut unread = Vec::<UnreadEquation>::new();
    for side in [baseline, mutant] {
        for equation in &side.equations {
            let explained = match &equation.index {
                TermIndex::Symbol(symbol) => {
                    redefined.contains(&**symbol) || side.generated_lambda(symbol)
                }
                _ => false,
            };
            if explained {
                continue;
            }
            for author in &equation.authors {
                let origin = match author {
                    Author::Baseline(at) if source.touched.contains(at) => {
                        Some(SentenceOrigin::Baseline(at.clone()))
                    }
                    Author::Baseline(_) => continue,
                    Author::Inserted(edit) => Some(SentenceOrigin::Inserted { edit: *edit }),
                    Author::Unresolved => None,
                };
                let found = UnreadEquation {
                    origin,
                    head: index_name(&equation.index),
                    equation: equation.name.clone(),
                };
                if !unread.contains(&found) {
                    unread.push(found);
                }
            }
        }
    }
    unread
}

/// The indexes whose equations reach one of `changed` (`changed` included), over `edges`: both
/// sides' compiled theories and both sides' witness equations (for each symbol, the indexes whose
/// equations apply it).
fn reach(
    changed: &BTreeSet<TermIndex>,
    edges: &[&BTreeMap<String, BTreeSet<TermIndex>>],
) -> BTreeSet<TermIndex> {
    let mut reached = BTreeSet::new();
    let mut pending = changed.iter().cloned().collect::<Vec<_>>();
    while let Some(index) = pending.pop() {
        if !reached.insert(index.clone()) {
            continue;
        }
        if let TermIndex::Symbol(symbol) = &index {
            for edges in edges {
                if let Some(dependents) = edges.get(&**symbol) {
                    pending.extend(dependents.difference(&reached).cloned());
                }
            }
        }
    }
    reached
}

/// The witness equations of a full check (`facts`), by index and priority, read as the compiled
/// equations are ([`meaning`]): the check renames each witness's variables canonically, so two
/// witnesses equal up to a renaming compare equal, and their unique ids (their text) and origins
/// (the proposing equation) are not read.
fn witness_theory(facts: &DataFacts) -> BTreeMap<TermIndex, BTreeMap<u8, Vec<RewriteRule>>> {
    let mut theory = BTreeMap::<TermIndex, BTreeMap<u8, Vec<RewriteRule>>>::new();
    for rule in facts.witnesses() {
        theory
            .entry(term_index(&rule.lhs))
            .or_default()
            .entry(rule.attributes.priority)
            .or_default()
            .push(meaning(rule));
    }
    theory
}

/// For each symbol a witness equation of `facts` applies (its head, and the constructors and
/// injections of its sides), the witnesses' indexes: a witness `p => t` reaches the symbols of
/// `t` and its head, as an equation of its head does.
fn witness_dependents(facts: &DataFacts) -> BTreeMap<String, BTreeSet<TermIndex>> {
    let mut dependents = BTreeMap::<String, BTreeSet<TermIndex>>::new();
    for rule in facts.witnesses() {
        for symbol in mentioned(rule) {
            dependents
                .entry(symbol)
                .or_default()
                .insert(term_index(&rule.lhs));
        }
    }
    dependents
}

fn index_name(index: &TermIndex) -> String {
    match index {
        TermIndex::Symbol(symbol) => symbol.to_string(),
        other => format!("{other:?}"),
    }
}

/// Whether the claim-free mutant `side` is shown to be a theory with models for the symbols
/// `heads` (K labels; `None` for every symbol): every pair with an equation of one of them, or
/// one not indexed at a symbol, joins by k-rust's critical-pair check. This reads the check for
/// given heads only, on `side` loaded on kink's route ([`loaded_definition`]); [`admit_mutant`]
/// decides which heads an edit can change.
///
/// # Errors
///
/// Returns the pairs not shown to join, or why the check could not decide.
pub fn check_heads(
    side: &ValidatedDefinition,
    heads: Option<&BTreeSet<String>>,
) -> Result<(), Inconsistency> {
    let definition = loaded_definition(side).map_err(Inconsistency::Unchecked)?;
    let heads = heads.map(|heads| {
        heads
            .iter()
            .map(|label| encode_label(label))
            .collect::<BTreeSet<_>>()
    });
    if let Some(heads) = &heads {
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
    check(&DataFacts::of(&definition, &[]), heads.as_ref())
}

/// k-rust's full check of a definition (`facts`, [`DataFacts::heads`] with its counts), read for
/// the KORE symbols `heads`: every finding, assumed by a name or not, that the gate reads for
/// those heads ([`DataFacts::reads`]) refuses.
fn check(facts: &DataFacts, heads: Option<&BTreeSet<String>>) -> Result<(), Inconsistency> {
    // The completeness guard (`DataFacts::incomplete`, the one place it is stated): the check
    // read every executable equation, skipped no candidate pair, classified at least as many
    // pairs as there are root pairs, and met no stack stop.
    if let Some(why) = facts.incomplete() {
        return Err(Inconsistency::Unchecked(why));
    }
    let mut pairs = BTreeSet::new();
    for finding in facts
        .heads()
        .findings()
        .iter()
        .chain(facts.heads().assumed())
        .filter(|finding| facts.reads(finding, heads))
    {
        match finding {
            Finding::Pair { pair, .. } | Finding::Equation(pair) => {
                pairs.insert(unjoined(pair));
            }
            Finding::Precondition(violation) => {
                let name = violation.rule.as_deref().map_or_else(String::new, name);
                pairs.insert(UnjoinedEquations {
                    first: name.clone(),
                    second: name,
                    position: Vec::new(),
                    reason: format!("outside the check: {}", violation.kind),
                });
            }
        }
    }
    if pairs.is_empty() {
        Ok(())
    } else {
        Err(Inconsistency::Unjoined(pairs.into_iter().collect()))
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
