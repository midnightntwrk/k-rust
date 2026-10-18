//! Matching-logic constructs in conditions and in terms.
//!
//! A condition whose root is a matching-logic connective (`#Or`, `#And`, `#Not`, `#Implies`,
//! `#Iff`, `#Top`, `#Bottom`, `#Ceil`, `#Floor`, `#Equals`, `#Exists`, `#Forall`) is a predicate,
//! not a Bool term. A pass that adds a conjunct to a condition must therefore conjoin a predicate
//! with the predicate conjunction `#And`: conjoined with `_andBool_`, a Bool function, the predicate
//! would stand as an argument of that function, where a connective denotes a set of values rather
//! than a truth, and where no backend reads it as a condition. Two Bool terms keep `_andBool_`, so
//! a condition without a connective compiles as before.
//!
//! Whether a condition is a predicate is a property of the pattern the backend reads, which the
//! passes that add conjuncts do not see yet: a macro or an alias (`isOne(N)` defined as
//! `{N #Equals 1}`) is expanded later, and a cast (`({N #Equals 1}):Bool`) computes nothing and is
//! read through. So [`conjoin_condition`] decides at once only when neither operand can change its
//! reading, and otherwise writes a pending conjunction, which the stage
//! [`resolve_condition_conjunctions_pass`] replaces right after macro expansion, and which the
//! search-pattern compiler resolves after its own macro expansion. Constant folding, which runs
//! before macro expansion, decides a pending conjunction whose operands it has made tokens
//! ([`settle_conjunction`]), so it folds it as it would fold `_andBool_` of two tokens. Every one
//! of these sites chooses the conjunction with [`condition_conjunction`].
//!
//! A pending conjunction is internal to the pipeline: no production declares its label. The public
//! functions of the conjoining passes (`resolve_strict`, `resolve_heat_cool_attributes`,
//! `resolve_semantic_casts_with_predicates_in_sentence`) therefore resolve it before they return,
//! on the condition as it stands, and the stage checker panics on one that survives the
//! resolving stage (C2, [`crate::kompile::invariants::stage`]).
//!
//! # A conjunction of two terms
//!
//! A term without a connective, built from variables, domain values and applications of
//! constructors and functions, denotes at most one value. For two such terms t1 = {a} and
//! t2 = {b}, `t1 #And t2` is {a} ∩ {b}: {a} where a = b, empty otherwise, which is exactly
//! `t1 #And {t1 #Equals t2}`; this also holds where t1 or t2 is undefined, since both sides are
//! then empty. The conjunction is associative and commutative, and an intersection with a set
//! of at most one value has at most one value, so a chain `t1 #And t2 #And ... #And tn` of such
//! terms, however it is grouped, is `t1 #And {t1 #Equals t2} #And ... #And {t1 #Equals tn}`.
//! The stage [`lower_term_conjunctions_pass`], after macro expansion (so a macro or alias body is
//! lowered where it is used), writes a chain of connective-free terms in that form wherever its
//! value is built: in the right side of a rewrite of a rule, a function equation, a
//! simplification or an anywhere rule, and anywhere in a claim's body. In a claim's left side,
//! and at a position of a claim outside its rewrites, which is in its left side too, it also
//! writes `P #as V`, which denotes the same set as `P #And V`, as `P #And {P #Equals V}`. The
//! form denotes the same set of values, and the backend decides its equality, where a
//! conjunction of two terms would be left as a leaf that denotes nothing.
//!
//! An operand that holds a connective may denote several values, where the identity does not
//! hold: `(X #Or 0) #And 1` at X = 1 is {1, 0} ∩ {1} = {1}, while
//! `(X #Or 0) #And {(X #Or 0) #Equals 1}` states {1, 0} = {1}, which never holds. An operand
//! that applies an `impure` production, directly or through a function whose equations do,
//! performs an effect when it is evaluated: the form would copy it, so the effect would be
//! performed again, and would place it in an equality, a predicate, where no effect is
//! performed. A chain with such an operand is left as written, and so is a conjunction at a
//! matched position (a rule's left side or a position its rewrites share): matching unifies its
//! operands. A macro-like rule defines an abbreviation and is lowered only through its uses.
//!
//! The stage generates the equalities and the copies of the first operand in them, so it is a
//! generating stage: the pipeline records [`LOWER_TERM_CONJUNCTIONS`] as the origin of each node
//! it changes or creates, linked to the origins of the node it came from, and each copy, cloned
//! from the operand, keeps the operand's span, production and sort.
#![deny(clippy::wildcard_enum_match_arm)]

use std::cell::OnceCell;
use std::collections::BTreeSet;
use std::convert::Infallible;

use crate::definition::{AttributeKey, Definition, ResolveError, Sentence};
use crate::kast::{GeneratedLabel, InternalLabel, Label, Term, TermParts};
use crate::provenance::GeneratingPass;

/// The matching-logic connectives and predicate atoms of the frontend's term language.
const CONNECTIVES: [InternalLabel; 12] = [
    InternalLabel::Or,
    InternalLabel::And,
    InternalLabel::Not,
    InternalLabel::Implies,
    InternalLabel::Iff,
    InternalLabel::Top,
    InternalLabel::Bottom,
    InternalLabel::Ceil,
    InternalLabel::Floor,
    InternalLabel::Equals,
    InternalLabel::Exists,
    InternalLabel::Forall,
];

/// The Bool conjunction, a function of two Bool terms.
const AND_BOOL: &str = "_andBool_";

/// The label of a conjunction whose operands may still change their reading. It lives only between
/// the conjoining passes and condition-conjunction resolution; no production declares it and no
/// emitted definition holds it.
const PENDING_CONJUNCTION: &str = "#krustPendingConditionAnd";

/// Whether the root of `term`, its annotations aside, is a matching-logic connective or predicate
/// atom.
pub(crate) fn is_ml_connective(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, .. } if CONNECTIVES.iter().any(|connective| label.is(*connective))
    )
}

/// The term a condition operand is read as: `term` without its annotations and without the casts
/// at its root (a semantic cast `(t):S`, a syntactic cast `t::S` or `{t}::S`, and `#OuterCast`),
/// which compute nothing.
fn read_through_casts(term: &Term) -> &Term {
    let mut term = term.unannotated();
    // Invariant: `term` is a subterm of the argument, one cast deeper on each iteration, so the
    // loop ends at the first root that is not a cast.
    while let Term::Apply { label, arguments } = term
        && let [operand] = &arguments[..]
        && (matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
            || label.is(InternalLabel::SyntacticCast)
            || label.is(InternalLabel::SyntacticCastBraced)
            || label.is(InternalLabel::OuterCast))
    {
        term = operand.unannotated();
    }
    term
}

/// Whether the condition `term` is read as a predicate: its root, read through casts, is a
/// matching-logic connective.
fn reads_as_predicate(term: &Term) -> bool {
    is_ml_connective(read_through_casts(term))
}

/// Whether no later stage can change how the condition `term` is read: a predicate stays one, and
/// a token or a variable is a Bool term whatever is expanded around it. Any other application may
/// be a macro or an alias that expands to a predicate.
fn is_settled(term: &Term) -> bool {
    reads_as_predicate(term)
        || matches!(
            read_through_casts(term),
            Term::Token { .. } | Term::Variable { .. }
        )
}

/// The label of the conjunction of two conditions as the backend reads them: the predicate
/// conjunction `#And` when either is a predicate, the Bool conjunction `_andBool_` otherwise.
fn conjunction_label(left: &Term, right: &Term) -> Label {
    if reads_as_predicate(left) || reads_as_predicate(right) {
        Label::new(InternalLabel::And.as_str())
    } else {
        Label::new(AND_BOOL)
    }
}

/// The label of the conjunction of `left` and `right` when no later stage can change it: one
/// operand already reads as a predicate, or both operands are settled; `None` otherwise.
fn decided_label(left: &Term, right: &Term) -> Option<Label> {
    (reads_as_predicate(left) || reads_as_predicate(right) || is_settled(left) && is_settled(right))
        .then(|| conjunction_label(left, right))
}

/// The conjunction of two conditions in the form the backend reads, macros expanded and casts
/// read through: `#And(left, right)` when either is a predicate, `_andBool_(left, right)`
/// otherwise.
pub(crate) fn condition_conjunction(left: Term, right: Term) -> Term {
    Term::Apply {
        label: conjunction_label(&left, &right),
        arguments: vec![left, right],
    }
}

/// The conjunction a pass adds to a condition: [`condition_conjunction`] when no later stage can
/// change its choice, otherwise the pending conjunction that [`resolve_condition_conjunctions`]
/// decides.
pub(crate) fn conjoin_condition(left: Term, right: Term) -> Term {
    let label = decided_label(&left, &right).unwrap_or_else(|| Label::new(PENDING_CONJUNCTION));
    Term::Apply {
        label,
        arguments: vec![left, right],
    }
}

/// `label` applied to `arguments`, with a pending conjunction whose choice no later stage can
/// change any more replaced by the conjunction [`condition_conjunction`] chooses; any other
/// application unchanged.
pub(crate) fn settle_conjunction(label: Label, arguments: Vec<Term>) -> (Label, Vec<Term>) {
    let decided = match &arguments[..] {
        [left, right] if label.name == PENDING_CONJUNCTION => decided_label(left, right),
        _ => None,
    };
    (decided.unwrap_or(label), arguments)
}

/// The label a sentence identifier hashes for `label`: `_andBool_` for a pending conjunction, so
/// that the identifier of a sentence numbered before the choice is made does not depend on a
/// label internal to the pipeline; `None` for any other label.
pub(crate) fn hashed_label(label: &Label) -> Option<Label> {
    (label.name == PENDING_CONJUNCTION).then(|| Label::new(AND_BOOL))
}

/// Whether `term` holds a pending conjunction.
pub(crate) fn holds_pending_conjunction(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |node| {
        found |= matches!(node, Term::Apply { label, .. } if label.name == PENDING_CONJUNCTION);
    });
    found
}

/// `term` with every pending conjunction replaced, innermost first, by the conjunction
/// [`condition_conjunction`] chooses on its operands; every node keeps its metadata. It runs after
/// macro expansion, when no operand changes its reading any more.
pub(crate) fn resolve_condition_conjunctions(term: Term) -> Term {
    if holds_pending_conjunction(&term) {
        resolve_in(term)
    } else {
        term
    }
}

// Invariant: each call recurses into the immediate subterms of `term`, so the finite `term`
// bounds the recursion; every pending conjunction below `term` is resolved before `term`.
fn resolve_in(term: Term) -> Term {
    crate::stack::guarded(|| match term.into_parts() {
        TermParts::Annotated { term, metadata } => resolve_in(*term).with_metadata(metadata),
        TermParts::Apply { label, arguments } => {
            let mut arguments = arguments.into_iter().map(resolve_in).collect::<Vec<_>>();
            if label.name == PENDING_CONJUNCTION && arguments.len() == 2 {
                let right = arguments.pop().expect("a conjunction has two operands");
                let left = arguments.pop().expect("a conjunction has two operands");
                condition_conjunction(left, right)
            } else {
                Term::Apply { label, arguments }
            }
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(resolve_in(*left)),
            right: Box::new(resolve_in(*right)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(resolve_in(*pattern)),
            alias: Box::new(resolve_in(*alias)),
        },
        TermParts::Sequence(items) => Term::Sequence(items.into_iter().map(resolve_in).collect()),
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(leaf),
    })
}

fn sentence_holds_pending_conjunction(sentence: &Sentence) -> bool {
    sentence
        .terms()
        .any(|(_, term)| holds_pending_conjunction(term))
}

fn definition_holds_pending_conjunction(definition: &Definition) -> bool {
    definition.modules.iter().any(|module| {
        module
            .local_sentences
            .iter()
            .any(|sentence| sentence_holds_pending_conjunction(sentence))
    })
}

fn resolve_terms(sentence: &mut Sentence) {
    for (_, term) in sentence.terms_mut() {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = resolve_condition_conjunctions(taken);
    }
}

/// `sentence` with every pending conjunction of its terms resolved by
/// [`resolve_condition_conjunctions`].
pub(crate) fn resolve_condition_conjunctions_in_sentence(mut sentence: Sentence) -> Sentence {
    if sentence_holds_pending_conjunction(&sentence) {
        resolve_terms(&mut sentence);
    }
    sentence
}

/// `definition` with every pending conjunction of every sentence resolved by
/// [`resolve_condition_conjunctions`]; a sentence without one is kept as it is.
pub(crate) fn resolve_condition_conjunctions_in_definition(
    mut definition: Definition,
) -> Definition {
    for module in &mut definition.modules {
        for sentence in &mut module.local_sentences {
            if sentence_holds_pending_conjunction(sentence) {
                resolve_terms(crate::definition::sentence_mut(sentence));
            }
        }
    }
    definition
}

/// The stage `resolve condition conjunctions`, right after `expand macros`: every pending
/// conjunction of every sentence resolved by [`resolve_condition_conjunctions`]. A sentence
/// without one is kept as it is, shared, and a definition without one is unchanged.
pub(crate) fn resolve_condition_conjunctions_pass(
    input: &super::pipeline::PassInput<'_>,
    _: &mut super::pipeline::PipelineState,
) -> Result<super::pipeline::PassOutcome, Infallible> {
    if !definition_holds_pending_conjunction(input.definition) {
        return Ok(super::pipeline::PassOutcome::Unchanged);
    }
    Ok(super::pipeline::PassOutcome::Changed(
        resolve_condition_conjunctions_in_definition(input.definition.clone()),
    ))
}

/// Where a subterm of a sentence body stands, and so which of its conjunctions the lowering
/// rewrites.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Position {
    /// A rule's left side or a position its rewrites share: matched, left as written.
    Matched,
    /// The right side of a rewrite: built.
    Built,
    /// A position of a claim outside its rewrites, in both its left and its right side.
    ClaimShared,
    /// The left side of a rewrite of a claim.
    ClaimLeft,
}

impl Position {
    fn lowers_conjunctions(self) -> bool {
        self != Self::Matched
    }

    /// An alias denotes the conjunction of its pattern and its variable where a claim's left side
    /// holds it: in the left side of a rewrite, and at a position the claim's sides share.
    fn lowers_aliases(self) -> bool {
        matches!(self, Self::ClaimShared | Self::ClaimLeft)
    }

    /// The position of the left side of a rewrite at this position.
    fn rewrite_left(self) -> Self {
        match self {
            Self::Matched | Self::Built => Self::Matched,
            Self::ClaimShared | Self::ClaimLeft => Self::ClaimLeft,
        }
    }
}

/// Whether `term` holds no matching-logic connective at any depth, and no rewrite or alias, which
/// are not terms.
fn is_connective_free_term(term: &Term) -> bool {
    let mut free = true;
    term.visit_preorder(&mut |node| {
        free &= !is_ml_connective(node) && !matches!(node, Term::Rewrite { .. } | Term::As { .. });
    });
    free
}

/// The operands of the conjunction chain `term`, left to right: `term` itself when it is no
/// conjunction, otherwise the operands of each of its operands' chains, so that
/// `(t1 #And t2) #And t3` and `t1 #And (t2 #And t3)` both give t1, t2, t3.
fn chain_operands(term: &Term) -> Vec<&Term> {
    let mut operands = Vec::new();
    let mut pending = vec![term];
    // Invariant: `operands` then the reverse of `pending` are the chain's operands in order; each
    // step replaces a conjunction on top of `pending` by its two operands or moves one operand
    // to `operands`, so the finite `term` bounds the loop.
    while let Some(node) = pending.pop() {
        match node.unannotated() {
            Term::Apply { label, arguments }
                if label.is(InternalLabel::And) && arguments.len() == 2 =>
            {
                pending.extend(arguments.iter().rev());
            }
            Term::Apply { .. }
            | Term::Annotated { .. }
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::InjectedLabel(_)
            | Term::Variable { .. }
            | Term::Token { .. } => operands.push(node),
        }
    }
    operands
}

/// `t1 #And {t1 #Equals t2} #And ... #And {t1 #Equals tn}` for the operands t1, ..., tn (at least
/// two), grouped to the left, with t1 copied into each equality.
fn guarded_by_equalities(conjunction: &Label, operands: &[&Term]) -> Term {
    let (first, rest) = operands.split_first().expect("a conjunction has operands");
    rest.iter().fold((*first).clone(), |guarded, operand| {
        let equality = Term::Apply {
            label: Label::new(InternalLabel::Equals.as_str()),
            arguments: vec![(*first).clone(), (*operand).clone()],
        };
        Term::Apply {
            label: conjunction.clone(),
            arguments: vec![guarded, equality],
        }
    })
}

/// The lowering of the sentences of one definition: which labels perform an effect when applied.
struct Lowering<'a> {
    /// Whether applying `label` performs an effect: it is declared `impure`, or a function whose
    /// equations apply one.
    is_impure: &'a dyn Fn(&Label) -> bool,
}

impl Lowering<'_> {
    /// Whether each of `terms` denotes at most one value and evaluating it performs no effect:
    /// no matching-logic connective at any depth, no rewrite or alias, which are not terms, and
    /// no application of an impure label. The impure labels are consulted only for terms that
    /// pass the first two checks, so that the definition is resolved only for a conjunction the
    /// stage may lower.
    fn are_plain_terms(&self, terms: &[&Term]) -> bool {
        terms.iter().all(|term| is_connective_free_term(term))
            && terms.iter().all(|term| {
                let mut pure = true;
                term.visit_preorder(&mut |node| {
                    pure &= !matches!(node, Term::Apply { label, .. } if (self.is_impure)(label));
                });
                pure
            })
    }

    /// `term`, standing at `position`, with each conjunction chain of plain terms
    /// ([`Self::are_plain_terms`]) that the position builds written as its first operand guarded
    /// by its equality with each other operand, and in a claim's left side and shared positions
    /// each alias `P #as V` of plain terms written as `P #And {P #Equals V}`; `None` when nothing
    /// in `term` changes. Every node that is kept keeps its metadata.
    fn lower(&self, term: &Term, position: Position) -> Option<Term> {
        crate::stack::guarded(|| self.lower_level(term, position))
    }

    /// Lowers each of `terms` at `position`; `None` when none changes. Nothing is allocated until
    /// a term changes.
    fn lower_all(&self, terms: &[Term], position: Position) -> Option<Vec<Term>> {
        let mut output: Option<Vec<Term>> = None;
        for (index, term) in terms.iter().enumerate() {
            match (self.lower(term, position), &mut output) {
                (Some(lowered), Some(output)) => output.push(lowered),
                (Some(lowered), None) => {
                    let mut kept = terms[..index].to_vec();
                    kept.push(lowered);
                    output = Some(kept);
                }
                (None, Some(output)) => output.push(term.clone()),
                (None, None) => {}
            }
        }
        output
    }

    /// The chain `term`, rooted at the conjunction `label`, lowered as a whole when every operand
    /// of it is a plain term; `None` otherwise.
    fn lower_chain(&self, label: &Label, term: &Term) -> Option<Term> {
        let operands = chain_operands(term);
        self.are_plain_terms(&operands)
            .then(|| guarded_by_equalities(label, &operands))
    }

    // Invariant: each call recurses into the immediate subterms of `term`, so the finite `term`
    // bounds the recursion; a lowered chain or alias is not descended into, since its operands
    // hold nothing to lower.
    fn lower_level(&self, term: &Term, position: Position) -> Option<Term> {
        match term {
            Term::Annotated {
                term: inner,
                metadata,
            } => {
                let lowered = self.lower(inner, position)?;
                let mut metadata = metadata.clone();
                // An alias lowered to a conjunction is no application of the alias production; an
                // alias kept, whose subterms were lowered, still is.
                if matches!(inner.unannotated(), Term::As { .. })
                    && !matches!(lowered.unannotated(), Term::As { .. })
                {
                    metadata.production = None;
                }
                Some(lowered.with_metadata(metadata))
            }
            Term::Apply { label, arguments }
                if position.lowers_conjunctions()
                    && label.is(InternalLabel::And)
                    && arguments.len() == 2
                    && let Some(lowered) = self.lower_chain(label, term) =>
            {
                Some(lowered)
            }
            Term::As { pattern, alias }
                if position.lowers_aliases() && self.are_plain_terms(&[pattern, alias]) =>
            {
                Some(guarded_by_equalities(
                    &Label::new(InternalLabel::And.as_str()),
                    &[pattern, alias],
                ))
            }
            Term::Apply { label, arguments } => {
                self.lower_all(arguments, position)
                    .map(|arguments| Term::Apply {
                        label: label.clone(),
                        arguments,
                    })
            }
            Term::Rewrite { left, right } => {
                let lowered_left = self.lower(left, position.rewrite_left());
                let lowered_right = self.lower(right, Position::Built);
                (lowered_left.is_some() || lowered_right.is_some()).then(|| Term::Rewrite {
                    left: Box::new(lowered_left.unwrap_or_else(|| (**left).clone())),
                    right: Box::new(lowered_right.unwrap_or_else(|| (**right).clone())),
                })
            }
            Term::As { pattern, alias } => {
                let lowered_pattern = self.lower(pattern, position);
                let lowered_alias = self.lower(alias, position);
                (lowered_pattern.is_some() || lowered_alias.is_some()).then(|| Term::As {
                    pattern: Box::new(lowered_pattern.unwrap_or_else(|| (**pattern).clone())),
                    alias: Box::new(lowered_alias.unwrap_or_else(|| (**alias).clone())),
                })
            }
            Term::Sequence(items) => self.lower_all(items, position).map(Term::Sequence),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
        }
    }

    /// `sentence` with its body lowered by [`Self::lower`]: a rule's at a matched position (so
    /// only its rewrites' right sides are built), a claim's at a position of both its sides;
    /// `None` for a sentence that does not change, including a macro-like rule, other sentence
    /// kinds and every condition.
    fn lower_sentence(&self, sentence: &Sentence) -> Option<Sentence> {
        let position = match sentence {
            Sentence::Rule { attributes, .. } if attributes.has_any(&AttributeKey::MACRO_LIKE) => {
                return None;
            }
            Sentence::Rule { .. } => Position::Matched,
            Sentence::Claim { .. } => Position::ClaimShared,
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => return None,
        };
        let (Sentence::Rule { body, .. } | Sentence::Claim { body, .. }) = sentence else {
            unreachable!("only rules and claims are lowered")
        };
        let lowered = self.lower(body, position)?;
        let mut sentence = sentence.clone();
        if let Sentence::Rule { body, .. } | Sentence::Claim { body, .. } = &mut sentence {
            *body = lowered;
        }
        Some(sentence)
    }
}

/// The labels whose application performs an effect when `definition` runs: the `impure`
/// productions and, transitively, the functions whose equations apply one, as its main module
/// sees them (the module whose rules run), or as any module does when it has no main module.
fn impure_labels(
    definition: &Definition,
    resolved: &crate::definition::ResolvedDefinition,
) -> BTreeSet<String> {
    let labels_of = |module| {
        let productions = resolved.production_catalog(module);
        super::module_to_kore::transitive_impure_labels(resolved, module, &productions)
    };
    match resolved.module_id(&definition.main_module) {
        Some(main) => labels_of(main),
        None => definition
            .modules
            .iter()
            .filter_map(|module| resolved.module_id(&module.name))
            .flat_map(labels_of)
            .collect(),
    }
}

/// The pass the stage `lower term conjunctions` records as the origin of the nodes it generates:
/// the equalities, and the copies of the first operand in them.
pub(crate) const LOWER_TERM_CONJUNCTIONS: GeneratingPass = GeneratingPass::LowerTermConjunctions;

/// The stage `lower term conjunctions`, after macro expansion: every rule and claim lowered by
/// [`Lowering::lower_sentence`] (see the module documentation). A sentence that does not change
/// is kept as it is, shared, and a definition in which none changes is unchanged. The impure
/// labels are computed, from the resolved definition, only when a conjunction or alias is
/// considered for lowering.
pub(crate) fn lower_term_conjunctions_pass(
    input: &super::pipeline::PassInput<'_>,
    _: &mut super::pipeline::PipelineState,
) -> Result<super::pipeline::PassOutcome, ResolveError> {
    let impure: OnceCell<Result<BTreeSet<String>, ResolveError>> = OnceCell::new();
    let is_impure = |label: &Label| {
        let labels = impure.get_or_init(|| {
            input
                .resolved_raw()
                .map(|resolved| impure_labels(input.definition, resolved))
                .map_err(Clone::clone)
        });
        // Without the resolved definition no label is known to be pure; the error is returned
        // below, so nothing is lowered under that assumption.
        labels
            .as_ref()
            .map_or(true, |labels| labels.contains(&label.name))
    };
    let lowering = Lowering {
        is_impure: &is_impure,
    };
    let mut output: Option<Definition> = None;
    for (module_index, module) in input.definition.modules.iter().enumerate() {
        for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
            if let Some(lowered) = lowering.lower_sentence(sentence) {
                let definition = output.get_or_insert_with(|| input.definition.clone());
                *crate::definition::sentence_mut(
                    &mut definition.modules[module_index].local_sentences[sentence_index],
                ) = lowered;
            }
        }
    }
    if let Some(Err(error)) = impure.into_inner() {
        return Err(error);
    }
    Ok(output.map_or(
        super::pipeline::PassOutcome::Unchanged,
        super::pipeline::PassOutcome::Changed,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kast::Sort;

    fn test(name: &str) -> Term {
        Term::apply(name, vec![Term::variable("X")])
    }

    fn equals() -> Term {
        Term::apply(
            InternalLabel::Equals.as_str(),
            vec![Term::variable("X"), Term::variable("Y")],
        )
    }

    fn truth() -> Term {
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        }
    }

    fn label(term: &Term) -> &str {
        let Term::Apply { label, .. } = term.unannotated() else {
            panic!("not an application: {term:?}")
        };
        &label.name
    }

    #[test]
    fn a_predicate_is_conjoined_as_a_predicate_and_two_bool_terms_as_a_bool_term() {
        for (left, right) in [
            (equals(), test("isInt")),
            (test("isInt"), equals()),
            (equals(), equals()),
        ] {
            assert_eq!(label(&condition_conjunction(left, right)), "#And");
        }
        assert_eq!(
            label(&condition_conjunction(test("isInt"), test("isBool"))),
            AND_BOOL
        );
    }

    #[test]
    fn a_predicate_under_a_cast_is_read_as_a_predicate() {
        for cast in ["#SemanticCastToBool", "#SyntacticCast", "#OuterCast"] {
            let cast = Term::apply(cast, vec![equals()]);
            assert_eq!(label(&condition_conjunction(cast, test("isInt"))), "#And");
        }
        let cast = Term::apply("#SemanticCastToBool", vec![test("isInt")]);
        assert_eq!(label(&condition_conjunction(cast, test("isInt"))), AND_BOOL);
    }

    /// Two settled operands are conjoined at once; an application that a later expansion may turn
    /// into a predicate leaves the conjunction pending until resolution.
    #[test]
    fn a_conjunction_is_pending_until_its_operands_are_settled() {
        assert_eq!(label(&conjoin_condition(truth(), truth())), AND_BOOL);
        assert_eq!(label(&conjoin_condition(equals(), test("isOne"))), "#And");
        assert_eq!(
            label(&conjoin_condition(Term::variable("B"), truth())),
            AND_BOOL
        );
        assert_eq!(
            label(&conjoin_condition(test("isOne"), truth())),
            PENDING_CONJUNCTION
        );
        // `isOne(X)` expanded to a predicate, in a pending conjunction that is an operand of
        // another: both resolve to `#And`, the inner one first.
        let expanded = Term::apply(PENDING_CONJUNCTION, vec![equals(), truth()]);
        let outer = Term::apply(PENDING_CONJUNCTION, vec![expanded, test("isKResult")]);
        let resolved = resolve_condition_conjunctions(outer);
        assert_eq!(label(&resolved), "#And");
        let Term::Apply { arguments, .. } = &resolved else {
            unreachable!("a conjunction is an application")
        };
        assert_eq!(label(&arguments[0]), "#And");
        let bool_terms = Term::apply(PENDING_CONJUNCTION, vec![test("isOne"), truth()]);
        assert_eq!(label(&resolve_condition_conjunctions(bool_terms)), AND_BOOL);
    }

    #[test]
    fn a_pending_conjunction_of_settled_operands_is_settled_for_the_fold() {
        let (settled, _) =
            settle_conjunction(Label::new(PENDING_CONJUNCTION), vec![truth(), truth()]);
        assert_eq!(settled.name, AND_BOOL);
        let (pending, _) = settle_conjunction(
            Label::new(PENDING_CONJUNCTION),
            vec![test("isOne"), truth()],
        );
        assert_eq!(pending.name, PENDING_CONJUNCTION);
    }

    #[test]
    fn a_pending_conjunction_is_hashed_as_the_bool_conjunction() {
        assert_eq!(
            hashed_label(&Label::new(PENDING_CONJUNCTION)),
            Some(Label::new(AND_BOOL))
        );
        assert_eq!(hashed_label(&Label::new(AND_BOOL)), None);
    }

    fn int(value: &str) -> Term {
        Term::Token {
            token: value.into(),
            sort: Sort::new("Int"),
        }
    }

    fn and(first: Term, second: Term) -> Term {
        Term::apply(InternalLabel::And.as_str(), vec![first, second])
    }

    fn equality(first: Term, second: Term) -> Term {
        Term::apply(InternalLabel::Equals.as_str(), vec![first, second])
    }

    fn rewrite(left: Term, right: Term) -> Term {
        Term::Rewrite {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn alias(pattern: Term, alias: Term) -> Term {
        Term::As {
            pattern: Box::new(pattern),
            alias: Box::new(alias),
        }
    }

    fn go(term: Term) -> Term {
        Term::apply("go", vec![term])
    }

    /// `term` at `position` lowered where the labels `impure` perform an effect.
    fn lower_with(impure: &[&str], term: &Term, position: Position) -> Option<Term> {
        let is_impure = |label: &Label| impure.contains(&label.name.as_str());
        Lowering {
            is_impure: &is_impure,
        }
        .lower(term, position)
    }

    /// `term` at `position` lowered where no label performs an effect.
    fn lower(term: &Term, position: Position) -> Option<Term> {
        lower_with(&[], term, position)
    }

    fn done(term: Term) -> Term {
        Term::apply("done", vec![term])
    }

    /// `X #And 1` and `f(X) #And 3`, built, become the first operand guarded by the equality.
    #[test]
    fn a_built_conjunction_of_two_terms_is_the_first_guarded_by_their_equality() {
        let x = Term::variable("X");
        let body = rewrite(go(x.clone()), done(and(x.clone(), int("1"))));
        assert_eq!(
            lower(&body, Position::Matched),
            Some(rewrite(
                go(x.clone()),
                done(and(x.clone(), equality(x.clone(), int("1"))))
            ))
        );
        let f = Term::apply("f", vec![x.clone()]);
        let built = and(f.clone(), int("3"));
        assert_eq!(
            lower(&built, Position::Built),
            Some(and(f.clone(), equality(f, int("3"))))
        );
    }

    /// A connective in an operand, at any depth, keeps the conjunction as written; one below it
    /// is still lowered.
    #[test]
    fn a_conjunction_whose_operand_holds_a_connective_is_kept() {
        let x = Term::variable("X");
        let or = Term::apply(InternalLabel::Or.as_str(), vec![x.clone(), int("0")]);
        assert_eq!(lower(&and(or.clone(), int("1")), Position::Built), None);
        let deep = and(Term::apply("g", vec![or]), int("1"));
        assert_eq!(lower(&deep, Position::Built), None);
        let predicate = and(x.clone(), equality(x.clone(), int("1")));
        assert_eq!(lower(&predicate, Position::Built), None);
        // The conjunction below an operand that holds a connective is still lowered.
        let nested = and(
            and(x.clone(), int("1")),
            Term::apply(InternalLabel::Or.as_str(), vec![x.clone(), int("0")]),
        );
        let Some(Term::Apply { ref arguments, .. }) = lower(&nested, Position::Built) else {
            panic!("the inner conjunction is lowered")
        };
        assert_eq!(arguments[0], and(x.clone(), equality(x, int("1"))));
    }

    /// A chain of terms, grouped either way, is its first operand guarded by its equality with
    /// each other operand, grouped to the left.
    #[test]
    fn a_conjunction_chain_of_terms_is_its_first_operand_guarded_by_each_equality() {
        let x = Term::variable("X");
        let expected = and(
            and(x.clone(), equality(x.clone(), int("1"))),
            equality(x.clone(), int("2")),
        );
        let left = and(and(x.clone(), int("1")), int("2"));
        assert_eq!(lower(&left, Position::Built), Some(expected.clone()));
        let right = and(x.clone(), and(int("1"), int("2")));
        assert_eq!(lower(&right, Position::Built), Some(expected));
        let annotated = and(
            and(x.clone(), int("1")).with_metadata(crate::kast::TermMetadata::default()),
            int("2"),
        );
        assert_eq!(
            lower(&annotated, Position::Built),
            lower(&left, Position::Built)
        );
    }

    /// An operand that applies an impure label, at any depth, keeps the whole chain as written.
    #[test]
    fn a_conjunction_with_an_impure_operand_is_kept() {
        let x = Term::variable("X");
        let read = Term::apply("#getc", vec![int("0")]);
        for term in [
            and(read.clone(), x.clone()),
            and(x.clone(), Term::apply("f", vec![read.clone()])),
            and(and(read.clone(), x.clone()), int("1")),
        ] {
            assert_eq!(lower_with(&["#getc"], &term, Position::Built), None);
            assert!(lower(&term, Position::Built).is_some());
        }
        // A conjunction of plain terms below the chain is lowered by itself; the impure operand
        // is neither copied nor placed in an equality.
        let below = and(and(x.clone(), int("1")), read.clone());
        assert_eq!(
            lower_with(&["#getc"], &below, Position::Built),
            Some(and(
                and(x.clone(), equality(x.clone(), int("1"))),
                read.clone()
            ))
        );
        let claim = rewrite(go(alias(read, Term::variable("Y"))), done(x));
        assert_eq!(lower_with(&["#getc"], &claim, Position::ClaimShared), None);
    }

    /// A rule's left side and the positions its rewrites share are matched; a claim's are not.
    #[test]
    fn a_matched_conjunction_is_kept_and_a_claim_side_is_lowered() {
        let x = Term::variable("X");
        let lowered = and(x.clone(), equality(x.clone(), int("1")));
        let body = rewrite(go(and(x.clone(), int("1"))), done(x.clone()));
        assert_eq!(lower(&body, Position::Matched), None);
        assert_eq!(
            lower(&body, Position::ClaimShared),
            Some(rewrite(go(lowered.clone()), done(x.clone())))
        );
        let shared = Term::apply(
            "pair",
            vec![and(x.clone(), int("1")), rewrite(int("2"), int("3"))],
        );
        assert_eq!(lower(&shared, Position::Matched), None);
        assert_eq!(
            lower(&shared, Position::ClaimShared),
            Some(Term::apply(
                "pair",
                vec![lowered, rewrite(int("2"), int("3"))]
            ))
        );
    }

    /// `P #as V` is lowered in a claim's left side and its shared positions only.
    #[test]
    fn an_alias_is_lowered_in_a_claim_left_side_and_shared_positions_only() {
        let (x, y) = (Term::variable("X"), Term::variable("Y"));
        let body = rewrite(go(alias(x.clone(), y.clone())), done(y.clone()));
        assert_eq!(lower(&body, Position::Matched), None);
        assert_eq!(
            lower(&body, Position::ClaimShared),
            Some(rewrite(
                go(and(x.clone(), equality(x.clone(), y.clone()))),
                done(y.clone())
            ))
        );
        let shared = go(alias(x.clone(), y.clone()));
        assert_eq!(
            lower(&shared, Position::ClaimShared),
            Some(go(and(x.clone(), equality(x.clone(), y.clone()))))
        );
        assert_eq!(lower(&shared, Position::Matched), None);
        let built = rewrite(go(x.clone()), done(alias(x.clone(), y.clone())));
        assert_eq!(lower(&built, Position::ClaimShared), None);
        let or = Term::apply(InternalLabel::Or.as_str(), vec![x.clone(), int("0")]);
        assert_eq!(lower(&alias(or, y), Position::ClaimLeft), None);
    }

    /// The conjunction keeps its annotation; an alias's annotation loses only its production.
    #[test]
    fn a_lowered_node_keeps_its_metadata() {
        let x = Term::variable("X");
        let metadata = crate::kast::TermMetadata {
            sort: Some(Sort::new("Int")),
            ..crate::kast::TermMetadata::default()
        };
        let annotated = and(x.clone(), int("1")).with_metadata(metadata.clone());
        let lowered = lower(&annotated, Position::Built).expect("lowered");
        assert_eq!(lowered.metadata(), Some(&metadata));
        assert_eq!(
            lowered.unannotated(),
            &and(x.clone(), equality(x.clone(), int("1")))
        );
        // An alias lowered to a conjunction loses its production; an alias kept, whose pattern
        // holds a lowered conjunction, keeps it.
        let production = crate::kast::TermMetadata {
            production: Some(crate::kast::ProductionIdentity::from_digest([7; 16])),
            ..metadata
        };
        let y = Term::variable("Y");
        let plain = alias(x.clone(), y.clone()).with_metadata(production.clone());
        let lowered = lower(&plain, Position::ClaimLeft).expect("lowered");
        assert_eq!(lowered.metadata().and_then(|m| m.production), None);
        let kept = alias(and(x.clone(), int("1")), y).with_metadata(production.clone());
        let lowered = lower(&kept, Position::ClaimLeft).expect("the inner conjunction is lowered");
        assert!(matches!(lowered.unannotated(), Term::As { .. }));
        assert_eq!(lowered.metadata(), Some(&production));
    }

    #[test]
    fn every_connective_and_only_a_connective_is_one() {
        for connective in CONNECTIVES {
            assert!(is_ml_connective(&Term::apply(
                connective.as_str(),
                Vec::new()
            )));
        }
        assert!(!is_ml_connective(&test(AND_BOOL)));
        assert!(!is_ml_connective(&Term::variable("X")));
        assert!(!is_ml_connective(&Term::apply(
            InternalLabel::Fun2.as_str(),
            Vec::new()
        )));
    }
}
