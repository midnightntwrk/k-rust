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
//! A predicate (an equality, a definedness atom, `#Top`, `#Bottom`, or a connective over
//! predicates) denotes every value or none, so it cannot enlarge the intersection: in a chain
//! that also holds predicates, each predicate is kept in place and each term after the first is
//! replaced by its equality with the first (`X #And {P} #And 1` is
//! `X #And {P} #And {X #Equals 1}`). The stage [`lower_term_conjunctions_pass`], after macro
//! expansion (so a macro or alias body is lowered where it is used), writes such a chain in that
//! form wherever its value is built: in the right side of a rewrite of a rule, a function
//! equation, a simplification or an anywhere rule, and anywhere in a claim's body. Everywhere in
//! a claim's body, which is a pattern on both sides (its left side matches the states it starts
//! from, its right side the states every path reaches, and a position outside its rewrites is in
//! both), an alias `P #as V`, which denotes the same set as `P #And V`, is a conjunction of the chain,
//! so `P #as V` is written `P #And {P #Equals V}` and `(X #as Y) #as Z` is
//! `X #And {X #Equals Y} #And {X #Equals Z}`. The form denotes the same set of values, and the
//! backend decides its equalities, where a conjunction of two terms would be left as a leaf that
//! denotes nothing.
//!
//! A term that holds a connective may denote several values, where the identity does not
//! hold: `(X #Or 0) #And 1` at X = 1 is {1, 0} ∩ {1} = {1}, while
//! `(X #Or 0) #And {(X #Or 0) #Equals 1}` states {1, 0} = {1}, which never holds. A term that
//! applies an effectful production (one declared `impure` or hooked to an effect, or one whose
//! equations apply such a production) may perform an effect when it is evaluated: the form would
//! copy it, so the effect would be performed again, and would place it in an equality, a
//! predicate, where no effect is performed. A chain with such a term is left as written (a chain
//! of plain terms below it is still lowered), and so is a conjunction at a matched position (a
//! rule's left side or a position its rewrites share): matching unifies its operands. A
//! macro-like rule defines an abbreviation and is lowered only through its uses.
//!
//! The stage generates the equalities and the copies of the first operand in them, so it is a
//! generating stage: the pipeline records [`LOWER_TERM_CONJUNCTIONS`] as the origin of each node
//! it changes or creates, linked to the origins of the node it came from, and each copy, cloned
//! from the operand, keeps the operand's span, production and sort.
#![deny(clippy::wildcard_enum_match_arm)]

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;

use crate::definition::{AttributeKey, Definition, Sentence};
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

/// Why an `#Equals` whose operands are not both terms and not both predicates states no condition,
/// with the remedy: the one text of the compile refusals of such an equality, on a condition's
/// spine (the KORE emitter) and at any depth (the matching-logic position check).
pub(crate) const MIXED_EQUALITY_OPERANDS: &str = "whose operands are not both terms (an equality of values) or both predicates (their iff); a predicate at sort Bool denotes all of Bool or nothing (at any sort, all of it or nothing), so it never equals one value, and a connective over terms denotes a set of values, which is not a Boolean condition. To state that a predicate P holds, write P itself as the condition (#Not(P) that it fails); to combine Bool values, use Bool operations such as andBool and orBool";

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
pub(crate) fn read_through_casts(term: &Term) -> &Term {
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
    /// The right side of a rewrite of a claim: the pattern the states every path reaches are
    /// matched against.
    ClaimRight,
}

impl Position {
    fn lowers_conjunctions(self) -> bool {
        self != Self::Matched
    }

    /// An alias denotes the conjunction of its pattern and its variable where a claim's pattern
    /// holds it: in either side of a rewrite, and at a position the claim's sides share.
    fn lowers_aliases(self) -> bool {
        matches!(self, Self::ClaimShared | Self::ClaimLeft | Self::ClaimRight)
    }

    /// The position of the left side of a rewrite at this position.
    fn rewrite_left(self) -> Self {
        match self {
            Self::Matched | Self::Built => Self::Matched,
            Self::ClaimShared | Self::ClaimLeft | Self::ClaimRight => Self::ClaimLeft,
        }
    }

    /// The position of the right side of a rewrite at this position.
    fn rewrite_right(self) -> Self {
        match self {
            Self::Matched | Self::Built => Self::Built,
            Self::ClaimShared | Self::ClaimLeft | Self::ClaimRight => Self::ClaimRight,
        }
    }
}

/// Whether `term` holds no matching-logic connective at any depth, and no rewrite or alias, which
/// are not terms.
pub(crate) fn is_connective_free_term(term: &Term) -> bool {
    let mut free = true;
    term.visit_preorder(&mut |node| {
        free &= !is_ml_connective(node) && !matches!(node, Term::Rewrite { .. } | Term::As { .. });
    });
    free
}

/// Whether `term` denotes every value or none whatever its operands denote: an equality, a
/// definedness or totality atom, `#Top` or `#Bottom`, or a connective over such patterns (for a
/// quantifier, its body).
pub(crate) fn is_predicate(term: &Term) -> bool {
    crate::stack::guarded(|| {
        let Term::Apply { label, arguments } = term.unannotated() else {
            return false;
        };
        if [
            InternalLabel::Equals,
            InternalLabel::Ceil,
            InternalLabel::Floor,
            InternalLabel::Top,
            InternalLabel::Bottom,
        ]
        .iter()
        .any(|atom| label.is(*atom))
        {
            return true;
        }
        if label.is(InternalLabel::Exists) || label.is(InternalLabel::Forall) {
            return arguments.last().is_some_and(is_predicate);
        }
        [
            InternalLabel::Or,
            InternalLabel::And,
            InternalLabel::Not,
            InternalLabel::Implies,
            InternalLabel::Iff,
        ]
        .iter()
        .any(|connective| label.is(*connective))
            && !arguments.is_empty()
            && arguments.iter().all(is_predicate)
    })
}

/// The operands of the conjunction chain `term`, left to right: `term` itself when it is no
/// conjunction, otherwise the operands of each of its operands' chains, so that
/// `(t1 #And t2) #And t3` and `t1 #And (t2 #And t3)` both give t1, t2, t3. With `aliases`, an
/// alias `P #as V`, which denotes `P #And V`, is a conjunction of the chain too.
pub(crate) fn chain_operands(term: &Term, aliases: bool) -> Vec<&Term> {
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
            Term::As { pattern, alias } if aliases => {
                pending.push(alias);
                pending.push(pattern);
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

/// The lowering of the sentences of one definition: which labels perform an effect when applied.
struct Lowering<'a> {
    /// Whether applying `label` may perform an effect ([`effectful_labels`]).
    is_effectful: &'a dyn Fn(&Label) -> bool,
}

impl Lowering<'_> {
    /// Whether each of `terms` denotes at most one value and evaluating it performs no effect:
    /// no matching-logic connective at any depth, no rewrite or alias, which are not terms, and
    /// no application of an effectful label. The effectful labels are consulted only for terms
    /// that pass the first two checks, so that they are computed only for a conjunction the
    /// stage may lower.
    fn are_plain_terms(&self, terms: &[&Term]) -> bool {
        terms.iter().all(|term| is_connective_free_term(term))
            && terms.iter().all(|term| {
                let mut pure = true;
                term.visit_preorder(&mut |node| {
                    pure &=
                        !matches!(node, Term::Apply { label, .. } if (self.is_effectful)(label));
                });
                pure
            })
    }

    /// `term`, standing at `position`, with each conjunction chain that the position builds, of
    /// plain terms ([`Self::are_plain_terms`]) and predicates, written as its first term guarded
    /// by its equality with each other term, the predicates kept in place; in a claim an alias
    /// `P #as V` is a conjunction of such a chain. `None` when
    /// nothing in `term` changes. Every node that is kept keeps its metadata.
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

    /// The chain rooted at `term` (a conjunction, or at a position that lowers aliases an alias),
    /// lowered as a whole when it has at least two terms, each of them plain, and every other
    /// operand is a predicate: each term after the first t1 becomes `{t1 #Equals t}` in place,
    /// each predicate is kept (lowered inside at `position`), grouped to the left. A predicate
    /// denotes every value or none, so it cannot enlarge the intersection, and the terms'
    /// intersection is t1 where each equals t1. `None` otherwise.
    fn lower_chain(&self, term: &Term, position: Position) -> Option<Term> {
        let operands = chain_operands(term, position.lowers_aliases());
        let predicate: Vec<bool> = operands
            .iter()
            .map(|operand| is_predicate(operand))
            .collect();
        let terms: Vec<&Term> = operands
            .iter()
            .zip(&predicate)
            .filter_map(|(operand, predicate)| (!predicate).then_some(*operand))
            .collect();
        if terms.len() < 2 || !self.are_plain_terms(&terms) {
            return None;
        }
        let first = terms[0];
        let conjunction = Label::new(InternalLabel::And.as_str());
        let mut seen_first = false;
        let mut lowered: Option<Term> = None;
        for (operand, predicate) in operands.into_iter().zip(predicate) {
            let piece = if predicate {
                self.lower(operand, position)
                    .unwrap_or_else(|| operand.clone())
            } else if !seen_first {
                seen_first = true;
                first.clone()
            } else {
                Term::Apply {
                    label: Label::new(InternalLabel::Equals.as_str()),
                    arguments: vec![first.clone(), operand.clone()],
                }
            };
            lowered = Some(match lowered {
                None => piece,
                Some(guarded) => Term::Apply {
                    label: conjunction.clone(),
                    arguments: vec![guarded, piece],
                },
            });
        }
        lowered
    }

    // Invariant: each call recurses into the immediate subterms of `term`, so the finite `term`
    // bounds the recursion; a lowered chain is not descended into except for its predicates,
    // each lowered once, since its terms hold nothing to lower.
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
                    && let Some(lowered) = self.lower_chain(term, position) =>
            {
                Some(lowered)
            }
            Term::As { .. }
                if position.lowers_aliases()
                    && let Some(lowered) = self.lower_chain(term, position) =>
            {
                Some(lowered)
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
                let lowered_right = self.lower(right, position.rewrite_right());
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

/// Whether `lower term conjunctions` lowers the alias `alias` (`P #as V`) standing in the right
/// side of a claim's rewrite: the terms of its chain (`P`'s chain with `V`, the predicates
/// beside them aside) are at least two, and each denotes at most one value and performs no
/// effect, `is_effectful` deciding which labels may perform one ([`effectful_labels`]). Only
/// then is `P #as V`, which denotes `P #And V`, written `P #And {P #Equals V}`: no other compiled
/// form of a claim's right side keeps `P`.
pub(crate) fn lowers_claim_alias(alias: &Term, is_effectful: &dyn Fn(&Label) -> bool) -> bool {
    Lowering { is_effectful }
        .lower_chain(alias, Position::ClaimRight)
        .is_some()
}

/// The hook namespace whose hooks act on the world outside the term: the backend evaluates
/// `IO.getc`, `IO.read`, `IO.putc`, `IO.write` and `IO.logString` with that effect, and every
/// other hook of the namespace (files, sockets, `IO.system`, `IO.time`, logs) acts on it by its
/// name.
const EFFECTFUL_HOOK_NAMESPACE: &str = "IO.";

/// The hooks outside [`EFFECTFUL_HOOK_NAMESPACE`] whose value depends on or changes state outside
/// their arguments: a random number or seed, a fresh identifier or buffer, the environment, the
/// command line, the compiled definition's directory, the configuration, a timer.
const EFFECTFUL_HOOKS: [&str; 11] = [
    "INT.rand",
    "INT.srand",
    "STRING.uuid",
    "BUFFER.empty",
    "KREFLECTION.configuration",
    "KREFLECTION.fresh",
    "KREFLECTION.getenv",
    "KREFLECTION.argv",
    "KREFLECTION.kompiledDir",
    "TIMER.timerStart",
    "TIMER.timerStop",
];

/// The one effectful hook whose application k-rust evaluates inside a predicate: `IO.logString`
/// (`#log`), whose value is `.K` by its declaration (`returnsUnit`) whatever its output does, and
/// whose output a predicate does not perform.
const VALUE_INDEPENDENT_HOOK: &str = "IO.logString";

/// The labels of `definition` whose application may perform an effect when it is evaluated, an
/// over-approximation: the productions declared `impure` or hooked to an effectful hook
/// ([`EFFECTFUL_HOOK_NAMESPACE`], [`EFFECTFUL_HOOKS`]), and every label with an equation (a
/// function's, a simplification, an anywhere rule or a macro-like rule, in any module) that
/// applies one of them, transitively. Lowering an operand that performs no effect is only
/// declined, while lowering one that does would perform its effect again, or not at all, so the
/// set errs on the side of keeping a conjunction as written.
pub(crate) fn effectful_labels(definition: &Definition) -> BTreeSet<String> {
    effect_closure(
        || {
            definition
                .modules
                .iter()
                .flat_map(|module| module.local_sentences.iter().map(|sentence| &**sentence))
        },
        |attributes| attributes.has(AttributeKey::Impure) || has_effectful_hook(attributes),
    )
}

/// The labels among the productions and equations of `sentences` (every local sentence of a
/// definition) whose application's value certainly depends on an effect: the productions hooked
/// to an effectful hook ([`EFFECTFUL_HOOK_NAMESPACE`], [`EFFECTFUL_HOOKS`]) other than
/// [`VALUE_INDEPENDENT_HOOK`], and, transitively, every label that has a defining equation (a
/// function's equation, an anywhere rule or a macro-like rule; simplifications restate values and
/// are not counted) and all of whose defining equations, `owise` included, apply such a label in
/// their right side or condition. Such a value depends on the state outside the term (the console,
/// a file, the environment, a random source, the configuration) and on what the effect does to it.
/// A label with one effect-free equation is not in the set: an application that equation decides
/// has its ordinary value (`sel(5)` where `sel(N) => N requires N =/=Int 0`), and an application
/// that reaches an effectful equation is left to the run. A production declared `impure` without
/// such a hook is evaluated by its equations from its arguments, so it is judged by them.
pub(crate) fn value_effect_labels<'s, I>(sentences: impl Fn() -> I) -> BTreeSet<String>
where
    I: Iterator<Item = &'s Sentence>,
{
    let mut certain = BTreeSet::new();
    let mut functions = BTreeSet::new();
    for sentence in sentences() {
        let Sentence::Production {
            label: Some(label),
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if [
            AttributeKey::Function,
            AttributeKey::Functional,
            AttributeKey::Total,
        ]
        .iter()
        .any(|key| attributes.has(*key))
        {
            functions.insert(label.name.clone());
        }
        if has_effectful_hook(attributes)
            && attributes.string(AttributeKey::Hook) != Some(VALUE_INDEPENDENT_HOOK)
        {
            certain.insert(label.name.clone());
        }
    }
    // The labels each defining equation of each head applies in its right side or condition.
    let mut equations: BTreeMap<String, Vec<BTreeSet<String>>> = BTreeMap::new();
    for sentence in sentences() {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } = sentence
        else {
            continue;
        };
        let Term::Rewrite { left, right } = body.unannotated() else {
            continue;
        };
        let Term::Apply { label: head, .. } = left.unannotated() else {
            continue;
        };
        if attributes.has(AttributeKey::Simplification)
            || !(functions.contains(&head.name)
                || attributes.has(AttributeKey::Anywhere)
                || attributes.has_any(&AttributeKey::MACRO_LIKE))
        {
            continue;
        }
        let mut applied = BTreeSet::new();
        for root in [&**right, requires, ensures] {
            root.visit_preorder(&mut |node| {
                if let Term::Apply { label, .. } = node.unannotated() {
                    applied.insert(label.name.clone());
                }
            });
        }
        equations
            .entry(head.name.clone())
            .or_default()
            .push(applied);
    }
    // Invariant: `certain` holds the seeds and the heads found so far all of whose equations
    // apply a member; each pass adds at least one head or stops, and the finite set of heads
    // bounds the passes.
    loop {
        let found = equations
            .iter()
            .filter(|(head, applied)| {
                !certain.contains(*head)
                    && applied
                        .iter()
                        .all(|labels| labels.iter().any(|label| certain.contains(label)))
            })
            .map(|(head, _)| head.clone())
            .collect::<Vec<_>>();
        if found.is_empty() {
            return certain;
        }
        certain.extend(found);
    }
}

/// Whether a production with `attributes` is hooked to an effectful hook.
fn has_effectful_hook(attributes: &crate::definition::Attributes) -> bool {
    attributes.string(AttributeKey::Hook).is_some_and(|hook| {
        hook.starts_with(EFFECTFUL_HOOK_NAMESPACE) || EFFECTFUL_HOOKS.contains(&hook)
    })
}

/// The labels of the productions of `sentences` that `seed` selects by their attributes, and every
/// label with an equation (a function's, a simplification, an anywhere rule or a macro-like rule,
/// in any module) that applies one of them, transitively.
fn effect_closure<'s, I>(
    sentences: impl Fn() -> I,
    seed: impl Fn(&crate::definition::Attributes) -> bool,
) -> BTreeSet<String>
where
    I: Iterator<Item = &'s Sentence>,
{
    let mut effectful = BTreeSet::new();
    let mut functions = BTreeSet::new();
    for sentence in sentences() {
        let Sentence::Production {
            label: Some(label),
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if [
            AttributeKey::Function,
            AttributeKey::Functional,
            AttributeKey::Total,
        ]
        .iter()
        .any(|key| attributes.has(*key))
        {
            functions.insert(label.name.clone());
        }
        if seed(attributes) {
            effectful.insert(label.name.clone());
        }
    }
    // The heads whose equations apply each label.
    let mut callers: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for sentence in sentences() {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } = sentence
        else {
            continue;
        };
        let left = if let Term::Rewrite { left, .. } = body.unannotated() {
            left.unannotated()
        } else {
            body.unannotated()
        };
        let Term::Apply { label: head, .. } = left else {
            continue;
        };
        if !(functions.contains(&head.name)
            || attributes.has(AttributeKey::Anywhere)
            || attributes.has(AttributeKey::Simplification)
            || attributes.has_any(&AttributeKey::MACRO_LIKE))
        {
            continue;
        }
        for root in [body, requires, ensures] {
            root.visit_preorder(&mut |node| {
                if let Term::Apply { label, .. } = node.unannotated() {
                    callers
                        .entry(label.name.clone())
                        .or_default()
                        .insert(head.name.clone());
                }
            });
        }
    }
    let mut pending: Vec<String> = effectful.iter().cloned().collect();
    // Invariant: `effectful` holds the seeds and every caller found so far; `pending` holds the
    // members whose callers are not yet added. A label enters `pending` once, when it enters
    // `effectful`, so the finite set of labels bounds the loop.
    while let Some(label) = pending.pop() {
        for caller in callers.get(&label).into_iter().flatten() {
            if effectful.insert(caller.clone()) {
                pending.push(caller.clone());
            }
        }
    }
    effectful
}

/// The pass the stage `lower term conjunctions` records as the origin of the nodes it generates:
/// the equalities, and the copies of the first term in them.
pub(crate) const LOWER_TERM_CONJUNCTIONS: GeneratingPass = GeneratingPass::LowerTermConjunctions;

/// The stage `lower term conjunctions`, after macro expansion: every rule and claim lowered by
/// [`Lowering::lower_sentence`] (see the module documentation). A sentence that does not change
/// is kept as it is, shared, and a definition in which none changes is unchanged. The effectful
/// labels ([`effectful_labels`]) are computed only when a conjunction is considered for
/// lowering.
pub(crate) fn lower_term_conjunctions_pass(
    input: &super::pipeline::PassInput<'_>,
    _: &mut super::pipeline::PipelineState,
) -> Result<super::pipeline::PassOutcome, Infallible> {
    let effectful: OnceCell<BTreeSet<String>> = OnceCell::new();
    let is_effectful = |label: &Label| {
        effectful
            .get_or_init(|| effectful_labels(input.definition))
            .contains(&label.name)
    };
    let lowering = Lowering {
        is_effectful: &is_effectful,
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
        let is_effectful = |label: &Label| impure.contains(&label.name.as_str());
        Lowering {
            is_effectful: &is_effectful,
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

    /// A predicate operand is kept in place and each term after the first is guarded against
    /// the first term, wherever the predicate stands.
    #[test]
    fn a_mixed_chain_keeps_its_predicates_and_guards_its_terms() {
        let x = Term::variable("X");
        let p = equality(x.clone(), int("1"));
        let mixed = and(and(x.clone(), p.clone()), int("2"));
        assert_eq!(
            lower(&mixed, Position::Built),
            Some(and(
                and(x.clone(), p.clone()),
                equality(x.clone(), int("2"))
            ))
        );
        let leading = and(p.clone(), and(x.clone(), int("2")));
        assert_eq!(
            lower(&leading, Position::Built),
            Some(and(
                and(p.clone(), x.clone()),
                equality(x.clone(), int("2"))
            ))
        );
        // One term only: nothing to guard.
        assert_eq!(lower(&and(x.clone(), p.clone()), Position::Built), None);
        // A connective over terms is no predicate.
        let or = Term::apply(InternalLabel::Or.as_str(), vec![x.clone(), int("0")]);
        assert_eq!(
            lower(&and(and(x.clone(), or), int("2")), Position::Built)
                .map(|lowered| lowered.unannotated().clone()),
            None
        );
        assert!(is_predicate(&Term::apply(
            InternalLabel::Not.as_str(),
            vec![p.clone()]
        )));
        assert!(!is_predicate(&Term::apply(
            InternalLabel::Not.as_str(),
            vec![x.clone()]
        )));
    }

    /// Nested aliases in a claim's left side are one chain.
    #[test]
    fn nested_claim_aliases_are_a_chain() {
        let (x, y, z) = (
            Term::variable("X"),
            Term::variable("Y"),
            Term::variable("Z"),
        );
        let nested = go(alias(alias(x.clone(), y.clone()), z.clone()));
        let expected = go(and(
            and(x.clone(), equality(x.clone(), y)),
            equality(x.clone(), z),
        ));
        assert_eq!(
            lower(&nested, Position::ClaimShared),
            Some(expected.clone())
        );
        assert_eq!(lower(&nested, Position::ClaimLeft), Some(expected));
        assert_eq!(lower(&nested, Position::Built), None);
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

    /// `P #as V` is lowered in a claim, on either side of its rewrites and at its shared
    /// positions, and nowhere in a rule.
    #[test]
    fn an_alias_is_lowered_in_a_claim_only() {
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
        assert_eq!(
            lower(&built, Position::ClaimShared),
            Some(rewrite(
                go(x.clone()),
                done(and(x.clone(), equality(x.clone(), y.clone())))
            ))
        );
        assert_eq!(lower(&built, Position::Matched), None);
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
        // holds a lowered conjunction below a constructor, keeps it.
        let production = crate::kast::TermMetadata {
            production: Some(crate::kast::ProductionIdentity::from_digest([7; 16])),
            ..metadata
        };
        let y = Term::variable("Y");
        let plain = alias(x.clone(), y.clone()).with_metadata(production.clone());
        let lowered = lower(&plain, Position::ClaimLeft).expect("lowered");
        assert_eq!(lowered.metadata().and_then(|m| m.production), None);
        let kept = alias(Term::apply("g", vec![and(x.clone(), int("1"))]), y)
            .with_metadata(production.clone());
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
