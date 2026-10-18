//! Matching-logic constructs in conditions.
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
#![deny(clippy::wildcard_enum_match_arm)]

use std::convert::Infallible;

use crate::definition::{Definition, Sentence};
use crate::kast::{GeneratedLabel, InternalLabel, Label, Term, TermParts};

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
