//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Matching-logic constructs at term positions that state no meaning k-rust can give, refused at
//! compile with [`DiagnosticCode::MlConstructPosition`], located at the sentence, for the Rust
//! target only (an LLVM target's consumer reads the emitted KORE on its own terms).
//!
//! - An or-pattern in the left side of a function or anywhere equation whose alternatives do not
//!   all bind a variable that the equation's result (its right side or its `ensures`) uses, and
//!   that the left side binds nowhere outside its or-patterns. An equation's left side matches
//!   each alternative, so an alternative that does not bind the variable states the
//!   application's value for every value of it: `f(X #Or 2) => 10 +Int X` states
//!   `f(2) = 10 +Int X` for every `X`. An application has at most one value, so the equation is
//!   an axiom with no model, and no answer derived from it is right. A variable that only the
//!   `requires` reads is quantified over the condition alone (`f(2) = 0` where some `X` meets
//!   it) and states no such value. A rewrite rule's left side matches a configuration, which may
//!   be any of the alternatives, so its alternatives may bind different variables. A
//!   simplification's or-pattern is refused when the definition loads, whatever its
//!   alternatives bind.
//! - A simplification whose left side is a term and whose right side is `#Top`, or a predicate
//!   other than `#Bottom`. A simplification equates a term with a term, or a predicate with a
//!   predicate: such a right side denotes every value of its sort or none, so the lemma states
//!   that the application, which has at most one value, is every value, an axiom with no model.
//!   A lemma whose left side is a predicate (`#Ceil(f(X)) => #Top`) states a predicate's truth
//!   and is unaffected; so is `#Bottom`, which states that the application is undefined. A
//!   function or anywhere equation with such a right side is refused when the definition loads.
//! - A conjunction where a value is built (the right side of a rewrite of a rule, a function
//!   equation, a simplification or an anywhere rule) with two operands that are not predicates,
//!   one of which holds a matching-logic connective (`(X #Or 0) #And 1`). A conjunction of terms
//!   without a connective, each at most one value, is the first where they are equal, and the
//!   stage `lower term conjunctions` writes it so (`t1 #And {t1 #Equals t2}`); a predicate
//!   operand conjoins a condition. A term that holds a connective may denote several values,
//!   where that reading does not hold, and the backend gives a built conjunction of terms
//!   neither a definedness nor a value, so the sentence has no reading.
//!
//! Macro-like rules (`macro`, `alias`) are abbreviations, not equations, and are not judged here;
//! claims and contexts are not judged here either.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;

use super::rhs_variables::compute_unbound;
use super::term_position::{Scope, TermPosition, scoped_children};
use super::{Sentence, is_anonymous};
use crate::definition::{AttributeKey, LabelHead, ProductionCatalog, match_rule_label};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{InternalLabel, Term};
use crate::kompile::ml_constructs::{chain_operands, is_ml_connective, is_predicate};

/// The [`DiagnosticCode::MlConstructPosition`] refusals of `sentences` (module documentation).
pub(super) fn check_ml_construct_positions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::Rule {
            body,
            ensures,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if attributes.has_any(&AttributeKey::MACRO_LIKE) {
            continue;
        }
        if attributes.has(AttributeKey::Simplification) {
            if let Term::Rewrite { left, right } = body.unannotated()
                && !is_ml_connective(left)
                && denotes_every_value_or_none(right)
            {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::MlConstructPosition,
                    "the right-hand side of this simplification is #Top or a predicate, which \
                     denotes every value of its sort or none, while its left-hand side is a term, \
                     whose application has at most one value: the lemma states that the \
                     application is every value, an axiom with no model; give the value, or write \
                     #Bottom where the application is undefined",
                    sentence,
                ));
            }
        } else if (attributes.has(AttributeKey::Anywhere)
            || is_function_rule(sentence, productions))
            && let Some(variables) = unequally_bound_result_variables(body, ensures)
        {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::MlConstructPosition,
                format!(
                    "the left-hand side of this equation holds an or-pattern whose alternatives \
                     do not all bind {}, which the result uses: an alternative that does not bind \
                     it states the application's value for every value of it, while an \
                     application has at most one value, so the equation is an axiom with no \
                     model; bind the same variables in every alternative, or write one equation \
                     per alternative",
                    variables.into_iter().collect::<Vec<_>>().join(", ")
                ),
                sentence,
            ));
        }
        if built_conjunction_over_a_connective(body) {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::MlConstructPosition,
                "a conjunction (#And) where a value is built has two operands that are not \
                 predicates, one of which holds a matching-logic connective: a conjunction of \
                 terms is the first operand where they are equal only when each denotes at most \
                 one value, and a term that holds a connective may denote several, so this \
                 conjunction has no reading; conjoin terms without a connective, or state the \
                 condition as a predicate ({X #Equals 1})",
                sentence,
            ));
        }
    }
    diagnostics
}

/// Whether `rule` is an equation of a `function` production: its left-hand side's root applies
/// one.
fn is_function_rule(rule: &Sentence, productions: &ProductionCatalog<'_>) -> bool {
    productions
        .attributes_for(&LabelHead::from(&match_rule_label(rule)))
        .is_some_and(|attributes| attributes.has(AttributeKey::Function))
}

/// Whether `term` denotes every value of its sort or none: `#Top`, or a predicate other than
/// `#Bottom`.
fn denotes_every_value_or_none(term: &Term) -> bool {
    let term = term.unannotated();
    let bottom = matches!(term, Term::Apply { label, .. } if label.is(InternalLabel::Bottom));
    !bottom && is_predicate(term)
}

fn is_binary(term: &Term, connective: InternalLabel) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, arguments } if label.is(connective) && arguments.len() == 2
    )
}

/// The named variables of `term`.
fn named_variables(term: &Term) -> BTreeSet<String> {
    let mut variables = BTreeSet::new();
    term.visit_preorder(&mut |node| {
        if let Term::Variable { name, .. } = node
            && !is_anonymous(name)
        {
            variables.insert(name.clone());
        }
    });
    variables
}

/// The variables of an equation's result (the built positions of `body`, and `ensures`) that an
/// or-pattern of its left side binds in some alternatives and not in others, and that the left
/// side binds nowhere outside its or-patterns; `None` when there is none.
///
/// A local function's own scope is not walked for bindings: its pattern binds in its body only.
fn unequally_bound_result_variables(body: &Term, ensures: &Term) -> Option<BTreeSet<String>> {
    let mut partial = BTreeSet::new();
    let mut bound_outside = BTreeSet::new();
    let mut pending = vec![(body, TermPosition::BODY, false)];
    // Invariant: each step takes a subterm of `body` and pushes only strict subterms of it.
    while let Some((term, position, in_or_pattern)) = pending.pop() {
        if position.lhs && !position.rhs && is_binary(term, InternalLabel::Or) {
            let alternatives = or_alternatives(term);
            let bindings = alternatives
                .iter()
                .map(|alternative| named_variables(alternative))
                .collect::<Vec<_>>();
            for variable in bindings.iter().flatten() {
                if !bindings.iter().all(|bound| bound.contains(variable)) {
                    partial.insert(variable.clone());
                }
            }
            pending.extend(
                alternatives
                    .into_iter()
                    .map(|alternative| (alternative, position, true)),
            );
            continue;
        }
        if let Term::Variable { name, .. } = term.unannotated()
            && position.lhs
            && !in_or_pattern
            && !is_anonymous(name)
        {
            bound_outside.insert(name.clone());
        }
        pending.extend(
            scoped_children(term, position)
                .into_iter()
                .filter(|(_, _, scope)| *scope == Scope::Enclosing)
                .map(|(child, position, _)| (child, position, in_or_pattern)),
        );
    }
    partial.retain(|variable| !bound_outside.contains(variable));
    if partial.is_empty() {
        return None;
    }
    let mut used = BTreeSet::new();
    compute_unbound(body, TermPosition::BODY, &BTreeSet::new(), &mut used);
    compute_unbound(
        ensures,
        TermPosition::CONDITION,
        &BTreeSet::new(),
        &mut used,
    );
    partial.retain(|variable| used.contains(variable));
    (!partial.is_empty()).then_some(partial)
}

/// The alternatives of the or-pattern `term`, nested or-patterns at its root flattened.
fn or_alternatives(term: &Term) -> Vec<&Term> {
    let mut alternatives = Vec::new();
    let mut pending = vec![term];
    // Invariant: each step replaces a disjunction by its two operands or moves one alternative to
    // `alternatives`, so the finite `term` bounds the loop.
    while let Some(node) = pending.pop() {
        match node.unannotated() {
            Term::Apply { label, arguments }
                if label.is(InternalLabel::Or) && arguments.len() == 2 =>
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
            | Term::Token { .. } => alternatives.push(node),
        }
    }
    alternatives
}

/// Whether a conjunction where `body` builds a value (a position on a rewrite's right side only)
/// has two operands that are not predicates, one of which holds a connective.
fn built_conjunction_over_a_connective(body: &Term) -> bool {
    let mut pending = vec![(body, TermPosition::BODY)];
    // Invariant: each step takes a subterm of `body` and pushes only its strict subterms.
    while let Some((term, position)) = pending.pop() {
        if position.rhs && !position.lhs && is_binary(term, InternalLabel::And) {
            let terms = chain_operands(term, false)
                .into_iter()
                .filter(|operand| !is_predicate(operand))
                .collect::<Vec<_>>();
            if terms.len() >= 2 && terms.iter().copied().any(holds_connective) {
                return true;
            }
        }
        pending.extend(
            scoped_children(term, position)
                .into_iter()
                .map(|(child, position, _)| (child, position)),
        );
    }
    false
}

fn holds_connective(term: &Term) -> bool {
    let mut holds = false;
    term.visit_preorder(&mut |node| holds |= is_ml_connective(node));
    holds
}
