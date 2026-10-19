//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Matching-logic constructs at term positions that state no meaning k-rust can give, refused at
//! compile with [`DiagnosticCode::MlConstructPosition`], located at the sentence, for the Rust
//! target only (an LLVM target's consumer reads the emitted KORE on its own terms).
//!
//! - An or-pattern in the left side of a function or anywhere equation, where some combination of
//!   the alternatives of its or-patterns does not bind a variable that the equation's result (its
//!   right side or its `ensures`) uses. An equation's left side matches each combination, the
//!   alternatives of different or-patterns chosen independently, so a combination that does not
//!   bind the variable states the application's value for every value of it:
//!   `f(X #Or 2) => 10 +Int X` states `f(2) = 10 +Int X` for every `X`. An application has at
//!   most one value, so the equation is an axiom with no model, and no answer derived from it is
//!   right. A variable is bound in every combination exactly when it occurs outside every
//!   or-pattern, or some or-pattern binds it in every one of its alternatives, recursively
//!   (`f3(g(X) #Or h(X), X #Or 0) => X` binds `X` in each of its four combinations). Use is
//!   syntactic, which is decidable: a variable that occurs in the result is used, even where the
//!   result's value does not depend on it (`f(X #Or 0) => X *Int 0`). A variable that only the
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
//!   one of which may denote several values (`(X #Or 0) #And 1`). A conjunction of terms that each
//!   denote at most one value is the first where they are equal, and the stage
//!   `lower term conjunctions` writes it so (`t1 #And {t1 #Equals t2}`) where no operand holds a
//!   connective; a predicate operand conjoins a condition. A term denotes at most one value when
//!   its only connectives are `#Bottom` and conjunctions whose term operands denote at most one
//!   value, beside any predicate conjuncts (`g(X #And 1)`, `g(X #And {X #Equals 1})`). A term
//!   with any other connective (`#Or`, `#Top`, `#Not`, `#Implies`, `#Iff`, a quantifier, or a
//!   predicate standing for a term) may denote several values, where that reading does not
//!   hold, and the backend gives a built conjunction of terms neither a definedness nor a value,
//!   so the sentence has no reading.
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
            && let Some(unbound) = unequally_bound_result_variables(body, ensures)
        {
            let uses = unbound
                .iter()
                .map(|(side, variable, alternative)| {
                    format!(
                        "the {side} uses {variable}, which the alternative `{}` of an or-pattern \
                         in the left-hand side does not bind",
                        display(alternative)
                    )
                })
                .collect::<Vec<_>>()
                .join("; ");
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::MlConstructPosition,
                format!(
                    "{uses}: an alternative that does not bind a variable the result uses states \
                     the application's value for every value of the variable, while an \
                     application has at most one value, so the equation is an axiom with no \
                     model (a variable is used where it occurs in the result, even where the \
                     result's value does not depend on it); bind the same variables in every \
                     alternative, or write one equation per alternative"
                ),
                sentence,
            ));
        }
        if built_conjunction_over_a_connective(body) {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::MlConstructPosition,
                "a conjunction (#And) where a value is built has two operands that are not \
                 predicates, one of which holds a matching-logic connective that lets it denote \
                 several values: a conjunction of terms is the first operand where they are \
                 equal only when each denotes at most one value, so this conjunction has no \
                 reading; conjoin terms without such a connective, or state the condition as a \
                 predicate ({X #Equals 1})",
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

/// A term as an author wrote it, for a message: a token as its text, anything else as KAST.
fn display(term: &Term) -> String {
    if let Term::Token { token, .. } = term.unannotated() {
        token.clone()
    } else {
        term.unannotated().to_string()
    }
}

/// The variables a term at a matched position binds in every combination of the alternatives of
/// its or-patterns (`every`), and in some combination (`some`).
struct Bindings {
    every: BTreeSet<String>,
    some: BTreeSet<String>,
}

/// The [`Bindings`] of `term` at `position`. An or-pattern binds in every combination what each
/// of its alternatives does, and in some what one of them does; any other term binds what its
/// children bind, the combinations of different children chosen independently. Only matched
/// positions bind, and a local function's own scope binds in its body only, so it is not walked.
fn bindings(term: &Term, position: TermPosition) -> Bindings {
    crate::stack::guarded(|| {
        if position.lhs && !position.rhs && is_binary(term, InternalLabel::Or) {
            let mut alternatives = or_alternatives(term)
                .into_iter()
                .map(|alternative| bindings(alternative, position));
            let first = alternatives.next().expect("an or-pattern has alternatives");
            return alternatives.fold(first, |mut found, alternative| {
                found
                    .every
                    .retain(|variable| alternative.every.contains(variable));
                found.some.extend(alternative.some);
                found
            });
        }
        let mut found = Bindings {
            every: BTreeSet::new(),
            some: BTreeSet::new(),
        };
        if let Term::Variable { name, .. } = term.unannotated()
            && position.lhs
            && !is_anonymous(name)
        {
            found.every.insert(name.clone());
            found.some.insert(name.clone());
        }
        for (child, position, scope) in scoped_children(term, position) {
            if scope == Scope::Enclosing {
                let child = bindings(child, position);
                found.every.extend(child.every);
                found.some.extend(child.some);
            }
        }
        found
    })
}

/// An alternative of an or-pattern of `term` (at `position`) whose combinations do not bind
/// `variable`, where some combination of `term` binds it and not every one does; the innermost
/// such alternative.
fn unbinding_alternative<'t>(
    term: &'t Term,
    position: TermPosition,
    variable: &str,
) -> Option<&'t Term> {
    crate::stack::guarded(|| {
        if position.lhs && !position.rhs && is_binary(term, InternalLabel::Or) {
            let alternative = or_alternatives(term)
                .into_iter()
                .find(|alternative| !bindings(alternative, position).every.contains(variable))?;
            return Some(
                unbinding_alternative(alternative, position, variable).unwrap_or(alternative),
            );
        }
        scoped_children(term, position)
            .into_iter()
            .filter(|(_, _, scope)| *scope == Scope::Enclosing)
            .find_map(|(child, position, _)| {
                let found = bindings(child, position);
                (found.some.contains(variable) && !found.every.contains(variable))
                    .then(|| unbinding_alternative(child, position, variable))
                    .flatten()
            })
    })
}

/// The variables of an equation's result (the built positions of `body`, and `ensures`) that some
/// combination of the alternatives of the or-patterns of its left side binds and another does
/// not, each with the part of the result that uses it and an alternative that does not bind it;
/// `None` when there is none.
fn unequally_bound_result_variables<'t>(
    body: &'t Term,
    ensures: &Term,
) -> Option<Vec<(&'static str, String, &'t Term)>> {
    let found = bindings(body, TermPosition::BODY);
    let partial = found
        .some
        .difference(&found.every)
        .cloned()
        .collect::<BTreeSet<_>>();
    if partial.is_empty() {
        return None;
    }
    let mut in_right = BTreeSet::new();
    compute_unbound(body, TermPosition::BODY, &BTreeSet::new(), &mut in_right);
    let mut in_ensures = BTreeSet::new();
    compute_unbound(
        ensures,
        TermPosition::CONDITION,
        &BTreeSet::new(),
        &mut in_ensures,
    );
    let unbound = partial
        .into_iter()
        .filter_map(|variable| {
            let side = if in_right.contains(&variable) {
                "right side"
            } else if in_ensures.contains(&variable) {
                "ensures"
            } else {
                return None;
            };
            let alternative = unbinding_alternative(body, TermPosition::BODY, &variable)?;
            Some((side, variable, alternative))
        })
        .collect::<Vec<_>>();
    (!unbound.is_empty()).then_some(unbound)
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
/// has two operands that are not predicates, one of which may denote several values.
fn built_conjunction_over_a_connective(body: &Term) -> bool {
    let mut pending = vec![(body, TermPosition::BODY)];
    // Invariant: each step takes a subterm of `body` and pushes only its strict subterms.
    while let Some((term, position)) = pending.pop() {
        if position.rhs && !position.lhs && is_binary(term, InternalLabel::And) {
            let terms = chain_operands(term, false)
                .into_iter()
                .filter(|operand| !is_predicate(operand))
                .collect::<Vec<_>>();
            if terms.len() >= 2 && !terms.iter().all(|operand| at_most_one_value(operand)) {
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

/// Whether the term `term`, at a built position, denotes at most one value: its only connectives
/// are `#Bottom` and conjunctions with at least one term operand, whose term operands denote at
/// most one value, beside any predicate conjuncts (module documentation).
fn at_most_one_value(term: &Term) -> bool {
    crate::stack::guarded(|| {
        if is_binary(term, InternalLabel::And) {
            let terms = chain_operands(term, false)
                .into_iter()
                .filter(|operand| !is_predicate(operand))
                .collect::<Vec<_>>();
            return !terms.is_empty() && terms.into_iter().all(at_most_one_value);
        }
        if is_ml_connective(term) {
            return matches!(
                term.unannotated(),
                Term::Apply { label, .. } if label.is(InternalLabel::Bottom)
            );
        }
        scoped_children(term, TermPosition::RHS)
            .into_iter()
            .all(|(child, _, _)| at_most_one_value(child))
    })
}
