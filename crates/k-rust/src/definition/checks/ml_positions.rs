//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Matching-logic constructs at positions that state no meaning k-rust reads, refused at compile
//! with [`DiagnosticCode::MlConstructPosition`], located at the sentence, for the Rust target only
//! (an LLVM target's consumer reads the emitted KORE on its own terms).
//!
//! The check runs twice: among the definition checks, on the sentences as written, and as the
//! pipeline stage `check matching-logic positions`, on the sentences as the backend reads them,
//! macros and aliases expanded at their uses and the conjunctions passes add to conditions chosen.
//! A macro or alias rule is an abbreviation, not an axiom: what its body states is judged where it
//! is used, in the context of the use, and a refusal there says that the construct was written in
//! a macro or alias body.
//!
//! # Equations with no model, and conjunctions with no reading
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
//!   be any of the alternatives, so its alternatives may bind different variables.
//! - A simplification whose left side is a term and whose right side is `#Top`, or a predicate
//!   other than `#Bottom`. A simplification equates a term with a term, or a predicate with a
//!   predicate: such a right side denotes every value of its sort or none, so the lemma states
//!   that the application, which has at most one value, is every value, an axiom with no model.
//!   A lemma whose left side is a predicate (`#Ceil(f(X)) => #Top`) states a predicate's truth
//!   and is unaffected; so is `#Bottom`, which states that the application is undefined.
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
//! # Positions
//!
//! One walk over each rule, claim, context and context alias carries the context of the subterm
//! it judges; the context changes only at a rewrite, at a condition's root, at a non-ML symbol on
//! a condition's spine, and at a predicate atom:
//!
//! - Matched, Built and Shared: a body position (`TermPosition`, from `scoped_children`) that is
//!   matched (a rewrite's left side), built (its right side) or both (outside every rewrite). A
//!   local function's pattern and body are the argument and the value of the function it is
//!   lowered to, so they are judged as that function's equation.
//! - Spine: a condition's root (`requires`, `ensures`, both sides of a predicate
//!   simplification) and the operands of the connectives on it, where a pattern is read as a
//!   predicate and a Bool term as `t = true`. A predicate conjoined to a term at a body position
//!   (`X #And {X #Equals 1}`) is a condition on that term and is judged as on a spine.
//! - BoolLeaf: below a non-ML symbol on a spine, where a Bool value is required.
//! - PredicateOperand: inside an operand of `#Equals`, `#Ceil` or `#Floor`, a term position.
//!   (`#In` is no construct of the K term language: `kast.md` declares no production for it, so
//!   a K sentence holds none; KORE `\in` input is the backend's to read.)
//!
//! A sentence's kind decides the body positions: an equation (function equation, anywhere rule,
//! simplification) states one value of an application, a rewrite rule or a context a step, a
//! claim the pattern every path reaches. Casts compute nothing and are read through.
//!
//! What is refused, by context, each because no route reads it or the backend misreads it:
//!
//! - Spine: `#as` (a condition is matched against nothing, so the alias names nothing); a local
//!   function in a claim (a claim's local function is lowered to nothing its proof applies);
//!   an `#Equals` whose operands are not both terms or both predicates (a predicate at sort Bool
//!   is all of Bool or nothing, and a connective over terms denotes a set of values). Every other
//!   connective and atom is a predicate there.
//! - BoolLeaf: every connective and predicate atom (`notBool {X #Equals 3}`,
//!   `(X #Or 5) <Int 3`): a predicate where a Bool value is required. `#fun`, `#let` and the
//!   matches `:=K`, `:/=K` are Bool-valued terms.
//! - PredicateOperand: every connective, predicate atom and `#as`
//!   (`{X #Equals (1 #Or 2)}`, `#Ceil({X #Equals 1})`), with one exception: below `#Ceil` a
//!   conjunction of connective-free terms, whose definedness `⌈t1 ∧ t2⌉ = ⌈t1⌉ ∧ t1 = t2` the
//!   backend decides. Below `#Floor` such a conjunction is refused: a term conjunction is at most
//!   one value, and `⌊t⌋` holds only where `t` is every value of its sort, which needs the
//!   complement of the conjunction that no route decides. An `#Equals` of two predicates is their
//!   iff at any depth, and its operands are judged as on a spine.
//! - Matched: `#Not`, `#Implies`, `#Iff`, a quantifier, `#Top`, `#Bottom`, and a predicate alone
//!   (each denotes a set of values that is not one term); in an equation, a predicate conjoined to
//!   a term (an equation's left side is matched against the application's arguments, where no
//!   condition is read), any or-pattern of a simplification, and an or-pattern of a function or
//!   anywhere equation that is not at the root of an argument of the application it defines (the
//!   backend matches equation or-patterns only there; a symbol distributes over `#Or`, so
//!   `g(1 #Or 2)` is `g(1) #Or g(2)`, and `(1 #Or 2) #as Y` is `(1 #as Y) #Or (2 #as Y)`),
//!   including one at the root whose alternatives are of a sort below the argument's, which sort
//!   injection places below an injection or, for an argument of sort `K`, a k-sequence (judged
//!   once the sorts are known, in the pipeline stage). Or-patterns, conjunctions of terms,
//!   predicates conjoined to a term in a rewrite rule or a claim, and `#as` are matched.
//! - Shared, in a rewrite rule, a context or a claim: `#Not`, `#Implies`, `#Iff` and a quantifier.
//!   An or-pattern, `#Top` (any value), `#Bottom` (no value) and a predicate alone (a condition on
//!   the match) are read; in a rewrite rule, `#Top`, `#Bottom` and a predicate only where each is
//!   itself what the sides share, an argument of a symbol that holds the rewrite in another
//!   argument: the right side reuses a shared term by a name the left side gives it, so as part
//!   of a larger shared term, or as an item of a k-sequence that holds the rewrite (which splices
//!   the sequence), it stands below a symbol of the matched term, where no rule reads it. In an
//!   equation a shared position is matched.
//! - Built: `#Not`, `#Implies`, `#Iff`, a quantifier, `#Top` and a predicate alone; `#Bottom` in a
//!   claim's right side; in an equation, an or-pattern with two alternatives other than `#Bottom`
//!   (which denotes no value, so `X #Or #Bottom` is `X`) and one that conjoins no predicate (an
//!   application has at most one value; guarded alternatives,
//!   `({X #Equals 1} #And 10) #Or (#Not({X #Equals 1}) #And 20)`, denote at most one where their
//!   guards exclude each other); a local function in a claim. `#Bottom` elsewhere (the step or the
//!   application is undefined), `#Or` in a rewrite rule or a claim, a term conjoined with
//!   predicates, and in a claim's right side, the pattern every path must reach, `P #as V`,
//!   which names the reached term matching `P`, are read; that alias only where
//!   `lower term conjunctions` writes it `P #And {P #Equals V}` (`P` a term with at most one value
//!   that performs no effect), since no other compiled form keeps `P`: the rewrite checks refuse
//!   the others, and the pipeline stage those whose pattern applies an effectful production, for
//!   every target.
//! - Everywhere: a quantifier over a set variable (`#Exists @T . ..`): a quantifier binds an
//!   element variable; a set variable is bound only by a fixpoint.
//!
//! Where an existing check already refuses a construct cleanly, the walk leaves it to that check:
//! `#as` where a rule builds its result (`InvalidRewrite`), a claim's right-side alias that is not
//! lowered (the rewrite checks, `MlConstructPosition`), and a local function in a pattern
//! (`InvalidFunctionPattern`).
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;

use super::rhs_variables::compute_unbound;
use super::term_position::{Scope, TermPosition, scoped_children};
use super::{Sentence, is_anonymous};
use crate::definition::{AttributeKey, LabelHead, ProductionCatalog, match_rule_label};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::binding::quantifier;
use crate::kast::{InternalLabel, Label, Term};
use crate::kompile::ml_constructs::{
    chain_operands, is_connective_free_term, is_ml_connective, is_predicate, read_through_casts,
};
use crate::provenance::GeneratingPass;

/// Whether the or-pattern `argument`, the root of argument `index` of an application of
/// `label` in an equation's left side, is placed below an injection or a k-sequence when it is
/// placed at the argument's sort: an oracle of the sorts, which the definition checks do not
/// have and the pipeline stage does.
pub(super) type InjectedOrPattern<'a> = dyn Fn(&Label, usize, &Term) -> bool + 'a;

/// The [`DiagnosticCode::MlConstructPosition`] refusals of `sentences` (module documentation).
/// `injected` decides the or-patterns an injection places below a symbol; without it they are
/// not judged.
pub(super) fn check_ml_construct_positions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    injected: Option<&InjectedOrPattern<'_>>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        diagnostics.extend(equation_diagnostics(sentence, productions));
        diagnostics.extend(position_diagnostics(sentence, productions, injected));
    }
    diagnostics
}

/// The refusal of an alias `P #as V` in the right side of a claim's rewrite that the stage
/// `lower term conjunctions` does not lower (`ml_constructs::lowers_claim_alias`).
pub(super) fn unlowered_claim_alias(sentence: &Sentence) -> Diagnostic {
    Diagnostic::error(
        DiagnosticCode::MlConstructPosition,
        "#as where the claim builds its result (its right-hand side): `P #as V` there denotes \
         `P #And V`, which a claim's right side keeps only as `P #And {P #Equals V}`, and that \
         form denotes the alias only where P is a term with at most one value whose evaluation \
         performs no effect (no matching-logic connective, alias or rewrite in it, and no \
         application of an effectful production); this alias's pattern is not such a term, so \
         no compiled form of the claim keeps it; write the alias around each alternative \
         ((A #as ?Y) #Or (B #as ?Y)), or name the reached term with an existential variable \
         and state the condition in the ensures",
        sentence,
    )
}

/// The refusals of the aliases in the right sides of the rewrites of the claim `sentence` that
/// `lower term conjunctions` does not lower, `is_effectful` deciding which applications may
/// perform an effect: one refusal per claim.
pub(super) fn unlowered_claim_alias_diagnostics(
    sentence: &Sentence,
    is_effectful: &dyn Fn(&Label) -> bool,
) -> Vec<Diagnostic> {
    let Sentence::Claim { body, .. } = sentence else {
        return Vec::new();
    };
    let mut pending = vec![(body, TermPosition::BODY)];
    // Invariant: each step takes a subterm of `body` and pushes only its strict subterms.
    while let Some((term, position)) = pending.pop() {
        if position.rhs
            && !position.lhs
            && matches!(term.unannotated(), Term::As { .. })
            && !crate::kompile::ml_constructs::lowers_claim_alias(term, is_effectful)
        {
            return vec![unlowered_claim_alias(sentence)];
        }
        pending.extend(
            scoped_children(term, position)
                .into_iter()
                .map(|(child, position, _)| (child, position)),
        );
    }
    Vec::new()
}

/// The refusals of the first three kinds of the module documentation: equations and
/// simplifications with no model, and built conjunctions with no reading.
fn equation_diagnostics(
    sentence: &Sentence,
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let Sentence::Rule {
        body,
        ensures,
        attributes,
        ..
    } = sentence
    else {
        return diagnostics;
    };
    if is_macro_like(sentence, productions) {
        return diagnostics;
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
    } else if (attributes.has(AttributeKey::Anywhere) || is_function_rule(sentence, productions))
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
        if position.rhs && !position.lhs && conjunction_without_reading(term) {
            return true;
        }
        pending.extend(
            scoped_children(term, position)
                .into_iter()
                .map(|(child, position, _)| (child, position)),
        );
    }
    false
}

/// Whether `term` is a conjunction with two operands that are not predicates, one of which may
/// denote several values: at a built position it has no reading.
fn conjunction_without_reading(term: &Term) -> bool {
    if !is_binary(term, InternalLabel::And) {
        return false;
    }
    let terms = chain_operands(term, false)
        .into_iter()
        .filter(|operand| !is_predicate(operand))
        .collect::<Vec<_>>();
    terms.len() >= 2 && !terms.iter().all(|operand| at_most_one_value(operand))
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

// ---------------------------------------------------------------- the position walk

/// What a sentence states, which decides what each of its positions may hold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    /// A rewrite rule (also a context, and the heating and cooling rules made of contexts):
    /// its left side matches a configuration, its right side denotes the states it steps to.
    Rewrite,
    /// An equation of a function production, or of a local function's generated function: its
    /// left side matches the application, its right side is the application's one value.
    Function,
    /// An anywhere rule: an equation of the symbol at its left side's root.
    Anywhere,
    /// A simplification whose left side is a term: an equation between two terms.
    Simplification,
    /// A simplification whose left side is a predicate: an equivalence of two predicates.
    PredicateSimplification,
    /// A claim: its left side matches the states it starts from, its right side is the pattern
    /// every path must reach.
    Claim,
}

impl Kind {
    fn of(sentence: &Sentence, productions: &ProductionCatalog<'_>) -> Option<Self> {
        Some(match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => {
                if is_macro_like(sentence, productions) {
                    return None;
                }
                if attributes.has(AttributeKey::Simplification) {
                    if let Term::Rewrite { left, .. } = body.unannotated()
                        && is_ml_connective(read_through_casts(left))
                    {
                        Kind::PredicateSimplification
                    } else {
                        Kind::Simplification
                    }
                } else if attributes.has(AttributeKey::Anywhere) {
                    Kind::Anywhere
                } else if is_function_rule(sentence, productions) {
                    Kind::Function
                } else {
                    Kind::Rewrite
                }
            }
            Sentence::Claim { .. } => Kind::Claim,
            Sentence::Context { .. } | Sentence::ContextAlias { .. } => Kind::Rewrite,
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => return None,
        })
    }

    /// Whether the sentence is an equation of an application, which has at most one value.
    fn is_equation(self) -> bool {
        matches!(self, Kind::Function | Kind::Anywhere | Kind::Simplification)
    }

    fn name(self) -> &'static str {
        match self {
            Kind::Rewrite => "rewrite rule",
            Kind::Function => "function equation",
            Kind::Anywhere => "anywhere rule",
            Kind::Simplification => "simplification",
            Kind::PredicateSimplification => "predicate simplification",
            Kind::Claim => "claim",
        }
    }
}

/// The context of a subterm: what the sentence states about the values at its position.
#[derive(Clone, Copy)]
enum Context {
    /// A position of a sentence body: matched (`lhs` only), built (`rhs` only), or shared by
    /// the sides of its rewrites (both).
    Body(TermPosition),
    /// The spine of a condition: its root and the operands of the matching-logic connectives
    /// on it. A pattern there is read as a predicate, a term as a Bool value that holds.
    Spine,
    /// Below a Bool symbol of a condition: a term position, where a Bool value is required.
    BoolLeaf,
    /// Inside an operand of `#Equals`, `#Ceil` or `#Floor` (`atom`): a term position, where a
    /// connective is an operation on sets of values.
    PredicateOperand { atom: Atom },
}

/// The predicate atom whose operand a [`Context::PredicateOperand`] is inside.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Atom {
    Equals,
    Ceil,
    Floor,
}

impl Context {
    fn matched(self) -> bool {
        matches!(self, Context::Body(position) if position.lhs && !position.rhs)
    }

    fn built(self) -> bool {
        matches!(self, Context::Body(position) if position.rhs && !position.lhs)
    }

    fn shared(self) -> bool {
        matches!(self, Context::Body(position) if position.lhs && position.rhs)
    }

    fn in_condition(self) -> bool {
        matches!(
            self,
            Context::Spine | Context::BoolLeaf | Context::PredicateOperand { .. }
        )
    }

    /// Where a construct stands, for a message.
    fn describe(self, kind: Kind) -> String {
        let kind = kind.name();
        match self {
            Context::Body(position) => match (position.lhs, position.rhs) {
                (true, false) => format!("where the {kind} matches (its left-hand side)"),
                (false, true) => {
                    format!("where the {kind} builds its result (its right-hand side)")
                }
                _ => format!("at a position the sides of the {kind} share"),
            },
            Context::Spine => format!("in a condition of the {kind}"),
            Context::BoolLeaf => {
                format!(
                    "below a Bool symbol in a condition of the {kind}, where a Bool value is required"
                )
            }
            Context::PredicateOperand { .. } => {
                format!(
                    "inside an operand of #Equals, #Ceil or #Floor in the {kind}, which is a term"
                )
            }
        }
    }
}

/// The shape of an operand of an `#Equals`, read through casts, which compute nothing: a term
/// denotes one value, a predicate all of its sort or nothing, and a connective over terms
/// (`(X ==Int 1) #Or (X ==Int 2)`, `1 #Or 2`) the set of values its connectives build.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OperandShape {
    Term,
    Predicate,
    Connective,
}

fn operand_shape(term: &Term) -> OperandShape {
    let term = read_through_casts(term);
    if !is_ml_connective(term) {
        OperandShape::Term
    } else if is_predicate(term) {
        OperandShape::Predicate
    } else {
        OperandShape::Connective
    }
}

/// The position refusals of one sentence: the walk of the module documentation, over its body
/// and conditions.
fn position_diagnostics(
    sentence: &Sentence,
    productions: &ProductionCatalog<'_>,
    injected: Option<&InjectedOrPattern<'_>>,
) -> Vec<Diagnostic> {
    let Some(kind) = Kind::of(sentence, productions) else {
        return Vec::new();
    };
    let mut walk = Walk {
        kind,
        sentence,
        diagnostics: Vec::new(),
        expanded: false,
        injected,
        alone: true,
        under_root: None,
    };
    match sentence {
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
        } => {
            walk.body(body);
            walk.term(requires, Context::Spine, false);
            walk.term(ensures, Context::Spine, false);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            walk.body(body);
            walk.term(requires, Context::Spine, false);
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => {}
    }
    let mut diagnostics = walk.diagnostics;
    diagnostics.sort();
    diagnostics.dedup();
    diagnostics
}

/// One sentence's walk: its kind, and the refusals found so far.
struct Walk<'s, 'o> {
    kind: Kind,
    sentence: &'s Sentence,
    diagnostics: Vec<Diagnostic>,
    /// Whether the node being judged was written in the body of a macro or an alias, and placed
    /// here by its expansion at this use (its origin is macro expansion).
    expanded: bool,
    /// The sort oracle of or-patterns at argument roots ([`InjectedOrPattern`]).
    injected: Option<&'o InjectedOrPattern<'o>>,
    /// Set for the next node judged: whether, at a position the sides of a rewrite rule share,
    /// the node is itself what the sides share, so that it is named alone where the right side
    /// reuses it: it is an argument of a symbol that holds a rewrite in another argument, or it
    /// stands below a matching-logic connective. As part of a larger term the sides share (its
    /// parent holds no rewrite) or as an item of a k-sequence (whose rewrite splices the
    /// sequence), the larger term or the sequence is what the sides share. Reset at each node.
    alone: bool,
    /// Set for the next node judged: the connective (`#as`, `#And`) at the root of an argument
    /// of an equation's application, directly below which the node stands. Reset at each node.
    under_root: Option<&'static str>,
}

impl Walk<'_, '_> {
    fn refuse(&mut self, message: String) {
        self.diagnostics.push(Diagnostic::error(
            DiagnosticCode::MlConstructPosition,
            message,
            self.sentence,
        ));
    }

    /// A refusal of `construct` where `context` places it, with the reason and the remedy.
    fn refuse_at(&mut self, construct: &str, context: Context, reason: &str) {
        let at = context.describe(self.kind);
        let origin = self.origin();
        self.refuse(format!("{construct}{origin} {at}: {reason}"));
    }

    /// Where the judged node was written, when a macro or alias expansion placed it.
    fn origin(&self) -> &'static str {
        if self.expanded {
            " (written in the body of a macro or alias used here)"
        } else {
            ""
        }
    }

    /// A sentence body. An equation's left side is the application it defines, whose arguments
    /// are the roots where an or-pattern may stand.
    fn body(&mut self, body: &Term) {
        if matches!(self.kind, Kind::Function | Kind::Anywhere) {
            // A function equation written with the configuration (`[[ f(..) => r ]] <cells>`)
            // holds its rewrite in the first argument; the cells beside it are matched against
            // the configuration.
            let (equation, configuration) = match body.unannotated() {
                Term::Apply { label, arguments }
                    if label.is(InternalLabel::WithConfig) && !arguments.is_empty() =>
                {
                    (&arguments[0], &arguments[1..])
                }
                Term::Apply { .. }
                | Term::Annotated { .. }
                | Term::Rewrite { .. }
                | Term::As { .. }
                | Term::Sequence(_)
                | Term::InjectedLabel(_)
                | Term::Variable { .. }
                | Term::Token { .. } => (body, &[][..]),
            };
            if let Term::Rewrite { left, right } = equation.unannotated() {
                self.application_pattern(left);
                self.term(right, Context::Body(TermPosition::RHS), false);
                for cells in configuration {
                    self.term(cells, Context::Body(TermPosition::BODY), false);
                }
                return;
            }
        }
        if self.kind == Kind::PredicateSimplification
            && let Term::Rewrite { left, right } = body.unannotated()
        {
            self.term(left, Context::Spine, false);
            self.term(right, Context::Spine, false);
            return;
        }
        if self.kind == Kind::Simplification
            && let Term::Rewrite { left, right } = body.unannotated()
        {
            self.term(left, Context::Body(TermPosition::LHS), false);
            // A right side that denotes every value or none is refused with the equation
            // refusals.
            if !denotes_every_value_or_none(right) {
                self.term(right, Context::Body(TermPosition::RHS), false);
            }
            return;
        }
        self.term(body, Context::Body(TermPosition::BODY), false);
    }

    /// The left side of an equation of an application: each argument of the application is an
    /// argument root.
    fn application_pattern(&mut self, pattern: &Term) {
        match read_through_casts(pattern) {
            Term::Apply { label, arguments }
                if !is_ml_connective(pattern) && !is_local_function(label) =>
            {
                for (index, argument) in arguments.iter().enumerate() {
                    if is_binary(read_through_casts(argument), InternalLabel::Or)
                        && self
                            .injected
                            .is_some_and(|injected| injected(label, index, argument))
                    {
                        self.refuse_at(
                            "#Or",
                            Context::Body(TermPosition::LHS),
                            "an or-pattern at the root of an argument whose alternatives are of \
                             a sort below the argument's is placed there by an injection (for an \
                             argument of sort K, as the item of a k-sequence), so it stands below \
                             that symbol, where an equation reads no or-pattern (a symbol \
                             distributes over #Or); write one equation per alternative, or give \
                             the alternatives the argument's sort",
                        );
                        continue;
                    }
                    self.term(argument, Context::Body(TermPosition::LHS), true);
                }
            }
            Term::Apply { .. }
            | Term::Annotated { .. }
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::InjectedLabel(_)
            | Term::Variable { .. }
            | Term::Token { .. } => self.term(pattern, Context::Body(TermPosition::LHS), false),
        }
    }

    /// `term` in `context`. `root`: the term is at the root of an argument of the application an
    /// equation defines, or an alternative of an or-pattern there.
    fn term(&mut self, term: &Term, context: Context, root: bool) {
        let expanded = term
            .metadata()
            .and_then(|metadata| metadata.origin.as_ref())
            .is_some_and(|origin| origin.pass == GeneratingPass::MacroExpansion);
        let enclosing = std::mem::replace(&mut self.expanded, expanded);
        crate::stack::guarded(|| self.node(read_through_casts(term), context, root));
        self.expanded = enclosing;
    }

    fn node(&mut self, term: &Term, context: Context, root: bool) {
        let alone = std::mem::replace(&mut self.alone, true);
        let under_root = self.under_root.take();
        if let Some(quantifier) = quantifier(term) {
            return self.quantifier(term, quantifier.binder, quantifier.body, context);
        }
        match term {
            Term::As { pattern, .. } => self.alias(term, pattern, context, root),
            Term::Apply { label, .. } if is_local_function(label) => {
                self.local_function(term, context)
            }
            Term::Apply { label, arguments } if is_match(label) && arguments.len() == 2 => {
                // The pattern is matched as the argument of the generated function; the matched
                // value is evaluated where the match stands.
                let kind = std::mem::replace(&mut self.kind, Kind::Function);
                self.term(&arguments[0], Context::Body(TermPosition::LHS), true);
                self.kind = kind;
                let inner = match context {
                    Context::Spine | Context::BoolLeaf => Context::BoolLeaf,
                    Context::PredicateOperand { .. } | Context::Body(_) => context,
                };
                self.term(&arguments[1], inner, false);
            }
            Term::Apply { label, arguments } if is_ml_connective(term) => self.connective(
                term,
                label,
                arguments,
                context,
                Place {
                    root,
                    under_root,
                    alone,
                },
            ),
            Term::Rewrite { .. }
            | Term::Apply { .. }
            | Term::Sequence(_)
            | Term::InjectedLabel(_)
            | Term::Variable { .. }
            | Term::Token { .. }
            | Term::Annotated { .. } => {
                let inner = match context {
                    Context::Spine | Context::BoolLeaf => Some(Context::BoolLeaf),
                    Context::PredicateOperand { atom } => Some(Context::PredicateOperand { atom }),
                    Context::Body(_) => None,
                };
                let position = match context {
                    Context::Body(position) => position,
                    Context::Spine | Context::BoolLeaf | Context::PredicateOperand { .. } => {
                        TermPosition::CONDITION
                    }
                };
                // A child is what the sides share alone where this term holds the rewrite in
                // another of its arguments; a k-sequence's rewrite splices the whole sequence.
                let children_alone = match term {
                    Term::Sequence(_) => false,
                    Term::Apply { .. } => holds_rewrite(term),
                    Term::Rewrite { .. }
                    | Term::As { .. }
                    | Term::InjectedLabel(_)
                    | Term::Variable { .. }
                    | Term::Token { .. }
                    | Term::Annotated { .. } => true,
                };
                for (child, position, _) in scoped_children(term, position) {
                    self.alone = children_alone;
                    self.term(child, inner.unwrap_or(Context::Body(position)), false);
                }
            }
        }
    }

    fn quantifier(&mut self, term: &Term, binder: &Term, body: &Term, context: Context) {
        let Term::Apply { label, .. } = term.unannotated() else {
            unreachable!("a quantifier is an application")
        };
        let label = label.name.clone();
        if let Term::Variable { name, .. } = read_through_casts(binder)
            && name.starts_with('@')
        {
            self.refuse(format!(
                "{label} binds the set variable {name}: a quantifier binds an element variable, \
                 which denotes one value, while a set variable denotes a set of values and is \
                 bound only by a fixpoint, so the quantifier is not a pattern; quantify an \
                 element variable (without @)"
            ));
        }
        if matches!(context, Context::Spine) {
            self.term(body, Context::Spine, false);
        } else {
            self.refuse_at(
                &label,
                context,
                "a quantifier is a predicate only over a predicate on a condition's spine; at a \
                 term position it denotes the union or the intersection of a set of values over \
                 every value of its variable, which no route reads; state the condition in the \
                 rule's requires, or use a fresh or existential variable (?X)",
            );
        }
    }

    fn alias(&mut self, term: &Term, pattern: &Term, context: Context, root: bool) {
        if context.in_condition() {
            return self.refuse_at(
                "#as",
                context,
                "a condition is matched against nothing, so #as names nothing; bind the \
                 variable in the left-hand side, or write the term itself",
            );
        }
        if context.built() {
            // An alias where a rule builds its result is refused by the rewrite checks
            // (InvalidRewrite); in a claim's right side, the pattern every path reaches, an
            // alias is read where it is lowered, and refused by them where it is not.
            if self.kind == Kind::Claim
                && crate::kompile::ml_constructs::lowers_claim_alias(term, &|_| false)
            {
                self.term(pattern, context, false);
            }
            return;
        }
        if root {
            self.under_root = Some("#as");
        }
        self.term(pattern, context, false);
    }

    fn local_function(&mut self, term: &Term, context: Context) {
        // In a pattern the rewrite checks refuse it (InvalidFunctionPattern).
        if matches!(context, Context::Body(position) if position.lhs) {
            return;
        }
        if self.kind == Kind::Claim {
            return self.refuse_at(
                "a local function (#fun or #let)",
                context,
                "a claim's local function is lowered to no function its proof can apply; define \
                 a function and apply it, or write its result",
            );
        }
        let position = match context {
            Context::Body(position) => position,
            Context::Spine | Context::BoolLeaf | Context::PredicateOperand { .. } => {
                TermPosition::CONDITION
            }
        };
        let kind = self.kind;
        for (child, child_position, scope) in scoped_children(term, position) {
            match scope {
                Scope::Lambda => {
                    // The local function's own equation: its pattern is the argument of the
                    // generated function, its body that function's value.
                    self.kind = Kind::Function;
                    if child_position.lhs && !child_position.rhs {
                        self.term(child, Context::Body(child_position), true);
                    } else if let Term::Rewrite { left, right } = child.unannotated() {
                        self.term(left, Context::Body(TermPosition::LHS), true);
                        self.term(right, Context::Body(TermPosition::RHS), false);
                    } else {
                        self.term(child, Context::Body(child_position), false);
                    }
                    self.kind = kind;
                }
                Scope::Enclosing => self.term(child, context, false),
            }
        }
    }

    fn connective(
        &mut self,
        term: &Term,
        label: &Label,
        arguments: &[Term],
        context: Context,
        place: Place,
    ) {
        let name = label.name.as_str();
        if label.is(InternalLabel::Or) {
            self.or(term, arguments, context, place)
        } else if label.is(InternalLabel::And) {
            self.and(term, arguments, context, place)
        } else if label.is(InternalLabel::Equals) {
            self.equals(arguments, context, place.alone)
        } else if label.is(InternalLabel::Ceil) || label.is(InternalLabel::Floor) {
            self.definedness(
                name,
                label.is(InternalLabel::Ceil),
                arguments,
                context,
                place.alone,
            )
        } else if label.is(InternalLabel::Top) || label.is(InternalLabel::Bottom) {
            self.constant(name, label.is(InternalLabel::Bottom), context, place.alone)
        } else {
            // #Not, #Implies, #Iff.
            if matches!(context, Context::Spine) {
                for argument in arguments {
                    self.term(argument, Context::Spine, false);
                }
            } else {
                self.refuse_connective(name, context);
            }
        }
    }

    /// A connective refused at a term position or below a Bool symbol.
    fn refuse_connective(&mut self, name: &str, context: Context) {
        let reason = match context {
            Context::BoolLeaf => {
                "a predicate where a Bool value is required: write it at the root of the \
                 condition, or write a Bool expression (notBool, andBool, orBool)"
            }
            Context::PredicateOperand { .. } => {
                "an operand of #Equals, #Ceil or #Floor is a term: a connective there denotes a \
                 set of values, which no route reads; compare or test the terms themselves"
            }
            Context::Body(_) | Context::Spine => {
                "the backend reads no such pattern where a term is required: it denotes a set of \
                 values other than the at most one value of a term; state the condition in the \
                 requires, or write the term"
            }
        };
        self.refuse_at(name, context, reason);
    }

    fn or(&mut self, term: &Term, arguments: &[Term], context: Context, place: Place) {
        let root = place.root;
        match context {
            Context::Spine => {
                for argument in arguments {
                    self.term(argument, Context::Spine, false);
                }
                return;
            }
            Context::BoolLeaf | Context::PredicateOperand { .. } => {
                return self.refuse_connective("#Or", context);
            }
            Context::Body(_) => {}
        }
        if context.matched() || context.shared() && self.kind.is_equation() {
            if self.kind == Kind::Simplification {
                return self.refuse_at(
                    "#Or",
                    context,
                    "a simplification's left-hand side is matched as one term; write one \
                     simplification per alternative",
                );
            }
            if matches!(self.kind, Kind::Function | Kind::Anywhere)
                && !root
                && let Some(connective) = place.under_root
            {
                return self.refuse_at(
                    "#Or",
                    context,
                    &format!(
                        "an or-pattern of an equation is matched only at the root of an argument \
                         of the application it defines, not below {connective} there; \
                         distribute the {} over the alternatives, which keeps them at the root{}",
                        if connective == "#as" {
                            "alias"
                        } else {
                            "conjunct"
                        },
                        if connective == "#as" {
                            " ((1 #Or 2) #as Y is (1 #as Y) #Or (2 #as Y))"
                        } else {
                            ""
                        }
                    ),
                );
            }
            if matches!(self.kind, Kind::Function | Kind::Anywhere) && !root {
                return self.refuse_at(
                    "#Or",
                    context,
                    "an or-pattern of an equation is matched only at the root of an argument of \
                     the application it defines; a symbol distributes over #Or \
                     (g(1 #Or 2) is g(1) #Or g(2)), so write the alternatives at the argument's \
                     root",
                );
            }
        } else if context.built() && self.kind.is_equation() && may_denote_several_values(term) {
            return self.refuse_at(
                "#Or",
                context,
                "an application has at most one value, while a disjunction of unguarded \
                 alternatives denotes each of them; guard every alternative with a predicate \
                 ({X #Equals 1} #And 10) so that at most one holds, or write one equation per \
                 alternative with a requires",
            );
        }
        for alternative in or_alternatives(term) {
            self.term(alternative, context, root);
        }
    }

    fn and(&mut self, term: &Term, arguments: &[Term], context: Context, place: Place) {
        match context {
            Context::Spine => {
                for argument in arguments {
                    self.term(argument, Context::Spine, false);
                }
            }
            Context::Body(_) => {
                if context.built() && self.kind != Kind::Claim && conjunction_without_reading(term)
                {
                    // Refused as a whole with the equation refusals.
                    return;
                }
                for operand in chain_operands(term, false) {
                    if !is_predicate(operand) {
                        if place.root {
                            self.under_root = Some("#And");
                        }
                        self.term(operand, context, false);
                    } else if context.built() || !self.kind.is_equation() {
                        self.term(operand, Context::Spine, false);
                    } else {
                        self.refuse_at(
                            "a predicate conjoined with #And",
                            context,
                            "an equation's left-hand side is matched against the application's \
                             arguments, where no condition is read; move the predicate to the \
                             requires",
                        );
                    }
                }
            }
            // ⌈t1 ∧ t2⌉ of terms each with at most one value is ⌈t1⌉ ∧ t1 = t2, which the
            // backend decides.
            Context::PredicateOperand { atom: Atom::Ceil }
                if chain_operands(term, false)
                    .iter()
                    .all(|operand| is_connective_free_term(operand)) => {}
            Context::PredicateOperand { atom: Atom::Floor } => self.refuse_at(
                "#And",
                context,
                "a conjunction of terms denotes at most one value, and #Floor of a pattern holds \
                 only where the pattern is every value of its sort; no route decides the \
                 complement of a term conjunction that this needs; state the condition as an \
                 equality of the terms ({X #Equals 1})",
            ),
            Context::BoolLeaf | Context::PredicateOperand { .. } => {
                self.refuse_connective("#And", context)
            }
        }
    }

    /// Whether a predicate, `#Top` or `#Bottom` at `context` is read: anywhere but at a position
    /// the sides of a rewrite rule share, and there only where it is what the sides share alone
    /// ([`Walk::alone`]), so that the right side reuses it by a name of its own. Otherwise the
    /// term the sides share holds it below a symbol of the matched term, where no rule reads a
    /// predicate.
    fn shared_alone(&self, context: Context, alone: bool) -> bool {
        alone
            || !context.shared()
            || self.kind != Kind::Rewrite
            || !matches!(self.sentence, Sentence::Rule { .. })
    }

    /// A predicate, `#Top` or `#Bottom` that is part of a larger term the sides of a rewrite
    /// rule share.
    fn refuse_shared_part(&mut self, name: &str, context: Context) {
        self.refuse_at(
            name,
            context,
            "a pattern that denotes every value or none is read at a shared position only as an \
             argument of a symbol that holds the rewrite in another argument, which the two sides \
             share alone; here it is part of a larger term the sides share, or an item of a \
             k-sequence that holds the rewrite, so it stands below a symbol of the matched term, \
             where no rule reads it; write a variable (_) for #Top, drop a rule that matches \
             #Bottom, or move a predicate to the requires",
        );
    }

    /// Whether a predicate stands where it is read as one: on a condition's spine, or at a
    /// position the sides of a rewrite rule, a context or a claim share, where it constrains the
    /// match.
    fn reads_predicate(&self, context: Context) -> bool {
        matches!(context, Context::Spine) || context.shared() && !self.kind.is_equation()
    }

    /// A predicate standing alone where a term is required.
    fn refuse_predicate(&mut self, name: &str, context: Context) {
        if matches!(context, Context::Body(_)) {
            self.refuse_at(
                name,
                context,
                "a predicate where a term is required: it denotes every value of its sort or \
                 none, never the one value of a term, and no route reads it there; conjoin it \
                 to a term (X #And {X #Equals 1}), or move it to the requires",
            );
        } else {
            self.refuse_connective(name, context);
        }
    }

    fn equals(&mut self, arguments: &[Term], context: Context, alone: bool) {
        if !self.reads_predicate(context) {
            return self.refuse_predicate("#Equals", context);
        }
        if !self.shared_alone(context, alone) {
            return self.refuse_shared_part("#Equals", context);
        }
        let shapes = arguments.iter().map(operand_shape).collect::<Vec<_>>();
        match shapes.as_slice() {
            [OperandShape::Term, OperandShape::Term] => {
                for argument in arguments {
                    self.term(
                        argument,
                        Context::PredicateOperand { atom: Atom::Equals },
                        false,
                    );
                }
            }
            [OperandShape::Predicate, OperandShape::Predicate] => {
                for argument in arguments {
                    self.term(argument, Context::Spine, false);
                }
            }
            _ => {
                let at = context.describe(self.kind);
                let origin = self.origin();
                self.refuse(format!(
                    "an #Equals{origin} {at} {}",
                    crate::kompile::ml_constructs::MIXED_EQUALITY_OPERANDS
                ));
            }
        }
    }

    fn definedness(
        &mut self,
        name: &str,
        ceil: bool,
        arguments: &[Term],
        context: Context,
        alone: bool,
    ) {
        if !self.reads_predicate(context) {
            return self.refuse_predicate(name, context);
        }
        if !self.shared_alone(context, alone) {
            return self.refuse_shared_part(name, context);
        }
        let atom = if ceil { Atom::Ceil } else { Atom::Floor };
        for argument in arguments {
            self.term(argument, Context::PredicateOperand { atom }, false);
        }
    }

    fn constant(&mut self, name: &str, bottom: bool, context: Context, alone: bool) {
        if self.reads_predicate(context) {
            if !self.shared_alone(context, alone) {
                self.refuse_shared_part(name, context);
            }
            return;
        }
        if context.built() && bottom {
            if self.kind != Kind::Claim {
                // A result that denotes no value: the step or the application is undefined.
                return;
            }
            return self.refuse_at(
                name,
                context,
                "a claim's right-hand side is the pattern every path must reach, and the proof \
                 route reads no #Bottom there; a claim that no state satisfies is stated by its \
                 requires (requires #Bottom), or by a right-hand side that no reached state \
                 matches",
            );
        }
        self.refuse_predicate(name, context);
    }
}

/// What the walk knows of a connective's place beyond its context.
#[derive(Clone, Copy)]
struct Place {
    /// At the root of an argument of the application an equation defines, or an alternative of
    /// an or-pattern there.
    root: bool,
    /// The connective at an argument root directly below which the node stands
    /// ([`Walk::under_root`]).
    under_root: Option<&'static str>,
    /// What the sides of a rewrite rule share alone ([`Walk::alone`]).
    alone: bool,
}

/// Whether the disjunction `term`, where an equation builds its result, may denote several
/// values: two or more of its alternatives are not `#Bottom`, which denotes no value (so
/// `X #Or #Bottom` is `X`), and one of them conjoins no predicate, which could exclude the others.
fn may_denote_several_values(term: &Term) -> bool {
    let values = or_alternatives(term)
        .into_iter()
        .filter(|alternative| !is_bottom(alternative))
        .collect::<Vec<_>>();
    values.len() > 1
        && !values.iter().all(|alternative| {
            chain_operands(alternative, false)
                .iter()
                .any(|operand| is_predicate(operand))
        })
}

/// Whether `term` holds a rewrite at any depth.
fn holds_rewrite(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |node| found |= matches!(node, Term::Rewrite { .. }));
    found
}

/// Whether `term`, read through casts, is `#Bottom`.
fn is_bottom(term: &Term) -> bool {
    matches!(
        read_through_casts(term),
        Term::Apply { label, .. } if label.is(InternalLabel::Bottom)
    )
}

/// Whether `rule` defines a macro or an alias, by its own attribute or, before the attributes of
/// macro productions are copied onto their rules, by the production its left side applies.
fn is_macro_like(rule: &Sentence, productions: &ProductionCatalog<'_>) -> bool {
    rule.attributes().has_any(&AttributeKey::MACRO_LIKE)
        || super::attributes::is_macro_rule(rule, productions)
}

/// Whether `label` is a match of a condition (`P :=K E`, `P :/=K E`): a local function whose
/// generated function is a predicate of `E` defined by one equation on the pattern `P`.
fn is_match(label: &crate::kast::Label) -> bool {
    label.is(InternalLabel::KEqualsK) || label.is(InternalLabel::KNotEqualsK)
}

/// Whether `label` is a local function (`#fun`, `#let`).
fn is_local_function(label: &crate::kast::Label) -> bool {
    label.is(InternalLabel::Fun2) || label.is(InternalLabel::Fun3) || label.is(InternalLabel::Let)
}
