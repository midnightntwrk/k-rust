//! Each partial construct a condition evaluates, tested before it (NT-37).
//!
//! A sentence's condition holds where it is true, so where a construct it evaluates has no value
//! (a sort projection or a read KRS projects, where the operand has another sort; a builtin
//! operation outside the domain the catalog states for it, such as a lookup of a key the map
//! lacks, a list read outside the list or a division by zero; a `let` statement whose pattern
//! does not match) the condition does not hold and the sentence does not apply. Every route must
//! read it so, and a backend that evaluates the condition reaches the construct before it knows:
//! Java K's LLVM backend aborts there. So KRS states the construct's test in the condition ahead
//! of it, joined with `andThenBool`, which every route evaluates first: `requires l[0]` over a
//! list of `KItem`s is `requires 0 <Int size(L) andThenBool isBool(L [ 0 ]) andThenBool {L [ 0
//! ]}:>Bool`. Where the tests hold the construct has its value and the condition is the
//! author's; where one fails the condition is `false`, as the author's would have no value. A
//! `k::matches!` over a projection is then stated on the projection's operand, which its test
//! makes the projection's value: `k::matches!(k::project!(Int, a), 1)` is `isInt(A) andThenBool
//! ( 1 :=K A )`, with no projection as `:=K`'s operand. A
//! user function's application is not tested: its equations state where it has a value, and
//! guarding a partial one is the author's.
//!
//! A step or an `unless` of a `k::patterns!` chain is such a sentence: the part is the set of
//! states that match its body and at which its condition is true, so a state where a construct
//! of the condition has no value is not in the set. A step does not match there, and an
//! `unless` does not exclude there; a construct below `!` is no exception, since the negation of
//! no value is no value. The pass therefore reads a module's rules and its pattern parts as one
//! sequence ([`SemanticModule::sentences`]), the one the validation of its result reads.
//!
//! A test stands where `false` and "no value" mean the same: at a conjunct of the condition's
//! top-level conjunction, or in the body of a `#let` that stands there
//! ([`krs_ir_levels::definedness`]), before the conjunct whose evaluation reaches the construct;
//! a test an earlier conjunct of its chain already states (the author's `m.contains_key(k) &&
//! m[k] > 0`, a key's guard, a bound that implies it) is not stated again. A construct in the
//! body of a `let x = v;` inside the conjunct is tested with `v` in `x`'s place; one whose test
//! would read a name another `#let` binds below that place cannot be tested there, and is
//! refused at its place.
//!
//! Results are not tested: where a construct in a result has no value, the sentence applied and
//! its result has none, which every route ends on; testing it would make another sentence apply
//! in its place. The pass runs after every check that reads the author's conditions (coverage,
//! overlap), which read them as written, and after the lifting of a claim's and a static clause's
//! blocks and tests into functions, whose equations it guards like any other.

use std::collections::BTreeSet;

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, InsertedNode, SemanticId, SemanticIdKind,
};
use krs_ir_levels::definedness::{self, Requirement, Sorts};
use krs_ir_levels::{
    IrTermKind, SemanticCondition, SemanticModule, SemanticRule, SemanticRuleCondition,
    SemanticSortRef, SemanticTerm, SemanticVariable,
};

use super::error::DescriptorLoweringError;
use super::origin::inserted_copy;

/// `modules` with the condition of each rule and of each `k::patterns!` part holding the test
/// of every partial construct it evaluates before the construct (the module documentation).
pub(super) fn guard_conditions(
    modules: Vec<SemanticModule>,
) -> Result<Vec<SemanticModule>, DescriptorLoweringError> {
    let sorts = Sorts::of_modules(&modules);
    modules
        .into_iter()
        .map(|module| {
            if !module.sentences().any(needs_guards) {
                return Ok(module);
            }
            let sentences = module
                .sentences()
                .map(|rule| guard_rule(rule, &sorts))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(module.with_sentences(sentences))
        })
        .collect()
}

/// The `warning[krs::analysis::dead-guard]` diagnostics of a theory's guarded modules: each
/// partial construct whose test the author wrote below `!` or `||` in the conjunct that
/// evaluates it ([`definedness::dead_tests`]).
#[must_use]
pub fn guard_warnings(modules: &[SemanticModule]) -> Vec<Diagnostic> {
    let sorts = Sorts::of_modules(modules);
    let mut warnings = Vec::new();
    for rule in modules.iter().flat_map(SemanticModule::sentences) {
        for dead in definedness::dead_tests(rule, &sorts) {
            let name = &dead.name;
            let mut warning = Diagnostic::error(
                codes::analysis::DEAD_GUARD,
                format!(
                    "this {name} is tested below `!` or `||` in the conjunct that evaluates it, which does not protect it: `&&`, `||` and `!` keep the definedness of every operand, evaluated or not, so the condition has no value where the {name} has none, and KRS tests the {name} before the conjunct, so the sentence applies only where it has a value; to apply where it has none, write that case as a sentence of its own (`#[k::requires(!k::is!(S, t))]`), and to say what the condition means, test before the conjunct (`k::is!(S, t) && ..`)",
                ),
                dead.construct
                    .origin()
                    .exact_authored_range()
                    .map_or(Location::None, Location::Source),
            );
            warning.severity = Severity::Warning;
            warnings.push(warning);
        }
    }
    warnings
}

/// Whether `rule` has a Bool condition, which may evaluate a partial construct, or an `ensures`
/// that holds a `k::matches!` over a projection ([`restated_ensures`]).
fn needs_guards(rule: &SemanticRule) -> bool {
    matches!(rule.requires(), Some(SemanticCondition::Bool(_))) || restated_ensures(rule).is_some()
}

/// The `ensures` of `rule`, where it is Bool and holds a `k::matches!` over a projection.
///
/// An `ensures` is not tested: one with no value is `ensures false`. A `k::matches!` over a
/// projection there is stated on the projection's operand as in a condition, after the
/// projection's test, which is `false` exactly where the projection has no value, so the
/// `ensures` means what it did, with no projection as `:=K`'s operand.
fn restated_ensures(rule: &SemanticRule) -> Option<&SemanticRuleCondition> {
    match rule.ensures() {
        Some(SemanticCondition::Bool(condition))
            if definedness::matched_on_operands(condition.term()) != *condition.term() =>
        {
            Some(condition)
        }
        _ => None,
    }
}

pub(crate) fn guard_rule(
    rule: &SemanticRule,
    sorts: &Sorts,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let mut guards = Guards {
        rule,
        sorts,
        tests: 0,
        wildcard_offset: rule
            .variables()
            .iter()
            .filter_map(|variable| wildcard_ordinal(variable.id()))
            .max()
            .map_or(0, |ordinal| ordinal + 1),
        wildcards: Vec::new(),
        restated: false,
    };
    let requires = match rule.requires() {
        Some(SemanticCondition::Bool(condition)) => {
            Some((condition, guards.guard_point(condition.term(), &[])?))
        }
        _ => None,
    };
    // The `ensures` is evaluated where the condition holds: its conjuncts are established.
    let established = requires
        .as_ref()
        .map(|(_, term)| conjuncts(term))
        .unwrap_or_default();
    let ensures = restated_ensures(rule)
        .map(|condition| {
            guards
                .guard_point(condition.term(), &established)
                .map(|term| (condition, term))
        })
        .transpose()?;
    if guards.tests == 0 && !guards.restated {
        return Ok(rule.clone());
    }
    let mut variables = rule.variables().to_vec();
    variables.extend(guards.wildcards);
    let mut guarded = rule.clone().with_variables(variables);
    if let Some((condition, term)) = ensures {
        guarded = guarded.with_ensures(Some(SemanticCondition::Bool(SemanticRuleCondition::new(
            condition.origin().clone(),
            term,
        ))));
    }
    let Some((condition, term)) = requires else {
        return Ok(guarded);
    };
    guarded
        .with_requires(Some(SemanticCondition::Bool(SemanticRuleCondition::new(
            condition.origin().clone(),
            term,
        ))))
        .map_err(|error| DescriptorLoweringError::InvalidSemanticTheory {
            error,
            range: None,
            item: Some(Box::new(rule.id().clone())),
        })
}

/// The ordinal of a wildcard's identity.
pub(super) fn wildcard_ordinal(id: &SemanticId) -> Option<usize> {
    (id.kind() == SemanticIdKind::Wildcard)
        .then(|| id.as_str().rsplit('_').next()?.parse().ok())
        .flatten()
}

/// The tests one condition gains.
struct Guards<'r, 's> {
    rule: &'r SemanticRule,
    sorts: &'s Sorts,
    /// The number of tests made, which keys each test's nodes apart.
    tests: usize,
    wildcard_offset: usize,
    wildcards: Vec<SemanticVariable>,
    /// Whether a `k::matches!` over a projection was stated on its operand.
    restated: bool,
}

impl Guards<'_, '_> {
    /// `term`, a Bool standing where `false` means "does not hold", with the tests its constructs
    /// need before them; `established` are the earlier conjuncts of its chain, which hold where
    /// it is evaluated.
    fn guard_point(
        &mut self,
        term: &SemanticTerm,
        established: &[SemanticTerm],
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        if let Some((left, right, ordered)) = definedness::conjunction(term) {
            let left = self.guard_point(left, established)?;
            let mut after = established.to_vec();
            if ordered {
                after.extend(conjuncts(&left));
            }
            let right = self.guard_point(right, &after)?;
            let IrTermKind::Application {
                application,
                instance,
                head_instance_fixed,
                ..
            } = term.kind()
            else {
                unreachable!("a conjunction is an application");
            };
            return Ok(term.with_kind(IrTermKind::Application {
                application: application.clone(),
                arguments: vec![left, right],
                instance: instance.clone(),
                head_instance_fixed: *head_instance_fixed,
            }));
        }
        let mut tests = Vec::new();
        if let IrTermKind::Let {
            pattern,
            value,
            body,
            binds,
        } = term.kind()
            && *body.sort() == SemanticSortRef::Builtin(BuiltinSort::Bool)
        {
            self.collect(value, true, established, &BTreeSet::new(), &mut tests)?;
            self.require(term, term, true, established, &BTreeSet::new(), &mut tests)?;
            let mut inside = established.to_vec();
            inside.extend(tests.iter().cloned());
            let body = self.guard_point(body, &inside)?;
            // The value's projections are tested before it, as a conjunct's are.
            let matched = definedness::matched_on_operands(value);
            self.restated |= matched != **value;
            let rebuilt = term.with_kind(IrTermKind::Let {
                pattern: pattern.clone(),
                value: Box::new(matched),
                body: Box::new(body),
                binds: binds.clone(),
            });
            return Ok(conjoin(tests, rebuilt));
        }
        self.collect(term, true, established, &BTreeSet::new(), &mut tests)?;
        // Each projection `term` evaluates is tested before it, so a `k::matches!` over one is
        // stated on its operand ([`definedness::matched_on_operands`]).
        let matched = definedness::matched_on_operands(term);
        if matched != *term {
            self.restated = true;
        }
        Ok(conjoin(tests, matched))
    }

    /// Adds to `tests` the test of every construct `term` evaluates, operands first, that
    /// `established` and the tests before it do not state; `bound` are the names the `#let`s
    /// inside the conjunct around `term` bind, which a test before the conjunct cannot read. A
    /// `let` of one name every value matches is read with its value in the name's place.
    fn collect(
        &mut self,
        term: &SemanticTerm,
        projected: bool,
        established: &[SemanticTerm],
        bound: &BTreeSet<SemanticId>,
        tests: &mut Vec<SemanticTerm>,
    ) -> Result<(), DescriptorLoweringError> {
        if let Some((name, value, body)) = definedness::name_binding(term, self.sorts) {
            self.collect(value, true, established, bound, tests)?;
            let body = definedness::substituted(body, name, value);
            return self.collect(&body, true, established, bound, tests);
        }
        match term.kind() {
            IrTermKind::Let {
                value, body, binds, ..
            } => {
                self.collect(value, true, established, bound, tests)?;
                let mut inner = bound.clone();
                inner.extend(binds.iter().cloned());
                self.collect(body, true, established, &inner, tests)?;
            }
            // The pattern is matched, not evaluated.
            IrTermKind::Matches { subject, .. } => {
                self.collect(subject, true, established, bound, tests)?;
            }
            _ => {
                let generated = definedness::is_generated(term);
                for child in term.children() {
                    self.collect(child, !generated, established, bound, tests)?;
                }
            }
        }
        self.require(term, term, projected, established, bound, tests)
    }

    /// Adds the tests of the construct at `term`'s root to `tests`; `at` locates a refusal.
    fn require(
        &mut self,
        term: &SemanticTerm,
        at: &SemanticTerm,
        projected: bool,
        established: &[SemanticTerm],
        bound: &BTreeSet<SemanticId>,
        tests: &mut Vec<SemanticTerm>,
    ) -> Result<(), DescriptorLoweringError> {
        for requirement in definedness::requirements(term, projected, self.sorts) {
            let known = established.iter().chain(tests.iter()).collect::<Vec<_>>();
            if requirement.established_by(&known, self.sorts) {
                continue;
            }
            if definedness::reads_any(&requirement, bound) {
                return Err(self.refusal(at, &requirement));
            }
            let anchor = term.origin().origin().exact_authored_range();
            let test = self.test(&requirement, anchor.as_ref());
            tests.push(test);
        }
        Ok(())
    }

    /// The test of `requirement`, under source-map keys of its own, each
    /// node marked inserted and anchored at the construct it tests.
    fn test(
        &mut self,
        requirement: &Requirement<'_>,
        anchor: Option<&krs_ir::SourceRange>,
    ) -> SemanticTerm {
        let ordinal = self.tests;
        self.tests += 1;
        let offset = self.wildcard_offset;
        let mut fresh_nodes = 0_usize;
        let wildcards = &mut self.wildcards;
        requirement.test(
            self.sorts,
            &mut |origin| {
                inserted_copy(
                    origin,
                    &format!("~defined-{ordinal}"),
                    InsertedNode::DefinednessTest,
                    anchor,
                )
            },
            &mut |origin| {
                fresh_nodes += 1;
                inserted_copy(
                    origin,
                    &format!("~defined-{ordinal}-{fresh_nodes}"),
                    InsertedNode::DefinednessTest,
                    anchor,
                )
            },
            &mut |sort, typed| {
                let id = definedness::test_name(typed, offset + wildcards.len());
                wildcards.push(SemanticVariable::new(id.clone(), sort.clone()));
                id
            },
        )
    }

    /// The refusal of a construct whose test would read a name a `#let` binds inside the
    /// conjunct that evaluates it, other than a name every value matches.
    fn refusal(
        &self,
        term: &SemanticTerm,
        requirement: &Requirement<'_>,
    ) -> DescriptorLoweringError {
        let item = Box::new(self.rule.id().clone());
        let range = term
            .origin()
            .origin()
            .exact_authored_range()
            .or_else(|| {
                requirement
                    .subject()
                    .origin()
                    .origin()
                    .exact_authored_range()
            })
            .map(Box::new);
        match requirement {
            Requirement::Sort { .. } => DescriptorLoweringError::InvalidSortTest {
                item,
                reason: "in a condition, this projection (or this read, which KRS projects to its position's sort) denotes a value only where its operand has that sort, and the condition holds only where it does, which KRS tests before the conjunct that evaluates it; the operand reads a name a `let` inside that conjunct binds by a pattern other than one name, which the test cannot read: project a name the sentence binds, bind the name alone (`let x = ..;`), or write the block's `let` outside the conjunct".to_owned(),
                range,
            },
            Requirement::Match { .. } => DescriptorLoweringError::InvalidLet {
                item,
                reason: "in a condition, this `let` statement denotes a value only where its pattern matches, which KRS tests before the conjunct that evaluates it; its value reads a name an earlier `let` inside that conjunct binds by a pattern other than one name, which the test cannot read: match a name the sentence binds, or write the statement where the condition's top-level conjunction holds it".to_owned(),
                range,
            },
            Requirement::Domain { .. } => DescriptorLoweringError::invalid_term(
                self.rule.id(),
                "in a condition, this operation denotes a value only on the domain KRS states for it (a key of the map, an index of the list, a divisor other than zero, ..), which KRS tests before the conjunct that evaluates it; an operand reads a name a `let` inside that conjunct binds by a pattern other than one name, which the test cannot read: read with names the sentence binds, bind the name alone (`let x = ..;`), or write the block's `let` outside the conjunct",
            )
            .within(self.rule.id(), range.as_deref()),
        }
    }
}

/// `tests andThenBool .. andThenBool term`. Each `andThenBool` joins a test
/// KRS states, so it is inserted with the test, anchored as the test is.
fn conjoin(tests: Vec<SemanticTerm>, term: SemanticTerm) -> SemanticTerm {
    tests.into_iter().rev().fold(term, |conjunct, test| {
        let anchor = test
            .origin()
            .origin()
            .inserted()
            .and_then(|(_, anchor)| anchor.cloned());
        let origin = inserted_copy(
            test.origin(),
            "~and",
            InsertedNode::DefinednessTest,
            anchor.as_ref(),
        );
        SemanticTerm::application(
            origin,
            SemanticSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Builtin(BuiltinOperation::BoolAndThen),
            vec![test, conjunct],
        )
    })
}

/// The conjuncts of `term`'s top-level conjunction.
fn conjuncts(term: &SemanticTerm) -> Vec<SemanticTerm> {
    match definedness::conjunction(term) {
        Some((left, right, _)) => {
            let mut all = conjuncts(left);
            all.extend(conjuncts(right));
            all
        }
        None => vec![term.clone()],
    }
}

#[cfg(test)]
mod tests;
