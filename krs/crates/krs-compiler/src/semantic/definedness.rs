//! Each partial construct a condition evaluates, tested before it (NT-37).
//!
//! A sentence's condition holds where it is true, so where a construct it evaluates has no value
//! (a sort projection or a read KRS projects, where the operand has another sort; a lookup of a
//! key the map lacks; a list read outside the list; a `let` statement whose pattern does not
//! match) the condition does not hold and the sentence does not apply. Every route must read it
//! so, and a backend that evaluates the condition reaches the construct before it knows: Java K's
//! LLVM backend aborts there. So KRS states the construct's test in the condition ahead of it,
//! joined with `andThenBool`, which every route evaluates first: `requires l[0]` over a list of
//! `KItem`s is `requires 0 <Int size(L) andThenBool isBool(L [ 0 ]) andThenBool {L [ 0 ]}:>Bool`.
//! Where the tests hold the construct has its value and the condition is the author's; where one
//! fails the condition is `false`, as the author's would have no value.
//!
//! A test stands where `false` and "no value" mean the same: at a conjunct of the condition's
//! top-level conjunction, or in the body of a `#let` that stands there
//! ([`krs_ir_levels::definedness`]), before the conjunct whose evaluation reaches the construct;
//! a test an earlier conjunct of its chain already states (the author's `m.contains_key(k) &&
//! m[k] > 0`, a key's guard) is not stated again. A test that would read a name a `#let` binds
//! below that place cannot stand there, and the construct is refused at its place.
//!
//! Results are not tested: where a construct in a result has no value, the sentence applied and
//! its result has none, which every route ends on; testing it would make another sentence apply
//! in its place. The pass runs after every check that reads the author's conditions (coverage,
//! overlap), which read them as written.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, NodeOrigin, SemanticId, SemanticIdKind,
    SourceMapKey,
};
use krs_ir_levels::definedness::{self, Requirement, Sorts};
use krs_ir_levels::{
    IrTermKind, SemanticCondition, SemanticModule, SemanticRule, SemanticRuleCondition,
    SemanticSortRef, SemanticTerm, SemanticVariable,
};

use super::catalog::semantic_is_subsort;
use super::error::DescriptorLoweringError;

/// `modules` with each rule's condition holding the test of every partial construct it
/// evaluates before the construct (the module documentation).
pub(super) fn guard_conditions(
    modules: Vec<SemanticModule>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<Vec<SemanticModule>, DescriptorLoweringError> {
    let Some(k_item) = modules
        .iter()
        .flat_map(SemanticModule::sorts)
        .map(krs_ir_levels::SemanticSort::id)
        .find(|id| {
            id.item_name() == "KItem"
                && id.package().k_namespace() == "KRS-FRAMEWORK"
                && id.package().cargo_name() == "krs"
                && id.package().cargo_source() == "framework"
        })
        .cloned()
        .map(SemanticSortRef::Declared)
    else {
        return Ok(modules);
    };
    let is_subsort = |candidate: &SemanticSortRef, expected: &SemanticSortRef| {
        expected == &k_item || semantic_is_subsort(candidate, expected, sort_parents)
    };
    let sorts = Sorts {
        k_item: &k_item,
        is_subsort: &is_subsort,
    };
    modules
        .into_iter()
        .map(|module| {
            if !module.rules().iter().any(needs_guards) {
                return Ok(module);
            }
            let rules = module
                .rules()
                .iter()
                .map(|rule| guard_rule(rule, &sorts))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(module.with_rules(rules))
        })
        .collect()
}

/// Whether `rule` has a Bool condition, which may evaluate a partial construct.
fn needs_guards(rule: &SemanticRule) -> bool {
    matches!(rule.requires(), Some(SemanticCondition::Bool(_)))
}

fn guard_rule(
    rule: &SemanticRule,
    sorts: &Sorts<'_>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let Some(SemanticCondition::Bool(condition)) = rule.requires() else {
        return Ok(rule.clone());
    };
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
    };
    let term = guards.guard_point(condition.term(), &[])?;
    if guards.tests == 0 {
        return Ok(rule.clone());
    }
    let mut variables = rule.variables().to_vec();
    variables.extend(guards.wildcards);
    rule.clone()
        .with_variables(variables)
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
fn wildcard_ordinal(id: &SemanticId) -> Option<usize> {
    (id.kind() == SemanticIdKind::Wildcard)
        .then(|| id.as_str().rsplit('_').next()?.parse().ok())
        .flatten()
}

/// The tests one condition gains.
struct Guards<'r, 's, 'a> {
    rule: &'r SemanticRule,
    sorts: &'s Sorts<'a>,
    /// The number of tests made, which keys each test's nodes apart.
    tests: usize,
    wildcard_offset: usize,
    wildcards: Vec<SemanticVariable>,
}

impl Guards<'_, '_, '_> {
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
        let mut needed = Vec::new();
        let rebuilt = if let IrTermKind::Let {
            pattern,
            value,
            body,
            binds,
        } = term.kind()
            && *body.sort() == SemanticSortRef::Builtin(BuiltinSort::Bool)
        {
            self.collect(value, true, established, &BTreeSet::new(), &mut needed)?;
            self.require(term, true, established, &BTreeSet::new(), &mut needed)?;
            let tests = self.tests_for(&needed);
            let mut inside = established.to_vec();
            inside.extend(tests.iter().cloned());
            let body = self.guard_point(body, &inside)?;
            let rebuilt = term.with_kind(IrTermKind::Let {
                pattern: pattern.clone(),
                value: value.clone(),
                body: Box::new(body),
                binds: binds.clone(),
            });
            return Ok(conjoin(tests, rebuilt));
        } else {
            self.collect(term, true, established, &BTreeSet::new(), &mut needed)?;
            term.clone()
        };
        let tests = self.tests_for(&needed);
        Ok(conjoin(tests, rebuilt))
    }

    /// Adds to `needed` the requirements of every construct `term` evaluates, operands first,
    /// that `established` does not state; `bound` are the names the `#let`s inside the conjunct
    /// around `term` bind, which a test before the conjunct cannot read.
    fn collect<'t>(
        &mut self,
        term: &'t SemanticTerm,
        projected: bool,
        established: &[SemanticTerm],
        bound: &BTreeSet<SemanticId>,
        needed: &mut Vec<Requirement<'t>>,
    ) -> Result<(), DescriptorLoweringError> {
        match term.kind() {
            IrTermKind::Let {
                value, body, binds, ..
            } => {
                self.collect(value, true, established, bound, needed)?;
                let mut inner = bound.clone();
                inner.extend(binds.iter().cloned());
                self.collect(body, true, established, &inner, needed)?;
            }
            // The pattern is matched, not evaluated.
            IrTermKind::Matches { subject, .. } => {
                self.collect(subject, true, established, bound, needed)?;
            }
            _ => {
                let generated = matches!(
                    term.kind(),
                    IrTermKind::Application {
                        application: ApplicationRef::Generated(_),
                        ..
                    }
                );
                for child in term.children() {
                    self.collect(child, !generated, established, bound, needed)?;
                }
            }
        }
        self.require(term, projected, established, bound, needed)
    }

    /// Adds the requirements of the construct at `term`'s root to `needed`.
    fn require<'t>(
        &mut self,
        term: &'t SemanticTerm,
        projected: bool,
        established: &[SemanticTerm],
        bound: &BTreeSet<SemanticId>,
        needed: &mut Vec<Requirement<'t>>,
    ) -> Result<(), DescriptorLoweringError> {
        for requirement in definedness::requirements(term, projected, self.sorts) {
            if established
                .iter()
                .any(|fact| requirement.holds_by(fact, self.sorts))
            {
                continue;
            }
            if definedness::reads_any(&requirement, bound) {
                return Err(self.refusal(term, &requirement));
            }
            let test = requirement.test(
                self.sorts,
                &mut NodeOrigin::clone,
                &mut NodeOrigin::clone,
                &mut |_| SemanticId::wildcard(0),
            );
            if needed
                .iter()
                .any(|earlier| earlier.holds_by(&test, self.sorts))
            {
                continue;
            }
            needed.push(requirement);
        }
        Ok(())
    }

    /// The tests of `needed`, in order, each under source-map keys of its own.
    fn tests_for(&mut self, needed: &[Requirement<'_>]) -> Vec<SemanticTerm> {
        let sorts = self.sorts;
        let offset = self.wildcard_offset;
        let mut tests = Vec::with_capacity(needed.len());
        for requirement in needed {
            let ordinal = self.tests;
            self.tests += 1;
            let mut fresh_nodes = 0_usize;
            let wildcards = &mut self.wildcards;
            tests.push(requirement.test(
                sorts,
                &mut |origin| suffixed(origin, &format!("~defined-{ordinal}")),
                &mut |origin| {
                    fresh_nodes += 1;
                    suffixed(origin, &format!("~defined-{ordinal}-{fresh_nodes}"))
                },
                &mut |sort| {
                    let id = SemanticId::wildcard(offset + wildcards.len());
                    wildcards.push(SemanticVariable::new(id.clone(), sort.clone()));
                    id
                },
            ));
        }
        tests
    }

    /// The refusal of a construct whose test would read a name a `#let` binds inside the
    /// conjunct that evaluates it.
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
                reason: "in a condition, this projection (or this read, which KRS projects to its position's sort) denotes a value only where its operand has that sort, and the condition holds only where it does, which KRS tests before the conjunct that evaluates it; the operand reads a name a `let` inside that conjunct binds, which the test cannot read: project a name the sentence binds, or write the block's `let` outside the conjunct".to_owned(),
                range,
            },
            Requirement::Match { .. } => DescriptorLoweringError::InvalidLet {
                item,
                reason: "in a condition, this `let` statement denotes a value only where its pattern matches, which KRS tests before the conjunct that evaluates it; its value reads a name an earlier `let` inside that conjunct binds, which the test cannot read: match a name the sentence binds, or write the statement where the condition's top-level conjunction holds it".to_owned(),
                range,
            },
            Requirement::Key { .. } | Requirement::Below { .. } | Requirement::Above { .. } => {
                DescriptorLoweringError::invalid_term(
                    self.rule.id(),
                    "in a condition, this lookup or index denotes a value only where its key or index is in the collection, which KRS tests before the conjunct that evaluates it; the collection or the key reads a name a `let` inside that conjunct binds, which the test cannot read: read with names the sentence binds, or write the block's `let` outside the conjunct",
                )
                .within(self.rule.id(), range.as_deref())
            }
        }
    }
}

/// `tests andThenBool .. andThenBool term`.
fn conjoin(tests: Vec<SemanticTerm>, term: SemanticTerm) -> SemanticTerm {
    tests.into_iter().rev().fold(term, |conjunct, test| {
        let origin = suffixed(test.origin(), "~and");
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

/// `origin` under the source-map key extended by `suffix`, which no node of the sentence has.
fn suffixed(origin: &NodeOrigin, suffix: &str) -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new(format!("{}{suffix}", origin.key().as_str()))
            .expect("a source-map key extended by a separator-free suffix is a key"),
        origin.origin().clone(),
    )
}
