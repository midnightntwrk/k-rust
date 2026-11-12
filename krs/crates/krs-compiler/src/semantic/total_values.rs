//! Each equation of a `total` function has a result with a value wherever it applies.
//!
//! `total` on a function `f` states that every application of `f` has a value. An equation
//! `f(p) = r requires c` states that `f(p)` is `r` wherever `p` matches and `c` holds. Where `r`
//! has no value there, the two statements contradict each other: the theory is inconsistent at
//! those arguments, and a reader that uses both (a prover, a solver summary) may conclude
//! anything. A missing equation is another matter, which the coverage lint reports: the theory
//! stays consistent and leaves a value unnamed.
//!
//! So a function declared `total` is checked: for each of its equations, the result has a value
//! wherever the equation applies, given that each function the result applies has one where its
//! own declaration says so. A result has a value where every construct it evaluates has one:
//!
//! - a partial construct ([`krs_ir_levels::definedness`]: a sort projection, a collection read
//!   KRS projects to its position's sort, a builtin operation outside the domain the catalog
//!   states, a `let` whose pattern may not match) needs each of its tests among the conjuncts of
//!   the equation's condition, or decided by the bounds those conjuncts state. The condition is
//!   read after the guarding pass, so a construct the condition itself evaluates counts as
//!   tested: the equation applies only where it has a value. An `if` block is two equations,
//!   whose conditions are its test and the test's negation, so its test guards its branches;
//!   `kequal::ite`, `&&` and `||` written as operations guard nothing, since each keeps the
//!   definedness of every operand;
//! - an application of a function must be of one declared `total`. A function KRS lifted out of
//!   the equation (a `k::matches!` over a projection) is no declaration of the author's, and is
//!   judged in place: its equations apply to the names the result applies it to, so each test
//!   the guarding pass stated in their conditions must be among the equation's conjuncts.
//!
//! The check is sound and incomplete: it never accepts a result that has no value at an argument
//! the equation applies to (given the callees' declarations), and it refuses results that have a
//! value everywhere by a fact it does not read (a range it does not compute, such as `1 << (b &
//! 7)`; a condition that applies a function; the element sort of a typed collection, which no
//! invariant establishes yet; what an `owise` equation knows from the equations before it).
//! Recursion is not judged: a recursive call is an application of a `total` function like any
//! other, so for a function in a call cycle the check shows totality given termination.
//!
//! A hooked function, one with an SMT hook, and one with no equation are not judged: nothing
//! here defines them. A simplification is no defining equation.

use std::collections::BTreeMap;

use krs_ir::{
    DomainFact, DomainTerm, InsertedNode, ProductionAttribute, SentenceKind, SourceRange,
    StableItemId,
};
use krs_ir_levels::definedness::{self, NotShown, Requirement, Sorts};
use krs_ir_levels::{
    IrTermKind, ListOperands, MapOperands, SemanticCondition, SemanticModule, SemanticProduction,
    SemanticRule, SemanticTerm,
};

use super::error::DescriptorLoweringError;
use crate::coverage::{display_name, sort_name};

/// What the author of a refused function may write instead.
const WAYS_OUT: &str = "Ways out: state the domain in the equation's condition (`#[k::requires(..)]`) and give the remaining arguments an equation (`#[k::equation(owise)]`); or use a form that has a value everywhere (`get_or` at the sort the collection holds, an `if` block whose test is the construct's); or declare the function `partial`";

/// The functions refused after the first that one error names.
const ALSO_LIMIT: usize = 8;

/// Refuses the first function declared `total` with an equation whose result is not shown to
/// have a value wherever the equation applies (the module documentation).
pub(super) fn check_total_values(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let judge = Judge::new(modules);
    let mut refused = Vec::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        if !crate::coverage::checked(production) {
            continue;
        }
        if let Some(finding) = judge.findings(production.id()).into_iter().next() {
            refused.push((production, finding));
        }
    }
    let Some((production, finding)) = refused.first() else {
        return Ok(());
    };
    let name = display_name(production.id());
    let also = if refused.len() > 1 {
        let others = refused[1..]
            .iter()
            .take(ALSO_LIMIT)
            .map(|(production, _)| format!("`{}`", display_name(production.id())))
            .collect::<Vec<_>>()
            .join(", ");
        match refused.len().saturating_sub(1 + ALSO_LIMIT) {
            0 => format!("; also not shown: {others}"),
            more => format!("; also not shown: {others} and {more} more"),
        }
    } else {
        String::new()
    };
    let reason = format!(
        "`{name}` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: {}. `total` and an equation whose result has no value contradict each other, and a proof that uses both may conclude anything. {WAYS_OUT}{also}",
        finding.what
    );
    Err(DescriptorLoweringError::TotalWithoutValue {
        item: Box::new(finding.equation.clone()),
        reason,
        range: finding.range.clone().map(Box::new),
    })
}

/// One construct or application of an equation's result that is not shown to have a value.
#[derive(Clone, Debug)]
pub(crate) struct Finding {
    /// The equation.
    pub(crate) equation: StableItemId,
    /// Where the construct or the application is written.
    pub(crate) range: Option<SourceRange>,
    /// Why it is not shown, as a clause of a message.
    pub(crate) what: String,
}

/// The judge of a theory's `total` functions.
pub(crate) struct Judge<'m> {
    sorts: Sorts,
    productions: BTreeMap<&'m StableItemId, &'m SemanticProduction>,
    equations: BTreeMap<&'m StableItemId, Vec<&'m SemanticRule>>,
}

impl<'m> Judge<'m> {
    /// The judge of `modules`, read after the guarding pass.
    pub(crate) fn new(modules: &'m [SemanticModule]) -> Self {
        let productions = modules
            .iter()
            .flat_map(SemanticModule::productions)
            .map(|production| (production.id(), production))
            .collect::<BTreeMap<_, _>>();
        let mut equations = BTreeMap::<_, Vec<_>>::new();
        for rule in modules.iter().flat_map(SemanticModule::rules) {
            if rule.kind() != SentenceKind::Equation || rule.simplification().is_some() {
                continue;
            }
            if let Some(head) = rule.body().and_then(|body| applied(body.from())) {
                equations.entry(head).or_default().push(rule);
            }
        }
        Self {
            sorts: Sorts::of_modules(modules),
            productions,
            equations,
        }
    }

    /// Each construct and application in the results of `function`'s equations that is not shown
    /// to have a value where its equation applies, in equation order.
    pub(crate) fn findings(&self, function: &StableItemId) -> Vec<Finding> {
        let mut findings = Vec::new();
        for rule in self.equations.get(function).into_iter().flatten() {
            let Some(body) = rule.body() else { continue };
            let facts = condition_conjuncts(rule);
            let mut found = Vec::new();
            self.result(body.to(), &facts, &mut found);
            findings.extend(found.into_iter().map(|(range, what)| Finding {
                equation: rule.id().clone(),
                range: range.or_else(|| rule.origin().origin().exact_authored_range()),
                what,
            }));
        }
        findings
    }

    /// Adds to `found` what `result`, built where `facts` hold, is not shown to have a value by.
    fn result(
        &self,
        result: &SemanticTerm,
        facts: &[&SemanticTerm],
        found: &mut Vec<(Option<SourceRange>, String)>,
    ) {
        let mut constructs = Vec::<(Option<SourceRange>, String, Vec<String>)>::new();
        let mut untested = Vec::new();
        let mut calls = Vec::new();
        let mut lifted = Vec::new();
        definedness::without_value(
            result,
            facts,
            &self.sorts,
            &mut |construct, why| {
                let range = authored(construct);
                let (name, need) = match why {
                    NotShown::Requirement(requirement) => {
                        (construct_name(requirement), needed(requirement))
                    }
                    NotShown::Untested(text) => {
                        untested.push((range, operation_name(construct), text));
                        return;
                    }
                };
                // The needs of one construct are one finding, each stated once: a name a `let`
                // binds alone is read in its value's place, so its value is read again there.
                match constructs.iter_mut().find(|(known, known_name, _)| {
                    range.is_some() && *known == range && *known_name == name
                }) {
                    Some((_, _, needs)) => {
                        if !needs.contains(&need) {
                            needs.push(need);
                        }
                    }
                    None => constructs.push((range, name, vec![need])),
                }
            },
            &mut |application, callee| {
                let Some(production) = self.productions.get(callee) else {
                    return;
                };
                let has = |test: fn(&krs_ir_levels::SemanticProductionAttribute) -> bool| {
                    production.attributes().iter().any(test)
                };
                if !has(|attribute| matches!(attribute, ProductionAttribute::Function { .. }))
                    || has(|attribute| matches!(attribute, ProductionAttribute::Total { .. }))
                {
                    return;
                }
                if callee.is_generated_production() {
                    lifted.push(application.clone());
                } else {
                    calls.push((authored(application), display_name(callee)));
                }
            },
        );
        for (range, name, needs) in constructs {
            let needs = match needs.as_slice() {
                [need] => need.clone(),
                needs => needs
                    .iter()
                    .enumerate()
                    .map(|(index, need)| format!("({}) {need}", index + 1))
                    .collect::<Vec<_>>()
                    .join(", and "),
            };
            found.push((
                range,
                format!(
                    "this {name} has a value only where {needs}, which the equation's condition does not state"
                ),
            ));
        }
        for (range, name, text) in untested {
            found.push((
                range,
                format!(
                    "this {name} is partial, and KRS has no test of its domain that a condition could state ({text})"
                ),
            ));
        }
        for (range, callee) in calls {
            found.push((
                range,
                format!(
                    "it applies `{callee}`, which is not declared `total`, so the application has no value where `{callee}` has none"
                ),
            ));
        }
        for application in lifted {
            self.lifted(&application, facts, found);
        }
    }

    /// Judges `application`, of a function KRS lifted out of the sentence that applies it, in
    /// place: the function has a value where one of its equations applies and that equation's
    /// result has one. Its equations are over the names the sentence applies it to, and their
    /// conditions are each other's complement but for the tests the guarding pass stated before
    /// them, so an equation applies wherever those tests hold.
    fn lifted(
        &self,
        application: &SemanticTerm,
        facts: &[&SemanticTerm],
        found: &mut Vec<(Option<SourceRange>, String)>,
    ) {
        let unread = |found: &mut Vec<(Option<SourceRange>, String)>| {
            found.push((
                authored(application),
                "this test or block is evaluated by a function KRS generates for it, which the check does not read here".to_owned(),
            ));
        };
        let Some(callee) = applied(application) else {
            return;
        };
        let Some(equations) = self.equations.get(callee) else {
            unread(found);
            return;
        };
        let mut stated = Vec::<Option<SourceRange>>::new();
        for equation in equations {
            let Some(body) = equation.body() else {
                unread(found);
                return;
            };
            // The equation is over the names the application passes.
            if !definedness::same(body.from(), application) {
                unread(found);
                return;
            }
            let conjuncts = condition_conjuncts(equation);
            for test in conjuncts
                .iter()
                .filter(|conjunct| is_definedness_test(conjunct))
            {
                if facts.iter().any(|fact| definedness::same(fact, test)) {
                    continue;
                }
                let range = test
                    .origin()
                    .origin()
                    .inserted()
                    .and_then(|(_, anchor)| anchor.cloned())
                    .or_else(|| authored(application));
                if !stated.contains(&range) {
                    stated.push(range.clone());
                    found.push((
                        range,
                        "this construct of a `k::matches!` test is partial (a projection, a read KRS projects, or an operation outside its domain), and the equation's condition does not test it (for a projection `k::project!(S, t)`: `k::is!(S, t)`)".to_owned(),
                    ));
                }
            }
            let mut inside = facts.to_vec();
            inside.extend(conjuncts);
            self.result(body.to(), &inside, found);
        }
    }
}

/// The declared production `term` applies at its root.
fn applied(term: &SemanticTerm) -> Option<&StableItemId> {
    match term.kind() {
        IrTermKind::Application {
            application: krs_ir::ApplicationRef::Declared(head),
            ..
        } => Some(head),
        _ => None,
    }
}

/// The conjuncts of `rule`'s Bool condition, which all hold where the rule applies.
fn condition_conjuncts(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    fn conjuncts<'t>(term: &'t SemanticTerm, output: &mut Vec<&'t SemanticTerm>) {
        match definedness::conjunction(term) {
            Some((left, right, _)) => {
                conjuncts(left, output);
                conjuncts(right, output);
            }
            None => output.push(term),
        }
    }
    let mut all = Vec::new();
    if let Some(SemanticCondition::Bool(condition)) = rule.requires() {
        conjuncts(condition.term(), &mut all);
    }
    all
}

/// Whether `term` is a test the guarding pass stated.
fn is_definedness_test(term: &SemanticTerm) -> bool {
    matches!(
        term.origin().origin().inserted(),
        Some((InsertedNode::DefinednessTest, _))
    )
}

fn authored(term: &SemanticTerm) -> Option<SourceRange> {
    term.origin().origin().exact_authored_range()
}

/// What the construct of `requirement` is, for a message.
fn construct_name(requirement: &Requirement<'_>) -> String {
    match requirement {
        Requirement::Sort { read: true, .. } | Requirement::Domain { .. } => {
            operation_name(match requirement {
                Requirement::Sort { operand, .. } => operand,
                Requirement::Domain { construct, .. } => construct,
                Requirement::Match { value, .. } => value,
            })
        }
        Requirement::Sort { read: false, .. } => "projection".to_owned(),
        Requirement::Match { .. } => "`let` statement".to_owned(),
    }
}

/// What the operation at `term`'s root is, for a message.
fn operation_name(term: &SemanticTerm) -> String {
    match term.kind() {
        IrTermKind::Map(operands) => match &**operands {
            MapOperands::Get { .. } => "lookup".to_owned(),
            MapOperands::GetOrDefault { .. } => "`get_or` read".to_owned(),
            operands => format!("map operation `{}`", operands.operation()),
        },
        IrTermKind::List(operands) => match &**operands {
            ListOperands::Get { .. } => "list read".to_owned(),
            operands => format!(
                "`{}`",
                krs_ir::CollectionApplication::spec(operands.operation()).description
            ),
        },
        IrTermKind::Set(operands) => format!(
            "`{}`",
            krs_ir::CollectionApplication::spec(operands.operation()).description
        ),
        IrTermKind::Application {
            application: krs_ir::ApplicationRef::Builtin(operation),
            ..
        } => {
            let spec = operation.spec();
            format!("`{}::{}`", spec.rust_module, spec.rust_name)
        }
        _ => "operation".to_owned(),
    }
}

/// The fact `requirement` needs, in words, with the test that states it.
fn needed(requirement: &Requirement<'_>) -> String {
    match requirement {
        Requirement::Sort {
            sort, read: false, ..
        } => {
            let sort = sort_name(sort);
            format!("its operand has sort `{sort}` (`k::is!({sort}, ..)` of the operand)")
        }
        Requirement::Sort {
            sort, read: true, ..
        } => {
            let sort = sort_name(sort);
            format!(
                "the element read has sort `{sort}`, which KRS projects the read to and no invariant of a typed collection establishes yet (`k::is!({sort}, ..)` of the read)"
            )
        }
        Requirement::Domain {
            fact: DomainFact::KeyOf { .. },
            construct,
        } if matches!(construct.kind(), IrTermKind::Map(_)) => {
            "the key is a key of the map (`contains_key`)".to_owned()
        }
        Requirement::Domain { fact, .. } => fact_in_words(*fact),
        Requirement::Match { .. } => {
            "its pattern matches its value (`k::matches!(value, pattern)`)".to_owned()
        }
    }
}

fn fact_in_words(fact: DomainFact) -> String {
    match fact {
        DomainFact::Less(left, right) => {
            format!("{} < {}", term_in_words(left), term_in_words(right))
        }
        DomainFact::AtMost(left, right) => {
            format!("{} <= {}", term_in_words(left), term_in_words(right))
        }
        DomainFact::Equal(left, right) => {
            format!("{} == {}", term_in_words(left), term_in_words(right))
        }
        DomainFact::NonZero(operand) => format!("{} != 0", term_in_words(operand)),
        DomainFact::KeyOf { key, map } => format!(
            "{} is a key of {} (`contains_key`)",
            operand_in_words(key),
            operand_in_words(map)
        ),
        DomainFact::Disjoint { left, right } => format!(
            "{} and {} share no element",
            operand_in_words(left),
            operand_in_words(right)
        ),
        DomainFact::OneOf { operand, texts } => format!(
            "{} is one of {}",
            operand_in_words(operand),
            texts
                .iter()
                .map(|text| format!("{text:?}"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn term_in_words(term: DomainTerm) -> String {
    match term {
        DomainTerm::Operand(position) => operand_in_words(position),
        DomainTerm::Int(value) => value.to_string(),
        DomainTerm::Length(position) => format!("the length of {}", operand_in_words(position)),
        DomainTerm::Sum(left, right) => {
            format!("{} + {}", term_in_words(*left), term_in_words(*right))
        }
        DomainTerm::Difference(left, right) => {
            format!("{} - {}", term_in_words(*left), term_in_words(*right))
        }
    }
}

fn operand_in_words(position: usize) -> String {
    format!("operand {}", position + 1)
}
