//! Alpha-aware equality used by the cascade differential tests.

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    builtin::UnsupportedHookReason,
    rewrite::{
        AppliedRule, ExecutionLeaf, ExecutionResult, HaltReason, IndeterminateReason, Pattern,
        RemainderBranch, TrivialApplication,
    },
    rule::Predicate,
    simplify::SimplificationError,
    smt::{SmtError, TranslationError},
    substitution::{Substitution, substitute},
    term::{
        CollectionSymbols, ListDefinition, MapDefinition, Sort, Term, TermKind, Variable,
        names::VariableProvenance,
    },
    transition::{
        ExecutionIoState, ObservationEvent, PatternDigest, TransitionClass, TransitionId,
        TransitionObservation,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FreshClass {
    Rule,
    Equation,
    Existential,
    UnmarkedRewrite,
}

fn fresh_class(variable: &Variable) -> Option<FreshClass> {
    let name = variable.name.as_ref();
    let numeric_suffix = name.rsplit_once('!').is_some_and(|(_, suffix)| {
        !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
    });
    match variable.provenance() {
        Some(VariableProvenance::Rule) if numeric_suffix => Some(FreshClass::Rule),
        Some(VariableProvenance::Equation) if numeric_suffix => Some(FreshClass::Equation),
        Some(VariableProvenance::Existential) => Some(FreshClass::Existential),
        None if numeric_suffix => Some(FreshClass::UnmarkedRewrite),
        _ => None,
    }
}

#[derive(Clone, Default)]
struct AlphaContext {
    forward: BTreeMap<Variable, Variable>,
    reverse: BTreeMap<Variable, Variable>,
    choice_plan: Vec<usize>,
    choice_arities: Vec<usize>,
    choice_cursor: usize,
}

impl AlphaContext {
    fn with_choice_plan(choice_plan: Vec<usize>) -> Self {
        Self {
            choice_plan,
            ..Self::default()
        }
    }

    fn begin_choice(&mut self) -> (usize, usize) {
        let index = self.choice_cursor;
        self.choice_cursor += 1;
        self.choice_arities.push(0);
        (index, self.choice_plan.get(index).copied().unwrap_or(0))
    }

    fn set_choice_arity(&mut self, index: usize, arity: usize) {
        self.choice_arities[index] = arity;
    }

    fn pair_variable(&mut self, left: &Variable, right: &Variable) -> Result<(), String> {
        if left == right && fresh_class(left).is_none() {
            return Ok(());
        }
        let left_class = fresh_class(left);
        let right_class = fresh_class(right);
        if left.kind != right.kind || left.sort != right.sort || left_class != right_class {
            return Err(format!(
                "variables are not compatible fresh names: {left:?} versus {right:?}"
            ));
        }
        if left_class.is_none() {
            return Err(format!(
                "non-fresh variable names differ: {} versus {}",
                left.name, right.name
            ));
        }
        if let Some(previous) = self.forward.get(left)
            && previous != right
        {
            return Err(format!(
                "fresh variable {} maps inconsistently to {} and {}",
                left.name, previous.name, right.name
            ));
        }
        if let Some(previous) = self.reverse.get(right)
            && previous != left
        {
            return Err(format!(
                "fresh-variable renaming is not injective: {} and {} both map to {}",
                previous.name, left.name, right.name
            ));
        }
        self.forward.insert(left.clone(), right.clone());
        self.reverse.insert(right.clone(), left.clone());
        Ok(())
    }

    fn renamed_variable(&self, variable: &Variable) -> Variable {
        self.forward
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    }

    fn report(&self) -> BTreeMap<String, String> {
        self.forward
            .iter()
            .filter(|(left, right)| left != right)
            .map(|(left, right)| (left.name.to_string(), right.name.to_string()))
            .collect()
    }
}

trait AlphaComparable: Sized + PartialEq + std::fmt::Debug {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String>;
    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String>;
}

fn alpha_equal<T: AlphaComparable>(
    left: &T,
    right: &T,
) -> Result<BTreeMap<String, String>, String> {
    let mut choice_plan = Vec::new();
    loop {
        let mut context = AlphaContext::with_choice_plan(choice_plan.clone());
        let attempt = left.collect_alpha(right, &mut context).and_then(|()| {
            let renamed = left.rename_alpha(&context)?;
            if renamed == *right {
                Ok(context.report())
            } else {
                Err(format!(
                    "values still differ after the validated global renaming\nrenamed left: {renamed:#?}\nright: {right:#?}"
                ))
            }
        });
        match attempt {
            Ok(renaming) => return Ok(renaming),
            Err(_) if advance_alpha_choices(&mut choice_plan, &context) => {}
            Err(error) => return Err(error),
        }
    }
}

fn advance_alpha_choices(choice_plan: &mut Vec<usize>, context: &AlphaContext) -> bool {
    choice_plan.resize(context.choice_cursor, 0);
    for index in (0..context.choice_cursor).rev() {
        if choice_plan[index] + 1 < context.choice_arities[index] {
            choice_plan[index] += 1;
            choice_plan.truncate(index + 1);
            return true;
        }
    }
    false
}

fn assert_alpha_equal<T: AlphaComparable>(left: &T, right: &T, case: &str) {
    match alpha_equal(left, right) {
        Ok(renaming) if renaming.is_empty() => {}
        Ok(renaming) => {
            eprintln!("{case}: accepted non-identity fresh-variable bijection {renaming:?}")
        }
        Err(error) => panic!("{case}: alpha equality failed: {error}"),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct StepOutcome<'a> {
    branches: &'a [AppliedRule],
    remainder: &'a Option<RemainderBranch>,
    error: &'a Result<(), SimplificationError>,
}

impl AlphaComparable for StepOutcome<'_> {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        collect_slice(
            self.branches,
            other.branches,
            context,
            AppliedRule::collect_alpha,
        )?;
        self.remainder.collect_alpha(other.remainder, context)?;
        match (self.error, other.error) {
            (Ok(()), Ok(())) => Ok(()),
            (Err(left), Err(right)) => left.collect_alpha(right, context),
            _ => Err("cascade and replay error shapes differ".into()),
        }
    }

    fn rename_alpha(&self, _context: &AlphaContext) -> Result<Self, String> {
        unreachable!("borrowed step outcomes use the owned comparison below")
    }
}

#[cfg(feature = "z3")]
pub(super) fn assert_step_alpha_equal(
    left: (
        &[AppliedRule],
        &Option<RemainderBranch>,
        &Result<(), SimplificationError>,
    ),
    right: (
        &[AppliedRule],
        &Option<RemainderBranch>,
        &Result<(), SimplificationError>,
    ),
    case: &str,
) {
    let renaming = step_alpha_equal(left, right)
        .unwrap_or_else(|error| panic!("{case}: alpha equality failed: {error}"));
    if !renaming.is_empty() {
        eprintln!("{case}: accepted non-identity fresh-variable bijection {renaming:?}");
    }
}

pub(super) fn step_alpha_equal(
    left: (
        &[AppliedRule],
        &Option<RemainderBranch>,
        &Result<(), SimplificationError>,
    ),
    right: (
        &[AppliedRule],
        &Option<RemainderBranch>,
        &Result<(), SimplificationError>,
    ),
) -> Result<BTreeMap<String, String>, String> {
    let left_outcome = StepOutcome {
        branches: left.0,
        remainder: left.1,
        error: left.2,
    };
    let right_outcome = StepOutcome {
        branches: right.0,
        remainder: right.1,
        error: right.2,
    };
    let mut choice_plan = Vec::new();
    loop {
        let mut context = AlphaContext::with_choice_plan(choice_plan.clone());
        let attempt = left_outcome
            .collect_alpha(&right_outcome, &mut context)
            .and_then(|()| {
                let renamed_branches = left
                    .0
                    .iter()
                    .map(|branch| branch.rename_alpha(&context))
                    .collect::<Result<Vec<_>, _>>()?;
                let renamed_remainder = left.1.rename_alpha(&context)?;
                let renamed_error = match left.2 {
                    Ok(()) => Ok(()),
                    Err(error) => Err(error.rename_alpha(&context)?),
                };
                if renamed_branches == right.0
                    && &renamed_remainder == right.1
                    && &renamed_error == right.2
                {
                    Ok(context.report())
                } else {
                    Err(format!(
                        "values differ after the validated global renaming\nrenamed branches: {renamed_branches:#?}\nright branches: {:#?}\nrenamed remainder: {renamed_remainder:#?}\nright remainder: {:#?}\nrenamed error: {renamed_error:#?}\nright error: {:#?}",
                        right.0, right.1, right.2
                    ))
                }
            });
        match attempt {
            Ok(renaming) => return Ok(renaming),
            Err(_) if advance_alpha_choices(&mut choice_plan, &context) => {}
            Err(error) => return Err(error),
        }
    }
}

impl AlphaComparable for SimplificationError {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        use SimplificationError::*;
        match (self, other) {
            (
                SmtPredicate {
                    predicate: lp,
                    error: le,
                },
                SmtPredicate {
                    predicate: rp,
                    error: re,
                },
            ) => {
                collect_predicate(lp, rp, context)?;
                collect_smt_error(le, re, context)
            }
            (
                IterationLimit {
                    limit: ll,
                    term: lt,
                },
                IterationLimit {
                    limit: rl,
                    term: rt,
                },
            ) if ll == rl => collect_term(lt, rt, context),
            (
                PredicateIterationLimit {
                    limit: ll,
                    predicate: lp,
                },
                PredicateIterationLimit {
                    limit: rl,
                    predicate: rp,
                },
            ) if ll == rl => collect_predicate(lp, rp, context),
            (
                UnsupportedHook {
                    hook: lh,
                    reason: lr,
                    term: lt,
                },
                UnsupportedHook {
                    hook: rh,
                    reason: rr,
                    term: rt,
                },
            ) if lh == rh && lr == rr => collect_term(lt, rt, context),
            (
                Smt {
                    rule_id: li,
                    error: le,
                },
                Smt {
                    rule_id: ri,
                    error: re,
                },
            ) if li == ri => collect_smt_error(le, re, context),
            _ if self == other => Ok(()),
            _ => Err(format!(
                "simplification errors differ: {self:?} versus {other:?}"
            )),
        }
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        use SimplificationError::*;
        Ok(match self {
            SmtPredicate { predicate, error } => SmtPredicate {
                predicate: Box::new(rename_predicate(predicate, context)),
                error: rename_smt_error(error, context),
            },
            IterationLimit { limit, term } => IterationLimit {
                limit: *limit,
                term: rename_term(term, context),
            },
            PredicateIterationLimit { limit, predicate } => PredicateIterationLimit {
                limit: *limit,
                predicate: rename_predicate(predicate, context),
            },
            UnsupportedHook { hook, reason, term } => UnsupportedHook {
                hook: hook.clone(),
                reason: reason.clone(),
                term: rename_term(term, context),
            },
            Smt { rule_id, error } => Smt {
                rule_id: rule_id.clone(),
                error: rename_smt_error(error, context),
            },
            exact => exact.clone(),
        })
    }
}

fn collect_smt_error(
    left: &SmtError,
    right: &SmtError,
    context: &mut AlphaContext,
) -> Result<(), String> {
    use SmtError::*;
    match (left, right) {
        (Translation(left), Translation(right)) => collect_translation_error(left, right, context),
        (MissingModelValue(left), MissingModelValue(right)) => context.pair_variable(left, right),
        (
            InvalidModelValue {
                variable: lv,
                value: lx,
            },
            InvalidModelValue {
                variable: rv,
                value: rx,
            },
        ) if lx == rx => context.pair_variable(lv, rv),
        _ if left == right => Ok(()),
        _ => Err(format!("SMT errors differ: {left:?} versus {right:?}")),
    }
}

fn rename_smt_error(error: &SmtError, context: &AlphaContext) -> SmtError {
    use SmtError::*;
    match error {
        Translation(error) => Translation(rename_translation_error(error, context)),
        MissingModelValue(variable) => MissingModelValue(context.renamed_variable(variable)),
        InvalidModelValue { variable, value } => InvalidModelValue {
            variable: context.renamed_variable(variable),
            value: value.clone(),
        },
        exact => exact.clone(),
    }
}

fn collect_translation_error(
    left: &TranslationError,
    right: &TranslationError,
    context: &mut AlphaContext,
) -> Result<(), String> {
    use TranslationError::*;
    match (left, right) {
        (NonBooleanAnd(left), NonBooleanAnd(right)) => collect_term(left, right, context),
        (
            SmtLemmaSurplusMappings {
                rule_id: li,
                terms: lt,
            },
            SmtLemmaSurplusMappings {
                rule_id: ri,
                terms: rt,
            },
        ) if li == ri => collect_slice(lt, rt, context, collect_term),
        (
            SmtLemmaSurplusPredicates {
                rule_id: li,
                predicates: lp,
            },
            SmtLemmaSurplusPredicates {
                rule_id: ri,
                predicates: rp,
            },
        ) if li == ri => collect_slice(lp, rp, context, collect_predicate),
        (
            MissingSmtLemmaVariable {
                rule_id: li,
                variable: lv,
            },
            MissingSmtLemmaVariable {
                rule_id: ri,
                variable: rv,
            },
        ) if li == ri => context.pair_variable(lv, rv),
        _ if left == right => Ok(()),
        _ => Err(format!(
            "SMT translation errors differ: {left:?} versus {right:?}"
        )),
    }
}

fn rename_translation_error(error: &TranslationError, context: &AlphaContext) -> TranslationError {
    use TranslationError::*;
    match error {
        NonBooleanAnd(term) => NonBooleanAnd(rename_term(term, context)),
        SmtLemmaSurplusMappings { rule_id, terms } => SmtLemmaSurplusMappings {
            rule_id: rule_id.clone(),
            terms: terms
                .iter()
                .map(|term| rename_term(term, context))
                .collect(),
        },
        SmtLemmaSurplusPredicates {
            rule_id,
            predicates,
        } => SmtLemmaSurplusPredicates {
            rule_id: rule_id.clone(),
            predicates: rename_predicates(predicates, context),
        },
        MissingSmtLemmaVariable { rule_id, variable } => MissingSmtLemmaVariable {
            rule_id: rule_id.clone(),
            variable: context.renamed_variable(variable),
        },
        exact => exact.clone(),
    }
}

fn collect_term(left: &Term, right: &Term, context: &mut AlphaContext) -> Result<(), String> {
    match (left.kind(), right.kind()) {
        (TermKind::And(ll, lr), TermKind::And(rl, rr)) => {
            collect_term(ll, rl, context)?;
            collect_term(lr, rr, context)
        }
        (
            TermKind::Application {
                symbol: ls,
                sort_arguments: lsa,
                arguments: la,
            },
            TermKind::Application {
                symbol: rs,
                sort_arguments: rsa,
                arguments: ra,
            },
        ) if ls == rs && lsa == rsa => collect_slice(la, ra, context, collect_term),
        (
            TermKind::DomainValue {
                sort: ls,
                value: lv,
            },
            TermKind::DomainValue {
                sort: rs,
                value: rv,
            },
        ) if ls == rs && lv == rv => Ok(()),
        (TermKind::Variable(left), TermKind::Variable(right)) => context.pair_variable(left, right),
        (
            TermKind::Injection {
                source: ls,
                target: lt,
                term: li,
            },
            TermKind::Injection {
                source: rs,
                target: rt,
                term: ri,
            },
        ) if ls == rs && lt == rt => collect_term(li, ri, context),
        (
            TermKind::Map {
                definition: ld,
                entries: le,
                rest: lr,
            },
            TermKind::Map {
                definition: rd,
                entries: re,
                rest: rr,
            },
        ) if ld == rd && le.len() == re.len() => {
            collect_unordered(le, re, context, |(lk, lv), (rk, rv), context| {
                collect_term(lk, rk, context)?;
                collect_term(lv, rv, context)
            })?;
            collect_option(lr, rr, context, collect_term)
        }
        (
            TermKind::List {
                definition: ld,
                heads: lh,
                rest: lr,
            },
            TermKind::List {
                definition: rd,
                heads: rh,
                rest: rr,
            },
        ) if ld == rd => {
            collect_slice(lh, rh, context, collect_term)?;
            match (lr, rr) {
                (None, None) => Ok(()),
                (Some((lm, lt)), Some((rm, rt))) => {
                    collect_term(lm, rm, context)?;
                    collect_slice(lt, rt, context, collect_term)
                }
                _ => Err("list rests differ".into()),
            }
        }
        (
            TermKind::Set {
                definition: ld,
                elements: le,
                rest: lr,
            },
            TermKind::Set {
                definition: rd,
                elements: re,
                rest: rr,
            },
        ) if ld == rd => {
            collect_unordered(le, re, context, collect_term)?;
            collect_option(lr, rr, context, collect_term)
        }
        _ => Err(format!("term structures differ: {left:?} versus {right:?}")),
    }
}

fn rename_term(term: &Term, context: &AlphaContext) -> Term {
    let renaming = term
        .attributes()
        .variables
        .iter()
        .filter_map(|variable| {
            let renamed = context.renamed_variable(variable);
            (renamed != *variable).then(|| (variable.clone(), Term::variable(renamed)))
        })
        .collect::<Substitution>();
    substitute(term, &renaming)
}

fn collect_predicate(
    left: &Predicate,
    right: &Predicate,
    context: &mut AlphaContext,
) -> Result<(), String> {
    use Predicate::*;
    match (left, right) {
        (True, True) | (False, False) => Ok(()),
        (Term(left), Term(right)) | (Ceil(left), Ceil(right)) | (Floor(left), Floor(right)) => {
            collect_term(left, right, context)
        }
        (Equals(ll, lr), Equals(rl, rr)) | (In(ll, lr), In(rl, rr)) => {
            collect_term(ll, rl, context)?;
            collect_term(lr, rr, context)
        }
        (Not(left), Not(right)) => collect_predicate(left, right, context),
        (And(left), And(right)) | (Or(left), Or(right)) => {
            collect_slice(left, right, context, collect_predicate)
        }
        (Implies(ll, lr), Implies(rl, rr)) | (Iff(ll, lr), Iff(rl, rr)) => {
            collect_predicate(ll, rl, context)?;
            collect_predicate(lr, rr, context)
        }
        (Exists(lv, lp), Exists(rv, rp)) | (Forall(lv, lp), Forall(rv, rp)) => {
            context.pair_variable(lv, rv)?;
            collect_predicate(lp, rp, context)
        }
        _ => Err(format!(
            "predicate structures differ: {left:?} versus {right:?}"
        )),
    }
}

fn rename_predicate(predicate: &Predicate, context: &AlphaContext) -> Predicate {
    use Predicate::*;
    match predicate {
        True => True,
        False => False,
        Term(term) => Term(rename_term(term, context)),
        Equals(left, right) => Equals(rename_term(left, context), rename_term(right, context)),
        Ceil(term) => Ceil(rename_term(term, context)),
        Floor(term) => Floor(rename_term(term, context)),
        In(left, right) => In(rename_term(left, context), rename_term(right, context)),
        Not(inner) => Not(Box::new(rename_predicate(inner, context))),
        And(inner) => And(rename_predicates(inner, context)),
        Or(inner) => Or(rename_predicates(inner, context)),
        Implies(left, right) => Implies(
            Box::new(rename_predicate(left, context)),
            Box::new(rename_predicate(right, context)),
        ),
        Iff(left, right) => Iff(
            Box::new(rename_predicate(left, context)),
            Box::new(rename_predicate(right, context)),
        ),
        Exists(variable, inner) => Exists(
            context.renamed_variable(variable),
            Box::new(rename_predicate(inner, context)),
        ),
        Forall(variable, inner) => Forall(
            context.renamed_variable(variable),
            Box::new(rename_predicate(inner, context)),
        ),
    }
}

fn rename_predicates(predicates: &[Predicate], context: &AlphaContext) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| rename_predicate(predicate, context))
        .collect()
}

fn collect_slice<T>(
    left: &[T],
    right: &[T],
    context: &mut AlphaContext,
    collect: impl Copy + Fn(&T, &T, &mut AlphaContext) -> Result<(), String>,
) -> Result<(), String> {
    if left.len() != right.len() {
        return Err(format!(
            "sequence lengths differ: {} versus {}",
            left.len(),
            right.len()
        ));
    }
    for (left, right) in left.iter().zip(right) {
        collect(left, right, context)?;
    }
    Ok(())
}

fn collect_unordered<T>(
    left: &[T],
    right: &[T],
    context: &mut AlphaContext,
    collect: impl Copy + Fn(&T, &T, &mut AlphaContext) -> Result<(), String>,
) -> Result<(), String> {
    if left.len() != right.len() {
        return Err(format!(
            "unordered collection lengths differ: {} versus {}",
            left.len(),
            right.len()
        ));
    }
    let (choice_index, selected) = context.begin_choice();

    fn generate_permutations(
        index: usize,
        permutation: &mut [usize],
        values: &mut Vec<Vec<usize>>,
    ) {
        if index == permutation.len() {
            values.push(permutation.to_vec());
            return;
        }
        for candidate in index..permutation.len() {
            permutation.swap(index, candidate);
            generate_permutations(index + 1, permutation, values);
            permutation.swap(index, candidate);
        }
    }

    let mut permutation = (0..right.len()).collect::<Vec<_>>();
    let mut candidates = Vec::new();
    generate_permutations(0, &mut permutation, &mut candidates);
    let arity = candidates.len();
    context.set_choice_arity(choice_index, arity);
    let Some(permutation) = candidates.get(selected) else {
        return Err("unordered collections have no alpha-compatible bijection".into());
    };
    for (left, right_index) in left.iter().zip(permutation) {
        collect(left, &right[*right_index], context)?;
    }
    Ok(())
}

fn collect_option<T>(
    left: &Option<T>,
    right: &Option<T>,
    context: &mut AlphaContext,
    collect: impl Copy + Fn(&T, &T, &mut AlphaContext) -> Result<(), String>,
) -> Result<(), String> {
    match (left, right) {
        (None, None) => Ok(()),
        (Some(left), Some(right)) => collect(left, right, context),
        _ => Err("option shapes differ".into()),
    }
}

fn collect_substitution(
    left: &Substitution,
    right: &Substitution,
    context: &mut AlphaContext,
) -> Result<(), String> {
    if left.len() != right.len() {
        return Err("substitution lengths differ".into());
    }
    let left = left.iter().collect::<Vec<_>>();
    let right = right.iter().collect::<Vec<_>>();
    collect_unordered(&left, &right, context, |(lv, lt), (rv, rt), context| {
        context.pair_variable(lv, rv)?;
        collect_term(lt, rt, context)
    })
}

fn rename_substitution(substitution: &Substitution, context: &AlphaContext) -> Substitution {
    substitution
        .iter()
        .map(|(variable, term)| {
            (
                context.renamed_variable(variable),
                rename_term(term, context),
            )
        })
        .collect()
}

impl AlphaComparable for Pattern {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        collect_term(&self.term, &other.term, context)?;
        collect_slice(
            &self.constraints,
            &other.constraints,
            context,
            collect_predicate,
        )
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            term: rename_term(&self.term, context),
            constraints: rename_predicates(&self.constraints, context),
        })
    }
}

impl AlphaComparable for AppliedRule {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        self.before.collect_alpha(&other.before, context)?;
        self.pattern.collect_alpha(&other.pattern, context)?;
        collect_substitution(&self.substitution, &other.substitution, context)?;
        collect_substitution(&self.rule_substitution, &other.rule_substitution, context)?;
        collect_slice(
            &self.rule_predicates,
            &other.rule_predicates,
            context,
            collect_predicate,
        )?;
        if self.label != other.label
            || self.unique_id != other.unique_id
            || self.effects != other.effects
            || self.io != other.io
        {
            return Err("non-pattern applied-rule fields differ".into());
        }
        Ok(())
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            before: self.before.rename_alpha(context)?,
            pattern: self.pattern.rename_alpha(context)?,
            label: self.label.clone(),
            unique_id: self.unique_id.clone(),
            substitution: rename_substitution(&self.substitution, context),
            rule_substitution: rename_substitution(&self.rule_substitution, context),
            rule_predicates: rename_predicates(&self.rule_predicates, context),
            effects: self.effects.clone(),
            io: self.io.clone(),
        })
    }
}

impl AlphaComparable for RemainderBranch {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        self.pattern.collect_alpha(&other.pattern, context)?;
        if self.rule_ids != other.rule_ids || self.effects != other.effects {
            return Err("non-pattern remainder fields differ".into());
        }
        Ok(())
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            pattern: self.pattern.rename_alpha(context)?,
            rule_ids: self.rule_ids.clone(),
            effects: self.effects.clone(),
        })
    }
}

impl AlphaComparable for TrivialApplication {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        collect_predicate(&self.obligation, &other.obligation, context)?;
        collect_predicate(&self.applicability, &other.applicability, context)?;
        collect_predicate(&self.remainder, &other.remainder, context)?;
        if self.rule_id != other.rule_id
            || self.label != other.label
            || self.effects != other.effects
        {
            return Err("non-predicate trivial-application fields differ".into());
        }
        Ok(())
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            rule_id: self.rule_id.clone(),
            label: self.label.clone(),
            obligation: rename_predicate(&self.obligation, context),
            applicability: rename_predicate(&self.applicability, context),
            remainder: rename_predicate(&self.remainder, context),
            effects: self.effects.clone(),
        })
    }
}

impl AlphaComparable for IndeterminateReason {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        use IndeterminateReason::*;
        match (self, other) {
            (
                Simplification {
                    rule_id: li,
                    error: le,
                },
                Simplification {
                    rule_id: ri,
                    error: re,
                },
            ) if li == ri => le.collect_alpha(re, context),
            (
                Match {
                    rule_id: li,
                    substitution: ls,
                    remainder: lr,
                },
                Match {
                    rule_id: ri,
                    substitution: rs,
                    remainder: rr,
                },
            ) if li == ri => {
                collect_substitution(ls, rs, context)?;
                collect_slice(lr, rr, context, |(ll, lr), (rl, rr), context| {
                    collect_term(ll, rl, context)?;
                    collect_term(lr, rr, context)
                })
            }
            (
                Instantiation {
                    rule_id: li,
                    missing_variables: lv,
                },
                Instantiation {
                    rule_id: ri,
                    missing_variables: rv,
                },
            ) if li == ri => {
                let left = lv.iter().collect::<Vec<_>>();
                let right = rv.iter().collect::<Vec<_>>();
                collect_unordered(&left, &right, context, |left, right, context| {
                    context.pair_variable(left, right)
                })
            }
            (
                Requires {
                    rule_id: li,
                    predicates: lp,
                },
                Requires {
                    rule_id: ri,
                    predicates: rp,
                },
            ) if li == ri => collect_slice(lp, rp, context, collect_predicate),
            (
                Smt {
                    rule_id: li,
                    error: le,
                },
                Smt {
                    rule_id: ri,
                    error: re,
                },
            ) if li == ri => collect_smt_error(le, re, context),
            (
                Remainder {
                    rule_ids: li,
                    predicates: lp,
                    satisfiability: ls,
                },
                Remainder {
                    rule_ids: ri,
                    predicates: rp,
                    satisfiability: rs,
                },
            ) if li == ri => {
                collect_slice(lp, rp, context, collect_predicate)?;
                match (ls, rs) {
                    (Ok(left), Ok(right)) if left == right => Ok(()),
                    (Err(left), Err(right)) => collect_smt_error(left, right, context),
                    _ => Err("remainder satisfiability results differ".into()),
                }
            }
            _ if self == other => Ok(()),
            _ => Err(format!(
                "indeterminate reasons differ: {self:?} versus {other:?}"
            )),
        }
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        use IndeterminateReason::*;
        Ok(match self {
            Simplification { rule_id, error } => Simplification {
                rule_id: rule_id.clone(),
                error: error.rename_alpha(context)?,
            },
            Match {
                rule_id,
                substitution,
                remainder,
            } => Match {
                rule_id: rule_id.clone(),
                substitution: rename_substitution(substitution, context),
                remainder: remainder
                    .iter()
                    .map(|(left, right)| (rename_term(left, context), rename_term(right, context)))
                    .collect(),
            },
            Instantiation {
                rule_id,
                missing_variables,
            } => Instantiation {
                rule_id: rule_id.clone(),
                missing_variables: missing_variables
                    .iter()
                    .map(|variable| context.renamed_variable(variable))
                    .collect(),
            },
            Requires {
                rule_id,
                predicates,
            } => Requires {
                rule_id: rule_id.clone(),
                predicates: rename_predicates(predicates, context),
            },
            Smt { rule_id, error } => Smt {
                rule_id: rule_id.clone(),
                error: rename_smt_error(error, context),
            },
            Remainder {
                rule_ids,
                predicates,
                satisfiability,
            } => Remainder {
                rule_ids: rule_ids.clone(),
                predicates: rename_predicates(predicates, context),
                satisfiability: match satisfiability {
                    Ok(value) => Ok(value.clone()),
                    Err(error) => Err(rename_smt_error(error, context)),
                },
            },
            exact => exact.clone(),
        })
    }
}

impl AlphaComparable for HaltReason {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        use HaltReason::*;
        match (self, other) {
            (
                Trivial {
                    depth: ld,
                    rule_id: li,
                    label: ll,
                    obligation: lp,
                },
                Trivial {
                    depth: rd,
                    rule_id: ri,
                    label: rl,
                    obligation: rp,
                },
            ) if ld == rd && li == ri && ll == rl => collect_predicate(lp, rp, context),
            (
                Vacuous {
                    depth: ld,
                    rule_id: li,
                    label: ll,
                    constraint: lp,
                },
                Vacuous {
                    depth: rd,
                    rule_id: ri,
                    label: rl,
                    constraint: rp,
                },
            ) if ld == rd && li == ri && ll == rl => collect_predicate(lp, rp, context),
            (
                Branch {
                    branches: lb,
                    remainder: lr,
                },
                Branch {
                    branches: rb,
                    remainder: rr,
                },
            ) => {
                collect_slice(lb, rb, context, AppliedRule::collect_alpha)?;
                lr.collect_alpha(rr, context)
            }
            (
                CutPointRule {
                    rule: lr,
                    next_states: ln,
                },
                CutPointRule {
                    rule: rr,
                    next_states: rn,
                },
            ) if lr == rr => collect_slice(ln, rn, context, AppliedRule::collect_alpha),
            (Indeterminate(left), Indeterminate(right)) => left.collect_alpha(right, context),
            (Simplification(left), Simplification(right)) => left.collect_alpha(right, context),
            _ if self == other => Ok(()),
            _ => Err(format!("halt reasons differ: {self:?} versus {other:?}")),
        }
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        use HaltReason::*;
        Ok(match self {
            Trivial {
                depth,
                rule_id,
                label,
                obligation,
            } => Trivial {
                depth: *depth,
                rule_id: rule_id.clone(),
                label: label.clone(),
                obligation: rename_predicate(obligation, context),
            },
            Vacuous {
                depth,
                rule_id,
                label,
                constraint,
            } => Vacuous {
                depth: *depth,
                rule_id: rule_id.clone(),
                label: label.clone(),
                constraint: rename_predicate(constraint, context),
            },
            Branch {
                branches,
                remainder,
            } => Branch {
                branches: branches.rename_alpha(context)?,
                remainder: remainder.rename_alpha(context)?,
            },
            CutPointRule { rule, next_states } => CutPointRule {
                rule: rule.clone(),
                next_states: next_states.rename_alpha(context)?,
            },
            Indeterminate(reason) => Indeterminate(reason.rename_alpha(context)?),
            Simplification(error) => Simplification(error.rename_alpha(context)?),
            exact => exact.clone(),
        })
    }
}

impl AlphaComparable for TransitionObservation {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        self.before.collect_alpha(&other.before, context)?;
        self.after.collect_alpha(&other.after, context)?;
        collect_substitution(&self.bindings, &other.bindings, context)?;
        collect_slice(
            &self.introduced_predicates,
            &other.introduced_predicates,
            context,
            collect_predicate,
        )?;
        if self.id.rule != other.id.rule
            || self.id.target != PatternDigest::of(&self.after)
            || other.id.target != PatternDigest::of(&other.after)
            || self.class != other.class
            || self.rule_label != other.rule_label
            || self.effects != other.effects
        {
            return Err("transition observation metadata or target digest differs".into());
        }
        Ok(())
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        let after = self.after.rename_alpha(context)?;
        Ok(Self {
            id: TransitionId {
                rule: self.id.rule.clone(),
                target: PatternDigest::of(&after),
            },
            class: self.class,
            rule_label: self.rule_label.clone(),
            bindings: rename_substitution(&self.bindings, context),
            introduced_predicates: rename_predicates(&self.introduced_predicates, context),
            before: self.before.rename_alpha(context)?,
            after,
            effects: self.effects.clone(),
        })
    }
}

impl AlphaComparable for ObservationEvent {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        match (self, other) {
            (Self::Transition(left), Self::Transition(right)) => {
                left.collect_alpha(right, context)
            }
            (Self::Uncommitted(left), Self::Uncommitted(right)) if left == right => Ok(()),
            (Self::Uncommitted(_), Self::Uncommitted(_)) => Err(
                "uncommitted transition differs and has no retained target for digest recomputation"
                    .into(),
            ),
            _ => Err("observation event shapes differ".into()),
        }
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(match self {
            Self::Transition(observation) => Self::Transition(observation.rename_alpha(context)?),
            Self::Uncommitted(observation) => Self::Uncommitted(observation.clone()),
        })
    }
}

fn retained_transition_target<'a>(
    id: &TransitionId,
    observations: &'a [ObservationEvent],
) -> Option<&'a Pattern> {
    observations.iter().find_map(|event| match event {
        ObservationEvent::Transition(observation) if observation.id == *id => {
            Some(&observation.after)
        }
        _ => None,
    })
}

impl AlphaComparable for ExecutionLeaf {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        self.pattern.collect_alpha(&other.pattern, context)?;
        collect_slice(
            &self.observations,
            &other.observations,
            context,
            ObservationEvent::collect_alpha,
        )?;
        if self.branch.len() != other.branch.len() {
            return Err("execution branch identity lengths differ".into());
        }
        for (left, right) in self.branch.iter().zip(&other.branch) {
            if left.rule != right.rule {
                return Err("execution branch rules differ".into());
            }
            let left_target =
                retained_transition_target(left, &self.observations).ok_or_else(|| {
                    format!("transition {left:?} has no retained target for digest recomputation")
                })?;
            let right_target =
                retained_transition_target(right, &other.observations).ok_or_else(|| {
                    format!("transition {right:?} has no retained target for digest recomputation")
                })?;
            left_target.collect_alpha(right_target, context)?;
        }
        self.halt_reason
            .collect_alpha(&other.halt_reason, context)?;
        if self.depth != other.depth
            || self.trace != other.trace
            || self.effects != other.effects
            || self.io != other.io
        {
            return Err("non-pattern execution leaf fields differ".into());
        }
        Ok(())
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        let observations = self.observations.rename_alpha(context)?;
        let branch = self
            .branch
            .iter()
            .map(|id| {
                let target =
                    retained_transition_target(id, &self.observations).ok_or_else(|| {
                        format!("transition {id:?} has no retained target for digest recomputation")
                    })?;
                let target = target.rename_alpha(context)?;
                Ok(TransitionId {
                    rule: id.rule.clone(),
                    target: PatternDigest::of(&target),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Self {
            pattern: self.pattern.rename_alpha(context)?,
            depth: self.depth,
            trace: self.trace.clone(),
            branch,
            observations,
            effects: self.effects.clone(),
            io: self.io.clone(),
            halt_reason: self.halt_reason.rename_alpha(context)?,
        })
    }
}

impl AlphaComparable for ExecutionResult {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        collect_slice(
            &self.leaves,
            &other.leaves,
            context,
            ExecutionLeaf::collect_alpha,
        )?;
        if self.effects != other.effects || self.discarded != other.discarded {
            return Err(
                "execution effects or discarded transitions differ; discarded targets are not retained"
                    .into(),
            );
        }
        Ok(())
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            leaves: self.leaves.rename_alpha(context)?,
            effects: self.effects.clone(),
            discarded: self.discarded.clone(),
        })
    }
}

impl<T: AlphaComparable> AlphaComparable for Vec<T> {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        collect_slice(self, other, context, T::collect_alpha)
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        self.iter()
            .map(|value| value.rename_alpha(context))
            .collect()
    }
}

impl<T: AlphaComparable> AlphaComparable for Option<T> {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        collect_option(self, other, context, T::collect_alpha)
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        self.as_ref()
            .map(|value| value.rename_alpha(context))
            .transpose()
    }
}

fn pattern(name: &str) -> Pattern {
    let variable = Variable::new(name, Sort::simple("SortS"));
    Pattern {
        term: Term::variable(variable),
        constraints: Vec::new(),
    }
}

fn result_with_transition(name: &str) -> ExecutionResult {
    let before = pattern("State");
    let after = pattern(name);
    let id = TransitionId {
        rule: "rule".into(),
        target: PatternDigest::of(&after),
    };
    ExecutionResult {
        leaves: vec![ExecutionLeaf {
            pattern: after.clone(),
            depth: 1,
            trace: Vec::new(),
            branch: vec![id.clone()],
            observations: vec![ObservationEvent::Transition(TransitionObservation {
                id,
                class: TransitionClass::Rewrite,
                rule_label: Some("rule".into()),
                bindings: Substitution::new(),
                introduced_predicates: Vec::new(),
                before,
                after,
                effects: Vec::new(),
            })],
            effects: Vec::new(),
            io: ExecutionIoState::default(),
            halt_reason: HaltReason::Stuck,
        }],
        effects: Vec::new(),
        discarded: Vec::new(),
    }
}

#[test]
fn alpha_equality_accepts_identity() {
    let value = vec![RemainderBranch {
        pattern: pattern("X!0"),
        rule_ids: vec!["rule".into()],
        effects: Vec::new(),
    }];
    assert_alpha_equal(&value, &value, "identity");
}

#[test]
fn alpha_equality_accepts_one_global_injective_renaming() {
    let left = vec![RemainderBranch {
        pattern: Pattern {
            term: Term::and(pattern("X!0").term, pattern("Y!1").term),
            constraints: Vec::new(),
        },
        rule_ids: vec![],
        effects: vec![],
    }];
    let right = vec![RemainderBranch {
        pattern: Pattern {
            term: Term::and(pattern("X!8").term, pattern("Y!9").term),
            constraints: Vec::new(),
        },
        rule_ids: vec![],
        effects: vec![],
    }];
    assert_alpha_equal(&left, &right, "non-identity renaming");
    assert_eq!(
        alpha_equal(&left, &right).unwrap(),
        BTreeMap::from([("X!0".into(), "X!8".into()), ("Y!1".into(), "Y!9".into())])
    );
}

#[test]
fn alpha_equality_rejects_noninjective_renaming() {
    let left = vec![pattern("X!0"), pattern("Y!1")];
    let right = vec![pattern("Z!2"), pattern("Z!2")];
    assert!(
        alpha_equal(&left, &right)
            .unwrap_err()
            .contains("not injective")
    );
}

#[test]
fn alpha_equality_rejects_inconsistent_per_leaf_renaming() {
    let left = vec![pattern("X!0"), pattern("X!0")];
    let right = vec![pattern("X!0"), pattern("X!2")];
    assert!(
        alpha_equal(&left, &right)
            .unwrap_err()
            .contains("inconsistently")
    );
}

#[test]
fn alpha_equality_recomputes_transition_digests() {
    let left = result_with_transition("Ex#Fresh!0");
    let right = result_with_transition("Ex#Fresh!7");
    assert_eq!(
        alpha_equal(&left, &right).unwrap(),
        BTreeMap::from([("Ex#Fresh!0".into(), "Ex#Fresh!7".into())])
    );

    let mut invalid = right;
    let invalid_digest = PatternDigest::of(&pattern("Ex#Fresh!8"));
    invalid.leaves[0].branch[0].target = invalid_digest;
    let ObservationEvent::Transition(observation) = &mut invalid.leaves[0].observations[0] else {
        unreachable!()
    };
    observation.id.target = invalid_digest;
    assert!(alpha_equal(&left, &invalid).is_err());
}

#[test]
fn alpha_equality_rejects_fresh_provenance_changes() {
    for right in ["Eq#X!7", "X!7", "Ex#X!7"] {
        let error = alpha_equal(&pattern("Rule#X!0"), &pattern(right)).unwrap_err();
        assert!(error.contains("not compatible fresh names"), "{error}");
    }
    assert!(alpha_equal(&pattern("Rule#X"), &pattern("Rule#Y")).is_err());
}

#[test]
fn alpha_equality_renames_variable_bearing_simplification_errors_globally() {
    let errors = |name: &str| {
        vec![
            SimplificationError::SmtPredicate {
                predicate: Box::new(Predicate::Ceil(pattern(name).term)),
                error: SmtError::MissingModelValue(Variable::new(name, Sort::simple("SortS"))),
            },
            SimplificationError::UnsupportedHook {
                hook: "TEST.hook".into(),
                reason: UnsupportedHookReason::NotImplemented,
                term: pattern(name).term,
            },
        ]
    };
    assert_alpha_equal(&errors("X!9"), &errors("X!10"), "errors");
}

#[test]
fn alpha_equality_renames_remainder_satisfiability_errors_globally() {
    let reason = |name: &str| IndeterminateReason::Remainder {
        rule_ids: vec!["conditional".into()],
        predicates: Vec::new(),
        satisfiability: Err(SmtError::MissingModelValue(Variable::new(
            name,
            Sort::simple("SortS"),
        ))),
    };
    assert_eq!(
        alpha_equal(&reason("X!9"), &reason("X!10")).unwrap(),
        BTreeMap::from([("X!9".into(), "X!10".into())])
    );
}

#[derive(Debug, Eq, PartialEq)]
struct OrderedCollections {
    map: Pattern,
    set: Pattern,
    substitution: Substitution,
}

impl AlphaComparable for OrderedCollections {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        self.map.collect_alpha(&other.map, context)?;
        self.set.collect_alpha(&other.set, context)?;
        collect_substitution(&self.substitution, &other.substitution, context)
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            map: self.map.rename_alpha(context)?,
            set: self.set.rename_alpha(context)?,
            substitution: rename_substitution(&self.substitution, context),
        })
    }
}

fn ordered_collections(first: &str, second: &str) -> OrderedCollections {
    let sort = Sort::simple("SortS");
    let first_variable = Variable::new(first, sort.clone());
    let second_variable = Variable::new(second, sort.clone());
    let symbols = CollectionSymbols {
        unit: "unit".into(),
        element: "element".into(),
        concat: "concat".into(),
    };
    let map_definition = Arc::new(MapDefinition {
        symbols: symbols.clone(),
        key_sort: "SortS".into(),
        value_sort: "SortS".into(),
        map_sort: "SortMap".into(),
    });
    let set_definition = Arc::new(ListDefinition {
        symbols,
        element_sort: "SortS".into(),
        list_sort: "SortSet".into(),
    });
    let value = |text: &str| Term::domain_value(sort.clone(), text);
    OrderedCollections {
        map: Pattern {
            term: Term::map(
                map_definition,
                vec![
                    (Term::variable(first_variable.clone()), value("first")),
                    (Term::variable(second_variable.clone()), value("second")),
                ],
                None,
            ),
            constraints: Vec::new(),
        },
        set: Pattern {
            term: Term::set(
                set_definition,
                vec![
                    Term::variable(first_variable.clone()),
                    Term::variable(second_variable.clone()),
                ],
                None,
            ),
            constraints: Vec::new(),
        },
        substitution: BTreeMap::from([
            (first_variable, value("first")),
            (second_variable, value("second")),
        ]),
    }
}

#[test]
fn alpha_equality_handles_fresh_renamings_that_cross_btree_order() {
    let left = ordered_collections("K!9", "K!10");
    let right = ordered_collections("K!11", "K!8");
    assert_alpha_equal(&left, &right, "crossing BTree order");
}

#[derive(Debug, Eq, PartialEq)]
struct AmbiguousSetThenOrdered {
    set: Pattern,
    ordered: Pattern,
}

impl AlphaComparable for AmbiguousSetThenOrdered {
    fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
        self.set.collect_alpha(&other.set, context)?;
        self.ordered.collect_alpha(&other.ordered, context)
    }

    fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
        Ok(Self {
            set: self.set.rename_alpha(context)?,
            ordered: self.ordered.rename_alpha(context)?,
        })
    }
}

fn ambiguous_set_then_ordered(first: &str, second: &str, ordered: &str) -> AmbiguousSetThenOrdered {
    let sort = Sort::simple("SortS");
    let set_definition = Arc::new(ListDefinition {
        symbols: CollectionSymbols {
            unit: "unit".into(),
            element: "element".into(),
            concat: "concat".into(),
        },
        element_sort: "SortS".into(),
        list_sort: "SortSet".into(),
    });
    AmbiguousSetThenOrdered {
        set: Pattern {
            term: Term::set(
                set_definition,
                vec![
                    Term::variable(Variable::new(first, sort.clone())),
                    Term::variable(Variable::new(second, sort.clone())),
                ],
                None,
            ),
            constraints: Vec::new(),
        },
        ordered: pattern(ordered),
    }
}

#[test]
fn alpha_equality_backtracks_ambiguous_unordered_choices_after_later_mismatch() {
    let left = ambiguous_set_then_ordered("X!0", "Y!1", "X!0");
    let right = ambiguous_set_then_ordered("A!2", "B!3", "B!3");
    assert_eq!(
        alpha_equal(&left, &right).unwrap(),
        BTreeMap::from([("X!0".into(), "B!3".into()), ("Y!1".into(), "A!2".into())])
    );
}
