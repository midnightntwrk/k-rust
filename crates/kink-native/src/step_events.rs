//! Step-event declarations and a baseline-owned observation decider.

use std::collections::BTreeMap;

use k_rust::backend::{Backend, BackendError};
use k_rust::kore::ast::{Pattern, Sort, VariableKind};
use k_rust_backend::definition::BackendDefinition;
use k_rust_backend::smt::SmtSolver;
use k_rust_backend::term::Sort as InternalSort;
use kink_pattern::{
    Constructor, EventVocabulary, Feasibility, PathInput, RelationDecider, RelationDecision,
    TermRelation,
};

use crate::feasibility::{
    BackendRelations, Inhabitation, contains_non_strict_injection, domain_value_identity_safe,
    free_constructor, non_strict_injection_node, strict_injection_sorts,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepEventSpec {
    pub constructor: String,
    pub pre: Pattern,
    pub post: Option<Pattern>,
    pub payload: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepObservationError {
    Internalization(String),
    VariableSort(String),
    NonFreeSymbol(String),
    NonCanonicalValue(String),
    UnsupportedPattern(String),
    ReservedVariable(String),
    MissingPayload(String),
    ConstructorSorts(String),
}

impl std::fmt::Display for StepObservationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for StepObservationError {}
impl From<BackendError> for StepObservationError {
    fn from(error: BackendError) -> Self {
        Self::Internalization(error.to_string())
    }
}
impl From<k_rust_backend::stop::StopCause> for StepObservationError {
    fn from(cause: k_rust_backend::stop::StopCause) -> Self {
        Self::Internalization(cause.to_string())
    }
}

#[derive(Clone, Debug)]
pub struct StepObservation {
    specs: Vec<StepEventSpec>,
    vocabulary: EventVocabulary,
}

impl StepObservation {
    pub fn new(
        backend: &mut Backend,
        specs: Vec<StepEventSpec>,
    ) -> Result<Self, StepObservationError> {
        let vocabulary = Self::vocabulary_of(&specs)?;
        backend.with_solver(None, |definition, _| -> Result<(), StepObservationError> {
            for spec in &specs {
                validate_pattern(definition, &spec.pre)?;
                if let Some(post) = &spec.post {
                    validate_pattern(definition, post)?;
                }
            }
            Ok(())
        })?;
        Ok(Self { specs, vocabulary })
    }

    pub fn vocabulary(&self) -> &EventVocabulary {
        &self.vocabulary
    }
    pub fn specs(&self) -> &[StepEventSpec] {
        &self.specs
    }

    pub fn vocabulary_of(specs: &[StepEventSpec]) -> Result<EventVocabulary, StepObservationError> {
        let mut constructors = BTreeMap::<String, Vec<Sort>>::new();
        for spec in specs {
            let mut vars = BTreeMap::new();
            collect_variables(&spec.pre, &mut vars)?;
            if let Some(post) = &spec.post {
                collect_variables(post, &mut vars)?;
            }
            let sorts = spec
                .payload
                .iter()
                .map(|name| {
                    vars.get(name)
                        .cloned()
                        .ok_or_else(|| StepObservationError::MissingPayload(name.clone()))
                })
                .collect::<Result<Vec<_>, _>>()?;
            match constructors.get(&spec.constructor) {
                Some(old) if old != &sorts => {
                    return Err(StepObservationError::ConstructorSorts(
                        spec.constructor.clone(),
                    ));
                }
                None => {
                    constructors.insert(spec.constructor.clone(), sorts);
                }
                _ => {}
            }
        }
        EventVocabulary::new(
            constructors
                .into_iter()
                .map(|(name, payload_sorts)| Constructor {
                    name,
                    payload_sorts,
                })
                .collect(),
        )
        .map_err(|error| StepObservationError::ConstructorSorts(error.to_string()))
    }
}

fn collect_variables(
    pattern: &Pattern,
    vars: &mut BTreeMap<String, Sort>,
) -> Result<(), StepObservationError> {
    match pattern {
        Pattern::Variable(var) => {
            if var.kind != VariableKind::Element {
                return Err(StepObservationError::UnsupportedPattern(var.name.clone()));
            }
            if var.name.contains('!') {
                return Err(StepObservationError::ReservedVariable(var.name.clone()));
            }
            if let Some(old) = vars.insert(var.name.clone(), var.sort.clone())
                && old != var.sort
            {
                return Err(StepObservationError::VariableSort(var.name.clone()));
            }
        }
        Pattern::Application { arguments, .. } => {
            for child in arguments {
                collect_variables(child, vars)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn internal_sort(sort: &Sort) -> Option<InternalSort> {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => {
            Some(InternalSort::simple(name.as_str()))
        }
        _ => None,
    }
}

fn validate_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
) -> Result<(), StepObservationError> {
    validate_node(definition, pattern, None)?;
    let term = definition
        .admit_unverified(pattern, &[])
        .internalize_term()
        .map_err(|error| StepObservationError::Internalization(error.to_string()))?;
    if term.sort() != InternalSort::simple("SortGeneratedTopCell") {
        return Err(StepObservationError::Internalization(
            "configuration sort".into(),
        ));
    }
    Ok(())
}

fn validate_node(
    definition: &BackendDefinition,
    pattern: &Pattern,
    expected: Option<&InternalSort>,
) -> Result<(), StepObservationError> {
    match pattern {
        Pattern::Variable(var) => {
            if var.kind != VariableKind::Element {
                return Err(StepObservationError::UnsupportedPattern(var.name.clone()));
            }
            if var.name.contains('!') {
                return Err(StepObservationError::ReservedVariable(var.name.clone()));
            }
            if expected.is_some_and(|sort| internal_sort(&var.sort).as_ref() != Some(sort)) {
                return Err(StepObservationError::VariableSort(var.name.clone()));
            }
        }
        Pattern::DomainValue { sort, value } => {
            if !domain_value_identity_safe(definition, sort, value.as_bytes()) {
                return Err(StepObservationError::NonCanonicalValue(format!(
                    "{value:?}"
                )));
            }
            if expected.is_some_and(|expected| internal_sort(sort).as_ref() != Some(expected)) {
                return Err(StepObservationError::VariableSort("domain value".into()));
            }
        }
        Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
            let [source, target] = symbol.sort_parameters.as_slice() else {
                return Err(StepObservationError::Internalization(
                    "injection sorts".into(),
                ));
            };
            if arguments.len() != 1 {
                return Err(StepObservationError::Internalization(
                    "injection arity".into(),
                ));
            }
            if !strict_injection_sorts(definition, source, target) {
                return Err(StepObservationError::VariableSort(
                    "injection must have a strict subsort source".into(),
                ));
            }
            if expected.is_some_and(|sort| internal_sort(target).as_ref() != Some(sort)) {
                return Err(StepObservationError::VariableSort(
                    "injection target".into(),
                ));
            }
            let source = internal_sort(source)
                .ok_or_else(|| StepObservationError::Internalization("injection source".into()))?;
            validate_node(definition, &arguments[0], Some(&source))?;
        }
        Pattern::Application { symbol, arguments } => {
            let backend_symbol = definition
                .symbols()
                .get(symbol.name.as_str())
                .ok_or_else(|| StepObservationError::Internalization(symbol.name.clone()))?;
            if !free_constructor(backend_symbol) {
                return Err(StepObservationError::NonFreeSymbol(symbol.name.clone()));
            }
            if expected.is_some_and(|sort| backend_symbol.result_sort != *sort) {
                return Err(StepObservationError::VariableSort(symbol.name.clone()));
            }
            if arguments.len() != backend_symbol.argument_sorts.len() {
                return Err(StepObservationError::Internalization(symbol.name.clone()));
            }
            for (arg, sort) in arguments.iter().zip(&backend_symbol.argument_sorts) {
                validate_node(definition, arg, Some(sort))?;
            }
        }
        _ => {
            return Err(StepObservationError::UnsupportedPattern(format!(
                "{pattern:?}"
            )));
        }
    }
    Ok(())
}

fn is_injection(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Application { symbol, .. } if symbol.name == "inj")
}

/// The sort of `pattern` when its syntax fixes it: a variable, a domain value, an injection's
/// target, or an application of a symbol without sort variables. `None` otherwise.
fn determined_sort(definition: &BackendDefinition, pattern: &Pattern) -> Option<InternalSort> {
    match pattern {
        Pattern::Variable(var) => internal_sort(&var.sort),
        Pattern::DomainValue { sort, .. } => internal_sort(sort),
        Pattern::Application { symbol, .. } if symbol.name == "inj" => {
            match symbol.sort_parameters.as_slice() {
                [_, target] => internal_sort(target),
                _ => None,
            }
        }
        Pattern::Application { symbol, .. } => definition
            .symbols()
            .get(symbol.name.as_str())
            .filter(|backend| {
                backend.sort_variables.is_empty() && symbol.sort_parameters.is_empty()
            })
            .map(|backend| backend.result_sort.clone()),
        _ => None,
    }
}

/// Whether `pattern` is a sort injection in k-rust's normal form (TV-01 fix 1, review R1-F1):
/// one argument, a proper subsort source (`strict_injection_sorts`), an argument whose sort is
/// determined and equal to the source, and an argument that is not itself an injection. k-rust
/// builds only such injections: `Term::injection` collapses a nested pair
/// (`term.rs:893-907`), `inject_to_sort` returns the bare term when the sorts are equal
/// (`matching/mod.rs:2342`, `builtin/substitution.rs:1172`). Internalization admits an identity
/// injection (`check_subsort` is reflexive) and does not sort-check an injection's argument
/// (`definition.rs:2474-2490`), so a test may write `inj{S,S}(t)`, which the matcher keeps
/// apart from `t` although `inj{S,S}(t) = t` in K's semantics. Such a term is neither a value
/// nor admissible test input.
pub(crate) fn canonical_injection(definition: &BackendDefinition, pattern: &Pattern) -> bool {
    let Pattern::Application { symbol, arguments } = pattern else {
        return false;
    };
    let ([source, target], [argument]) = (symbol.sort_parameters.as_slice(), arguments.as_slice())
    else {
        return false;
    };
    symbol.name == "inj"
        && strict_injection_sorts(definition, source, target)
        && !is_injection(argument)
        && internal_sort(source).is_some_and(|source| {
            determined_sort(definition, argument).is_some_and(|sort| sort == source)
        })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepPresence {
    Certain(Vec<Pattern>),
    Conditional(Vec<Pattern>, Vec<TermRelation>),
    Absent,
    Undecided,
}

pub struct ObservationDecider<'a> {
    definition: &'a BackendDefinition,
    solver: &'a dyn SmtSolver,
    inhabitation: Inhabitation,
    relations: BackendRelations<'a>,
}

impl<'a> ObservationDecider<'a> {
    pub fn new(
        definition: &'a BackendDefinition,
        solver: &'a dyn SmtSolver,
        initial_state: &Pattern,
    ) -> Self {
        Self {
            definition,
            solver,
            inhabitation: Inhabitation::of(definition),
            relations: BackendRelations::shared(definition, solver, initial_state),
        }
    }
    /// Whether `term` is a value that no definition can change: variables, domain values with a
    /// trusted injective codec, free constructors, and sort injections in k-rust's normal form
    /// ([`canonical_injection`]). Anything else, including an identity or nested injection, is
    /// not (TV-01 and its fix 1, review R1-F1).
    pub fn definition_independent(&self, term: &Pattern) -> bool {
        match term {
            Pattern::Variable(_) => true,
            Pattern::DomainValue { sort, value } => {
                domain_value_identity_safe(self.definition, sort, value.as_bytes())
            }
            Pattern::Application { arguments, .. } if is_injection(term) => {
                canonical_injection(self.definition, term)
                    && arguments.iter().all(|arg| self.definition_independent(arg))
            }
            Pattern::Application { symbol, arguments } => {
                self.definition
                    .symbols()
                    .get(symbol.name.as_str())
                    .is_some_and(|s| free_constructor(s))
                    && arguments.iter().all(|arg| self.definition_independent(arg))
            }
            _ => false,
        }
    }
    pub(crate) fn shared_leaf_feasibility(
        &self,
        state: &serde_json::Value,
    ) -> crate::feasibility::LeafFeasibility {
        crate::feasibility::shared_leaf_feasibility(
            self.definition,
            self.solver,
            &self.inhabitation,
            state,
        )
    }
    pub fn classify_step(
        &self,
        spec: &StepEventSpec,
        pre: &Pattern,
        post: Option<&Pattern>,
        path: &PathInput,
    ) -> StepPresence {
        if contains_non_strict_injection(self.definition, &spec.pre)
            || spec
                .post
                .as_ref()
                .is_some_and(|post| contains_non_strict_injection(self.definition, post))
            || contains_non_strict_injection(self.definition, pre)
            || post.is_some_and(|post| contains_non_strict_injection(self.definition, post))
        {
            return StepPresence::Undecided;
        }
        let mut walk = Walk::default();
        walk.pair(self.definition, &spec.pre, pre);
        if let Some(pattern) = &spec.post {
            if let Some(post) = post {
                walk.pair(self.definition, pattern, post);
            } else {
                walk.undecided = true;
            }
        }
        if walk.absent {
            return StepPresence::Absent;
        }
        if walk.undecided {
            return StepPresence::Undecided;
        }
        let mut relations = Vec::new();
        for (left, right, deferred) in &walk.pairs {
            let left = if *deferred {
                let Some(left) = substitute_pattern(left, &walk.bindings) else {
                    return StepPresence::Undecided;
                };
                left
            } else {
                left.clone()
            };
            // Both terms are subterms of states of one request, where one decoded name is one
            // variable (variable identity), so identical terms are equal on every instance.
            let decision = if left == *right
                && !crate::feasibility::contains_untrusted_domain_value(self.definition, &left)
            {
                RelationDecision::Equal
            } else {
                self.relations.relate(path, &[], &left, right)
            };
            match decision {
                RelationDecision::Equal => {}
                RelationDecision::EqualIf(more) => relations.extend(more),
                RelationDecision::Unequal => return StepPresence::Absent,
                RelationDecision::Indeterminate => return StepPresence::Undecided,
            }
        }
        relations.sort();
        relations.dedup();
        let Some(payload) = spec
            .payload
            .iter()
            .map(|name| walk.bindings.get(name).cloned())
            .collect::<Option<Vec<_>>>()
        else {
            return StepPresence::Undecided;
        };
        if relations.is_empty() {
            StepPresence::Certain(payload)
        } else if self.relations.feasible(path, &relations) == Feasibility::Unsat {
            StepPresence::Absent
        } else {
            StepPresence::Conditional(payload, relations)
        }
    }
}

fn substitute_pattern(pattern: &Pattern, bindings: &BTreeMap<String, Pattern>) -> Option<Pattern> {
    match pattern {
        Pattern::Variable(var) => bindings.get(&var.name).cloned(),
        Pattern::Application { symbol, arguments } => Some(Pattern::Application {
            symbol: symbol.clone(),
            arguments: arguments
                .iter()
                .map(|arg| substitute_pattern(arg, bindings))
                .collect::<Option<Vec<_>>>()?,
        }),
        Pattern::DomainValue { .. } => Some(pattern.clone()),
        _ => None,
    }
}

#[derive(Default)]
struct Walk {
    bindings: BTreeMap<String, Pattern>,
    pairs: Vec<(Pattern, Pattern, bool)>,
    absent: bool,
    undecided: bool,
}

impl Walk {
    fn pair(&mut self, definition: &BackendDefinition, pattern: &Pattern, state: &Pattern) {
        if self.absent {
            return;
        }
        if non_strict_injection_node(definition, pattern)
            || non_strict_injection_node(definition, state)
        {
            self.undecided = true;
            return;
        }
        if let Pattern::Variable(var) = pattern {
            if let Some(first) = self.bindings.get(&var.name) {
                self.pairs.push((first.clone(), state.clone(), false));
            } else {
                self.bindings.insert(var.name.clone(), state.clone());
            }
            return;
        }
        if matches!(state, Pattern::Variable(_)) {
            self.pairs.push((pattern.clone(), state.clone(), true));
            return;
        }
        match (pattern, state) {
            (
                Pattern::DomainValue {
                    sort: ps,
                    value: pv,
                },
                Pattern::DomainValue {
                    sort: ss,
                    value: sv,
                },
            ) => {
                if ps != ss
                    || !domain_value_identity_safe(definition, ps, pv.as_bytes())
                    || !domain_value_identity_safe(definition, ss, sv.as_bytes())
                {
                    self.undecided = true;
                } else if pv != sv {
                    self.absent = true;
                }
            }
            (
                Pattern::Application {
                    symbol: ps,
                    arguments: pa,
                },
                Pattern::Application {
                    symbol: ss,
                    arguments: sa,
                },
            ) if ps == ss && pa.len() == sa.len() => {
                if ps.name == "inj" || free_symbol(definition, &ps.name) {
                    for (p, s) in pa.iter().zip(sa) {
                        self.pair(definition, p, s);
                    }
                } else {
                    self.undecided = true;
                }
            }
            (
                Pattern::Application {
                    symbol: ps,
                    arguments: pa,
                },
                Pattern::Application {
                    symbol: ss,
                    arguments: sa,
                },
            ) if ps.name == "inj" && ss.name == "inj" && pa.len() == 1 && sa.len() == 1 => {
                let ([p_source, p_target], [s_source, s_target]) =
                    (ps.sort_parameters.as_slice(), ss.sort_parameters.as_slice())
                else {
                    self.undecided = true;
                    return;
                };
                if p_target != s_target {
                    self.undecided = true;
                    return;
                }
                let (Some(p_sort), Some(s_sort)) =
                    (internal_sort(p_source), internal_sort(s_source))
                else {
                    self.undecided = true;
                    return;
                };
                if definition
                    .sort_graph()
                    .check_subsort(&s_sort, &p_sort)
                    .unwrap_or(false)
                {
                    if p_sort == s_sort {
                        self.pair(definition, &pa[0], &sa[0]);
                    } else {
                        self.pair(
                            definition,
                            &pa[0],
                            &Pattern::Application {
                                symbol: k_rust::kore::ast::Symbol {
                                    name: "inj".into(),
                                    sort_parameters: vec![s_source.clone(), p_source.clone()],
                                },
                                arguments: vec![sa[0].clone()],
                            },
                        );
                    }
                } else if definition
                    .sort_graph()
                    .check_subsort(&p_sort, &s_sort)
                    .unwrap_or(false)
                {
                    if matches!(sa[0], Pattern::Variable(_)) {
                        self.pairs.push((pattern.clone(), state.clone(), true));
                    } else if free_top(definition, &sa[0], &s_sort) {
                        self.absent = true;
                    } else {
                        self.undecided = true;
                    }
                } else if free_top(definition, &sa[0], &s_sort)
                    || free_top(definition, &pa[0], &p_sort)
                    || closures_disjoint(definition, &p_sort, &s_sort)
                {
                    self.absent = true;
                } else {
                    self.undecided = true;
                }
            }
            (Pattern::Application { symbol: ps, .. }, Pattern::Application { symbol: ss, .. })
                if (free_symbol(definition, &ps.name)
                    && (free_symbol(definition, &ss.name) || ss.name == "inj"))
                    || (ps.name == "inj" && free_symbol(definition, &ss.name)) =>
            {
                self.absent = true;
            }
            _ => self.undecided = true,
        }
    }
}

fn free_symbol(definition: &BackendDefinition, name: &str) -> bool {
    definition
        .symbols()
        .get(name)
        .is_some_and(|symbol| free_constructor(symbol))
}
fn free_top(definition: &BackendDefinition, pattern: &Pattern, sort: &InternalSort) -> bool {
    matches!(pattern, Pattern::Application { symbol, .. }
        if definition.symbols().get(symbol.name.as_str()).is_some_and(|head|
            free_constructor(head) && head.result_sort == *sort))
}

fn closures_disjoint(
    definition: &BackendDefinition,
    left: &InternalSort,
    right: &InternalSort,
) -> bool {
    !definition.sorts().keys().any(|sort| {
        let sort = InternalSort::simple(sort.as_ref());
        definition
            .sort_graph()
            .check_subsort(&sort, left)
            .unwrap_or(false)
            && definition
                .sort_graph()
                .check_subsort(&sort, right)
                .unwrap_or(false)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{NativeValidator, support};
    use k_rust::backend::BackendOptions;
    use k_rust::kompile::CompileOptions;

    #[test]
    fn generated_cells_and_k_sequence_are_free_constructors() {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
        let side = validator.compile_baseline().expect("symmem compiles");
        let mut backend = Backend::new(
            &side.artifacts().definition_kore,
            "SYMMEM",
            BackendOptions::default(),
        )
        .expect("backend");
        backend
            .with_solver(None, |definition, _| -> Result<(), BackendError> {
                for name in [
                    "Lbl'-LT-'generatedTop'-GT-'",
                    "Lbl'-LT-'k'-GT-'",
                    "Lbl'-LT-'generatedCounter'-GT-'",
                    "kseq",
                    "dotk",
                ] {
                    let symbol = definition
                        .symbols()
                        .get(name)
                        .expect("declared constructor");
                    assert!(
                        free_constructor(symbol),
                        "{name} must be a free constructor"
                    );
                }
                Ok(())
            })
            .expect("definition");
    }

    #[test]
    fn same_non_free_head_does_not_decompose_to_an_absence() {
        let validator =
            NativeValidator::bind(support::load("residue.k"), CompileOptions::default());
        let side = validator.compile_baseline().expect("residue compiles");
        let mut backend = Backend::new(
            &side.artifacts().definition_kore,
            "RESIDUE",
            BackendOptions::default(),
        )
        .expect("backend");
        backend
            .with_solver(None, |definition, _| -> Result<(), BackendError> {
                let mut walk = Walk::default();
                walk.pair(
                    definition,
                    &support::app("Lblf", vec![support::int(1)]),
                    &support::app("Lblf", vec![support::int(2)]),
                );
                assert!(walk.undecided);
                assert!(!walk.absent);
                Ok(())
            })
            .expect("definition");
    }
}
