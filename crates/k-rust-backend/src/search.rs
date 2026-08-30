//! Reachability search over the symbolic execution tree.

use std::collections::{BTreeSet, VecDeque};

use crate::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rewrite::{
        AppliedRule, IndeterminateReason, Pattern, RemainderBranch, RewriteResult, TraceEntry,
        TraceKind, Truth, predicates_truth, rewrite_step_with_options, substitute_predicates,
    },
    rule::Predicate,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver},
    substitution::{Substitution, compose, substitute},
};

/// Which nodes in the execution tree are returned by a search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SearchType {
    /// Configurations reached in exactly one semantic rewrite step.
    One,
    /// Configurations which cannot be rewritten further.
    Final,
    /// Every reachable configuration, including the initial configuration.
    Star,
    /// Every configuration reached in at least one semantic rewrite step.
    Plus,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SearchOptions {
    pub search_type: SearchType,
    pub max_depth: u64,
    pub max_breadth: Option<usize>,
    pub max_results: Option<usize>,
    pub max_simplification_iterations: usize,
}

impl Default for SearchOptions {
    fn default() -> Self {
        Self {
            search_type: SearchType::Final,
            max_depth: u64::MAX,
            max_breadth: None,
            max_results: None,
            max_simplification_iterations: 100,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchState {
    pub pattern: Pattern,
    pub depth: u64,
    /// One valid path to this pattern; when paths converge, which witness survives is unspecified.
    pub trace: Vec<TraceEntry>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncompleteSearch {
    ResultBound,
    DepthBound(SearchState),
    BreadthBound(Vec<SearchState>),
    Indeterminate {
        state: SearchState,
        reason: IndeterminateReason,
    },
    Cancelled(SearchState),
    Simplification {
        state: SearchState,
        error: SimplificationError,
    },
    Match {
        state: SearchState,
        substitution: Substitution,
        remainder: Vec<(crate::term::Term, crate::term::Term)>,
    },
    Smt {
        state: SearchState,
        error: SmtError,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchResult {
    pub states: Vec<SearchState>,
    pub effects: Vec<BuiltinEffect>,
    pub incomplete: Vec<IncompleteSearch>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchMatch {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
    pub state: SearchState,
}

/// The condition under which a subject is an instance of a search pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternMatch {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
}

/// A pattern match which could not be decided by the available simplifier and solver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternMatchError {
    Indeterminate {
        substitution: Substitution,
        remainder: Vec<(crate::term::Term, crate::term::Term)>,
    },
    Simplification(SimplificationError),
    Smt(SmtError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternSearchResult {
    pub matches: Vec<SearchMatch>,
    pub effects: Vec<BuiltinEffect>,
    pub incomplete: Vec<IncompleteSearch>,
}

/// Match a constrained pattern against each alternative in a disjunction.
pub fn match_disjunction(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
) -> Result<Vec<PatternMatch>, PatternMatchError> {
    match_disjunction_using(
        definition,
        target,
        subjects,
        SimplificationOptions::default(),
        &NoSolver,
        true,
    )
}

/// Match a constrained pattern against each alternative using the supplied SMT solver.
pub fn match_disjunction_with_solver(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Vec<PatternMatch>, PatternMatchError> {
    match_disjunction_using(definition, target, subjects, options, solver, false)
}

fn match_disjunction_using(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    retain_unknown: bool,
) -> Result<Vec<PatternMatch>, PatternMatchError> {
    let output_variables = pattern_variables(target);
    let mut matches = Vec::new();
    for subject in subjects {
        let Some(found) = match_pattern_with_variables(
            definition,
            target,
            subject,
            &output_variables,
            options,
            solver,
            retain_unknown,
        )?
        else {
            continue;
        };
        if !matches.contains(&found) {
            matches.push(found);
        }
    }
    Ok(matches)
}

pub fn search_graph(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
) -> SearchResult {
    search_graph_with_solver(definition, initial, options, &NoSolver)
}

pub fn search_graph_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> SearchResult {
    search_graph_with_solver_and_observer(definition, initial, options, solver, |_| {})
}

pub fn search_graph_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    mut observe: impl FnMut(&BuiltinEffect),
) -> SearchResult {
    let mut pending = VecDeque::from([SearchState {
        pattern: initial,
        depth: 0,
        trace: Vec::new(),
    }]);
    let mut states = Vec::new();
    let mut effects = Vec::new();
    let mut incomplete = Vec::new();
    let mut fresh_counter = 0;

    if options.max_breadth == Some(0) {
        incomplete.push(IncompleteSearch::BreadthBound(pending.drain(..).collect()));
        return SearchResult {
            states,
            effects,
            incomplete,
        };
    }

    if options.max_results == Some(0) {
        incomplete.push(IncompleteSearch::ResultBound);
        return SearchResult {
            states,
            effects,
            incomplete,
        };
    }

    while let Some(mut state) = pending.pop_front() {
        match simplify_predicates_with_solver(
            definition,
            &state.pattern.constraints,
            &[],
            simplification_options(options),
            solver,
        ) {
            Ok(constraints) => state.pattern.constraints = constraints,
            Err(error) => {
                incomplete.push(simplification_incomplete(state, error));
                continue;
            }
        }
        match simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            simplification_options(options),
            solver,
        ) {
            Ok(simplified) => {
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.constraints);
                record_effects(&mut effects, simplified.effects, &mut observe);
                state
                    .trace
                    .extend(
                        simplified
                            .applied_rules
                            .into_iter()
                            .map(|unique_id| TraceEntry {
                                depth: state.depth,
                                kind: TraceKind::Simplification,
                                label: None,
                                unique_id,
                            }),
                    );
            }
            Err(error) => {
                incomplete.push(simplification_incomplete(state, error));
                continue;
            }
        }

        if selects_reachable_state(options.search_type, state.depth)
            && push_unique(&mut states, state.clone(), options.max_results)
        {
            if !pending.is_empty()
                || state_may_expand(definition, &state, options, &mut fresh_counter, solver)
            {
                incomplete.push(IncompleteSearch::ResultBound);
            }
            break;
        }
        if options.search_type == SearchType::One && state.depth == 1 {
            continue;
        }
        let at_depth_bound = state.depth >= options.max_depth;
        if at_depth_bound && options.search_type != SearchType::Final {
            incomplete.push(IncompleteSearch::DepthBound(state));
            continue;
        }

        let rewrite = rewrite_step_with_options(
            definition,
            &state.pattern,
            &mut fresh_counter,
            simplification_options(options),
            solver,
        );
        if at_depth_bound {
            match rewrite {
                RewriteResult::Stuck(pattern) => {
                    state.pattern = pattern;
                    if push_unique(&mut states, state, options.max_results) {
                        if !pending.is_empty() {
                            incomplete.push(IncompleteSearch::ResultBound);
                        }
                        break;
                    }
                }
                RewriteResult::Trivial(_) | RewriteResult::Vacuous(_) => {}
                RewriteResult::Indeterminate { pattern, reason } => {
                    state.pattern = pattern;
                    incomplete.push(rewrite_incomplete(state, reason));
                }
                RewriteResult::Finished(_) | RewriteResult::Branch { .. } => {
                    incomplete.push(IncompleteSearch::DepthBound(state));
                }
            }
            continue;
        }

        match rewrite {
            RewriteResult::Stuck(pattern) => {
                state.pattern = pattern;
                if options.search_type == SearchType::Final
                    && push_unique(&mut states, state, options.max_results)
                {
                    if !pending.is_empty() {
                        incomplete.push(IncompleteSearch::ResultBound);
                    }
                    break;
                }
            }
            RewriteResult::Trivial(_) | RewriteResult::Vacuous(_) => {}
            RewriteResult::Indeterminate { pattern, reason } => {
                state.pattern = pattern;
                incomplete.push(rewrite_incomplete(state, reason));
            }
            RewriteResult::Finished(applied) => {
                record_effects(&mut effects, applied.effects.iter().cloned(), &mut observe);
                pending.push_back(next_state(state.depth, state.trace, applied));
                if search_breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth) {
                    break;
                }
            }
            RewriteResult::Branch {
                branches,
                remainder,
                ..
            } => {
                for applied in branches {
                    record_effects(&mut effects, applied.effects.iter().cloned(), &mut observe);
                    pending.push_back(next_state(state.depth, state.trace.clone(), applied));
                }
                if let Some(remainder) = remainder {
                    pending.push_back(remaining_state(state.depth, state.trace, remainder));
                }
                if search_breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth) {
                    break;
                }
            }
        }
    }

    SearchResult {
        states,
        effects,
        incomplete,
    }
}

fn search_breadth_exceeded(
    pending: &mut VecDeque<SearchState>,
    incomplete: &mut Vec<IncompleteSearch>,
    max_breadth: Option<usize>,
) -> bool {
    if !max_breadth.is_some_and(|bound| pending.len() > bound) {
        return false;
    }
    incomplete.push(IncompleteSearch::BreadthBound(pending.drain(..).collect()));
    true
}

/// Search the selected execution states for instances of `target`.
pub fn search_pattern(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
) -> PatternSearchResult {
    search_pattern_with_solver(definition, initial, target, options, &NoSolver)
}

pub fn search_pattern_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> PatternSearchResult {
    let requested_bound = options.max_results;
    if requested_bound == Some(0) {
        return PatternSearchResult {
            matches: Vec::new(),
            effects: Vec::new(),
            incomplete: vec![IncompleteSearch::ResultBound],
        };
    }
    let graph = search_graph_with_solver(
        definition,
        initial,
        SearchOptions {
            max_results: None,
            ..options
        },
        solver,
    );
    let mut matches = Vec::new();
    let mut incomplete = graph.incomplete;
    let output_variables = pattern_variables(target);

    let mut remaining = graph.states.into_iter();
    while let Some(state) = remaining.next() {
        let found = match match_pattern_with_variables(
            definition,
            target,
            &state.pattern,
            &output_variables,
            simplification_options(options),
            solver,
            false,
        ) {
            Ok(Some(found)) => found,
            Ok(None) => continue,
            Err(PatternMatchError::Indeterminate {
                substitution,
                remainder,
            }) => {
                incomplete.push(IncompleteSearch::Match {
                    state,
                    substitution,
                    remainder,
                });
                continue;
            }
            Err(PatternMatchError::Simplification(error)) => {
                incomplete.push(simplification_incomplete(state, error));
                continue;
            }
            Err(PatternMatchError::Smt(error)) => {
                incomplete.push(IncompleteSearch::Smt { state, error });
                continue;
            }
        };

        let found = SearchMatch {
            substitution: found.substitution,
            constraints: found.constraints,
            state,
        };
        if !matches.iter().any(|existing: &SearchMatch| {
            existing.substitution == found.substitution && existing.constraints == found.constraints
        }) {
            matches.push(found);
        }
        if requested_bound.is_some_and(|bound| matches.len() >= bound) {
            // The bound only truncates the answer when candidate states were left unchecked.
            if remaining.len() > 0 {
                incomplete.push(IncompleteSearch::ResultBound);
            }
            break;
        }
    }

    PatternSearchResult {
        matches,
        effects: graph.effects,
        incomplete,
    }
}

fn simplification_incomplete(state: SearchState, error: SimplificationError) -> IncompleteSearch {
    match error {
        SimplificationError::Cancelled => IncompleteSearch::Cancelled(state),
        error => IncompleteSearch::Simplification { state, error },
    }
}

fn rewrite_incomplete(state: SearchState, reason: IndeterminateReason) -> IncompleteSearch {
    match reason {
        IndeterminateReason::Simplification { error, .. } => {
            simplification_incomplete(state, error)
        }
        reason => IncompleteSearch::Indeterminate { state, reason },
    }
}

fn pattern_variables(pattern: &Pattern) -> BTreeSet<crate::term::Variable> {
    pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(Predicate::free_variables),
        )
        .collect()
}

fn match_pattern_with_variables(
    definition: &BackendDefinition,
    target: &Pattern,
    subject: &Pattern,
    output_variables: &BTreeSet<crate::term::Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    retain_unknown: bool,
) -> Result<Option<PatternMatch>, PatternMatchError> {
    let substitution = match match_terms_in_definition(
        MatchMode::Implies,
        definition,
        &target.term,
        &subject.term,
    ) {
        MatchResult::Success(substitution) => substitution,
        MatchResult::Failed(_) => return Ok(None),
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            return Err(PatternMatchError::Indeterminate {
                substitution,
                remainder,
            });
        }
    };

    let mut constraints = subject.constraints.clone();
    constraints.extend(substitute_predicates(&target.constraints, &substitution));
    let (substitution, constraints) =
        normalize_match_condition(substitution, constraints, output_variables);
    let constraints =
        simplify_predicates_with_solver(definition, &constraints, &[], options, solver)
            .map_err(PatternMatchError::Simplification)?;
    match predicates_truth(&constraints) {
        Truth::False => return Ok(None),
        Truth::True => {}
        Truth::Unknown if retain_unknown => {}
        Truth::Unknown => match solver.is_sat(&constraints, &substitution) {
            Ok(Satisfiability::Unsat) => return Ok(None),
            Ok(Satisfiability::Sat) => {}
            Ok(Satisfiability::Unknown(reason)) => {
                return Err(PatternMatchError::Smt(SmtError::Unknown(reason)));
            }
            Err(error) => return Err(PatternMatchError::Smt(error)),
        },
    }

    Ok(Some(PatternMatch {
        substitution,
        constraints,
    }))
}

fn normalize_match_condition(
    output: Substitution,
    mut constraints: Vec<Predicate>,
    output_variables: &BTreeSet<crate::term::Variable>,
) -> (Substitution, Vec<Predicate>) {
    let mut solved = Substitution::new();
    loop {
        let mut binding = None;
        for (index, constraint) in constraints.iter().enumerate() {
            let Predicate::Equals(left, right) = constraint else {
                continue;
            };
            let left = substitute(left, &solved);
            let right = substitute(right, &solved);
            if left == right {
                binding = Some((index, None));
                break;
            }
            let candidate = match (left.kind(), right.kind()) {
                (crate::term::TermKind::Variable(variable), _)
                    if !right.attributes().variables.contains(variable) =>
                {
                    Some((variable.clone(), right))
                }
                (_, crate::term::TermKind::Variable(variable))
                    if !left.attributes().variables.contains(variable) =>
                {
                    Some((variable.clone(), left))
                }
                _ => None,
            };
            if let Some(candidate) = candidate {
                binding = Some((index, Some(candidate)));
                break;
            }
        }
        let Some((index, binding)) = binding else {
            break;
        };
        constraints.remove(index);
        let Some((variable, value)) = binding else {
            continue;
        };
        let binding = Substitution::from([(variable, value)]);
        solved = compose(&binding, &solved);
        constraints = substitute_predicates(&constraints, &binding);
    }

    let mut output = compose(&solved, &output);
    output.retain(|variable, _| output_variables.contains(variable));
    let constraints = substitute_predicates(&constraints, &solved);
    (output, constraints)
}

fn simplification_options(options: SearchOptions) -> SimplificationOptions {
    SimplificationOptions {
        max_iterations: options.max_simplification_iterations,
    }
}

fn selects_reachable_state(search_type: SearchType, depth: u64) -> bool {
    match search_type {
        SearchType::Star => true,
        SearchType::Plus => depth > 0,
        SearchType::One => depth == 1,
        SearchType::Final => false,
    }
}

/// Whether a state that just satisfied the result bound could still contribute unexplored
/// successors. Stopping at the bound is only a truncation when such work remains; a search
/// that is exhausted exactly at the bound is complete.
fn state_may_expand(
    definition: &BackendDefinition,
    state: &SearchState,
    options: SearchOptions,
    fresh_counter: &mut u64,
    solver: &dyn SmtSolver,
) -> bool {
    if options.search_type == SearchType::One && state.depth == 1 {
        return false;
    }
    if state.depth >= options.max_depth {
        // Continuing would have reported a depth bound; the frontier is not exhausted.
        return true;
    }
    !matches!(
        rewrite_step_with_options(
            definition,
            &state.pattern,
            fresh_counter,
            simplification_options(options),
            solver,
        ),
        RewriteResult::Stuck(_) | RewriteResult::Trivial(_) | RewriteResult::Vacuous(_)
    )
}

/// Returns whether the requested solution bound has been reached.
fn push_unique(
    states: &mut Vec<SearchState>,
    state: SearchState,
    max_results: Option<usize>,
) -> bool {
    if !states.iter().any(|found| found.pattern == state.pattern) {
        states.push(state);
    }
    max_results.is_some_and(|limit| states.len() >= limit)
}

fn record_effects(
    recorded: &mut Vec<BuiltinEffect>,
    effects: impl IntoIterator<Item = BuiltinEffect>,
    observe: &mut impl FnMut(&BuiltinEffect),
) {
    for effect in effects {
        observe(&effect);
        recorded.push(effect);
    }
}

fn next_state(depth: u64, mut trace: Vec<TraceEntry>, applied: AppliedRule) -> SearchState {
    trace.push(TraceEntry {
        depth: depth + 1,
        kind: TraceKind::Rewrite,
        label: applied.label,
        unique_id: applied.unique_id,
    });
    SearchState {
        pattern: applied.pattern,
        depth: depth + 1,
        trace,
    }
}

fn remaining_state(
    depth: u64,
    mut trace: Vec<TraceEntry>,
    remainder: RemainderBranch,
) -> SearchState {
    trace.push(TraceEntry {
        depth,
        kind: TraceKind::Remainder,
        label: None,
        unique_id: remainder.rule_ids.join(","),
    });
    SearchState {
        pattern: remainder.pattern,
        depth,
        trace,
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, sync::Arc};

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
    use proptest::prelude::*;

    use super::*;
    use crate::term::{Sort, Symbol, Term, TermKind, Variable};

    #[test]
    fn cancellation_is_not_reported_as_a_simplifier_failure() {
        let definition = definition();
        let token = crate::cancellation::CancellationToken::new();
        token.cancel();
        let result = token
            .scope(|| search_graph(&definition, initial(&definition), SearchOptions::default()));

        assert!(result.states.is_empty());
        let [IncompleteSearch::Cancelled(state)] = result.incomplete.as_slice() else {
            panic!("expected cancellation, found {:?}", result.incomplete);
        };
        assert_eq!(state.depth, 0);
    }

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} []
                symbol initial{}() : SortS{} [constructor{}()]
                symbol next1{}() : SortS{} [constructor{}()]
                symbol next2{}() : SortS{} [constructor{}()]
                symbol final1{}() : SortS{} [constructor{}()]
                symbol final2{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next1{}()
                ) [label{}("initial-next1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next2{}()
                ) [label{}("initial-next2")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next1{}(), \top{SortS{}}()),
                    final1{}()
                ) [label{}("next1-final1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next2{}(), \top{SortS{}}()),
                    final2{}()
                ) [label{}("next2-final2")]
            endmodule []"#,
        )
        .expect("search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("search definition should internalize")
    }

    fn converging_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} []
                symbol initial{}() : SortS{} [constructor{}()]
                symbol next1{}() : SortS{} [constructor{}()]
                symbol next2{}() : SortS{} [constructor{}()]
                symbol final1{}() : SortS{} [constructor{}()]
                symbol final2{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next1{}()
                ) [label{}("initial-next1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next2{}()
                ) [label{}("initial-next2")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next1{}(), \top{SortS{}}()),
                    final1{}()
                ) [label{}("next1-final1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next2{}(), \top{SortS{}}()),
                    final1{}()
                ) [label{}("next2-final1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next2{}(), \top{SortS{}}()),
                    final2{}()
                ) [label{}("next2-final2")]
            endmodule []"#,
        )
        .expect("converging search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("converging search definition should internalize")
    }

    fn rewrite_simplification_failure_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} []
                symbol initial{}() : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                symbol expand{}(SortS{}) : SortS{} [function{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        expand{}(X:SortS{}),
                        \and{SortS{}}(
                            expand{}(expand{}(X:SortS{})),
                            \top{SortS{}}()
                        )
                    )
                ) [label{}("expand"), simplification{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        initial{}(),
                        \equals{SortS{}, SortS{}}(
                            expand{}(initial{}()),
                            initial{}()
                        )
                    ),
                    done{}()
                ) [label{}("conditional")]
            endmodule []"#,
        )
        .expect("search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("search definition should internalize")
    }

    #[test]
    fn rewrite_simplification_failure_is_classified_as_simplification() {
        let definition = rewrite_simplification_failure_definition();
        let result = search_graph(
            &definition,
            pattern(&definition, "initial{}()"),
            SearchOptions {
                max_simplification_iterations: 1,
                ..SearchOptions::default()
            },
        );

        assert!(matches!(
            result.incomplete.as_slice(),
            [IncompleteSearch::Simplification {
                error: SimplificationError::IterationLimit { .. }
                    | SimplificationError::PredicateIterationLimit { .. },
                ..
            }]
        ));
    }

    #[test]
    fn cancelled_rewrite_simplification_is_classified_as_cancellation() {
        let definition = definition();
        let state = SearchState {
            pattern: initial(&definition),
            depth: 0,
            trace: Vec::new(),
        };

        assert_eq!(
            rewrite_incomplete(
                state.clone(),
                IndeterminateReason::Simplification {
                    rule_id: Some("rule".into()),
                    error: SimplificationError::Cancelled,
                },
            ),
            IncompleteSearch::Cancelled(state)
        );
    }

    fn initial(definition: &BackendDefinition) -> Pattern {
        pattern(definition, "initial{}()")
    }

    fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
        Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(source).expect("search pattern should parse"),
                    &[],
                )
                .expect("search pattern should internalize"),
            constraints: Vec::new(),
        }
    }

    fn names(result: &SearchResult) -> BTreeSet<String> {
        result
            .states
            .iter()
            .map(|state| match state.pattern.term.kind() {
                TermKind::Application { symbol, .. } => symbol.name.to_string(),
                other => panic!("expected an application, found {other:?}"),
            })
            .collect()
    }

    fn state_name(state: &SearchState) -> String {
        match state.pattern.term.kind() {
            TermKind::Application { symbol, .. } => symbol.name.to_string(),
            other => panic!("expected an application, found {other:?}"),
        }
    }

    fn search_types() -> impl Strategy<Value = SearchType> {
        prop_oneof![
            Just(SearchType::One),
            Just(SearchType::Star),
            Just(SearchType::Plus),
            Just(SearchType::Final),
        ]
    }

    fn result_variable() -> Variable {
        Variable::new("Result", Sort::simple("SortS"))
    }

    fn pattern_result_names(result: &PatternSearchResult, variable: &Variable) -> BTreeSet<String> {
        result
            .matches
            .iter()
            .map(|found| match found.substitution[variable].kind() {
                TermKind::Application { symbol, .. } => symbol.name.to_string(),
                other => panic!("expected an application, found {other:?}"),
            })
            .collect()
    }

    proptest! {
        #[test]
        fn complete_result_bounded_state_search_agrees_with_unbounded_search(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = definition();
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_graph(&definition, initial(&definition), options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_graph(
                    &definition,
                    initial(&definition),
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(names(&bounded), names(&unbounded));
            }
        }

        #[test]
        fn complete_result_bounded_pattern_search_agrees_with_unbounded_search(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = definition();
            let result_variable = result_variable();
            let target = Pattern {
                term: Term::variable(result_variable.clone()),
                constraints: Vec::new(),
            };
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_pattern(&definition, initial(&definition), &target, options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_pattern(
                    &definition,
                    initial(&definition),
                    &target,
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(
                    pattern_result_names(&bounded, &result_variable),
                    pattern_result_names(&unbounded, &result_variable),
                );
            }
        }

        #[test]
        fn bounded_search_incompleteness_never_invents_states(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_breadth in 0_usize..=7,
            max_results in 0_usize..=7,
        ) {
            let definition = definition();
            let bounded = search_graph(
                &definition,
                initial(&definition),
                SearchOptions {
                    search_type,
                    max_depth,
                    max_breadth: Some(max_breadth),
                    max_results: Some(max_results),
                    ..SearchOptions::default()
                },
            );
            prop_assume!(!bounded.incomplete.is_empty());

            let selected = search_graph(
                &definition,
                initial(&definition),
                SearchOptions { search_type, ..SearchOptions::default() },
            );
            let closure = search_graph(
                &definition,
                initial(&definition),
                SearchOptions { search_type: SearchType::Star, ..SearchOptions::default() },
            );
            let selected_names = names(&selected);
            let closure_names = names(&closure);

            prop_assert!(names(&bounded).is_subset(&selected_names));
            for marker in &bounded.incomplete {
                match marker {
                    IncompleteSearch::DepthBound(state) => {
                        prop_assert!(closure_names.contains(&state_name(state)));
                    }
                    IncompleteSearch::BreadthBound(states) => {
                        for state in states {
                            prop_assert!(closure_names.contains(&state_name(state)));
                        }
                    }
                    IncompleteSearch::ResultBound => {}
                    other => prop_assert!(false, "unexpected marker for finite fixture: {other:?}"),
                }
            }
        }

        #[test]
        fn bounded_properties_hold_on_the_converging_fixture(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = converging_definition();
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_graph(&definition, initial(&definition), options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_graph(
                    &definition,
                    initial(&definition),
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(names(&bounded), names(&unbounded));
            }
        }
    }

    #[test]
    fn converging_paths_collapse_to_one_state_per_pattern() {
        let definition = converging_definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert_eq!(
            result
                .states
                .iter()
                .filter(|state| state_name(state) == "final1")
                .count(),
            1
        );
    }

    #[test]
    fn a_deduplicated_state_keeps_one_valid_trace() {
        let definition = converging_definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );
        let final1 = result
            .states
            .iter()
            .find(|state| state_name(state) == "final1")
            .expect("final1 should be reachable");
        let labels = final1
            .trace
            .iter()
            .filter(|entry| entry.kind == TraceKind::Rewrite)
            .map(|entry| entry.label.as_deref().expect("fixture rules have labels"))
            .collect::<Vec<_>>();

        assert!(
            labels == ["initial-next1", "next1-final1"]
                || labels == ["initial-next2", "next2-final1"],
            "unexpected witness: {labels:?}"
        );
    }

    #[test]
    fn search_traces_are_always_valid_paths() {
        for definition in [definition(), converging_definition()] {
            for search_type in [
                SearchType::One,
                SearchType::Star,
                SearchType::Plus,
                SearchType::Final,
            ] {
                let result = search_graph(
                    &definition,
                    initial(&definition),
                    SearchOptions {
                        search_type,
                        ..SearchOptions::default()
                    },
                );
                for state in result.states {
                    let mut current = "initial";
                    let mut rewrite_count = 0;
                    for entry in &state.trace {
                        if entry.kind != TraceKind::Rewrite {
                            continue;
                        }
                        let label = entry.label.as_deref().expect("fixture rules have labels");
                        current = match (current, label) {
                            ("initial", "initial-next1") => "next1",
                            ("initial", "initial-next2") => "next2",
                            ("next1", "next1-final1") => "final1",
                            ("next2", "next2-final1") => "final1",
                            ("next2", "next2-final2") => "final2",
                            edge => panic!("invalid trace edge {edge:?} in {:?}", state.trace),
                        };
                        rewrite_count += 1;
                    }
                    assert_eq!(rewrite_count, state.depth, "{:?}", state.trace);
                    assert_eq!(current, state_name(&state), "{:?}", state.trace);
                }
            }
        }
    }

    fn search(search_type: SearchType) -> SearchResult {
        let definition = definition();
        search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type,
                ..SearchOptions::default()
            },
        )
    }

    #[test]
    fn one_selects_exactly_one_step() {
        let result = search(SearchType::One);
        assert_eq!(
            names(&result),
            BTreeSet::from(["next1".into(), "next2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn star_selects_the_reflexive_transitive_closure() {
        let result = search(SearchType::Star);
        assert_eq!(
            names(&result),
            BTreeSet::from([
                "initial".into(),
                "next1".into(),
                "next2".into(),
                "final1".into(),
                "final2".into(),
            ])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn plus_selects_the_strict_transitive_closure() {
        let result = search(SearchType::Plus);
        assert_eq!(
            names(&result),
            BTreeSet::from([
                "next1".into(),
                "next2".into(),
                "final1".into(),
                "final2".into(),
            ])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn final_selects_only_irreducible_configurations() {
        let result = search(SearchType::Final);
        assert_eq!(
            names(&result),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn result_bound_stops_the_breadth_first_search() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::One,
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(names(&result), BTreeSet::from(["next1".into()]));
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn exhausting_the_graph_exactly_at_the_result_bound_is_complete() {
        let definition = definition();
        for (search_type, bound, expected) in [
            (SearchType::One, 2, ["next1", "next2"].as_slice()),
            (SearchType::Final, 2, ["final1", "final2"].as_slice()),
            (
                SearchType::Star,
                5,
                ["initial", "next1", "next2", "final1", "final2"].as_slice(),
            ),
        ] {
            let result = search_graph(
                &definition,
                initial(&definition),
                SearchOptions {
                    search_type,
                    max_results: Some(bound),
                    ..SearchOptions::default()
                },
            );
            assert_eq!(
                names(&result),
                expected.iter().map(|name| (*name).to_owned()).collect(),
                "{search_type:?}"
            );
            assert!(result.incomplete.is_empty(), "{search_type:?}");
        }
    }

    #[test]
    fn result_bound_at_the_depth_bound_still_reports_truncation() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Star,
                max_depth: 1,
                max_results: Some(3),
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["initial".into(), "next1".into(), "next2".into()])
        );
        // `next1` was already reported as depth-bound before the result bound fired on `next2`.
        assert!(
            matches!(
                result.incomplete.as_slice(),
                [
                    IncompleteSearch::DepthBound(_),
                    IncompleteSearch::ResultBound
                ]
            ),
            "{:?}",
            result.incomplete
        );
    }

    #[test]
    fn zero_result_bounds_are_reported_as_incomplete() {
        let definition = definition();
        let options = SearchOptions {
            search_type: SearchType::Star,
            max_results: Some(0),
            ..SearchOptions::default()
        };
        let graph = search_graph(&definition, initial(&definition), options);
        assert!(graph.states.is_empty());
        assert_eq!(graph.incomplete, [IncompleteSearch::ResultBound]);

        let target = Pattern {
            term: Term::variable(Variable::new("Result", Sort::simple("SortS"))),
            constraints: Vec::new(),
        };
        let pattern = search_pattern(&definition, initial(&definition), &target, options);
        assert!(pattern.matches.is_empty());
        assert_eq!(pattern.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn pattern_result_bound_reports_mid_collection_truncation() {
        let definition = definition();
        let target = Pattern {
            term: Term::variable(Variable::new("Result", Sort::simple("SortS"))),
            constraints: Vec::new(),
        };
        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 1);
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);

        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                max_results: Some(2),
                ..SearchOptions::default()
            },
        );
        assert_eq!(result.matches.len(), 2);
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn breadth_bound_reports_the_live_search_frontier() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                max_breadth: Some(1),
                ..SearchOptions::default()
            },
        );

        assert!(result.states.is_empty());
        let [IncompleteSearch::BreadthBound(frontier)] = result.incomplete.as_slice() else {
            panic!(
                "expected a breadth-bound frontier, found {:?}",
                result.incomplete
            );
        };
        assert_eq!(
            frontier
                .iter()
                .map(|state| match state.pattern.term.kind() {
                    TermKind::Application { symbol, .. } => symbol.name.as_ref(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<Vec<_>>(),
            vec!["next1", "next2"]
        );
    }

    #[test]
    fn zero_breadth_reports_the_initial_search_frontier() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                max_breadth: Some(0),
                ..SearchOptions::default()
            },
        );

        assert!(result.states.is_empty());
        let [IncompleteSearch::BreadthBound(frontier)] = result.incomplete.as_slice() else {
            panic!(
                "expected a breadth-bound frontier, found {:?}",
                result.incomplete
            );
        };
        assert_eq!(frontier.len(), 1);
        assert_eq!(frontier[0].depth, 0);
        assert!(matches!(
            frontier[0].pattern.term.kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "initial"
        ));
    }

    #[test]
    fn final_search_recognizes_a_normal_form_at_the_depth_bound() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: 2,
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn pattern_search_returns_substitutions_for_matching_states() {
        let definition = definition();
        let result_variable = Variable::new("Result", Sort::simple("SortS"));
        let target = Pattern {
            term: Term::variable(result_variable.clone()),
            constraints: Vec::new(),
        };

        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 2);
        assert_eq!(
            result
                .matches
                .iter()
                .map(|found| match found.substitution[&result_variable].kind() {
                    TermKind::Application { symbol, .. } => symbol.name.to_string(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn matches_each_disjunction_alternative_independently() {
        let definition = definition();
        let result_variable = Variable::new("Result", Sort::simple("SortS"));
        let target = Pattern {
            term: Term::variable(result_variable.clone()),
            constraints: Vec::new(),
        };
        let subjects = [
            pattern(&definition, "final1{}()"),
            pattern(&definition, "final2{}()"),
        ];

        let matches = match_disjunction(&definition, &target, &subjects).unwrap();

        assert_eq!(matches.len(), 2);
        assert_eq!(
            matches
                .iter()
                .map(|found| match found.substitution[&result_variable].kind() {
                    TermKind::Application { symbol, .. } => symbol.name.to_string(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(matches.iter().all(|found| found.constraints.is_empty()));
    }

    #[test]
    fn disjunction_matching_returns_top_only_for_an_exact_alternative() {
        let definition = definition();
        let target = initial(&definition);
        let absent = [
            pattern(&definition, "final1{}()"),
            pattern(&definition, "final2{}()"),
        ];
        let present = [pattern(&definition, "final1{}()"), initial(&definition)];

        assert!(
            match_disjunction(&definition, &target, &absent)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            match_disjunction(&definition, &target, &present).unwrap(),
            vec![PatternMatch {
                substitution: Substitution::new(),
                constraints: Vec::new(),
            }]
        );
    }

    #[test]
    fn disjunction_matching_retains_predicates_without_an_smt_decision() {
        let definition = definition();
        let variable = Term::variable(Variable::new("X", Sort::simple("SortS")));
        let unresolved = Predicate::Not(Box::new(Predicate::Equals(
            variable,
            pattern(&definition, "final1{}()").term,
        )));
        let subject = Pattern {
            term: initial(&definition).term,
            constraints: vec![unresolved.clone()],
        };

        let matches = match_disjunction(&definition, &initial(&definition), &[subject]).unwrap();

        assert_eq!(
            matches,
            vec![PatternMatch {
                substitution: Substitution::new(),
                constraints: vec![unresolved],
            }]
        );
    }

    #[test]
    fn concrete_pattern_search_reports_reachability() {
        let definition = definition();
        let target = pattern(&definition, "initial{}()");

        let reachable = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Star,
                ..SearchOptions::default()
            },
        );
        let unreachable = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(reachable.matches.len(), 1);
        assert!(reachable.matches[0].substitution.is_empty());
        assert!(unreachable.matches.is_empty());
    }

    #[test]
    fn constrained_kore_search_patterns_filter_solutions() {
        let definition = definition();
        let syntax = parse_pattern(
            r#"\and{SortS{}}(
                Result:SortS{},
                \equals{SortS{}, SortS{}}(Result:SortS{}, final1{}())
            )"#,
        )
        .expect("constrained target should parse");
        let target = definition
            .internalize_pattern(&syntax, &[])
            .expect("constrained target should internalize");

        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 1);
        assert!(result.matches[0].constraints.is_empty());
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn projects_solved_path_equalities_onto_search_variables() {
        let sort = Sort::simple("SortS");
        let result_variable = Variable::new("Result", sort.clone());
        let configuration_variable = Variable::new("Configuration", sort.clone());
        let left = Variable::new("Left", sort.clone());
        let right = Variable::new("Right", sort.clone());
        let value = Term::application(
            Arc::new(Symbol::constructor(
                "arrow",
                vec![sort.clone(), sort.clone()],
                sort,
            )),
            Vec::new(),
            vec![Term::variable(left), Term::variable(right)],
        );

        let (output, constraints) = normalize_match_condition(
            Substitution::from([(
                result_variable.clone(),
                Term::variable(configuration_variable.clone()),
            )]),
            vec![Predicate::Equals(
                Term::variable(configuration_variable),
                value.clone(),
            )],
            &BTreeSet::from([result_variable.clone()]),
        );

        assert_eq!(output, Substitution::from([(result_variable, value)]));
        assert!(constraints.is_empty());
    }
}
