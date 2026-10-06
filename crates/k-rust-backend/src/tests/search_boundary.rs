//! Boundary contracts of path search (`crate::search::search_paths`): what each budget bound,
//! a cancelled request, and a state the search cannot explore leave in the result.
//!
//! The definitions are chains of constructors, `a => b => c` with `c` stuck, so every state
//! has exactly one successor (or none) and every path is the one through the chain: what a
//! bound leaves behind is read off the depth.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    rewrite::{IndeterminateReason, Pattern},
    rule::Predicate,
    search::{
        IncompleteSearch, PathSearchResult, SearchEnd, SearchOptions, SearchState, SearchType,
        search_paths,
    },
    simplify::SimplificationError,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    stop::{CancellationToken, StopCause},
    substitution::Substitution,
    term::{Term, TermKind},
};

/// `a => b => c`, `m => macroed` and `p => q` ensuring `g(q) = q`, over constructors `a`, `b`,
/// `c`, `m`, `p` and `q`, a macro symbol `macroed`, a total function `g` without equations, and
/// `unsupported(\dv)`, an application of a hooked function whose hook the backend
/// does not implement and which has no equations.
fn definition() -> BackendDefinition {
    let rule = |label: &str, left: &str, right: &str| {
        format!(
            r#"
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({left}, \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}())
                ) [label{{}}("{label}")]"#
        )
    };
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} []
                sort SortV{{}} [hasDomainValues{{}}()]
                symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol m{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol macroed{{}}() : SortS{{}} [constructor{{}}(), functional{{}}(), macro{{}}()]
                symbol pair{{}}(SortS{{}}, SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol p{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol q{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol g{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                hooked-symbol unsupported{{}}(SortV{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), hook{{}}("TEST.unimplemented")]
                {a_b}
                {b_c}
                {m_macroed}
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(p{{}}(), \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}(q{{}}(), \equals{{SortS{{}}, SortS{{}}}}(g{{}}(q{{}}()), q{{}}()))
                ) [label{{}}("p-q")]
            endmodule []"#,
        a_b = rule("a-b", "a{}()", "b{}()"),
        b_c = rule("b-c", "b{}()", "c{}()"),
        m_macroed = rule("m-macroed", "m{}()", "macroed{}()"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    Pattern {
        term: term(definition, source),
        constraints: Vec::new(),
    }
}

fn options(search_type: SearchType, max_depth: u64) -> SearchOptions {
    SearchOptions {
        search_type,
        max_depth,
        ..SearchOptions::default()
    }
}

fn head(term: &Term) -> String {
    match term.kind() {
        TermKind::Application { symbol, .. } => symbol.name.to_string(),
        other => panic!("expected an application, found {other:?}"),
    }
}

/// The head and depth of every witness, in the order the search reported them.
fn witnesses(result: &PathSearchResult) -> Vec<(String, u64)> {
    result
        .witnesses
        .iter()
        .map(|witness| (head(&witness.pattern.term), witness.depth))
        .collect()
}

fn state_summary(state: &SearchState) -> (String, u64) {
    (head(&state.pattern.term), state.depth)
}

/// The head and depth of every `DepthBound` entry.
fn depth_bounded(result: &PathSearchResult) -> Vec<(String, u64)> {
    result
        .incomplete
        .iter()
        .filter_map(|entry| match entry {
            IncompleteSearch::DepthBound(state) => Some(state_summary(state)),
            _ => None,
        })
        .collect()
}

fn owned(entries: &[(&str, u64)]) -> Vec<(String, u64)> {
    entries
        .iter()
        .map(|(name, depth)| ((*name).to_owned(), *depth))
        .collect()
}

/// A depth bound `d` explores the states at depth at most `d` and steps none at depth `d`: each
/// path that reaches depth `d` is a `DepthBound` entry, the results are the states the search
/// type selects among those explored, and the result is incomplete, since the bounded states
/// may have successors. A `One` search never steps a state at depth 1, so a bound of 1 leaves
/// it nothing unexplored. The bounds 0 and 1 are the two that separate "nothing stepped" from
/// "one step".
#[test]
fn a_depth_bound_steps_no_state_at_the_bound_and_reports_each_path_reaching_it() {
    type Case<'a> = (SearchType, u64, &'a [(&'a str, u64)], &'a [(&'a str, u64)]);
    let definition = definition();
    let cases: [Case<'_>; 6] = [
        (SearchType::Star, 0, &[("a", 0)], &[("a", 0)]),
        (SearchType::Star, 1, &[("a", 0), ("b", 1)], &[("b", 1)]),
        (SearchType::Plus, 0, &[], &[("a", 0)]),
        (SearchType::Plus, 1, &[("b", 1)], &[("b", 1)]),
        (SearchType::One, 0, &[], &[("a", 0)]),
        (SearchType::One, 1, &[("b", 1)], &[]),
    ];
    for (search_type, max_depth, results, bounded) in cases {
        let result = search_paths(
            &definition,
            pattern(&definition, "a{}()"),
            options(search_type, max_depth),
        );
        let case = format!("{search_type:?} to depth {max_depth}: {result:?}");
        assert_eq!(witnesses(&result), owned(results), "{case}");
        assert_eq!(depth_bounded(&result), owned(bounded), "{case}");
        assert_eq!(result.incomplete.len(), bounded.len(), "{case}");
        assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{case}");
        assert_eq!(result.is_complete(), bounded.is_empty(), "{case}");
    }
    // Without a bound the same chain is explored to its stuck end and is complete.
    let result = search_paths(
        &definition,
        pattern(&definition, "a{}()"),
        options(SearchType::Star, u64::MAX),
    );
    assert_eq!(witnesses(&result), owned(&[("a", 0), ("b", 1), ("c", 2)]));
    assert!(result.is_complete(), "{result:?}");
}

/// A zero breadth bound is exceeded by the initial path itself: nothing is explored, the
/// initial state is the whole reported frontier, and the search ends at the breadth bound.
#[test]
fn a_zero_breadth_bound_reports_the_initial_path_as_the_frontier() {
    let definition = definition();
    let result = search_paths(
        &definition,
        pattern(&definition, "a{}()"),
        SearchOptions {
            search_type: SearchType::Star,
            max_breadth: Some(0),
            ..SearchOptions::default()
        },
    );
    assert!(result.witnesses.is_empty(), "{result:?}");
    let [IncompleteSearch::BreadthBound(frontier)] = result.incomplete.as_slice() else {
        panic!("expected one breadth-bound frontier, found {result:?}");
    };
    assert_eq!(
        frontier.iter().map(state_summary).collect::<Vec<_>>(),
        owned(&[("a", 0)])
    );
    assert!(
        matches!(result.end, SearchEnd::BreadthBound(_)),
        "{result:?}"
    );
    assert!(!result.is_complete());
}

/// A request cancelled before the search starts ends it at the first poll: the initial state
/// is the one `Stopped` entry with the cancellation, no state is retained as a result (its
/// retention comes after the poll), and the search ends with the cancellation.
#[test]
fn a_cancelled_request_stops_the_search_at_its_first_state() {
    let definition = definition();
    let token = CancellationToken::new();
    token.cancel();
    let result = token.scope(|| {
        search_paths(
            &definition,
            pattern(&definition, "a{}()"),
            options(SearchType::Star, u64::MAX),
        )
    });
    assert!(result.witnesses.is_empty(), "{result:?}");
    let [IncompleteSearch::Stopped { state, cause }] = result.incomplete.as_slice() else {
        panic!("expected one stopped entry, found {result:?}");
    };
    assert_eq!(state_summary(state), ("a".to_owned(), 0));
    assert_eq!(cause, &StopCause::Cancelled);
    assert_eq!(result.end, SearchEnd::Stopped(StopCause::Cancelled));
    assert!(!result.is_complete());
}

/// A successor in which a macro symbol survived has no executable meaning: the path ends there
/// with an `Indeterminate` entry naming the symbol, the state is not a result, and the search
/// goes on with the other paths and ends exhausted, but incomplete.
#[test]
fn a_successor_with_a_surviving_macro_is_an_indeterminate_entry() {
    let definition = definition();
    let result = search_paths(
        &definition,
        pattern(&definition, "m{}()"),
        options(SearchType::Star, u64::MAX),
    );
    assert_eq!(witnesses(&result), owned(&[("m", 0)]));
    let [IncompleteSearch::Indeterminate { state, reason }] = result.incomplete.as_slice() else {
        panic!("expected one indeterminate entry, found {result:?}");
    };
    assert_eq!(state_summary(state), ("macroed".to_owned(), 1));
    assert!(
        matches!(
            reason,
            IndeterminateReason::SurvivingMacroOrAlias { symbol } if symbol.as_ref() == "macroed"
        ),
        "{reason:?}"
    );
    assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{result:?}");
    assert!(!result.is_complete());
}

/// A state whose constraints simplify to false has no instance: it is no result, it leaves no
/// incomplete entry, and the search over it is complete.
#[test]
fn a_state_with_contradictory_constraints_is_no_result_and_leaves_nothing_behind() {
    let definition = definition();
    let initial = Pattern {
        term: term(&definition, "a{}()"),
        constraints: vec![Predicate::Equals(
            term(&definition, "b{}()"),
            term(&definition, "c{}()"),
        )],
    };
    let result = search_paths(&definition, initial, options(SearchType::Star, u64::MAX));
    assert!(result.witnesses.is_empty(), "{result:?}");
    assert!(result.incomplete.is_empty(), "{result:?}");
    assert!(result.is_complete(), "{result:?}");
}

/// When simplifying a state fails, whether in its term or in its constraints, the state's
/// successors are unknown: the path ends with a `Simplification` entry carrying the failure,
/// the state is not a result, and the result is incomplete.
#[test]
fn a_state_whose_simplification_fails_is_a_simplification_entry() {
    let definition = definition();
    let unsupported = r#"unsupported{}(\dv{SortV{}}("1"))"#;
    let in_term = pattern(&definition, &format!("pair{{}}(a{{}}(), {unsupported})"));
    let in_constraints = Pattern {
        term: term(&definition, "a{}()"),
        constraints: vec![Predicate::Equals(
            term(&definition, unsupported),
            term(&definition, "b{}()"),
        )],
    };
    for (place, initial) in [("term", in_term), ("constraints", in_constraints)] {
        let result = search_paths(&definition, initial, options(SearchType::Star, u64::MAX));
        assert!(result.witnesses.is_empty(), "{place}: {result:?}");
        let [IncompleteSearch::Simplification { state, error }] = result.incomplete.as_slice()
        else {
            panic!("{place}: expected one simplification entry, found {result:?}");
        };
        assert_eq!(state.depth, 0, "{place}");
        assert!(
            matches!(
                error,
                SimplificationError::UnsupportedHook { hook, .. } if hook == "TEST.unimplemented"
            ),
            "{place}: {error:?}"
        );
        assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{place}");
        assert!(!result.is_complete(), "{place}");
    }
}

/// A solver that cancels `token` when it is asked about a predicate that mentions `g`, then
/// answers as if nothing happened: the request is cancelled while the search is underway.
struct CancelOnG {
    token: CancellationToken,
}

impl CancelOnG {
    fn observe(&self, predicates: &[Predicate]) {
        let mut mentions = false;
        for predicate in predicates {
            predicate.visit_terms(&mut |term| {
                term.visit_symbols(&mut |symbol| mentions |= symbol.name.as_ref() == "g");
            });
        }
        if mentions {
            self.token.cancel();
        }
    }
}

impl SmtSolver for CancelOnG {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        self.observe(predicates);
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        self.observe(known);
        self.observe(checked);
        Ok(Ok(Validity::Contingent))
    }
}

/// A request cancelled while the search is underway keeps what was established before: the
/// results already retained are published, and the state whose exploration observed the
/// cancellation is the one `Stopped` entry, with no successor. Here the cancellation arrives
/// while the step from `p` decides the condition `g(q) = q` it ensures, after `p` itself was
/// retained, so `p` is both the one result and the stopped state, and `q` is never reached.
#[test]
fn a_request_cancelled_midway_keeps_the_results_retained_before_it() {
    let definition = definition();
    let token = CancellationToken::new();
    let solver = CancelOnG {
        token: token.clone(),
    };
    let result = token.scope(|| {
        crate::search::search_paths_with_solver(
            &definition,
            pattern(&definition, "p{}()"),
            options(SearchType::Star, u64::MAX),
            &solver,
        )
    });
    assert_eq!(witnesses(&result), owned(&[("p", 0)]), "{result:?}");
    let [IncompleteSearch::Stopped { state, cause }] = result.incomplete.as_slice() else {
        panic!("expected one stopped entry, found {result:?}");
    };
    assert_eq!(state_summary(state), ("p".to_owned(), 0));
    assert_eq!(cause, &StopCause::Cancelled);
    assert_eq!(result.end, SearchEnd::Stopped(StopCause::Cancelled));
}
