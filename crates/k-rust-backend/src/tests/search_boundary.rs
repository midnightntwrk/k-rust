//! Boundary contracts of path search (`crate::search::search_paths`): what each budget bound,
//! a stop in each phase of a state's exploration, and a state the search cannot explore leave
//! in the result.
//!
//! The definitions are chains of constructors, `a => b => c` with `c` stuck, so every state
//! has exactly one successor (or none) and every path is the one through the chain: what a
//! bound leaves behind is read off the depth. A stop is raised by a solver the first time a
//! phase asks it about the function `g`, so the state chosen decides which phase sees it.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    rewrite::{IndeterminateReason, Pattern},
    rule::Predicate,
    search::{
        IncompleteSearch, PathSearchResult, SearchEnd, SearchOptions, SearchState, SearchType,
        Truncation, search_paths,
    },
    simplify::SimplificationError,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    stop::{CancellationToken, StopCause},
    substitution::Substitution,
    term::{Term, TermKind},
};

/// `a => b => c`, `m => macroed`, `p => q` ensuring `g(q) = q`, and `t => c`, `t => macroed`,
/// over constructors `a`, `b`, `c`, `m`, `p`, `q` and `t`, a macro symbol `macroed`, a total
/// function `g` without equations, and `unsupported(\dv)`, an application of a hooked function
/// whose hook the backend does not implement and which has no equations, declared `impure` so
/// that it is the unsupported-hook error where the simplifier reaches it (a pure `total` one is
/// left for the run to refuse where it uses the value).
///
/// Two equations are guarded by `g(X) = X`, which nothing decides, so simplifying what they
/// apply to asks the solver about `g`: `f(X) = c`, of a total function `f`, and `\ceil(pf(X))`,
/// the definedness of a partial function `pf` without equations of its own.
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
                symbol t{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                symbol pf{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(\equals{{SortS{{}}, R}}(g{{}}(X:SortS{{}}), X:SortS{{}}), \top{{R}}()),
                    \equals{{SortS{{}}, R}}(f{{}}(X:SortS{{}}), \and{{SortS{{}}}}(c{{}}(), \top{{SortS{{}}}}()))
                ) [label{{}}("f-c"), simplification{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(\equals{{SortS{{}}, R}}(g{{}}(X:SortS{{}}), X:SortS{{}}), \top{{R}}()),
                    \equals{{R, R}}(\ceil{{SortS{{}}, R}}(pf{{}}(X:SortS{{}})), \top{{R}}())
                ) [label{{}}("pf-defined")]
                hooked-symbol unsupported{{}}(SortV{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), impure{{}}(), hook{{}}("TEST.unimplemented")]
                {a_b}
                {b_c}
                {m_macroed}
                {t_c}
                {t_macroed}
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(p{{}}(), \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}(q{{}}(), \equals{{SortS{{}}, SortS{{}}}}(g{{}}(q{{}}()), q{{}}()))
                ) [label{{}}("p-q")]
            endmodule []"#,
        a_b = rule("a-b", "a{}()", "b{}()"),
        b_c = rule("b-c", "b{}()", "c{}()"),
        m_macroed = rule("m-macroed", "m{}()", "macroed{}()"),
        t_c = rule("t-c", "t{}()", "c{}()"),
        t_macroed = rule("t-macroed", "t{}()", "macroed{}()"),
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

/// A `Final` search returns the normal forms of the bounded search: a state at the depth bound
/// takes no step, so it is a result, and since it may still have successors without the bound,
/// it is also a `DepthBound` entry and the search is incomplete. That holds for a state that is
/// a normal form without the bound too (`c` at depth 2), since the search does not step it to
/// find out; and it holds without stepping: `m` at the bound 0 is no `Indeterminate` entry for
/// the macro its step would produce.
#[test]
fn a_final_search_reports_each_state_at_the_depth_bound_as_a_result_and_a_frontier() {
    let definition = definition();
    for (initial, max_depth, reached) in [
        ("a{}()", 0, ("a", 0)),
        ("a{}()", 1, ("b", 1)),
        ("a{}()", 2, ("c", 2)),
        ("m{}()", 0, ("m", 0)),
    ] {
        let result = search_paths(
            &definition,
            pattern(&definition, initial),
            options(SearchType::Final, max_depth),
        );
        let case = format!("{initial} to depth {max_depth}: {result:?}");
        assert_eq!(witnesses(&result), owned(&[reached]), "{case}");
        assert_eq!(depth_bounded(&result), owned(&[reached]), "{case}");
        assert_eq!(result.incomplete.len(), 1, "{case}");
        assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{case}");
        assert!(!result.is_complete(), "{case}");
    }
    // Without a bound the one normal form is `c`, and the search is complete.
    let result = search_paths(
        &definition,
        pattern(&definition, "a{}()"),
        options(SearchType::Final, u64::MAX),
    );
    assert_eq!(witnesses(&result), owned(&[("c", 2)]));
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
/// incomplete entry, and the search over it is complete. That holds at a depth bound too: a
/// state with no instance has no successor that the bound could hide, so it is no `DepthBound`
/// frontier, in the path search and in the state-set search alike. (Its definedness facts are
/// empty, so the initial-state emptiness check does not refute it; the constraints do.)
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
    for search_type in [SearchType::Star, SearchType::Final] {
        for max_depth in [0, u64::MAX] {
            let case = format!("{search_type:?} to depth {max_depth}");
            let result = search_paths(
                &definition,
                initial.clone(),
                options(search_type, max_depth),
            );
            assert!(result.witnesses.is_empty(), "{case}: {result:?}");
            assert!(result.incomplete.is_empty(), "{case}: {result:?}");
            assert!(result.is_complete(), "{case}: {result:?}");
            let states = crate::search::search_graph(
                &definition,
                initial.clone(),
                options(search_type, max_depth),
            );
            assert!(states.states.is_empty(), "{case}: {states:?}");
            assert!(states.incomplete.is_empty(), "{case}: {states:?}");
            assert!(states.is_complete(), "{case}: {states:?}");
        }
    }
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

/// Whether some predicate of `predicates` mentions the symbol `g`.
fn mentions_g(predicates: &[Predicate]) -> bool {
    let mut mentions = false;
    for predicate in predicates {
        predicate.visit_terms(&mut |term| {
            term.visit_symbols(&mut |symbol| mentions |= symbol.name.as_ref() == "g");
        });
    }
    mentions
}

/// What a [`StopOnG`] solver raises the first time it is asked about `g`.
enum Raise {
    /// Cancel the request: a stop that ends the search.
    Cancel(CancellationToken),
    /// Arm a step deadline that has already passed: a stop that ends only the work observing
    /// it. It stays armed until the solver is dropped, as a deadline a caller arms around a whole
    /// search does.
    Deadline(std::cell::RefCell<Option<crate::stop::DeadlineGuard>>),
}

/// A solver that raises a stop the first time it is asked about a predicate that mentions `g`
/// and, like a solver that polls while it works, reports every raised stop from then on as its
/// answer, so the stop arrives in the phase of the search that asked.
struct StopOnG(Raise);

const PASSED: crate::timeout::StepTimeoutMode =
    crate::timeout::StepTimeoutMode::Manual(std::time::Duration::ZERO);

impl StopOnG {
    fn cancel(token: &CancellationToken) -> Self {
        Self(Raise::Cancel(token.clone()))
    }

    fn deadline() -> Self {
        Self(Raise::Deadline(std::cell::RefCell::new(None)))
    }

    fn observe(&self, predicates: &[&[Predicate]]) -> Stoppable<()> {
        if predicates.iter().any(|predicates| mentions_g(predicates)) {
            match &self.0 {
                Raise::Cancel(token) => token.cancel(),
                Raise::Deadline(armed) => {
                    armed.borrow_mut().get_or_insert_with(|| {
                        crate::stop::arm_deadline(std::time::Instant::now(), PASSED)
                    });
                }
            }
        }
        crate::stop::check()
    }
}

impl SmtSolver for StopOnG {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        self.observe(&[predicates])?;
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        self.observe(&[known, checked])?;
        Ok(Ok(Validity::Contingent))
    }
}

/// `term` under `constraints`, each a pair of terms stated equal.
fn constrained(
    definition: &BackendDefinition,
    term_source: &str,
    equal: &[(&str, &str)],
) -> Pattern {
    Pattern {
        term: term(definition, term_source),
        constraints: equal
            .iter()
            .map(|(left, right)| Predicate::Equals(term(definition, left), term(definition, right)))
            .collect(),
    }
}

/// A request cancelled during any phase of exploring a state lists that state, as it stood
/// before the phase, as the one `Stopped` entry, retains no result, and ends the search. The
/// phases are told apart by where the first question about `g` comes from: simplifying the
/// constraint `f(c) = c` (the equation for `f` is guarded by `g(c) = c`), simplifying the term
/// `pair(a, f(c))`, or deciding whether the initial state `pair(a, pf(c))` is empty, whose
/// definedness fact `\ceil(pf(c))` only the guarded `\ceil` equation decides.
#[test]
fn a_request_cancelled_while_a_state_is_simplified_or_checked_stops_at_that_state() {
    let definition = definition();
    for (phase, initial) in [
        (
            "constraint simplification",
            constrained(&definition, "a{}()", &[("f{}(c{}())", "c{}()")]),
        ),
        (
            "term simplification",
            pattern(&definition, "pair{}(a{}(), f{}(c{}()))"),
        ),
        (
            "initial-state emptiness",
            pattern(&definition, "pair{}(a{}(), pf{}(c{}()))"),
        ),
    ] {
        let token = CancellationToken::new();
        let solver = StopOnG::cancel(&token);
        let result = token.scope(|| {
            crate::search::search_paths_with_solver(
                &definition,
                initial.clone(),
                options(SearchType::Star, u64::MAX),
                &solver,
            )
        });
        assert!(
            token.is_cancelled(),
            "{phase}: the solver was asked about g"
        );
        assert!(result.witnesses.is_empty(), "{phase}: {result:?}");
        let [IncompleteSearch::Stopped { state, cause }] = result.incomplete.as_slice() else {
            panic!("{phase}: expected one stopped entry, found {result:?}");
        };
        assert_eq!(state.depth, 0, "{phase}");
        assert_eq!(state.pattern, initial, "{phase}");
        assert_eq!(cause, &StopCause::Cancelled, "{phase}");
        assert_eq!(
            result.end,
            SearchEnd::Stopped(StopCause::Cancelled),
            "{phase}"
        );
    }
}

/// A stop while a state is externalised as a result leaves that result unknown. A cancellation
/// ends the search there: the state is the one `Stopped` entry and is not stepped. A step
/// deadline ends only the work that observed it: the state is still explored, so its step,
/// which polls the same passed deadline, is listed too, and the search goes on to its end. The
/// constraint `g(c) = c` is first asked about by the externalisation, which simplifies the
/// result with the solver.
#[test]
fn a_stop_while_a_result_is_externalised_ends_the_search_only_when_it_ends_the_request() {
    let definition = definition();
    let initial = constrained(&definition, "a{}()", &[("g{}(c{}())", "c{}()")]);

    let token = CancellationToken::new();
    let solver = StopOnG::cancel(&token);
    let result = token.scope(|| {
        crate::search::search_paths_with_solver(
            &definition,
            initial.clone(),
            options(SearchType::Star, u64::MAX),
            &solver,
        )
    });
    assert!(result.witnesses.is_empty(), "{result:?}");
    let [IncompleteSearch::Stopped { state, cause }] = result.incomplete.as_slice() else {
        panic!("expected one stopped entry, found {result:?}");
    };
    assert_eq!(state_summary(state), ("a".to_owned(), 0));
    assert_eq!(cause, &StopCause::Cancelled);
    assert_eq!(result.end, SearchEnd::Stopped(StopCause::Cancelled));

    let solver = StopOnG::deadline();
    let result = crate::search::search_paths_with_solver(
        &definition,
        initial,
        options(SearchType::Star, u64::MAX),
        &solver,
    );
    assert!(result.witnesses.is_empty(), "{result:?}");
    let stopped = result
        .incomplete
        .iter()
        .map(|entry| match entry {
            IncompleteSearch::Stopped { state, cause } => (state_summary(state), cause.clone()),
            other => panic!("expected only stopped entries, found {other:?}"),
        })
        .collect::<Vec<_>>();
    let a = ("a".to_owned(), 0);
    assert_eq!(
        stopped,
        [
            (a.clone(), StopCause::Deadline(PASSED)),
            (a, StopCause::Deadline(PASSED))
        ],
        "the result's externalisation, then the state's step"
    );
    assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{result:?}");
    assert!(!result.is_complete());
}

/// A `Final` search externalises a stuck state as its result; a step deadline that passes
/// there leaves that result unknown, lists the state as `Stopped`, and does not end the search,
/// which ends exhausted. Only the stuck `c` asks the solver about `g(c) = c`: the states before
/// it are not results.
#[test]
fn a_deadline_while_a_stuck_result_is_externalised_ends_only_that_result() {
    let definition = definition();
    let solver = StopOnG::deadline();
    let result = crate::search::search_paths_with_solver(
        &definition,
        constrained(&definition, "a{}()", &[("g{}(c{}())", "c{}()")]),
        options(SearchType::Final, u64::MAX),
        &solver,
    );
    assert!(result.witnesses.is_empty(), "{result:?}");
    let [IncompleteSearch::Stopped { state, cause }] = result.incomplete.as_slice() else {
        panic!("expected one stopped entry, found {result:?}");
    };
    assert_eq!(state_summary(state), ("c".to_owned(), 2));
    assert_eq!(cause, &StopCause::Deadline(PASSED));
    assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{result:?}");
}

/// The result bound of a pattern search reached on the last path the search holds: what is left
/// is the matched state's own continuation. `b` can still step, so its successors are unexplored
/// work and the search ends at the result bound; `c` cannot, under `Star` (it would be stepped
/// and found stuck) or `Final` (it is stuck), so the search is exhausted at the bound and
/// complete.
#[test]
fn a_result_bound_reached_on_the_last_path_ends_the_search_only_if_the_match_can_step() {
    let definition = definition();
    for (search_type, target, exhausted) in [
        (SearchType::Star, "b{}()", false),
        (SearchType::Star, "c{}()", true),
        (SearchType::Final, "c{}()", true),
    ] {
        let result = crate::search::search_pattern_paths(
            &definition,
            pattern(&definition, "a{}()"),
            &pattern(&definition, target),
            SearchOptions {
                max_results: Some(1),
                ..options(search_type, u64::MAX)
            },
        );
        let case = format!("{search_type:?} for {target}: {result:?}");
        assert_eq!(result.matches.len(), 1, "{case}");
        assert!(result.incomplete.is_empty(), "{case}");
        if exhausted {
            assert!(matches!(result.end, SearchEnd::Exhausted(_)), "{case}");
            assert!(result.is_complete(), "{case}");
        } else {
            assert!(
                matches!(
                    result.end,
                    SearchEnd::ResultBound(Truncation::UnexploredWork(_))
                ),
                "{case}"
            );
            assert!(!result.is_complete(), "{case}");
        }
    }
}

/// A cancellation that a target-pattern match observes is listed with the matched state, whose
/// exploration it does not end; the search ends at the next path's poll, which comes before
/// anything else that path does. Here `t` has the successors `c` and `macroed` at the depth
/// bound 1. Matching `c` against `X` with `g(X) = X` asks the solver about `g` and cancels the
/// request; `c` is at the bound, so the next path is `macroed`, which the poll lists as
/// `Stopped`, and the search ends `Stopped`. Were that path's surviving macro looked at first,
/// it would be `Indeterminate` and the search would end exhausted, as if no cancellation came.
#[test]
fn a_cancellation_a_match_observes_stops_the_next_path_before_anything_else() {
    let definition = definition();
    let token = CancellationToken::new();
    let solver = StopOnG::cancel(&token);
    let target = Pattern {
        term: term(&definition, "X:SortS{}"),
        constraints: vec![Predicate::Equals(
            term(&definition, "g{}(X:SortS{})"),
            term(&definition, "X:SortS{}"),
        )],
    };
    let result = token.scope(|| {
        crate::search::search_pattern_paths_with_solver(
            &definition,
            pattern(&definition, "t{}()"),
            &target,
            options(SearchType::Plus, 1),
            &solver,
        )
    });
    assert!(result.matches.is_empty(), "{result:?}");
    let entries = result
        .incomplete
        .iter()
        .map(|entry| match entry {
            IncompleteSearch::DepthBound(state) => ("depth bound", state_summary(state)),
            IncompleteSearch::Stopped {
                state,
                cause: StopCause::Cancelled,
            } => ("cancelled", state_summary(state)),
            other => panic!("unexpected entry {other:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        entries,
        [
            ("depth bound", ("c".to_owned(), 1)),
            ("cancelled", ("macroed".to_owned(), 1)),
            ("cancelled", ("c".to_owned(), 1)),
        ],
        "the traversal's entries, then the match's"
    );
    assert_eq!(result.end, SearchEnd::Stopped(StopCause::Cancelled));
}
