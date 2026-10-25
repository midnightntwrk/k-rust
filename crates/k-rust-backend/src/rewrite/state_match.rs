//! Matching every reached state of an execution against a target pattern
//! ([`ExecutionOptions::match_states`](super::ExecutionOptions::match_states)).
//!
//! An existential reachability question ("does some path reach a configuration that matches
//! this pattern?") is answered by the states a run reaches, not by its leaves: a state-set run
//! skips the subtree of a state equal at its depth to one it expanded, and every path's leaf is
//! the end of the path, not the configurations on it. So the run matches each state it reaches,
//! as it reaches it, and reports a summary of the verdicts ([`StateMatches`]).
//!
//! Which states are matched: every state of rewritable kind once its normalization (constraint
//! and term simplification) left it defined and it was not merged into a recorded state of its
//! depth: the initial configuration (after its definedness restriction), every state the run
//! goes on to step, every state the depth bound stops, and every successor a terminal rule ends.
//! Not matched: a remainder (its term is its parent's, which was matched, under more
//! constraints), a state a stop or the work budget cut before its normalization finished (it is
//! not a reached configuration in normal form), a cut-point rule's proposed successor (the rule
//! is proposed, not committed), and the configuration of an undefined or vacuous leaf (it
//! denotes no reached state; the configuration an undefined step was taken from was matched when
//! it was reached). A state merged into a recorded state of its depth equals it up to a renaming
//! of variables the request does not name, and a pattern reads only the configuration and its
//! constraints, so its verdict is the recorded state's; it is not matched again (the prefix that
//! reached it is handled by [`StateMatcher::absorbed`]).
//!
//! The verdict of a state ([`Verdict`]) is decided as a final configuration's would be: a state
//! *reaches* when it is decided (no constraint, no variable), shown to exist
//! ([`BackendDefinition::ground_defined`]: it denotes exactly one value; it runs in `Proof` mode
//! whatever the run's mode, so it reads no value the definition leaves to the implementation and
//! gives the answer a final configuration read back would get) and the pattern matches it with
//! empty constraints, in execution mode and, when the
//! request asks for proof agreement, in proof mode too, where a value the definition leaves to
//! the implementation stays unevaluated. It is *refuted* when every required mode refutes it,
//! and *undecided* otherwise. A state with constraints is first simplified once more as a leaf
//! would be (`execute::simplify_leaf_pattern`), which may drop a redundant constraint; a state
//! without constraints is already in that form.
//!
//! A reach is *clean* when the diagnostics of the path that reached the state, up to the state,
//! hold nothing the existence of that path may rest on without having been decided: no
//! implementation-chosen value (in another model the path may differ), no contradicted claim (a
//! model of the claim may decide otherwise), no simplification budget exhaustion and no failed
//! condition simplification (a rule may have been left unapplied for lack of budget, or because
//! simplifying its condition failed, rather than because its condition is open, so the path
//! taken may not exist), and no undecided definedness of the initial configuration (the path
//! exists only on the instances where those obligations hold). What follows the state on the
//! path cannot unmake the state's reach, so only the prefix is read. Matching stops after the
//! first clean reach whose term holds no term-level `\and` (a client that confirms a reach by a
//! query may refuse one with such a conjunction); a clean reach with one is kept as the first
//! clean reach until such a later one replaces it. The run goes on unchanged.
//!
//! The summary keeps at most five matched states (the first clean reach, the first dirty
//! reach, and the first undecided state of each of the three reasons), each with a copy of its
//! path's diagnostics up to it; nothing else grows with the run.
//!
//! Matching is isolated from the run (`coverage::isolated_on_the_clock`): it reports to no
//! coverage set, notes no path fact into the run, emits no diagnostic into the run, takes
//! nothing from the run's `FreshCounter`, and fills none of the run's memos. Its solver queries
//! go to the request's solver without the run's count of undecided answers, and are counted in
//! [`StateMatches::smt_unknowns`] instead; its stops for lack of native stack are counted in
//! [`StateMatches::stack_stops`], not the run's. It runs on the run's clock, so a request's step
//! deadline bounds it too: a deadline that passes during a match leaves the match undecided and
//! times the step out, as it would have without the match. So every other field of the result
//! is the field of the same request without `match_states`, within the execution determinism
//! contract, with two exceptions that concern every answer of the run: a solver prelude that
//! the matcher's first query finds inconsistent ends the run (it makes every solver answer of
//! the run meaningless, so the run must not go on), and a stop for lack of stack, or a step
//! deadline, which depend on the host. A decided answer the matcher leaves in the solver's
//! cache is a fact about the query, so it answers the run as the solver would; a run with
//! undecided answers is outside the contract anyway.

use crate::{
    definition::BackendDefinition,
    diagnostic::{BackendDiagnostic, PathDiagnostics},
    evaluation::{EvaluationMode, with_evaluation},
    search::{PatternMatch, PatternMatchError, match_disjunction_with_solver},
    simplify::SimplificationOptions,
    smt::{SmtSolver, UndecidedCounting},
    stop::Stoppable,
    term::{Term, TermKind, immediate_children},
};

use super::{Pattern, Truth, predicates_truth};

/// What a run matches its states against ([`super::ExecutionOptions::match_states`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateMatchOptions {
    /// The internalized target pattern, with its constraints (a `requires`).
    pub target: Pattern,
    /// Whether a state's verdict must also hold in proof mode, where a value the definition
    /// leaves to the implementation stays unevaluated: a reach then needs both modes to match,
    /// and a refutation both modes to refute; a disagreement is undecided. A target with no
    /// constraints whose every application has a free-constructor head evaluates nothing, so
    /// its verdict is the same in every mode and the second match can be left out.
    pub proof_agreement: bool,
}

/// Why a matched state's verdict is undecided ([`StateMatches::undecided`]), in the order the
/// summary lists them.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UndecidedMatchReason {
    /// The state has a constraint or a variable after its normalization: it may stand for
    /// several configurations, some of which may match.
    UndecidedState,
    /// The pattern matches, but the state's term is not shown to exist
    /// ([`BackendDefinition::ground_defined`]): it holds an application of a partial function
    /// whose definedness the walk does not discharge, map keys not shown apart, or a term-level
    /// `\and` of different sides, so it may denote nothing. (The name is the wire's
    /// `not-ceil-free`, kept from when the stored `ceil_free` attribute decided it; every term
    /// that attribute accepts is still accepted.)
    NotCeilFree,
    /// The matcher left the match undecided, matched only under constraints, the two required
    /// modes disagreed, or a stop interrupted the match.
    UndecidedMatch,
}

/// One matched state: its depth (committed rewrite steps from the initial configuration), its
/// configuration as normalized, and the diagnostics of the path that reached it, up to it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateMatch {
    pub depth: u64,
    pub pattern: Pattern,
    pub diagnostics: Vec<BackendDiagnostic>,
    /// The state's term holds a term-level `\and` (equal sides included); `false` for an
    /// undecided state.
    pub term_conjunction: bool,
}

/// The first matched state left undecided for one reason, and how many were.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UndecidedStateMatches {
    pub reason: UndecidedMatchReason,
    pub count: u64,
    pub first: StateMatch,
}

/// The summary of a run's state matches ([`super::ExecutionResult::state_matches`]), in the
/// run's depth-first order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StateMatches {
    /// The first state that reaches the target on a clean prefix and whose term holds no
    /// term-level `\and`, where one exists, and otherwise the first clean reach; matching stopped
    /// at the former. A state merged into a recorded reaching state whose prefix was not clean is
    /// reported here with its own, clean prefix ([`StateMatcher::absorbed`]).
    pub first_clean_reach: Option<StateMatch>,
    /// The first state that reaches the target on a prefix that is not clean.
    pub first_dirty_reach: Option<StateMatch>,
    /// The reaching states whose prefix was not clean.
    pub dirty_reaches: u64,
    /// For each reason, the first undecided state and the count, in reason order.
    pub undecided: Vec<UndecidedStateMatches>,
    /// The states matched.
    pub matched: u64,
    /// The states every required mode refuted.
    pub refuted: u64,
    /// The undecided answers the solver gave the matcher, which the run's own count leaves out.
    pub smt_unknowns: usize,
    /// The matcher's stops for lack of native stack, which the run's own count leaves out. A
    /// match a stop interrupted is undecided; whether the stop happens depends on the host, so a
    /// summary with a nonzero count is outside the determinism contract, as a run's is.
    pub stack_stops: usize,
}

/// What the merge table keeps of a recorded state's verdict: whether it reaches, so that an
/// arrival merged into it on a cleaner prefix can be reported.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) enum MatchMark {
    /// Not matched, refuted or undecided.
    #[default]
    Other,
    /// It reaches the target (on a clean prefix or not).
    Reach { term_conjunction: bool },
}

/// One state's verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict {
    Reach { term_conjunction: bool },
    Refuted,
    Undecided(UndecidedMatchReason),
}

/// One mode's answer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ModeVerdict {
    Matched,
    NotMatched,
    Undecided,
}

/// The matcher of one run: the target, the solver without the run's count, and the summary so
/// far.
pub(super) struct StateMatcher<'a> {
    target: Pattern,
    proof_agreement: bool,
    solver: UndecidedCounting<'a>,
    options: SimplificationOptions,
    max_iterations: usize,
    found: StateMatches,
}

impl<'a> StateMatcher<'a> {
    pub(super) fn new(
        options: StateMatchOptions,
        solver: &'a dyn SmtSolver,
        max_iterations: usize,
    ) -> Self {
        Self {
            target: options.target,
            proof_agreement: options.proof_agreement,
            solver: UndecidedCounting::new(solver),
            options: SimplificationOptions {
                max_iterations,
                ..SimplificationOptions::default()
            },
            max_iterations,
            found: StateMatches::default(),
        }
    }

    /// Whether matching is over: a clean reach whose term holds no term-level `\and` was found.
    pub(super) fn done(&self) -> bool {
        self.found
            .first_clean_reach
            .as_ref()
            .is_some_and(|reach| !reach.term_conjunction)
    }

    /// Keep `reach` as the first clean reach unless one is kept already (which, matching not
    /// being over, holds a term-level `\and`) and `reach` is no better.
    fn keep_clean(&mut self, reach: StateMatch) {
        if self.found.first_clean_reach.is_none() || !reach.term_conjunction {
            self.found.first_clean_reach = Some(reach);
        }
    }

    /// Match the state `pattern`, reached at `depth` on a path with `diagnostics`, and record
    /// its verdict. Returns what the merge table keeps of it.
    pub(super) fn observe(
        &mut self,
        definition: &BackendDefinition,
        depth: u64,
        pattern: &Pattern,
        diagnostics: &PathDiagnostics,
    ) -> MatchMark {
        if self.done() {
            return MatchMark::Other;
        }
        // A normal form that a value the definition leaves open decided is one model's: the
        // state is matched as the run left it.
        let ((normalized, normalizing_stops), read_chosen) =
            crate::coverage::isolated_on_the_clock(|| {
                crate::stop::counting_stack_stops(|| self.normal_form(definition, pattern))
            });
        let normalized = if read_chosen {
            pattern.clone()
        } else {
            normalized
        };
        let ((verdict, matching_stops), _) = crate::coverage::isolated_on_the_clock(|| {
            crate::stop::counting_stack_stops(|| self.verdict(definition, &normalized))
        });
        self.found.stack_stops += normalizing_stops + matching_stops;
        self.found.matched += 1;
        let state = |term_conjunction| StateMatch {
            depth,
            pattern: normalized.clone(),
            diagnostics: diagnostics.to_vec(),
            term_conjunction,
        };
        match verdict {
            Verdict::Reach { term_conjunction } => {
                if clean(diagnostics) {
                    self.keep_clean(state(term_conjunction));
                } else {
                    self.found.dirty_reaches += 1;
                    if self.found.first_dirty_reach.is_none() {
                        self.found.first_dirty_reach = Some(state(term_conjunction));
                    }
                }
                MatchMark::Reach { term_conjunction }
            }
            Verdict::Refuted => {
                self.found.refuted += 1;
                MatchMark::Other
            }
            Verdict::Undecided(reason) => {
                match self
                    .found
                    .undecided
                    .binary_search_by(|entry| entry.reason.cmp(&reason))
                {
                    Ok(index) => self.found.undecided[index].count += 1,
                    Err(index) => self.found.undecided.insert(
                        index,
                        UndecidedStateMatches {
                            reason,
                            count: 1,
                            first: state(false),
                        },
                    ),
                }
                MatchMark::Other
            }
        }
    }

    /// A state reached at `depth` on a path with `diagnostics` was merged into a recorded state
    /// of its depth whose verdict `mark` holds. Their verdicts are equal (module documentation),
    /// so when the recorded state reaches and this path is clean, this path is a clean reach of
    /// the same configuration: it is reported as the first clean reach, with its own prefix,
    /// unless a clean reach is kept already and this one holds a term-level `\and` too.
    pub(super) fn absorbed(
        &mut self,
        mark: MatchMark,
        depth: u64,
        pattern: &Pattern,
        diagnostics: &PathDiagnostics,
    ) {
        if self.done() {
            return;
        }
        if let MatchMark::Reach { term_conjunction } = mark
            && clean(diagnostics)
        {
            self.keep_clean(StateMatch {
                depth,
                pattern: pattern.clone(),
                diagnostics: diagnostics.to_vec(),
                term_conjunction,
            });
        }
    }

    /// The summary, with the matcher's undecided solver answers.
    pub(super) fn finish(mut self) -> StateMatches {
        self.found.smt_unknowns = self.solver.undecided();
        self.found
    }

    /// The state as a leaf would report it: a state with constraints is simplified once more
    /// (`simplify_leaf_pattern`), which drops a constraint the others and the definition's
    /// lemmas make valid; the result is kept unless the simplification failed, stopped, or found
    /// the constraints `\bottom` (a leaf would then be undefined, which the run decides, not the
    /// matcher). A state without constraints is returned as it is.
    fn normal_form(&self, definition: &BackendDefinition, pattern: &Pattern) -> Pattern {
        if pattern.constraints.is_empty() {
            return pattern.clone();
        }
        let mut trace = Vec::new();
        match super::execute::simplify_leaf_pattern(
            definition,
            pattern,
            self.max_iterations,
            &self.solver,
            0,
            &mut trace,
        ) {
            Ok(Ok(simplified))
                if predicates_truth(&simplified.pattern.constraints) != Truth::False =>
            {
                simplified.pattern
            }
            Ok(_) => pattern.clone(),
            Err(stop) => {
                // Kept outcome: the state as the run normalized it, which denotes the same
                // configurations; a stop of the request stays raised for the run's next poll.
                stop.forgo_refinement();
                pattern.clone()
            }
        }
    }

    /// The verdict on `pattern` (module documentation).
    fn verdict(&self, definition: &BackendDefinition, pattern: &Pattern) -> Verdict {
        let attributes = pattern.term.attributes();
        if !pattern.constraints.is_empty() || !attributes.variables.is_empty() {
            return Verdict::Undecided(UndecidedMatchReason::UndecidedState);
        }
        let execution = self.match_in(definition, pattern, EvaluationMode::Execution);
        // A second mode is asked only when it can change the verdict: agreement is required
        // and the first mode decided.
        let agreed = !self.proof_agreement
            || execution == ModeVerdict::Undecided
            || self.match_in(definition, pattern, EvaluationMode::Proof) == execution;
        let answer = if agreed {
            execution
        } else {
            ModeVerdict::Undecided
        };
        match answer {
            ModeVerdict::Matched if definition.ground_defined(&pattern.term) => Verdict::Reach {
                term_conjunction: holds_term_conjunction(&pattern.term),
            },
            ModeVerdict::Matched => Verdict::Undecided(UndecidedMatchReason::NotCeilFree),
            ModeVerdict::NotMatched => Verdict::Refuted,
            ModeVerdict::Undecided => Verdict::Undecided(UndecidedMatchReason::UndecidedMatch),
        }
    }

    /// The pattern's verdict on `pattern` in `mode`: matched when some match has empty
    /// constraints, refuted when there is no match, undecided otherwise.
    fn match_in(
        &self,
        definition: &BackendDefinition,
        pattern: &Pattern,
        mode: EvaluationMode,
    ) -> ModeVerdict {
        let outcome: Stoppable<Result<Vec<PatternMatch>, PatternMatchError>> =
            with_evaluation(mode, || {
                match_disjunction_with_solver(
                    definition,
                    &self.target,
                    std::slice::from_ref(pattern),
                    self.options,
                    &self.solver,
                )
            });
        match outcome {
            Ok(Ok(matches)) if matches.iter().any(|found| found.constraints.is_empty()) => {
                ModeVerdict::Matched
            }
            Ok(Ok(matches)) if matches.is_empty() => ModeVerdict::NotMatched,
            // Matched only under constraints, or left undecided (a solver `unknown` among them).
            Ok(_) => ModeVerdict::Undecided,
            Err(stop) => {
                // Kept outcome: undecided, which claims nothing; a stop of the request stays
                // raised, and the run's next poll publishes it.
                stop.forgo_refinement();
                ModeVerdict::Undecided
            }
        }
    }
}

/// Whether a path whose diagnostics are `diagnostics` is clean for a reach (module
/// documentation).
fn clean(diagnostics: &PathDiagnostics) -> bool {
    !diagnostics.any(|diagnostic| {
        matches!(
            diagnostic,
            BackendDiagnostic::ImplementationChosenValue { .. }
                | BackendDiagnostic::ContradictedClaim(_)
                | BackendDiagnostic::SimplificationBudgetExhausted { .. }
                | BackendDiagnostic::RuleConditionUnsimplified { .. }
                | BackendDiagnostic::RuleConditionFailed { .. }
                | BackendDiagnostic::UndefinedInitialInstances { .. }
        )
    })
}

/// Whether `term` holds a term-level `\and` anywhere, with equal sides or not; iterative, so a
/// deep term needs no stack.
fn holds_term_conjunction(term: &Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if matches!(term.kind(), TermKind::And(..)) {
            return true;
        }
        pending.extend(immediate_children(term.kind()));
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{Sort, Variable};

    fn pattern(name: &str) -> Pattern {
        Pattern {
            term: Term::variable(Variable::new(name, Sort::simple("SortS"))),
            constraints: Vec::new(),
        }
    }

    fn reach(name: &str, term_conjunction: bool) -> StateMatch {
        StateMatch {
            depth: 1,
            pattern: pattern(name),
            diagnostics: Vec::new(),
            term_conjunction,
        }
    }

    /// A clean reach whose term holds a term-level `\and` is kept, and matching goes on; a
    /// later one with a conjunction does not replace it; the first without one does, and ends
    /// matching (a client's query may refuse a conjunction).
    #[test]
    fn a_clean_reach_without_a_conjunction_is_preferred_and_ends_matching() {
        let solver = crate::smt::NoSolver;
        let mut matcher = StateMatcher::new(
            StateMatchOptions {
                target: pattern("T"),
                proof_agreement: false,
            },
            &solver,
            10,
        );
        let kept = |matcher: &StateMatcher<'_>| {
            matcher
                .found
                .first_clean_reach
                .as_ref()
                .map(|reach| reach.pattern.clone())
        };
        matcher.keep_clean(reach("a", true));
        assert!(!matcher.done());
        matcher.keep_clean(reach("b", true));
        assert_eq!(kept(&matcher), Some(pattern("a")));
        matcher.keep_clean(reach("c", false));
        assert!(matcher.done());
        assert_eq!(kept(&matcher), Some(pattern("c")));
    }
}
