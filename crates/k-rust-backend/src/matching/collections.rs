//! ```toml algorithm
//! id = "backend.matching.collections"
//! name = "associative and associative-commutative collection matching"
//! sites = ["solve_collection_pairs_in_definition", "solve_collection_pair", "solve_list_pair", "solve_map_pair", "solve_set_pair", "match_collection_remainders_all_in_definition", "cancel_common_opaque_chunks"]
//! variable = "k = pattern entries or elements left after common-key cancellation; n = subject entries or elements; h = list elements outside the frames; q = collection pairs in one call"
//! counters = ["MatchingCollectionProblems"]
//! span = "per problem"
//! consumes = [
//!   { type = "k_rust_backend::matching::MatchResult", role = "match result" },
//!   { type = "k_rust_backend::unification::UnificationResult", role = "unification result" },
//! ]
//! produces = [{ type = "k_rust_backend::matching::collections::CollectionSolution", role = "collection solution" }]
//!
//! [[cost]]
//! mode = "maps and sets"
//! bound = "O((n+1)^k) solve_term_pair assignments with narrowing, O(n^k) without"
//!
//! [[cost]]
//! mode = "lists"
//! bound = "O(h) solve_term_pair calls per list pair"
//!
//! [[cost]]
//! mode = "deferred pair sweep (solve_collection_pairs_from_solution)"
//! bound = "O(q^2) solve_collection_pair attempts per solution branch"
//! ```
//!
//! AC(U) matching over multisets with a frame variable (maps and sets) by backtracking assignment,
//! O(n^k) assignments worst case for k pattern elements against n subject elements (exponential in
//! k, the number of pattern elements left after cancellation); A(U) matching over lists by a
//! length-fixed frame split, one pair solve per element outside the frames; opaque-concatenation
//! cancellation;
//! `Counter::MatchingCollectionProblems`. The per-pair rules (sorts, overloads,
//! injections) stay in `solve_term_pair`, which is why no generic AC matcher replaces this.

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::{BuiltinResult, evaluate_hook},
    condition::MatchSolution,
    definition::BackendDefinition,
    substitution::{Substitution, substitute},
    term::{ListDefinition, MapDefinition, Name, Sort, SymbolType, Term, TermKind, Variable},
    unification::{MatchUnification, unify_from},
};

use super::{MatchFailed, MatchMode, MatchResult, match_terms_with_context};
/// One solution for a set of deferred collection pairs.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct CollectionSolution {
    /// Rule-variable and narrowed subject-frame bindings, with the irreducible element
    /// equalities stated under those bindings.
    pub matched: MatchSolution,
    /// Fresh collection remainders introduced while narrowing a subject frame.
    pub fresh: BTreeSet<Variable>,
}

/// Rewrite-side support for narrowing subject collection frames.
pub(crate) struct Narrowing<'a> {
    /// Mint a variable of the requested collection sort which is fresh in the current pattern.
    pub fresh_frame: &'a mut dyn FnMut(&Sort) -> Variable,
}

enum PairSolution {
    Solved(Vec<CollectionSolution>),
    NoSolution,
    Indeterminate,
}

const MAX_NESTED_COLLECTION_DEPTH: usize = 64;

/// Solve deferred collection pairs in their original, pattern-oriented order.
///
/// `None` means at least one pair needs collection or term theory outside the supported fragment;
/// an empty vector means the equation is decidably bottom. Supplying [`Narrowing`] additionally
/// permits a variable frame on the subject side to absorb pattern entries.
pub(crate) fn solve_collection_pairs_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    initial: Substitution,
    pairs: &[(Term, Term)],
    mut narrowing: Option<&mut Narrowing<'_>>,
) -> Option<Vec<CollectionSolution>> {
    let _span = measure::algorithm_span(Algorithm::BackendMatchingCollections);
    let initial = CollectionSolution {
        matched: MatchSolution::new(initial),
        fresh: BTreeSet::new(),
    };
    let mut solutions =
        solve_collection_pairs_from_solution(mode, definition, initial, pairs, &mut narrowing, 0)?;
    for solution in &mut solutions {
        solution.matched.sort_conditions();
    }
    solutions.sort();
    solutions.dedup();
    Some(solutions)
}

/// Solve whichever deferred collection pair is currently decidable, then restart the remaining
/// pairs with its substitutions. A whole sweep without a decidable pair is indeterminate.
fn solve_collection_pairs_from_solution(
    mode: MatchMode,
    definition: &BackendDefinition,
    solution: CollectionSolution,
    pairs: &[(Term, Term)],
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    if depth > MAX_NESTED_COLLECTION_DEPTH {
        return None;
    }
    if pairs.is_empty() {
        return Some(vec![solution]);
    }

    let mut deferred = Vec::new();
    for (index, (pattern, subject)) in pairs.iter().enumerate() {
        let Some(found) = solve_collection_pair(
            mode,
            definition,
            pattern,
            subject,
            solution.clone(),
            narrowing,
            depth,
        ) else {
            deferred.push((pattern.clone(), subject.clone()));
            continue;
        };
        if found.is_empty() {
            return Some(Vec::new());
        }

        deferred.extend(pairs[index + 1..].iter().cloned());
        let mut completed = Vec::new();
        for found in found {
            completed.extend(solve_collection_pairs_from_solution(
                mode, definition, found, &deferred, narrowing, depth,
            )?);
        }
        return Some(completed);
    }
    None
}

fn solve_collection_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    let pattern = substitute(pattern, solution.matched.substitution());
    let subject = substitute(subject, solution.matched.substitution());
    match (pattern.kind(), subject.kind()) {
        (TermKind::Map { .. }, TermKind::Map { .. }) => solve_map_pair(
            mode, definition, &pattern, &subject, solution, narrowing, depth,
        ),
        (TermKind::Set { .. }, TermKind::Set { .. }) => solve_set_pair(
            mode, definition, &pattern, &subject, solution, narrowing, depth,
        ),
        (TermKind::Application { .. }, TermKind::Set { .. }) if set_parts(&pattern).is_some() => {
            solve_set_pair(
                mode, definition, &pattern, &subject, solution, narrowing, depth,
            )
        }
        (TermKind::List { .. }, TermKind::List { .. }) => solve_list_pair(
            mode, definition, &pattern, &subject, solution, narrowing, depth,
        ),
        (
            TermKind::Map { .. } | TermKind::Set { .. } | TermKind::List { .. },
            TermKind::Variable(_),
        ) if narrowing.is_some() => {
            match solve_term_pair(
                mode, definition, solution, &pattern, &subject, narrowing, depth,
            ) {
                PairSolution::Solved(solutions) => Some(solutions),
                PairSolution::NoSolution => Some(Vec::new()),
                PairSolution::Indeterminate => None,
            }
        }
        _ => None,
    }
}

fn solve_term_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    mut solution: CollectionSolution,
    pattern: &Term,
    subject: &Term,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> PairSolution {
    let pattern = substitute(pattern, solution.matched.substitution());
    let subject = substitute(subject, solution.matched.substitution());
    match match_terms_with_context(
        mode,
        definition.sort_graph(),
        Some(definition),
        &pattern,
        &subject,
        // A collection element is never the root an equation is tried on.
        false,
    ) {
        MatchResult::Success(found) => {
            solution.matched.bind(&found);
            PairSolution::Solved(vec![solution])
        }
        MatchResult::Failed(_) => PairSolution::NoSolution,
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } if narrowing.is_some() => {
            solution.matched.bind(&substitution);
            let remainder = if mode == MatchMode::Rewrite {
                let Some(recovered) =
                    recover_rewrite_candidate(definition, &mut solution.matched, remainder)
                else {
                    return PairSolution::NoSolution;
                };
                recovered
            } else {
                remainder
            };
            if remainder.is_empty() {
                return PairSolution::Solved(vec![solution]);
            }
            let (collection_pairs, remainder): (Vec<_>, Vec<_>) =
                remainder.into_iter().partition(|(pattern, subject)| {
                    is_collection_term(pattern) && is_collection_term(subject)
                });
            let mut solutions = if collection_pairs.is_empty() {
                vec![solution]
            } else {
                if depth >= MAX_NESTED_COLLECTION_DEPTH {
                    return PairSolution::Indeterminate;
                }
                let Some(solutions) = solve_collection_pairs_from_solution(
                    mode,
                    definition,
                    solution,
                    &collection_pairs,
                    narrowing,
                    depth + 1,
                ) else {
                    return PairSolution::Indeterminate;
                };
                solutions
            };
            if remainder.is_empty() {
                return if solutions.is_empty() {
                    PairSolution::NoSolution
                } else {
                    PairSolution::Solved(solutions)
                };
            }

            let mut unified_solutions = Vec::new();
            for solution in solutions.drain(..) {
                match unify_from(definition, solution.matched.clone(), remainder.clone()) {
                    MatchUnification::Unified(matched) => {
                        unified_solutions.push(CollectionSolution {
                            matched,
                            fresh: solution.fresh,
                        });
                    }
                    MatchUnification::Bottom(_) => {}
                    MatchUnification::Unsupported { .. } => return PairSolution::Indeterminate,
                }
            }
            if unified_solutions.is_empty() {
                PairSolution::NoSolution
            } else {
                PairSolution::Solved(unified_solutions)
            }
        }
        MatchResult::Indeterminate { .. } => PairSolution::Indeterminate,
    }
}

/// Re-run each residual AC-candidate pair in rewrite mode before symbolic unification.
///
/// Collection solving isolates candidate entries after the whole collection match has deferred.
/// At that point a residual pair can be decidable even though the collection pair was not.  In
/// particular, normalized rewrite-rigid heads beneath widening injections must fail as a concrete
/// candidate rather than becoming an opaque equality through symbolic unification.
fn recover_rewrite_candidate(
    definition: &BackendDefinition,
    matched: &mut MatchSolution,
    remainder: Vec<(Term, Term)>,
) -> Option<Vec<(Term, Term)>> {
    let mut unresolved = Vec::new();
    for (pattern, subject) in remainder {
        let pattern = substitute(&pattern, matched.substitution());
        let subject = substitute(&subject, matched.substitution());
        match match_terms_with_context(
            MatchMode::Rewrite,
            definition.sort_graph(),
            Some(definition),
            &pattern,
            &subject,
            // A collection element is never the root an equation is tried on.
            false,
        ) {
            MatchResult::Success(found) => {
                matched.bind(&found);
            }
            MatchResult::Failed(_) => return None,
            MatchResult::Indeterminate {
                substitution: found,
                remainder,
            } => {
                matched.bind(&found);
                unresolved.extend(remainder);
            }
        }
    }
    Some(unresolved)
}

fn solve_list_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    mut solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    measure::bump(Counter::MatchingCollectionProblems);
    match match_terms_with_context(
        mode,
        definition.sort_graph(),
        Some(definition),
        pattern,
        subject,
        // A collection element is never the root an equation is tried on.
        false,
    ) {
        MatchResult::Success(found) => {
            solution.matched.bind(&found);
            return Some(vec![solution]);
        }
        MatchResult::Failed(_) => return Some(Vec::new()),
        MatchResult::Indeterminate { .. } if narrowing.is_none() => return None,
        MatchResult::Indeterminate {
            substitution,
            remainder: _,
        } => {
            solution.matched.bind(&substitution);
        }
    }

    let pattern = substitute(pattern, solution.matched.substitution());
    let subject = substitute(subject, solution.matched.substitution());
    let (
        TermKind::List {
            definition: pattern_definition,
            heads: pattern_heads,
            rest: pattern_rest,
        },
        TermKind::List {
            definition: subject_definition,
            heads: subject_heads,
            rest: subject_rest,
        },
    ) = (pattern.kind(), subject.kind())
    else {
        return None;
    };
    if pattern_definition != subject_definition {
        return Some(Vec::new());
    }

    match (pattern_rest, subject_rest) {
        (None, Some((subject_middle, subject_tails))) => solve_single_list_frame(
            mode,
            definition,
            pattern_definition,
            solution,
            pattern_heads,
            subject_heads,
            subject_middle,
            subject_tails,
            true,
            narrowing,
            depth,
        ),
        (Some((pattern_middle, pattern_tails)), None) => solve_single_list_frame(
            mode,
            definition,
            pattern_definition,
            solution,
            subject_heads,
            pattern_heads,
            pattern_middle,
            pattern_tails,
            false,
            narrowing,
            depth,
        ),
        (Some((pattern_middle, pattern_tails)), Some((subject_middle, subject_tails))) => {
            solve_two_list_frames(
                mode,
                definition,
                pattern_definition,
                solution,
                pattern_heads,
                pattern_middle,
                pattern_tails,
                subject_heads,
                subject_middle,
                subject_tails,
                narrowing,
                depth,
            )
        }
        (None, None) => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn solve_single_list_frame(
    mode: MatchMode,
    backend: &BackendDefinition,
    definition: &Arc<ListDefinition>,
    solution: CollectionSolution,
    closed: &[Term],
    framed_heads: &[Term],
    frame: &Term,
    framed_tails: &[Term],
    frame_on_subject: bool,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    if !matches!(frame.kind(), TermKind::Variable(_)) {
        return None;
    }
    let Some(frame_end) = closed.len().checked_sub(framed_tails.len()) else {
        return Some(Vec::new());
    };
    if framed_heads.len() > frame_end {
        return Some(Vec::new());
    }

    let mut pairs = Vec::with_capacity(framed_heads.len() + framed_tails.len() + 1);
    if frame_on_subject {
        pairs.extend(
            closed[..framed_heads.len()]
                .iter()
                .cloned()
                .zip(framed_heads.iter().cloned()),
        );
        pairs.extend(
            closed[frame_end..]
                .iter()
                .cloned()
                .zip(framed_tails.iter().cloned()),
        );
        pairs.push((
            Term::list(
                definition.clone(),
                closed[framed_heads.len()..frame_end].to_vec(),
                None,
            ),
            frame.clone(),
        ));
    } else {
        pairs.extend(
            framed_heads
                .iter()
                .cloned()
                .zip(closed[..framed_heads.len()].iter().cloned()),
        );
        pairs.extend(
            framed_tails
                .iter()
                .cloned()
                .zip(closed[frame_end..].iter().cloned()),
        );
        pairs.push((
            frame.clone(),
            Term::list(
                definition.clone(),
                closed[framed_heads.len()..frame_end].to_vec(),
                None,
            ),
        ));
    }
    solve_ordered_term_pairs(mode, backend, solution, pairs, narrowing, depth)
}

#[allow(clippy::too_many_arguments)]
fn solve_two_list_frames(
    mode: MatchMode,
    backend: &BackendDefinition,
    definition: &Arc<ListDefinition>,
    solution: CollectionSolution,
    pattern_heads: &[Term],
    pattern_middle: &Term,
    pattern_tails: &[Term],
    subject_heads: &[Term],
    subject_middle: &Term,
    subject_tails: &[Term],
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    if !matches!(pattern_middle.kind(), TermKind::Variable(_))
        || !matches!(subject_middle.kind(), TermKind::Variable(_))
    {
        return None;
    }
    let (mut pairs, head_remainder) = pair_prefix(pattern_heads, subject_heads);
    let (tail_pairs, tail_remainder) = pair_suffix(pattern_tails, subject_tails);
    pairs.extend(tail_pairs);
    let (pattern_extra_heads, subject_extra_heads) = match head_remainder {
        Some(PairRemainder::Left(terms)) => (terms, Vec::new()),
        Some(PairRemainder::Right(terms)) => (Vec::new(), terms),
        None => (Vec::new(), Vec::new()),
    };
    let (pattern_extra_tails, subject_extra_tails) = match tail_remainder {
        Some(PairRemainder::Left(terms)) => (terms, Vec::new()),
        Some(PairRemainder::Right(terms)) => (Vec::new(), terms),
        None => (Vec::new(), Vec::new()),
    };
    let pattern_has_extra = !pattern_extra_heads.is_empty() || !pattern_extra_tails.is_empty();
    let subject_has_extra = !subject_extra_heads.is_empty() || !subject_extra_tails.is_empty();
    if pattern_has_extra && subject_has_extra {
        return None;
    }
    let middle_pair = if pattern_has_extra {
        (
            Term::list(
                definition.clone(),
                pattern_extra_heads,
                Some((pattern_middle.clone(), pattern_extra_tails)),
            ),
            subject_middle.clone(),
        )
    } else if subject_has_extra {
        (
            pattern_middle.clone(),
            Term::list(
                definition.clone(),
                subject_extra_heads,
                Some((subject_middle.clone(), subject_extra_tails)),
            ),
        )
    } else {
        (pattern_middle.clone(), subject_middle.clone())
    };
    pairs.push(middle_pair);
    solve_ordered_term_pairs(mode, backend, solution, pairs, narrowing, depth)
}

fn solve_ordered_term_pairs(
    mode: MatchMode,
    definition: &BackendDefinition,
    solution: CollectionSolution,
    pairs: Vec<(Term, Term)>,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    let mut solutions = vec![solution];
    for (pattern, subject) in pairs {
        let mut next = Vec::new();
        for solution in solutions {
            match solve_term_pair(
                mode, definition, solution, &pattern, &subject, narrowing, depth,
            ) {
                PairSolution::Solved(found) => next.extend(found),
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => return None,
            }
        }
        solutions = next;
    }
    Some(solutions)
}

fn solve_map_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    let (
        TermKind::Map {
            definition: pattern_definition,
            entries: pattern_entries,
            rest: pattern_rest,
        },
        TermKind::Map {
            definition: subject_definition,
            entries: subject_entries,
            rest: subject_rest,
        },
    ) = (pattern.kind(), subject.kind())
    else {
        unreachable!()
    };
    if pattern_definition != subject_definition {
        return Some(Vec::new());
    }
    if [(pattern, pattern_entries), (subject, subject_entries)]
        .into_iter()
        .any(|(map, entries)| !binds_each_key_once(map) && repeats_a_key(entries))
    {
        return None;
    }
    let (pattern_rest, subject_rest) = cancel_common_opaque_chunks(
        pattern_rest.clone(),
        subject_rest.clone(),
        &pattern_definition.symbols.concat,
    );

    let CommonKeys {
        values,
        pattern_only,
        subject_only,
    } = split_common_keys(pattern_entries, subject_entries);
    let mut solutions = vec![solution];
    for (pattern_value, subject_value) in values {
        let mut next = Vec::new();
        for solution in solutions {
            match solve_term_pair(
                mode,
                definition,
                solution,
                &pattern_value,
                &subject_value,
                narrowing,
                depth,
            ) {
                PairSolution::Solved(found) => next.extend(found),
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => return None,
            }
        }
        solutions = next;
    }

    measure::bump(Counter::MatchingCollectionProblems);
    let problem = MapCollectionProblem {
        mode,
        backend: definition,
        definition: pattern_definition.clone(),
        entries: pattern_only,
        rest: pattern_rest,
        subject_rest,
        depth,
    };
    let remaining = subject_only;
    let mut found = Vec::new();
    let mut indeterminate = false;
    for solution in solutions {
        problem.search(
            0,
            remaining.clone(),
            Vec::new(),
            solution,
            narrowing,
            &mut found,
            &mut indeterminate,
        );
    }
    (!indeterminate).then_some(found)
}

struct MapCollectionProblem<'a> {
    mode: MatchMode,
    backend: &'a BackendDefinition,
    definition: Arc<MapDefinition>,
    entries: Vec<(Term, Term)>,
    rest: Option<Term>,
    subject_rest: Option<Term>,
    depth: usize,
}

impl MapCollectionProblem<'_> {
    #[allow(clippy::too_many_arguments)]
    fn search(
        &self,
        index: usize,
        remaining: Vec<(Term, Term)>,
        frame_entries: Vec<(Term, Term)>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if index == self.entries.len() {
            self.finish(
                remaining,
                frame_entries,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
            return;
        }

        let (key, value) = &self.entries[index];
        // Backtracking assignment of pattern entry `index` to each unassigned subject entry; each
        // level consumes one subject entry, so the depth is at most the number of pattern entries.
        // Invariant: `solution` matches every assigned pair; `remaining` holds the unassigned ones.
        for subject_index in 0..remaining.len() {
            let (subject_key, subject_value) = &remaining[subject_index];
            let key_solutions = match solve_term_pair(
                self.mode,
                self.backend,
                solution.clone(),
                key,
                subject_key,
                narrowing,
                self.depth,
            ) {
                PairSolution::Solved(solutions) => solutions,
                PairSolution::NoSolution => continue,
                PairSolution::Indeterminate => {
                    *indeterminate = true;
                    continue;
                }
            };
            for key_solution in key_solutions {
                let value_solutions = match solve_term_pair(
                    self.mode,
                    self.backend,
                    key_solution,
                    value,
                    subject_value,
                    narrowing,
                    self.depth,
                ) {
                    PairSolution::Solved(solutions) => solutions,
                    PairSolution::NoSolution => continue,
                    PairSolution::Indeterminate => {
                        *indeterminate = true;
                        continue;
                    }
                };
                for solution in value_solutions {
                    let mut next_remaining = remaining.clone();
                    next_remaining.remove(subject_index);
                    self.search(
                        index + 1,
                        next_remaining,
                        frame_entries.clone(),
                        solution,
                        narrowing,
                        solutions,
                        indeterminate,
                    );
                }
            }
        }

        if narrowing.is_some()
            && matches!(
                self.subject_rest.as_ref().map(Term::kind),
                Some(TermKind::Variable(_))
            )
        {
            let mut frame_entries = frame_entries;
            frame_entries.push((key.clone(), value.clone()));
            self.search(
                index + 1,
                remaining,
                frame_entries,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
        } else if self.subject_rest.is_some() {
            *indeterminate = true;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn finish(
        &self,
        remaining: Vec<(Term, Term)>,
        frame_entries: Vec<(Term, Term)>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if frame_entries.is_empty() {
            if let Some(rest) = &self.rest {
                let subject = Term::map(
                    self.definition.clone(),
                    remaining,
                    self.subject_rest.clone(),
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    rest,
                    &subject,
                    narrowing,
                    self.depth,
                ) {
                    PairSolution::Solved(found) => solutions.extend(found),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
                return;
            }
            match &self.subject_rest {
                None if remaining.is_empty() => solutions.push(solution),
                Some(subject_rest) if narrowing.is_some() => {
                    if let TermKind::Variable(variable) = subject_rest.kind() {
                        if !remaining.is_empty() {
                            return;
                        }
                        let empty = Term::map(self.definition.clone(), Vec::new(), None);
                        match solve_term_pair(
                            self.mode,
                            self.backend,
                            solution,
                            subject_rest,
                            &empty,
                            narrowing,
                            self.depth,
                        ) {
                            PairSolution::Solved(found) => solutions.extend(found),
                            PairSolution::NoSolution => {}
                            PairSolution::Indeterminate => *indeterminate = true,
                        }
                        debug_assert_eq!(variable.sort, empty.sort());
                    } else {
                        *indeterminate = true;
                    }
                }
                Some(_) => *indeterminate = true,
                None => {}
            }
            return;
        }

        let Some(subject_rest) = &self.subject_rest else {
            return;
        };
        let TermKind::Variable(frame) = subject_rest.kind() else {
            *indeterminate = true;
            return;
        };
        if self.rest.is_none() {
            if remaining.is_empty() {
                let value = Term::map(
                    self.definition.clone(),
                    frame_entries
                        .into_iter()
                        .map(|(key, value)| {
                            (
                                substitute(&key, solution.matched.substitution()),
                                substitute(&value, solution.matched.substitution()),
                            )
                        })
                        .collect(),
                    None,
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    subject_rest,
                    &value,
                    narrowing,
                    self.depth,
                ) {
                    PairSolution::Solved(found) => solutions.extend(found),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
            }
            return;
        }
        let fresh = {
            let Some(narrowing) = narrowing.as_deref_mut() else {
                *indeterminate = true;
                return;
            };
            (narrowing.fresh_frame)(&frame.sort)
        };
        let fresh_term = Term::variable(fresh.clone());
        let assigned = Term::map(
            self.definition.clone(),
            frame_entries
                .into_iter()
                .map(|(key, value)| {
                    (
                        substitute(&key, solution.matched.substitution()),
                        substitute(&value, solution.matched.substitution()),
                    )
                })
                .collect(),
            Some(fresh_term.clone()),
        );
        let assigned_solutions = match solve_term_pair(
            self.mode,
            self.backend,
            solution,
            subject_rest,
            &assigned,
            narrowing,
            self.depth,
        ) {
            PairSolution::Solved(solutions) => solutions,
            PairSolution::NoSolution => return,
            PairSolution::Indeterminate => {
                *indeterminate = true;
                return;
            }
        };
        let remainder = Term::map(self.definition.clone(), remaining, Some(fresh_term));
        for mut solution in assigned_solutions {
            solution.fresh.insert(fresh.clone());
            match solve_term_pair(
                self.mode,
                self.backend,
                solution,
                self.rest.as_ref().expect("pattern frame checked above"),
                &remainder,
                narrowing,
                self.depth,
            ) {
                PairSolution::Solved(found) => solutions.extend(found),
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => *indeterminate = true,
            }
        }
    }
}

/// A collection term: an internal collection, or an opaque concatenation of collection
/// symbols, which `Term::set` and its siblings leave as the bare application when it carries no
/// element.
pub(crate) fn is_collection_term(term: &Term) -> bool {
    match term.kind() {
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => true,
        TermKind::Application { symbol, .. } => {
            symbol
                .attributes
                .collection
                .as_ref()
                .is_some_and(|collection| match collection {
                    crate::term::CollectionMetadata::Map(definition) => {
                        definition.symbols.concat == symbol.name
                    }
                    crate::term::CollectionMetadata::List(definition) => {
                        definition.symbols.concat == symbol.name
                    }
                    crate::term::CollectionMetadata::Set(definition) => {
                        definition.symbols.concat == symbol.name
                    }
                })
        }
        _ => false,
    }
}

/// The parts of a Set term: an internal set, or an opaque concatenation viewed as a set with no
/// element and that concatenation as its rest.
fn set_parts(term: &Term) -> Option<(Arc<crate::term::SetDefinition>, Vec<Term>, Option<Term>)> {
    match term.kind() {
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Some((definition.clone(), elements.clone(), rest.clone())),
        TermKind::Application { symbol, .. } => match &symbol.attributes.collection {
            Some(crate::term::CollectionMetadata::Set(definition))
                if definition.symbols.concat == symbol.name =>
            {
                Some((definition.clone(), Vec::new(), Some(term.clone())))
            }
            _ => None,
        },
        _ => None,
    }
}

fn solve_set_pair(
    mode: MatchMode,
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    solution: CollectionSolution,
    narrowing: &mut Option<&mut Narrowing<'_>>,
    depth: usize,
) -> Option<Vec<CollectionSolution>> {
    let (
        Some((pattern_definition, pattern_elements, pattern_rest)),
        Some((subject_definition, subject_elements, subject_rest)),
    ) = (set_parts(pattern), set_parts(subject))
    else {
        unreachable!()
    };
    if pattern_definition != subject_definition {
        return Some(Vec::new());
    }
    let (pattern_rest, subject_rest) = cancel_common_opaque_chunks(
        pattern_rest,
        subject_rest,
        &pattern_definition.symbols.concat,
    );
    let pattern_element_count = pattern_elements.len();
    let subject_element_count = subject_elements.len();
    let mut pattern_elements = pattern_elements.iter().cloned().collect::<BTreeSet<_>>();
    let mut subject_elements = subject_elements.iter().cloned().collect::<BTreeSet<_>>();
    // A set that holds an element twice is `\bottom` (set concatenation is nilpotent,
    // `Term::set`); as for a map with a repeated key, no solution is claimed for it.
    if pattern_elements.len() != pattern_element_count
        || subject_elements.len() != subject_element_count
    {
        return None;
    }
    let common = pattern_elements
        .intersection(&subject_elements)
        .cloned()
        .collect::<Vec<_>>();
    for element in common {
        pattern_elements.remove(&element);
        subject_elements.remove(&element);
    }
    measure::bump(Counter::MatchingCollectionProblems);
    let problem = SetCollectionProblem {
        mode,
        backend: definition,
        definition: pattern_definition.clone(),
        elements: pattern_elements.into_iter().collect(),
        rest: pattern_rest,
        subject_rest,
        depth,
    };
    let mut found = Vec::new();
    let mut indeterminate = false;
    problem.search(
        0,
        subject_elements.into_iter().collect(),
        Vec::new(),
        solution,
        narrowing,
        &mut found,
        &mut indeterminate,
    );
    (!indeterminate).then_some(found)
}

struct SetCollectionProblem<'a> {
    mode: MatchMode,
    backend: &'a BackendDefinition,
    definition: Arc<crate::term::SetDefinition>,
    elements: Vec<Term>,
    rest: Option<Term>,
    subject_rest: Option<Term>,
    depth: usize,
}

impl SetCollectionProblem<'_> {
    #[allow(clippy::too_many_arguments)]
    fn search(
        &self,
        index: usize,
        remaining: Vec<Term>,
        frame_elements: Vec<Term>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if index == self.elements.len() {
            self.finish(
                remaining,
                frame_elements,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
            return;
        }

        let element = &self.elements[index];
        // Backtracking assignment of pattern element `index` to each unassigned subject element;
        // each level consumes one subject element, so the depth is at most the pattern size.
        // Invariant: `solution` matches every assigned pair; `remaining` holds the unassigned ones.
        for subject_index in 0..remaining.len() {
            match solve_term_pair(
                self.mode,
                self.backend,
                solution.clone(),
                element,
                &remaining[subject_index],
                narrowing,
                self.depth,
            ) {
                PairSolution::Solved(found) => {
                    for solution in found {
                        let mut next_remaining = remaining.clone();
                        next_remaining.remove(subject_index);
                        self.search(
                            index + 1,
                            next_remaining,
                            frame_elements.clone(),
                            solution,
                            narrowing,
                            solutions,
                            indeterminate,
                        );
                    }
                }
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => *indeterminate = true,
            }
        }

        if narrowing.is_some()
            && matches!(
                self.subject_rest.as_ref().map(Term::kind),
                Some(TermKind::Variable(_))
            )
        {
            let mut frame_elements = frame_elements;
            frame_elements.push(element.clone());
            self.search(
                index + 1,
                remaining,
                frame_elements,
                solution,
                narrowing,
                solutions,
                indeterminate,
            );
        } else if self.subject_rest.is_some() {
            *indeterminate = true;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn finish(
        &self,
        remaining: Vec<Term>,
        frame_elements: Vec<Term>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if frame_elements.is_empty() {
            if let Some(rest) = &self.rest {
                let subject = Term::set(
                    self.definition.clone(),
                    remaining,
                    self.subject_rest.clone(),
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    rest,
                    &subject,
                    narrowing,
                    self.depth,
                ) {
                    PairSolution::Solved(found) => solutions.extend(found),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
                return;
            }
            match &self.subject_rest {
                None if remaining.is_empty() => solutions.push(solution),
                Some(subject_rest) if narrowing.is_some() => {
                    if matches!(subject_rest.kind(), TermKind::Variable(_)) {
                        if !remaining.is_empty() {
                            return;
                        }
                        let empty = Term::set(self.definition.clone(), Vec::new(), None);
                        match solve_term_pair(
                            self.mode,
                            self.backend,
                            solution,
                            subject_rest,
                            &empty,
                            narrowing,
                            self.depth,
                        ) {
                            PairSolution::Solved(found) => solutions.extend(found),
                            PairSolution::NoSolution => {}
                            PairSolution::Indeterminate => *indeterminate = true,
                        }
                    } else {
                        *indeterminate = true;
                    }
                }
                Some(_) => *indeterminate = true,
                None => {}
            }
            return;
        }

        let Some(subject_rest) = &self.subject_rest else {
            return;
        };
        let TermKind::Variable(frame) = subject_rest.kind() else {
            *indeterminate = true;
            return;
        };
        if self.rest.is_none() {
            if remaining.is_empty() {
                let value = Term::set(
                    self.definition.clone(),
                    frame_elements
                        .into_iter()
                        .map(|element| substitute(&element, solution.matched.substitution()))
                        .collect(),
                    None,
                );
                match solve_term_pair(
                    self.mode,
                    self.backend,
                    solution,
                    subject_rest,
                    &value,
                    narrowing,
                    self.depth,
                ) {
                    PairSolution::Solved(found) => solutions.extend(found),
                    PairSolution::NoSolution => {}
                    PairSolution::Indeterminate => *indeterminate = true,
                }
            }
            return;
        }
        let fresh = {
            let Some(narrowing) = narrowing.as_deref_mut() else {
                *indeterminate = true;
                return;
            };
            (narrowing.fresh_frame)(&frame.sort)
        };
        let fresh_term = Term::variable(fresh.clone());
        let assigned = Term::set(
            self.definition.clone(),
            frame_elements
                .into_iter()
                .map(|element| substitute(&element, solution.matched.substitution()))
                .collect(),
            Some(fresh_term.clone()),
        );
        let assigned_solutions = match solve_term_pair(
            self.mode,
            self.backend,
            solution,
            subject_rest,
            &assigned,
            narrowing,
            self.depth,
        ) {
            PairSolution::Solved(solutions) => solutions,
            PairSolution::NoSolution => return,
            PairSolution::Indeterminate => {
                *indeterminate = true;
                return;
            }
        };
        let remainder = Term::set(self.definition.clone(), remaining, Some(fresh_term));
        for mut solution in assigned_solutions {
            solution.fresh.insert(fresh.clone());
            match solve_term_pair(
                self.mode,
                self.backend,
                solution,
                self.rest.as_ref().expect("pattern frame checked above"),
                &remainder,
                narrowing,
                self.depth,
            ) {
                PairSolution::Solved(found) => solutions.extend(found),
                PairSolution::NoSolution => {}
                PairSolution::Indeterminate => *indeterminate = true,
            }
        }
    }
}

/// The complete collection matches of the deferred pairs of an ordinary match.
pub(crate) enum CollectionMatches {
    /// Every solution, in the solver's stable sorted order; never empty.
    Solutions(Vec<Substitution>),
    /// The pairs have no solution: the match failed.
    NoSolution(MatchFailed),
    /// The solver could not decide the pairs.
    Undecided,
}

/// Enumerate complete collection matches for every deferred pair from an ordinary match.
///
/// A deferred Set or Map pair may have multiple AC solutions. Returning all substitutions keeps
/// that branching policy outside the one-result [`MatchResult`] API and lets each consumer decide
/// whether the solutions are execution branches or instances of one equation.
/// An empty solution set is a failed match of the pattern, so it carries the [`MatchFailed`]
/// token instead of an empty list.
pub(crate) fn match_collection_remainders_all_in_definition(
    mode: MatchMode,
    definition: &BackendDefinition,
    initial: Substitution,
    remainder: &[(Term, Term)],
) -> CollectionMatches {
    match solve_collection_pairs_in_definition(mode, definition, initial, remainder, None) {
        None => CollectionMatches::Undecided,
        Some(solutions) if solutions.is_empty() => CollectionMatches::NoSolution(MatchFailed(())),
        Some(solutions) => CollectionMatches::Solutions(
            solutions
                .into_iter()
                .map(|solution| {
                    let (substitution, conditions) = solution.matched.into_parts();
                    debug_assert!(
                        conditions.is_empty(),
                        "without narrowing the solver keeps no equation"
                    );
                    substitution
                })
                .collect(),
        ),
    }
}

#[derive(Clone)]
struct OpaqueConcatHead {
    symbol: Arc<crate::term::Symbol>,
    sort_arguments: Vec<Sort>,
}

/// Cancel opaque chunks which occur on both sides of an AC equation.
///
/// The parts of a defined set or map concatenation are disjoint, so wherever both sides are
/// defined, a chunk occurring on both sides accounts for the same elements of each, and removing
/// every occurrence of it from both sides leaves an equivalent residual equation. A side that
/// repeats a nonempty chunk is undefined; that definedness is collection simplification's to
/// decide, so rewriting needs only the residual equation.
pub(crate) fn cancel_common_opaque_chunks(
    left: Option<Term>,
    right: Option<Term>,
    concat: &Name,
) -> (Option<Term>, Option<Term>) {
    let (mut left, left_head) = flatten_opaque_chunks(left, concat);
    let (mut right, right_head) = flatten_opaque_chunks(right, concat);
    let common = left
        .iter()
        .filter(|term| right.contains(*term))
        .cloned()
        .collect::<BTreeSet<_>>();
    left.retain(|term| !common.contains(term));
    right.retain(|term| !common.contains(term));
    left.sort();
    right.sort();
    (
        rebuild_opaque_chunks(left, left_head),
        rebuild_opaque_chunks(right, right_head),
    )
}

fn flatten_opaque_chunks(
    rest: Option<Term>,
    concat: &Name,
) -> (Vec<Term>, Option<OpaqueConcatHead>) {
    fn visit(
        term: Term,
        concat: &Name,
        chunks: &mut Vec<Term>,
        head: &mut Option<OpaqueConcatHead>,
    ) {
        if let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
            && &symbol.name == concat
            && let [left, right] = arguments.as_slice()
        {
            head.get_or_insert_with(|| OpaqueConcatHead {
                symbol: symbol.clone(),
                sort_arguments: sort_arguments.clone(),
            });
            visit(left.clone(), concat, chunks, head);
            visit(right.clone(), concat, chunks, head);
        } else {
            chunks.push(term);
        }
    }

    let mut chunks = Vec::new();
    let mut head = None;
    if let Some(rest) = rest {
        visit(rest, concat, &mut chunks, &mut head);
    }
    (chunks, head)
}

fn rebuild_opaque_chunks(chunks: Vec<Term>, head: Option<OpaqueConcatHead>) -> Option<Term> {
    let mut chunks = chunks.into_iter();
    let first = chunks.next()?;
    Some(chunks.fold(first, |left, right| {
        let head = head
            .as_ref()
            .expect("multiple opaque chunks came from a concatenation");
        Term::application(
            head.symbol.clone(),
            head.sort_arguments.clone(),
            vec![left, right],
        )
    }))
}

pub(super) fn is_opaque_concat(term: &Term, concat: &Name) -> bool {
    matches!(term.kind(), TermKind::Application { symbol, .. } if &symbol.name == concat)
}

/// Expand implication remainders where a closed destination map is unified with an open current
/// map. Each returned branch is one AC entry permutation expressed as ordinary term equalities;
/// the implication layer can simplify and existentially quantify those equations uniformly with
/// its other obligations.
pub(crate) fn expand_closed_map_implication_remainders(
    initial: &Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<Vec<(Term, Term)>>> {
    let mut expanded = false;
    let mut branches = vec![Vec::new()];
    for (pattern, subject) in remainder {
        let pattern = substitute(pattern, initial);
        let subject = substitute(subject, initial);
        let expansion = match (pattern.kind(), subject.kind()) {
            (
                TermKind::Map {
                    definition: pattern_definition,
                    entries: pattern_entries,
                    rest: None,
                },
                TermKind::Map {
                    definition: subject_definition,
                    entries: subject_entries,
                    rest: Some(subject_rest),
                },
            ) if pattern_definition == subject_definition
                && subject_entries.len() <= pattern_entries.len() =>
            {
                let mut solutions = Vec::new();
                ClosedMapImplicationProblem {
                    pattern_definition,
                    pattern_entries,
                    subject_entries,
                    subject_rest,
                }
                .enumerate(0, Vec::new(), &mut solutions);
                Some(solutions)
            }
            _ => None,
        };
        let Some(expansion) = expansion else {
            for branch in &mut branches {
                branch.push((pattern.clone(), subject.clone()));
            }
            continue;
        };
        expanded = true;
        let mut next = Vec::new();
        for branch in branches {
            for equations in &expansion {
                let mut combined = branch.clone();
                combined.extend(equations.iter().cloned());
                next.push(combined);
            }
        }
        branches = next;
    }
    if !expanded {
        return None;
    }
    branches.sort();
    branches.dedup();
    Some(branches)
}

struct ClosedMapImplicationProblem<'a> {
    pattern_definition: &'a Arc<MapDefinition>,
    pattern_entries: &'a [(Term, Term)],
    subject_entries: &'a [(Term, Term)],
    subject_rest: &'a Term,
}

impl ClosedMapImplicationProblem<'_> {
    fn enumerate(
        &self,
        subject_index: usize,
        selected: Vec<(usize, Vec<(Term, Term)>)>,
        solutions: &mut Vec<Vec<(Term, Term)>>,
    ) {
        if subject_index == self.subject_entries.len() {
            let selected_indices = selected
                .iter()
                .map(|(index, _)| *index)
                .collect::<BTreeSet<_>>();
            let remaining = self
                .pattern_entries
                .iter()
                .enumerate()
                .filter(|(index, _)| !selected_indices.contains(index))
                .map(|(_, entry)| entry.clone())
                .collect();
            let mut equations = selected
                .into_iter()
                .flat_map(|(_, equations)| equations)
                .collect::<Vec<_>>();
            equations.push((
                self.subject_rest.clone(),
                Term::map(self.pattern_definition.clone(), remaining, None),
            ));
            solutions.push(equations);
            return;
        }

        let (subject_key, subject_value) = &self.subject_entries[subject_index];
        let used = selected
            .iter()
            .map(|(index, _)| *index)
            .collect::<BTreeSet<_>>();
        // Each level assigns subject entry `subject_index` to an unused pattern entry and recurses
        // on the next subject entry, so the depth is bounded by the number of subject entries.
        // Invariant: `selected` pairs each earlier subject entry with a distinct pattern entry.
        for (pattern_index, (pattern_key, pattern_value)) in self.pattern_entries.iter().enumerate()
        {
            if used.contains(&pattern_index) {
                continue;
            }
            let mut next = selected.clone();
            next.push((
                pattern_index,
                vec![
                    (subject_key.clone(), pattern_key.clone()),
                    (subject_value.clone(), pattern_value.clone()),
                ],
            ));
            self.enumerate(subject_index + 1, next, solutions);
        }
    }
}

/// Every result of `LIST.update(L, I, V)` is a fixed point of updating at `I` with `V`.
/// Reuse the hook to refute a concrete result with a conflicting element or an out-of-range index.
/// This necessary condition is independent of `L`; satisfying it does not solve for the base list.
pub(super) fn list_update_cannot_match(pattern: &Term, subject: &Term) -> bool {
    let TermKind::Application {
        symbol, arguments, ..
    } = pattern.kind()
    else {
        return false;
    };
    if symbol.attributes.hook.as_deref() != Some("LIST.update")
        || !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
        || !subject.attributes().constructor_like
        || !matches!(subject.kind(), TermKind::List { rest: None, .. })
    {
        return false;
    }
    let [_, index, value] = arguments.as_slice() else {
        return false;
    };
    // false only declines to refute the match; a stop is minted again by the caller's next poll.
    match evaluate_hook(
        "LIST.update",
        &[subject.clone(), index.clone(), value.clone()],
    ) {
        Ok(Ok(BuiltinResult::Bottom)) => true,
        Ok(Ok(BuiltinResult::Value(updated))) => {
            updated.attributes().constructor_like && updated != *subject
        }
        Ok(_) => false,
        Err(stop) => {
            stop.forgo_refinement();
            false
        }
    }
}

pub(super) enum PairRemainder {
    Left(Vec<Term>),
    Right(Vec<Term>),
}

pub(super) fn pair_prefix(
    left: &[Term],
    right: &[Term],
) -> (Vec<(Term, Term)>, Option<PairRemainder>) {
    let common = left.len().min(right.len());
    let pairs = left[..common]
        .iter()
        .cloned()
        .zip(right[..common].iter().cloned())
        .collect();
    let remainder = if left.len() > common {
        Some(PairRemainder::Left(left[common..].to_vec()))
    } else if right.len() > common {
        Some(PairRemainder::Right(right[common..].to_vec()))
    } else {
        None
    };
    (pairs, remainder)
}

pub(super) fn pair_suffix(
    left: &[Term],
    right: &[Term],
) -> (Vec<(Term, Term)>, Option<PairRemainder>) {
    let common = left.len().min(right.len());
    let pairs = left[left.len() - common..]
        .iter()
        .cloned()
        .zip(right[right.len() - common..].iter().cloned())
        .collect();
    let remainder = if left.len() > common {
        Some(PairRemainder::Left(left[..left.len() - common].to_vec()))
    } else if right.len() > common {
        Some(PairRemainder::Right(right[..right.len() - common].to_vec()))
    } else {
        None
    };
    (pairs, remainder)
}

pub(super) fn prepend(pair: (Term, Term), mut pairs: Vec<(Term, Term)>) -> Vec<(Term, Term)> {
    pairs.insert(0, pair);
    pairs
}

/// Whether `map`'s attributes show that it binds each of its keys once: a map term that binds a
/// key twice is neither constructor-like nor `ceil_free` (`Term::map`, `term::ceil_free`).
pub(super) fn binds_each_key_once(map: &Term) -> bool {
    map.attributes().constructor_like || map.attributes().ceil_free()
}

/// Whether `entries`, a map term's entries in their stored `(key, value)` order, bind some key
/// twice: the bindings of one key are adjacent there.
fn repeats_a_key(entries: &[(Term, Term)]) -> bool {
    entries.windows(2).any(|pair| pair[0].0 == pair[1].0)
}

/// The entries of a pattern map and of a subject map, split by their keys.
pub(super) struct CommonKeys<K, V> {
    /// The pattern's and the subject's values of each key both bind, in key order.
    pub(super) values: Vec<(V, V)>,
    /// The pattern's entries whose key the subject does not bind, in key order.
    pub(super) pattern_only: Vec<(K, V)>,
    /// The subject's entries whose key the pattern does not bind, in key order.
    pub(super) subject_only: Vec<(K, V)>,
}

/// The keys `pattern` and `subject` bind both, syntactically, and the entries of each outside
/// them.
///
/// Both are entries in the stored order of a map term, `(key, value)` (`Term::map`), and neither
/// binds a key twice, so the keys of each are strictly increasing: each pattern key is found in
/// the subject by binary search, after the place of the previous one, and the subject's entries
/// are copied once, around the places found, without comparing them. A step that reads one
/// binding of an `n`-entry map makes `O(log n)` key comparisons here.
pub(super) fn split_common_keys<K: Ord + Clone, V: Clone>(
    pattern: &[(K, V)],
    subject: &[(K, V)],
) -> CommonKeys<K, V> {
    find_common_keys(pattern, subject).split(subject)
}

/// The keys `pattern` and `subject` bind both, as [`split_common_keys`] finds them, before the
/// subject's other entries are copied.
pub(super) struct FoundKeys<K, V> {
    /// As [`CommonKeys::values`].
    pub(super) values: Vec<(V, V)>,
    /// As [`CommonKeys::pattern_only`].
    pub(super) pattern_only: Vec<(K, V)>,
    /// The subject's indices of the common keys, increasing.
    found: Vec<usize>,
}

impl<K: Clone, V: Clone> FoundKeys<K, V> {
    /// The split, with the subject's entries outside the common keys copied once.
    pub(super) fn split(self, subject: &[(K, V)]) -> CommonKeys<K, V> {
        let Self {
            values,
            pattern_only,
            found,
        } = self;
        let mut subject_only = Vec::with_capacity(subject.len() - found.len());
        let mut start = 0;
        for index in found {
            subject_only.extend_from_slice(&subject[start..index]);
            start = index + 1;
        }
        subject_only.extend_from_slice(&subject[start..]);
        CommonKeys {
            values,
            pattern_only,
            subject_only,
        }
    }
}

/// The search half of [`split_common_keys`]: `O(log n)` key comparisons per pattern key and no
/// copy of the subject's other entries.
pub(super) fn find_common_keys<K: Ord + Clone, V: Clone>(
    pattern: &[(K, V)],
    subject: &[(K, V)],
) -> FoundKeys<K, V> {
    let mut values = Vec::new();
    let mut pattern_only = Vec::new();
    let mut found = Vec::new();
    let mut from = 0;
    for (key, value) in pattern {
        match subject[from..].binary_search_by(|(subject_key, _)| subject_key.cmp(key)) {
            Ok(offset) => {
                let index = from + offset;
                values.push((value.clone(), subject[index].1.clone()));
                found.push(index);
                from = index + 1;
            }
            Err(offset) => {
                pattern_only.push((key.clone(), value.clone()));
                from += offset;
            }
        }
    }
    FoundKeys {
        values,
        pattern_only,
        found,
    }
}

pub(super) struct MapRemainder {
    pub(super) concrete: Vec<(Term, Term)>,
    pub(super) symbolic: Vec<(Term, Term)>,
    pub(super) rest: Option<Term>,
}

impl MapRemainder {
    pub(super) fn new(entries: Vec<(Term, Term)>, rest: Option<Term>) -> Self {
        let (concrete, symbolic) = entries
            .into_iter()
            .partition(|(key, _)| key.attributes().constructor_like);
        Self {
            concrete,
            symbolic,
            rest,
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.concrete.is_empty() && self.symbolic.is_empty() && self.rest.is_none()
    }

    pub(super) fn to_term(&self, definition: Arc<MapDefinition>) -> Term {
        let entries = self
            .concrete
            .iter()
            .chain(&self.symbolic)
            .cloned()
            .collect();
        Term::map(definition, entries, self.rest.clone())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;
    use crate::counted::Counted;

    /// A pattern that binds one key of an `n`-entry subject finds it with at most
    /// `ilog2(n) + 1` key comparisons, the binary search's own count, and the subject's other
    /// entries are copied around the place found without being compared: one comparison per entry
    /// would mean the subject was scanned or reordered. A key the subject does not bind costs no
    /// more, and leaves the subject whole.
    #[test]
    fn one_pattern_key_is_found_in_the_subject_by_binary_search() {
        const ENTRIES: u32 = 4096;
        let comparisons = Cell::new(0);
        let counted = |value| Counted {
            value,
            comparisons: &comparisons,
        };
        let subject = (1..=ENTRIES)
            .map(|index| (counted(2 * index), index))
            .collect::<Vec<_>>();
        let bound = ENTRIES.ilog2() as usize + 1;
        let values_of = |entries: &[(Counted<'_>, u32)]| -> Vec<u32> {
            entries.iter().map(|(key, _)| key.value).collect()
        };
        for (probe, bound_in_subject) in [
            (2, true),
            (ENTRIES, true),
            (2 * ENTRIES, true),
            (1, false),
            (ENTRIES + 1, false),
            (2 * ENTRIES + 1, false),
        ] {
            let pattern = [(counted(probe), 0)];
            comparisons.set(0);
            let CommonKeys {
                values,
                pattern_only,
                subject_only,
            } = split_common_keys(&pattern, &subject);
            let made = comparisons.get();
            assert!(
                made <= bound,
                "key {probe}: {made} comparisons, bound {bound}"
            );
            let expected_rest: Vec<u32> = (1..=ENTRIES)
                .map(|index| 2 * index)
                .filter(|&key| key != probe)
                .collect();
            assert_eq!(values_of(&subject_only), expected_rest, "key {probe}");
            if bound_in_subject {
                assert_eq!(values, [(0, probe / 2)], "key {probe}");
                assert!(pattern_only.is_empty(), "key {probe}");
            } else {
                assert!(values.is_empty(), "key {probe}");
                assert_eq!(values_of(&pattern_only), [probe], "key {probe}");
            }
        }
    }
}
