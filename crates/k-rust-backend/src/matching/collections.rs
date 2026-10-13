//! ```toml algorithm
//! id = "backend.matching.collections"
//! name = "associative and associative-commutative collection matching"
//! sites = ["solve_collection_pairs_in_definition", "solve_collection_pair", "solve_list_pair", "solve_map_pair", "solve_set_pair", "match_collection_remainders_all_in_definition", "cancel_common_opaque_chunks", "list_implication_expansion"]
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
//! mode = "frame of one map or set assignment (the subject without the assigned items)"
//! bound = "O(k log n): one removal from the subject's tree per assigned item"
//!
//! [[cost]]
//! mode = "lists"
//! bound = "O(h) solve_term_pair calls per list pair"
//!
//! [[cost]]
//! mode = "list frame (the closed side without the items outside the frames)"
//! bound = "O(log n): two cuts of the closed side's tree"
//!
//! [[cost]]
//! mode = "list item positions in an implication remainder (list_implication_expansion)"
//! bound = "O(k n) item matches, each pattern item against each subject position at most once; at most C(n, k) branches, each O(k log n) nodes (one cut of the subject's trees per run of parts)"
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
//! cancellation. A frame is never copied: a map or set frame is the subject's tree with the
//! assigned items removed, a list frame a cut of the closed side, so a frame costs the logarithm
//! of the subject's size, not its size. In an implication remainder, a list pattern with an item
//! between two parts is expanded into one branch per position of its items in the subject list
//! (`list_implication_expansion`), each part a cut of the subject's trees;
//! `Counter::MatchingCollectionProblems`. The per-pair rules (sorts, overloads,
//! injections) stay in `solve_term_pair`, which is why no generic AC matcher replaces this.

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::{BuiltinResult, evaluate_hook},
    condition::MatchSolution,
    definition::BackendDefinition,
    substitution::{Substitution, substitute},
    term::{
        CollectionMetadata, Items, ListDefinition, MapDefinition, Name, Sort, SymbolType, Term,
        TermKind, Variable, chunked::Item,
    },
    unification::{MatchUnification, unify_from},
};

use super::{FailReason, MatchFailed, MatchMode, MatchResult, match_terms_with_context};
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
    closed: &Items<Term>,
    framed_heads: &Items<Term>,
    frame: &Term,
    framed_tails: &Items<Term>,
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

    let heads_end = framed_heads.len();
    // The closed side's items between the framed side's heads and tails, cut from its tree.
    let framed = Term::list_of_items(
        definition.clone(),
        closed
            .split_at(heads_end)
            .1
            .split_at(frame_end - heads_end)
            .0,
        None,
    );
    let mut pairs = Vec::with_capacity(heads_end + framed_tails.len() + 1);
    let closed_ends = closed
        .range(..heads_end)
        .zip(framed_heads.iter())
        .chain(closed.range(frame_end..).zip(framed_tails.iter()));
    if frame_on_subject {
        pairs.extend(closed_ends.map(|(known, other)| (known.clone(), other.clone())));
        pairs.push((framed, frame.clone()));
    } else {
        pairs.extend(closed_ends.map(|(known, other)| (other.clone(), known.clone())));
        pairs.push((frame.clone(), framed));
    }
    solve_ordered_term_pairs(mode, backend, solution, pairs, narrowing, depth)
}

#[allow(clippy::too_many_arguments)]
fn solve_two_list_frames(
    mode: MatchMode,
    backend: &BackendDefinition,
    definition: &Arc<ListDefinition>,
    solution: CollectionSolution,
    pattern_heads: &Items<Term>,
    pattern_middle: &Term,
    pattern_tails: &Items<Term>,
    subject_heads: &Items<Term>,
    subject_middle: &Term,
    subject_tails: &Items<Term>,
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
    let none = Items::new;
    let (pattern_extra_heads, subject_extra_heads) = match head_remainder {
        Some(PairRemainder::Left(terms)) => (terms, none()),
        Some(PairRemainder::Right(terms)) => (none(), terms),
        None => (none(), none()),
    };
    let (pattern_extra_tails, subject_extra_tails) = match tail_remainder {
        Some(PairRemainder::Left(terms)) => (terms, none()),
        Some(PairRemainder::Right(terms)) => (none(), terms),
        None => (none(), none()),
    };
    let pattern_has_extra = !pattern_extra_heads.is_empty() || !pattern_extra_tails.is_empty();
    let subject_has_extra = !subject_extra_heads.is_empty() || !subject_extra_tails.is_empty();
    if pattern_has_extra && subject_has_extra {
        return None;
    }
    let middle_pair = if pattern_has_extra {
        (
            Term::list_of_items(
                definition.clone(),
                pattern_extra_heads,
                Some((pattern_middle.clone(), pattern_extra_tails)),
            ),
            subject_middle.clone(),
        )
    } else if subject_has_extra {
        (
            pattern_middle.clone(),
            Term::list_of_items(
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
        remaining: Items<(Term, Term)>,
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
        // A candidate's unassigned entries are `remaining` without it, one removal by path copy.
        for (subject_index, (subject_key, subject_value)) in remaining.iter().enumerate() {
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
                    self.search(
                        index + 1,
                        remaining.remove_at(subject_index).0,
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
        remaining: Items<(Term, Term)>,
        frame_entries: Vec<(Term, Term)>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if frame_entries.is_empty() {
            if let Some(rest) = &self.rest {
                let subject = Term::map_of_items(
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
        let remainder = Term::map_of_items(self.definition.clone(), remaining, Some(fresh_term));
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
/// element and that concatenation as its rest. The elements are the set's tree, shared, not
/// copied.
fn set_parts(term: &Term) -> Option<(Arc<crate::term::SetDefinition>, Items<Term>, Option<Term>)> {
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
                Some((
                    definition.clone(),
                    Items::from_vec(Vec::new()),
                    Some(term.clone()),
                ))
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
    // A set that holds an element twice is `\bottom` (set concatenation is nilpotent,
    // `Term::set`); as for a map with a repeated key, no solution is claimed for it. The
    // elements are in the set's order, so a repeat is a pair of neighbours, which the summary
    // of each side's tree records.
    if pattern_elements.summary().collision || subject_elements.summary().collision {
        return None;
    }
    // The elements both sides hold syntactically cancel: each pattern element is sought in the
    // subject's tree, and the subject's other elements are that tree with the found ones
    // removed, `O(k log n)` nodes built for `k` pattern elements.
    let found = find_common_elements(&pattern_elements, &subject_elements);
    let subject_elements = found.subject_only(&subject_elements);
    measure::bump(Counter::MatchingCollectionProblems);
    let problem = SetCollectionProblem {
        mode,
        backend: definition,
        definition: pattern_definition.clone(),
        elements: found.pattern_only,
        rest: pattern_rest,
        subject_rest,
        depth,
    };
    let mut found = Vec::new();
    let mut indeterminate = false;
    problem.search(
        0,
        subject_elements,
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
        remaining: Items<Term>,
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
        // A candidate's unassigned elements are `remaining` without it, one removal by path copy.
        for (subject_index, candidate) in remaining.iter().enumerate() {
            match solve_term_pair(
                self.mode,
                self.backend,
                solution.clone(),
                element,
                candidate,
                narrowing,
                self.depth,
            ) {
                PairSolution::Solved(found) => {
                    for solution in found {
                        self.search(
                            index + 1,
                            remaining.remove_at(subject_index).0,
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
        remaining: Items<Term>,
        frame_elements: Vec<Term>,
        solution: CollectionSolution,
        narrowing: &mut Option<&mut Narrowing<'_>>,
        solutions: &mut Vec<CollectionSolution>,
        indeterminate: &mut bool,
    ) {
        if frame_elements.is_empty() {
            if let Some(rest) = &self.rest {
                let subject = Term::set_of_items(
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
        let remainder = Term::set_of_items(self.definition.clone(), remaining, Some(fresh_term));
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

/// Expand the collection pairs of an implication remainder into a disjunction of ordinary term
/// equations: a closed destination map against an open current map has one branch per entry
/// assignment, and a destination list with two or more parts and an item against a current
/// list one branch per position of its items (`list_implication_expansion`). The pairs of a
/// remainder hold together, so the branches of two expanded pairs multiply. The implication
/// layer simplifies and existentially quantifies each branch uniformly with its other
/// obligations. `None` when no pair is expanded; an empty disjunction (`Some` of no branch)
/// when a pair has no branch, which refutes the remainder.
pub(crate) fn expand_implication_remainders(
    definition: &BackendDefinition,
    initial: &Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<Vec<(Term, Term)>>> {
    let mut expanded = false;
    let mut branches = vec![Vec::new()];
    for (pattern, subject) in remainder {
        let pattern = substitute(pattern, initial);
        let subject = substitute(subject, initial);
        let expansion = closed_map_expansion(&pattern, &subject)
            .or_else(|| list_implication_expansion(definition, &pattern, &subject));
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

/// The entry assignments of a closed destination map against an open current map: each is one
/// AC entry permutation expressed as ordinary term equalities.
fn closed_map_expansion(pattern: &Term, subject: &Term) -> Option<Vec<Vec<(Term, Term)>>> {
    match (pattern.kind(), subject.kind()) {
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
    }
}

/// One run of a list read as the sequence of its parts: items in order (a tree, shared with the
/// list it was read from), or an opaque term that stands for any list.
#[derive(Clone)]
enum ListRun {
    Items(Items<Term>),
    Part(Term),
}

/// The list of `definition` that `term` is, as a list term or as an application of its
/// concatenation.
fn list_definition_of(term: &Term) -> Option<&Arc<ListDefinition>> {
    match term.kind() {
        TermKind::List { definition, .. } => Some(definition),
        TermKind::Application { symbol, .. } => match &symbol.attributes.collection {
            Some(CollectionMetadata::List(definition))
                if symbol.name == definition.symbols.concat =>
            {
                Some(definition)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Read `term` as a list of `definition`, appending its runs to `runs` in order: the heads, the
/// middle read the same way, and the tails of a list term; the operands of a concatenation in
/// order (recording its head); any other term as one part. Neighbouring item runs are joined.
fn flatten_list_runs(
    definition: &Arc<ListDefinition>,
    term: &Term,
    runs: &mut Vec<ListRun>,
    head: &mut Option<OpaqueConcatHead>,
) {
    fn push_items(runs: &mut Vec<ListRun>, items: &Items<Term>) {
        if items.is_empty() {
            return;
        }
        if let Some(ListRun::Items(last)) = runs.last_mut() {
            *last = last.join(items);
        } else {
            runs.push(ListRun::Items(items.clone()));
        }
    }

    match term.kind() {
        TermKind::List {
            definition: found,
            heads,
            rest,
        } if found == definition => {
            push_items(runs, heads);
            if let Some((middle, tails)) = rest {
                flatten_list_runs(definition, middle, runs, head);
                push_items(runs, tails);
            }
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } if symbol.name == definition.symbols.concat
            && let [left, right] = arguments.as_slice() =>
        {
            head.get_or_insert_with(|| OpaqueConcatHead {
                symbol: symbol.clone(),
                sort_arguments: sort_arguments.clone(),
            });
            flatten_list_runs(definition, left, runs, head);
            flatten_list_runs(definition, right, runs, head);
        }
        _ => runs.push(ListRun::Part(term.clone())),
    }
}

/// The list of `definition` that is the concatenation of `runs` in order. With at most one part
/// it is a list term; with more, `head` (the concatenation that held them) joins them.
fn concat_list_runs(
    definition: &Arc<ListDefinition>,
    head: Option<&OpaqueConcatHead>,
    runs: Vec<ListRun>,
) -> Term {
    let parts = runs
        .iter()
        .filter(|run| matches!(run, ListRun::Part(_)))
        .count();
    if parts <= 1 {
        let mut heads = Items::new();
        let mut middle = None;
        let mut tails = Items::new();
        for run in runs {
            match run {
                ListRun::Items(items) if middle.is_none() => heads = heads.join(&items),
                ListRun::Items(items) => tails = tails.join(&items),
                ListRun::Part(part) => middle = Some(part),
            }
        }
        return Term::list_of_items(definition.clone(), heads, middle.map(|part| (part, tails)));
    }
    let head = head.expect("two parts of a list came from a concatenation");
    runs.into_iter()
        .map(|run| match run {
            ListRun::Items(items) => Term::list_of_items(definition.clone(), items, None),
            ListRun::Part(part) => part,
        })
        .reduce(|left, right| {
            Term::application(
                head.symbol.clone(),
                head.sort_arguments.clone(),
                vec![left, right],
            )
        })
        .expect("a list with two parts has runs")
}

/// The branches of a destination list `pattern` with two or more parts and at least one item
/// against a current list `subject` of the same definition, or `None` for any other pair.
///
/// A list value is a finite sequence and concatenation is associative with unit `.List`, so
/// `pattern = subject` holds exactly when the elements line up: each item of the pattern is one
/// element of the subject, in order, and each run of the pattern's parts between two items (or an
/// end) is the subject between them. Each branch places the pattern's items at increasing
/// positions of the subject's items, and states that each item equals the subject's item there
/// and that each run of parts equals the subject's cut between its neighbouring items, the
/// subject's parts that lie there included. Items with no part between them take neighbouring
/// positions with no subject part between them; items before the pattern's first part start at
/// the subject's first item and items after its last part end at its last, with no subject part
/// beyond them. Each branch implies the equation by associativity.
///
/// When the subject has no part, every element of its value is at a known position, so the
/// branches are equivalent to the equation, and an empty set of them refutes it. A subject part
/// may hold a pattern item, or be empty under an adjacency across it, which no known-position
/// branch states, so a subject with a part adds the equation itself as one more branch: the
/// disjunction stays equivalent to the equation, and an item found at a known position decides
/// it.
///
/// A position where the pattern's item fails to match the subject's item is a false branch and
/// is dropped; a match that succeeds or is left open keeps the item's equation for the
/// implication to decide.
fn list_implication_expansion(
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
) -> Option<Vec<Vec<(Term, Term)>>> {
    let list = list_definition_of(pattern)?;
    if list_definition_of(subject) != Some(list) {
        return None;
    }
    let mut head = None;
    let mut pattern_runs = Vec::new();
    flatten_list_runs(list, pattern, &mut pattern_runs, &mut head);
    // The pattern as blocks of items between runs of parts: `blocks[0]` before the first run
    // and `blocks[j]` after `parts[j - 1]`; the inner blocks are not empty.
    let mut blocks = vec![Vec::new()];
    let mut parts: Vec<Vec<ListRun>> = Vec::new();
    let mut part_count = 0;
    for run in pattern_runs {
        match run {
            ListRun::Items(items) => blocks
                .last_mut()
                .expect("the pattern's blocks start with one")
                .extend(items.iter().cloned()),
            ListRun::Part(part) => {
                part_count += 1;
                if blocks.last().is_some_and(Vec::is_empty) && !parts.is_empty() {
                    parts
                        .last_mut()
                        .expect("a run of parts precedes an empty block")
                        .push(ListRun::Part(part));
                } else {
                    parts.push(vec![ListRun::Part(part)]);
                    blocks.push(Vec::new());
                }
            }
        }
    }
    if part_count < 2 || blocks.iter().all(Vec::is_empty) {
        return None;
    }
    measure::bump(Counter::MatchingCollectionProblems);

    let mut subject_runs = Vec::new();
    flatten_list_runs(list, subject, &mut subject_runs, &mut head);
    let current = ListSubject::new(subject_runs);
    let mut problem = ListImplicationProblem {
        definition,
        list,
        head: head.as_ref(),
        blocks: &blocks,
        parts: &parts,
        subject: &current,
        matched: std::collections::HashMap::new(),
    };
    let mut branches = Vec::new();
    problem.enumerate(&mut Vec::new(), &mut branches);
    if current.has_part() {
        branches.push(vec![(pattern.clone(), subject.clone())]);
    }
    Some(branches)
}

/// A current list as runs, indexed by item position: `n` items at positions `0 … n-1`, and each
/// part at the cut point (`0 … n`) between the items around it.
struct ListSubject {
    runs: Vec<ListRun>,
    /// The position of the first item of each item run, with the run's index, in order.
    item_runs: Vec<(usize, usize)>,
    /// The cut point of each part, in order.
    part_points: Vec<usize>,
    len: usize,
}

impl ListSubject {
    fn new(runs: Vec<ListRun>) -> Self {
        let mut item_runs = Vec::new();
        let mut part_points = Vec::new();
        let mut len = 0;
        for (index, run) in runs.iter().enumerate() {
            match run {
                ListRun::Items(items) => {
                    item_runs.push((len, index));
                    len += items.len();
                }
                ListRun::Part(_) => part_points.push(len),
            }
        }
        Self {
            runs,
            item_runs,
            part_points,
            len,
        }
    }

    fn has_part(&self) -> bool {
        !self.part_points.is_empty()
    }

    /// Whether a part lies at a cut point in `first ..= last`.
    fn part_within(&self, first: usize, last: usize) -> bool {
        let from = self.part_points.partition_point(|point| *point < first);
        self.part_points
            .get(from)
            .is_some_and(|point| *point <= last)
    }

    fn item(&self, position: usize) -> &Term {
        let run = self
            .item_runs
            .partition_point(|(start, _)| *start <= position)
            - 1;
        let (start, index) = self.item_runs[run];
        let ListRun::Items(items) = &self.runs[index] else {
            unreachable!("an item run holds items")
        };
        items
            .get(position - start)
            .expect("a position below the subject's length")
    }

    /// The subject between cut points `from` and `to`: its items at `from … to-1` and its parts
    /// at cut points `from ..= to`, as cuts of its trees.
    fn cut(&self, from: usize, to: usize) -> Vec<ListRun> {
        let mut cut = Vec::new();
        let mut start = 0;
        for run in &self.runs {
            match run {
                ListRun::Items(items) => {
                    let end = start + items.len();
                    let (low, high) = (from.max(start), to.min(end));
                    if low < high {
                        // Only an end inside the run cuts its tree.
                        let mut items = items.clone();
                        if high < end {
                            items = items.split_at(high - start).0;
                        }
                        if low > start {
                            items = items.split_at(low - start).1;
                        }
                        cut.push(ListRun::Items(items));
                    }
                    start = end;
                }
                ListRun::Part(part) => {
                    if from <= start && start <= to {
                        cut.push(ListRun::Part(part.clone()));
                    }
                }
            }
        }
        cut
    }
}

struct ListImplicationProblem<'a> {
    definition: &'a BackendDefinition,
    list: &'a Arc<ListDefinition>,
    head: Option<&'a OpaqueConcatHead>,
    blocks: &'a [Vec<Term>],
    parts: &'a [Vec<ListRun>],
    subject: &'a ListSubject,
    /// Whether the item `(block, offset)` can be the subject's item at a position: no `false`
    /// entry without a failed match.
    matched: std::collections::HashMap<(usize, usize, usize), bool>,
}

impl ListImplicationProblem<'_> {
    /// Whether the pattern's item `offset` of block `block` may be the subject's item at
    /// `position`: false only when their match fails, so no instance makes them equal.
    fn item_matches(&mut self, block: usize, offset: usize, position: usize) -> bool {
        if let Some(found) = self.matched.get(&(block, offset, position)) {
            return *found;
        }
        let found = !matches!(
            match_terms_with_context(
                MatchMode::Implies,
                self.definition.sort_graph(),
                Some(self.definition),
                &self.blocks[block][offset],
                self.subject.item(position),
                // A collection element is never the root an equation is tried on.
                false,
            ),
            MatchResult::Failed(reason) if !matches!(reason, FailReason::Subsorting(_))
        );
        self.matched.insert((block, offset, position), found);
        found
    }

    /// Whether block `block` may start at `start`: it fits, no subject part lies between its
    /// items (`start + 1 … start + len - 1`), and each of its items matches.
    fn block_fits(&mut self, block: usize, start: usize) -> bool {
        let len = self.blocks[block].len();
        if start + len > self.subject.len {
            return false;
        }
        if len > 1 && self.subject.part_within(start + 1, start + len - 1) {
            return false;
        }
        (0..len).all(|offset| self.item_matches(block, offset, start + offset))
    }

    /// Place each block from `starts.len()` on, after those placed (`starts[j]` is block `j`'s
    /// first position), and push a branch for each placement of all of them.
    ///
    /// Each level places one block and recurses on the next, so the depth is the number of
    /// blocks. Invariant: the blocks in `starts` are placed at increasing, non-overlapping
    /// positions, and each fits.
    fn enumerate(&mut self, starts: &mut Vec<usize>, branches: &mut Vec<Vec<(Term, Term)>>) {
        let block = starts.len();
        let last = self.blocks.len() - 1;
        if block > last {
            branches.push(self.branch(starts));
            return;
        }
        let len = self.blocks[block].len();
        let n = self.subject.len;
        // The first position after the previous block.
        let earliest = starts
            .last()
            .map_or(0, |start| start + self.blocks[block - 1].len());
        let candidates = if block == 0 {
            // Before the pattern's first part: at the subject's first item, with no part ahead.
            if len > 0 && self.subject.part_within(0, 0) {
                return;
            }
            0..1
        } else if block == last {
            // After the pattern's last part: at the subject's last item, with no part beyond.
            let Some(start) = n.checked_sub(len) else {
                return;
            };
            if start < earliest || (len > 0 && self.subject.part_within(start + 1, n)) {
                return;
            }
            start..start + 1
        } else {
            // An inner block (not empty): anywhere before the room the later blocks need.
            let later = self.blocks[block + 1..].iter().map(Vec::len).sum::<usize>();
            let Some(latest) = n.checked_sub(later + len) else {
                return;
            };
            if earliest > latest {
                return;
            }
            earliest..latest + 1
        };
        for start in candidates {
            if self.block_fits(block, start) {
                starts.push(start);
                self.enumerate(starts, branches);
                starts.pop();
            }
        }
    }

    /// The equations of one placement: each item with the subject's item at its position, and
    /// each run of parts with the subject's cut between its neighbouring items.
    fn branch(&self, starts: &[usize]) -> Vec<(Term, Term)> {
        let mut equations = Vec::new();
        for (block, (items, start)) in self.blocks.iter().zip(starts).enumerate() {
            for (offset, item) in items.iter().enumerate() {
                equations.push((item.clone(), self.subject.item(start + offset).clone()));
            }
            if let Some(parts) = self.parts.get(block) {
                let from = start + items.len();
                let to = starts[block + 1];
                equations.push((
                    concat_list_runs(self.list, self.head, parts.clone()),
                    concat_list_runs(self.list, self.head, self.subject.cut(from, to)),
                ));
            }
        }
        equations
    }
}

struct ClosedMapImplicationProblem<'a> {
    pattern_definition: &'a Arc<MapDefinition>,
    pattern_entries: &'a Items<(Term, Term)>,
    subject_entries: &'a Items<(Term, Term)>,
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
            // The pattern's entries no subject entry selected: its tree with the selected ones
            // removed, last first so that the positions still to remove do not move.
            let selected_indices = selected
                .iter()
                .map(|(index, _)| *index)
                .collect::<BTreeSet<_>>();
            let remaining = selected_indices
                .iter()
                .rev()
                .fold(self.pattern_entries.clone(), |entries, &index| {
                    entries.remove_at(index).0
                });
            let mut equations = selected
                .into_iter()
                .flat_map(|(_, equations)| equations)
                .collect::<Vec<_>>();
            equations.push((
                self.subject_rest.clone(),
                Term::map_of_items(self.pattern_definition.clone(), remaining, None),
            ));
            solutions.push(equations);
            return;
        }

        let (subject_key, subject_value) = self
            .subject_entries
            .get(subject_index)
            .expect("below the number of subject entries");
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
    Left(Items<Term>),
    Right(Items<Term>),
}

/// The pairs of the first items of `left` and `right`, as many as the shorter has, and the
/// longer one's other items, cut from its tree: `O(k + log n)` for `k` pairs of sequences of up
/// to `n` items, so a pattern `ListItem(X) L` takes its frame from the subject's nodes.
pub(super) fn pair_prefix(
    left: &Items<Term>,
    right: &Items<Term>,
) -> (Vec<(Term, Term)>, Option<PairRemainder>) {
    let common = left.len().min(right.len());
    let pairs = left
        .range(..common)
        .cloned()
        .zip(right.range(..common).cloned())
        .collect();
    let remainder = if left.len() > common {
        Some(PairRemainder::Left(left.split_at(common).1))
    } else if right.len() > common {
        Some(PairRemainder::Right(right.split_at(common).1))
    } else {
        None
    };
    (pairs, remainder)
}

/// The pairs of the last items of `left` and `right`, as many as the shorter has, and the
/// longer one's other items, cut from its tree, as [`pair_prefix`] from the other end.
pub(super) fn pair_suffix(
    left: &Items<Term>,
    right: &Items<Term>,
) -> (Vec<(Term, Term)>, Option<PairRemainder>) {
    let common = left.len().min(right.len());
    let (left_extra, right_extra) = (left.len() - common, right.len() - common);
    let pairs = left
        .range(left_extra..)
        .cloned()
        .zip(right.range(right_extra..).cloned())
        .collect();
    let remainder = if left_extra > 0 {
        Some(PairRemainder::Left(left.split_at(left_extra).0))
    } else if right_extra > 0 {
        Some(PairRemainder::Right(right.split_at(right_extra).0))
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
/// twice: the bindings of one key are adjacent there, so the summary's adjacent-key flag
/// (`collision`) says it without reading the entries.
fn repeats_a_key(entries: &Items<(Term, Term)>) -> bool {
    entries.summary().collision
}

/// The entries of a pattern map and of a subject map, split by their keys.
pub(super) struct CommonKeys<K, V>
where
    (K, V): Item,
{
    /// The pattern's and the subject's values of each key both bind, in key order.
    pub(super) values: Vec<(V, V)>,
    /// The pattern's entries whose key the subject does not bind, in key order.
    pub(super) pattern_only: Vec<(K, V)>,
    /// The subject's entries whose key the pattern does not bind, in key order: the subject's
    /// tree without the common keys' entries.
    pub(super) subject_only: Items<(K, V)>,
}

/// The keys `pattern` and `subject` bind both, syntactically, and the entries of each outside
/// them.
///
/// Both are entries in the stored order of a map term, `(key, value)` (`Term::map`), and neither
/// binds a key twice, so the keys of each are strictly increasing: each pattern key is found in
/// the subject by binary search, and the subject's other entries are the subject's tree with the
/// found entries removed, each removal a path copy that shares every node off its path. A step
/// that reads one binding of an `n`-entry map makes `O(log n)` key comparisons here and builds
/// `O(log n)` nodes.
pub(super) fn split_common_keys<'p, K: Ord + Clone + 'p, V: Clone + 'p>(
    pattern: impl IntoIterator<Item = &'p (K, V)>,
    subject: &Items<(K, V)>,
) -> CommonKeys<K, V>
where
    (K, V): Item,
{
    find_common_keys(pattern, subject).split(subject)
}

/// The keys `pattern` and `subject` bind both, as [`split_common_keys`] finds them, before the
/// subject's other entries are taken apart from them.
pub(super) struct FoundKeys<K, V> {
    /// As [`CommonKeys::values`].
    pub(super) values: Vec<(V, V)>,
    /// As [`CommonKeys::pattern_only`].
    pub(super) pattern_only: Vec<(K, V)>,
    /// The subject's indices of the common keys, increasing.
    found: Vec<usize>,
}

impl<K: Clone, V: Clone> FoundKeys<K, V>
where
    (K, V): Item,
{
    /// The split: the subject's other entries are its tree with the found entries removed,
    /// last first so that the positions of the ones still to remove do not move.
    pub(super) fn split(self, subject: &Items<(K, V)>) -> CommonKeys<K, V> {
        let Self {
            values,
            pattern_only,
            found,
        } = self;
        let subject_only = found.iter().rev().fold(subject.clone(), |entries, &index| {
            entries.remove_at(index).0
        });
        CommonKeys {
            values,
            pattern_only,
            subject_only,
        }
    }
}

impl FoundKeys<Term, Term> {
    /// Whether every key of `subject` outside the common ones is constructor-like: the subject's
    /// count of other keys (its summary's `symbolic_keys`) is all among the found entries, which
    /// are read by position, so the other entries are not read.
    pub(super) fn others_constructor_like(&self, subject: &Items<(Term, Term)>) -> bool {
        let found_symbolic = self
            .found
            .iter()
            .filter(|&&index| {
                subject
                    .get(index)
                    .is_some_and(|(key, _)| !key.attributes().constructor_like)
            })
            .count();
        subject.symbolic_keys() == found_symbolic
    }
}

/// The search half of [`split_common_keys`]: `O(log n)` key comparisons per pattern key and no
/// node of the subject built.
pub(super) fn find_common_keys<'p, K: Ord + Clone + 'p, V: Clone + 'p>(
    pattern: impl IntoIterator<Item = &'p (K, V)>,
    subject: &Items<(K, V)>,
) -> FoundKeys<K, V>
where
    (K, V): Item,
{
    let mut values = Vec::new();
    let mut pattern_only = Vec::new();
    let mut found = Vec::new();
    for (key, value) in pattern {
        match subject.search_by(|(subject_key, _)| subject_key.cmp(key)) {
            Ok(index) => {
                let (_, subject_value) = subject.get(index).expect("a found entry");
                values.push((value.clone(), subject_value.clone()));
                found.push(index);
            }
            Err(_) => pattern_only.push((key.clone(), value.clone())),
        }
    }
    FoundKeys {
        values,
        pattern_only,
        found,
    }
}

/// The elements a pattern set and a subject set hold both, syntactically, found by
/// [`find_common_elements`] before the subject's other elements are taken apart from them.
pub(super) struct FoundElements {
    /// The pattern's elements the subject does not hold, in the set's order.
    pub(super) pattern_only: Vec<Term>,
    /// The subject's indices of the common elements, increasing.
    found: Vec<usize>,
}

impl FoundElements {
    /// The subject's other elements: its tree with the found elements removed, last first so
    /// that the positions of the ones still to remove do not move. Each removal is a path copy
    /// that shares every node off its path, so `k` common elements of an `n`-element subject
    /// build `O(k log n)` nodes.
    pub(super) fn subject_only(&self, subject: &Items<Term>) -> Items<Term> {
        self.found
            .iter()
            .rev()
            .fold(subject.clone(), |elements, &index| {
                elements.remove_at(index).0
            })
    }

    /// Whether every element of `subject` outside the common ones is constructor-like: the
    /// subject's count of other elements (its summary's `symbolic_keys`) is all among the found
    /// elements, which are read by position, so the other elements are not read.
    pub(super) fn others_constructor_like(&self, subject: &Items<Term>) -> bool {
        let found_symbolic = self
            .found
            .iter()
            .filter(|&&index| {
                subject
                    .get(index)
                    .is_some_and(|element| !element.attributes().constructor_like)
            })
            .count();
        subject.symbolic_keys() == found_symbolic
    }
}

/// The elements of `pattern` that `subject` holds too, syntactically, each found by binary search
/// in the subject's tree: `O(log n)` comparisons per pattern element and no node of the subject
/// built. Both are a set's elements in its stored order with no element twice (`Term::set`), so
/// the found positions increase with the pattern's elements.
pub(super) fn find_common_elements<'p>(
    pattern: impl IntoIterator<Item = &'p Term>,
    subject: &Items<Term>,
) -> FoundElements {
    let mut pattern_only = Vec::new();
    let mut found = Vec::new();
    for element in pattern {
        match subject.search(element) {
            Ok(index) => found.push(index),
            Err(_) => pattern_only.push(element.clone()),
        }
    }
    FoundElements {
        pattern_only,
        found,
    }
}

/// The entries of one side of a map match that the other side's keys did not bind
/// syntactically, and that side's rest. The entries are a map's tree, so whether they hold a key
/// that is not constructor-like, and which, is read from its summary (`symbolic_keys`) and by
/// seeking the subtrees that count one, without reading the constructor-like keys.
pub(super) struct MapRemainder {
    pub(super) entries: Items<(Term, Term)>,
    pub(super) rest: Option<Term>,
}

impl MapRemainder {
    pub(super) fn new(entries: Items<(Term, Term)>, rest: Option<Term>) -> Self {
        Self { entries, rest }
    }

    /// The number of entries whose key is not constructor-like.
    pub(super) fn symbolic(&self) -> usize {
        self.entries.symbolic_keys()
    }

    /// The number of entries whose key is constructor-like.
    pub(super) fn concrete(&self) -> usize {
        self.entries.len() - self.symbolic()
    }

    /// The first entry, in the map's order, whose key is not constructor-like.
    pub(super) fn first_symbolic(&self) -> Option<&(Term, Term)> {
        self.entries.symbolic_keyed().next()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.rest.is_none()
    }

    /// The map of these entries and this rest: the tree is kept as it is.
    pub(super) fn to_term(&self, definition: Arc<MapDefinition>) -> Term {
        Term::map_of_items(definition, self.entries.clone(), self.rest.clone())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;
    use crate::counted::Counted;

    /// A pattern that binds one key of an `n`-entry subject finds it with at most the
    /// comparisons of one binary search per node on a path of the subject's tree
    /// (`Items::search_comparison_bound`, logarithmic in `n`), and the subject's other
    /// entries are its tree without the found one, a removal that compares only the adjacent
    /// keys of the nodes it rebuilds on one path (`Items::path_copy_comparison_bound`): one
    /// comparison per entry would mean the subject was scanned, reordered or rebuilt. A key the
    /// subject does not bind costs no more, and leaves the subject whole, sharing its tree.
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
            .collect::<Items<_>>();
        let bound = subject.search_comparison_bound();
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
            let found = find_common_keys(&pattern, &subject);
            let made = comparisons.get();
            assert!(
                made <= bound,
                "key {probe}: {made} comparisons, bound {bound}"
            );
            comparisons.set(0);
            let CommonKeys {
                values,
                pattern_only,
                subject_only,
            } = found.split(&subject);
            let made = comparisons.get();
            let path_bound = subject.path_copy_comparison_bound();
            assert!(
                made <= path_bound,
                "key {probe}: the split made {made} comparisons, bound {path_bound}"
            );
            if !bound_in_subject {
                assert!(subject_only.shares_root(&subject), "key {probe}");
            }
            let subject_only = subject_only.to_vec();
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
