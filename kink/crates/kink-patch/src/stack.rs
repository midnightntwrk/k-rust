//! Native stack for kink's recursions over terms and JSON documents of any depth (re-pin
//! L1-3-fix-2).
//!
//! k-rust bounds neither the depth of a term nor the nesting of its JSON, and a recursion that
//! descends one level per level of its input overflows the native stack of the thread it runs
//! on, which aborts the whole process and loses every other row of the run. Two of kink's own
//! steps recurse so: k-rust's typing of an edited rule (`SentenceTyper::typing_in`, which has no
//! stack guard; [`crate::apply`]) and serde_json's parse and serialization of a document
//! ([`crate::parse_json`], [`crate::canonical_json`], the patch codec). Each measures the depth
//! of its input first, without recursion, and runs through [`with_stack`]: on the calling
//! thread's stack when enough of it remains, as before, and otherwise on a fresh segment sized
//! from that depth, which `stacker` maps for the duration of the work (k-rust-backend
//! `nesting::map_segment`) and unmaps afterwards. A segment is reserved address space whose pages
//! are committed only as the work touches them. So the outcome is a function of the input, not
//! of the thread that runs it, up to k-rust's largest segment (`nesting::STACK_LIMIT`, 4 GiB on a
//! 64-bit target), beyond which the work is refused with that limit named, without running.

use k_rust::definition::Sentence;
use k_rust::k_rust_backend::nesting::{STACK_LIMIT, SegmentRefused, map_segment};
use k_rust::kast::Term;
use std::fmt;

/// Whether kink-patch is compiled at a level at which the optimized measurements of the stack a
/// recursion takes per level hold (`build.rs`). Frame sizes, and so that stack, follow the level.
/// The optimized measurements were taken at `opt-level = 3`; `opt-level = 1`, the level of the
/// dev and test profile (k-rust's profile), was not measured, so it takes the unoptimized bounds,
/// which hold there because optimization does not enlarge a frame.
pub(crate) const OPTIMIZED: bool = cfg!(any(
    kink_opt_level = "2",
    kink_opt_level = "3",
    kink_opt_level = "s",
    kink_opt_level = "z"
));

/// The stack beyond the per-level need that work run through [`with_stack`] keeps: the fixed
/// frames below its first level and at its deepest one. Measured at most 48 KiB for kink-patch
/// `apply` and for a parse or a serialization, in either profile (L1-3-fix-2 probe).
pub(crate) const RED_ZONE: usize = 256 * 1024;

/// Upper bound on the native stack that k-rust's typing of one rule or claim takes per level of
/// its deepest term, as [`sentence_depth`] counts levels: compilation's typing
/// (`SentenceTyper::typing_in`, `resolve_semantic_casts`) of an edited rule in [`crate::apply`],
/// and either typing view of a baseline rule in `CompilationTyping::site_typing`.
///
/// Measured over 34 term shapes 3,000 levels deep (re-pin L1-3-tail, review L1-3-fix-2-1 D2;
/// the probe is in the L1-3-tail handoff): unary and binary symbols on either side, semantic and
/// syntactic casts, K sequences, lists, maps, overloads, `==K`, a six-argument function, a
/// left-hand side, `requires` and `ensures` chains of `notBool`, `andBool` and `+Int`, `#if` in a
/// branch, in the condition and around a cast, the ML connectives `#And`, `#Or`, `#Implies`,
/// `#Not`, `#Equals` and `#Ceil`, and user productions with one, two and three sort parameters.
/// By the pages the work touched on a fresh 3 GiB segment, a shape through a parametric
/// production (`#if`, an ML connective, a `{S}` production) takes 3.9 to 4.1 KiB per level in
/// the unoptimized test build (at most 4,191 bytes: `#Equals` nested in a `requires`) and 2.7
/// KiB in a release build (at most 2,755 bytes), and every other shape about 2.0 KiB and 1.7
/// KiB (at most 2,095 and 1,684); a K sequence's items take a few bytes. Part of that is
/// k-rust's own guarded recursion, which maps a segment of its own when the stack runs short:
/// every bisected shape, parametric ones included, fits a segment of 2,048 bytes per level plus
/// [`RED_ZONE`] in the test build (1,792 in release) and overflows one of 1,792 (1,536). The
/// bound is about twice the most any shape
/// touched and four times the smallest segment that held each, so a shape costlier than any
/// measured still fits (at L1-3-fix-2 it was 4 KiB, from the unary shape alone). At the bound a
/// rule at kink's document limit (`MAX_JSON_DEPTH` / 2: 300,000 term levels in release, 64,000
/// unoptimized) takes a 2.4 GiB segment, within k-rust's largest (`nesting::STACK_LIMIT`).
pub(crate) const TYPING_STACK_PER_LEVEL: usize = 8 * 1024;

/// Work that [`with_stack`] could not give the stack its input needs; it did not run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StackRefusal {
    /// The input is `levels` deep and needs `required` bytes of native stack, more than the
    /// `limit` bytes of the largest segment kink maps (k-rust-backend `nesting::STACK_LIMIT`).
    TooDeep {
        levels: usize,
        required: usize,
        limit: usize,
    },
    /// The system refused to map the segment of the size the input needs.
    Refused(SegmentRefused),
}

impl fmt::Display for StackRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooDeep {
                levels,
                required,
                limit,
            } => write!(
                formatter,
                "an input {levels} levels deep needs {required} bytes of native stack, more \
                 than the {limit} bytes of the largest stack segment kink maps"
            ),
            Self::Refused(refused) => write!(formatter, "{refused}"),
        }
    }
}

impl std::error::Error for StackRefusal {}

/// Run `work`, whose recursion descends at most `levels` levels taking at most `per_level` bytes
/// of native stack each, with that stack plus [`RED_ZONE`]: on the current thread when its
/// remaining stack covers it or is unknown (as k-rust does), otherwise on a fresh segment of that
/// size. Refused, without running, when the segment would exceed k-rust's largest segment or the
/// system refuses to map it.
pub(crate) fn with_stack<T>(
    levels: usize,
    per_level: usize,
    work: impl FnOnce() -> T,
) -> Result<T, StackRefusal> {
    let required = levels.saturating_mul(per_level).saturating_add(RED_ZONE);
    match stacker::remaining_stack() {
        None => return Ok(work()),
        Some(remaining) if required <= remaining => return Ok(work()),
        Some(_) => {}
    }
    if required > STACK_LIMIT {
        return Err(StackRefusal::TooDeep {
            levels,
            required,
            limit: STACK_LIMIT,
        });
    }
    map_segment(required, work).map_err(StackRefusal::Refused)
}

/// The number of terms on the longest path from `term` to a leaf, counted without recursion,
/// with a sequence's items counted as the chain its conversion to KORE nests them into (as
/// k-rust's own `stack::term_depth` counts them; an over-count only reserves more address
/// space).
pub(crate) fn term_depth(term: &Term) -> usize {
    let mut deepest = 0;
    let mut pending = vec![(term, 1)];
    // Invariant: `deepest` is the greatest depth of the terms popped so far, and `pending` holds
    // every unvisited child of a popped term with its depth.
    while let Some((term, depth)) = pending.pop() {
        deepest = deepest.max(depth);
        match term.unannotated() {
            Term::Sequence(items) => pending.extend(
                items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| (item, depth + 1 + index)),
            ),
            other => pending.extend(other.children().into_iter().map(|child| (child, depth + 1))),
        }
    }
    deepest
}

/// The deepest of `sentence`'s terms (its body, requires and ensures): the number of terms on the
/// longest path from one of them to a leaf, counted without recursion, with a sequence's items
/// counted as the chain its conversion to KORE nests them into (k-rust's `stack::term_depth`
/// convention). It is the depth kink sizes the typing of the sentence from, and the depth a
/// refusal of a rule too deep for kink names.
#[must_use]
pub fn sentence_depth(sentence: &Sentence) -> usize {
    (0..3)
        .filter_map(|field| crate::field_term(sentence, field))
        .map(term_depth)
        .max()
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Work too deep for any segment is refused before it runs, with the levels, the stack they
    /// need and the largest segment.
    #[test]
    fn work_too_deep_for_any_segment_is_refused_without_running() {
        let levels = STACK_LIMIT / TYPING_STACK_PER_LEVEL + 1;
        let mut ran = false;
        let refused = with_stack(levels, TYPING_STACK_PER_LEVEL, || ran = true).unwrap_err();
        assert!(!ran);
        assert!(
            matches!(refused, StackRefusal::TooDeep { levels: l, required, limit }
                if l == levels && required > limit && limit == STACK_LIMIT),
            "{refused:?}"
        );
    }

    /// Work deeper than the calling thread holds runs on a segment of the size it needs.
    #[test]
    fn work_deeper_than_the_thread_runs_on_a_segment() {
        let depth = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                fn descend(level: usize) -> usize {
                    // About 1 KiB of frame per level, kept from being optimised away.
                    let frame = std::hint::black_box([level as u8; 1024]);
                    if level == 0 {
                        usize::from(frame[0])
                    } else {
                        descend(level - 1) + 1
                    }
                }
                with_stack(20_000, 4 * 1024, || descend(20_000)).unwrap()
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(depth, 20_000);
    }

    /// The depth counts the nodes on the longest path, and a sequence's items as its chain.
    #[test]
    fn term_depth_counts_the_longest_path_and_sequences_as_chains() {
        let leaf = || Term::apply("z", vec![]);
        let mut chain = leaf();
        for _ in 0..9_999 {
            chain = Term::apply("s", vec![chain]);
        }
        assert_eq!(
            term_depth(&Term::apply("pair", vec![leaf(), chain])),
            10_001
        );
        assert_eq!(term_depth(&Term::Sequence(vec![leaf(); 100])), 1 + 100);
        assert_eq!(term_depth(&Term::Sequence(vec![])), 1);
    }
}
