//! Native stack for recursions over terms whose depth their callers do not measure.
//!
//! K bounds neither the depth of a term nor that of a sort, and the readers accept both at any
//! depth; a recursion that descends one level per level of its input therefore needs stack in
//! proportion to a depth that may be anything, and overflowing the native stack aborts the whole
//! process. Macro expansion measures the depth of what it expands and sizes its stack from it;
//! a recursion with many entry points (the sort injector) or whose input is only known once read
//! (the KAST text reader) instead calls [`guarded`] at every level: the level runs on the current
//! stack while at least [`RED_ZONE`] of it remains, and otherwise on a fresh segment of
//! [`SEGMENT`] bytes, which `stacker` maps for the duration of the level and unmaps afterwards.
//! A segment is address space whose pages are committed only as they are used, so a recursion
//! uses the stack it descends through, as it would on a thread that large, and its depth is
//! bounded by memory rather than by the thread it happens to run on.
//!
//! The check is a thread-local read and a comparison per level. On wasm32 the engine's stack
//! limit is invisible to the module and its stack cannot be switched, so the work runs on the
//! current stack unchanged.

/// The stack that must remain for one more level of a guarded recursion: more than the frames
/// any one level of a guarded recursion pushes before it reaches the next guard, in any build.
///
/// Measured as the largest drop in the remaining stack between two consecutive guards, over
/// application chains 2,000 levels deep: the conversion of KAST terms to KORE takes the most,
/// 3.0 KiB per level in a release build, 3.4 KiB in the `dev` profile (opt-level 1) and 33 KiB
/// unoptimized; sort injection takes 2.0, 2.5 and 8.5 KiB, the KAST text reader 1.2, 1.1 and
/// 6.6 KiB. 256 KiB is more than seven times the deepest of them.
#[cfg(not(target_family = "wasm"))]
pub(crate) const RED_ZONE: usize = 256 * 1024;

/// The size of each segment mapped when less than [`RED_ZONE`] remains: about 500 levels of the
/// deepest guarded recursion unoptimized and 5,000 in a release build, so a chain maps a
/// segment every few hundred to few thousand levels.
#[cfg(not(target_family = "wasm"))]
pub(crate) const SEGMENT: usize = 16 * 1024 * 1024;

/// Run `work`, one level of a recursion over a term or sort of any depth, with at least
/// [`RED_ZONE`] of native stack, on a fresh segment when the current stack has less.
#[inline]
pub(crate) fn guarded<T>(work: impl FnOnce() -> T) -> T {
    #[cfg(not(target_family = "wasm"))]
    {
        stacker::maybe_grow(RED_ZONE, SEGMENT, work)
    }
    #[cfg(target_family = "wasm")]
    {
        work()
    }
}

/// Upper bound on the native stack that the compile passes take per level of the terms they
/// walk, as [`term_depth`] counts levels: the recursions of the passes and of the term
/// operations they call (copies, comparisons, conversions to KORE), where a pass does not guard
/// its own levels ([`guarded`]).
///
/// Measured by compiling rule bodies 2,000 and 4,000 levels deep (an operator chain inside an
/// application, a nesting of a unary symbol, and the nesting on a rule's right-hand side) with
/// every stage on a segment of exactly the size this bound gives for twice the depth
/// (`DeepestTerm::run` in the pipeline): they compiled at 1 KiB per level in a release build and
/// failed at 512 bytes (`resolve_fun` and `resolve_fresh_constants`, about 1.5 KiB per level
/// of the term), compiled at 2 KiB and failed at 1 KiB in the `dev` profile (opt-level 1 with
/// debug assertions), and compiled at 8 KiB and failed at 4 KiB unoptimized. The bound is
/// twice each.
#[cfg(not(target_family = "wasm"))]
pub(crate) const STACK_PER_LEVEL: usize = if !cfg!(any(
    k_rust_opt_level = "1",
    k_rust_opt_level = "2",
    k_rust_opt_level = "3",
    k_rust_opt_level = "s",
    k_rust_opt_level = "z"
)) {
    16 * 1024
} else if cfg!(any(debug_assertions, k_rust_opt_level = "1")) {
    4 * 1024
} else {
    2 * 1024
};

/// The largest stack segment [`with_depth`] maps for one piece of work: reserved address space,
/// whose pages are committed only as the work touches them.
#[cfg(all(not(target_family = "wasm"), target_pointer_width = "64"))]
pub(crate) const STACK_LIMIT: usize = 4 << 30;
#[cfg(all(not(target_family = "wasm"), not(target_pointer_width = "64")))]
pub(crate) const STACK_LIMIT: usize = 256 << 20;

/// Work over terms deeper than any stack segment [`with_depth`] maps holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TooDeep {
    /// The depth of the deepest term the work walks.
    pub(crate) depth: usize,
    /// The stack that depth needs.
    pub(crate) required: usize,
    /// The largest segment mapped.
    pub(crate) limit: usize,
}

impl std::fmt::Display for TooDeep {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "a term {} levels deep needs {} bytes of native stack, more than the {} bytes this build provides",
            self.depth, self.required, self.limit
        )
    }
}

/// Run `work`, whose recursions descend through terms at most `depth` levels deep (as
/// [`term_depth`] counts them), with stack for all of them: on the current stack when enough of
/// it remains, and otherwise on a fresh segment of [`STACK_PER_LEVEL`] per level plus
/// [`RED_ZONE`], which `stacker` maps for the duration of the work. Refused, without running,
/// when that segment would exceed [`STACK_LIMIT`] or cannot be mapped.
pub(crate) fn with_depth<T>(depth: usize, work: impl FnOnce() -> T) -> Result<T, TooDeep> {
    #[cfg(target_family = "wasm")]
    {
        let _ = depth;
        Ok(work())
    }
    #[cfg(not(target_family = "wasm"))]
    {
        let required = depth
            .saturating_mul(STACK_PER_LEVEL)
            .saturating_add(RED_ZONE);
        let Some(remaining) = stacker::remaining_stack() else {
            return Ok(work());
        };
        if required <= remaining {
            return Ok(work());
        }
        let refused = TooDeep {
            depth,
            required,
            limit: STACK_LIMIT.max(remaining),
        };
        if required > STACK_LIMIT {
            return Err(refused);
        }
        // `stacker` maps the segment before it runs the work and panics when the mapping fails:
        // a panic before the work started is that failure, a refusal; one from the work itself
        // continues to unwind.
        let mut started = false;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            stacker::grow(required, || {
                started = true;
                work()
            })
        }));
        match outcome {
            Ok(result) => Ok(result),
            Err(_) if !started => Err(refused),
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }
}

/// The number of terms on the longest path from `term` to a leaf, counted without recursion,
/// with a sequence's items counted as the chain the conversion to KORE nests them into.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants have children"
)]
pub(crate) fn term_depth(term: &crate::kast::Term) -> usize {
    use crate::kast::Term;
    let mut deepest = 0;
    let mut pending = vec![(term, 1)];
    // Invariant: `deepest` is the greatest depth of the terms popped so far, and `pending` holds
    // every unvisited child of a popped term with its depth.
    while let Some((term, depth)) = pending.pop() {
        deepest = deepest.max(depth);
        match term.unannotated() {
            Term::Apply {
                arguments: children,
                ..
            } => {
                pending.extend(children.iter().map(|child| (child, depth + 1)));
            }
            // A sequence is a right-nested `kseq` chain once converted to KORE, which emission
            // walks one level per item: item `i` sits `i + 1` levels below the sequence.
            Term::Sequence(items) => {
                pending.extend(
                    items
                        .iter()
                        .enumerate()
                        .map(|(index, item)| (item, depth + 1 + index)),
                );
            }
            Term::Rewrite { left, right }
            | Term::As {
                pattern: left,
                alias: right,
            } => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            _ => {}
        }
    }
    deepest
}

#[cfg(all(test, not(target_family = "wasm")))]
mod tests {
    use super::*;

    /// Work over terms deeper than any segment holds is refused before any of it runs, with
    /// the depth, the stack it needs and the largest segment.
    #[test]
    fn work_too_deep_for_any_segment_is_refused_without_running() {
        let depth = STACK_LIMIT / STACK_PER_LEVEL + 1;
        let mut ran = false;
        let refused = with_depth(depth, || ran = true).unwrap_err();
        assert!(!ran);
        assert_eq!(refused.depth, depth);
        assert!(refused.required > STACK_LIMIT, "{refused:?}");
        assert!(refused.limit >= STACK_LIMIT, "{refused:?}");
    }

    /// Work over terms that fit runs, on the current stack or on a segment of the size the
    /// depth needs.
    #[test]
    fn work_that_fits_a_segment_runs() {
        assert_eq!(with_depth(10_000, || 7), Ok(7));
    }

    /// The depth counts the nodes on the longest path, annotations not counted.
    #[test]
    fn term_depth_counts_the_longest_path() {
        use crate::kast::{Label, Term};
        let leaf = Term::Variable {
            name: "X".to_owned(),
            sort: None,
        };
        let mut chain = leaf.clone();
        for _ in 0..99_999 {
            chain = Term::Apply {
                label: Label::new("s"),
                arguments: vec![chain],
            };
        }
        let pair = Term::Apply {
            label: Label::new("pair"),
            arguments: vec![leaf, chain],
        };
        assert_eq!(term_depth(&pair), 100_001);
    }

    /// A sequence of `n` items is as deep as the `kseq` chain it becomes: its last item sits
    /// `n` levels below it.
    #[test]
    fn term_depth_counts_a_sequence_as_its_chain() {
        use crate::kast::{Label, Term};
        let item = || Term::Apply {
            label: Label::new("a"),
            arguments: vec![],
        };
        let mut items = vec![item(); 999];
        items.push(Term::Apply {
            label: Label::new("s"),
            arguments: vec![item()],
        });
        assert_eq!(term_depth(&Term::Sequence(items)), 1 + 1_000 + 1);
        assert_eq!(term_depth(&Term::Sequence(vec![])), 1);
    }
}
