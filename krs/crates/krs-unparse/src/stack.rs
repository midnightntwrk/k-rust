//! Native stack for the passes that descend a term one level per level of it.
//!
//! K bounds no term's depth, and a collection a run built is as deep as it is long: a list cell
//! of 100,000 items is a concatenation nested 100,000 levels. A pass that recurses into its
//! term therefore calls [`guarded`] at every level: the level runs on the current stack while at
//! least [`RED_ZONE`] of it remains, and otherwise on a fresh segment of [`SEGMENT`] bytes, which
//! `stacker` maps for the duration of the level. A segment is address space whose pages are
//! committed only as they are used, so a print's depth is bounded by memory, not by the thread
//! it runs on.
//!
//! The check is a thread-local read and a comparison per level. On wasm32 the engine's stack
//! limit is invisible to the module and its stack cannot be switched, so the work runs on the
//! current stack unchanged.

/// The stack that must remain for one more level: more than the frames any pass of this crate
/// pushes between two guards, in any build (the formatter's, which interprets a production's
/// format between an application and its arguments, takes the most).
#[cfg(not(target_family = "wasm"))]
const RED_ZONE: usize = 256 * 1024;

/// The size of each segment mapped when less than [`RED_ZONE`] remains.
#[cfg(not(target_family = "wasm"))]
const SEGMENT: usize = 16 * 1024 * 1024;

/// Run `work`, one level of a recursion over a term of any depth, with at least [`RED_ZONE`] of
/// native stack, on a fresh segment when the current stack has less.
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
