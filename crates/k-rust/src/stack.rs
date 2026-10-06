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
