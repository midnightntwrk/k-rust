//! The test binary's allocator, which records the most memory a thread holds while it runs a
//! piece of work, for tests that measure how many bytes a hook application holds per byte of its
//! result (the peak factors in `builtin`).
//!
//! The counts are per thread, so tests running in parallel do not see each other's allocations.
//! Memory a thread frees that another thread allocated lowers its count; the work measured here
//! allocates and frees on its own thread.

use std::{
    alloc::{GlobalAlloc, Layout, System},
    cell::Cell,
};

struct PeakAllocator;

#[global_allocator]
static ALLOCATOR: PeakAllocator = PeakAllocator;

thread_local! {
    /// Bytes this thread allocated and has not freed, since it started.
    static LIVE: Cell<i64> = const { Cell::new(0) };
    /// The most `LIVE` has been since the last [`peak_during`] started.
    static PEAK: Cell<i64> = const { Cell::new(0) };
}

fn record(change: i64) {
    // `try_with` fails only while the thread's locals are being destroyed, after any measurement.
    let _ = LIVE.try_with(|live| {
        let now = live.get() + change;
        live.set(now);
        let _ = PEAK.try_with(|peak| peak.set(peak.get().max(now)));
    });
}

fn signed(size: usize) -> i64 {
    i64::try_from(size).expect("an allocation is at most isize::MAX bytes")
}

// SAFETY: every call is forwarded to `System` with the caller's arguments; the bookkeeping
// touches only thread-local cells, which allocate nothing.
unsafe impl GlobalAlloc for PeakAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() {
            record(signed(layout.size()));
        }
        pointer
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc_zeroed(layout) };
        if !pointer.is_null() {
            record(signed(layout.size()));
        }
        pointer
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let replacement = unsafe { System.realloc(pointer, layout, new_size) };
        if !replacement.is_null() {
            // A reallocation that moves holds both blocks while it copies.
            if replacement != pointer {
                record(signed(new_size));
                record(-signed(layout.size()));
            } else {
                record(signed(new_size) - signed(layout.size()));
            }
        }
        replacement
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) };
        record(-signed(layout.size()));
    }
}

/// Runs `work` and returns its result with the most bytes this thread held during it beyond what
/// it held when `work` started, counting the result, which is still held when `work` returns.
pub(crate) fn peak_during<T>(work: impl FnOnce() -> T) -> (T, u64) {
    let start = LIVE.with(Cell::get);
    PEAK.with(|peak| peak.set(start));
    let result = work();
    let peak = PEAK.with(Cell::get);
    (result, u64::try_from(peak - start).unwrap_or(0))
}
