//! A test-only seeded chooser for the values the definition leaves to the implementation
//! (docs/compatibility.md, "Implementation-chosen hook values").
//!
//! A run whose `implementationChosenValues` list is empty is read as the run of every model of
//! the definition. That holds when every evaluation that takes an open value notes a mark. To
//! test it, each site that computes such a value computes, under [`with_seed`], another value
//! some single model of the definition gives, and a run without a mark must be unchanged.
//!
//! Every choice is a function of the seed and of the application's arguments (the collection's
//! value, whose stored order is canonical; the length a read may take), so one seed is one model:
//! one listing order per collection value, one item, one letter case, one NaN sign, one zero.
//! The exception is `#read`, an effect, whose count another implementation may choose per call.
//!
//! Only the cargo feature `choice-sampling` (enabled by no shipped crate) has a seed; without it
//! [`seed`] is the constant `None`, every site computes k-rust's value, and nothing changes.

use crate::term::{Items, chunked::Item};

#[cfg(feature = "choice-sampling")]
use std::cell::Cell;
#[cfg(feature = "choice-sampling")]
use std::num::NonZeroU64;

#[cfg(feature = "choice-sampling")]
thread_local! {
    /// The seed of the innermost [`with_seed`] scope on this thread.
    static SEED: Cell<Option<u64>> = const { Cell::new(None) };
}

/// Run `action` with every site computing an implementation-chosen value on this thread taking
/// the value `seed` chooses. Compilation and execution run on the calling thread, so the scope
/// must wrap both: a compile-time choice (the fresh counter's association) is read there.
#[cfg(feature = "choice-sampling")]
pub fn with_seed<T>(seed: NonZeroU64, action: impl FnOnce() -> T) -> T {
    struct Restore(Option<u64>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SEED.set(self.0);
        }
    }
    let _restore = Restore(SEED.replace(Some(seed.get())));
    action()
}

/// The seed of the innermost [`with_seed`] scope on this thread, for a site outside this crate.
#[cfg(feature = "choice-sampling")]
pub fn current() -> Option<u64> {
    SEED.get()
}

/// The seed in force on this thread: that of the innermost [`with_seed`] scope, and always `None`
/// without the feature `choice-sampling`.
#[inline(always)]
pub(crate) fn seed() -> Option<u64> {
    #[cfg(feature = "choice-sampling")]
    {
        SEED.get()
    }
    #[cfg(not(feature = "choice-sampling"))]
    {
        None
    }
}

/// An order of `n` items, as indices into their stored order: reversed when `seed % 3 == 1`,
/// rotated left by one when `seed % 3 == 2`, and shuffled by a generator seeded from `seed` and
/// `n` otherwise.
pub(crate) fn permutation(seed: u64, n: usize) -> Vec<usize> {
    let mut order: Vec<usize> = (0..n).collect();
    match seed % 3 {
        1 => order.reverse(),
        2 => order.rotate_left(1.min(n)),
        _ => {
            let mut state = seed ^ n as u64;
            for last in (1..n).rev() {
                let other = (split_mix_64(&mut state) % (last as u64 + 1)) as usize;
                order.swap(last, other);
            }
        }
    }
    order
}

/// The stored `items` in the order [`permutation`] gives for `seed`.
pub(crate) fn permuted<T: Item>(seed: u64, items: &Items<T>) -> impl Iterator<Item = &T> {
    permutation(seed, items.len())
        .into_iter()
        .map(|index| items.get(index).expect("a permuted index is in range"))
}

/// The index of the item a choice among `n >= 1` stored items takes.
pub(crate) fn item(seed: u64, n: usize) -> usize {
    (seed % n as u64) as usize
}

/// One binary choice: the other letter case, NaN sign or zero.
pub(crate) fn bit(seed: u64) -> bool {
    seed & 1 == 1
}

/// How many of the `n >= 2` characters a read may take it takes: from 1 to `n - 1`.
pub(crate) fn read_count(seed: u64, n: usize) -> usize {
    debug_assert!(n >= 2);
    1 + (seed % (n as u64 - 1)) as usize
}

/// One step of SplitMix64.
fn split_mix_64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut mixed = *state;
    mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    mixed ^ (mixed >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_order_is_a_permutation() {
        for seed in 0..12 {
            for n in 0..9 {
                let mut order = permutation(seed, n);
                order.sort_unstable();
                assert_eq!(order, (0..n).collect::<Vec<_>>(), "seed {seed}, n {n}");
            }
        }
    }

    #[test]
    fn reads_and_items_stay_in_range() {
        for seed in 0..12 {
            for n in 2..9 {
                assert!((1..n).contains(&read_count(seed, n)));
                assert!(item(seed, n) < n);
            }
        }
    }
}
