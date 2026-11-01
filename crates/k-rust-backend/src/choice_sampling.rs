//! A test-only seeded chooser for the values the definition leaves to the implementation
//! (docs/compatibility.md, "Implementation-chosen hook values").
//!
//! A run whose `implementationChosenValues` list is empty is read as the run of every model of
//! the definition. That holds when every evaluation that takes an open value notes a mark. To
//! test it, each site that computes such a value computes, under [`with_seed`], another value
//! some single model of the definition gives, and a run without a mark must be unchanged.
//!
//! Every choice is a function of the seed and of the application's arguments (the collection's
//! value, whose stored order is canonical; the length a read may take; the substitution's terms;
//! the rule), so one seed is one model: one listing order per collection value, one item, one
//! letter case, one NaN sign, one zero, one destination format for operands of two formats, one
//! renaming of the binders of each substitution, one association of each rule's fresh names,
//! one case per letter digit of a hex output, one byte encoding (k-rust's, or UTF-8), one
//! integer per `Float2Int` tie, one value per hook application outside
//! its described domain, and a value of the sort for each `\bottom` k-rust takes there where the
//! hook's arguments give one. The exception is `#read`, an effect, whose count another
//! implementation may choose per call.
//!
//! Three classes have no other value here. `curve`: no other curve than alt_bn128 is
//! implemented, so no other model's sums, products, pairings or point tests can be computed.
//! `literal`: a literal's element is fixed when the definition is loaded, before any seed scope
//! of a run, and the load runs in `Proof`, so no execution computes it. `effect-order` is not a
//! value. Within `outside-domain`, `String2Token` of a text that names no element of its sort
//! keeps k-rust's `\bottom`: a value of the declared sort is a token the sort's lexical syntax
//! admits, which the hook's arguments do not give; a `total` symbol's application there is
//! defined and unknown on every route, so it has no pick to replace. The matcher's refutation of
//! a list-update pattern (`matching::collections`) reads the evaluator's own `\bottom` through
//! the context-free `builtin::evaluate_hook`, which does not take the sampled value.
//!
//! Only the cargo feature `choice-sampling` (enabled by no shipped crate) has a seed; without it
//! [`seed`] is the constant `None`, every site computes k-rust's value, and nothing changes.

use crate::{
    builtin::ChosenClass,
    term::{Items, chunked::Item},
};

#[cfg(feature = "choice-sampling")]
use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
    num::NonZeroU64,
};

#[cfg(feature = "choice-sampling")]
thread_local! {
    /// The seed of the innermost [`with_seed`] scope on this thread.
    static SEED: Cell<Option<u64>> = const { Cell::new(None) };
    /// Per class name, the open values a site took under a seed on this thread since the last
    /// [`take_counts`].
    static TAKEN: RefCell<BTreeMap<&'static str, u64>> = const { RefCell::new(BTreeMap::new()) };
    /// Whether the symbol of the innermost hook application under evaluation on this thread is
    /// declared `total` ([`Application`]).
    static TOTAL: Cell<bool> = const { Cell::new(false) };
}

/// The evaluation of one hook application, whose symbol is declared `total` exactly when
/// `total` holds, for as long as the value lives: a site reads the declaration through
/// [`declared_total`] and [`taken`]. Nothing without the feature `choice-sampling`.
pub(crate) struct Application {
    #[cfg(feature = "choice-sampling")]
    enclosing: bool,
}

impl Application {
    #[inline(always)]
    pub(crate) fn enter(total: bool) -> Self {
        #[cfg(feature = "choice-sampling")]
        {
            Self {
                enclosing: TOTAL.replace(total),
            }
        }
        #[cfg(not(feature = "choice-sampling"))]
        {
            let _ = total;
            Self {}
        }
    }
}

#[cfg(feature = "choice-sampling")]
impl Drop for Application {
    fn drop(&mut self) {
        TOTAL.set(self.enclosing);
    }
}

/// Whether the symbol of the hook application under evaluation is declared `total`
/// ([`Application`]); `false` outside one, and always without the feature `choice-sampling`.
#[inline(always)]
pub(crate) fn declared_total() -> bool {
    #[cfg(feature = "choice-sampling")]
    {
        TOTAL.get()
    }
    #[cfg(not(feature = "choice-sampling"))]
    {
        false
    }
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

/// Count one value of `class` that a site took under the seed: the site's own condition, under
/// which the definition leaves the value open, held, and the seed chose the value, whichever it
/// chose (k-rust's own included). Nothing without the feature `choice-sampling`.
///
/// A value is counted where its mark is noted. Inside a `suspend`ed evaluation, which reads only
/// whether the application is defined (`crate::path_facts::suspend`), a value of an application
/// every model defines (`ChosenClass::defined_in_every_model`, at the declaration
/// [`declared_total`] reads) decides nothing that depends on which value was taken, so it does
/// not reach the run's result and neither its mark nor its count is kept: an unmarked run then
/// takes no value. One whose definedness is open (`curve`, `outside-domain` at a partial symbol)
/// is the pick that evaluation reads, so it is marked and counted.
#[inline(always)]
pub(crate) fn taken(class: ChosenClass) {
    #[cfg(feature = "choice-sampling")]
    {
        if class.defined_in_every_model(declared_total()) && crate::path_facts::suspended() {
            return;
        }
        TAKEN.with_borrow_mut(|taken| *taken.entry(class.name()).or_default() += 1);
    }
    #[cfg(not(feature = "choice-sampling"))]
    let _ = class;
}

/// [`taken`], for a site outside this crate (the compiler's fresh-counter association).
#[cfg(feature = "choice-sampling")]
pub fn note_taken(class: ChosenClass) {
    taken(class);
}

/// The open values each class's sites took under a seed on this thread since the last call, by
/// class name, and the count reset: a harness reads it around each compilation and run, so that
/// an unmarked run that took one shows a site that computed an open value without its mark.
#[cfg(feature = "choice-sampling")]
pub fn take_counts() -> BTreeMap<&'static str, u64> {
    TAKEN.take()
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

/// A second binary choice, independent of [`bit`]: whether an application k-rust leaves
/// undefined outside the inputs its description covers takes a value of its sort instead
/// (`super::builtin`'s `undescribed_value`). A site that may itself choose `\bottom` under [`bit`]
/// (`replaceAtBytes` up to the end) composes with it, so every combination is one model's.
pub(crate) fn defines(seed: u64) -> bool {
    seed & 2 == 2
}

/// The case of the letter digit at `position` of one hex output: uppercase when this is `true`.
/// `krypto.md` names no case and no consistency clause, so each letter digit's case is a model's
/// own choice; the choice is a function of the seed and the position, so one application has one
/// spelling per seed.
pub(crate) fn upper_case_at(seed: u64, position: usize) -> bool {
    let mut state = seed ^ (position as u64).wrapping_mul(0xD6E8_FEB8_6659_FD93);
    split_mix_64(&mut state) & 1 == 1
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
