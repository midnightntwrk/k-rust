//! Independently specified M2 Rust semantics.
//!
//! This package's only KRS dependency is the renamed author-facing facade.
//! The spelling below is the oracle input and must not be regenerated from a
//! compiler or adapter artifact.

use language_host as k;
use std::sync::atomic::{AtomicUsize, Ordering};

static INIT_RUNTIME_DROPS: AtomicUsize = AtomicUsize::new(0);

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult: KItem {}

#[k::sort]
pub trait M2Obj: KResult {}

#[k::constructor(sort = M2Obj, syntax = "foo")]
pub struct Foo;

#[k::constructor(sort = M2Obj, syntax = "bar")]
pub struct Bar;

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

#[allow(clippy::must_use_candidate)]
impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![Foo]),
        }
    }
}

impl Drop for Machine {
    fn drop(&mut self) {
        INIT_RUNTIME_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

/// Number of ordinary `Machine` values dropped in this process.
///
/// The oracle reads this immediately after descriptor collection. If macro
/// registration evaluates `Machine::init`, its temporary is observably
/// dropped and the hard zero-call assertion fails.
#[must_use]
pub fn init_runtime_drops() -> usize {
    INIT_RUNTIME_DROPS.load(Ordering::SeqCst)
}

#[k::rule]
pub fn foo_to_bar(Foo: k::Term<dyn M2Obj>) -> k::Term<dyn M2Obj> {
    Bar
}
