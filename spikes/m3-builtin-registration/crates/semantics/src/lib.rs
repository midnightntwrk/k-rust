//! Author fixture using a renamed facade dependency and ordinary Rust aliases.

use std::sync::atomic::{AtomicUsize, Ordering};

use dialect::int as integer;
use integer::add as plus;

static APPLICATION_CALLS: AtomicUsize = AtomicUsize::new(0);

#[dialect::builtin_application]
pub fn direct_add(x: dialect::int::Int, y: dialect::int::Int) -> dialect::int::add {
    APPLICATION_CALLS.fetch_add(1, Ordering::Relaxed);
    dialect::int::add(x, y)
}

#[dialect::builtin_application]
pub fn module_alias_add(x: integer::Int, y: integer::Int) -> integer::add {
    APPLICATION_CALLS.fetch_add(1, Ordering::Relaxed);
    integer::add(x, y)
}

#[dialect::builtin_application]
pub fn imported_alias_add(x: integer::Int, y: integer::Int) -> plus {
    APPLICATION_CALLS.fetch_add(1, Ordering::Relaxed);
    plus(x, y)
}

#[dialect::builtin_application]
pub fn module_alias_sub(x: integer::Int, y: integer::Int) -> integer::sub {
    APPLICATION_CALLS.fetch_add(1, Ordering::Relaxed);
    integer::sub(x, y)
}

/// Forces the author crate to be linked and reports whether collection called
/// any authored application carrier.
#[must_use]
pub fn application_calls() -> usize {
    APPLICATION_CALLS.load(Ordering::Relaxed)
}

