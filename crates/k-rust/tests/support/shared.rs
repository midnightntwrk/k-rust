//! Compile-once fixtures shared by the tests of one test binary.
//!
//! Compiling a definition is a function of its sources, its options and the environment the
//! compiler reads: `KRUST_TYPE_INFERENCE_MODE` selects the inference engine on every call, and
//! `checked` runs both engines and fails on any disagreement. So the tests of one process that
//! compile the same definition may share one result, but only among calls made under the same
//! environment. A [`Shared`] keeps one value per value of the `KRUST_*` and `K_RUST_*` variables:
//! a call under another inference mode builds its own, and never receives a value built under a
//! different one.
//!
//! Only immutable artefacts are shared, behind an [`Arc`]; every mutable object a test drives,
//! such as a `Backend`, is still built by that test. The cache lives for one process, so under
//! nextest, which runs each test in a process of its own, every test still compiles once.
//!
//! Test binaries include this file with `#[path = "support/shared.rs"] mod shared;`.

use std::{
    ffi::OsString,
    sync::{Arc, Mutex, PoisonError},
};

/// The `KRUST_*` and `K_RUST_*` variables of the process, sorted by name.
type Environment = Vec<(OsString, OsString)>;

fn compiler_environment() -> Environment {
    let mut variables = std::env::vars_os()
        .filter(|(name, _)| {
            name.to_str()
                .is_some_and(|name| name.starts_with("KRUST_") || name.starts_with("K_RUST_"))
        })
        .collect::<Environment>();
    variables.sort();
    variables
}

/// A value built at most once per compiler environment and shared by every test that asks for
/// it under that environment.
pub struct Shared<T> {
    entries: Mutex<Vec<(Environment, Arc<T>)>>,
}

impl<T> Shared<T> {
    pub const fn new() -> Self {
        Self {
            entries: Mutex::new(Vec::new()),
        }
    }

    /// The value `build` makes under the current environment. The first caller under an
    /// environment builds it while holding the lock, so concurrent callers wait for that value
    /// instead of building their own. A `build` that panics stores nothing, and the next caller
    /// builds again and reports the same failure in its own test.
    pub fn get(&self, build: impl FnOnce() -> T) -> Arc<T> {
        let environment = compiler_environment();
        let mut entries = self.entries.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some((_, value)) = entries.iter().find(|(key, _)| *key == environment) {
            return Arc::clone(value);
        }
        let value = Arc::new(build());
        entries.push((environment, Arc::clone(&value)));
        value
    }
}
