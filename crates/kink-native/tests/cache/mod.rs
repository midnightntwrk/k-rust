//! A per-binary cache of the `testdata/k` fixtures bound to a [`NativeValidator`].
//!
//! Integration tests that compile one fixture several times include this module with
//! `mod cache;` next to `support`; [`validator`] binds each fixture once per test binary and
//! its baseline compile is memoised by the validator ([`NativeValidator::compile_baseline`]),
//! so every later caller in the same process gets the same compiled side instead of a fresh
//! compile of the full domains prelude. The cached validator is never mutated: callers read
//! its baseline, compile mutants from it (`validate`, which is never memoised) or clone it
//! (a clone keeps the baseline memo). nextest runs every test in its own process, so the
//! cache saves the repeated compiles within one test; under `cargo test` the tests of a binary
//! share it as well.
//!
//! A test that checks fresh-load or compile determinism must not use it: it binds its own
//! validators with `support::load`.
#![allow(dead_code)]

use std::collections::HashMap;
use std::path::Path;
use std::sync::{Mutex, OnceLock, PoisonError};

use k_rust::kompile::CompileOptions;
use kink_native::{NativeValidator, ValidatedDefinition};

/// The validator of `testdata/k/<name>` (main module: the upper-cased stem, as
/// `support::load`), bound with the default compile options once per test binary.
pub fn validator(name: &str) -> &'static NativeValidator {
    let module = name
        .strip_suffix(".k")
        .expect("a .k file")
        .to_ascii_uppercase();
    validator_at(name, &module)
}

/// The validator of `testdata/k/<relative>` with main module `module`, bound with the default
/// compile options once per test binary.
pub fn validator_at(relative: &str, module: &str) -> &'static NativeValidator {
    type Cache = Mutex<HashMap<(String, String), &'static NativeValidator>>;
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let mut cache = CACHE
        .get_or_init(Cache::default)
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    cache
        .entry((relative.to_owned(), module.to_owned()))
        .or_insert_with(|| {
            let baseline =
                crate::support::load_path(&Path::new(crate::support::DIR).join(relative), module);
            Box::leak(Box::new(NativeValidator::bind(
                baseline,
                CompileOptions::default(),
            )))
        })
}

/// The compiled baseline of `testdata/k/<name>` (see [`validator`]).
pub fn side(name: &str) -> ValidatedDefinition {
    validator(name)
        .compile_baseline()
        .unwrap_or_else(|error| panic!("{name}: {error}"))
}
