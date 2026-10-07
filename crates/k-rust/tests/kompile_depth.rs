//! How compiling a definition grows with the depth of its rule bodies.
//!
//! A rule body is as deep as its author writes it: an operator chain or a numeral thousands of
//! levels deep parses in work linear in its length (`inner_parser_scaling`), and the compile
//! passes after parsing must then neither overflow the native stack nor take memory in the square
//! of its depth.
//!
//! The bytes come from the counting allocator this binary installs, which counts the whole
//! process, so the measurement takes a lock.

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use std::sync::{Mutex, MutexGuard};

use k_rust::builtin::embedded;
use k_rust::kompile::{CompilationBackend, minimize_term_construction};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options};
use k_rust_kore::measure::{self, Counter, CountingAllocator, Snapshot};

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

/// Serializes the measurements of this binary's tests.
static MEASURING: Mutex<()> = Mutex::new(());

fn measuring() -> MutexGuard<'static, ()> {
    MEASURING
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// A definition whose module `MAIN` holds the rule `rule`, with a left-associative `+` chain at
/// sort `E` and a unary numeral at sort `N`.
fn definition(rule: &str) -> String {
    format!(
        r#"module MAIN-SYNTAX
  imports INT-SYNTAX
  syntax E ::= Int | E "+" E [left, symbol(plus)]
  syntax N ::= "z" [symbol(z)] | s(N) [symbol(s)]
  syntax KItem ::= foo(E) [symbol(foo)] | bar(N) [symbol(bar)]
endmodule
module MAIN
  imports MAIN-SYNTAX
  imports INT
  configuration <k> $PGM:K </k>
  {rule}
endmodule
"#
    )
}

/// The `+` chain `0 + 1 + ...` of `n` operands.
fn chain(n: usize) -> String {
    (0..n)
        .map(|operand| (operand % 10).to_string())
        .collect::<Vec<_>>()
        .join(" + ")
}

/// Load module `MAIN` of `source` as `kcompile` does, with the K prelude.
fn load(source: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("definition.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("the definition does not load: {error:?}"))
}

/// The bytes the term-construction minimization of `rule foo(C) => foo(C)`, with `C` a chain of
/// `n` operands, allocates. Every subterm of the left side is named, and the right side reuses
/// each name it finds. The rule is labelled, so that the origins the pass records find the rule
/// it changed (a compile finds it by the input it was read from).
fn minimized_bytes(n: usize) -> u64 {
    let chain = chain(n);
    let loaded = load(&definition(&format!(
        "rule foo({chain}) => foo({chain}) [label(deep)]"
    )));
    let allocated = || {
        let mut totals = Snapshot::default();
        measure::set_allocation_counters(&mut totals);
        totals
    };
    let before = allocated();
    let minimized = minimize_term_construction(loaded.definition());
    let bytes = allocated().delta(&before).get(Counter::AllocatedBytes);
    assert!(minimized.is_ok(), "{:?}", minimized.err());
    drop(minimized);
    bytes
}

/// Minimization names each left-hand subterm of a rule once and finds its right-hand
/// occurrences by number, so it allocates in proportion to the rule, not to the sum of its
/// subterms' sizes. It once copied every left-hand subterm into its map and compared whole
/// subterms there.
#[test]
fn term_construction_is_minimized_in_memory_linear_in_a_rules_depth() {
    let _measuring = measuring();
    let (small, large) = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, || (minimized_bytes(1_000), minimized_bytes(2_000)))
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish")
    });
    println!("minimizing 1,000 operands allocated {small} bytes, 2,000 allocated {large}");
    assert!(
        large <= small * 5 / 2,
        "minimizing 2,000 operands allocated {large} bytes, 1,000 allocated {small}"
    );
}
