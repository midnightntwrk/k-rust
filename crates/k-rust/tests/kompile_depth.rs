//! How compiling a definition grows with the depth of its rule bodies.
//!
//! A rule body is as deep as its author writes it: an operator chain or a numeral thousands of
//! levels deep parses in work linear in its length (`inner_parser_scaling`), and the compile
//! passes after parsing must then neither overflow the native stack nor take memory in the square
//! of its depth.
//!
//! The bytes come from the counting allocator this binary installs, which counts the whole
//! process, so every test of this binary takes one lock: a test that only allocates would
//! otherwise land in a concurrent test's measurement under a runner that shares the process.

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use std::sync::{Mutex, MutexGuard};

use k_rust::builtin::embedded;
use k_rust::kompile::{
    CompilationBackend, CompileOptions, compile_loaded_definition, minimize_term_construction,
};
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

/// The numeral `s(s(...(z)))` of `n` levels.
fn numeral(n: usize) -> String {
    format!("{}z{}", "s(".repeat(n), ")".repeat(n))
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

/// Rule bodies 4,000 levels deep (a chain in an application, a numeral on the left and on the
/// right of the rewrite) load and compile on a thread of 256 KiB: the parser guards its own
/// levels, and every compile stage runs on a stack measured from the deepest term of the
/// definition it reads. Each overflowed the 8 MiB main thread of `kcompile` before, in the first
/// pass that recursed per level (`concretize_cells`).
#[test]
fn rule_bodies_thousands_of_levels_deep_compile_on_a_small_stack() {
    const LEVELS: usize = 4_000;
    let _measuring = measuring();
    let sources = [
        definition(&format!("rule foo({}) => .K", chain(LEVELS))),
        definition(&format!("rule bar({}) => .K", numeral(LEVELS))),
        definition(&format!("rule bar(z) => bar({})", numeral(LEVELS))),
    ];
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(move || {
            for source in &sources {
                let loaded = load(source);
                let compiled = compile_loaded_definition(&loaded, CompileOptions::default());
                assert!(compiled.is_ok(), "{:?}", compiled.err());
            }
        })
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish");
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

/// The bytes `kcompile` allocates for `rule bar(z) => hn(s(s(...(z))))` of `n` levels, where
/// `s` takes an `M` and `N` is a subsort of `M`, so that sort injection places an injection at
/// every level.
fn injected_nesting_bytes(n: usize) -> u64 {
    let source = format!(
        r#"module MAIN
  imports INT
  syntax N ::= "z" [symbol(z)] | s(M) [symbol(s)]
  syntax M ::= N
  syntax KItem ::= bar(N) [symbol(bar)] | hn(N) [symbol(hn)]
  configuration <k> $PGM:K </k>
  rule bar(z) => hn({})
endmodule
"#,
        numeral(n)
    );
    let loaded = load(&source);
    let allocated = || {
        let mut totals = Snapshot::default();
        measure::set_allocation_counters(&mut totals);
        totals
    };
    let before = allocated();
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default());
    let bytes = allocated().delta(&before).get(Counter::AllocatedBytes);
    assert!(compiled.is_ok(), "{:?}", compiled.err());
    bytes
}

/// Sort injection gives a subterm it does not wrap back to the level that tried the wrappers,
/// so a nesting with an injection at every level is compiled in memory linear in its depth. Each
/// level once copied the whole subterm below it for each wrapper it tried.
#[test]
fn a_nesting_injected_at_every_level_compiles_in_memory_linear_in_its_depth() {
    let _measuring = measuring();
    let [at_500, at_1000, at_2000] = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, || [500, 1_000, 2_000].map(injected_nesting_bytes))
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish")
    });
    println!("injected nesting: {at_500}, {at_1000} and {at_2000} bytes at 500, 1,000 and 2,000");
    let increments = at_1000
        .checked_sub(at_500)
        .zip(at_2000.checked_sub(at_1000));
    assert!(
        increments.is_some_and(|(first, second)| second <= first * 3),
        "{at_500}, {at_1000} and {at_2000} bytes at 500, 1,000 and 2,000 levels"
    );
}
