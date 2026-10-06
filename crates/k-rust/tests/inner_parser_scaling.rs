//! How the inner parser's work grows with the depth and the length of a program.
//!
//! A program is as deep and as long as its author writes it: a numeral `s(s(...(z)))` is a chain
//! as deep as its value, and a statement sequence or a list literal is a chain as deep as its
//! length. Parsing must therefore take work linear in the input, not in its square. The tests
//! parse each shape at two sizes and bound the growth of the bytes the parse allocates and of
//! the Earley chart's work.
//!
//! The bytes come from the counting allocator this binary installs, which counts the whole
//! process, so the tests of this binary take a lock and measure one at a time.

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use std::sync::{Mutex, MutexGuard};

use k_rust::inner::ProgramParser;
use k_rust::kast::Sort;
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

fn parser(source: &str) -> ProgramParser {
    let parsed = k_rust::outer::parse("program.k", source).expect("definition should parse");
    let definition = k_rust::outer::lower(&parsed, "MAIN").expect("definition should lower");
    ProgramParser::new(&definition, "MAIN").expect("program grammar should build")
}

/// The counters of parsing `program` at `sort`, with the bytes allocated meanwhile.
fn parse_work(parser: &ProgramParser, sort: &str, program: &str) -> Snapshot {
    let allocated = || {
        let mut totals = Snapshot::default();
        measure::set_allocation_counters(&mut totals);
        totals
    };
    let before = (measure::snapshot(), allocated());
    let parsed = parser.parse(&Sort::new(sort), program);
    let mut work = measure::snapshot().delta(&before.0);
    let bytes = allocated().delta(&before.1);
    work.0[Counter::AllocatedBytes as usize] = bytes.get(Counter::AllocatedBytes);
    work.0[Counter::Allocations as usize] = bytes.get(Counter::Allocations);
    assert!(parsed.is_ok(), "{sort} program should parse: {parsed:?}");
    drop(parsed);
    work
}

/// The bytes a parse of a program `n` and `2 * n` units long allocates, with the size of the
/// smaller program in bytes.
fn allocated_at_two_sizes(
    source: &str,
    sort: &str,
    program: impl Fn(usize) -> String,
    n: usize,
) -> (u64, u64) {
    let _measuring = measuring();
    let parser = parser(source);
    let (small, large) = (program(n), program(2 * n));
    // Parsing descends once per level of the tree, so it runs on a thread with room for that.
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, || {
                (
                    parse_work(&parser, sort, &small).get(Counter::AllocatedBytes),
                    parse_work(&parser, sort, &large).get(Counter::AllocatedBytes),
                )
            })
            .expect("the worker should spawn")
            .join()
            .expect("the parses should finish")
    })
}

/// Lowering a parse tree to KAST and inferring its sorts touch each node once: a numeral 4,000
/// levels deep allocates about twice what one 2,000 levels deep does. Lowering once copied every
/// lowered child into its parent, and inference named every node by its path from the root, so
/// both allocated in proportion to the square of the depth (four times as much at twice the
/// depth).
#[test]
fn deep_programs_parse_in_allocation_linear_in_their_depth() {
    let (small, large) = allocated_at_two_sizes(
        "module MAIN\n  syntax Nat ::= \"z\" | s(Nat)\nendmodule\n",
        "Nat",
        |depth| format!("{}z{}", "s(".repeat(depth), ")".repeat(depth)),
        2_000,
    );
    println!("allocated: {small} bytes at 2,000 levels, {large} at 4,000");
    assert!(
        large <= small * 5 / 2,
        "{small} bytes at 2,000 levels, {large} at 4,000"
    );
}
