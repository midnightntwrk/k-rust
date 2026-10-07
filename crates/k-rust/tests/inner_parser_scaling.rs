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

use k_rust::builtin::embedded;
use k_rust::inner::ProgramParser;
use k_rust::kast::Sort;
use k_rust::kompile::CompilationBackend;
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

fn parser(source: &str) -> ProgramParser {
    let parsed = k_rust::outer::parse("program.k", source).expect("definition should parse");
    let definition = k_rust::outer::lower(&parsed, "MAIN").expect("definition should lower");
    ProgramParser::new(&definition, "MAIN").expect("program grammar should build")
}

/// Load module `MAIN` of `source` as `kast` and `kcompile` load a definition: with the K
/// prelude, which gives every sort the matching-logic connectives (`S "#And" S`, ...) and every
/// rule grammar the rewrite and the casts, and with every rule body parsed.
fn load_with_prelude(source: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("program.k", source),
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

/// The program parser of module `MAIN` of `source`, loaded with the K prelude.
fn prelude_parser(source: &str) -> ProgramParser {
    ProgramParser::from_resolved(load_with_prelude(source).resolved(), "MAIN")
        .expect("program grammar should build")
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

/// A nesting of a parametric production (`syntax {S} S ::= wrap(S)`) is parsed in work linear in
/// its depth, read at the sort of its argument (`p(wrap(...(z)))`) or above it (`wrap(...(z))`
/// as a `KItem`): a nesting 2,000 levels deep allocates, and compares packed nodes, at most
/// about twice what one 1,000 levels deep does. Portable sort inference once walked, from every
/// parameter slot, the chain of slots above it to find its bound (cloning the path at every
/// step); list completion instantiated every node once per node above it; and the instances of
/// `wrap` read at `Nat` and at `KItem` over one span were built as distinct equal nodes all the
/// way up, so the chart compared each new node with its twin down to the bottom.
#[test]
fn parametric_nestings_parse_in_work_linear_in_their_depth() {
    let _measuring = measuring();
    let parser = parser(
        "module MAIN\n  syntax Nat ::= \"z\"\n  syntax {S} S ::= wrap(S)\n  syntax KItem ::= p(Nat)\nendmodule\n",
    );
    fn nesting(depth: usize) -> String {
        format!("{}z{}", "wrap(".repeat(depth), ")".repeat(depth))
    }
    fn applied(depth: usize) -> String {
        format!("p({})", nesting(depth))
    }
    let shapes = [
        ("p(wrap(...))", applied as fn(usize) -> String),
        ("wrap(...)", nesting),
    ];
    for (shape, program) in shapes {
        let [small, large] = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(1 << 30)
                .spawn_scoped(scope, || {
                    [1_000, 2_000].map(|depth| parse_work(&parser, "KItem", &program(depth)))
                })
                .expect("the worker should spawn")
                .join()
                .expect("the parses should finish")
        });
        for counter in [
            Counter::AllocatedBytes,
            Counter::ParserPackedStructuralComparisons,
        ] {
            let (small, large) = (small.get(counter), large.get(counter));
            println!("{shape}: {counter:?} {small} at 1,000 levels, {large} at 2,000");
            assert!(
                large <= small * 5 / 2 + 16,
                "{shape}: {counter:?} {small} at 1,000 levels, {large} at 2,000"
            );
        }
    }
}

/// A chain of a left-associative operator that fails at its end (`0+1+...+`) is recognized
/// again with the relations ignored, to tell whether the grammar derives it (the error would then
/// be the relation every derivation breaks) or where its longest viable prefix ends. That
/// recognition reads only which items exist, so it does not build the parse forest of the
/// ambiguous grammar, which grows far faster than its chart: twice the operands take at most
/// about six times the completions and bytes (the chart of an ambiguous chain is quadratic in its
/// length). Building the forest took sixteen times the completions and eighteen times the bytes
/// (3.4 million and 3 GB at 80 operands).
#[test]
fn failed_associativity_chains_are_explained_without_their_forest() {
    let _measuring = measuring();
    let parser = parser(
        "module MAIN\n  syntax Int ::= r\"[0-9]+\" [token]\n  syntax E ::= Int | E \"+\" E [left]\nendmodule\n",
    );
    let allocated = || {
        let mut totals = Snapshot::default();
        measure::set_allocation_counters(&mut totals);
        totals
    };
    let [small, large] = [40, 80].map(|length: usize| {
        let program = (0..length)
            .map(|operand| operand.to_string())
            .collect::<Vec<_>>()
            .join("+")
            + "+";
        let before = (measure::snapshot(), allocated());
        let error = parser.parse(&Sort::new("E"), &program).unwrap_err();
        assert!(
            error.to_string().contains("unexpected end of file"),
            "{error}"
        );
        let mut work = measure::snapshot().delta(&before.0);
        work.0[Counter::AllocatedBytes as usize] =
            allocated().delta(&before.1).get(Counter::AllocatedBytes);
        work
    });
    for counter in [
        Counter::ParserChartCompletionCandidates,
        Counter::AllocatedBytes,
    ] {
        let (small, large) = (small.get(counter), large.get(counter));
        println!("{counter:?}: {small} at 40 operands, {large} at 80");
        assert!(
            large <= small * 6,
            "{counter:?}: {small} at 40 operands, {large} at 80"
        );
    }
}

/// The Earley chart's completions and the bytes of parsing one shape at two lengths.
fn chart_work_at_two_sizes(
    source: &str,
    sort: &str,
    program: impl Fn(usize) -> String,
    n: usize,
) -> [(u64, u64); 2] {
    let _measuring = measuring();
    let parser = parser(source);
    [n, 2 * n].map(|length| {
        let work = parse_work(&parser, sort, &program(length));
        (
            work.get(Counter::ParserChartCompletionCandidates),
            work.get(Counter::AllocatedBytes),
        )
    })
}

/// A program shape: its name, its definition, its sort and its program of a given length.
type Shape = (
    &'static str,
    &'static str,
    &'static str,
    Box<dyn Fn(usize) -> String>,
);

/// A statement sequence, a list literal and a chain of a binary operator are as deep as they
/// are long, and their chart work is linear in their length: a sequence of 600 statements
/// completes about twice the items one of 300 does, whether the sequence is a right-recursive
/// list (`Stmt Stmts`, `List{Int, ","}`, `Stmt Stmt [right]`) or a left-associative chain
/// (`Stmt Stmt [left]`, `E "+" E [left]`). The recognizer once completed, after each statement,
/// every enclosing list back to the first statement (N²/2 completions), and in a
/// left-associative chain every sum starting after the first operand, which the associativity
/// forbids from becoming the right operand it would have to be.
#[test]
fn long_programs_parse_in_chart_work_linear_in_their_length() {
    let skips = |count: usize| "skip ;\n".repeat(count);
    let numbers = |separator: &'static str| {
        move |count: usize| {
            (0..count)
                .map(|number| number.to_string())
                .collect::<Vec<_>>()
                .join(separator)
        }
    };
    let shapes: [Shape; 5] = [
        (
            "Stmt Stmts",
            "module MAIN\n  syntax Stmt ::= \"skip\" \";\"\n  syntax Stmts ::= Stmt | Stmt Stmts\nendmodule\n",
            "Stmts",
            Box::new(skips),
        ),
        (
            "List{Int, \",\"}",
            "module MAIN\n  syntax Int ::= r\"[0-9]+\" [token]\n  syntax Ints ::= List{Int, \",\"}\nendmodule\n",
            "Ints",
            Box::new(numbers(",")),
        ),
        (
            "Stmt Stmt [right]",
            "module MAIN\n  syntax Stmt ::= \"skip\" \";\"\n  syntax Stmt ::= Stmt Stmt [right]\nendmodule\n",
            "Stmt",
            Box::new(skips),
        ),
        (
            "Stmt Stmt [left]",
            "module MAIN\n  syntax Stmt ::= \"skip\" \";\"\n  syntax Stmt ::= Stmt Stmt [left]\nendmodule\n",
            "Stmt",
            Box::new(skips),
        ),
        (
            "E \"+\" E [left]",
            "module MAIN\n  syntax Int ::= r\"[0-9]+\" [token]\n  syntax E ::= Int | E \"+\" E [left]\nendmodule\n",
            "E",
            Box::new(numbers("+")),
        ),
    ];
    for (shape, source, sort, program) in shapes {
        let [(small, small_bytes), (large, large_bytes)] =
            chart_work_at_two_sizes(source, sort, program, 300);
        println!(
            "{shape}: {small} and {large} completions, {small_bytes} and {large_bytes} bytes at 300 and 600"
        );
        assert!(
            large <= small * 9 / 4,
            "{shape}: {small} completions at 300, {large} at 600"
        );
        assert!(
            large_bytes <= small_bytes * 5 / 2,
            "{shape}: {small_bytes} bytes at 300, {large_bytes} at 600"
        );
    }
}

/// A chain that every reading parses but that is ambiguous (`0+1+...+x`, with two productions
/// of `x`) is reported in chart work linear in its length: the ambiguity is read from the
/// forest of the first recognition, which skipping completions leaves as it is. The parser once
/// recognized such an input a second time without skipping anything, as it does for an input
/// with no derivation, whose diagnostic reads the chart: a chain of 600 operands then completed
/// four times the items one of 300 does (183,907 against 46,957; now 1,804 against 904).
#[test]
fn ambiguous_chains_are_reported_in_chart_work_linear_in_their_length() {
    let _measuring = measuring();
    let parser = parser(
        "module MAIN\n  syntax Int ::= r\"[0-9]+\" [token]\n  syntax E ::= Int | E \"+\" E [left] | \"x\" [symbol(x1)] | \"x\" [symbol(x2)]\nendmodule\n",
    );
    let [small, large] = [300, 600].map(|length: usize| {
        let program = (0..length)
            .map(|operand| operand.to_string())
            .collect::<Vec<_>>()
            .join("+")
            + "+x";
        let before = measure::snapshot();
        let error = parser.parse(&Sort::new("E"), &program).unwrap_err();
        assert!(error.to_string().contains("Parsing ambiguity"), "{error}");
        measure::snapshot()
            .delta(&before)
            .get(Counter::ParserChartCompletionCandidates)
    });
    println!("ambiguous chain: {small} completions at 300 operands, {large} at 600");
    assert!(
        large <= small * 9 / 4,
        "{small} completions at 300 operands, {large} at 600"
    );
}

/// Operator chains under the K prelude, which declares `S "#And" S`, `S "#Or" S` and
/// `S "#Implies" S` at every sort, and under a priority between two operators: their chart work
/// is linear in their length, as it is for a sort with one binary operator. The recognizer kept
/// every sum that starts after the first operand, because the sum could be the left operand of
/// an `#And` (or of a `*`) at its origin, which in turn could be the right operand of a `+`;
/// that the input holds no `#And`, and that `*` binds tighter than `+`, were not consulted. Such
/// a chain of 600 operands completed about seven times the items one of 300 does.
#[test]
fn operator_chains_parse_in_chart_work_linear_in_their_length_under_the_prelude() {
    let numbers = |separator: &'static str| {
        move |count: usize| {
            (0..count)
                .map(|number| number.to_string())
                .collect::<Vec<_>>()
                .join(separator)
        }
    };
    let alternating = |count: usize| {
        (0..count)
            .map(|number| {
                let operator = if number % 2 == 0 { " + " } else { " * " };
                format!("{number}{operator}")
            })
            .collect::<String>()
            + "0"
    };
    let one_operator = "module MAIN\n  syntax Num ::= r\"[0-9]+\" [token]\n  syntax E ::= Num | E \"+\" E [left]\nendmodule\n";
    let arithmetic = "module MAIN\n  syntax Num ::= r\"[0-9]+\" [token]\n  syntax E ::= Num\n             | E \"*\" E [left]\n             > E \"+\" E [left]\nendmodule\n";
    let below_a_rewrite = "module MAIN\n  syntax Num ::= r\"[0-9]+\" [token]\n  syntax E ::= Num | E \"+\" E [left, symbol(plus)] | E \"=>\" E [symbol(rw)]\n  syntax priority plus > rw\nendmodule\n";
    let shapes: [(&str, &str, Box<dyn Fn(usize) -> String>); 5] = [
        ("E \"+\" E [left]", one_operator, Box::new(numbers(" + "))),
        (
            "`+` chain under `*` > `+`",
            arithmetic,
            Box::new(numbers(" + ")),
        ),
        (
            "`*` chain under `*` > `+`",
            arithmetic,
            Box::new(numbers(" * ")),
        ),
        ("alternating `+` and `*`", arithmetic, Box::new(alternating)),
        (
            "`+` chain under `plus > rw`",
            below_a_rewrite,
            Box::new(numbers(" + ")),
        ),
    ];
    let _measuring = measuring();
    for (shape, source, program) in shapes {
        let parser = prelude_parser(source);
        let [(small, small_bytes), (large, large_bytes)] = [300, 600].map(|length| {
            let work = parse_work(&parser, "E", &program(length));
            (
                work.get(Counter::ParserChartCompletionCandidates),
                work.get(Counter::AllocatedBytes),
            )
        });
        println!(
            "{shape}: {small} and {large} completions, {small_bytes} and {large_bytes} bytes at 300 and 600"
        );
        assert!(
            large <= small * 9 / 4,
            "{shape}: {small} completions at 300, {large} at 600"
        );
        assert!(
            large_bytes <= small_bytes * 5 / 2,
            "{shape}: {small_bytes} bytes at 300, {large_bytes} at 600"
        );
    }
}

/// An operator chain in a rule body, whose grammar also has the rewrite, the casts and the
/// matching-logic connectives at every sort, is parsed in chart work linear in its length: the
/// work of loading the definition grows by about as much from 100 to 200 operands as from 50
/// to 100, where the cubic chart of the chain made it grow eight times as much.
#[test]
fn operator_chains_in_rule_bodies_parse_in_chart_work_linear_in_their_length() {
    let definition = |length: usize| {
        let chain = (0..length)
            .map(|number| (number % 10).to_string())
            .collect::<Vec<_>>()
            .join(" + ");
        format!(
            "module MAIN\n  imports INT\n  imports BOOL\n  \
             syntax E ::= Int | E \"+\" E [left, symbol(plus)]\n  \
             syntax KItem ::= foo(E) [symbol(foo)]\n  rule foo({chain}) => .K\nendmodule\n"
        )
    };
    let _measuring = measuring();
    let [at_50, at_100, at_200] = [50, 100, 200].map(|length| {
        let before = measure::snapshot();
        drop(load_with_prelude(&definition(length)));
        measure::snapshot()
            .delta(&before)
            .get(Counter::ParserChartCompletionCandidates)
    });
    let (first, second) = (at_100 - at_50, at_200 - at_100);
    println!(
        "rule-body chain: {at_50}, {at_100} and {at_200} completions at 50, 100 and 200 operands"
    );
    assert!(
        second <= first * 5 / 2,
        "{at_50}, {at_100} and {at_200} completions at 50, 100 and 200 operands"
    );
}
