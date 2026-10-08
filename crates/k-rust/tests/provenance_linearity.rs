//! How the provenance of a definition grows with the definition.
//!
//! Every generating pass gives each node it builds a receipt naming the node's origin set and its
//! destination, and `KRUST-PROVENANCE` writes those receipts and every node's metadata. Each of
//! those per-node items must cost a constant amount of work, memory and bytes, whatever the
//! depth of the node and whatever the size of the origin set it inherits: a deep chain (depth
//! and width grow together), a wide sequence (width without depth) and a deep rule body (the
//! compile-stage passes re-receipt it) are compiled at N and 2N operands, encoded and decoded,
//! and every provenance work counter and the document length must at most double.
//!
//! Counters rather than allocated bytes or time are the oracle: a quadratic term `c N^2` next to
//! a linear one `a N` raises the 2N/N ratio above 2.1 as soon as `c N` exceeds `a / 20`, and each
//! provenance counter's linear coefficient is a few steps per node while a per-node copy of a
//! path or of an inherited set adds at least one step per level per node.

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use k_rust::builtin::embedded;
use k_rust::definition::json;
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options};
use k_rust_kore::measure::{Counter, Snapshot, snapshot};

/// The provenance work counters whose growth the tests bound.
const COUNTERS: [Counter; 7] = [
    Counter::ProvenanceSetNodesBuilt,
    Counter::ProvenanceSetPartsBuilt,
    Counter::ProvenanceLinksSteps,
    Counter::ProvenanceNonflatFlattens,
    Counter::ProvenanceEncoderSetKeys,
    Counter::ProvenanceEncoderAnchorInternings,
    Counter::ProvenanceDecoderSteps,
];

#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `configuration <k> $PGM:K </k> <c> foo(0 + 1 + ...) </c>`: depth and width together.
    Config,
    /// `configuration <k> $PGM:K </k> <c> foo(0) ~> foo(1) ~> ... </c>`: width without depth.
    Wide,
    /// `rule foo(0 + 1 + ...) => .K`: a deep rule body that compile-stage passes rebuild.
    Rule,
}

/// The definition of `shape` at `n` operands, its main module named `module`. Every line that
/// names a module ends in a comment that pads it to a width fixed by the longest name the tests
/// use, so that the length of the name moves no source offset.
fn source(shape: Shape, n: usize, module: &str) -> String {
    let pad = |line: String| format!("{line} //{}", "-".repeat(256 - line.len()));
    let chain = (0..n)
        .map(|operand| (operand % 10).to_string())
        .collect::<Vec<_>>()
        .join(" + ");
    let sequence = (0..n)
        .map(|operand| format!("foo({})", operand % 10))
        .collect::<Vec<_>>()
        .join(" ~> ");
    let body = match shape {
        Shape::Config => format!("configuration <k> $PGM:K </k> <c> foo({chain}) </c>"),
        Shape::Wide => format!("configuration <k> $PGM:K </k> <c> {sequence} </c>"),
        Shape::Rule => format!("configuration <k> $PGM:K </k>\n  rule foo({chain}) => .K"),
    };
    format!(
        r#"{}
  imports INT-SYNTAX
  syntax E ::= Int | E "+" E [left, symbol(plus)]
  syntax KItem ::= foo(E) [symbol(foo)]
endmodule
{}
{}
  imports INT
  {body}
endmodule
"#,
        pad(format!("module {module}-SYNTAX")),
        pad(format!("module {module}")),
        pad(format!("  imports {module}-SYNTAX")),
    )
}

fn load(source: &str, module: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("definition.k", source),
        module,
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

/// What one shape costs: the counters of loading and compiling it, of encoding its loaded and
/// execution definitions and of decoding both documents, and the two documents' total length.
struct Cost {
    compile: Snapshot,
    total: Snapshot,
    bytes: usize,
}

fn cost(shape: Shape, n: usize, module: &str) -> Cost {
    let source = source(shape, n, module);
    let start = snapshot();
    let loaded = load(&source, module);
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the definition does not compile: {error:?}"));
    let compile = snapshot().delta(&start);
    let mut bytes = 0;
    for definition in [loaded.definition(), &compiled.execution_definition] {
        let text = json::to_provenance_string(definition, loaded.source_table())
            .expect("the definition encodes");
        let decoded = json::from_provenance_str(&text).expect("the document decodes");
        bytes += text.len();
        drop(decoded);
    }
    Cost {
        compile,
        total: snapshot().delta(&start),
        bytes,
    }
}

fn on_large_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(scope, work)
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish")
    })
}

fn ratio_failures(shape: Shape, n: usize, small: &Cost, large: &Cost) -> Vec<String> {
    let mut failures = Vec::new();
    if small.compile.get(Counter::ProvenanceNonflatFlattens) != 0
        || large.compile.get(Counter::ProvenanceNonflatFlattens) != 0
    {
        failures.push(format!(
            "{shape:?}: the compile flattened a term origin set ({} at {n}, {} at {})",
            small.compile.get(Counter::ProvenanceNonflatFlattens),
            large.compile.get(Counter::ProvenanceNonflatFlattens),
            2 * n
        ));
    }
    for counter in COUNTERS {
        let (at_n, at_2n) = (small.total.get(counter), large.total.get(counter));
        println!(
            "{shape:?} {}: {at_n} at {n}, {at_2n} at {}",
            counter.name(),
            2 * n
        );
        if at_2n * 10 > at_n * 21 {
            failures.push(format!(
                "{shape:?} {}: {at_2n} at {} is more than 2.1 x {at_n} at {n}",
                counter.name(),
                2 * n
            ));
        }
    }
    println!(
        "{shape:?} document bytes: {} at {n}, {} at {}",
        small.bytes,
        large.bytes,
        2 * n
    );
    if large.bytes * 10 > small.bytes * 21 {
        failures.push(format!(
            "{shape:?} document bytes: {} at {} is more than 2.1 x {} at {n}",
            large.bytes,
            2 * n,
            small.bytes
        ));
    }
    failures
}

/// Recording, encoding and decoding provenance is linear in a deep configuration, a wide one and
/// a deep rule body, and the compile flattens no term origin set.
#[test]
fn provenance_work_and_bytes_grow_linearly() {
    let failures = on_large_stack(|| {
        let mut failures = Vec::new();
        for (shape, n) in [(Shape::Config, 100), (Shape::Wide, 100), (Shape::Rule, 200)] {
            let small = cost(shape, n, "MAIN");
            let large = cost(shape, 2 * n, "MAIN");
            failures.extend(ratio_failures(shape, n, &small, &large));
        }
        failures
    });
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A name is written once per sentence that holds receipts, not once per receipt: the bytes
/// that lengthening the main module's name adds to the documents of a configuration do not grow
/// with the configuration. Every receipt names its destination module, so a per-receipt copy of
/// the name makes them grow in proportion to the receipts, about twice as many at 200 operands
/// as at 100.
#[test]
fn provenance_bytes_hold_each_name_once() {
    const PAD: usize = 64;
    let extra = |n: usize| {
        let short = format!("MAIN{}", "A".repeat(PAD));
        let long = format!("MAIN{}", "A".repeat(2 * PAD));
        cost(Shape::Config, n, &long).bytes - cost(Shape::Config, n, &short).bytes
    };
    let (small, large) = on_large_stack(|| (extra(100), extra(200)));
    println!("{PAD} more characters of module name add {small} bytes at 100, {large} at 200");
    assert!(
        large <= small + PAD,
        "{PAD} more characters of module name add {small} bytes at 100 operands and {large} at 200"
    );
}
