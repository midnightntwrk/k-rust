//! How the provenance of a definition grows with the definition.
//!
//! Every generating pass gives each node it builds a receipt naming the node's origin set and its
//! destination, and `KRUST-PROVENANCE` writes those receipts and every node's metadata. Each of
//! those per-node items must cost a constant amount of work, memory and bytes, whatever the
//! depth of the node and whatever the size of the origin set it inherits: a deep chain (depth
//! and width grow together), a wide sequence (width without depth) and a deep rule body (the
//! compile-stage passes re-receipt it) are compiled at N, 2N and 3N operands, encoded and
//! decoded, and every provenance work counter and the documents' length must grow by equal
//! steps.
//!
//! Counters rather than allocated bytes or time are the oracle, and successive differences
//! rather than ratios: every total includes the prelude's work K, which does not grow with N and
//! at these sizes is many times the part that does, so a ratio of totals hides a quadratic term
//! behind it. For a measure f(n) = K + a n + c n^2 the differences d1 = f(2N) - f(N) = a N + 3 c
//! N^2 and d2 = f(3N) - f(2N) = a N + 5 c N^2 do not contain K, and d2 <= 1.1 d1 fails exactly
//! when c > a / (17 N). Here a is the measure's own cost per operand, a few to a few tens of
//! steps for a counter, so the test catches any per-node item that grows with the depth or
//! with the inherited set by even a fraction of a step per level; the test prints a and that
//! threshold for every measure.

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use k_rust::builtin::embedded;
use k_rust::definition::json;
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options};
use k_rust_kore::measure::{Counter, Snapshot, snapshot};

/// The provenance work counters whose growth the tests bound.
const COUNTERS: [Counter; 11] = [
    Counter::ProvenanceSetNodesBuilt,
    Counter::ProvenanceSetPartsBuilt,
    Counter::ProvenanceLinksSteps,
    Counter::ProvenanceNonflatFlattens,
    Counter::ProvenanceEncoderSetKeys,
    Counter::ProvenanceEncoderAnchorInternings,
    Counter::ProvenanceEncoderAnchorRoots,
    Counter::ProvenanceNormalPartComparisons,
    Counter::ProvenanceAnchorPathSteps,
    Counter::ProvenanceEncoderPreorderSteps,
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

/// The failures of the difference test over the costs of `shape` at `n`, `2n` and `3n`
/// operands: a compile that flattened a term origin set, and every measure whose second
/// difference exceeds its first by more than a tenth.
fn difference_failures(shape: Shape, n: usize, costs: &[Cost; 3]) -> Vec<String> {
    let mut failures = Vec::new();
    let flattens = costs
        .each_ref()
        .map(|cost| cost.compile.get(Counter::ProvenanceNonflatFlattens));
    if flattens != [0; 3] {
        failures.push(format!(
            "{shape:?}: the compile flattened a term origin set ({flattens:?} at {n}, {}, {})",
            2 * n,
            3 * n
        ));
    }
    let mut check = |name: &str, [small, middle, large]: [u64; 3]| {
        let first = i128::from(middle) - i128::from(small);
        let second = i128::from(large) - i128::from(middle);
        // The cost per operand, and the coefficient of a quadratic term the test detects.
        let per_operand = first as f64 / n as f64;
        println!(
            "{shape:?} {name}: {small}, {middle}, {large} at {n}, {}, {}; differences {first}, \
             {second}; {per_operand:.2} per operand, a quadratic term above {:.4} per operand^2 \
             fails",
            2 * n,
            3 * n,
            per_operand / (17.0 * n as f64)
        );
        if second * 10 > first * 11 {
            failures.push(format!(
                "{shape:?} {name}: it grew by {first} from {n} to {} operands and by {second} \
                 from {} to {}",
                2 * n,
                2 * n,
                3 * n
            ));
        }
    };
    for counter in COUNTERS {
        check(
            counter.name(),
            costs.each_ref().map(|cost| cost.total.get(counter)),
        );
    }
    check(
        "document bytes",
        costs.each_ref().map(|cost| cost.bytes as u64),
    );
    failures
}

/// Recording, encoding and decoding provenance is linear in a deep configuration, a wide one and
/// a deep rule body, and the compile flattens no term origin set.
#[test]
fn provenance_work_and_bytes_grow_linearly() {
    let failures = on_large_stack(|| {
        let mut failures = Vec::new();
        for (shape, n) in [(Shape::Config, 100), (Shape::Wide, 100), (Shape::Rule, 200)] {
            let costs = [1, 2, 3].map(|multiple| cost(shape, multiple * n, "MAIN"));
            failures.extend(difference_failures(shape, n, &costs));
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
