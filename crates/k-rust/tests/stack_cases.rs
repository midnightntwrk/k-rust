//! Inputs that once overflowed the native stack while loading or compiling, each compiled on a
//! small thread at a size that overflowed it, and executions whose evaluation recurses far deeper
//! than their input, run through the backend facade on a small thread (`docs/backend-port.md`,
//! "Stack bounds").
//!
//! A failure here is a stack overflow, which aborts the process; these tests live in their own
//! binary so that the abort takes down only this file's tests.

use k_rust::backend::{Backend, BackendOptions, ExecuteRequest};
use k_rust::builtin::embedded;
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::kore::parser::parse_pattern;
use k_rust::outer::{LoadOptions, ResolvedSource, load_with_options};

/// The stack of the thread each test compiles on: small enough that the sizes below overflowed
/// it before the fixes, in every build.
const SMALL_STACK: usize = 256 << 10;

/// A definition whose module `MAIN` declares `configuration` and holds `rule`, with a unary
/// numeral at sort `N` and a constructor `l` of a `List` argument.
fn definition(configuration: &str, rule: &str) -> String {
    format!(
        r#"module MAIN-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax N ::= "nz" [symbol(nz)] | s(N) [symbol(s)]
  syntax KItem ::= l(List) [symbol(l)] | a() [symbol(a)] | g(Int) [symbol(g)]
endmodule
module MAIN
  imports MAIN-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:K </k> {configuration}
  {rule}
endmodule
"#
    )
}

/// The `List` literal `ListItem(0) ListItem(1) ...` of `n` elements: a `_List_` nesting one
/// level per element.
fn list(n: usize) -> String {
    (0..n)
        .map(|element| format!("ListItem({element})"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The numeral `s(s(...(nz)))` of `n` levels.
fn numeral(n: usize) -> String {
    format!("{}nz{}", "s(".repeat(n), ")".repeat(n))
}

/// Load module `MAIN` of `source` as `kcompile` does, with the K prelude, on a thread of
/// [`SMALL_STACK`], and compile it when `compile` is set.
fn loads_on_a_small_stack(source: String, compile: bool) {
    std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(move || {
            let mut resolver = |_: &str, required: &str| {
                embedded(required).ok_or_else(|| format!("unexpected require {required}"))
            };
            let loaded = load_with_options(
                ResolvedSource::new("definition.k", &source),
                "MAIN",
                &mut resolver,
                &LoadOptions {
                    implicit_sources: vec![
                        embedded("prelude.md").expect("the prelude is embedded"),
                    ],
                    excluded_module_attributes: vec![
                        CompilationBackend::Rust.excluded_module_attribute().into(),
                    ],
                    ..LoadOptions::default()
                },
            )
            .unwrap_or_else(|error| panic!("the definition does not load: {error:?}"));
            if compile {
                let compiled = compile_loaded_definition(&loaded, CompileOptions::default());
                assert!(compiled.is_ok(), "{:?}", compiled.err());
            }
        })
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish");
}

/// A configuration cell initialised with a `List` literal of 200 elements. Configuration
/// expansion walked the initializer, one level per element, before any compile stage measured
/// it, and overflowed this thread from about 100 elements.
#[test]
fn a_long_list_literal_in_a_configuration_cell_compiles() {
    loads_on_a_small_stack(definition(&format!("<c> {} </c>", list(200)), ""), true);
}

/// A configuration cell initialised with a numeral 200 levels deep, which overflowed in the
/// same walk.
#[test]
fn a_deep_configuration_initializer_compiles() {
    loads_on_a_small_stack(definition(&format!("<c> {} </c>", numeral(200)), ""), true);
}

/// The control for the two above: the same literal in a rule body compiled before as well,
/// since the compile stages run on a stack measured from it.
#[test]
fn the_same_list_literal_in_a_rule_compiles() {
    loads_on_a_small_stack(
        definition("", &format!("rule g(0) => l({})", list(200))),
        true,
    );
}

/// Cells nested 200 deep in a configuration declaration load: configuration expansion
/// generates them one level per cell, on the stack measured from the declaration. It overflowed
/// this thread at 200 before. Loading alone is checked, as compiling nested cells takes time
/// in the square of their depth.
#[test]
fn deeply_nested_cells_load() {
    let open: String = (0..200).map(|cell| format!("<c{cell}> ")).collect();
    let close: String = (0..200).rev().map(|cell| format!(" </c{cell}>")).collect();
    loads_on_a_small_stack(definition(&format!("{open}0{close}"), ""), false);
}

/// A rule whose right-hand side is a `~>` sequence of 4,000 items. Emission turns the sequence
/// into a `kseq` chain one level per item, which the stack measure of the compile stages once
/// counted as one level; it overflowed this thread from about 2,000 items.
#[test]
fn a_long_k_sequence_in_a_rule_compiles() {
    let items = vec!["a()"; 4_000].join(" ~> ");
    loads_on_a_small_stack(definition("", &format!("rule g(0) => {items}")), true);
}

/// A KORE definition in which `run(n, z)` takes `n` rewrite steps to build the term `c^n(z)` and
/// then rewrites to `done(size(c^n(z)))`, where the function `size` counts the `c` levels
/// recursively (`size(c(T)) = 1 + size(T)`): evaluating it descends `n` levels in the
/// simplifier, from an input one level deep.
const DEEP_EVALUATION: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), total{}(), hook{}("INT.add")]
        hooked-symbol intSub{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), total{}(), hook{}("INT.sub")]
        hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.gt")]
        sort SortT{} []
        sort SortState{} []
        symbol z{}() : SortT{} [constructor{}(), functional{}()]
        symbol c{}(SortT{}) : SortT{} [constructor{}(), functional{}()]
        symbol size{}(SortT{}) : SortInt{} [function{}(), total{}()]
        symbol run{}(SortInt{}, SortT{}) : SortState{} [constructor{}(), functional{}()]
        symbol done{}(SortInt{}) : SortState{} [constructor{}(), functional{}()]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(
                run{}(N:SortInt{}, T:SortT{}),
                \equals{SortBool{}, SortState{}}(
                    gtInt{}(N:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            run{}(intSub{}(N:SortInt{}, \dv{SortInt{}}("1")), c{}(T:SortT{}))
        ) [label{}("step")]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(run{}(\dv{SortInt{}}("0"), T:SortT{}), \top{SortState{}}()),
            done{}(size{}(T:SortT{}))
        ) [label{}("measure")]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, z{}()), \top{R}())),
            \equals{SortInt{}, R}(size{}(X0:SortT{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
        ) [label{}("size-z")]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, c{}(T:SortT{})), \top{R}())),
            \equals{SortInt{}, R}(
                size{}(X0:SortT{}),
                \and{SortInt{}}(intAdd{}(\dv{SortInt{}}("1"), size{}(T:SortT{})), \top{SortInt{}}())
            )
        ) [label{}("size-c")]
    endmodule []"#;

/// The levels the deep evaluations below recurse through: far more than a 2 MiB thread holds
/// in any build (about 400 levels in the `dev` profile).
const EVALUATION_LEVELS: usize = 20_000;

/// The stack of the thread each execution runs on: the default for a spawned Rust thread.
const THREAD_STACK: usize = 2 << 20;

/// Execute `run(levels, z)` through the facade on a [`THREAD_STACK`] thread, with the
/// simplification stack budget set to `budget` when given, and return the result text or the
/// error.
fn execute_deep_evaluation(levels: usize, budget: Option<usize>) -> Result<String, String> {
    std::thread::Builder::new()
        .stack_size(THREAD_STACK)
        .spawn(move || {
            let mut backend = Backend::new(DEEP_EVALUATION, "MAIN", BackendOptions::default())
                .expect("the definition loads");
            if let Some(budget) = budget {
                backend.set_simplification_stack_budget(budget);
            }
            let state = parse_pattern(&format!(
                r#"run{{}}(\dv{{SortInt{{}}}}("{levels}"), z{{}}())"#
            ))
            .expect("the state parses");
            backend
                .execute_json(ExecuteRequest::new(state))
                .map_err(|error| error.to_string())
        })
        .expect("the worker should spawn")
        .join()
        .expect("the worker should not panic")
}

/// A recursive function 20,000 levels deep, evaluated from an input one level deep, completes:
/// below its thread's stack the simplifier's recursion goes on on segments, up to
/// `SIMPLIFICATION_STACK_BUDGET`. On this thread alone it stopped with `StackExhausted` a few
/// hundred levels down.
#[test]
fn a_deep_recursive_function_completes_on_a_small_thread() {
    let result = execute_deep_evaluation(EVALUATION_LEVELS, None).expect("the execution runs");
    assert!(
        result.contains(&format!(r#""value":"{EVALUATION_LEVELS}""#)),
        "{result}"
    );
}

/// The same recursion past the stack it may take (a budget of 16 MiB beyond the thread's 2 MiB)
/// stops with `StackExhausted` and does not abort, though the stopped state holds a term 20,000
/// levels deep that the operation then drops. The stop names the thread's budget that stopped it.
#[test]
fn a_recursion_past_its_stack_budget_stops_with_stack_exhausted() {
    use k_rust_backend::stop::{StackLimit, StopCause};
    let budget = 16 << 20;
    let result = execute_deep_evaluation(EVALUATION_LEVELS, Some(budget));
    let text = match &result {
        Ok(text) | Err(text) => text,
    };
    let cause = StopCause::StackExhausted(StackLimit::ThreadBudget(budget));
    assert!(
        text.contains(&format!("{cause:?}")) || text.contains(&cause.to_string()),
        "{result:?}"
    );
}
