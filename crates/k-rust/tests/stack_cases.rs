//! Inputs that once overflowed the native stack while loading or compiling, each compiled on a
//! small thread at a size that overflowed it (`docs/backend-port.md`, "Stack bounds").
//!
//! A failure here is a stack overflow, which aborts the process; these tests live in their own
//! binary so that the abort takes down only this file's tests.

use k_rust::builtin::embedded;
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
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
