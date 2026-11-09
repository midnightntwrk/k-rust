//! Inputs that once overflowed the native stack while loading or compiling, each compiled on a
//! small thread at a size that overflowed it, executions whose evaluation recurses far deeper
//! than their input, run through the backend facade on a small thread, KORE patterns a million
//! levels deep converted to KAST on an 8 MiB thread, and a request holding a list longer than
//! the backend's deepest stack executed through the facade to a pattern result, which is walked
//! and dropped, on an 8 MiB thread (`docs/backend-port.md`, "Stack bounds").
//!
//! A failure here is a stack overflow, which aborts the process; these tests live in their own
//! binary so that the abort takes down only this file's tests.

use k_rust::backend::{Backend, BackendOptions, ExecuteRequest};
use k_rust::builtin::embedded;
use k_rust::kast::convert::Converter;
use k_rust::kast::{Sort, Term};
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::kore::ast::{KoreString, Pattern, Sort as KoreSort, Symbol, Variable, VariableKind};
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
            let mut backend = Backend::new(DEEP_EVALUATION, "MAIN", BackendOptions::DEFAULT)
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

/// The levels of the patterns converted to KAST below: a collection of a million elements, which
/// a KORE result holds as a chain one level per element. The list and the map take about 2 GiB
/// each in a `dev` build.
const CONVERSION_LEVELS: usize = 1_000_000;

/// The stack of the thread each conversion runs on: a main thread's default on Linux. A
/// conversion that recursed once per level overflowed it at about 4,000 levels in a release
/// build.
const CONVERSION_STACK: usize = 8 << 20;

/// Run `work` on a [`CONVERSION_STACK`] thread.
fn on_a_conversion_thread(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(CONVERSION_STACK)
        .spawn(work)
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish");
}

/// The application of the KORE symbol `name`, without sort parameters, to `arguments`.
fn apply(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

/// The nullary KORE sort `name`.
fn kore_sort(name: &str) -> KoreSort {
    KoreSort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

/// The integer `value`. A collection in a result holds its elements injected into `KItem`; the
/// conversion removes injections (a unit test of `kast::convert` shows it), and they are left out
/// here, as they add memory and no depth.
fn int(value: usize) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortInt"),
        value: KoreString::from_bytes(value.to_string().into_bytes()),
    }
}

/// The arguments of `term`, an application of `label`.
fn arguments_of<'t>(term: &'t Term, label: &str) -> &'t [Term] {
    match term {
        Term::Apply {
            label: applied,
            arguments,
        } if applied.name == label => arguments,
        _ => panic!("expected an application of {label}"),
    }
}

/// Whether `term` is the `Int` token of `value`.
fn is_int(term: &Term, value: usize) -> bool {
    matches!(term, Term::Token { token, sort } if *token == value.to_string() && sort.name == "Int")
}

/// A `List` of a million elements, as a left-nested `_List_` chain over `.List`, converts on an
/// 8 MiB thread: each level is a `_List_` application whose second argument is the element.
#[test]
fn a_million_element_list_converts_to_kast_on_an_8_mib_thread() {
    on_a_conversion_thread(|| {
        let mut list = apply("Lbl'Stop'List", Vec::new());
        for element in 0..CONVERSION_LEVELS {
            list = apply(
                "Lbl'Unds'List'Unds'",
                vec![list, apply("LblListItem", vec![int(element)])],
            );
        }
        let term = Converter::new(&Default::default())
            .convert(&list)
            .expect("the list converts");
        let mut level = &term;
        for element in (0..CONVERSION_LEVELS).rev() {
            let [rest, last] = arguments_of(level, "_List_") else {
                panic!("`_List_` is binary");
            };
            let [value] = arguments_of(last, "ListItem") else {
                panic!("`ListItem` is unary");
            };
            assert!(is_int(value, element), "element {element}");
            level = rest;
        }
        assert!(arguments_of(level, ".List").is_empty());
    });
}

/// A `Map` of a million entries, as a right-nested `_Map_` chain over `.Map`, converts on an
/// 8 MiB thread: each level is a `_Map_` application whose first argument is the entry.
#[test]
fn a_million_entry_map_converts_to_kast_on_an_8_mib_thread() {
    on_a_conversion_thread(|| {
        let mut map = apply("Lbl'Stop'Map", Vec::new());
        for key in (0..CONVERSION_LEVELS).rev() {
            let entry = apply("Lbl'UndsPipe'-'-GT-Unds'", vec![int(key), int(key % 256)]);
            map = apply("Lbl'Unds'Map'Unds'", vec![entry, map]);
        }
        let term = Converter::new(&Default::default())
            .convert(&map)
            .expect("the map converts");
        let mut level = &term;
        for key in 0..CONVERSION_LEVELS {
            let [entry, rest] = arguments_of(level, "_Map_") else {
                panic!("`_Map_` is binary");
            };
            let [stored, value] = arguments_of(entry, "_|->_") else {
                panic!("`_|->_` is binary");
            };
            assert!(
                is_int(stored, key) && is_int(value, key % 256),
                "entry {key}"
            );
            level = rest;
        }
        assert!(arguments_of(level, ".Map").is_empty());
    });
}

/// A variable whose sort nests a million sort applications converts on an 8 MiB thread: the
/// KAST sort has the same nesting.
#[test]
fn a_million_level_sort_converts_to_kast_on_an_8_mib_thread() {
    on_a_conversion_thread(|| {
        let mut sort = kore_sort("SortInt");
        for _ in 0..CONVERSION_LEVELS {
            sort = KoreSort::Application {
                name: "SortWrap".to_owned(),
                arguments: vec![sort],
            };
        }
        let variable = Pattern::Variable(Variable {
            kind: VariableKind::Element,
            name: "VarX".to_owned(),
            sort,
        });
        let term = Converter::new(&Default::default())
            .convert(&variable)
            .expect("the variable converts");
        let Term::Variable {
            name,
            sort: Some(sort),
        } = &term
        else {
            panic!("a variable converts to a sorted variable");
        };
        assert_eq!(name, "X");
        let mut level: &Sort = sort;
        for _ in 0..CONVERSION_LEVELS {
            assert_eq!(level.name, "Wrap");
            let [parameter] = level.parameters.as_slice() else {
                panic!("`Wrap` has one parameter");
            };
            level = parameter;
        }
        assert!(level.name == "Int" && level.parameters.is_empty());
    });
}

/// A definition with a builtin `List` of integers and a constructor `wrap` of a list, and no
/// rule.
const LIST_STATE: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortList{}
            [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
        sort SortState{} []
        hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
        hooked-symbol listItem{}(SortInt{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
        hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
            [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
        symbol wrap{}(SortList{}) : SortState{} [constructor{}(), functional{}()]
    endmodule []"#;

/// A state holding a list of a million entries, or of one entry more than the deepest pattern
/// the backend provides a stack for where that is more, written as a right-nested `listConcat`
/// chain, executes through `execute_kore` on an 8 MiB thread, and its one leaf, a pattern
/// holding every entry in order, is walked and dropped there.
/// The facade sizes the operation for the request with its collections associated, where the
/// list is one level deep, and builds the leaf's pattern, which its holder walks and drops,
/// with explicit stacks. Sized for the nested chain, the request was refused with
/// `InsufficientStack` on any thread.
#[test]
fn a_state_holding_a_million_entry_list_executes_to_a_pattern_on_an_8_mib_thread() {
    on_a_conversion_thread(|| {
        let entries = 1_000_000.max(k_rust_backend::nesting::max_depth() + 1);
        let element = |value: usize| apply("listItem", vec![int(value)]);
        let mut list = element(entries - 1);
        for value in (0..entries - 1).rev() {
            list = apply("listConcat", vec![element(value), list]);
        }
        let mut backend = Backend::new(LIST_STATE, "MAIN", BackendOptions::DEFAULT)
            .expect("the definition loads");
        let mut request = ExecuteRequest::new(apply("wrap", vec![list]));
        request.max_depth = Some(0);
        let result = backend.execute_kore(request).expect("the state executes");
        let [leaf] = result.leaves.as_slice() else {
            panic!("one leaf, not {}", result.leaves.len());
        };
        let (mut wraps, mut items) = (0, Vec::with_capacity(entries));
        k_rust::kore::walk::for_each_post_order(&leaf.state, |pattern| match pattern {
            Pattern::Application { symbol, .. } if symbol.name == "wrap" => wraps += 1,
            Pattern::DomainValue { value, .. } => items.push(value.clone()),
            _ => {}
        });
        assert_eq!(wraps, 1);
        assert_eq!(items.len(), entries);
        assert!(
            items
                .iter()
                .enumerate()
                .all(|(index, value)| value.as_bytes() == index.to_string().as_bytes()),
            "every entry, in order"
        );
        drop(result);
    });
}
