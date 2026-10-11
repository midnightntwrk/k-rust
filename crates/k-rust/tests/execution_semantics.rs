//! Execution semantics on the KORE krust compiles, checked in-process.
//!
//! What a run of a compiled definition ends in is the backend's contract: the leaves the backend
//! returns for an initial configuration. `cli.rs` checks how `krust krun` reports these runs
//! (printed KORE, exit status); the tests here compile the definition, assemble the initial
//! configuration from the program text as `krun` does, and ask the backend for the run directly.
//! A test whose result rests on a condition the solver decides needs the backend's Z3 solver
//! (`z3-inference`): without it the step is indeterminate.

#[path = "support/execution_sources.rs"]
#[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
mod execution_sources;
use execution_sources::PINNED_PLUGIN_BN128;
#[cfg(feature = "z3-inference")]
use execution_sources::{NO_EVALUATOR, SEARCH_BOUND, SIZE_BOUND};

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, HaltReasonOutput,
        SearchPatternRequest, SearchTypeArg,
    },
    builtin::embedded,
    definition::ResolvedDefinition,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition, compile_search_pattern,
    },
    kore::{ast::Pattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

/// A definition compiled for the Rust backend with the prelude, and the initial configuration
/// of a program for it. Only the solver-dependent search test reads a target.
#[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
struct Compiled {
    kore: String,
    initial: Pattern,
    /// The parsing and execution contexts of the compilation, as `krun` reads a `--pattern`.
    grammar: ProgramGrammar,
    execution: ResolvedDefinition,
}

#[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
impl Compiled {
    /// The search target `contents` (a rule body, `<k> f(X) </k> requires X >Int 0`) compiled in
    /// `module` as `krun --pattern` compiles it.
    fn target(&self, module: &str, contents: &str) -> Pattern {
        compile_search_pattern(
            self.grammar.resolved(),
            &self.execution,
            module,
            contents,
            Default::default(),
        )
        .unwrap()
        .pattern
    }
}

/// Compile `source` (main module `main`, programs parsed with `syntax`) and assemble the initial
/// configuration whose `$PGM` is `program` parsed at `sort`.
fn compile(source: &str, main: &str, syntax: &str, sort: &str, program: &str) -> Compiled {
    compile_bound(source, main, syntax, sort, program, &[])
}

/// [`compile`], with the other configuration variables bound to the given texts.
fn compile_bound(
    source: &str,
    main: &str,
    syntax: &str,
    sort: &str,
    program: &str,
    bindings: &[(&str, &str)],
) -> Compiled {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("test.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler =
        ConfigurationAssembler::new(&grammar, main, syntax, &artifacts.configuration_variables);
    assembler.program(&Sort::new(sort), program).unwrap();
    for (name, text) in bindings {
        assembler.bind(name, text).unwrap();
    }
    let initial = assembler.finish().unwrap();
    Compiled {
        kore: artifacts.definition_kore,
        initial,
        execution: ResolvedDefinition::resolve(&artifacts.execution_definition).unwrap(),
        grammar,
    }
}

fn execute(compiled: &Compiled, main: &str, max_depth: Option<u64>) -> ExecutionResult {
    let mut backend = Backend::new(&compiled.kore, main, BackendOptions::default()).unwrap();
    backend
        .execute(ExecuteRequest {
            max_depth,
            ..ExecuteRequest::new(compiled.initial.clone())
        })
        .unwrap()
}

fn text(result: &ExecutionResult) -> Vec<String> {
    result
        .leaves
        .iter()
        .map(|leaf| Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap()))
        .collect()
}

/// A function the initial configuration applies that equals `#Bottom` makes the initial
/// configuration itself `\bottom`: the run ends there, before any step, in one vacuous leaf
/// whose state is `\bottom` of the configuration's sort.
#[test]
fn an_initial_configuration_that_simplifies_to_bottom_is_one_vacuous_leaf() {
    const SOURCE: &str = r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [function, symbol(fail)]
  rule fail(_:Int) => #Bottom
  configuration <k> fail($PGM:Int) </k> <exit exit=""> 0 </exit>
endmodule
"#;
    let compiled = compile(SOURCE, "MAIN", "MAIN", "Int", "7");
    let result = execute(&compiled, "MAIN", Some(0));
    assert_eq!(
        result
            .leaves
            .iter()
            .map(|leaf| (leaf.reason, leaf.depth))
            .collect::<Vec<_>>(),
        [(HaltReasonOutput::Vacuous, 0)],
        "{result:?}"
    );
    assert_eq!(text(&result), [r"\bottom{SortGeneratedTopCell{}}()"]);
}

/// A step whose result needs an integer above the size bound (`2 ^Int 2^24`, `1 <<Int (2^24 +
/// 1)`) is not computed, and the run neither ends in a configuration holding the application
/// nor branches on a condition over it (`<<Int` has no interpreted SMT encoding, so the solver
/// would otherwise take both `pos` and the unreachable `nonpos`): it halts on the step with the
/// unsupported-hook reason naming the bound. An application above the bound that the run
/// never needs is left unevaluated and the run goes on, in one leaf: it is dropped by a
/// short-circuit (`unusedshl`, with no definedness condition left), in a condition another
/// conjunct already decides (`guard`) or the solver decides (`decided`), or after a step that
/// carries it (`dropped`). A result within the bound is computed
/// (`computed`, 2^20 + 1 bits). `i` hides the constants from the constant folder.
#[cfg(feature = "z3-inference")]
#[test]
fn a_run_halts_on_a_result_above_the_size_bound() {
    for (program, hook) in [("used", "INT.pow"), ("shl", "INT.shl")] {
        let compiled = compile(SIZE_BOUND, "BOUND", "BOUND", "Pgm", program);
        let result = execute(&compiled, "BOUND", Some(10));
        let [leaf] = result.leaves.as_slice() else {
            panic!("{program}: {result:?}");
        };
        assert_eq!(
            (leaf.reason, leaf.depth),
            (HaltReasonOutput::UnsupportedHook, 1),
            "{program}"
        );
        let detail = leaf.detail.as_deref().unwrap_or_default();
        assert!(
            detail.contains(&format!("unsupported hook '{hook}'"))
                && detail.contains("needs more than 16777216 bits"),
            "{program}: {detail}"
        );
        let [state] = text(&result).try_into().unwrap();
        assert!(
            !state.contains("nonpos") && !state.contains("Lblpos"),
            "{program}: {state}"
        );
    }
    let item = |sort: &str, value: &str| {
        format!(r#"inj{{Sort{sort}{{}}, SortKItem{{}}}}(\dv{{Sort{sort}{{}}}}("{value}"))"#)
    };
    for (program, sort, value) in [
        ("unusedshl", "Bool", "false"),
        ("guard", "Int", "4"),
        ("decided", "Int", "1"),
        ("dropped", "Int", "9"),
        ("computed", "Bool", "true"),
    ] {
        let compiled = compile(SIZE_BOUND, "BOUND", "BOUND", "Pgm", program);
        let result = execute(&compiled, "BOUND", Some(10));
        let [state] = text(&result)
            .try_into()
            .unwrap_or_else(|leaves| panic!("{program}: {leaves:?}"));
        assert!(
            state.contains(&item(sort, value)) && !state.contains("\\ceil"),
            "{program}: {state}"
        );
    }
}

/// A definition each of whose steps adds a fresh key by any of three equal rules.
const RENAMINGS: &str = r#"
module T
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:KItem </k>
  syntax KItem ::= go(Map, List, Int)
  rule [ra]: <k> go(M, L, N) => go(M (?K:Int |-> 0), L ListItem(?K), N -Int 1) </k> requires N >Int 0
  rule [rb]: <k> go(M, L, N) => go(M (?K:Int |-> 0), L ListItem(?K), N -Int 1) </k> requires N >Int 0
  rule [rc]: <k> go(M, L, N) => go(M (?K:Int |-> 0), L ListItem(?K), N -Int 1) </k> requires N >Int 0
endmodule
"#;

/// Each step of `go(M, L, N)` adds a new variable `?K` to the map and the list, by any of three
/// equal rules, so the states at one depth are renamings of each other: their map entries differ
/// only in the names of their keys (which order differently once the counter reaches two digits,
/// `!10` before `!3`), while the list fixes which entry is which. So each depth is one state: the
/// search for every state (a target that is one variable of the configuration's sort, as `krun`
/// searches) finds the five counters once each, and the final state once.
#[test]
fn a_search_finds_the_renamings_of_one_state_once() {
    let compiled = compile(RENAMINGS, "T", "T", "KItem", "go(.Map, .List, 4)");
    let counter = regex::Regex::new(r#"\("([0-9]+)"\)\), dotk\{\}\(\)"#).unwrap();
    let search = |search_type| {
        let mut backend = Backend::new(&compiled.kore, "T", BackendOptions::default()).unwrap();
        let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
        let response = backend
            .search_pattern(SearchPatternRequest {
                search_type,
                ..SearchPatternRequest::new(compiled.initial.clone(), target)
            })
            .unwrap();
        assert!(response.incomplete.is_empty(), "{:?}", response.incomplete);
        let mut counters = response
            .matches
            .iter()
            .map(|found| {
                let text = Printer::compact()
                    .print_pattern(&codec::from_value(&found.state.state).unwrap());
                let [counter] = counter
                    .captures_iter(&text)
                    .map(|found| found[1].to_owned())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap_or_else(|found| panic!("{found:?} in {text}"));
                counter
            })
            .collect::<Vec<_>>();
        counters.sort();
        counters
    };
    assert_eq!(search(SearchTypeArg::Final), ["0"]);
    assert_eq!(search(SearchTypeArg::All), ["0", "1", "2", "3", "4"]);
}

/// Whether a String holds a surrogate code point the definition does not settle (K's string
/// syntax writes one, KORE's literals cannot), so `chrChar(55296)` is neither a value nor
/// undefined: the run keeps the application unevaluated, with a diagnostic naming the hook,
/// rather than ending in `\bottom`.
#[test]
fn chr_of_a_surrogate_is_left_unevaluated() {
    let fixtures =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/hooks");
    let source = std::fs::read_to_string(fixtures.join("hook-boundaries.k")).unwrap();
    let program = std::fs::read_to_string(fixtures.join("surrogate.hooks")).unwrap();
    let compiled = compile(
        &source,
        "HOOK-BOUNDARIES",
        "HOOK-BOUNDARIES-SYNTAX",
        "Pgm",
        &program,
    );
    let result = execute(&compiled, "HOOK-BOUNDARIES", Some(10));
    let states = text(&result).join("\n");
    assert!(
        states.contains("LblchrChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int{}(")
            && states.contains(r#"\dv{SortInt{}}("55296")"#)
            && !states.contains("\\bottom"),
        "{states}"
    );
    let diagnostics = format!(
        "{:?}",
        result
            .leaves
            .iter()
            .map(|leaf| &leaf.diagnostics)
            .collect::<Vec<_>>()
    );
    assert!(
        diagnostics.contains("STRING.chr") && diagnostics.contains("does not determine its value"),
        "{diagnostics}"
    );
}

/// A rule that writes to the `stdout` stream cell appends to its list, and with I/O off the
/// stream buffers the concatenation of what was written: each run ends with what its rules wrote
/// in the buffer, in order, whether literals or a value read from another cell; two rules that
/// both apply write in two leaves, one item each.
#[test]
fn rules_append_their_output_to_the_stream_buffer() {
    let source = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/captured-output/test.k"),
    )
    .unwrap();
    let buffered = |program: &str| {
        let compiled = compile_bound(
            &source,
            "CAPTURED-OUTPUT",
            "CAPTURED-OUTPUT-SYNTAX",
            "Pgm",
            program,
            &[("STDIN", "\"text\""), ("IO", "\"off\"")],
        );
        let result = execute(&compiled, "CAPTURED-OUTPUT", None);
        let mut buffers = text(&result)
            .into_iter()
            .map(|state| {
                let (_, buffer) = state
                    .split_once("Lbl'Hash'buffer")
                    .unwrap_or_else(|| panic!("{program}: no stream buffer in {state}"));
                let string = regex::Regex::new(r#"\\dv\{SortString\{\}\}\("([^"]*)"\)"#).unwrap();
                string
                    .captures_iter(buffer)
                    .map(|found| found[1].to_owned())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        buffers.sort();
        buffers
    };
    assert_eq!(buffered("literal"), [["literal output"]]);
    assert_eq!(buffered("stdin"), [["textoutput"]]);
    assert_eq!(buffered("branch"), [["first"], ["second"]]);
}

/// The BN128 hooks evaluate on the point productions of the pinned plugin, whose KORE labels are
/// generated from the production: membership is `true` on the generator of each group and `false`
/// off the curve or on another constructor of `G1Point`, adding the generator to itself and
/// multiplying it by two give the same point, and the pairing check holds. Each run ends in one
/// `result` with the hook's value, no application left.
#[test]
fn the_bn128_hooks_evaluate_on_the_pinned_plugin_point_productions() {
    let doubled = concat!(
        r#"Lbl'LParUndsCommUndsRParUnds'KRYPTO'Unds'G1Point'Unds'Int'Unds'Int{}("#,
        r#"\dv{SortInt{}}("1368015179489954701390400359078579693043519447331113978918064868415326638035"), "#,
        r#"\dv{SortInt{}}("9918110051302171585080402603319702774565515993150576347155970296011118125764"))"#,
    );
    let boolean = |value: &str| format!(r#"\dv{{SortBool{{}}}}("{value}")"#);
    for (check, expected) in [
        ("valid", boolean("true")),
        ("off-curve", boolean("false")),
        ("other-constructor", boolean("false")),
        ("g2-valid", boolean("true")),
        ("add", doubled.to_owned()),
        ("mul", doubled.to_owned()),
        ("pairing", boolean("true")),
    ] {
        let compiled = compile(PINNED_PLUGIN_BN128, "MAIN", "MAIN", "Check", check);
        let result = execute(&compiled, "MAIN", Some(10));
        let [state] = text(&result)
            .try_into()
            .unwrap_or_else(|leaves| panic!("{check}: {leaves:?}"));
        assert!(
            state.contains("Lblresult") && state.contains(&expected),
            "{check}: {state}"
        );
        assert!(
            !state.contains("BN128") && !state.contains("isValid"),
            "{check}: {state}"
        );
    }
}

/// An application of a `total` hook without an evaluator (`expFloat`) is left unevaluated with a
/// diagnostic, so a run whose result does not depend on it ends with that result; a run that
/// decides a condition over it, or ends on a configuration holding it, halts on the
/// unsupported-hook reason, as does one that reaches a partial hook without an evaluator
/// (`logFloat`), whose definedness is unknown even where the application is discarded.
#[cfg(feature = "z3-inference")]
#[test]
fn an_application_without_an_evaluator_halts_a_run_only_where_it_is_needed() {
    let item = |sort: &str, value: &str| {
        format!(r#"inj{{Sort{sort}{{}}, SortKItem{{}}}}(\dv{{Sort{sort}{{}}}}("{value}"))"#)
    };
    for (program, value) in [
        ("unused", item("Bool", "false")),
        ("branch", item("Int", "7")),
    ] {
        let compiled = compile(NO_EVALUATOR, "NOEVAL", "NOEVAL", "Pgm", program);
        let result = execute(&compiled, "NOEVAL", Some(10));
        let [leaf] = result.leaves.as_slice() else {
            panic!("{program}: {result:?}");
        };
        assert_eq!(
            leaf.reason,
            HaltReasonOutput::Stuck,
            "{program}: {result:?}"
        );
        let [state] = text(&result).try_into().unwrap();
        assert!(state.contains(&value), "{program}: {state}");
        let diagnostics = format!("{:?}", leaf.diagnostics);
        assert!(
            diagnostics.contains("UnsupportedHookUnevaluated") && diagnostics.contains("FLOAT.exp"),
            "{program}: {diagnostics}"
        );
    }
    for (program, hook) in [
        ("used", "FLOAT.exp"),
        ("decide", "FLOAT.exp"),
        ("partial", "FLOAT.log"),
    ] {
        let compiled = compile(NO_EVALUATOR, "NOEVAL", "NOEVAL", "Pgm", program);
        let result = execute(&compiled, "NOEVAL", Some(10));
        let [leaf] = result.leaves.as_slice() else {
            panic!("{program}: {result:?}");
        };
        assert_eq!(leaf.reason, HaltReasonOutput::UnsupportedHook, "{program}");
        let detail = leaf.detail.as_deref().unwrap_or_default();
        assert!(
            detail.contains(&format!(
                "unsupported hook '{hook}' on constructor-like arguments"
            )),
            "{program}: {detail}"
        );
        let [state] = text(&result).try_into().unwrap();
        assert!(
            !state.contains("Lblpos") && !state.contains("Lblnonpos"),
            "{program}: {state}"
        );
    }
}

/// A search target's condition over a `^Int` result above the size bound is decided by the
/// solver, which reads `^Int` as the interpreted power: the final `f(X)` of `power` is a solution
/// of `X >Int 0` and not of `X <=Int 0`. One over a `<<Int` result above the bound (no
/// interpreted encoding) is not decided either way: the search reports the state as incomplete
/// with the unsupported-hook reason and finds no solution.
#[cfg(feature = "z3-inference")]
#[test]
fn a_search_condition_on_a_result_above_the_size_bound_is_decided_only_by_an_interpreted_hook() {
    let search = |program: &str, condition: &str| {
        let compiled = compile(SEARCH_BOUND, "SEARCH-BOUND", "SEARCH-BOUND", "Pgm", program);
        let target = compiled.target(
            "SEARCH-BOUND",
            &format!("<k> f(X) </k> requires {condition}"),
        );
        let mut backend =
            Backend::new(&compiled.kore, "SEARCH-BOUND", BackendOptions::default()).unwrap();
        backend
            .search_pattern(SearchPatternRequest {
                search_type: SearchTypeArg::All,
                ..SearchPatternRequest::new(compiled.initial, target)
            })
            .unwrap()
    };
    for (condition, solutions) in [("X >Int 0", 1), ("X <=Int 0", 0)] {
        let response = search("power", condition);
        assert!(
            response.incomplete.is_empty(),
            "{condition}: {:?}",
            response.incomplete
        );
        assert_eq!(
            response.matches.len(),
            solutions,
            "{condition}: {:?}",
            response.matches
        );
    }
    for condition in ["X <=Int 0", "X >Int 0"] {
        let response = search("go", condition);
        assert!(
            response.matches.is_empty(),
            "{condition}: {:?}",
            response.matches
        );
        let incomplete = format!("{:?}", response.incomplete);
        assert!(
            incomplete.contains("INT.shl") && incomplete.contains("16777217"),
            "{condition}: {incomplete}"
        );
    }
}

/// An initial configuration whose constraint is unsatisfiable (`N ==Int 0` and `N =/=Int 0`) but
/// not simplified to `\bottom` takes the rule step, whose path constraint is then refuted: the
/// run ends in one vacuous leaf at depth 1 whose state is `\bottom`.
#[test]
fn a_step_under_a_refuted_path_constraint_is_a_vacuous_leaf() {
    const SOURCE: &str = r#"
module MAIN
  imports INT
  syntax State ::= "a" | "b"
  configuration <k> $PGM:State </k>
  rule a => b [label(step)]
endmodule
"#;
    let compiled = compile(SOURCE, "MAIN", "MAIN", "State", "a");
    let condition = |operator: &str| {
        format!(
            r#"\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}({operator}{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")), \dv{{SortBool{{}}}}("true"))"#
        )
    };
    let constrained = parse_pattern(&format!(
        r#"\and{{SortGeneratedTopCell{{}}}}({}, \and{{SortGeneratedTopCell{{}}}}({}, {}))"#,
        Printer::compact().print_pattern(&compiled.initial),
        condition("Lbl'UndsEqlsEqls'Int'Unds'"),
        condition("Lbl'UndsEqlsSlshEqls'Int'Unds'"),
    ))
    .unwrap();
    let mut backend = Backend::new(&compiled.kore, "MAIN", BackendOptions::default()).unwrap();
    let result = backend.execute(ExecuteRequest::new(constrained)).unwrap();
    let [leaf] = result.leaves.as_slice() else {
        panic!("{result:?}");
    };
    assert_eq!((leaf.reason, leaf.depth), (HaltReasonOutput::Vacuous, 1));
    assert_eq!(text(&result), [r"\bottom{SortGeneratedTopCell{}}()"]);
}

/// Narrowing the symbolic map of `<m>` against the `mapsel` rule's `(_K |-> _V) REST` binds the
/// frame and the entry to fresh variables, which the result names with KORE identifiers.
#[cfg(feature = "z3-inference")]
#[test]
fn fresh_remainder_variables_are_kore_identifiers() {
    let compiled = compile(
        include_str!("fixtures/reference/matching/map/test.k"),
        "TEST",
        "TEST",
        "Pgm",
        "go",
    );
    let initial =
        parse_pattern(include_str!("fixtures/reference/matching/map/pgm-map.kore")).unwrap();
    let mut backend = Backend::new(&compiled.kore, "TEST", BackendOptions::default()).unwrap();
    let result = backend
        .execute(ExecuteRequest {
            max_depth: Some(1),
            ..ExecuteRequest::new(initial)
        })
        .unwrap();
    let variable = regex::Regex::new(r"([^\s(),{}]+):Sort").unwrap();
    let mut names = text(&result)
        .iter()
        .flat_map(|state| {
            variable
                .captures_iter(state)
                .map(|found| found[1].to_owned())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    let kore_identifier = |name: &str| {
        let mut characters = name.chars();
        characters
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic())
            && characters
                .all(|character| character.is_ascii_alphanumeric() || "'-".contains(character))
    };
    assert!(names.iter().all(|name| kore_identifier(name)), "{names:?}");
    assert!(names.contains(&"Ex-hFrame-b0".to_owned()), "{names:?}");
    assert!(names.contains(&"VarM".to_owned()), "{names:?}");
}

/// The solver prelude of a definition holding two `smt-lemma` equations of one function with
/// different results is inconsistent, so a run that needs the solver reports that failure as its
/// result, though a rule could rewrite without end.
#[cfg(feature = "z3-inference")]
#[test]
fn a_run_reports_an_inconsistent_solver_prelude() {
    let compiled = compile(
        include_str!("fixtures/inconsistent-smt-prelude-loop.k"),
        "LIVENESS-KRUN",
        "LIVENESS-KRUN",
        "State",
        "start(f(0))",
    );
    let mut backend =
        Backend::new(&compiled.kore, "LIVENESS-KRUN", BackendOptions::default()).unwrap();
    let error = backend
        .execute(ExecuteRequest {
            max_depth: Some(10),
            ..ExecuteRequest::new(compiled.initial)
        })
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "could not initialize Z3: the SMT prelude (the definition's SMT axioms and any user prelude) is unsatisfiable"
    );
}

/// The result of `krun`'s run driver (`Backend::run_cli`) on the internalized initial
/// configuration, with `krun`'s defaults (strategy `any`), the depth bound `depth` and the
/// search `search` (`None` runs).
#[cfg(feature = "z3-inference")]
fn run_driver(
    compiled: &Compiled,
    main: &str,
    depth: u64,
    search: Option<k_rust::backend::execution::SearchRunOptions>,
) -> Result<k_rust::backend::execution::BackendRunOutput, Box<dyn std::error::Error>> {
    use k_rust::backend::execution::BackendRunOptions;
    use k_rust_backend::{rewrite::ExecutionMode, simplify::DEFAULT_MAX_SIMPLIFICATION_ITERATIONS};

    let mut backend = Backend::new(&compiled.kore, main, BackendOptions::default()).unwrap();
    let initial = backend
        .internalize_executable(None, &compiled.initial)
        .unwrap();
    let function_symbols = backend
        .select_definition(None)
        .unwrap()
        .function_symbol_names();
    backend.run_cli(
        None,
        initial,
        BackendRunOptions {
            depth,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            breadth_limit: None,
            execute_to_branch: false,
            cut_point_rules: Default::default(),
            terminal_rules: Default::default(),
            strategy: ExecutionMode::Any,
            search,
            match_target: None,
            function_symbols,
            stop_leaves: None,
            step_timeout: None,
            moving_average_timeout: false,
            capture_stdout: false,
            execution_input: None,
        },
    )
}

/// `krun`'s run driver on results above the size bound. `2 ^Int 2^24` is defined (its exponent is
/// not negative) but not computed, so a step whose result discards it, by the short-circuit of
/// `false andBool` (`unused`) or the branch of a decided `#if` (`branch`), ends in the one result
/// that does not hold it, with no definedness condition over it. A step whose result holds such a
/// value (`used`), or whose rules branch on a condition over a `<<Int` one the solver cannot
/// decide (`shl`), halts the run at that step with the unsupported-hook reason naming the bound.
#[cfg(feature = "z3-inference")]
#[test]
fn the_run_driver_neither_branches_nor_ends_on_a_result_above_the_size_bound() {
    for (program, value) in [
        (
            "unused",
            r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("false"))"#,
        ),
        (
            "branch",
            r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7"))"#,
        ),
    ] {
        let compiled = compile(SIZE_BOUND, "BOUND", "BOUND", "Pgm", program);
        let output = run_driver(&compiled, "BOUND", 10, None).unwrap();
        assert_eq!(output.exit_code, 0, "{program}");
        let result = Printer::compact().print_pattern(&output.pattern.to_pattern());
        assert!(
            result.contains(value) && !result.contains(r"\ceil") && !result.contains(r"\or"),
            "{program}: {result}"
        );
    }
    for (program, hook) in [("used", "INT.pow"), ("shl", "INT.shl")] {
        let compiled = compile(SIZE_BOUND, "BOUND", "BOUND", "Pgm", program);
        let error = run_driver(&compiled, "BOUND", 10, None)
            .map(|output| Printer::compact().print_pattern(&output.pattern.to_pattern()))
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("halted at depth 1")
                && error.contains(&format!(
                    "unsupported hook '{hook}' on constructor-like arguments"
                ))
                && error.contains("needs more than 16777216 bits"),
            "{program}: {error}"
        );
    }
}

/// `krun`'s run driver searches the states of [`a_search_finds_the_renamings_of_one_state_once`]
/// with no bound on depth: the final state once, and each of the five counters once.
#[cfg(feature = "z3-inference")]
#[test]
fn the_run_driver_searches_the_renamings_of_one_state_once() {
    use k_rust::backend::execution::SearchRunOptions;
    use k_rust_backend::search::SearchType;

    let compiled = compile(RENAMINGS, "T", "T", "KItem", "go(.Map, .List, 4)");
    let counter = regex::Regex::new(r#"\("([0-9]+)"\)\), dotk\{\}\(\)"#).unwrap();
    let search = |search_type| {
        let output = run_driver(
            &compiled,
            "T",
            u64::MAX,
            Some(SearchRunOptions {
                search_type,
                pattern: None,
                bound: None,
            }),
        )
        .unwrap();
        let result = Printer::compact().print_pattern(&output.pattern.to_pattern());
        let mut counters = counter
            .captures_iter(&result)
            .map(|found| found[1].to_owned())
            .collect::<Vec<_>>();
        counters.sort();
        counters
    };
    assert_eq!(search(SearchType::Final), ["0"]);
    assert_eq!(search(SearchType::Star), ["0", "1", "2", "3", "4"]);
}

/// A definition with a `multiplicity="*"` cell `<r>` of collection type `COLLECTION`, and pairs
/// of commands that read one instance written as a cell (`get`, `anyP`) and as an alias of that
/// cell (`getA`, `anyPA`). `mk` adds an instance written as a cell, `put` one held by a variable.
const ALIASED_INSTANCES: &str = r#"
module TEST-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= mk(Int, Int) | put(Int, Int) | get(Int) | getA(Int) | anyP() | anyPA()
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT
  imports LIST
  configuration <T> <k> $PGM:Pgm </k> <rs> <r multiplicity="*" type="COLLECTION"> <rid> 0 </rid> <v> 0 </v> </r> </rs> <out> .List </out> </T>

  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> mk(I, V) => .K ... </k> <rs> ... .Bag => <r> <rid> I </rid> <v> V </v> </r> ... </rs>
  syntax KItem ::= putR(RCell)
  rule <k> put(I, V) => putR(<r> <rid> I </rid> <v> V </v> </r>) ... </k>
  rule <k> putR(R) => .K ... </k> <rs> ... .Bag => R ... </rs>

  rule <k> get(I) => .K ... </k> <r> <rid> I </rid> <v> V </v> </r> <out> ... .List => ListItem(V) </out>
  rule <k> getA(I) => .K ... </k> (<r> <rid> I </rid> <v> V </v> </r> #as _R) <out> ... .List => ListItem(V) </out>
  rule <k> anyP() => .K ... </k> <r> <rid> I </rid> ... </r> <out> ... .List => ListItem(I) </out>
  rule <k> anyPA() => .K ... </k> (<r> <rid> I </rid> ... </r> #as _R) <out> ... .List => ListItem(I) </out>
endmodule
"#;

/// What a program ends in on [`ALIASED_INSTANCES`] for `collection`: the leaves (or the error)
/// of its run and the final states of its search, each with the aliased commands renamed to
/// their unaliased partners.
fn aliased_instance_outcomes(collection: &str, programs: &[&str]) -> Vec<(String, Vec<String>)> {
    let source = ALIASED_INSTANCES.replace("COLLECTION", collection);
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("test.k", &source),
        "TEST",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let rename = |text: String| {
        text.replace("LblgetA'", "Lblget'")
            .replace("LblanyPA'", "LblanyP'")
    };
    let print = |pattern: &serde_json::Value| {
        rename(Printer::compact().print_pattern(&codec::from_value(pattern).unwrap()))
    };
    programs
        .iter()
        .map(|program| {
            let mut assembler = ConfigurationAssembler::new(
                &grammar,
                "TEST",
                "TEST-SYNTAX",
                &artifacts.configuration_variables,
            );
            assembler.program(&Sort::new("Pgm"), program).unwrap();
            let initial = assembler.finish().unwrap();
            let mut backend = Backend::new(
                &artifacts.definition_kore,
                "TEST",
                BackendOptions::default(),
            )
            .unwrap();
            let run = match backend.execute(ExecuteRequest::new(initial.clone())) {
                Ok(result) => result
                    .leaves
                    .iter()
                    .map(|leaf| format!("{:?} {}", leaf.reason, print(&leaf.state)))
                    .collect::<Vec<_>>()
                    .join("\n"),
                Err(error) => format!("error: {error:?}"),
            };
            let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
            let mut finals = match backend.search_pattern(SearchPatternRequest {
                search_type: SearchTypeArg::Final,
                ..SearchPatternRequest::new(initial, target)
            }) {
                Ok(response) => response
                    .matches
                    .iter()
                    .map(|found| print(&found.state.state))
                    .collect(),
                Err(error) => vec![format!("error: {error:?}")],
            };
            finals.sort();
            (rename(run), finals)
        })
        .collect()
}

/// `P #as V` matches what `P` matches and binds `V` to it, so a rule that reads an instance of
/// a `multiplicity="*"` cell through an alias applies exactly where the rule that writes the
/// instance alone applies, and ends in the same configuration: on no instance (stuck), on one,
/// and on several (each instance once in a search), for a key that is written or a variable.
#[test]
fn an_alias_of_a_collection_cell_instance_matches_what_the_instance_matches() {
    let three = "mk(1,10) ; mk(2,20) ; mk(3,30) ; ";
    let pairs = [
        ("get(1)", "getA(1)"),
        ("anyP()", "anyPA()"),
        ("mk(1,10) ; get(1)", "mk(1,10) ; getA(1)"),
        ("mk(1,10) ; get(2)", "mk(1,10) ; getA(2)"),
        ("mk(1,10) ; anyP()", "mk(1,10) ; anyPA()"),
        (
            &format!("{three}get(2) ; get(3) ; get(2)"),
            &format!("{three}getA(2) ; getA(3) ; getA(2)"),
        ),
        (
            &format!("{three}get(3) ; get(3)"),
            &format!("{three}getA(3) ; getA(3)"),
        ),
        (&format!("{three}get(4)"), &format!("{three}getA(4)")),
        (&format!("{three}anyP()"), &format!("{three}anyPA()")),
    ];
    let programs = pairs
        .iter()
        .flat_map(|(cell, alias)| [*cell, *alias])
        .collect::<Vec<_>>();
    for collection in ["Map", "List"] {
        let outcomes = aliased_instance_outcomes(collection, &programs);
        for ((cell, alias), outcome) in pairs.iter().zip(outcomes.chunks(2)) {
            assert_eq!(outcome[0], outcome[1], "{collection}: {cell} / {alias}");
        }
        // Not vacuous: two reads of the instance added last complete, and a search finds an
        // instance (each of the three in a Map, whose instances are found by key).
        let (run, _) = &outcomes[12];
        assert!(
            run.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())") && !run.contains("error"),
            "{collection}: {run}"
        );
        let (_, finals) = &outcomes[outcomes.len() - 1];
        assert!(
            !finals.is_empty() && finals.iter().all(|state| !state.contains("error")),
            "{collection}: {finals:?}"
        );
        if collection == "Map" {
            assert_eq!(finals.len(), 3, "{finals:?}");
        }
        // A right-side variable of the cell sort in its collection is the item holding its
        // value, as the cell written there is: the instance `put` adds is read as `mk`'s is.
        let added = aliased_instance_outcomes(
            collection,
            &[
                "mk(1,10) ; mk(2,20) ; get(2)",
                "put(1,10) ; put(2,20) ; get(2)",
            ],
        );
        assert_eq!(added[0], added[1], "{collection}");
        assert!(
            added[0].0.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())"),
            "{collection}: {}",
            added[0].0
        );
    }
}
