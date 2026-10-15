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
        Backend, BackendDiagnosticOutput, BackendOptions, ExecuteRequest, ExecutionResult,
        HaltReasonOutput, SearchPatternRequest, SearchRequest, SearchTypeArg,
    },
    builtin::embedded,
    definition::ResolvedDefinition,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ProgramGrammar, compile_loaded_definition, compile_search_pattern,
    },
    kore::{ast::Pattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options},
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
/// `!10` before `!3`, and so do the sides of the equalities that keep two keys apart), while the
/// list fixes which entry is which. So each depth is one state: the search for every state (a
/// target that is one variable of the configuration's sort, as `krun` searches) finds the five
/// counters once each, and the final state once, and so does the search for states without a
/// target.
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
    let states = |search_type| {
        let mut backend = Backend::new(&compiled.kore, "T", BackendOptions::default()).unwrap();
        let response = backend
            .search(SearchRequest {
                search_type,
                ..SearchRequest::new(compiled.initial.clone())
            })
            .unwrap();
        assert!(response.incomplete.is_empty(), "{:?}", response.incomplete);
        let mut counters = response
            .states
            .iter()
            .map(|found| {
                let text =
                    Printer::compact().print_pattern(&codec::from_value(&found.state).unwrap());
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
    assert_eq!(states(SearchTypeArg::Final), ["0"]);
    assert_eq!(states(SearchTypeArg::All), ["0", "1", "2", "3", "4"]);
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
/// diagnostic, so a run whose result does not depend on it ends with that result (in the operand
/// a decided `#if` discards, `branch`, it is never evaluated, so there is no diagnostic); a run that
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
        assert_eq!(
            diagnostics.contains("UnsupportedHookUnevaluated") && diagnostics.contains("FLOAT.exp"),
            program == "unused",
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
/// not negative) but not computed, so a step whose result discards it by the short-circuit of
/// `false andBool` (`unused`) ends in the one result that does not hold it, with no definedness
/// condition over it. The branch of a decided `#if` (`branch`) is never evaluated, so its
/// definedness stays the open obligation `\ceil(2 ^Int i(2^24))` (showing it defined needs `i`'s
/// value), still one result. A step whose result holds such a value (`used`), or whose rules
/// branch on a condition over a `<<Int` one the solver cannot decide (`shl`), halts the run at
/// that step with the unsupported-hook reason naming the bound.
#[cfg(feature = "z3-inference")]
#[test]
fn the_run_driver_neither_branches_nor_ends_on_a_result_above_the_size_bound() {
    for (program, value, ceils) in [
        (
            "unused",
            r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("false"))"#,
            0,
        ),
        (
            "branch",
            r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7"))"#,
            1,
        ),
    ] {
        let compiled = compile(SIZE_BOUND, "BOUND", "BOUND", "Pgm", program);
        let output = run_driver(&compiled, "BOUND", 10, None).unwrap();
        assert_eq!(output.exit_code, 0, "{program}");
        let result = Printer::compact().print_pattern(&output.pattern.to_pattern());
        assert!(
            result.contains(value)
                && result.matches(r"\ceil").count() == ceils
                && !result.contains(r"\or"),
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

/// A rule `residual => done(?N)` with `ensures ?N >Int 0` has a result for every instance it
/// applies to, since some `?N` is positive: the instances it leaves without one (`not exists ?N.
/// ?N >Int 0`) are none, so neither strategy reports a leaf for them. The run ends in the one
/// stuck `done(?N)`, under `?N >Int 0` and with what the rule wrote in the stream buffer, which
/// is also the one result of `krun`'s run driver.
#[cfg(feature = "z3-inference")]
#[test]
fn an_ensures_some_value_satisfies_leaves_no_undefined_instances() {
    use k_rust::backend::ExecutionStrategy;

    let source = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/captured-output/test.k"),
    )
    .unwrap();
    let compiled = compile_bound(
        &source,
        "CAPTURED-OUTPUT",
        "CAPTURED-OUTPUT-SYNTAX",
        "Pgm",
        "residual",
        &[("STDIN", "\"\""), ("IO", "\"off\"")],
    );
    let stuck = regex::Regex::new(
        r#"Lbldone'[^(]*\(Ex-hVar'Ques'N-b0:SortInt\{\}\).*\\dv\{SortString\{\}\}\("residual"\).*Lbl'Unds-GT-'Int'Unds'\{\}\(Ex-hVar'Ques'N-b0:SortInt\{\}, \\dv\{SortInt\{\}\}\("0"\)\)"#,
    )
    .unwrap();
    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        let mut backend =
            Backend::new(&compiled.kore, "CAPTURED-OUTPUT", BackendOptions::default()).unwrap();
        let result = backend
            .execute(ExecuteRequest {
                strategy,
                ..ExecuteRequest::new(compiled.initial.clone())
            })
            .unwrap();
        let leaves = result
            .leaves
            .iter()
            .map(|leaf| (leaf.depth, leaf.reason))
            .collect::<Vec<_>>();
        assert_eq!(leaves, [(2, HaltReasonOutput::Stuck)], "{strategy:?}");
        let [state] = text(&result).try_into().unwrap();
        assert!(stuck.is_match(&state), "{strategy:?}: {state}");
    }
    let output = run_driver(&compiled, "CAPTURED-OUTPUT", u64::MAX, None).unwrap();
    let result = Printer::compact().print_pattern(&output.pattern.to_pattern());
    assert!(
        stuck.is_match(&result) && !result.contains(r"\or"),
        "{result}"
    );
}

/// A definition with a `multiplicity="*"` cell `<r>` of collection type `COLLECTION`, and pairs
/// of commands that read one instance written as a cell (`get`, `anyP`) and as an alias of that
/// cell (`getA`, `anyPA`), or that read or remove one instance written as a cell (`rd`, `drop`)
/// and as a left-side variable of the cell sort in `<rs>` (`rdV`, `dropV`), or that look for a
/// given instance held by a variable as itself (`has`) and as the variable of an alias
/// (`hasA`). `mk` adds an instance written as a cell, `put` one held by a variable.
const ALIASED_INSTANCES: &str = r#"
module TEST-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= mk(Int, Int) | put(Int, Int) | get(Int) | getA(Int) | getK(Int) | anyP() | anyPA()
               | rd() | rdV() | drop() | dropV() | has(Int, Int) | hasA(Int, Int)
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT
  imports LIST
  configuration <T> <k> $PGM:Pgm </k> <rs> <r multiplicity="*" type="COLLECTION"> <rid> 0 </rid> <v> 0 </v> </r> </rs> <out> .List </out> </T>

  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> mk(I, V) => .K ... </k> <rs> (.Bag => <r> <rid> I </rid> <v> V </v> </r>) ... </rs>
  syntax KItem ::= putR(RCell)
  rule <k> put(I, V) => putR(<r> <rid> I </rid> <v> V </v> </r>) ... </k>
  rule <k> putR(R) => .K ... </k> <rs> (.Bag => R) ... </rs>

  rule <k> get(I) => .K ... </k> <r> <rid> I </rid> <v> V </v> </r> <out> ... .List => ListItem(V) </out>
  rule <k> getA(I) => .K ... </k> (<r> <rid> I </rid> <v> V </v> </r> #as _R) <out> ... .List => ListItem(V) </out>
  rule <k> getK(I) => .K ... </k> (<r> (<rid> I </rid> #as _K) <v> V </v> </r> #as _R) <out> ... .List => ListItem(V) </out>
  rule <k> anyP() => .K ... </k> <r> <rid> I </rid> ... </r> <out> ... .List => ListItem(I) </out>
  rule <k> anyPA() => .K ... </k> (<r> <rid> I </rid> ... </r> #as _R) <out> ... .List => ListItem(I) </out>

  syntax Int ::= ridOf(RCell) [function] | vOf(RCell) [function]
  rule ridOf(<r> <rid> I </rid> ... </r>) => I
  rule vOf(<r> <v> V </v> ... </r>) => V
  rule <k> rd() => .K ... </k> <rs> <r> <rid> I </rid> <v> V </v> </r> ... </rs> <out> ... .List => ListItem(I) ListItem(V) </out>
  rule <k> rdV() => .K ... </k> <rs> R:RCell ... </rs> <out> ... .List => ListItem(ridOf(R)) ListItem(vOf(R)) </out>
  rule <k> drop() => .K ... </k> <rs> (<r> <rid> _ </rid> <v> _ </v> </r> => .Bag) ... </rs>
  rule <k> dropV() => .K ... </k> <rs> (_R:RCell => .Bag) ... </rs>

  syntax KItem ::= hasR(RCell) | hasAR(RCell)
  rule <k> has(I, V) => hasR(<r> <rid> I </rid> <v> V </v> </r>) ... </k>
  rule <k> hasA(I, V) => hasAR(<r> <rid> I </rid> <v> V </v> </r>) ... </k>
  rule <k> hasR(R) => .K ... </k> <rs> R ... </rs> <out> ... .List => ListItem(ridOf(R)) </out>
  rule <k> hasAR(R) => .K ... </k> (<r> <rid> I </rid> ... </r> #as R) <out> ... .List => ListItem(I) </out>
endmodule
"#;

/// [`ALIASED_INSTANCES`] with `collection` as its instances' `type`, loaded and compiled.
fn compile_aliased_instances(collection: &str) -> (LoadedDefinition, CompiledKoreArtifacts) {
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
    (loaded, artifacts)
}

/// What a program ends in on [`ALIASED_INSTANCES`] for `collection`: the leaves (or the error)
/// of its run and the final states of its search, each with the aliased and variable commands
/// renamed to their written-cell partners.
fn aliased_instance_outcomes(collection: &str, programs: &[&str]) -> Vec<(String, Vec<String>)> {
    let (loaded, artifacts) = compile_aliased_instances(collection);
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let rename = |text: String| {
        text.replace("LblgetA'", "Lblget'")
            .replace("LblgetK'", "Lblget'")
            .replace("LblanyPA'", "LblanyP'")
            .replace("LblrdV'", "Lblrd'")
            .replace("LbldropV'", "Lbldrop'")
            .replace("LblhasA'", "Lblhas'")
            .replace("LblhasAR'", "LblhasR'")
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
        ("mk(1,10) ; has(1,10)", "mk(1,10) ; hasA(1,10)"),
        (&format!("{three}has(2,20)"), &format!("{three}hasA(2,20)")),
        (&format!("{three}has(2,30)"), &format!("{three}hasA(2,30)")),
        (&format!("{three}anyP()"), &format!("{three}anyPA()")),
    ];
    let programs = pairs
        .iter()
        .flat_map(|(cell, alias)| [*cell, *alias])
        .collect::<Vec<_>>();
    for collection in ["Map", "Set", "List"] {
        let outcomes = aliased_instance_outcomes(collection, &programs);
        for ((cell, alias), outcome) in pairs.iter().zip(outcomes.chunks(2)) {
            assert_eq!(outcome[0], outcome[1], "{collection}: {cell} / {alias}");
        }
        // Not vacuous: two reads of the instance added last complete, and a search finds an
        // instance (each of the three in a Map or a Set, the first in a List).
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
        let instances = if collection == "List" { 1 } else { 3 };
        assert_eq!(finals.len(), instances, "{collection}: {finals:?}");
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

/// An alias inside an instance's pattern, `(<rid> I </rid> #as _K)` in `getK`'s aliased
/// instance, denotes the key cell its pattern matches, so `getK` applies exactly where `get`
/// applies and ends in the same configuration: on no instance (stuck), on one, and on three
/// (each read completes, and a search finds the one final state). In a Map that key cell is the
/// key of the instance's item, which the match seeks as the pattern it aliases.
#[test]
fn an_alias_inside_a_collection_cell_instance_matches_what_its_pattern_matches() {
    let three = "mk(1,10) ; mk(2,20) ; mk(3,30) ; ";
    let pairs = [
        ("get(1)", "getK(1)"),
        ("mk(1,10) ; get(1)", "mk(1,10) ; getK(1)"),
        ("mk(1,10) ; get(2)", "mk(1,10) ; getK(2)"),
        (
            &format!("{three}get(2) ; get(3) ; get(2)"),
            &format!("{three}getK(2) ; getK(3) ; getK(2)"),
        ),
        (&format!("{three}get(1)"), &format!("{three}getK(1)")),
        (&format!("{three}get(4)"), &format!("{three}getK(4)")),
        (
            &format!("{three}get(3) ; get(3)"),
            &format!("{three}getK(3) ; getK(3)"),
        ),
    ];
    let programs = pairs
        .iter()
        .flat_map(|(cell, alias)| [*cell, *alias])
        .collect::<Vec<_>>();
    for collection in ["Map", "Set", "List"] {
        let outcomes = aliased_instance_outcomes(collection, &programs);
        for ((cell, alias), outcome) in pairs.iter().zip(outcomes.chunks(2)) {
            assert_eq!(outcome[0], outcome[1], "{collection}: {cell} / {alias}");
        }
        // Not vacuous: among three instances the reads complete (in a List, where `get` reads the
        // instance at the front, the one `mk` added last), `<out>` holds a value read, and the
        // search ends in that one state.
        let index = if collection == "List" { 13 } else { 7 };
        let (run, finals) = &outcomes[index];
        assert!(
            run.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())") && !run.contains("error"),
            "{collection}: {run}"
        );
        let read = r#"LblListItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("30")))"#;
        assert!(run.contains(read), "{collection}: {run}");
        assert_eq!(finals.len(), 1, "{collection}: {finals:?}");
        assert!(
            outcomes.iter().all(|(run, _)| !run.contains(r"\and{")),
            "{collection}: an alias left in a configuration"
        );
    }
}

/// A variable of a cell's sort stands for one instance of the cell, so a rule that reads or
/// removes an instance through a left-side variable `R:RCell` in `<rs>` applies exactly where
/// the rule that writes the instance's cells applies, and ends in the same configuration: on no
/// instance (stuck), on one, and on three (in a search, every instance a written cell matches:
/// any of them in a Map or a Set, the first in a List).
#[test]
fn a_left_side_variable_of_a_collection_cell_sort_matches_one_instance() {
    let three = "mk(1,10) ; mk(2,20) ; mk(3,30) ; ";
    let pairs = [
        ("rd()", "rdV()"),
        ("drop()", "dropV()"),
        ("mk(1,10) ; rd()", "mk(1,10) ; rdV()"),
        ("mk(1,10) ; drop()", "mk(1,10) ; dropV()"),
        (&format!("{three}rd()"), &format!("{three}rdV()")),
        (&format!("{three}drop()"), &format!("{three}dropV()")),
        (
            &format!("{three}drop() ; drop() ; rd()"),
            &format!("{three}dropV() ; dropV() ; rdV()"),
        ),
    ];
    let programs = pairs
        .iter()
        .flat_map(|(cell, variable)| [*cell, *variable])
        .collect::<Vec<_>>();
    let done = "Lbl'-LT-'k'-GT-'{}(dotk{}())";
    for collection in ["Map", "Set", "List"] {
        let outcomes = aliased_instance_outcomes(collection, &programs);
        for ((cell, variable), outcome) in pairs.iter().zip(outcomes.chunks(2)) {
            assert_eq!(outcome[0], outcome[1], "{collection}: {cell} / {variable}");
        }
        // Not vacuous: with no instance both are stuck, with one or three both complete, and a
        // search over three instances finds one final state per instance the rule can take.
        for (index, (run, finals)) in outcomes.iter().enumerate() {
            assert!(
                !run.contains("error") && finals.iter().all(|state| !state.contains("error")),
                "{collection}: {}: {run} {finals:?}",
                programs[index]
            );
            assert_eq!(
                run.contains(done),
                index >= 4,
                "{collection}: {}: {run}",
                programs[index]
            );
        }
        let instances = if collection == "List" { 1 } else { 3 };
        for index in [8, 10, 12] {
            assert_eq!(
                outcomes[index].1.len(),
                instances,
                "{collection}: {}: {:?}",
                programs[index],
                outcomes[index].1
            );
        }
    }
}

/// A search pattern is matched against states, so a variable of a `multiplicity="*"` cell's sort
/// written in its collection (`<rs> R:RCell ... </rs>`) stands there for one instance as on a
/// rule's left side: the pattern of one item, keyed in a `Map` by a minted variable. The pattern
/// then matches where the pattern that writes the instance's cells matches, in a `Map`, a `Set`
/// and a `List`, on one instance and on three, with `R` bound to the instance whose cells the
/// written pattern binds.
#[test]
fn a_search_pattern_variable_of_a_collection_cell_sort_matches_one_instance() {
    let written = "<r> <rid> I </rid> <v> V </v> </r>";
    let pairs = [
        (
            "<rs> R:RCell ... </rs>",
            format!("<rs> {written} ... </rs>"),
        ),
        ("<rs> R:RCell </rs>", format!("<rs> {written} </rs>")),
    ];
    let print = |value: &serde_json::Value| {
        Printer::compact().print_pattern(&codec::from_value(value).unwrap())
    };
    for collection in ["Map", "Set", "List"] {
        let source = ALIASED_INSTANCES.replace("COLLECTION", collection);
        for (instances, program) in [(1, "mk(1,10)"), (3, "mk(1,10) ; mk(2,20) ; mk(3,30)")] {
            let compiled = compile(&source, "TEST", "TEST-SYNTAX", "Pgm", program);
            // Each match's state and bindings by variable, and whether the search is complete.
            let search = |contents: &str| {
                let target = compiled.target("TEST", contents);
                let printed = Printer::compact().print_pattern(&target);
                assert!(!printed.contains("RCellMapKey"), "{contents}: {printed}");
                let mut backend =
                    Backend::new(&compiled.kore, "TEST", BackendOptions::default()).unwrap();
                let response = backend
                    .search_pattern(SearchPatternRequest {
                        search_type: SearchTypeArg::Final,
                        ..SearchPatternRequest::new(compiled.initial.clone(), target)
                    })
                    .unwrap();
                let matches = response
                    .matches
                    .iter()
                    .map(|found| {
                        let bindings = found
                            .bindings
                            .iter()
                            .map(|binding| (print(&binding.variable), print(&binding.value)))
                            .collect::<std::collections::BTreeMap<_, _>>();
                        (print(&found.state.state), bindings)
                    })
                    .collect::<Vec<_>>();
                (matches, response.incomplete.is_empty())
            };
            for (variable, cells) in &pairs {
                let context = format!("{collection}, {instances}: {variable}");
                let (by_variable, variable_complete) = search(variable);
                let (by_cells, cells_complete) = search(cells);
                assert_eq!(variable_complete, cells_complete, "{context}");
                assert_eq!(by_variable.len(), by_cells.len(), "{context}");
                for ((state, bindings), (cells_state, cells_bindings)) in
                    by_variable.iter().zip(&by_cells)
                {
                    assert_eq!(state, cells_state, "{context}");
                    let [rid, v] = ["VarI:SortInt{}", "VarV:SortInt{}"]
                        .map(|name| cells_bindings[name].as_str());
                    let instance = format!(
                        "Lbl'-LT-'r'-GT-'{{}}(Lbl'-LT-'rid'-GT-'{{}}({rid}), Lbl'-LT-'v'-GT-'{{}}({v}))"
                    );
                    assert_eq!(bindings["VarR:SortRCell{}"], instance, "{context}");
                }
                // Not vacuous: one instance is matched by both patterns; among three the open
                // pattern matches the front instance of a `List` and each instance of a `Map` or
                // a `Set`, and the closed one nothing.
                let count = match (instances, variable.contains("..."), collection) {
                    (1, _, _) => 1,
                    (3, false, _) => 0,
                    (3, true, "List") => 1,
                    _ => 3,
                };
                assert!(variable_complete, "{context}");
                assert_eq!(by_variable.len(), count, "{context}");
            }
        }
    }
}

/// A search pattern that matches one state in several ways denotes the disjunction of those
/// ways: an instance of the state is an instance of the pattern under any one of the
/// substitutions. With a cell-map or cell-set pattern whose instance cells nothing fixes, each
/// way is a solution of its own, of the one final state: one per instance for one written
/// instance, one per ordered pair of distinct instances for two, and none where no instance
/// fits (a closed pattern of one instance among three, a value no instance holds).
#[test]
fn a_search_pattern_that_matches_a_state_in_several_ways_reports_each_way() {
    let one = "<r> <rid> I </rid> <v> V </v> </r>";
    let two = "<r> <rid> J </rid> <v> W </v> </r>";
    let print = |value: &serde_json::Value| {
        Printer::compact().print_pattern(&codec::from_value(value).unwrap())
    };
    let int = |value: u32| format!("\\dv{{SortInt{{}}}}(\"{value}\")");
    for collection in ["Map", "Set"] {
        let source = ALIASED_INSTANCES.replace("COLLECTION", collection);
        for (instances, program) in [(1, "mk(1,10)"), (3, "mk(1,10) ; mk(2,20) ; mk(3,30)")] {
            let compiled = compile(&source, "TEST", "TEST-SYNTAX", "Pgm", program);
            // Each solution's bindings of `names`, in order, and the final states matched.
            let search = |contents: &str, names: &[&str], max_results: Option<usize>| {
                let target = compiled.target("TEST", contents);
                let mut backend =
                    Backend::new(&compiled.kore, "TEST", BackendOptions::default()).unwrap();
                let response = backend
                    .search_pattern(SearchPatternRequest {
                        search_type: SearchTypeArg::Final,
                        max_results,
                        ..SearchPatternRequest::new(compiled.initial.clone(), target)
                    })
                    .unwrap();
                assert!(
                    response.incomplete.is_empty(),
                    "{collection}, {instances}: {contents}: {:?}",
                    response.incomplete
                );
                let mut solutions = response
                    .matches
                    .iter()
                    .map(|found| {
                        let bindings = found
                            .bindings
                            .iter()
                            .map(|binding| (print(&binding.variable), print(&binding.value)))
                            .collect::<std::collections::BTreeMap<_, _>>();
                        names
                            .iter()
                            .map(|name| bindings[&format!("Var{name}:SortInt{{}}")].clone())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                solutions.sort();
                let states = response
                    .matches
                    .iter()
                    .map(|found| print(&found.state.state))
                    .collect::<std::collections::BTreeSet<_>>();
                (solutions, states)
            };
            let context = format!("{collection}, {instances}");
            let ids = if instances == 1 {
                vec![1]
            } else {
                vec![1, 2, 3]
            };
            // Every instance, as its `I` and `V`.
            let each = ids
                .iter()
                .map(|&id| vec![int(id), int(10 * id)])
                .collect::<Vec<_>>();
            let (open, states) = search(&format!("<rs> {one} ... </rs>"), &["I", "V"], None);
            assert_eq!(open, each, "{context}: open");
            assert_eq!(states.len(), 1, "{context}: {states:?}");
            let (closed, _) = search(&format!("<rs> {one} </rs>"), &["I", "V"], None);
            let expected_closed = if instances == 1 {
                each.clone()
            } else {
                Vec::new()
            };
            assert_eq!(closed, expected_closed, "{context}: closed");
            let (valued, _) = search(
                "<rs> <r> <rid> I </rid> <v> 20 </v> </r> ... </rs>",
                &["I"],
                None,
            );
            let expected_valued = if instances == 1 {
                Vec::new()
            } else {
                vec![vec![int(2)]]
            };
            assert_eq!(valued, expected_valued, "{context}: valued");
            let (pairs, states) = search(&format!("<rs> {one} {two} ... </rs>"), &["I", "J"], None);
            let expected_pairs = ids
                .iter()
                .flat_map(|&left| {
                    ids.iter()
                        .filter(move |&&right| right != left)
                        .map(move |&right| vec![int(left), int(right)])
                })
                .collect::<Vec<_>>();
            assert_eq!(pairs, expected_pairs, "{context}: pairs");
            assert_eq!(
                states.len(),
                usize::from(instances == 3),
                "{context}: {states:?}"
            );
            // A result bound counts solutions, so it selects that many of the ways.
            let (bounded, _) = search(&format!("<rs> {one} ... </rs>"), &["I", "V"], Some(2));
            assert_eq!(bounded.len(), each.len().min(2), "{context}: bounded");
            assert!(
                bounded.iter().all(|way| each.contains(way)),
                "{context}: {bounded:?}"
            );
        }
    }
}

/// A rule that reads an instance through `P #as V` and leaves it in place has `V` on its right
/// side, and in a cell map that item is keyed by its instance's key. `V` is the instance `P`
/// matched, whose key is `P`'s key cell as matched, so the compiled right side holds that key
/// and applies no key function to `V`, which would be evaluated at every application of the
/// rule; an alias inside that key cell (`getK`'s `_K`) stands there for the key cell it matched.
/// A right-side variable that no left-side alias binds (`putR`'s) still needs the key function.
/// That the aliased rules' results are unchanged is
/// `an_alias_of_a_collection_cell_instance_matches_what_the_instance_matches`.
#[test]
fn a_right_side_alias_of_a_map_cell_instance_is_keyed_by_the_key_its_pattern_matched() {
    let (_, artifacts) = compile_aliased_instances("Map");
    let kore = &artifacts.definition_kore;
    // The right side of the one rewrite rule whose left side applies `symbol`.
    let rewrite_of = |symbol: &str| {
        let applied = format!("Lbl{symbol}'LPar");
        let rules = kore
            .split("\n  axiom")
            .filter(|axiom| axiom.contains("\\rewrites{"))
            .map(|axiom| {
                axiom
                    .split_once(",\n      \\and{SortGeneratedTopCell{}}(")
                    .expect("a rewrite rule's right side")
            })
            .filter(|(left, _)| left.contains(&applied))
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), 1, "one rewrite rule for {symbol}");
        rules[0].1.to_owned()
    };
    for symbol in ["getA", "getK", "anyPA", "hasAR"] {
        let right = rewrite_of(symbol);
        assert!(right.contains("LblRCellMapItem{}("), "{symbol}: {right}");
        assert!(!right.contains("LblRCellMapKey{}("), "{symbol}: {right}");
    }
    let right = rewrite_of("getK");
    assert!(
        right.contains("LblRCellMapItem{}(Var'Unds'K:SortRidCell{}, Var'Unds'R:SortRCell{})"),
        "getK: {right}"
    );
    let right = rewrite_of("putR");
    assert!(right.contains("LblRCellMapKey{}("), "putR: {right}");
}

/// The instances of a `type="List"` cell collection keep their order, and a rule states the
/// position of an instance it writes among the items written side by side in one cell body and
/// the rest of the list that the cell's `...` stands for, placed where that `...` is written
/// (`docs/compatibility.md#cells-written-inside-another-cell`). After three `mk` commands, each
/// adding an instance at the front, the list is `3 2 1`:
/// - `get(I)` writes one instance without its parent, which completion builds with the rest after
///   the instance, so it reads the front instance: `get(3)` rewrites, `get(2)` and `get(1)` are
///   stuck;
/// - `last()` writes `<rs> ... <r> .. </r> </rs>` and `dropLast()` writes
///   `<rs> ... (<r> .. </r> => .Bag) </rs>`: the leading `...` is the part of the list before the
///   instance, so they read and remove the back instance, and `mkLast` adds at the back.
///
/// Each program is run, and searched for its final states, which are the run's one leaf. The
/// reference execution differential case `list-cell-positions`
/// (`scripts/reference-differential.toml`) runs the same programs on this fixture; the pinned
/// reference acts at the front for the leading `...`, a recorded divergence.
#[test]
fn a_list_cell_frame_stands_for_the_rest_of_the_list_where_it_is_written() {
    const SOURCE: &str = include_str!("fixtures/reference/execution/list-cell-positions/test.k");
    const MAIN: &str = "LIST-CELL-POSITIONS";
    let run = |program: &str| {
        let compiled = compile(SOURCE, MAIN, "LIST-CELL-POSITIONS-SYNTAX", "Pgm", program);
        let result = execute(&compiled, MAIN, None);
        let states = text(&result);
        assert_eq!(states.len(), 1, "{program}: {states:?}");
        let mut backend = Backend::new(&compiled.kore, MAIN, BackendOptions::default()).unwrap();
        let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
        let finals = backend
            .search_pattern(SearchPatternRequest {
                search_type: SearchTypeArg::Final,
                ..SearchPatternRequest::new(compiled.initial.clone(), target)
            })
            .unwrap()
            .matches
            .iter()
            .map(|found| {
                Printer::compact().print_pattern(&codec::from_value(&found.state.state).unwrap())
            })
            .collect::<Vec<_>>();
        assert_eq!(finals, states, "{program}: search-final");
        (
            (result.leaves[0].reason, result.leaves[0].depth),
            states.into_iter().next().unwrap(),
        )
    };
    let three = "mk(1,10) ; mk(2,20) ; mk(3,30) ; ";
    let empty_k = "Lbl'-LT-'k'-GT-'{}(dotk{}())";
    let int = |value: u32| format!("\\dv{{SortInt{{}}}}(\"{value}\")");
    let item = |value: u32| {
        format!(
            "LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}))",
            int(value)
        )
    };
    let rid = |value: u32| format!("Lbl'-LT-'rid'-GT-'{{}}({})", int(value));
    // The `<out>` cell holds exactly `values`, in order.
    let out = |state: &str, values: &[u32]| {
        let start = state.find("Lbl'-LT-'out'-GT-'").unwrap();
        let cell = &state[start..];
        let positions = values
            .iter()
            .map(|value| cell.find(&item(*value)))
            .collect::<Option<Vec<_>>>();
        positions.is_some_and(|positions| positions.is_sorted())
            && cell.matches("LblListItem{}").count() == values.len()
    };
    // The instances in the `<rs>` cell, front first.
    let ids = |state: &str| {
        let start = state.find("Lbl'-LT-'rs'-GT-'").unwrap();
        let end = state.find("Lbl'-LT-'out'-GT-'").unwrap();
        let mut positions = (0..10)
            .filter_map(|value| state[start..end].find(&rid(value)).map(|at| (at, value)))
            .collect::<Vec<_>>();
        positions.sort();
        positions
            .into_iter()
            .map(|(_, value)| value)
            .collect::<Vec<_>>()
    };

    // Three sequencing steps and three mk steps, then the read.
    let (leaf, front) = run(&format!("{three}get(3)"));
    assert_eq!(leaf, (HaltReasonOutput::Stuck, 7), "{front}");
    assert!(front.contains(empty_k) && out(&front, &[30]), "{front}");
    assert_eq!(ids(&front), [3, 2, 1], "{front}");

    for key in [2, 1] {
        let (leaf, state) = run(&format!("{three}get({key})"));
        assert_eq!(leaf, (HaltReasonOutput::Stuck, 6), "get({key}): {state}");
        assert!(
            !state.contains(empty_k) && state.contains("Lblget'") && out(&state, &[]),
            "get({key}): {state}"
        );
    }

    let (leaf, last) = run(&format!("{three}last()"));
    assert_eq!(leaf, (HaltReasonOutput::Stuck, 7), "{last}");
    assert!(last.contains(empty_k) && out(&last, &[1]), "{last}");
    assert_eq!(ids(&last), [3, 2, 1], "{last}");

    let (leaf, dropped) = run(&format!("{three}dropLast() ; dropLast()"));
    assert_eq!(leaf, (HaltReasonOutput::Stuck, 9), "{dropped}");
    assert!(
        dropped.contains(empty_k) && out(&dropped, &[1, 2]),
        "{dropped}"
    );
    assert_eq!(ids(&dropped), [3], "{dropped}");

    // `mkLast(2,20)` puts `2` behind `1`, so `get(2)`, which reads the front, is stuck on it.
    let (leaf, added) = run("mk(1,10) ; mkLast(2,20) ; get(2)");
    assert_eq!(leaf, (HaltReasonOutput::Stuck, 4), "{added}");
    assert!(
        !added.contains(empty_k) && added.contains("Lblget'") && out(&added, &[]),
        "{added}"
    );
    assert_eq!(ids(&added), [1, 2], "{added}");
    let (leaf, added) = run("mk(1,10) ; mkLast(2,20) ; last()");
    assert_eq!(leaf, (HaltReasonOutput::Stuck, 5), "{added}");
    assert!(added.contains(empty_k) && out(&added, &[2]), "{added}");
}

/// A cell written with `...` on both sides of items of its `type="List"` collection would match
/// them anywhere in the list, between two parts of it the rule does not divide; the rule is
/// rejected with a located error naming the cell, while the same items with the `...` on one side,
/// and `...` on both sides of a cell holding no item of the list, compile.
#[test]
fn a_list_cell_frame_written_on_both_sides_of_its_items_is_rejected() {
    const SOURCE: &str = include_str!("fixtures/reference/execution/list-cell-positions/test.k");
    // The rule, added to the main module (the source's last).
    let with_rule = |rule: &str| {
        let end = SOURCE.rfind("endmodule").unwrap();
        format!("{}  {rule}\n{}", &SOURCE[..end], &SOURCE[end..])
    };
    let compile_rule = |rule: &str| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let source = with_rule(rule);
        let loaded = load_with_options(
            ResolvedSource::new("test.k", &source),
            "LIST-CELL-POSITIONS",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                ..CompilationBackend::Rust.load_options()
            },
        )
        .unwrap();
        compile_loaded_definition(&loaded, CompileOptions::default()).map(|_| ())
    };
    let rule_line =
        u32::try_from(SOURCE[..SOURCE.rfind("endmodule").unwrap()].lines().count()).unwrap() + 1;
    for rule in [
        "rule <k> last() => .K ... </k> <rs> ... <r> <rid> I </rid> ... </r> ... </rs>",
        "rule <k> mkLast(I, V) => .K ... </k> <rs> ... (.Bag => <r> <rid> I </rid> <v> V </v> </r>) ... </rs>",
    ] {
        let error = compile_rule(rule).expect_err(rule);
        let [diagnostic] = error.diagnostics.as_slice() else {
            panic!("{rule}: {error}");
        };
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidCellConcretization,
            "{rule}"
        );
        assert_eq!(diagnostic.source.as_deref(), Some("test.k"), "{rule}");
        assert_eq!(
            diagnostic.location.map(|location| location.start_line),
            Some(rule_line),
            "{rule}"
        );
        assert!(
            diagnostic
                .message
                .contains("<rs> is written with ... on both sides")
                && diagnostic.message.contains("<r> cells")
                && diagnostic.message.contains("one of its ends"),
            "{rule}: {}",
            diagnostic.message
        );
    }
    for rule in [
        "rule <k> last() => .K ... </k> <rs> <r> <rid> I </rid> ... </r> ... </rs>",
        "rule <T> ... <k> last() => .K ... </k> ... </T>",
    ] {
        compile_rule(rule).unwrap_or_else(|error| panic!("{rule}: {error}"));
    }
}

/// A definition whose rules write a variable beside the instances of a `type="List"` cell
/// collection: `mk` adds an instance at the front, and every other command writes `B` where the
/// part of the list it stands for is.
const LIST_CELL_VARIABLES: &str = r#"
module LIST-CELL-VARIABLES-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= mk(Int) | last() | first() | lastUntyped() | dropLast() | mkLast(Int) | ends()
               | rotate() | probe()
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module LIST-CELL-VARIABLES
  imports LIST-CELL-VARIABLES-SYNTAX
  imports INT
  imports LIST
  configuration
    <T>
      <k> $PGM:Pgm </k>
      <rs> <r multiplicity="*" type="List"> <rid> 0 </rid> </r> </rs>
      <out> .List </out>
    </T>

  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> mk(I) => .K ... </k> <rs> (.Bag => <r> <rid> I </rid> </r>) ... </rs>
  rule <k> last() => .K ... </k> <rs> B:Bag <r> <rid> I </rid> </r> </rs> <out> ... .List => ListItem(I) </out>
  rule <k> first() => .K ... </k> <rs> <r> <rid> I </rid> </r> B:Bag </rs> <out> ... .List => ListItem(I) </out>
  rule <k> lastUntyped() => .K ... </k> <rs> B <r> <rid> I </rid> </r> </rs> <out> ... .List => ListItem(I) </out>
  rule <k> dropLast() => .K ... </k> <rs> B:Bag (<r> <rid> I </rid> </r> => .Bag) </rs> <out> ... .List => ListItem(I) </out>
  rule <k> mkLast(I) => .K ... </k> <rs> B:Bag (.Bag => <r> <rid> I </rid> </r>) </rs>
  rule <k> ends() => .K ... </k> <rs> <r> <rid> I </rid> </r> B:Bag <r> <rid> J </rid> </r> </rs> <out> ... .List => ListItem(I) ListItem(J) </out>
  rule <k> rotate() => .K ... </k> <rs> (<r> <rid> I </rid> </r> B:Bag => B:Bag <r> <rid> I </rid> </r>) </rs>
endmodule
"#;

/// A variable written in a cell body beside instances of a `type="List"` collection (of `Bag`,
/// or of no sort) stands for the part of the list between the items written before it and those
/// written after it (`docs/compatibility.md#cells-written-inside-another-cell`). After three `mk`
/// commands the list is `3 2 1`: `last`, `lastUntyped` and `dropLast` write the variable before
/// the instance, so they read and remove the back; `first` writes it after, and reads the front;
/// `mkLast` adds at the back; `ends` writes it between two instances, which are the front and
/// the back; `rotate` moves the front instance behind the rest. Each program is run, and searched
/// for its final states, which are the run's one leaf.
#[test]
fn a_list_cell_variable_stands_for_the_part_of_the_list_where_it_is_written() {
    const MAIN: &str = "LIST-CELL-VARIABLES";
    let run = |program: &str| {
        let compiled = compile(
            LIST_CELL_VARIABLES,
            MAIN,
            "LIST-CELL-VARIABLES-SYNTAX",
            "Pgm",
            program,
        );
        let result = execute(&compiled, MAIN, None);
        let states = text(&result);
        assert_eq!(states.len(), 1, "{program}: {states:?}");
        assert_eq!(
            result.leaves[0].reason,
            HaltReasonOutput::Stuck,
            "{program}: {states:?}"
        );
        let mut backend = Backend::new(&compiled.kore, MAIN, BackendOptions::default()).unwrap();
        let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
        let finals = backend
            .search_pattern(SearchPatternRequest {
                search_type: SearchTypeArg::Final,
                ..SearchPatternRequest::new(compiled.initial.clone(), target)
            })
            .unwrap()
            .matches
            .iter()
            .map(|found| {
                Printer::compact().print_pattern(&codec::from_value(&found.state.state).unwrap())
            })
            .collect::<Vec<_>>();
        assert_eq!(finals, states, "{program}: search-final");
        let state = states.into_iter().next().unwrap();
        assert!(
            state.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())"),
            "{program}: {state}"
        );
        state
    };
    let int = |value: u32| format!("\\dv{{SortInt{{}}}}(\"{value}\")");
    // The values in the `<out>` cell, in order.
    let out = |state: &str| {
        let cell = &state[state.find("Lbl'-LT-'out'-GT-'").unwrap()..];
        let mut positions = (0..10)
            .flat_map(|value| {
                let item = format!(
                    "LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}))",
                    int(value)
                );
                cell.match_indices(&item)
                    .map(|(at, _)| (at, value))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        positions.sort_unstable();
        positions
            .into_iter()
            .map(|(_, value)| value)
            .collect::<Vec<_>>()
    };
    // The instances in the `<rs>` cell, front first.
    let ids = |state: &str| {
        let start = state.find("Lbl'-LT-'rs'-GT-'").unwrap();
        let end = state.find("Lbl'-LT-'out'-GT-'").unwrap();
        let mut positions = (0..10)
            .flat_map(|value| {
                state[start..end]
                    .match_indices(&format!("Lbl'-LT-'rid'-GT-'{{}}({})", int(value)))
                    .map(|(at, _)| (at, value))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        positions.sort_unstable();
        positions
            .into_iter()
            .map(|(_, value)| value)
            .collect::<Vec<_>>()
    };

    let three = "mk(1) ; mk(2) ; mk(3) ; ";
    for (program, read, left) in [
        ("last()", vec![1], vec![3, 2, 1]),
        ("lastUntyped()", vec![1], vec![3, 2, 1]),
        ("first()", vec![3], vec![3, 2, 1]),
        ("dropLast() ; dropLast()", vec![1, 2], vec![3]),
        ("mkLast(4) ; last()", vec![4], vec![3, 2, 1, 4]),
        ("ends()", vec![3, 1], vec![3, 2, 1]),
        ("rotate() ; last()", vec![3], vec![2, 1, 3]),
    ] {
        let state = run(&format!("{three}{program}"));
        assert_eq!(out(&state), read, "{program}: {state}");
        assert_eq!(ids(&state), left, "{program}: {state}");
    }
}

/// The list a rule matches is divided by the items written in it around at most one part that a
/// term stands for; a variable beside another variable or beside the frame `...` (on either side
/// of the items, or with none) would divide the rest of the list between two parts in a way the
/// rule does not state. Such a rule is rejected with a located error naming the cell and both
/// terms; the same variables on the right side of a rewrite, which builds the list, compile.
#[test]
fn a_list_cell_variable_beside_another_part_of_the_list_is_rejected() {
    let with_rule = |rule: &str| {
        let end = LIST_CELL_VARIABLES.rfind("endmodule").unwrap();
        format!(
            "{}  {rule}\n{}",
            &LIST_CELL_VARIABLES[..end],
            &LIST_CELL_VARIABLES[end..]
        )
    };
    let compile_rule = |rule: &str| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let source = with_rule(rule);
        let loaded = load_with_options(
            ResolvedSource::new("test.k", &source),
            "LIST-CELL-VARIABLES",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                ..CompilationBackend::Rust.load_options()
            },
        )
        .unwrap();
        compile_loaded_definition(&loaded, CompileOptions::default()).map(|_| ())
    };
    let rule_line = u32::try_from(
        LIST_CELL_VARIABLES[..LIST_CELL_VARIABLES.rfind("endmodule").unwrap()]
            .lines()
            .count(),
    )
    .unwrap()
        + 1;
    for (rule, parts) in [
        (
            "rule <k> probe() => .K ... </k> <rs> B:Bag (<r> <rid> I </rid> </r> => .Bag) C:Bag </rs>",
            "`B` and `C`",
        ),
        (
            "rule <k> probe() => .K ... </k> <rs> B:Bag C:Bag </rs>",
            "`B` and `C`",
        ),
        (
            "rule <k> probe() => .K ... </k> <rs> B:Bag <r> <rid> I </rid> </r> ... </rs>",
            "`B` and `...`",
        ),
        (
            "rule <k> probe() => .K ... </k> <rs> ... <r> <rid> I </rid> </r> B:Bag </rs>",
            "`...` and `B`",
        ),
        (
            "rule <k> probe() => .K ... </k> <rs> B:Bag ... </rs>",
            "`B` and `...`",
        ),
    ] {
        let error = compile_rule(rule).expect_err(rule);
        let [diagnostic] = error.diagnostics.as_slice() else {
            panic!("{rule}: {error}");
        };
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidCellConcretization,
            "{rule}"
        );
        assert_eq!(diagnostic.source.as_deref(), Some("test.k"), "{rule}");
        assert_eq!(
            diagnostic.location.map(|location| location.start_line),
            Some(rule_line),
            "{rule}"
        );
        assert!(
            diagnostic
                .message
                .starts_with(&format!("The cell <rs> is written with {parts} among the items of its type=\"List\" collection of <r> cells")),
            "{rule}: {}",
            diagnostic.message
        );
    }
    compile_rule(
        "rule <k> probe() => .K ... </k> <rs> (<r> <rid> I </rid> </r> B:Bag => B:Bag <r> <rid> I </rid> </r> B:Bag) </rs>",
    )
    .unwrap_or_else(|error| panic!("{error}"));
}

/// A definition whose configurations hold a map with a symbolic rest or a partial `Int`
/// operation, so that some instances of a symbolic initial configuration are undefined, and one
/// rule whose `requires` is partial on a defined configuration.
#[cfg(feature = "z3-inference")]
const UNDEFINED_INSTANCES: &str = r#"
module UD-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports MAP
  syntax Pgm ::= stm(Map) [symbol(stm)] | stl(Map) [symbol(stl)] | sti(Int) [symbol(sti)]
               | stz(Int) [symbol(stz)] | stc(Int, Int) [symbol(stc)]
               | donem(Int) [symbol(donem)] | donei(Int) [symbol(donei)] | zero() [symbol(zero)]
               | pos() [symbol(pos)] | other() [symbol(other)]
endmodule

module UD
  imports UD-SYNTAX
  imports INT
  imports MAP
  imports STRING
  configuration <k> $PGM:Pgm </k>
  rule <k> stm(("a" |-> V:Int) _M) => donem(V) ... </k>
  rule <k> stl(("a" |-> V:Int) _M) => donem(V) ... </k>
  rule <k> stl(_) => other() ... </k> [owise]
  rule <k> sti(I:Int) => donei(I) ... </k>
  rule <k> stz(0) => zero() ... </k>
  rule <k> stc(X, Y) => pos() ... </k> requires X /Int Y >Int 0
endmodule
"#;

/// The initial configuration `<k> PROGRAM </k>` of [`UNDEFINED_INSTANCES`], `program` in KORE.
#[cfg(feature = "z3-inference")]
fn undefined_instances_initial(program: &str) -> Pattern {
    parse_pattern(&format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    ))
    .unwrap()
}

/// A configuration `t ∧ φ` denotes only its defined instances, so where a subterm of the
/// initial configuration is undefined there is no configuration: no rule is stuck on it and no
/// result reports it. `("a" |-> 0) R` is undefined where `"a"` is a key of `R`, and
/// `X /Int Y` where `Y` is 0. Execution (both strategies), a search and `krun`'s run driver
/// report only the defined instances' results, each restricted where the step leaves it over:
/// `stm` has the one result `donem(0)`, with no stuck leaf for the duplicated key; `stl`'s
/// `owise` rule is not given those instances, so no `other()` appears; `sti` has `donei` only,
/// and `stz`'s stuck remainder states `Y` is not 0. Each run names the condition in an
/// `UndefinedInitialInstances` diagnostic. A `requires` undefined on a defined configuration is
/// the rule's own condition: `stc(X, Y)` keeps its stuck remainder, which includes `Y` = 0,
/// and has no such diagnostic.
#[cfg(feature = "z3-inference")]
#[test]
fn an_undefined_instance_of_the_initial_configuration_has_no_result() {
    use k_rust::backend::{BackendDiagnosticOutput, ExecutionStrategy};

    let map = r#"Lbl'Unds'Map'Unds'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortString{}, SortKItem{}}(\dv{SortString{}}("a")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))), VarR:SortMap{})"#;
    let quotient = r#"Lbl'UndsSlsh'Int'Unds'{}(VarX:SortInt{}, VarY:SortInt{})"#;
    let y_is_not_zero = r#"\not{SortGeneratedTopCell{}}(\equals{SortInt{}, SortGeneratedTopCell{}}(VarY:SortInt{}, \dv{SortInt{}}("0")))"#;
    let cases = [
        // (program, the term heads of its results, a constraint every result states, whether
        // the initial configuration has undefined instances)
        (
            format!("Lblstm{{}}({map})"),
            vec!["Lbldonem"],
            "in'Unds'keys",
            true,
        ),
        (
            format!("Lblstl{{}}({map})"),
            vec!["Lbldonem"],
            "in'Unds'keys",
            true,
        ),
        (
            format!("Lblsti{{}}({quotient})"),
            vec!["Lbldonei"],
            y_is_not_zero,
            true,
        ),
        (
            format!("Lblstz{{}}({quotient})"),
            vec!["Lblstz", "Lblzero"],
            "",
            true,
        ),
        (
            "Lblstc{}(VarX:SortInt{}, VarY:SortInt{})".to_owned(),
            vec!["Lblpos", "Lblstc"],
            "",
            false,
        ),
    ];
    let mut compiled = compile(UNDEFINED_INSTANCES, "UD", "UD-SYNTAX", "Pgm", "zero()");
    let heads = |state: &str| {
        let mut heads = [
            "Lbldonem", "Lbldonei", "Lblstm", "Lblstl", "Lblsti", "Lblstz", "Lblstc",
        ]
        .into_iter()
        .chain(["Lblzero", "Lblpos", "Lblother"])
        .filter(|head| state.contains(&format!("{head}{{}}(")))
        .collect::<Vec<_>>();
        heads.sort();
        heads
    };
    for (program, results, stated, undefined) in &cases {
        let initial = undefined_instances_initial(program);
        for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
            let mut backend =
                Backend::new(&compiled.kore, "UD", BackendOptions::default()).unwrap();
            let result = backend
                .execute(ExecuteRequest {
                    strategy,
                    ..ExecuteRequest::new(initial.clone())
                })
                .unwrap();
            let states = text(&result);
            let mut found = states
                .iter()
                .flat_map(|state| heads(state))
                .collect::<Vec<_>>();
            found.sort();
            assert_eq!(&found, results, "{program} {strategy:?}: {states:#?}");
            assert!(
                states.iter().all(|state| state.contains(stated)),
                "{program} {strategy:?}: {states:#?}"
            );
            assert!(
                result
                    .leaves
                    .iter()
                    .all(|leaf| leaf.reason == HaltReasonOutput::Stuck),
                "{program} {strategy:?}"
            );
            for leaf in &result.leaves {
                assert_eq!(
                    leaf.diagnostics.iter().any(|diagnostic| matches!(
                        diagnostic,
                        BackendDiagnosticOutput::UndefinedInitialInstances { .. }
                    )),
                    *undefined,
                    "{program} {strategy:?}: {:?}",
                    leaf.diagnostics
                );
            }
        }
        if *program == format!("Lblstz{{}}({quotient})") {
            let mut backend =
                Backend::new(&compiled.kore, "UD", BackendOptions::default()).unwrap();
            let result = backend
                .execute(ExecuteRequest::new(initial.clone()))
                .unwrap();
            let stuck = text(&result)
                .into_iter()
                .find(|state| state.contains("Lblstz{}("))
                .unwrap();
            assert!(stuck.contains(y_is_not_zero), "{stuck}");
        }
        let mut backend = Backend::new(&compiled.kore, "UD", BackendOptions::default()).unwrap();
        let response = backend
            .search(SearchRequest {
                search_type: SearchTypeArg::Final,
                ..SearchRequest::new(initial.clone())
            })
            .unwrap();
        assert!(response.incomplete.is_empty(), "{:?}", response.incomplete);
        let mut found = response
            .states
            .iter()
            .flat_map(|found| {
                heads(&Printer::compact().print_pattern(&codec::from_value(&found.state).unwrap()))
            })
            .collect::<Vec<_>>();
        found.sort();
        assert_eq!(&found, results, "{program} search");
        compiled.initial = initial;
        let output = run_driver(&compiled, "UD", u64::MAX, None).unwrap();
        let result = Printer::compact().print_pattern(&output.pattern.to_pattern());
        let mut found = heads(&result);
        found.sort();
        // `krun`'s `any` strategy follows one of `stz`'s and `stc`'s two branches.
        assert!(
            !found.is_empty() && found.iter().all(|head| results.contains(head)),
            "{program} krun: {result}"
        );
        assert!(result.contains(stated), "{program} krun: {result}");
    }
}

/// The definedness of `sti(X /Int Y)` is `Y` not 0. When the initial constraints establish it
/// (`Y >Int 0`), the configuration has no undefined instance, so nothing is restricted or named;
/// when they refute it together (`Y *Int Y ==Int 0`, which no single obligation's simplification
/// decides), the configuration has no instance at all: the run ends as one simplified to
/// `\bottom` and a search reports that it started from no configuration, neither naming a
/// condition under which it would be defined.
#[cfg(feature = "z3-inference")]
#[test]
fn constraints_that_settle_the_initial_definedness_leave_no_undefined_instance_to_name() {
    use k_rust::backend::{BackendDiagnosticOutput, ExecutionStrategy};

    let compiled = compile(UNDEFINED_INSTANCES, "UD", "UD-SYNTAX", "Pgm", "zero()");
    let program = r#"Lblsti{}(Lbl'UndsSlsh'Int'Unds'{}(VarX:SortInt{}, VarY:SortInt{}))"#;
    let initial = |condition: &str| {
        parse_pattern(&format!(
            r#"\and{{SortGeneratedTopCell{{}}}}({}, \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(\dv{{SortBool{{}}}}("true"), {condition}))"#,
            Printer::compact().print_pattern(&undefined_instances_initial(program))
        ))
        .unwrap()
    };
    let positive = r#"Lbl'Unds-GT-'Int'Unds'{}(VarY:SortInt{}, \dv{SortInt{}}("0"))"#;
    let square_zero = r#"Lbl'UndsEqlsEqls'Int'Unds'{}(Lbl'UndsStar'Int'Unds'{}(VarY:SortInt{}, VarY:SortInt{}), \dv{SortInt{}}("0"))"#;
    for (condition, heads) in [(positive, vec!["Lbldonei{}("]), (square_zero, vec![])] {
        for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
            let mut backend =
                Backend::new(&compiled.kore, "UD", BackendOptions::default()).unwrap();
            let result = backend
                .execute(ExecuteRequest {
                    strategy,
                    ..ExecuteRequest::new(initial(condition))
                })
                .unwrap();
            let states = text(&result);
            assert!(
                heads
                    .iter()
                    .all(|head| states.iter().any(|state| state.contains(head)))
                    && (heads.is_empty()
                        == result
                            .leaves
                            .iter()
                            .all(|leaf| leaf.reason == HaltReasonOutput::Vacuous)),
                "{condition} {strategy:?}: {states:#?}"
            );
            assert!(
                result
                    .leaves
                    .iter()
                    .all(|leaf| !leaf.diagnostics.iter().any(|diagnostic| matches!(
                        diagnostic,
                        BackendDiagnosticOutput::UndefinedInitialInstances { .. }
                    ))),
                "{condition} {strategy:?}: {:#?}",
                result.leaves
            );
        }
        // A search from no configuration says so, as its empty result alone cannot.
        let mut backend = Backend::new(&compiled.kore, "UD", BackendOptions::default()).unwrap();
        let request = SearchRequest {
            search_type: SearchTypeArg::Final,
            ..SearchRequest::new(initial(condition))
        };
        let states = backend.search(request.clone()).unwrap();
        let paths = backend.search_paths(request).unwrap();
        assert_eq!(
            (
                states.states.is_empty(),
                states.initial_bottom,
                paths.witnesses.is_empty(),
                paths.initial_bottom
            ),
            (
                heads.is_empty(),
                heads.is_empty(),
                heads.is_empty(),
                heads.is_empty()
            ),
            "{condition} search: {states:#?} {paths:#?}"
        );
    }
}

/// The order `keys_list` lists a map's keys in, reached through a rule `requires` (on 1) and a
/// function equation's `requires` (on 2).
const KEYS_LIST_ORDER_IN_CONDITIONS: &str = r#"
module ORDREQ
  imports DOMAINS
  imports COLLECTIONS
  syntax KItem ::= res(List) | cond(Bool) | fres(Int)
  syntax Int ::= f(Map) [function]
  rule f(M) => 1 requires keys_list(M) ==K ListItem(-1) ListItem(10) ListItem(2)
  rule f(_) => 0 [owise]
  configuration <k> $PGM:Int </k>
  rule 0 => res(keys_list(10 |-> 1 2 |-> 2 -1 |-> 3))
  rule 1 => cond(true) requires keys_list(10 |-> 1 2 |-> 2 -1 |-> 3) ==K ListItem(-1) ListItem(10) ListItem(2)
  rule 2 => fres(f(10 |-> 1 2 |-> 2 -1 |-> 3))
endmodule
"#;

/// The facade's `execute` and `search_pattern` are executions: they evaluate every listing in
/// k-rust's documented order (decimal text order for Int keys, -1 10 2), also in the conditions
/// they decide, so a rule `requires` (on 1) and a function equation's `requires` (on 2) that hold
/// in that order are taken.
#[test]
fn backend_execute_and_search_keep_the_order_in_conditions() {
    for (program, expected) in [
        (
            "1",
            r#"Lblcond'LParUndsRParUnds'ORDREQ'Unds'KItem'Unds'Bool{}(\dv{SortBool{}}("true"))"#,
        ),
        (
            "2",
            r#"Lblfres'LParUndsRParUnds'ORDREQ'Unds'KItem'Unds'Int{}(\dv{SortInt{}}("1"))"#,
        ),
    ] {
        let compiled = compile(
            KEYS_LIST_ORDER_IN_CONDITIONS,
            "ORDREQ",
            "ORDREQ",
            "Int",
            program,
        );
        let executed = text(&execute(&compiled, "ORDREQ", None));
        assert!(
            matches!(executed.as_slice(), [state]
                if state.contains(expected) && !state.contains("Lblkeys")),
            "execute {program}: {executed:?}"
        );
        let mut backend =
            Backend::new(&compiled.kore, "ORDREQ", BackendOptions::default()).unwrap();
        let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
        let response = backend
            .search_pattern(SearchPatternRequest {
                search_type: SearchTypeArg::Final,
                ..SearchPatternRequest::new(compiled.initial.clone(), target)
            })
            .unwrap();
        let found = response
            .matches
            .iter()
            .map(|found| {
                Printer::compact().print_pattern(&codec::from_value(&found.state.state).unwrap())
            })
            .collect::<Vec<_>>();
        assert!(
            matches!(found.as_slice(), [state]
                if state.contains(expected) && !state.contains("Lblkeys")),
            "search_pattern {program}: {found:?}"
        );
    }
}

/// Float operations over a binary32 and a binary64 operand, as a result (`div`) and in
/// complementary rule conditions (`pick`).
const MIXED_FLOAT_FORMATS: &str = r#"
module MIXED
  imports DOMAINS
  imports FLOAT
  syntax Pgm ::= div(Float, Float) | pick(Float, Float)
  configuration <k> $PGM:Pgm </k>
  rule div(X, Y) => X /Float Y
  rule pick(X, Y) => true requires X /Float Y >Float 0.0
  rule pick(X, Y) => false requires notBool (X /Float Y >Float 0.0)
endmodule
"#;

/// The facade's `execute`, the route KRS runs programs through, is an execution: a Float
/// operation over a binary32 and a binary64 operand is the exact result rounded to binary64.
#[test]
fn backend_execute_rounds_float_arithmetic_over_two_formats() {
    let compiled = compile(
        MIXED_FLOAT_FORMATS,
        "MIXED",
        "MIXED",
        "Pgm",
        "div(0.1f, 2.0)",
    );
    let executed = text(&execute(&compiled, "MIXED", None));
    assert!(
        matches!(executed.as_slice(), [state]
            if state.contains(r#"\dv{SortFloat{}}("5.0000000745058060e-02p53x11")"#)),
        "{executed:?}"
    );
}

/// The facade's `execute` reports a Float operation of a format the backend does not compute
/// (p113x15) as the capability gap it is, the unsupported-hook halt naming the hook and the
/// format, not as a simplification error; so does an operation over binary64 and p113x15, whose
/// destination format p113x15 contains binary64.
#[test]
fn backend_execute_reports_a_float_format_it_does_not_compute_as_an_unsupported_hook() {
    for program in ["div(1.0p113x15, 3.0p113x15)", "div(1.0, 3.0p113x15)"] {
        let compiled = compile(MIXED_FLOAT_FORMATS, "MIXED", "MIXED", "Pgm", program);
        let result = execute(&compiled, "MIXED", Some(10));
        let [leaf] = result.leaves.as_slice() else {
            panic!("{program}: {result:?}");
        };
        assert_eq!(
            leaf.reason,
            HaltReasonOutput::UnsupportedHook,
            "{program}: {result:?}"
        );
        let detail = leaf.detail.as_deref().unwrap_or_default();
        assert!(
            detail.contains("unsupported hook 'FLOAT.div'") && detail.contains("p113x15"),
            "{program}: {detail}"
        );
    }
}

/// The facade's `search_pattern` is an execution too: the condition over the mixed quotient is
/// decided, so the search reaches `true` and nothing else.
#[test]
fn backend_search_rounds_float_arithmetic_over_two_formats() {
    let compiled = compile(
        MIXED_FLOAT_FORMATS,
        "MIXED",
        "MIXED",
        "Pgm",
        "pick(1.0f, 2.0)",
    );
    let mut backend = Backend::new(&compiled.kore, "MIXED", BackendOptions::default()).unwrap();
    let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
    let response = backend
        .search_pattern(SearchPatternRequest {
            search_type: SearchTypeArg::Final,
            ..SearchPatternRequest::new(compiled.initial.clone(), target)
        })
        .unwrap();
    let found = response
        .matches
        .iter()
        .map(|found| {
            Printer::compact().print_pattern(&codec::from_value(&found.state.state).unwrap())
        })
        .collect::<Vec<_>>();
    assert!(
        matches!(found.as_slice(), [state]
            if state.contains(r#"\dv{SortBool{}}("true")"#) && !state.contains("Lblpick")),
        "{found:?}"
    );
}

/// The facade's proof routes evaluate only consequences of the definition, also when the caller
/// runs them inside an `Execution` scope: `simplify` leaves `keys_list` of a map of three keys
/// unevaluated there, while `execute` in the same definition lists them.
#[test]
fn backend_simplify_stays_a_proof_route_inside_an_execution_scope() {
    use k_rust::backend::PatternRequest;
    use k_rust_backend::evaluation::{EvaluationMode, with_evaluation};
    let compiled = compile(
        KEYS_LIST_ORDER_IN_CONDITIONS,
        "ORDREQ",
        "ORDREQ",
        "Int",
        "0",
    );
    let item = |key: i64, value: i64| {
        format!(
            r#"Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{key}")), inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}")))"#
        )
    };
    let listing = parse_pattern(&format!(
        "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{{}}(Lbl'Unds'Map'Unds'{{}}({}, Lbl'Unds'Map'Unds'{{}}({}, {})))",
        item(10, 1),
        item(2, 2),
        item(-1, 3)
    ))
    .unwrap();
    let mut backend = Backend::new(&compiled.kore, "ORDREQ", BackendOptions::default()).unwrap();
    let simplified = with_evaluation(EvaluationMode::Execution, || {
        backend.simplify(PatternRequest::new(listing)).unwrap()
    });
    assert!(simplified.to_string().contains("Lblkeys"), "{simplified}");
    let executed = text(&execute(&compiled, "ORDREQ", None));
    assert!(
        matches!(executed.as_slice(), [state] if !state.contains("Lblkeys")),
        "{executed:?}"
    );
}

/// `kore-match-disjunction`'s `Backend::match_patterns` is a proof route: a target whose condition
/// states that `keys_list` of a map lists `-1 10 2` is not decided by k-rust's order, also inside
/// a caller's `Execution` scope, so matching it against `0` keeps that condition as a constraint.
#[test]
fn backend_match_patterns_stays_a_proof_route_inside_an_execution_scope() {
    use k_rust_backend::evaluation::{EvaluationMode, with_evaluation};
    let compiled = compile(
        KEYS_LIST_ORDER_IN_CONDITIONS,
        "ORDREQ",
        "ORDREQ",
        "Int",
        "0",
    );
    let int =
        |value: i64| format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#);
    let item = |key: i64, value: i64| {
        format!("Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {})", int(key), int(value))
    };
    let listing = parse_pattern(&format!(
        "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{{}}(Lbl'Unds'Map'Unds'{{}}({}, Lbl'Unds'Map'Unds'{{}}({}, {})))",
        item(10, 1),
        item(2, 2),
        item(-1, 3)
    ))
    .unwrap();
    let list = parse_pattern(&format!(
        "Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({}), Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({}), LblListItem{{}}({})))",
        int(-1),
        int(10),
        int(2)
    ))
    .unwrap();
    let mut backend = Backend::new(&compiled.kore, "ORDREQ", BackendOptions::default()).unwrap();
    let internalize = |backend: &mut Backend, pattern: &Pattern| {
        backend
            .with_solver(None, |definition, _| {
                definition
                    .verify_standalone_pattern(pattern, &[])
                    .and_then(|admitted| admitted.internalize_pattern())
                    .map_err(|error| k_rust::backend::BackendError(error.to_string()))
            })
            .unwrap()
    };
    // `X` where `keys_list` of the map lists `-1 10 2`: the condition the match decides.
    let condition = parse_pattern(&format!(
        r#"\and{{SortInt{{}}}}(X:SortInt{{}}, \equals{{SortList{{}}, SortInt{{}}}}({}, {}))"#,
        Printer::compact().print_pattern(&listing),
        Printer::compact().print_pattern(&list)
    ))
    .unwrap();
    let target = internalize(&mut backend, &condition);
    let subject = internalize(
        &mut backend,
        &parse_pattern(r#"\dv{SortInt{}}("0")"#).unwrap(),
    );
    let matched = with_evaluation(EvaluationMode::Execution, || {
        backend.match_patterns(None, &target, std::slice::from_ref(&subject))
    });
    let proof = backend.match_patterns(None, &target, std::slice::from_ref(&subject));
    // The condition stays a constraint of the match: its order is not read.
    let matched = matched.unwrap();
    assert!(
        matches!(matched.as_slice(), [found] if !found.constraints.is_empty()),
        "{matched:?}"
    );
    assert_eq!(matched, proof.unwrap());
}

/// Whether the one leaf of a run of `program` ends normally (stuck) at depth 1 with `<k>` holding
/// `okb(expected)`, and no leaf left a `KEQUAL.eq` application unevaluated.
fn assert_ends_in_okb(source: &str, main: &str, program: &str, expected: bool) {
    let compiled = compile(source, main, &format!("{main}-SYNTAX"), "Stmt", program);
    let result = execute(&compiled, main, Some(3));
    let [leaf] = result.leaves.as_slice() else {
        panic!("{program}: {result:#?}");
    };
    assert_eq!(
        (&leaf.reason, leaf.depth),
        (&HaltReasonOutput::Stuck, 1),
        "{program}: {leaf:#?}"
    );
    let [state] = text(&result).try_into().unwrap();
    assert!(
        state.contains(&format!(r#"Lblokb{{}}(\dv{{SortBool{{}}}}("{expected}"))"#)),
        "{program}: {state}"
    );
    assert_no_unevaluated_kequal(program, &result);
}

fn assert_no_unevaluated_kequal(program: &str, result: &ExecutionResult) {
    for leaf in &result.leaves {
        assert!(
            !leaf.diagnostics.iter().any(|diagnostic| matches!(
                diagnostic,
                BackendDiagnosticOutput::UnsupportedHookUnevaluated { hook, .. }
                    if hook == "KEQUAL.eq"
            )),
            "{program}: {:#?}",
            leaf.diagnostics
        );
    }
}

const K_EQUALITY: &str = r#"
module KEQ-SYNTAX
  syntax Stmt ::= "dotdot" | "fundot" | "abab" | "aseqa" | "kitem" | "ite"
                | "dota" | "adot" | "dotmap" | "ab" | "kitemne" | "injkitem" | "abac" | "dotdotne"
                | "req" | "reqab"
endmodule
module KEQ
  imports KEQ-SYNTAX
  imports K-EQUAL
  imports BOOL
  imports INT
  imports MAP
  configuration <k> $PGM:Stmt </k>
  syntax KItem ::= okb(Bool) [symbol(okb)] | a() | b() | c() | foo(Int) | rq() [symbol(rq)]
  syntax K ::= e() [function, total]
  rule e() => .K
  syntax Foo ::= x()
  rule <k> dotdot => okb(.K ==K .K) ...</k>
  rule <k> fundot => okb(e() ==K .K) ...</k>
  rule <k> abab => okb((a() ~> b()) ==K (a() ~> b())) ...</k>
  rule <k> aseqa => okb((a() ~> .K) ==K a()) ...</k>
  rule <k> kitem => okb(foo(1) ==K foo(1)) ...</k>
  rule <k> ite => okb(#if .K ==K .K #then true #else false #fi) ...</k>
  rule <k> dota => okb(.K ==K a()) ...</k>
  rule <k> adot => okb(a() ==K .K) ...</k>
  rule <k> dotmap => okb(.K ==K .Map) ...</k>
  rule <k> ab => okb(a() ==K b()) ...</k>
  rule <k> kitemne => okb(foo(1) ==K foo(2)) ...</k>
  rule <k> injkitem => okb(x() ==K a()) ...</k>
  rule <k> abac => okb((a() ~> b()) ==K (a() ~> c())) ...</k>
  rule <k> dotdotne => okb(.K =/=K .K) ...</k>
  rule <k> req => rq() ...</k> requires .K ==K .K
  rule <k> reqab => rq() ...</k> requires a() ==K b()
endmodule
"#;

/// `K` is generated by the free constructors `.K` and `~>` over `KItem`, so `==K` and `=/=K`
/// have a value on every pair of constructor-like `K` operands, not only on two one-item
/// sequences of injected items: the empty sequence, sequences of several items and items of
/// sort `KItem` itself are compared as whole values, wherever the hook is evaluated (a rule's
/// right-hand side, a function result, an `#if` condition).
#[test]
fn k_equality_gives_a_value_on_every_k_sequence_shape() {
    for (program, expected) in [
        ("dotdot", true),
        ("fundot", true),
        ("abab", true),
        ("aseqa", true),
        ("kitem", true),
        ("ite", true),
        ("dota", false),
        ("adot", false),
        ("dotmap", false),
        ("ab", false),
        ("kitemne", false),
        ("injkitem", false),
        ("abac", false),
        ("dotdotne", false),
    ] {
        assert_ends_in_okb(K_EQUALITY, "KEQ", program, expected);
    }
}

/// A rule condition built from `==K` is decided by the hook itself: `.K ==K .K` applies the
/// rule, `a() ==K b()` leaves it unapplied, and neither leaves the hook unevaluated.
#[test]
fn k_equality_in_a_rule_condition_is_decided_by_the_hook() {
    for (program, applies) in [("req", true), ("reqab", false)] {
        let compiled = compile(K_EQUALITY, "KEQ", "KEQ-SYNTAX", "Stmt", program);
        let result = execute(&compiled, "KEQ", Some(3));
        let [leaf] = result.leaves.as_slice() else {
            panic!("{program}: {result:#?}");
        };
        assert_eq!(
            (&leaf.reason, leaf.depth),
            (&HaltReasonOutput::Stuck, u64::from(applies)),
            "{program}: {leaf:#?}"
        );
        let [state] = text(&result).try_into().unwrap();
        assert_eq!(state.contains("Lblrq{}()"), applies, "{program}: {state}");
        assert_no_unevaluated_kequal(program, &result);
    }
}

/// Two one-item sequences whose items are injected from sorts that may share values (`S1` and
/// `S2` both above `S3`) are compared by their items: `g1(1)` and `g2(1)` are distinct normal
/// forms, so they differ, while `g1(0)` and `g2(0)` both reduce to `c()`.
#[test]
fn k_equality_of_items_from_sorts_sharing_a_subsort_is_kept() {
    const SOURCE: &str = r#"
module KEQ-ANYW-SYNTAX
  syntax Stmt ::= "anyw" | "anywsame"
endmodule
module KEQ-ANYW
  imports KEQ-ANYW-SYNTAX
  imports K-EQUAL
  imports BOOL
  imports INT
  configuration <k> $PGM:Stmt </k>
  syntax KItem ::= okb(Bool) [symbol(okb)]
  syntax S3 ::= c()
  syntax S1 ::= S3 | g1(Int)
  syntax S2 ::= S3 | g2(Int)
  rule g1(0) => c() [anywhere]
  rule g2(0) => c() [anywhere]
  rule <k> anyw => okb(g1(1) ==K g2(1)) ...</k>
  rule <k> anywsame => okb(g1(0) ==K g2(0)) ...</k>
endmodule
"#;
    assert_ends_in_okb(SOURCE, "KEQ-ANYW", "anyw", false);
    assert_ends_in_okb(SOURCE, "KEQ-ANYW", "anywsame", true);
}

/// A user function hooked `KEQUAL.eq` on a sort other than `K` compares its operands as values
/// of that sort: constructor terms by freeness and injection, `Int` operands as numbers.
#[test]
fn a_user_symbol_hooked_kequal_is_decided_on_its_own_sort() {
    const SOURCE: &str = r#"
module KEQ-USER-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "usame" | "udiff" | "usub" | "uint" | "uone"
endmodule
module KEQ-USER
  imports KEQ-USER-SYNTAX
  imports K-EQUAL
  imports BOOL
  imports INT
  configuration <k> $PGM:Stmt </k>
  syntax KItem ::= okb(Bool) [symbol(okb)]
  syntax Bar ::= z()
  syntax Foo ::= Bar | x() | y(Int)
  syntax Bool ::= Foo "eqf" Foo [function, total, hook(KEQUAL.eq)]
  syntax Bool ::= Int "eqi" Int [function, total, hook(KEQUAL.eq)]
  rule <k> usame => okb(y(1) eqf y(1)) ...</k>
  rule <k> udiff => okb(x() eqf y(1)) ...</k>
  rule <k> usub => okb(z() eqf x()) ...</k>
  rule <k> uint => okb(01 eqi 1) ...</k>
  rule <k> uone => okb(1 eqi 1) ...</k>
endmodule
"#;
    for (program, expected) in [
        ("usame", true),
        ("udiff", false),
        ("usub", false),
        ("uint", true),
        ("uone", true),
    ] {
        assert_ends_in_okb(SOURCE, "KEQ-USER", program, expected);
    }
}

/// A user function hooked `KEQUAL.eq` or `KEQUAL.ne` whose two operands have different sorts is
/// not decided: `z() eqfb z()` compares `inj{Bar, Foo}(z())` with `z()`, two spellings of one
/// value, so a comparison of the terms would give a wrong `false`. Each run halts on the
/// unevaluated hook, as for any constructor-like application without a value.
#[test]
fn a_user_symbol_hooked_kequal_on_two_sorts_is_left_unevaluated() {
    const SOURCE: &str = r#"
module KEQ-MIX-SYNTAX
  syntax Stmt ::= "mixsub" | "mixsubne" | "mixkitem" | "mixdiff"
endmodule
module KEQ-MIX
  imports KEQ-MIX-SYNTAX
  imports K-EQUAL
  imports BOOL
  configuration <k> $PGM:Stmt </k>
  syntax KItem ::= okb(Bool) [symbol(okb)] | a()
  syntax Bar ::= z()
  syntax Foo ::= Bar | x()
  syntax Bool ::= Foo "eqfb" Bar [function, total, hook(KEQUAL.eq)]
  syntax Bool ::= Foo "nefb" Bar [function, total, hook(KEQUAL.ne)]
  syntax Bool ::= KItem "eqik" K [function, total, hook(KEQUAL.eq)]
  rule <k> mixsub => okb(z() eqfb z()) ...</k>
  rule <k> mixsubne => okb(z() nefb z()) ...</k>
  rule <k> mixkitem => okb(a() eqik a()) ...</k>
  rule <k> mixdiff => okb(x() eqfb z()) ...</k>
endmodule
"#;
    for (program, hook) in [
        ("mixsub", "KEQUAL.eq"),
        ("mixsubne", "KEQUAL.ne"),
        ("mixkitem", "KEQUAL.eq"),
        ("mixdiff", "KEQUAL.eq"),
    ] {
        let compiled = compile(SOURCE, "KEQ-MIX", "KEQ-MIX-SYNTAX", "Stmt", program);
        let result = execute(&compiled, "KEQ-MIX", Some(3));
        let [leaf] = result.leaves.as_slice() else {
            panic!("{program}: {result:#?}");
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
        assert!(!state.contains(r#"\dv{SortBool{}}"#), "{program}: {state}");
    }
}

/// Two paths of a state-set run end in the one configuration `c`: `start => c`, and
/// `start => norm(a)`, where `norm(a)` evaluates to `c` on a condition whose simplification
/// exhausts the request's budget of 3 (`g(X) => g(g(X))` never ends), so only that path reports
/// the exhaustion and the rule decided on its unsimplified condition. The state-set result reports
/// `c` once, carrying both diagnostics in either rule declaration order, so it is
/// diagnostic-free exactly when the path-set run of the same request is.
#[test]
fn a_state_set_leaf_lists_the_diagnostics_of_every_path_merged_into_it() {
    use k_rust::backend::{BudgetSubjectOutput, ResultModalityOutput};

    for rules in [
        ["rule start => c", "rule start => norm(a)"],
        ["rule start => norm(a)", "rule start => c"],
    ] {
        let source = format!(
            r#"
module MERGE-DIAGNOSTICS
  imports INT
  imports K-EQUAL
  syntax Pgm ::= "start" | "c" | "a" | norm(Pgm) [function]
  syntax Int ::= g(Int) [function, total]
  rule g(X) => g(g(X)) [simplification]
  rule norm(_) => c requires {{g(0) #Equals g(0)}}
  {}
  {}
endmodule
"#,
            rules[0], rules[1]
        );
        let compiled = compile(
            &source,
            "MERGE-DIAGNOSTICS",
            "MERGE-DIAGNOSTICS",
            "Pgm",
            "start",
        );
        let mut backend = Backend::new(
            &compiled.kore,
            "MERGE-DIAGNOSTICS",
            BackendOptions::default(),
        )
        .unwrap();
        let mut run = |result_modality| {
            backend
                .execute(ExecuteRequest {
                    max_simplification_iterations: 3,
                    result_modality,
                    ..ExecuteRequest::new(compiled.initial.clone())
                })
                .unwrap()
        };
        let exhausted = |leaf: &k_rust::backend::ExecutionLeaf| {
            let budget = leaf.diagnostics.iter().any(|diagnostic| {
                matches!(
                    diagnostic,
                    BackendDiagnosticOutput::SimplificationBudgetExhausted {
                        limit: 3,
                        subject: BudgetSubjectOutput::Predicates,
                    }
                )
            });
            let condition = leaf.diagnostics.iter().any(|diagnostic| {
                matches!(
                    diagnostic,
                    BackendDiagnosticOutput::RuleConditionUnsimplified { limit: 3, .. }
                )
            });
            assert_eq!(
                leaf.diagnostics.len(),
                usize::from(budget) + usize::from(condition)
            );
            budget && condition
        };

        let state_set = run(ResultModalityOutput::StateSet);
        let [leaf] = state_set.leaves.as_slice() else {
            panic!("{rules:?}: expected one state-set leaf: {state_set:#?}");
        };
        assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{rules:?}");
        assert!(text(&state_set)[0].contains("Lblc'"), "{rules:?}");
        assert!(exhausted(leaf), "{rules:?}: {:?}", leaf.diagnostics);

        let path_set = run(ResultModalityOutput::PathSet);
        let [state] = text(&state_set).try_into().unwrap();
        assert_eq!(text(&path_set), [state.clone(), state], "{rules:?}");
        let mut diagnosed = path_set.leaves.iter().map(exhausted).collect::<Vec<_>>();
        diagnosed.sort();
        assert_eq!(diagnosed, [false, true], "{rules:?}");
    }
}
