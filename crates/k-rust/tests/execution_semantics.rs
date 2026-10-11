//! Execution semantics on the KORE krust compiles, checked in-process.
//!
//! What a run of a compiled definition ends in is the backend's contract: the leaves the backend
//! returns for an initial configuration. `cli.rs` checks how `krust krun` reports these runs
//! (printed KORE, exit status); the tests here compile the definition, assemble the initial
//! configuration from the program text as `krun` does, and ask the backend for the run directly.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, HaltReasonOutput,
        SearchPatternRequest, SearchTypeArg,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::{ast::Pattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

/// A definition compiled for the Rust backend with the prelude, and the initial configuration
/// of a program for it.
struct Compiled {
    kore: String,
    initial: Pattern,
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
    Compiled {
        kore: artifacts.definition_kore,
        initial: assembler.finish().unwrap(),
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
#[test]
fn a_run_halts_on_a_result_above_the_size_bound() {
    const SOURCE: &str = r#"
module BOUND
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "unusedshl" | "guard" | "decided" | "dropped" | "used" | "shl" | "computed"
  syntax KItem ::= r(K) | f(Int) | g(Int) | "pos" | "nonpos"
  syntax Int ::= i(Int) [function, total]
  rule i(X) => X
  rule <k> unusedshl => r(false andBool (1 <<Int i(16777216) >Int i(0))) </k>
  rule <k> guard => r(1) </k> requires i(0) >Int i(1) andBool (1 <<Int i(16777216)) >Int i(0)
  rule <k> guard => r(4) </k> [owise]
  rule <k> decided => r(1) </k> requires 2 ^Int i(16777217) >Int i(0)
  rule <k> decided => r(4) </k> [owise]
  rule <k> dropped => g(1 <<Int i(16777217)) </k>
  rule <k> g(_) => r(9) </k>
  rule <k> used => r(2 ^Int 16777216) </k>
  rule <k> shl => f(1 <<Int i(16777217)) </k>
  rule <k> computed => r(2 ^Int i(1048576) >Int 0) </k>
  rule <k> f(X) => r(pos) </k> requires X >Int 0
  rule <k> f(X) => r(nonpos) </k> requires X <=Int 0
endmodule
"#;
    for (program, hook) in [("used", "INT.pow"), ("shl", "INT.shl")] {
        let compiled = compile(SOURCE, "BOUND", "BOUND", "Pgm", program);
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
        let compiled = compile(SOURCE, "BOUND", "BOUND", "Pgm", program);
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

/// Each step of `go(M, L, N)` adds a new variable `?K` to the map and the list, by any of three
/// equal rules, so the states at one depth are renamings of each other: their map entries differ
/// only in the names of their keys (which order differently once the counter reaches two digits,
/// `!10` before `!3`), while the list fixes which entry is which. So each depth is one state: the
/// search for every state (a target that is one variable of the configuration's sort, as `krun`
/// searches) finds the five counters once each, and the final state once.
#[test]
fn a_search_finds_the_renamings_of_one_state_once() {
    const SOURCE: &str = r#"
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
    let compiled = compile(SOURCE, "T", "T", "KItem", "go(.Map, .List, 4)");
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
