//! An execute request (`Backend::execute`) has no console and evaluates no hook this backend
//! has no evaluator for: an application of such a hook on constructor-like arguments that the
//! run needs the value of is on the result's `unsupportedHooks`, whichever position of a rule or
//! equation holds it (docs/compatibility.md, "Backend scope", the paragraph after the console
//! operations).
//!
//! The hooks are the console operations, which only `krun --io on` gives a console
//! (`execution_only` in the [hook capability inventory](fixtures/hook-capabilities.toml)), and
//! the hooks without an evaluator whose value the builtin files leave to the backend, the
//! implementation or the environment ([`CASES`]). A run that needs one of their values gets
//! none: the value is not computed, so it cannot steer the run unrecorded. Each position is one
//! test: a rewrite rule's right-hand side, its `requires`, a left-hand-side map key whose match
//! fails, and an equation passed over for a sibling of its priority group (its attempt dropped).
//! Each runs every case under path-set and state-set results.

use std::collections::BTreeSet;

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ResultModalityOutput},
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use serde::Deserialize;

/// Each hook with an application of it on constructor-like arguments, in K. `.RangeMap`
/// applies `RANGEMAP.unit`, which has no evaluator either (no `RangeMap` value is
/// constructor-like in this backend), so its cases list that hook too ([`expected`]).
///
/// The set is the console operations and every hook without an evaluator in this backend that
/// kink-native's census of open hooks lists (`IMPLEMENTATION_CHOSEN_HOOKS`, kink-native
/// `definition-exclusion/v2`): the hooks a client that reads `unsupportedHooks` instead of
/// scanning the definition for them relies on this contract for.
pub const CASES: &[(&str, &str)] = &[
    ("IO.getc", "#getc(0)"),
    ("IO.putc", "#putc(1, 65)"),
    ("IO.read", "#read(0, 1)"),
    ("IO.write", r#"#write(1, "x")"#),
    ("IO.open", r#"#open("f", "r")"#),
    ("IO.tell", "#tell(3)"),
    ("IO.seek", "#seek(3, 0)"),
    ("IO.seekEnd", "#seekEnd(3, 0)"),
    ("IO.close", "#close(3)"),
    ("IO.lock", "#lock(3, 1)"),
    ("IO.unlock", "#unlock(3, 1)"),
    ("IO.accept", "#accept(3)"),
    ("IO.shutdownWrite", "#shutdownWrite(3)"),
    ("IO.time", "#time()"),
    ("IO.system", r#"#system("true")"#),
    ("IO.mkstemp", r#"#mkstemp("tXXXXXX")"#),
    ("IO.remove", r#"#remove("f")"#),
    ("STRING.float2string", "Float2String(1.0)"),
    ("STRING.floatFormat", r#"Float2String(1.0, "%g")"#),
    ("STRING.category", r#"categoryChar("a")"#),
    ("STRING.directionality", r#"directionalityChar("a")"#),
    ("STRING.uuid", "newUUID"),
    ("INT.rand", "randInt(5)"),
    ("INT.srand", "srandInt(5)"),
    ("KREFLECTION.configuration", "#configuration"),
    ("KREFLECTION.fresh", r#"#fresh("Int")"#),
    ("KREFLECTION.getenv", r#"#getenv("HOME")"#),
    ("KREFLECTION.kompiledDir", "#kompiledDirectory()"),
    ("KREFLECTION.argv", "#argv()"),
    ("KREFLECTION.printKORE", "#unparseKORE(1)"),
    ("RANGEMAP.choice", "choice(.RangeMap)"),
    ("RANGEMAP.keys_list", "keys_list(.RangeMap)"),
    ("RANGEMAP.values", "values(.RangeMap)"),
    ("SUBSTITUTION.substMany", "1 [ .Map ]"),
    ("UNIFICATION.renameVariables", "#renameVariables(.K)"),
    ("UNIFICATION.variables", "#variables(.K)"),
    ("UNIFICATION.metaVariables", "#metaKVariables(.K)"),
    ("UNIFICATION.variablesMap", "#variablesMap(.K)"),
    ("UNIFICATION.rename", "#renameMetaKVariables(1, .Set)"),
    ("UNIFICATION.freezeVariables", "#freezeKVariables(1, .K)"),
    ("UNIFICATION.unifiable", "#unifiable(.K, .K)"),
    ("JSON.json2string", "JSON2String(null)"),
    ("JSON.string2json", r#"String2JSON("1")"#),
    ("TIMER.timerStart", "timerStart()"),
    ("TIMER.timerStop", "timerStop()"),
    ("FFI.call", "#ffiCall(0, .List, .List, #void)"),
    (
        "FFI.call_variadic",
        "#ffiCall(0, .List, .List, .List, #void)",
    ),
    ("FFI.address", r#"#functionAddress("f")"#),
    ("FFI.alloc", "#alloc(done, 1, 1)"),
    ("FFI.bytes_address", r#"#address(b"a")"#),
    ("FFI.read", r#"#nativeRead(0, b"a")"#),
    ("FFI.write", r#"#nativeWrite(0, b"a")"#),
];

/// The hooks a run of `hook`'s case lists: the hook, and `RANGEMAP.unit` for `.RangeMap`.
fn expected(hook: &str) -> BTreeSet<String> {
    let mut hooks = BTreeSet::from([hook.to_owned()]);
    if hook.starts_with("RANGEMAP.") {
        hooks.insert("RANGEMAP.unit".to_owned());
    }
    hooks
}

/// Where a case's application sits. Each position needs the application's value: `KEYS`
/// holds a key of every sort an application has, so whether `wrap(E)` is one of them depends on
/// `E`'s value (against a key of another sort it is decided by the sorts alone and reads no
/// value, as `wrap(E) =/=K done` is decided by the heads alone).
#[derive(Clone, Copy, Debug)]
enum Position {
    /// `<r> _ => wrap(E) </r>` in a rewrite rule's right-hand side.
    RightHandSide,
    /// `requires notBool wrap(E) in_keys(KEYS)`: the rule does not apply.
    Condition,
    /// `<m> wrap(E) |-> V ... </m>` in a left-hand side, `<m>` holding `KEYS`, none of which is
    /// `E`'s value: the rule does not apply.
    FailingMapKey,
    /// `dz(_) => 1 requires notBool wrap(E) in_keys(KEYS)` beside `dz(N) => 2 requires N >Int 0`:
    /// the first equation is undecided and passed over, and the second gives the value.
    PassedOverEquation,
}

/// The map whose keys `wrap(E)` is compared with: one key of each sort a case's application
/// has.
fn keys() -> String {
    [
        "0",
        r#""""#,
        "done",
        ".List",
        ".Set",
        ".Bytes",
        "false",
        "null",
        r#"#tempFile("", 0)"#,
    ]
    .map(|key| format!("wrap({key}) |-> 0"))
    .join(" ")
}

/// One definition with one rule (or equation and rule) per case, `go(i)` selecting case `i`.
fn source(position: Position) -> String {
    let keys = keys();
    let mut syntax = String::new();
    let mut rules = String::new();
    for (index, (_, application)) in CASES.iter().enumerate() {
        let wrapped = format!("wrap({application})");
        let go = format!("go({index})");
        match position {
            Position::RightHandSide => rules.push_str(&format!(
                "  rule <k> {go} => .K ... </k> <r> _ => {wrapped} </r>\n"
            )),
            Position::Condition => rules.push_str(&format!(
                "  rule <k> {go} => .K ... </k> <r> _ => 1 </r> \
                 requires notBool {wrapped} in_keys({keys})\n"
            )),
            Position::FailingMapKey => rules.push_str(&format!(
                "  rule <k> {go} => .K ... </k> <m> {wrapped} |-> V ... </m> <r> _ => V </r>\n"
            )),
            Position::PassedOverEquation => {
                syntax.push_str(&format!("  syntax Int ::= dz{index}(Int) [function]\n"));
                rules.push_str(&format!(
                    "  rule dz{index}(_) => 1 requires notBool {wrapped} in_keys({keys})\n  \
                     rule dz{index}(N) => 2 requires N >Int 0\n  \
                     rule <k> {go} => .K ... </k> <r> _ => dz{index}(1) </r>\n"
                ));
            }
        }
    }
    format!(
        r#"requires "substitution.md"
requires "unification.k"
requires "json.md"
requires "timer.md"
requires "ffi.md"
module MAIN
  imports DOMAINS
  imports FLOAT
  imports BYTES
  imports K-IO
  imports K-REFLECTION
  imports RANGEMAP
  imports SUBSTITUTION
  imports UNIFICATION
  imports JSON
  imports TIMER
  imports FFI
  syntax Pgm ::= go(Int)
  syntax KItem ::= wrap(K) | "done"
{syntax}  configuration <k> $PGM:Pgm </k> <m> {keys} </m> <r> .K </r>
{rules}endmodule
"#
    )
}

/// Run every case in `position` and check that each result lists exactly its case's hooks, met
/// by the run.
fn assert_each_case_listed(position: Position) {
    let source = source(position);
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("main.k", source.clone()),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap_or_else(|error| panic!("{position:?}: load: {error}\n{source}"));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{position:?}: compile: {error}"));
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut backend = Backend::new(
        &artifacts.definition_kore,
        "MAIN",
        BackendOptions::default(),
    )
    .unwrap();
    for (index, (hook, application)) in CASES.iter().enumerate() {
        let mut assembler = ConfigurationAssembler::new(
            &grammar,
            "MAIN",
            "MAIN",
            &artifacts.configuration_variables,
        );
        assembler
            .program(&Sort::new("Pgm"), &format!("go({index})"))
            .unwrap();
        let initial = assembler.finish().unwrap();
        for modality in [
            ResultModalityOutput::PathSet,
            ResultModalityOutput::StateSet,
        ] {
            let result = backend
                .execute(ExecuteRequest {
                    result_modality: modality,
                    strategy: ExecutionStrategy::All,
                    ..ExecuteRequest::new(initial.clone())
                })
                .unwrap_or_else(|error| panic!("{position:?} {application}: {error}"));
            let listed = result
                .unsupported_hooks
                .iter()
                .map(|entry| {
                    (
                        entry.hook.clone(),
                        serde_json::to_value(entry.observed_in).unwrap().to_string(),
                    )
                })
                .collect::<BTreeSet<_>>();
            assert_eq!(
                listed,
                expected(hook)
                    .into_iter()
                    .map(|hook| (hook, r#""run""#.to_owned()))
                    .collect(),
                "{position:?} {application} {modality:?}"
            );
            for leaf in &result.leaves {
                let state = leaf.state.to_string();
                let held = match position {
                    Position::RightHandSide => true,
                    // The rule did not apply: `go` is still in `<k>`.
                    Position::Condition | Position::FailingMapKey => state.contains("Lblgo"),
                    // The sibling equation gave the value: `<r> 2 </r>`, no `dz` left.
                    Position::PassedOverEquation => {
                        state.contains(r#""value":"2""#)
                            && !state.contains(&format!("Lbldz{index}"))
                    }
                };
                assert!(held, "{position:?} {application} {modality:?}: {state}");
            }
        }
    }
}

#[test]
fn an_application_in_a_right_hand_side_is_on_the_run_list() {
    assert_each_case_listed(Position::RightHandSide);
}

#[test]
fn an_application_in_a_condition_is_on_the_run_list() {
    assert_each_case_listed(Position::Condition);
}

#[test]
fn an_application_in_a_failing_left_hand_side_map_key_is_on_the_run_list() {
    assert_each_case_listed(Position::FailingMapKey);
}

#[test]
fn an_application_in_a_passed_over_equation_is_on_the_run_list() {
    assert_each_case_listed(Position::PassedOverEquation);
}

#[derive(Deserialize)]
struct Inventory {
    execution_only: Vec<String>,
    unsupported: Vec<UnsupportedGroup>,
}

#[derive(Deserialize)]
struct UnsupportedGroup {
    hooks: Vec<String>,
}

/// The cases hold every console operation, and each prelude hook among them is one the
/// inventory classes `execution_only` or `unsupported`; the others come from builtin files the
/// prelude does not require (`substitution.md`, `unification.k`, `json.md`, `timer.md`,
/// `ffi.md`), and their right-hand-side test shows them unevaluated.
#[test]
fn the_cases_are_hooks_without_an_evaluator_and_hold_every_console_operation() {
    let inventory: Inventory = toml::from_str(include_str!("fixtures/hook-capabilities.toml"))
        .expect("hook capability manifest must be valid TOML");
    let hooks = CASES
        .iter()
        .map(|(hook, _)| (*hook).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(hooks.len(), CASES.len(), "one case per hook");
    let execution_only = inventory
        .execution_only
        .into_iter()
        .collect::<BTreeSet<_>>();
    assert!(execution_only.is_subset(&hooks), "{execution_only:?}");
    let unsupported = inventory
        .unsupported
        .into_iter()
        .flat_map(|group| group.hooks)
        .collect::<BTreeSet<_>>();
    let outside_prelude = ["SUBSTITUTION.", "UNIFICATION.", "JSON.", "TIMER.", "FFI."];
    for hook in &hooks {
        assert!(
            execution_only.contains(hook)
                || unsupported.contains(hook)
                || outside_prelude
                    .iter()
                    .any(|namespace| hook.starts_with(namespace)),
            "{hook}"
        );
    }
}

/// R1-SIMPLE: the converse. A definition whose rules project the result of an effect over a
/// rule variable, as the prelude's stream rules do (`{#getc(N)}:>Int` and
/// `{#write(N, S) ~> N}:>Int`), has no entry on the list of a run that never applies those
/// rules: nothing needed the effects' values. The load's discharge of rewrite-rule definedness
/// reads such a right-hand side over the rule's variables; the projection's ceil equation
/// instantiated at the effect's application would state a predicate over the effect's result,
/// which only performing the effect decides, and simplifying it met the application unevaluated
/// at load, listing `IO.getc` and `IO.write` on every run. A run that applies the rule on a
/// constructor-like argument needs the value, and lists the hook as met by the run.
#[test]
fn an_effect_under_a_projection_in_a_rule_no_run_applies_is_on_no_run_list() {
    let source = r#"module MAIN
  imports DOMAINS
  imports K-IO
  syntax Pgm ::= go(Int) | get(Int) | put(Int, String)
  configuration <k> $PGM:Pgm </k> <r> 0 </r>
  rule <k> go(N) => .K ... </k> <r> _ => N </r>
  rule <k> get(N) => .K ... </k> <r> _ => {#getc(N)}:>Int </r>
  rule <k> put(N, S) => .K ... </k> <r> _ => {#write(N, S) ~> N}:>Int </r>
endmodule
"#;
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("main.k", source.to_owned()),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap_or_else(|error| panic!("load: {error}"));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("compile: {error}"));
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut backend = Backend::new(
        &artifacts.definition_kore,
        "MAIN",
        BackendOptions::default(),
    )
    .unwrap();
    for (program, listed) in [("go(1)", None), ("get(0)", Some("IO.getc"))] {
        let mut assembler = ConfigurationAssembler::new(
            &grammar,
            "MAIN",
            "MAIN",
            &artifacts.configuration_variables,
        );
        assembler.program(&Sort::new("Pgm"), program).unwrap();
        let result = backend
            .execute(ExecuteRequest {
                strategy: ExecutionStrategy::All,
                ..ExecuteRequest::new(assembler.finish().unwrap())
            })
            .unwrap_or_else(|error| panic!("{program}: {error}"));
        let entries = result
            .unsupported_hooks
            .iter()
            .map(|entry| {
                (
                    entry.hook.clone(),
                    serde_json::to_value(entry.observed_in).unwrap().to_string(),
                )
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            entries,
            listed
                .map(|hook| (hook.to_owned(), r#""run""#.to_owned()))
                .into_iter()
                .collect(),
            "{program}"
        );
    }
}
