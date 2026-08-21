#![cfg(feature = "cli")]

use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use k_rust::kore::parser::parse_definition;

const DEFINITION: &str = r#"
requires "base.k"

module MAIN
  imports BASE
  syntax Exp ::= Int
  syntax Exp ::= Exp "+" Exp [comm, function, symbol(_+_)]
  rule 1 + 2 => 2 + 1 [simplification, comm]
endmodule
"#;

const BASE: &str = r#"
module BASE
  syntax Int ::= r"[0-9]+" [token]
endmodule
"#;

#[test]
fn reports_the_packaged_version() {
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("--version")
        .output()
        .unwrap();

    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("krust {}\n", env!("CARGO_PKG_VERSION"))
    );
}

fn fixture() -> (PathBuf, PathBuf) {
    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
    let nonce = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!("k-rust-cli-{}-{nonce}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let definition = root.join("definition.k");
    fs::write(&definition, DEFINITION).unwrap();
    fs::write(root.join("base.k"), BASE).unwrap();
    (root, definition)
}

#[test]
fn kast_parses_a_program_as_text_and_json() {
    let (root, definition) = fixture();
    let binary = env!("CARGO_BIN_EXE_krust");

    let text = Command::new(binary)
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "42",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        text.status.success(),
        "{}",
        String::from_utf8_lossy(&text.stderr)
    );
    assert_eq!(
        String::from_utf8(text.stdout).unwrap(),
        "#token(\"42\",\"Int\")\n"
    );

    let json = Command::new(binary)
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "42",
            "--output",
            "json",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        json.status.success(),
        "{}",
        String::from_utf8_lossy(&json.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&json.stdout).unwrap();
    assert_eq!(value["format"], "KAST");
    assert_eq!(value["version"], 4);
    assert_eq!(value["term"]["token"], "42");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn installed_cli_uses_embedded_pinned_builtins_by_default() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        "module MAIN\n  imports DOMAINS\n  syntax Exp ::= Int\nendmodule\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "42",
        ])
        .current_dir(&root)
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "#token(\"42\",\"Int\")\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_executes_a_concrete_program_in_process() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
  syntax State ::= "b" [symbol(b)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lblb{}()"), "{output}");
    assert!(!output.contains("Lbla{}()"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_eliminates_a_k_sequence_rewritten_to_bottom() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Marker ::= "marker"
  configuration <k> marker ~> $PGM:Int </k>
  rule <k> marker => #Bottom ... </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "1",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.contains(r"\bottom{SortGeneratedTopCell{}}()"),
        "{output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_explores_by_default_and_can_stop_at_a_branch_point() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" | "b" | "c" | "d" | "e"
  configuration <k> $PGM:State </k>
  rule a => b
  rule b => c
  rule c => d
  rule c => e
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
            "--execute-to-branch",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lblc'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lbld'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );
    assert!(
        !output.contains("Lble'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_explores_an_unconditional_branch() {
    let (root, definition) = fixture();
    let search_pattern = root.join("target.kore");
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" | "b" | "c" | "d" | "e"
  configuration <k> $PGM:State </k>
  rule a => b
  rule b => c
  rule c => d
  rule c => e
endmodule
"#,
    )
    .unwrap();
    fs::write(&search_pattern, "Result:SortGeneratedTopCell{}").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-final",
            "--search-pattern",
            search_pattern.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Result:SortGeneratedTopCell{}"), "{output}");
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lblc'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_runs_a_compiled_definition_and_searches_it() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let program = root.join("program.kore");
    let target = root.join("target.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol c{}() : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    b{}()
  ) [label{}("a-to-b")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    c{}()
  ) [label{}("a-to-c")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&program, "a{}()").unwrap();
    fs::write(&target, "Result:SortS{}").unwrap();

    let execute = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        execute.status.success(),
        "{}",
        String::from_utf8_lossy(&execute.stderr)
    );
    let execute = String::from_utf8(execute.stdout).unwrap();
    assert!(execute.starts_with(r#"\or{SortS{}}("#), "{execute}");
    assert!(execute.contains("b{}()"), "{execute}");
    assert!(execute.contains("c{}()"), "{execute}");

    let branch = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--execute-to-branch",
        ])
        .output()
        .unwrap();
    assert!(
        branch.status.success(),
        "{}",
        String::from_utf8_lossy(&branch.stderr)
    );
    assert_eq!(String::from_utf8(branch.stdout).unwrap(), "a{}()\n");

    let any = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--strategy",
            "any",
        ])
        .output()
        .unwrap();
    assert!(
        any.status.success(),
        "{}",
        String::from_utf8_lossy(&any.stderr)
    );
    assert_eq!(String::from_utf8(any.stdout).unwrap(), "b{}()\n");

    let search = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--search-final",
            "--search-pattern",
            target.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        search.status.success(),
        "{}",
        String::from_utf8_lossy(&search.stderr)
    );
    let search = String::from_utf8(search.stdout).unwrap();
    assert!(search.contains("Result:SortS{}"), "{search}");
    assert!(search.contains("b{}()"), "{search}");
    assert!(search.contains("c{}()"), "{search}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_match_disjunction_matches_each_configuration_and_writes_its_result() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let disjunction = root.join("disjunction.kore");
    let pattern = root.join("pattern.kore");
    let result = root.join("result.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&disjunction, r#"\or{SortS{}}(a{}(), b{}())"#).unwrap();
    fs::write(&pattern, "Result:SortS{}").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-match-disjunction",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--disjunction",
            disjunction.to_str().unwrap(),
            "--match",
            pattern.to_str().unwrap(),
            "--output",
            result.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    let result = fs::read_to_string(result).unwrap();
    assert!(result.starts_with(r#"\or{SortS{}}("#), "{result}");
    assert!(result.contains("Result:SortS{}"), "{result}");
    assert!(result.contains("a{}()"), "{result}");
    assert!(result.contains("b{}()"), "{result}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_proves_a_modal_claim_in_process() {
    let (root, definition) = fixture();
    let saved_proofs = root.join("proofs.kore");
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
                 | "c" [symbol(c)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
  claim <k> a => b #Or c </k> [label(reaches-b-or-c)]
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--claim",
            "reaches-b-or-c",
            "--depth",
            "10",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "claim reaches-b-or-c: proven (2 states, 0 unexplored)\n"
    );
    let saved = parse_definition(&fs::read_to_string(&saved_proofs).unwrap()).unwrap();
    assert_eq!(
        saved.modules[0].name,
        "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d"
    );
    assert_eq!(
        saved.modules[0]
            .sentences
            .iter()
            .filter(|sentence| matches!(sentence, k_rust::kore::ast::Sentence::Claim { .. }))
            .count(),
        1
    );

    let resumed = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--claim",
            "reaches-b-or-c",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        resumed.status.success(),
        "{}",
        String::from_utf8_lossy(&resumed.stderr)
    );
    assert_eq!(
        String::from_utf8(resumed.stdout).unwrap(),
        "claim reaches-b-or-c: proven (saved)\n"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_recalls_the_same_claim_from_another_spec_module() {
    let (root, _) = fixture();
    let saved_proofs = root.join("proofs.kore");
    let semantics = root.join("semantics.k");
    let first_spec = root.join("first-spec.k");
    let second_spec = root.join("second-spec.k");
    fs::write(
        &semantics,
        r#"
module SEMANTICS
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &first_spec,
        r#"
requires "semantics.k"
module FIRST-SPEC
  imports SEMANTICS
  claim <k> a => b </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &second_spec,
        r#"
requires "semantics.k"
module SECOND-SPEC
  imports SEMANTICS
  claim <k> a => b </k>
endmodule
"#,
    )
    .unwrap();

    let first = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            first_spec.to_str().unwrap(),
            "--main-module",
            "FIRST-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );

    let second = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            second_spec.to_str().unwrap(),
            "--main-module",
            "SECOND-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        second.status.success(),
        "{}",
        String::from_utf8_lossy(&second.stderr)
    );
    assert_eq!(
        String::from_utf8(second.stdout).unwrap(),
        "claim #1: proven (saved)\n"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_handles_generated_concreteness_constraints() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Int ::= abs(Int) [function, total]
               | "error" [function, total]
  rule abs(X:Int) => X:Int requires X >Int 0
  rule abs(X) => 0 -Int X [owise]
  rule abs(0) => error [simplification]
  configuration <k> $PGM:Int </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "abs(0)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("0")"#), "{output}");
    assert!(!output.contains("Lblerror{}()"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_simplifies_partial_rhs_functions_before_definedness() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Pgm ::= run(Int)
  syntax Num ::= Int
               | inc(Num) [function]
               | foo(Num) [function]
  rule run(3) => foo(inc(333))
  rule inc(I:Int) => I +Int 1 [concrete]
  rule foo(I) => I
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Pgm",
            "--expression",
            "run(3)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("334")"#), "{output}");
    assert!(!output.contains("Lblinc"), "{output}");
    assert!(!output.contains("Lblfoo"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_retains_unresolved_definedness_as_a_constraint() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Pgm ::= run(Int)
  syntax Num ::= Int | stuck(Num) [function]
  rule run(I) => stuck(I)
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Pgm",
            "--expression",
            "run(1)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.contains(r#"\ceil{SortNum{}, SortGeneratedTopCell{}}"#),
        "{output}"
    );
    assert!(output.contains("Lblstuck"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_recovers_evaluable_collection_function_patterns() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports LIST
  imports INT
  configuration <k> $PGM:K </k>
                <list> ListItem(0) ListItem(1) ListItem(2) </list>
  syntax KItem ::= l(Int, Int)
  rule <k> l(I, J) => .K ...</k>
       <list> _ [ I <- J ] </list>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
            "--expression",
            "l(1, 1)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())"), "{output}");
    assert!(output.contains(r#"\dv{SortInt{}}("2")"#), "{output}");
    assert!(!output.contains("Lbll'LPar"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_emits_k_user_logs_on_standard_error() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports K-IO
  imports STRING
  configuration <k> $PGM:K </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "K",
            "--expression",
            r#"#log("hello from K")"#,
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stderr).unwrap(), "hello from K\n");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("dotk{}()"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_writes_parseable_kore_outputs() {
    let (root, definition) = fixture();
    let output_directory = root.join("compiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    for name in ["definition.kore", "syntaxDefinition.kore"] {
        let source = fs::read_to_string(output_directory.join(name)).unwrap();
        let parsed = parse_definition(&source).unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(
            parsed
                .modules
                .iter()
                .map(|module| module.name.as_str())
                .collect::<Vec<_>>(),
            ["BASIC-K", "KSEQ", "INJ", "K", "MAIN"],
        );
        assert!(source.contains("Source("));
        if name == "definition.kore" {
            assert_eq!(source.matches("simplification{}()").count(), 3);
        }
    }
    assert!(
        fs::read_to_string(output_directory.join("macros.kore"))
            .unwrap()
            .trim()
            .is_empty()
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_backend_selects_symbolic_or_concrete_modules() {
    let source = r#"
module SYMBOLIC [symbolic]
  syntax Exp ::= "symbolic" [symbol(symbolicOnly)]
endmodule

module CONCRETE [concrete]
  syntax Exp ::= "concrete" [symbol(concreteOnly)]
endmodule

module MAIN
  imports SYMBOLIC
  imports CONCRETE
  syntax Exp ::= "main" [symbol(main)]
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();

    for (backend, present, absent) in [
        ("llvm", "concreteOnly", "symbolicOnly"),
        ("rust", "symbolicOnly", "concreteOnly"),
    ] {
        let output_directory = root.join(backend);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kcompile",
                definition.to_str().unwrap(),
                "--main-module",
                "MAIN",
                "--backend",
                backend,
                "--output-directory",
                output_directory.to_str().unwrap(),
                "--no-prelude",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{backend}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let kore = fs::read_to_string(output_directory.join("definition.kore")).unwrap();
        assert!(kore.contains(present), "{backend} should retain {present}");
        assert!(!kore.contains(absent), "{backend} should exclude {absent}");
    }

    fs::remove_dir_all(root).unwrap();
}
