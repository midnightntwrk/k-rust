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

fn branching_search_fixture() -> (PathBuf, PathBuf) {
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
fn kast_parses_and_rejects_a_batch_with_one_frontend_load() {
    let (root, definition) = fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--batch-case",
            "integer",
            "Exp",
            "42",
            "--batch-case",
            "addition",
            "Exp",
            "1 + 2",
            "--batch-reject-case",
            "malformed",
            "Exp",
            "+",
            "--output",
            "json",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(value["integer"]["term"]["token"], "42");
    assert_eq!(value["addition"]["term"]["node"], "KApply");
    assert!(value.get("malformed").is_none());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_preserves_and_krun_expands_macros_in_concrete_programs() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Input ::= Int | "twice" "(" Int ")" [macro]
  rule twice(I) => I +Int I
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();
    let binary = env!("CARGO_BIN_EXE_krust");

    let kast = Command::new(binary)
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "twice(21)",
            "--output",
            "json",
        ])
        .output()
        .unwrap();
    assert!(
        kast.status.success(),
        "{}",
        String::from_utf8_lossy(&kast.stderr)
    );
    let kast = String::from_utf8(kast.stdout).unwrap();
    assert!(kast.contains("twice"), "{kast}");
    assert!(!kast.contains("_+Int_"), "{kast}");

    let krun = Command::new(binary)
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "twice(21)",
            "--depth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        krun.status.success(),
        "{}",
        String::from_utf8_lossy(&krun.stderr)
    );
    let krun = String::from_utf8(krun.stdout).unwrap();
    assert!(!krun.contains("Lbltwice"), "{krun}");
    assert!(krun.contains(r#"\dv{SortInt{}}("42")"#), "{krun}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_omits_inferred_parametric_label_arguments() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax A ::= "a" [symbol(a)]
  syntax {S} S ::= "pair(" S "," S ")" [symbol(pair)]
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--batch-case",
            "pair",
            "A",
            "pair(a,a)",
            "--output",
            "json",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(value["pair"]["term"]["label"]["name"], "pair");
    assert_eq!(
        value["pair"]["term"]["label"]["params"],
        serde_json::json!([])
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_backend_selects_the_matching_module_view() {
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
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let binary = env!("CARGO_BIN_EXE_krust");
    let kast = |backend: Option<&str>, expression: &str| {
        let mut command = Command::new(binary);
        command.args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            expression,
            "--no-prelude",
        ]);
        if let Some(backend) = backend {
            command.args(["--backend", backend]);
        }
        command.output().unwrap()
    };

    // Without `--backend`, kast parses against the same Rust-backend view that `kcompile` and
    // `krun` use by default, so the grammar can never disagree with the compiled artifact.
    assert!(kast(None, "symbolic").status.success());
    assert!(!kast(None, "concrete").status.success());
    assert!(kast(Some("rust"), "symbolic").status.success());
    assert!(!kast(Some("rust"), "concrete").status.success());
    assert!(kast(Some("llvm"), "concrete").status.success());
    assert!(!kast(Some("llvm"), "symbolic").status.success());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_binds_declared_configuration_variables() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
  syntax State ::= "b" [symbol(b)]
  syntax Env ::= "ready" [symbol(ready)]
  configuration
    <top>
      <k> $PGM:State </k>
      <env> $ENV:Env </env>
    </top>
  rule <k> a => b </k> <env> ready </env>
endmodule
"#,
    )
    .unwrap();
    let binary = env!("CARGO_BIN_EXE_krust");
    let output = Command::new(binary)
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "-cENV=ready",
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
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lblb{}()"), "{stdout}");
    assert!(stdout.contains("Lblready{}()"), "{stdout}");
    assert!(
        !stdout.contains("\\bottom{SortGeneratedTopCell{}}("),
        "{stdout}"
    );

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
fn krun_populates_additional_configuration_variables() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports MAP
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
  configuration <k> $PGM:State </k> <env> $ENV:Map </env>
  rule <k> a => b </k> <env> .Map </env>
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
            "-c",
            "ENV=.Map",
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
    assert!(output.contains("Lbl'Stop'Map{}()"), "{output}");

    let missing = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
        ])
        .output()
        .unwrap();
    assert!(!missing.status.success());
    assert!(
        String::from_utf8_lossy(&missing.stderr)
            .contains("missing required configuration variable $ENV; pass `-c ENV=VALUE`"),
        "{}",
        String::from_utf8_lossy(&missing.stderr)
    );

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
    let (root, definition) = branching_search_fixture();
    let search_pattern = root.join("target.kore");
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
fn default_search_binds_the_reference_result_variable() {
    let (root, definition) = branching_search_fixture();
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
            "--search-one-step",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("VarResult:SortGeneratedTopCell{}"),
        "{stdout}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn search_bound_truncation_is_reported_to_the_user() {
    let (root, definition) = branching_search_fixture();
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
            "--search-all",
            "--search-bound",
            "1",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("search stopped at the requested result bound"),
        "{stderr}"
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!stdout.contains("\\or{"), "{stdout}");

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
            "--search-bound",
            "2",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("result bound"), "{stderr}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\\or{"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn undeclared_config_variables_are_rejected_by_name() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
  configuration <k> $PGM:State </k>
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
            "-cNOPE=1",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("NOPE"), "{stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn search_flag_combinations_are_validated() {
    let (root, definition) = fixture();
    let target = root.join("target.kore");
    fs::write(&target, "Result:SortExp{}").unwrap();
    let cases = [
        (
            "exclusive search modes",
            vec!["--search-all", "--search-one-step"],
            "--search-one-step",
        ),
        (
            "bound requires a mode",
            vec!["--search-bound", "3"],
            "--search-bound",
        ),
        (
            "pattern requires a mode",
            vec!["--search-pattern", target.to_str().unwrap()],
            "--search-pattern",
        ),
    ];

    for (name, extra, expected) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "MAIN",
                "--sort",
                "Exp",
                "--expression",
                "1",
            ])
            .args(extra)
            .output()
            .unwrap();
        assert!(!output.status.success(), "{name} unexpectedly succeeded");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains(expected), "{name}: {stderr}");
    }

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
  symbol d{}() : SortS{} [constructor{}()]
  symbol e{}() : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    b{}()
  ) [label{}("a-to-b")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    c{}()
  ) [label{}("a-to-c")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(b{}(), \top{SortS{}}()),
    d{}()
  ) [label{}("b-to-d")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(c{}(), \top{SortS{}}()),
    e{}()
  ) [label{}("c-to-e")]
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
    assert!(execute.contains("d{}()"), "{execute}");
    assert!(execute.contains("e{}()"), "{execute}");

    let result_file = root.join("result.kore");
    let file_output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--output",
            result_file.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        file_output.status.success(),
        "{}",
        String::from_utf8_lossy(&file_output.stderr)
    );
    assert!(file_output.stdout.is_empty());
    let file_output = fs::read_to_string(result_file).unwrap();
    assert!(file_output.contains("d{}()"), "{file_output}");
    assert!(file_output.contains("e{}()"), "{file_output}");

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
    assert_eq!(String::from_utf8(any.stdout).unwrap(), "d{}()\n");

    let breadth = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--breadth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        breadth.status.success(),
        "{}",
        String::from_utf8_lossy(&breadth.stderr)
    );
    let breadth = String::from_utf8(breadth.stdout).unwrap();
    assert!(breadth.contains("b{}()"), "{breadth}");
    assert!(breadth.contains("c{}()"), "{breadth}");
    assert!(!breadth.contains("d{}()"), "{breadth}");
    assert!(!breadth.contains("e{}()"), "{breadth}");

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
    assert!(search.contains("d{}()"), "{search}");
    assert!(search.contains("e{}()"), "{search}");

    let bounded_search = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--search-final",
            "--breadth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(!bounded_search.status.success());
    assert!(
        String::from_utf8_lossy(&bounded_search.stderr).contains("BreadthBound"),
        "{}",
        String::from_utf8_lossy(&bounded_search.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_adds_a_rule_module_before_execution() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let added_module = root.join("new-module.kore");
    let program = root.join("program.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortState{} [hasDomainValues{}()]
  symbol state{}(SortState{}) : SortState{} [constructor{}()]
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(state{}(\dv{SortState{}}("a")), \top{SortState{}}()),
    \and{SortState{}}(state{}(\dv{SortState{}}("d")), \top{SortState{}}())
  ) [label{}("MAIN.AD")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(
        &added_module,
        r#"module NEW
  import MAIN []
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(state{}(\dv{SortState{}}("d")), \top{SortState{}}()),
    \and{SortState{}}(state{}(\dv{SortState{}}("e")), \top{SortState{}}())
  ) [label{}("NEW.DE")]
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(state{}(\dv{SortState{}}("e")), \top{SortState{}}()),
    \and{SortState{}}(state{}(\dv{SortState{}}("f")), \top{SortState{}}())
  ) [label{}("NEW.EF")]
endmodule []"#,
    )
    .unwrap();
    fs::write(&program, r#"state{}(\dv{SortState{}}("a"))"#).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "NEW",
            "--add-module",
            added_module.to_str().unwrap(),
            "--pattern",
            program.to_str().unwrap(),
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
        "state{}(\\dv{SortState{}}(\"f\"))\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_get_model_returns_a_typed_substitution() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let predicate = root.join("predicate.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
    [function{}(), total{}(), smt-hook{}("<")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(
        &predicate,
        r#"\equals{SortBool{}, SortBool{}}(
  \dv{SortBool{}}("true"),
  lt{}(X:SortInt{}, \dv{SortInt{}}("5"))
)"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-get-model",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            predicate.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(output["satisfiable"], "Sat");
    assert_eq!(output["substitution"]["format"], "KORE");
    assert_eq!(output["substitution"]["term"]["tag"], "Equals");
    assert_eq!(output["substitution"]["term"]["first"]["name"], "X");
    assert_eq!(
        output["substitution"]["term"]["second"]["sort"]["name"],
        "SortInt"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_implies_returns_the_matching_condition() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let antecedent = root.join("antecedent.kore");
    let consequent = root.join("consequent.kore");
    fs::write(
        &definition,
        "[]\nmodule MAIN\n  sort SortK{} []\nendmodule []\n",
    )
    .unwrap();
    fs::write(&antecedent, "X:SortK{}").unwrap();
    fs::write(&consequent, r"\exists{SortK{}}(Z:SortK{}, Z:SortK{})").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-implies",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--antecedent",
            antecedent.to_str().unwrap(),
            "--consequent",
            consequent.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(output["status"], "valid");
    assert_eq!(
        output["condition"]["substitution"]["term"]["first"]["name"],
        "X"
    );
    assert_eq!(
        output["condition"]["substitution"]["term"]["second"]["name"],
        "Z"
    );
    assert_eq!(output["condition"]["predicate"]["term"]["tag"], "Top");

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

    let limited = Command::new(env!("CARGO_BIN_EXE_krust"))
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
            "--max-simplification-iterations",
            "1",
        ])
        .output()
        .unwrap();
    assert!(!limited.status.success());
    let stderr = String::from_utf8(limited.stderr).unwrap();
    assert!(stderr.contains("Simplification"), "{stderr}");
    assert!(stderr.contains("IterationLimit"), "{stderr}");

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
            "--emit-json",
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
    let parsed = k_rust::definition::json::from_str(
        &fs::read_to_string(output_directory.join("parsed.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(parsed.main_module, "MAIN");
    assert_eq!(parsed.attributes.get_str("syntaxModule"), Some("MAIN"));
    assert_eq!(
        parsed
            .modules
            .iter()
            .map(|module| module.name.as_str())
            .collect::<Vec<_>>(),
        ["BASE", "MAIN"],
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_hook_namespaces_default_per_backend() {
    let source = r#"
module MAIN
  syntax Bytes
  syntax String
  syntax String ::= "keccak(" Bytes ")" [function, hook(KRYPTO.keccak256), symbol(keccak)]
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();

    let kompile = |name: &str, extra: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--no-prelude",
        ]);
        command.args(extra);
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        fs::read_to_string(output_directory.join("definition.kore")).unwrap()
    };
    let hooked = |kore: &str| kore.contains("hooked-symbol Lblkeccak{}");

    // The Rust backend implements KRYPTO natively, so it is admitted without a flag.
    assert!(hooked(&kompile("rust", &[])));
    // Other backends match a default Java kompile: plugin hooks need --hook-namespaces.
    assert!(!hooked(&kompile("llvm", &["--backend", "llvm"])));
    assert!(hooked(&kompile(
        "llvm-admitted",
        &["--backend", "llvm", "--hook-namespaces", "HASH,KRYPTO"]
    )));

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

#[test]
fn krun_executes_bn128_fixture_to_pinned_kore_results() {
    fn g1_result(x: &str, y: &str) -> String {
        format!(
            r#"Lbl'-LT-'generatedTop'-GT-'{{}}(
  Lbl'-LT-'k'-GT-'{{}}(
    kseq{{}}(
      inj{{SortG1Point{{}}, SortKItem{{}}}}(
        Lbl'LParUndsCommUndsRParUnds'BN128-EXECUTION'Unds'G1Point'Unds'Int'Unds'Int{{}}(
          \dv{{SortInt{{}}}}("{x}"),
          \dv{{SortInt{{}}}}("{y}")
        )
      ),
      dotk{{}}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{{}}(\dv{{SortInt{{}}}}("0"))
)
"#,
        )
    }

    let bool_result = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortBool{}, SortKItem{}}(\\dv{SortBool{}}(\"true\")), dotk{}())),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))\n",
        ")\n",
    );
    let doubled = g1_result(
        "1368015179489954701390400359078579693043519447331113978918064868415326638035",
        "9918110051302171585080402603319702774565515993150576347155970296011118125764",
    );
    let cases = [
        (
            "bn128-ecadd.crypto",
            g1_result(
                "15497584038690294240042153688304417339506091937513459124271972833238779664131",
                "21762456842531143558012592863461237297422391564814111359902381816272400009493",
            ),
        ),
        ("bn128-ecmul.crypto", doubled.clone()),
        ("bn128-ecmul-reduce.crypto", doubled),
        ("bn128-pairing.crypto", bool_result.to_owned()),
        ("bn128-valid-infinity.crypto", bool_result.to_owned()),
    ];
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("bn128-execution.k");

    for (program, expected) in cases {
        let program_path = fixtures.join(program);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "BN128-EXECUTION",
                "--sort",
                "Input",
                program_path.to_str().unwrap(),
                "--depth",
                "10",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            expected,
            "{program}"
        );
    }
}

#[test]
fn krun_executes_evm_optimized_add_fixture_to_pinned_kore_result() {
    let expected = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'kevm'-GT-'{}(\n",
        "    Lbl'-LT-'k'-GT-'{}(dotk{}()),\n",
        "    Lbl'-LT-'schedule'-GT-'{}(LblCANCUN'Unds'EVM-OPTIMIZED-ADD'Unds'Schedule{}()),\n",
        "    Lbl'-LT-'useGas'-GT-'{}(\\dv{SortBool{}}(\"false\")),\n",
        "    Lbl'-LT-'ethereum'-GT-'{}(\n",
        "      Lbl'-LT-'evm'-GT-'{}(\n",
        "        Lbl'-LT-'callState'-GT-'{}(\n",
        "          Lbl'-LT-'wordStack'-GT-'{}(\n",
        "            Lbl'UndsColnUndsUnds'EVM-OPTIMIZED-ADD'Unds'WordStack'Unds'Int'Unds'WordStack{}(\n",
        "              \\dv{SortInt{}}(\"11\"),\n",
        "              Lbl'Stop'WordStack'Unds'EVM-OPTIMIZED-ADD'Unds'WordStack{}()\n",
        "            )\n",
        "          ),\n",
        "          Lbl'-LT-'pc'-GT-'{}(\\dv{SortInt{}}(\"1\")),\n",
        "          Lbl'-LT-'gas'-GT-'{}(\\dv{SortInt{}}(\"99\"))\n",
        "        )\n",
        "      )\n",
        "    )\n",
        "  ),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))\n",
        ")\n",
    );
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("evm-optimized-add.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "EVM-OPTIMIZED-ADD",
            "--sort",
            "Input",
            "--expression",
            "optimized-add",
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
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn krun_executes_invalid_ecdsa_recovery_to_empty_bytes() {
    let expected = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortBytes{}, SortKItem{}}(\\dv{SortBytes{}}(\"\")), dotk{}())),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))\n",
        ")\n",
    );
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("crypto-execution.k");
    let program = fixtures.join("ecdsa-invalid.crypto");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "CRYPTO-EXECUTION",
            "--sort",
            "Input",
            program.to_str().unwrap(),
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
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn krun_executes_fresh_constant_fixture_to_pinned_kore_result() {
    let expected = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortInt{}, SortKItem{}}(\\dv{SortInt{}}(\"0\")), dotk{}())),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"1\"))\n",
        ")\n",
    );
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("fresh-constants.k");
    let program = fixtures.join("fresh.input");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "FRESH-CONSTANTS",
            "--sort",
            "Input",
            program.to_str().unwrap(),
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
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn krun_executes_float_fixture_to_pinned_kore_results() {
    fn scalar_result(sort: &str, value: &str) -> String {
        if sort == "Float" {
            return format!(
                concat!(
                    "Lbl'-LT-'generatedTop'-GT-'{{}}(\n",
                    "  Lbl'-LT-'k'-GT-'{{}}(\n",
                    "    kseq{{}}(inj{{SortFloat{{}}, SortKItem{{}}}}(\\dv{{SortFloat{{}}}}(\"{value}\")), dotk{{}}())\n",
                    "  ),\n",
                    "  Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\"))\n",
                    ")\n",
                ),
                value = value,
            );
        }
        format!(
            concat!(
                "Lbl'-LT-'generatedTop'-GT-'{{}}(\n",
                "  Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{Sort{sort}{{}}, SortKItem{{}}}}(\\dv{{Sort{sort}{{}}}}(\"{value}\")), dotk{{}}())),\n",
                "  Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\"))\n",
                ")\n",
            ),
            sort = sort,
            value = value,
        )
    }

    let cases = [
        (
            "float-add.float",
            scalar_result("Float", "3.75000000e+00p24x8"),
        ),
        (
            "float-round-tie.float",
            scalar_result("Float", "1.00000000e+00p24x8"),
        ),
        (
            "float-sqrt.float",
            scalar_result("Float", "2.00000000e+00p24x8"),
        ),
        (
            "float-min-zero.float",
            scalar_result("Float", "-0e+00p24x8"),
        ),
        ("float-nan-eq.float", scalar_result("Bool", "false")),
        ("float2int-tie.float", scalar_result("Int", "12")),
        (
            "float-max-value.float",
            scalar_result("Float", "3.40282347e+38p24x8"),
        ),
    ];
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("float-execution.k");

    for (program, expected) in cases {
        let program_path = fixtures.join(program);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "FLOAT-EXECUTION",
                "--sort",
                "Input",
                program_path.to_str().unwrap(),
                "--depth",
                "10",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            expected,
            "{program}"
        );
    }
}
