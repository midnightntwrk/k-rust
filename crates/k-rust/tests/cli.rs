#![cfg(feature = "cli")]

use std::{
    collections::BTreeSet,
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

use k_rust::kore::{ast::Pattern, parser::parse_definition, parser::parse_pattern};
use regex::Regex;

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

/// Compiles `rule` over the semcast grammar and returns `definition.kore`.
fn compiled_semcast_kore(rule: &str, checked: bool) -> String {
    let (root, definition) = fixture();
    let source = include_str!("fixtures/reference/inner/semcast3/test.k")
        .replace("  rule bar(X:Big) => foo(X) ~> a(X)", rule);
    fs::write(&definition, source).unwrap();
    let compiled = root.join("compiled");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .args(["kcompile", definition.to_str().unwrap(), "-m", "TEST", "-o"])
        .arg(&compiled);
    if checked {
        command.env("KRUST_TYPE_INFERENCE_MODE", "checked");
    }
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{rule}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let kore = fs::read_to_string(compiled.join("definition.kore")).unwrap();
    fs::remove_dir_all(root).unwrap();
    kore
}

/// A semantic cast `X:Big` placed after the occurrence that narrows X to Small compiles X at
/// Small at every occurrence, injected upward into Big under `bar`, never downward.
#[test]
fn kcompile_keeps_the_inferred_sort_of_a_variable_under_a_later_semantic_cast() {
    let mut rules = vec![("  rule foo(X) ~> bar(X:Big) => .K", false)];
    #[cfg(feature = "z3-inference")]
    rules.extend([
        ("  rule foo(X) ~> bar(X:Big) => .K", true),
        ("  rule a(X) ~> bar(X:Big) => .K", false),
        ("  rule a(X) ~> bar(X:Big) => .K", true),
    ]);
    for (rule, checked) in rules {
        let kore = compiled_semcast_kore(rule, checked);
        assert!(
            !kore.contains("inj{SortBig{}, SortSmall{}}"),
            "{rule} (checked: {checked}) has a downward injection:\n{kore}"
        );
        assert!(
            !kore.contains("VarX:SortBig{}"),
            "{rule} (checked: {checked}) gives X the sort Big:\n{kore}"
        );
        assert!(
            kore.contains("Lblbar{}(inj{SortSmall{}, SortBig{}}(VarX:SortSmall{}))"),
            "{rule} (checked: {checked}):\n{kore}"
        );
    }
}

#[test]
fn runnable_compiled_artifact_is_equivalent_and_validated() {
    let (root, definition) = fixture();
    let definition_source = r#"
module MAIN
  syntax Input ::= "zero" | "twice" "(" Input ")" [macro]
  rule twice(I:Input) => I
  context alias [input]: HERE requires isInput(HOLE)
  configuration <top><k> $PGM:Input </k><env> $ENV:Input </env></top>
endmodule
"#;
    fs::write(&definition, definition_source).unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap(), "-m", "MAIN", "-o"])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    for name in [
        "runtime.json",
        "frontend.json",
        "execution.json",
        "definition.kore",
    ] {
        assert!(compiled.join(name).is_file(), "missing {name}");
    }
    assert!(!compiled.join("parsed.json").exists());

    let source = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "-m",
            "MAIN",
            "-s",
            "Input",
            "-e",
            "twice(zero)",
            "-c",
            "ENV=twice(zero)",
            "--search-final",
            "--pattern",
            "<k> ?K:K </k>",
        ])
        .output()
        .unwrap();
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    fs::remove_file(&definition).unwrap();
    let artifact = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "twice(zero)",
            "-c",
            "ENV=twice(zero)",
            "--search-final",
            "--pattern",
            "<k> ?K:K </k>",
        ])
        .output()
        .unwrap();
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(artifact.stdout, source.stdout);

    fs::write(&definition, definition_source).unwrap();
    let compiled_again = root.join("compiled-again");
    let repeated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap(), "-m", "MAIN", "-o"])
        .arg(&compiled_again)
        .output()
        .unwrap();
    assert!(
        repeated.status.success(),
        "{}",
        String::from_utf8_lossy(&repeated.stderr)
    );
    for name in [
        "runtime.json",
        "frontend.json",
        "execution.json",
        "definition.kore",
    ] {
        assert_eq!(
            fs::read(compiled.join(name)).unwrap(),
            fs::read(compiled_again.join(name)).unwrap(),
            "nondeterministic {name}"
        );
    }

    let frontend = fs::read(compiled.join("frontend.json")).unwrap();
    let manifest = fs::read(compiled.join("runtime.json")).unwrap();
    fs::write(compiled.join("frontend.json"), "corrupt").unwrap();
    let corrupt = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(!corrupt.status.success());
    let stderr = String::from_utf8(corrupt.stderr).unwrap();
    assert!(stderr.contains("failed SHA-256 validation"), "{stderr}");
    assert!(stderr.contains("fresh runnable artifact"), "{stderr}");

    fs::write(compiled.join("frontend.json"), frontend).unwrap();

    // The execution definition is decoded only to compile a search pattern: a payload that
    // passes its digest check but does not decode fails the run that reads it, not every run.
    let execution = fs::read(compiled.join("execution.json")).unwrap();
    let undecodable = b"{}";
    let mut rehashed: serde_json::Value = serde_json::from_slice(&manifest).unwrap();
    rehashed["execution"]["sha256"] = {
        use sha2::{Digest, Sha256};
        Sha256::digest(undecodable)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
            .into()
    };
    fs::write(compiled.join("execution.json"), undecodable).unwrap();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&rehashed).unwrap(),
    )
    .unwrap();
    let without_pattern = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
            "-c",
            "ENV=zero",
        ])
        .output()
        .unwrap();
    assert!(
        without_pattern.status.success(),
        "{}",
        String::from_utf8_lossy(&without_pattern.stderr)
    );
    let with_pattern = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
            "-c",
            "ENV=zero",
            "--search-final",
            "--pattern",
            "<k> ?K:K </k>",
        ])
        .output()
        .unwrap();
    assert!(!with_pattern.status.success());
    let stderr = String::from_utf8(with_pattern.stderr).unwrap();
    assert!(
        stderr.contains("runnable artifact payload `execution.json` is corrupt"),
        "{stderr}"
    );
    assert!(stderr.contains("fresh runnable artifact"), "{stderr}");
    fs::write(compiled.join("execution.json"), execution).unwrap();

    let mut incompatible: serde_json::Value = serde_json::from_slice(&manifest).unwrap();
    incompatible["version"] = 2.into();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&incompatible).unwrap(),
    )
    .unwrap();
    let version = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&version.stderr).contains("unsupported runnable artifact version"),
        "{}",
        String::from_utf8_lossy(&version.stderr)
    );

    incompatible["version"] = 1.into();
    incompatible["backend"] = "llvm".into();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&incompatible).unwrap(),
    )
    .unwrap();
    let backend = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&backend.stderr).contains("is not executable by the Rust backend"),
        "{}",
        String::from_utf8_lossy(&backend.stderr)
    );

    fs::remove_file(compiled.join("runtime.json")).unwrap();
    let partial = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&partial.stderr).contains("manifest")
            && String::from_utf8_lossy(&partial.stderr).contains("missing or unreadable"),
        "{}",
        String::from_utf8_lossy(&partial.stderr)
    );
}

fn output_with_stdin(command: &mut Command, input: &[u8]) -> Output {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

fn captured_output_command(compiled: &Path, expression: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        expression,
        "--output",
        "captured",
    ]);
    command
}

fn compiled_live_io_fixture() -> (PathBuf, PathBuf) {
    let fixture_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/live-io/test.k");
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixture_path.to_str().unwrap(),
            "--main-module",
            "LIVE-IO",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    (root, compiled)
}

fn live_io_command(compiled: &Path, expression: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        expression,
        "--io",
        "on",
        "--output",
        "none",
    ]);
    command
}

fn pattern_binding<'a>(pattern: &'a Pattern, variable_name: &str) -> Option<&'a Pattern> {
    match pattern {
        Pattern::Equals { left, right, .. } => match (left.as_ref(), right.as_ref()) {
            (Pattern::Variable(variable), value) if variable.name == variable_name => Some(value),
            (value, Pattern::Variable(variable)) if variable.name == variable_name => Some(value),
            _ => None,
        },
        Pattern::And { arguments, .. } => arguments
            .iter()
            .find_map(|argument| pattern_binding(argument, variable_name)),
        _ => None,
    }
}

fn exit_reference_fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/exit")
}

fn stdin_delimiter_run_command() -> (Command, PathBuf) {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixtures = manifest.join("tests/fixtures/reference/execution/stdin-delimiter-run");
    let builtin = manifest
        .join("../..")
        .join("k/k-distribution/include/kframework/builtin");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("cb19.k").to_str().unwrap(),
        fixtures.join("three.cb19").to_str().unwrap(),
        "--main-module",
        "CB19",
        "--syntax-module",
        "CB19-SYNTAX",
        "--sort",
        "Stmt",
        "-I",
        fixtures.to_str().unwrap(),
        "--builtin-directory",
        builtin.to_str().unwrap(),
        "--io",
        "off",
    ]);
    (command, fixtures)
}

fn exit_krun_command() -> Command {
    let fixtures = exit_reference_fixtures();
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .arg("krun")
        .arg(fixtures.join("test.k"))
        .arg(fixtures.join("program.pgm"))
        .args([
            "--main-module",
            "EXIT",
            "--syntax-module",
            "EXIT",
            "--sort",
            "Int",
        ]);
    command
}

fn compiled_exit_fixture() -> (PathBuf, PathBuf, PathBuf) {
    let (root, _) = fixture();
    let fixtures = exit_reference_fixtures();
    let compiled = root.join("compiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(fixtures.join("test.k"))
        .args([
            "--main-module",
            "EXIT",
            "--syntax-module",
            "EXIT",
            "--backend",
            "rust",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let initial = root.join("initial.kore");
    let output = exit_krun_command().args(["--depth", "0"]).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::write(&initial, output.stdout).unwrap();
    (root, compiled.join("definition.kore"), initial)
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
fn krun_uses_main_module_macros_for_syntax_and_configuration_inputs() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module COMMON
  syntax Hidden
  syntax Input ::= Hidden
  syntax Input ::= "done" [symbol(done)]
                 | "programMacro" [macro, symbol(programMacro)]
                 | "configMacro" [macro, symbol(configMacro)]
                 | "hiddenMacro" [macro, symbol(hiddenMacro)]
                 | "hiddenConditional" [macro, symbol(hiddenConditional)]
endmodule

module SYNTAX
  imports COMMON
endmodule

module MACROS
  imports COMMON
  syntax Hidden ::= "$hidden" [token]
  rule configMacro => done
  rule hiddenMacro => $hidden
  rule hiddenConditional => done requires true
endmodule

module MAIN
  imports COMMON
  imports MACROS
  syntax Input ::= "wrapped" [symbol(mainWrap)]
  rule programMacro => wrapped
  configuration <k> $PGM:Input </k>
                <state parser="STATE, SYNTAX"> $STATE:Input </state>
                <local parser="LOCAL, SYNTAX"> $LOCAL:Input </local>
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
            "--syntax-module",
            "SYNTAX",
            "--sort",
            "Input",
            "--expression",
            "programMacro",
            "-c",
            "STATE=configMacro",
            "-c",
            "LOCAL=hiddenMacro",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "SYNTAX",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let artifact = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "--sort",
            "Input",
            "--expression",
            "programMacro",
            "-c",
            "STATE=configMacro",
            "-c",
            "LOCAL=hiddenMacro",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(artifact.stdout, output.stdout);
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(!output.contains("LblprogramMacro"), "{output}");
    assert!(!output.contains("LblconfigMacro"), "{output}");
    assert!(!output.contains("LblhiddenMacro"), "{output}");
    assert!(
        output.contains("LblmainWrap{}()"),
        "expected a main-only application on a macro RHS to survive expansion: {output}"
    );
    assert!(
        output.contains("Lbldone{}()"),
        "expected the configuration input to expand: {output}"
    );
    assert!(
        output.contains(r#"\dv{SortHidden{}}("$hidden")"#),
        "expected the macro module's private token to survive expansion: {output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_rejects_a_macro_symbol_that_survives_expansion() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax Input ::= "stuck" [macro, symbol(stuckMacro)]
  configuration <k> $PGM:Input </k>
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
            "Input",
            "--expression",
            "stuck",
            "--depth",
            "1",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("invalid executable input"), "{error}");
    assert!(error.contains("LblstuckMacro"), "{error}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_parses_programs_with_the_selected_syntax_module() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module SELECTED-SYNTAX
  syntax Input ::= "go" [symbol(selectedGo)]
endmodule

module ALTERNATE-SYNTAX
  syntax Input ::= "go" [symbol(alternateGo)]
endmodule

module MAIN
  imports SELECTED-SYNTAX
  imports ALTERNATE-SYNTAX
  configuration <k> $PGM:Input </k>
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
            "--syntax-module",
            "SELECTED-SYNTAX",
            "--sort",
            "Input",
            "--expression",
            "go",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("LblselectedGo"), "{stdout}");
    assert!(!stdout.contains("LblalternateGo"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_parses_configuration_variables_with_the_main_module() {
    // reference: k/result/bin/krun 1.pgm --definition ref -cENV='two()' --output kore
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/cfg");
    let expected = fs::read_to_string(fixtures.join("config-main.kore")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join("1.pgm").to_str().unwrap(),
            "--main-module",
            "CFG",
            "--syntax-module",
            "CFG-SYNTAX",
            "--sort",
            "Pgm",
            "-cENV=two()",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let result = r#"\dv{SortInt{}}("3")"#;
    assert!(expected.contains(result), "reference fixture: {expected}");
    assert!(stdout.contains(result), "{stdout}");
}

#[test]
fn reference_krun_defaults_the_program_grammar_to_the_syntax_module() {
    // reference: k/result/bin/krun two.pgm --definition ref -cENV=1 exits 113
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/cfg");
    assert_eq!(
        fs::read_to_string(fixtures.join("program-reject.exit")).unwrap(),
        "113\n"
    );
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join("two.pgm").to_str().unwrap(),
            "--main-module",
            "CFG",
            "--sort",
            "Pgm",
            "-cENV=1",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success(), "program unexpectedly parsed");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("could not parse program as Pgm"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn reference_krun_honours_the_configuration_cell_parser_attribute() {
    // reference: k/result/bin/krun go.pgm --definition parser-ref -cENV=selected --output kore
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/cfg");
    let expected = fs::read_to_string(fixtures.join("parser-config.kore")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("parser.k").to_str().unwrap(),
            fixtures.join("go.pgm").to_str().unwrap(),
            "--main-module",
            "PARSER",
            "--sort",
            "Pgm",
            "-cENV=selected",
            "--depth",
            "0",
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
        expected.contains("LblselectedEnv"),
        "reference fixture: {expected}"
    );
    assert!(stdout.contains("LblselectedEnv"), "{stdout}");

    let rejected = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("parser.k").to_str().unwrap(),
            fixtures.join("go.pgm").to_str().unwrap(),
            "--main-module",
            "PARSER",
            "--sort",
            "Pgm",
            "-cENV=main",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        !rejected.status.success(),
        "the per-cell parser unexpectedly accepted main-module-only syntax"
    );
}

#[test]
fn krun_warns_when_the_default_syntax_module_is_missing() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "ready" [symbol(ready)]
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
            "ready",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "Could not find main syntax module with name MAIN-SYNTAX in definition.  Use --syntax-module to specify one. Using MAIN as default."
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("Lblready"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_at_kitem_matches_krun_at_the_concrete_sort() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/inner/programs/cast-kitem");
    let definition = fixtures.join("test.k");
    let program = fixtures.join("1.test");
    let run = |sort: &str| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                program.to_str().unwrap(),
                "--main-module",
                "TEST",
                "--syntax-module",
                "TEST",
                "--sort",
                sort,
                "--depth",
                "10",
            ])
            .output()
            .unwrap()
    };

    let concrete = run("Int");
    assert!(
        concrete.status.success(),
        "{}",
        String::from_utf8_lossy(&concrete.stderr)
    );
    let at_kitem = run("KItem");
    assert!(
        at_kitem.status.success(),
        "{}",
        String::from_utf8_lossy(&at_kitem.stderr)
    );
    assert_eq!(at_kitem.stdout, concrete.stdout);
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
fn krun_runs_a_definition_that_declares_no_program_variable() {
    // K regression-new issue-946: `krun --definition test-kompiled` with no positional
    // argument runs a configuration without `$PGM`; the reference builds the initial
    // configuration from an empty variable map instead of reading standard input.
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= "start" [symbol(start)]
  configuration <k> start </k> <env> 1 </env>
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
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lblstart{}()"), "{stdout}");
    assert!(stdout.contains("\\dv{SortInt{}}(\"1\")"), "{stdout}");
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
fn reference_fun_with_an_uncast_variable_executes_on_an_empty_user_list() {
    // reference: k/result/bin/kompile --backend haskell test.k && k/result/bin/krun program.pgm
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/kompile/fun-int-list-config");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "FUN-INT-LIST-CONFIG",
            "--syntax-module",
            "FUN-INT-LIST-CONFIG",
            "--sort",
            "KItem",
            fixtures.join("program.pgm").to_str().unwrap(),
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
    assert!(!output.contains("Hash'lambda"), "{output}");
    assert!(!output.contains(r"\ceil"), "{output}");
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
fn reference_krun_supplies_io_and_stdin_for_stream_cells() {
    // reference: k/result/bin/krun program.pgm --definition ref --output kore </dev/null
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let expected =
        parse_pattern(&fs::read_to_string(fixtures.join("default.kore")).unwrap()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(parse_pattern(&stdout).unwrap(), expected);
    assert!(!stdout.contains(r"\bottom"), "{stdout}");
}

#[test]
fn krun_captured_output_emits_one_complete_stdout_buffer_without_kore_framing() {
    let fixture_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/captured-output/test.k");
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixture_path.to_str().unwrap(),
            "--main-module",
            "CAPTURED-OUTPUT",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let literal = output_with_stdin(&mut captured_output_command(&compiled, "literal"), b"");
    assert!(
        literal.status.success(),
        "{}",
        String::from_utf8_lossy(&literal.stderr)
    );
    assert_eq!(literal.stdout, b"literal output");
    assert!(
        literal.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&literal.stderr)
    );

    let empty = output_with_stdin(&mut captured_output_command(&compiled, "empty"), b"");
    assert!(
        empty.status.success(),
        "{}",
        String::from_utf8_lossy(&empty.stderr)
    );
    assert!(empty.stdout.is_empty());

    let from_stdin = output_with_stdin(
        &mut captured_output_command(&compiled, "stdin"),
        b"piped input\n",
    );
    assert!(
        from_stdin.status.success(),
        "{}",
        String::from_utf8_lossy(&from_stdin.stderr)
    );
    assert_eq!(from_stdin.stdout, b"piped input\noutput");

    let mut kore = Command::new(env!("CARGO_BIN_EXE_krust"));
    kore.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        "literal",
        "--io",
        "off",
    ]);
    let kore = output_with_stdin(&mut kore, b"");
    assert!(
        kore.status.success(),
        "{}",
        String::from_utf8_lossy(&kore.stderr)
    );
    let kore_text = String::from_utf8(kore.stdout).unwrap();
    assert!(parse_pattern(&kore_text).is_ok(), "{kore_text}");
    assert_ne!(kore_text.as_bytes(), literal.stdout);

    for (expression, extra, expected) in [
        ("bottom", &[][..], "found 0 leaves"),
        (
            "residual",
            &[][..],
            "found 1 leaf: constraints=1, stdout stream buffers=1",
        ),
        ("branch", &["--strategy", "all"][..], "found 2 leaves"),
    ] {
        let mut command = captured_output_command(&compiled, expression);
        command.args(extra);
        let output = output_with_stdin(&mut command, b"");
        assert!(!output.status.success(), "{expression}");
        assert!(output.stdout.is_empty(), "{expression}");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains(
                "captured output requires exactly one execution leaf, unconstrained and with exactly one stdout stream buffer"
            ),
            "{expression}: {stderr}"
        );
        assert!(stderr.contains(expected), "{expression}: {stderr}");
    }

    let mut explicit_on = captured_output_command(&compiled, "literal");
    explicit_on.args(["--io", "on"]);
    let explicit_on = explicit_on.output().unwrap();
    assert!(!explicit_on.status.success());
    assert!(explicit_on.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&explicit_on.stderr).contains(
            "--output captured uses buffered stream semantics and cannot be combined with --io on"
        ),
        "{}",
        String::from_utf8_lossy(&explicit_on.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_delivers_committed_transitions_once_without_kore_framing() {
    let (root, compiled) = compiled_live_io_fixture();

    let output = output_with_stdin(&mut live_io_command(&compiled, "multi"), b"");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"first second");
    assert!(output.stderr.is_empty());

    let mut mixed = Command::new(env!("CARGO_BIN_EXE_krust"));
    mixed.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        "multi",
        "--io",
        "on",
    ]);
    let mixed = output_with_stdin(&mut mixed, b"");
    assert!(!mixed.status.success());
    assert!(mixed.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&mixed.stderr).contains(
            "use --output none so program output remains separate from KORE result rendering"
        ),
        "{}",
        String::from_utf8_lossy(&mixed.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_keeps_stderr_and_empty_stdout_writes_separate_from_kore_stdout() {
    let (root, compiled) = compiled_live_io_fixture();

    for (expression, expected_stderr) in [
        ("stderr-only", b"stderr only".as_slice()),
        ("empty-stdout", b"after empty stdout".as_slice()),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "--sort",
            "Pgm",
            "--expression",
            expression,
            "--io",
            "on",
        ]);
        let output = output_with_stdin(&mut command, b"");

        assert!(
            output.status.success(),
            "{expression}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stderr, expected_stderr, "{expression}");
        let result = String::from_utf8(output.stdout).unwrap();
        assert!(parse_pattern(&result).is_ok(), "{expression}: {result}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_preserves_descriptor_order_and_arbitrary_bytes() {
    let (root, compiled) = compiled_live_io_fixture();

    let ordered = output_with_stdin(&mut live_io_command(&compiled, "ordered"), b"");
    assert!(
        ordered.status.success(),
        "{}",
        String::from_utf8_lossy(&ordered.stderr)
    );
    assert_eq!(ordered.stdout, b"out-1out-2");
    assert_eq!(ordered.stderr, b"err-1!");

    let combined_path = root.join("combined-output");
    let combined = fs::File::create(&combined_path).unwrap();
    let mut combined_command = live_io_command(&compiled, "ordered");
    let mut child = combined_command
        .stdin(Stdio::null())
        .stdout(Stdio::from(combined.try_clone().unwrap()))
        .stderr(Stdio::from(combined))
        .spawn()
        .unwrap();
    assert!(child.wait().unwrap().success());
    assert_eq!(fs::read(&combined_path).unwrap(), b"out-1err-1out-2!");

    let bytes = [0xff, 0x80, 0x00, b'A'];
    let arbitrary = output_with_stdin(&mut live_io_command(&compiled, "bytes"), &bytes);
    assert!(
        arbitrary.status.success(),
        "{}",
        String::from_utf8_lossy(&arbitrary.stderr)
    );
    assert_eq!(arbitrary.stdout, bytes);
    assert!(arbitrary.stderr.is_empty());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_prebuffers_input_and_withholds_rejected_candidate_output() {
    let (root, compiled) = compiled_live_io_fixture();

    let input = output_with_stdin(&mut live_io_command(&compiled, "input"), b"A");
    assert!(
        input.status.success(),
        "{}",
        String::from_utf8_lossy(&input.stderr)
    );
    assert_eq!(input.stdout, b"accepted");
    assert!(input.stderr.is_empty());

    let rollback = output_with_stdin(&mut live_io_command(&compiled, "rollback"), b"");
    assert!(rollback.status.success());
    assert!(rollback.stdout.is_empty());
    assert!(
        !rollback
            .stderr
            .windows(b"leaked".len())
            .any(|part| part == b"leaked")
    );
    assert!(
        String::from_utf8_lossy(&rollback.stderr).contains("execution ended with no successor")
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_rejects_search_and_alternative_execution() {
    let (root, compiled) = compiled_live_io_fixture();

    let mut search = live_io_command(&compiled, "branch");
    search.arg("--search-final");
    let search = output_with_stdin(&mut search, b"");
    assert!(!search.status.success());
    assert!(search.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&search.stderr)
            .contains("--io on is supported only for ordinary execution, not search")
    );

    // Both alternatives have empty transcripts. The mode is rejected before execution rather
    // than relying on transcript selection to notice a conflict.
    let mut alternatives = live_io_command(&compiled, "branch-empty");
    alternatives.args(["--strategy", "all"]);
    let alternatives = output_with_stdin(&mut alternatives, b"");
    assert!(!alternatives.status.success());
    assert!(alternatives.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&alternatives.stderr).contains("--io on requires --strategy any")
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_io_off_feeds_standard_input_into_stdin() {
    // reference: printf 'ab\n' | k/result/bin/krun program.pgm --definition ref --io off
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let expected = parse_pattern(&fs::read_to_string(fixtures.join("off.kore")).unwrap()).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("io.k").to_str().unwrap(),
        fixtures.join("program.pgm").to_str().unwrap(),
        "--main-module",
        "IO",
        "--sort",
        "Int",
        "--depth",
        "0",
        "--io",
        "off",
    ]);
    let output = output_with_stdin(&mut command, b"ab\n");

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap(),
        expected
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr)
            .contains("reading standard input into $STDIN until end of file"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn reference_krun_io_off_reads_single_delimiters() {
    let (mut command, fixtures) = stdin_delimiter_run_command();
    let input = fs::read(fixtures.join("single.in")).unwrap();
    let output = output_with_stdin(&mut command, &input);

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stdout.contains(r#"\dv{SortString{}}("241")"#), "{stdout}");
    assert!(
        !stderr.contains("execution ended with no successor"),
        "{stderr}"
    );
}

#[test]
fn reference_krun_io_off_reports_undefined_delimiter_runs() {
    for input in ["runs.in", "leading.in"] {
        let (mut command, fixtures) = stdin_delimiter_run_command();
        let output = output_with_stdin(&mut command, &fs::read(fixtures.join(input)).unwrap());

        assert!(
            output.status.success(),
            "{input}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            "\\bottom{SortGeneratedTopCell{}}()\n"
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("rule STDIN-STREAM.stdinParseInt applied with an undefined result"),
            "{input}: {stderr}"
        );
        assert!(stderr.contains("refuted obligation"), "{input}: {stderr}");
        assert!(stderr.contains("String2Int"), "{input}: {stderr}");
        assert!(
            stderr.contains(r#"(\dv{SortString{}}(""))"#),
            "{input}: {stderr}"
        );
    }
}

#[test]
fn reference_krun_io_off_surface_pattern_reads_closed_stdin() {
    // reference: printf 'ab\n' | k/result/bin/krun program.pgm --definition ref --io off
    //   --depth 0 --pattern '<k> KK:K </k>' --output kore
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("io.k").to_str().unwrap(),
        fixtures.join("program.pgm").to_str().unwrap(),
        "--main-module",
        "IO",
        "--sort",
        "Int",
        "--depth",
        "0",
        "--io",
        "off",
        "--pattern",
        "<k> KK:K </k>",
    ]);
    let output = output_with_stdin(&mut command, b"ab\n");

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let expected_binding =
        parse_pattern(r#"kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("5")), dotk{}())"#)
            .unwrap();
    assert_eq!(
        pattern_binding(&actual, "VarKK"),
        Some(&expected_binding),
        "{actual:?}"
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr)
            .contains("reading standard input into $STDIN until end of file"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn krun_accepts_explicit_stdin_and_io_overrides() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
            "-cIO=\"off\"",
            "-cSTDIN=\"x\"",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortString{}}("x")"#), "{stdout}");
    assert_eq!(stdout.matches(r#"\dv{SortString{}}("off")"#).count(), 2);
}

#[test]
fn krun_search_defaults_io_off() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
            "--search-final",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortString{}}("off")"#), "{stdout}");
    assert!(!stdout.contains(r#"\dv{SortString{}}("on")"#), "{stdout}");
}

#[test]
fn krun_io_off_preserves_non_utf8_stdin_bytes() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("io.k").to_str().unwrap(),
        fixtures.join("program.pgm").to_str().unwrap(),
        "--main-module",
        "IO",
        "--sort",
        "Int",
        "--depth",
        "0",
        "--io",
        "off",
    ]);
    let output = output_with_stdin(&mut command, &[b'x', 0x80]);

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains(r#"\dv{SortString{}}("x\x80\n")"#)
    );
}

/// K's krun builds `$STDIN` under `--io off` from `$(</dev/stdin)` fed through a bash
/// here-string into its escaping awk script (krun:557-558): the command substitution strips
/// every trailing newline, the here-string appends one, and awk emits every record with `ORS`.
/// The buffered text is therefore standard input with its trailing newlines replaced by exactly
/// one, also when standard input is empty (`#buffer("\n")` in regression-new/imp++-llvm
/// div.imp.out; `printf 'ab' | krun ... --io off` gives `"ab\n"` in
/// tests/fixtures/reference/cli/io/off.kore). Interior newlines and other bytes are kept.
#[test]
fn krun_io_off_buffers_stdin_in_the_reference_here_string_shape() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let cases: [(&[u8], &[&str], &str); 5] = [
        (b"", &["--io", "off"], r#"\dv{SortString{}}("\n")"#),
        (b"", &["--search-final"], r#"\dv{SortString{}}("\n")"#),
        (b"ab", &["--io", "off"], r#"\dv{SortString{}}("ab\n")"#),
        (
            b"ab\n\n\n",
            &["--io", "off"],
            r#"\dv{SortString{}}("ab\n")"#,
        ),
        (
            b"a\r\n\nb\n",
            &["--io", "off"],
            r#"\dv{SortString{}}("a\r\n\nb\n")"#,
        ),
    ];
    for (input, mode, expected) in cases {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
        ]);
        command.args(mode);
        let output = output_with_stdin(&mut command, input);

        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.contains(expected),
            "stdin {input:?} under {mode:?} must buffer {expected}:\n{stdout}"
        );
    }
}

#[test]
fn krun_warns_when_the_initial_configuration_is_bottom() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [function, symbol(fail)]
  rule fail(_:Int) => #Bottom
  configuration <k> fail($PGM:Int) </k>
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
            "0",
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
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "warning: the initial configuration simplified to \\bottom before any rewrite step; check the configuration variables"
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_reports_when_the_first_semantic_rewrite_is_bottom() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [symbol(fail)]
  rule fail(_:Int) => #Bottom [label(fail)]
  configuration <k> fail($PGM:Int) </k>
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
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr)
            .contains("the initial configuration simplified to \\bottom"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "execution ended with no successor at depth 1: rule fail applied with an undefined result; refuted obligation"
        ),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_reports_the_rule_that_precedes_a_vacuous_path() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax State ::= "a" | "b"
  configuration <k> $PGM:State </k>
  rule a => b [label(step)]
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--backend",
            "rust",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let initial = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        initial.status.success(),
        "{}",
        String::from_utf8_lossy(&initial.stderr)
    );
    let initial_term = String::from_utf8(initial.stdout).unwrap();
    let constrained = format!(
        r#"\and{{SortGeneratedTopCell{{}}}}(
  {},
  \and{{SortGeneratedTopCell{{}}}}(
    \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(
      Lbl'UndsEqlsEqls'Int'Unds'{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
      \dv{{SortBool{{}}}}("true")
    ),
    \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(
      Lbl'UndsEqlsSlshEqls'Int'Unds'{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
      \dv{{SortBool{{}}}}("true")
    )
  )
)"#,
        initial_term.trim()
    );
    let initial_path = root.join("vacuous.kore");
    fs::write(&initial_path, constrained).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            compiled.join("definition.kore").to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            initial_path.to_str().unwrap(),
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
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains(
            "execution ended with no successor at depth 1: rule step applied with a false path constraint; refuted obligation"
        ),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_exits_with_the_exit_cell_value_and_prints_the_final_pattern() {
    let output = exit_krun_command().output().unwrap();

    assert_eq!(output.status.code(), Some(7));
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lbl'-LT-'exit'-GT-'{}"), "{stdout}");
    assert!(stdout.contains(r#"\dv{SortInt{}}("7")"#), "{stdout}");
}

#[test]
fn reference_kore_exec_exits_with_the_exit_cell_value() {
    let (root, definition, initial) = compiled_exit_fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "EXIT",
            "--pattern",
            initial.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(7));
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains(r#"\dv{SortInt{}}("7")"#)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_exits_zero_without_an_exit_cell() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  configuration <k> $PGM:Int </k>
  rule <k> _:Int => .K </k>
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
            "--syntax-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "7",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

fn divergent_exit_fixture() -> (PathBuf, PathBuf) {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  configuration <k> $PGM:Int </k> <exit exit=""> 0 </exit>
  rule <k> N:Int => .K </k> <exit> _ => N </exit>
  rule <k> N:Int => .K </k> <exit> _ => N +Int 1 </exit>
endmodule
"#,
    )
    .unwrap();
    (root, definition)
}

fn divergent_exit_krun(definition: &Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "7",
        ])
        .args(extra)
        .output()
        .unwrap()
}

#[test]
fn krun_exits_111_on_divergent_exit_values_when_exploring_all_rules() {
    let (root, definition) = divergent_exit_fixture();
    let output = divergent_exit_krun(&definition, &["--strategy", "all", "--io", "off"]);

    assert_eq!(output.status.code(), Some(111));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("7")"#), "{stdout}");
    assert!(stdout.contains(r#"\dv{SortInt{}}("8")"#), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_exits_with_the_first_rules_exit_value_by_default() {
    // K's krun follows one successor per step: the first applicable rule by priority and
    // definition order (the LLVM backend's choice; kore-exec `--strategy any`), so the second
    // rule never fires and the exit cell holds the first rule's value.
    let (root, definition) = divergent_exit_fixture();
    let output = divergent_exit_krun(&definition, &[]);

    assert_eq!(output.status.code(), Some(7));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("7")"#), "{stdout}");
    assert!(!stdout.contains(r#"\dv{SortInt{}}("8")"#), "{stdout}");
    assert!(!stdout.contains("\\or{"), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_exits_111_on_a_symbolic_exit_value() {
    let (root, definition, initial) = compiled_exit_fixture();
    let concrete = r#"Lbl'-LT-'exit'-GT-'{}(\dv{SortInt{}}("0"))"#;
    let symbolic = "Lbl'-LT-'exit'-GT-'{}(VarExit:SortInt{})";
    let initial_source = fs::read_to_string(&initial).unwrap();
    assert!(initial_source.contains(concrete), "{initial_source}");
    fs::write(&initial, initial_source.replacen(concrete, symbolic, 1)).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "EXIT",
            "--pattern",
            initial.to_str().unwrap(),
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(111));
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("VarExit:SortInt{}")
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_exits_zero_regardless_of_the_exit_cell() {
    let output = exit_krun_command().arg("--search-final").output().unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!output.stdout.is_empty());
}

#[test]
fn krun_bottom_final_with_an_exit_cell_exits_111() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [function, symbol(fail)]
  rule fail(_:Int) => #Bottom
  configuration <k> fail($PGM:Int) </k> <exit exit=""> 0 </exit>
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
            "--syntax-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "7",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(111));
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "\\bottom{SortGeneratedTopCell{}}()\n"
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
fn krun_follows_the_first_rule_by_default_and_explores_with_strategy_all() {
    let (root, definition) = branching_search_fixture();
    let krun = |extra: &[&str]| {
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
            .args(extra)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    };

    // Default: one successor per step, the first rule `c => d` by definition order.
    let output = krun(&[]);
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lble'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );
    assert!(!output.contains("\\or{"), "{output}");

    // `--strategy all` explores both rules and prints both final configurations.
    let output = krun(&["--strategy", "all", "--io", "off"]);
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");

    // `--execute-to-branch` stops at the branch point that `--strategy all` exposes.
    let output = krun(&["--strategy", "all", "--execute-to-branch", "--io", "off"]);
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
fn krun_preserves_source_rule_order_across_kore_emission_sorting() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" | "d" | "e"
  configuration <k> $PGM:State </k>
  rule a => e
  rule a => d
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
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lbld'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_heats_a_strict_production_in_one_order_by_default_and_search_enumerates_both() {
    // Two unevaluated arguments of a `strict` production have two heating rules with equal
    // priority. K's krun (LLVM backend; kore-exec `--strategy any`) heats the first argument
    // and follows that single successor, so the pending frontier stays one state per step;
    // exploring both orders is exponential in the number of such heatings and is what
    // `--search` is for.
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module STRICT-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | Exp "+" Exp [strict] | "(" Exp ")" [bracket]
endmodule

module STRICT
  imports STRICT-SYNTAX
  imports INT
  syntax KResult ::= Int
  configuration <k> $PGM:Exp </k>
  rule I1:Int + I2:Int => I1 +Int I2
endmodule
"#,
    )
    .unwrap();
    let krun = |extra: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "STRICT",
                "--syntax-module",
                "STRICT-SYNTAX",
                "--sort",
                "Exp",
                "--expression",
                "(1 + 2) + (3 + 4)",
            ])
            .args(extra)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    };
    let first_argument_heated = "'Unds'Exp0'Unds'{}(";
    let second_argument_heated = "'Unds'Exp1'Unds'{}(";

    // One step: exactly one configuration, the left argument heated (its freezer holds `3 + 4`).
    let output = krun(&["--depth", "1"]);
    assert!(!output.contains("\\or{"), "{output}");
    assert!(output.contains(first_argument_heated), "{output}");
    assert!(!output.contains(second_argument_heated), "{output}");

    // The whole run reaches the single final value.
    let output = krun(&[]);
    assert!(!output.contains("\\or{"), "{output}");
    assert!(output.contains(r#"\dv{SortInt{}}("10")"#), "{output}");

    // Control: search still enumerates both heating orders.
    let output = krun(&["--search-one-step"]);
    assert!(output.contains("\\or{"), "{output}");
    assert!(output.contains(first_argument_heated), "{output}");
    assert!(output.contains(second_argument_heated), "{output}");

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

fn run_branching_surface_pattern(definition: &Path, pattern: &str, extra: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        definition.to_str().unwrap(),
        "--main-module",
        "MAIN",
        "--syntax-module",
        "MAIN",
        "--sort",
        "State",
        "--expression",
        "a",
        "--pattern",
        pattern,
    ]);
    command.args(extra).output().unwrap()
}

#[test]
fn krun_surface_pattern_projects_ordinary_final_states() {
    let (root, definition) = branching_search_fixture();

    let matching = run_branching_surface_pattern(&definition, "<k> d </k>", &[]);
    assert!(
        matching.status.success(),
        "{}",
        String::from_utf8_lossy(&matching.stderr)
    );
    assert!(matches!(
        parse_pattern(&String::from_utf8(matching.stdout).unwrap()).unwrap(),
        Pattern::Top { .. }
    ));

    let nonmatching = run_branching_surface_pattern(&definition, "<k> e </k>", &[]);
    assert!(
        nonmatching.status.success(),
        "{}",
        String::from_utf8_lossy(&nonmatching.stderr)
    );
    assert!(matches!(
        parse_pattern(&String::from_utf8(nonmatching.stdout).unwrap()).unwrap(),
        Pattern::Bottom { .. }
    ));

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_projects_every_strategy_all_final_state() {
    let (root, definition) = branching_search_fixture();

    let output = run_branching_surface_pattern(
        &definition,
        "<k> S:State </k>",
        &["--strategy", "all", "--io", "off"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("\\or{"), "{output}");
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_routes_through_each_explicit_search_mode() {
    let (root, definition) = branching_search_fixture();
    for (mode, pattern) in [
        ("--search-final", "<k> d </k>"),
        ("--search-all", "<k> a </k>"),
        ("--search-one-step", "<k> b </k>"),
        ("--search-one-or-more-steps", "<k> c </k>"),
    ] {
        let output = run_branching_surface_pattern(&definition, pattern, &[mode, "--depth", "10"]);
        assert!(
            output.status.success(),
            "{mode}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
        assert!(matches!(output, Pattern::Top { .. }), "{mode}: {output:?}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_filters_only_generated_anonymous_bindings() {
    let (root, definition) = branching_search_fixture();

    let named = run_branching_surface_pattern(&definition, "<k> S:State </k>", &[]);
    assert!(
        named.status.success(),
        "{}",
        String::from_utf8_lossy(&named.stderr)
    );
    let named = String::from_utf8(named.stdout).unwrap();
    assert!(named.contains("VarS:SortState{}"), "{named}");

    let anonymous = run_branching_surface_pattern(&definition, "<k> _ </k>", &[]);
    assert!(
        anonymous.status.success(),
        "{}",
        String::from_utf8_lossy(&anonymous.stderr)
    );
    assert!(matches!(
        parse_pattern(&String::from_utf8(anonymous.stdout).unwrap()).unwrap(),
        Pattern::Top { .. }
    ));

    let authored = run_branching_surface_pattern(&definition, "<k> _Gen0:State </k>", &[]);
    assert!(
        authored.status.success(),
        "{}",
        String::from_utf8_lossy(&authored.stderr)
    );
    let authored = String::from_utf8(authored.stdout).unwrap();
    assert!(authored.contains("Var'Unds'Gen0:SortState{}"), "{authored}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_preserves_the_ordinary_exit_code() {
    let output = exit_krun_command()
        .args(["--pattern", "<k> 999 </k>"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(7));
    assert!(matches!(
        parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap(),
        Pattern::Bottom { .. }
    ));
}

#[test]
fn krun_surface_pattern_reports_command_line_parse_locations() {
    let (root, definition) = branching_search_fixture();
    let output = run_branching_surface_pattern(&definition, "<k>", &[]);

    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("<command line>"), "{stderr}");
    // The incomplete cell fails at EOF, immediately after the opening tag.
    assert!(stderr.contains("1:4"), "{stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_symbolic_depth_two_leaves_match_gotstuck_selection() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/symbolic-depth-bound");
    let (root, _) = fixture();
    let compiled = root.join("symbolic-depth-bound-kompiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "SD",
            "--syntax-module",
            "SD-SYNTAX",
            "--backend",
            "rust",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let execute = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            compiled.join("definition.kore").to_str().unwrap(),
            "--module",
            "SD",
            "--pattern",
            fixtures.join("symbolic.kore").to_str().unwrap(),
            "--depth",
            "2",
        ])
        .output()
        .unwrap();
    assert!(
        execute.status.success(),
        "{}",
        String::from_utf8_lossy(&execute.stderr)
    );

    let disjuncts = |mut pattern| match &mut pattern {
        Pattern::Or { arguments, .. } => std::mem::take(arguments),
        _ => vec![pattern],
    };
    let reference = disjuncts(
        parse_pattern(&fs::read_to_string(fixtures.join("depth-two.kore")).unwrap()).unwrap(),
    );
    let actual = disjuncts(parse_pattern(&String::from_utf8(execute.stdout).unwrap()).unwrap());
    assert_eq!(reference.len(), 2, "the reference records two stuck leaves");
    assert_eq!(
        actual.len(),
        reference.len(),
        "the port must drop depth-bounded leaves when the traversal gets stuck"
    );
    for expected in reference {
        assert!(
            actual.contains(&expected),
            "missing reference remainder leaf: {expected:#?}"
        );
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_applies_rewrite_rules_tagged_concrete_and_symbolic() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/concrete-symbolic-rules");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "CO",
            "--syntax-module",
            "CO-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("concrete-input.pgm").to_str().unwrap(),
            "--depth",
            "2",
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
        stdout.contains("Lblh'LParUndsRParUnds'CO-SYNTAX'Unds'Pgm'Unds'Int"),
        "{stdout}"
    );
}

#[test]
fn krun_search_final_reports_states_cut_by_the_depth_bound() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/symbolic-depth-bound");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "SD",
            "--syntax-module",
            "SD-SYNTAX",
            "--sort",
            "Pgm",
            "--expression",
            "count(5)",
            "--search-final",
            "--depth",
            "2",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("3")"#), "{stdout}");
    assert!(!stdout.contains(r"\bottom"), "{stdout}");
}

#[test]
fn kore_exec_merges_converging_final_states() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/branching-execution");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "BR",
            "--syntax-module",
            "BR-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("start.pgm").to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lble'Unds'BR-SYNTAX'Unds'Pgm"), "{stdout}");
    assert!(!stdout.contains(r"\or{"), "{stdout}");
}

#[test]
fn krun_reports_bottom_when_the_only_matching_rule_has_a_false_ensures() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/trivial-result-execution");
    let run = |search: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "TR",
            "--syntax-module",
            "TR-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("false-ensures.pgm").to_str().unwrap(),
        ]);
        if search {
            command.arg("--search-final");
        }
        command.output().unwrap()
    };

    for search in [false, true] {
        let output = run(search);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.contains(r"\bottom{SortGeneratedTopCell{}}()"),
            "search={search}: {stdout}"
        );
        assert!(
            !stdout.contains("Lblc'Unds'TR-SYNTAX'Unds'Pgm"),
            "search={search}: {stdout}"
        );
    }
}

#[test]
fn reference_hook_string_index_boundaries_follow_domains_md() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/hooks/string-index-boundaries");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("string-index-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOKS",
            "--syntax-module",
            "HOOKS-SYNTAX",
            "--sort",
            "Pgm",
            fixtures
                .join("string-index-boundaries.hooks")
                .to_str()
                .unwrap(),
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

    let expected = fs::read_to_string(fixtures.join("domains.out"))
        .unwrap()
        .lines()
        .filter_map(|line| {
            let value = line.trim().strip_prefix("ListItem ( ")?;
            let value = value
                .strip_suffix(" ) ~> .K")
                .or_else(|| value.strip_suffix(" )"))?;
            value.parse::<i64>().ok()
        })
        .collect::<Vec<_>>();
    let integer = Regex::new(r#"\\dv\{SortInt\{\}\}\(\"(-?[0-9]+)\"\)"#).unwrap();
    let actual = integer
        .captures_iter(&String::from_utf8(output.stdout).unwrap())
        .take(expected.len())
        .map(|captures| captures[1].parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(expected, vec![2, 3, 5, -1, 0]);
    assert_eq!(actual, expected);
}

#[test]
fn krun_executes_hook_edges_to_the_backend_results() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/hooks");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("hook-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOK-BOUNDARIES",
            "--syntax-module",
            "HOOK-BOUNDARIES-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("edges.hooks").to_str().unwrap(),
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
    let bool_value = Regex::new(r#"\\dv\{SortBool\{\}\}\(\"(true|false)\"\)"#).unwrap();
    let int_value = Regex::new(r#"\\dv\{SortInt\{\}\}\(\"(-?[0-9]+)\"\)"#).unwrap();
    let string_value = Regex::new(r#"\\dv\{SortString\{\}\}\(\"([^\"]*)\"\)"#).unwrap();

    let bools = bool_value
        .captures_iter(&stdout)
        .map(|captures| captures[1].parse::<bool>().unwrap())
        .collect::<Vec<_>>();
    let ints = int_value
        .captures_iter(&stdout)
        .take(4)
        .map(|captures| captures[1].parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    let strings = string_value
        .captures_iter(&stdout)
        .map(|captures| captures[1].to_owned())
        .collect::<Vec<_>>();

    assert_eq!(bools, vec![false, false, false], "{stdout}");
    assert_eq!(ints, vec![1, 3, 65_533, 0], "{stdout}");
    assert_eq!(strings, vec!["he"], "{stdout}");
}

#[test]
fn krun_reports_an_unsupported_hook_with_a_nonzero_exit() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/hooks");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("hook-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOK-BOUNDARIES",
            "--syntax-module",
            "HOOK-BOUNDARIES-SYNTAX",
            "--sort",
            "Pgm",
            fixtures
                .join("unsupported-bytes-memset.hooks")
                .to_str()
                .unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("unsupported hook 'BYTES.memset'"),
        "{stderr}"
    );
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
fn search_bound_stops_a_catch_all_over_an_infinite_result_stream() {
    fn flatten_disjuncts<'a>(pattern: &'a Pattern, disjuncts: &mut Vec<&'a Pattern>) {
        match pattern {
            Pattern::Or { arguments, .. } => {
                for argument in arguments {
                    flatten_disjuncts(argument, disjuncts);
                }
            }
            pattern => disjuncts.push(pattern),
        }
    }

    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/search-pattern/infinite-result.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "INFINITE-RESULT",
            "--syntax-module",
            "INFINITE-RESULT-SYNTAX",
            "--sort",
            "State",
            "--expression",
            "loop(z)",
            "--search-final",
            "--search-bound",
            "5",
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
    let result = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let mut disjuncts = Vec::new();
    flatten_disjuncts(&result, &mut disjuncts);
    assert_eq!(disjuncts.len(), 5);
    let mut successor_counts = disjuncts
        .iter()
        .map(|disjunct| disjunct.to_string().matches("Lbls{}(").count())
        .collect::<Vec<_>>();
    successor_counts.sort_unstable();
    assert_eq!(successor_counts, [0, 1, 2, 3, 4]);
}

#[test]
fn krun_search_all_prints_disjuncts_in_a_deterministic_order() {
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/branching-order.k");
    let run = |search_type: &str| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "BR",
                "--syntax-module",
                "BR-SYNTAX",
                "--sort",
                "Pgm",
                "--expression",
                "a",
                "--depth",
                "10",
                search_type,
            ])
            .output()
            .unwrap()
    };
    let assert_order = |stdout: &str, labels: &[&str]| {
        let positions = labels
            .iter()
            .map(|label| {
                stdout
                    .find(&format!("Lbl{label}'Unds'BR-SYNTAX'Unds'Pgm"))
                    .unwrap_or_else(|| panic!("missing {label:?} in {stdout}"))
            })
            .collect::<Vec<_>>();
        assert!(
            positions.windows(2).all(|pair| pair[0] < pair[1]),
            "labels {labels:?} were not ordered in {stdout}"
        );
    };

    let all = run("--search-all");
    assert!(
        all.status.success(),
        "{}",
        String::from_utf8_lossy(&all.stderr)
    );
    assert_order(
        &String::from_utf8(all.stdout).unwrap(),
        &["a", "b", "c", "d", "zz"],
    );

    let final_states = run("--search-final");
    assert!(
        final_states.status.success(),
        "{}",
        String::from_utf8_lossy(&final_states.stderr)
    );
    assert_order(
        &String::from_utf8(final_states.stdout).unwrap(),
        &["c", "d", "zz"],
    );
}

#[test]
fn krun_search_final_decides_result_predicates_for_ground_overloaded_lists() {
    fn collect_result_bindings(pattern: &Pattern, bindings: &mut Vec<Pattern>) {
        match pattern {
            Pattern::And { arguments, .. } => {
                for argument in arguments {
                    collect_result_bindings(argument, bindings);
                }
            }
            Pattern::Equals { left, right, .. } => {
                let variable = match (left.as_ref(), right.as_ref()) {
                    (Pattern::Variable(variable), _) | (_, Pattern::Variable(variable)) => variable,
                    _ => panic!("unexpected residual constraint in search result: {pattern:#?}"),
                };
                if variable.name == "VarS" {
                    bindings.push(pattern.clone());
                } else {
                    assert!(
                        variable.name.starts_with("Var'Unds'Gen"),
                        "unexpected binding in search result: {pattern:#?}"
                    );
                }
            }
            _ => panic!("unexpected residual constraint in search result: {pattern:#?}"),
        }
    }

    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/simple-print");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join("nondeterministic.cb11").to_str().unwrap(),
            "--main-module",
            "SIMPLE-PRINT",
            "--syntax-module",
            "SIMPLE-PRINT-SYNTAX",
            "--sort",
            "Stmt",
            "--search-final",
            "--pattern",
            r#"<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>"#,
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut result = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let disjuncts = match &mut result {
        Pattern::Or { arguments, .. } => std::mem::take(arguments),
        _ => vec![result],
    };
    let mut actual = Vec::new();
    for disjunct in &disjuncts {
        let before = actual.len();
        collect_result_bindings(disjunct, &mut actual);
        assert_eq!(
            actual.len(),
            before + 1,
            "each disjunct must contain exactly one S binding: {disjunct:#?}"
        );
    }
    actual.sort();

    let mut expected = ["1\\n", "2\\n"]
        .map(|value| {
            parse_pattern(&format!(
                r#"\equals{{SortString{{}}, SortGeneratedTopCell{{}}}}(VarS:SortString{{}}, \dv{{SortString{{}}}}("{value}"))"#
            ))
            .unwrap()
        })
        .to_vec();
    expected.sort();
    assert_eq!(actual, expected);
}

#[test]
fn krun_owise_decides_distinct_ground_overloaded_list_shapes() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/overloaded-list-owise");
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "OVERLOADED-LIST-OWISE",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    for (expression, expected) in [("nil-cons", "2"), ("one-cons", "2"), ("cons-nil", "1")] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                "--definition",
                compiled.to_str().unwrap(),
                "--sort",
                "Pgm",
                "--expression",
                expression,
                "--depth",
                "20",
                "--strategy",
                "all",
                "--io",
                "off",
                "--pattern",
                "<k> V:Int </k>",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{expression}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = String::from_utf8(output.stdout).unwrap();
        assert!(
            matches!(parse_pattern(&output).unwrap(), Pattern::Equals { .. }),
            "{expression}: {output}"
        );
        assert!(
            output.contains(&format!(r#"\dv{{SortInt{{}}}}("{expected}")"#)),
            "{expression}: {output}"
        );
        assert!(!output.contains(r"\or{"), "{expression}: {output}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_bound_returns_a_subset_of_the_unbounded_solutions() {
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/branching-order.k");
    let run = |bound: Option<&str>| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "BR",
            "--syntax-module",
            "BR-SYNTAX",
            "--sort",
            "Pgm",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-all",
        ]);
        if let Some(bound) = bound {
            command.args(["--search-bound", bound]);
        }
        command.output().unwrap()
    };
    let labels = ["a", "b", "c", "d", "zz"];
    let members = |stdout: &str| {
        labels
            .iter()
            .copied()
            .filter(|label| stdout.contains(&format!("Lbl{label}'Unds'BR-SYNTAX'Unds'Pgm")))
            .collect::<BTreeSet<_>>()
    };

    let unbounded = run(None);
    assert!(
        unbounded.status.success(),
        "{}",
        String::from_utf8_lossy(&unbounded.stderr)
    );
    let unbounded = members(&String::from_utf8(unbounded.stdout).unwrap());
    assert_eq!(unbounded, labels.into_iter().collect());

    let bounded = run(Some("2"));
    assert!(
        bounded.status.success(),
        "{}",
        String::from_utf8_lossy(&bounded.stderr)
    );
    let stderr = String::from_utf8(bounded.stderr).unwrap();
    assert!(
        stderr.contains("search stopped at the requested result bound"),
        "{stderr}"
    );
    let bounded = members(&String::from_utf8(bounded.stdout).unwrap());
    assert_eq!(bounded.len(), 2);
    assert!(bounded.is_subset(&unbounded));
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

/// Kore/Parser/Lexer.x:57-58: `@ident = [a-zA-Z][a-zA-Z0-9'\-]*`, set variables prefixed by `@`.
fn is_kore_identifier(name: &str) -> bool {
    let name = name.strip_prefix('@').unwrap_or(name);
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic())
        && characters.all(|character| character.is_ascii_alphanumeric() || "'-".contains(character))
}

fn variable_names(pattern: &Pattern, names: &mut Vec<String>) {
    match pattern {
        Pattern::Variable(variable) => names.push(variable.name.clone()),
        Pattern::Exists { variable, body, .. } | Pattern::Forall { variable, body, .. } => {
            names.push(variable.name.clone());
            variable_names(body, names);
        }
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                variable_names(argument, names);
            }
        }
        Pattern::Not { argument, .. } | Pattern::Ceil { argument, .. } => {
            variable_names(argument, names);
        }
        Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. }
        | Pattern::Implies { left, right, .. } => {
            variable_names(left, names);
            variable_names(right, names);
        }
        _ => {}
    }
}

/// Symbolic collection frame narrowing mints `Ex#Frame!0`; the reference prints its own remainder as
/// `VarAC1'Unds'1:SortMap{}` (kore-exec on the same fixture), a plain KORE identifier.
#[test]
fn kore_exec_prints_fresh_remainder_names_as_kore_identifiers() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/matching/map");
    let (root, _) = fixture();
    let compiled = root.join("map-kompiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "TEST",
            "--syntax-module",
            "TEST",
            "--backend",
            "rust",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let execute = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            compiled.join("definition.kore").to_str().unwrap(),
            "--module",
            "TEST",
            "--pattern",
            fixtures.join("pgm-map.kore").to_str().unwrap(),
            "--depth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        execute.status.success(),
        "{}",
        String::from_utf8_lossy(&execute.stderr)
    );
    let output = String::from_utf8(execute.stdout).unwrap();
    let parsed = parse_pattern(&output).unwrap_or_else(|error| panic!("{output}\n{error:?}"));
    let mut names = Vec::new();
    variable_names(&parsed, &mut names);
    names.sort();
    names.dedup();
    assert!(
        names.iter().all(|name| is_kore_identifier(name)),
        "{names:?}"
    );
    assert!(names.contains(&"ExFrame0".to_owned()), "{names:?}");
    assert!(names.contains(&"VarM".to_owned()), "{names:?}");
    assert_eq!(parse_pattern(&parsed.to_string()).unwrap(), parsed);

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

    let stop_leaves = root.join("stop-leaves.kore");
    let bounded = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--depth",
            "1",
            "--stop-leaves",
            stop_leaves.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        bounded.status.success(),
        "{}",
        String::from_utf8_lossy(&bounded.stderr)
    );
    let stop_leaves = fs::read_to_string(stop_leaves).unwrap();
    assert!(stop_leaves.contains("b{}()"), "{stop_leaves}");
    assert!(stop_leaves.contains("c{}()"), "{stop_leaves}");
    assert!(!stop_leaves.contains("d{}()"), "{stop_leaves}");
    assert!(!stop_leaves.contains("e{}()"), "{stop_leaves}");

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
    // Equal priority: any follows the first applicable rule in definition.kore declaration
    // order, a-to-b before a-to-c, so the single successor chain ends at d.
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
fn kore_exec_executes_every_disjunct_of_the_initial_pattern() {
    let (root, _) = fixture();
    let definition = root.join("disjunctive-definition.kore");
    let program = root.join("disjunctive-program.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol left{}() : SortS{} [constructor{}()]
  symbol right{}() : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(\and{SortS{}}(a{}(),\top{SortS{}}()), left{}()) [label{}("left-step")]
  axiom{} \rewrites{SortS{}}(\and{SortS{}}(b{}(),\top{SortS{}}()), right{}()) [label{}("right-step")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&program, r#"\or{SortS{}}(a{}(), b{}())"#).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
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
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("left{}()"), "{stdout}");
    assert!(stdout.contains("right{}()"), "{stdout}");

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
  symbol state{}(SortState{}) : SortState{} [function{}(), injective{}(), total{}()]
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
fn reference_pattern_files_are_verified_before_internalization() {
    // reference: k/result/bin/kore-parser ok.kore --module M --pattern dv.kore --verify
    let root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/definition");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            root.join("ok.kore").to_str().unwrap(),
            "--module",
            "M",
            "--pattern",
            root.join("dv.kore").to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("hasDomainValues"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
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
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
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
    assert_eq!(output["condition"]["witnesses"]["term"]["tag"], "Top");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_implies_follows_the_reference_special_case_matrix() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
endmodule []
"#,
    )
    .unwrap();
    let bottom = root.join("bottom.kore");
    let top = root.join("top.kore");
    let regular = root.join("regular.kore");
    fs::write(&bottom, r#"\bottom{SortS{}}()"#).unwrap();
    fs::write(&top, r#"\top{SortS{}}()"#).unwrap();
    fs::write(&regular, "a{}()").unwrap();

    let cases = [
        (&bottom, &bottom, "valid", "Bottom"),
        (&bottom, &top, "valid", "Bottom"),
        (&bottom, &regular, "valid", "Bottom"),
        (&regular, &bottom, "invalid", "Bottom"),
        (&regular, &top, "valid", "Top"),
        (&regular, &regular, "valid", "Top"),
    ];
    for (antecedent, consequent, status, predicate) in cases {
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
            "{} => {}: {}",
            antecedent.display(),
            consequent.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(output["status"], status, "{output:#}");
        assert_eq!(
            output["condition"]["predicate"]["term"]["tag"], predicate,
            "{output:#}"
        );
        assert_eq!(
            output["condition"]["substitution"]["term"]["tag"], "Top",
            "{output:#}"
        );
        assert_eq!(
            output["condition"]["witnesses"]["term"]["tag"], "Top",
            "{output:#}"
        );
    }

    for consequent in [&bottom, &top, &regular] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kore-implies",
                definition.to_str().unwrap(),
                "--module",
                "MAIN",
                "--antecedent",
                top.to_str().unwrap(),
                "--consequent",
                consequent.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("function-like"),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_implies_rejects_a_syntactic_sort_mismatch_before_internalization() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let antecedent = root.join("antecedent.kore");
    let consequent = root.join("consequent.kore");
    fs::write(
        &definition,
        "[]\nmodule MAIN\n  sort SortA{} []\n  sort SortB{} []\nendmodule []\n",
    )
    .unwrap();
    fs::write(&antecedent, r#"\bottom{SortA{}}()"#).unwrap();
    fs::write(&consequent, r#"\top{SortB{}}()"#).unwrap();

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

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("antecedent and consequent sorts differ: SortA{} and SortB{}"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
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

fn modal_claim_fixture() -> (PathBuf, PathBuf, PathBuf) {
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
    (root, definition, saved_proofs)
}

#[test]
fn kprove_proves_a_modal_claim_in_process() {
    let (root, definition, saved_proofs) = modal_claim_fixture();

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

/// The modal claim fixture prepared once with `kcompile --for-proving`, so that a `kprove`
/// child loads the compiled KORE instead of compiling the definition and its prelude.
fn compiled_modal_claim_fixture() -> (PathBuf, PathBuf) {
    let (root, definition, _) = modal_claim_fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            compiled.to_str().unwrap(),
            "--for-proving",
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    (root, compiled)
}

#[test]
fn kprove_reports_closed_stdout_as_io_error() {
    let (root, compiled) = compiled_modal_claim_fixture();
    // Exercise trusted reporting, an executed proof, and an unproven result. Each child reaches
    // its first report line, where the closed pipe surfaces, after loading the compiled
    // definition; nothing is compiled behind the dead stdout.
    for options in [
        ["--trusted", "reaches-b-or-c"],
        ["--depth", "10"],
        ["--depth", "0"],
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                "--compiled-definition",
                compiled.to_str().unwrap(),
            ])
            .args(["--main-module", "MAIN", "--claim", "reaches-b-or-c"])
            .args(options)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        drop(child.stdout.take().unwrap());

        // The child holds no pipe it could block on: stdout is closed and stderr is drained
        // here, so the wait has no deadline.
        let output = child.wait_with_output().unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert_eq!(output.status.code(), Some(1), "{options:?}: {stderr}");
        assert!(stderr.contains("error:"), "{options:?}: {stderr}");
        assert!(
            stderr.to_lowercase().contains("pipe"),
            "{options:?}: {stderr}"
        );
        assert!(!stderr.contains("panicked"), "{options:?}: {stderr}");
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_compiles_only_a_specification_against_prepared_semantics() {
    let (root, _) = fixture();
    let timings = root.join("timings.json");
    let semantics = root.join("semantics.k");
    let specification = root.join("spec.k");
    let compiled = root.join("compiled");
    fs::write(
        &semantics,
        r#"
module SEMANTICS
  syntax State ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &specification,
        r#"
requires "semantics.k"
module SPEC
  imports SEMANTICS
  claim <k> a => b </k> [label(reaches-b)]
endmodule
"#,
    )
    .unwrap();

    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            semantics.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--output-directory",
            compiled.to_str().unwrap(),
            "--for-proving",
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    assert!(!compiled.join("runtime.json").exists());
    fs::remove_file(&semantics).unwrap();

    let load = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--load-only",
            "--timings",
            timings.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        load.status.success(),
        "{}",
        String::from_utf8_lossy(&load.stderr)
    );
    assert!(load.stdout.is_empty());
    let load_timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    assert_eq!(
        load_timings["version"],
        k_rust::timings::TIMINGS_SCHEMA_VERSION
    );
    assert!(load_timings["input_seconds"].as_f64().unwrap() > 0.0);
    assert!(load_timings["internalize_seconds"].as_f64().unwrap() > 0.0);
    assert_eq!(load_timings["proof_seconds"], 0.0);
    assert_eq!(load_timings["proof_setup_seconds"], 0.0);
    assert_eq!(load_timings["claims"], serde_json::json!([]));

    let proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--claim",
            "reaches-b",
        ])
        .output()
        .unwrap();
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    assert_eq!(
        String::from_utf8(proof.stdout).unwrap(),
        "claim reaches-b: proven (2 states, 0 unexplored)\n"
    );

    let prepared_spec = root.join("prepared-spec");
    let compile_spec = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--for-proving",
            "--output-directory",
            prepared_spec.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile_spec.status.success(),
        "{}",
        String::from_utf8_lossy(&compile_spec.stderr)
    );
    assert!(!prepared_spec.join("runtime.json").exists());
    fs::remove_file(&specification).unwrap();
    let prepared_proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            prepared_spec.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--claim",
            "reaches-b",
            "--timings",
            timings.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        prepared_proof.status.success(),
        "{}",
        String::from_utf8_lossy(&prepared_proof.stderr)
    );
    assert_eq!(
        String::from_utf8(prepared_proof.stdout).unwrap(),
        "claim reaches-b: proven (2 states, 0 unexplored)\n"
    );
    let proof_timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    assert_eq!(
        proof_timings["version"],
        k_rust::timings::TIMINGS_SCHEMA_VERSION
    );
    assert!(proof_timings["proof_setup_seconds"].as_f64().unwrap() > 0.0);
    assert!(proof_timings["proof_seconds"].as_f64().unwrap() > 0.0);
    assert_eq!(proof_timings["claims"][0]["label"], "reaches-b");
    assert_eq!(proof_timings["claims"][0]["status"], "proven");
    assert_eq!(
        proof_timings["claims"][0]["seconds"],
        proof_timings["proof_seconds"]
    );

    let bounded = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            prepared_spec.join("definition.kore").to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--depth",
            "0",
            "--timings",
            timings.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!bounded.status.success());
    let bounded_timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    assert_ne!(bounded_timings["claims"][0]["status"], "proven");
    assert_eq!(bounded_timings["claims"][0]["label"], "reaches-b");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_keeps_definition_and_spec_markdown_selectors_distinct() {
    let (root, _) = fixture();
    let semantics = root.join("semantics.md");
    let specification = root.join("spec.md");
    let reread_specification = root.join("reread-spec.md");
    let compiled = root.join("compiled");
    let definition_selector = "(k|keep) & !discard";
    fs::write(
        &semantics,
        r#"
```k
requires "domains.md"
module SEMANTICS
  imports INT
  syntax State ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <k> $PGM:State </k>
```
```keep
  rule <k> a => b </k>
```
```discard
  rule <k> b => a </k>
```
```k
endmodule
```
"#,
    )
    .unwrap();
    fs::write(
        &specification,
        r#"
```keep
module SPEC
  imports SEMANTICS
  claim <k> a => b </k> [label(reaches-b)]
  claim <k> b => b </k> [label(stays-b)]
endmodule
```
```discard
module DISCARDED imports MISSING-DISCARDED endmodule
```
```k
module WRONG-SELECTOR imports MISSING-K endmodule
```
"#,
    )
    .unwrap();
    fs::write(
        &reread_specification,
        r#"
```k
requires "semantics.md"
module REREAD-SPEC
  imports SEMANTICS
  claim <k> b => b </k> [label(reloads-identical-semantics)]
endmodule
```
"#,
    )
    .unwrap();

    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            semantics.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--md-selector",
            definition_selector,
            "--for-proving",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            "keep&!(discard|k)",
        ])
        .output()
        .unwrap();
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    let stdout = String::from_utf8(proof.stdout).unwrap();
    assert!(stdout.contains("claim reaches-b: proven"), "{stdout}");
    assert!(stdout.contains("claim stays-b: proven"), "{stdout}");

    let without_prepared = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            "keep&!(discard|k)",
        ])
        .output()
        .unwrap();
    assert!(!without_prepared.status.success());
    assert!(
        String::from_utf8_lossy(&without_prepared.stderr)
            .contains("imports missing module \"SEMANTICS\"")
    );

    let same_selector = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            reread_specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "REREAD-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            definition_selector,
        ])
        .output()
        .unwrap();
    assert!(
        same_selector.status.success(),
        "{}",
        String::from_utf8_lossy(&same_selector.stderr)
    );

    let changed_selector = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            reread_specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "REREAD-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            "k",
        ])
        .output()
        .unwrap();
    assert!(!changed_selector.status.success());
    let stderr = String::from_utf8_lossy(&changed_selector.stderr);
    assert!(
        stderr.contains("differs from previous declaration"),
        "{stderr}"
    );
    assert!(
        stderr.contains("This can happen if --md-selector differs for kompile and kprove"),
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_rejects_unsupported_prepared_manifest_versions() {
    let (root, definition) = fixture();
    let compiled = root.join("compiled");
    fs::create_dir_all(&compiled).unwrap();
    fs::write(
        compiled.join("krust.json"),
        r#"{"format":"krust-prepared-definition","version":999,"sources":[]}"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "-m",
            "MAIN",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("unsupported prepared definition manifest")
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_loads_a_new_spec_module_from_the_semantics_entry_file() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module SEMANTICS
  syntax State ::= "a" | "b"
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
module SPEC
  imports SEMANTICS
  claim <k> a => b </k> [label(reaches-b)]
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "-m",
            "SEMANTICS",
            "--for-proving",
            "-o",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let parsed = fs::read_to_string(compiled.join("parsed.json")).unwrap();
    let base = k_rust::definition::json::from_str(&parsed).unwrap();
    assert!(!base.modules.iter().any(|module| module.name == "SPEC"));
    let proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "-m",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
        ])
        .output()
        .unwrap();
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    assert!(String::from_utf8_lossy(&proof.stdout).contains("claim reaches-b: proven"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_claim_selection_does_not_use_unselected_lemmas() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("lemma-spec.k");

    let isolated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "LEMMA-SPEC",
            "--definition-module",
            "SPLIT",
            "--claim",
            "ca",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let isolated_stdout = String::from_utf8(isolated.stdout).unwrap();
    assert!(!isolated.status.success(), "{isolated_stdout}");
    assert!(
        isolated_stdout.contains("claim LEMMA-SPEC.ca: disproved"),
        "{isolated_stdout}"
    );

    let batch = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "LEMMA-SPEC",
            "--definition-module",
            "SPLIT",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let batch_stdout = String::from_utf8(batch.stdout).unwrap();
    assert!(!batch.status.success(), "{batch_stdout}");
    assert!(
        batch_stdout.contains("claim LEMMA-SPEC.ca: proven"),
        "{batch_stdout}"
    );
    assert!(
        batch_stdout.contains("claim LEMMA-SPEC.cb: disproved"),
        "{batch_stdout}"
    );
}

#[test]
fn kprove_filters_claims_imported_into_the_specification_module() {
    // reference (k/result/bin, split.k kompiled with --backend haskell, imported-spec.k with
    // --depth 10): --exclude SPLIT-LEMMAS.fail1 --exclude SPLIT-LEMMAS.fail2 exits 0 (#Top);
    // --trusted SPLIT-LEMMAS.fail1 --trusted SPLIT-LEMMAS.fail2 exits 0 (#Top); no flags exits 1
    // stuck on fail1 (imported-spec.k:5); excluding all three claims exits 113 with kore-exec's
    // "Unexpected empty set of claims." (Kore/Exec.hs:989). Recorded in split/reference.toml.
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("imported-spec.k");
    let (root, _) = fixture();
    let compiled_semantics = root.join("semantics");
    let compiled_spec = root.join("specification");
    let timings = root.join("timings.json");
    for (source, module, destination) in [
        (fixtures.join("split.k"), "SPLIT", &compiled_semantics),
        (specification.clone(), "IMPORTED-SPEC", &compiled_spec),
    ] {
        let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kcompile")
            .arg(source)
            .args([
                "--main-module",
                module,
                "--definition-module",
                "SPLIT",
                "--for-proving",
            ])
            .arg("--output-directory")
            .arg(destination)
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
    }
    for input in [
        vec![specification.to_str().unwrap()],
        vec![
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled_semantics.to_str().unwrap(),
        ],
        vec!["--compiled-definition", compiled_spec.to_str().unwrap()],
    ] {
        let mut common = vec!["kprove"];
        common.extend(input);
        common.extend([
            "--main-module",
            "IMPORTED-SPEC",
            "--definition-module",
            "SPLIT",
            "--depth",
            "10",
        ]);

        let excluded = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .args(["--exclude", "fail1", "--exclude", "SPLIT-LEMMAS.fail2"])
            .output()
            .unwrap();
        assert!(
            excluded.status.success(),
            "{}{}",
            String::from_utf8_lossy(&excluded.stdout),
            String::from_utf8_lossy(&excluded.stderr)
        );
        assert_eq!(
            String::from_utf8(excluded.stdout).unwrap(),
            "claim SPLIT-LEMMAS.pass: proven (3 states, 0 unexplored)\n"
        );

        let trusted = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .args(["--trusted", "fail1", "--trusted", "fail2"])
            .arg("--timings")
            .arg(&timings)
            .output()
            .unwrap();
        assert!(
            trusted.status.success(),
            "{}{}",
            String::from_utf8_lossy(&trusted.stdout),
            String::from_utf8_lossy(&trusted.stderr)
        );
        // Claims are reported in declaration order (imported-spec.k: pass, fail1, fail2).
        assert_eq!(
            String::from_utf8(trusted.stdout).unwrap(),
            "claim SPLIT-LEMMAS.pass: proven (3 states, 0 unexplored)\n\
         claim SPLIT-LEMMAS.fail1: proven (trusted)\n\
         claim SPLIT-LEMMAS.fail2: proven (trusted)\n"
        );

        let recorded: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
        let claims = recorded["claims"].as_array().unwrap();
        assert_eq!(claims.len(), 3, "{recorded}");
        for claim in &claims[1..] {
            assert_eq!(claim["status"], "trusted");
            assert_eq!(claim["seconds"], 0.0);
        }
        assert_eq!(recorded["proof_seconds"], claims[0]["seconds"]);

        // Control: without filtering every imported claim is attempted.
        let batch = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .output()
            .unwrap();
        let batch_stdout = String::from_utf8(batch.stdout).unwrap();
        assert!(!batch.status.success(), "{batch_stdout}");
        assert!(
            batch_stdout.contains("claim SPLIT-LEMMAS.pass: proven"),
            "{batch_stdout}"
        );
        for claim in ["SPLIT-LEMMAS.fail1", "SPLIT-LEMMAS.fail2"] {
            assert!(
                batch_stdout.contains(&format!("claim {claim}: disproved")),
                "{batch_stdout}"
            );
        }

        // Excluding every claim leaves the reference backend with an empty claim set, an error.
        let emptied = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .args([
                "--exclude",
                "pass",
                "--exclude",
                "fail1",
                "--exclude",
                "fail2",
            ])
            .output()
            .unwrap();
        assert!(!emptied.status.success());
        assert_eq!(String::from_utf8(emptied.stdout).unwrap(), "");
        assert!(
            String::from_utf8_lossy(&emptied.stderr)
                .contains("the selected module contains no modal reachability claims"),
            "{}",
            String::from_utf8_lossy(&emptied.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_one_path_claim_fails_on_the_uncovered_case() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("onepath-spec.k");

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "ONEPATH-SPEC",
            "--definition-module",
            "SPLIT",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert!(!output.status.success(), "{stdout}");
    // `start(I)` with `I <=Int 0` has the one successor `bad` (the two rules' conditions are
    // disjoint), which has none: no path reaches `good`, a certified refutation.
    assert!(
        stdout.contains("claim ONEPATH-SPEC.c1: disproved"),
        "{stdout}"
    );
    assert!(stdout.contains("Stuck (certified) at depth 1"), "{stdout}");
}

#[test]
fn reference_ite_bug_splits_implication_obligations_without_branching_functions() {
    // reference: kprove fixture captured under reference/implication/ite-bug/reference.log
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/implication/ite-bug");
    let (root, _) = fixture();
    fs::copy(fixtures.join("ite-bug.k"), root.join("ite-bug.k")).unwrap();
    let cases = [
        ("passing-spec.k", "PASSING-SPEC", true),
        ("failing-1-spec.k", "FAILING-1-SPEC", false),
        ("failing-2-spec.k", "FAILING-2-SPEC", false),
    ];

    for (specification, module, should_prove) in cases {
        let source = format!(
            "requires \"ite-bug.k\"\n{}",
            fs::read_to_string(fixtures.join(specification)).unwrap()
        );
        let specification_path = root.join(specification);
        fs::write(&specification_path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                specification_path.to_str().unwrap(),
                "--main-module",
                module,
                "--definition-module",
                "ITE-BUG",
                "--depth",
                "10",
            ])
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();

        assert_eq!(
            output.status.success(),
            should_prove,
            "{specification}: {stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        // The failing leaves are constrained through `bool2Word`, which has no SMT translation:
        // they are non-empty only modulo abstraction, so the claims fail without a certified
        // refutation.
        assert!(
            stdout.contains(if should_prove { "proven" } else { "failed" }),
            "{specification}: {stdout}"
        );
    }

    let nolemma = fixtures.join("nolemma");
    fs::copy(nolemma.join("ite-bug.k"), root.join("ite-bug.k")).unwrap();
    let specification = root.join("passing-nolemma-spec.k");
    fs::write(
        &specification,
        format!(
            "requires \"ite-bug.k\"\n{}",
            fs::read_to_string(nolemma.join("passing-spec.k")).unwrap()
        ),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "PASSING-SPEC",
            "--definition-module",
            "ITE-BUG",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "nolemma/passing-spec.k: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("proven"), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_rejects_claims_reached_only_through_bottom() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("trivial-spec.k");
    let common = [
        "kprove",
        specification.to_str().unwrap(),
        "--main-module",
        "TRIVIAL-SPEC",
        "--definition-module",
        "SPLIT",
        "--depth",
        "10",
    ];

    let rejected = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(common)
        .output()
        .unwrap();
    let rejected_stdout = String::from_utf8(rejected.stdout).unwrap();
    assert!(!rejected.status.success(), "{rejected_stdout}");
    // A trivial leaf is an empty set of configurations: the vacuity policy rejects it, so the
    // claim fails, but no configuration refutes it.
    for claim in ["TRIVIAL-SPEC.ct1", "TRIVIAL-SPEC.ct2"] {
        assert!(
            rejected_stdout.contains(&format!("claim {claim}: failed")),
            "{rejected_stdout}"
        );
    }
    assert!(
        rejected_stdout.contains("Trivial at depth 1"),
        "{rejected_stdout}"
    );
    assert!(
        rejected_stdout.contains(
            "the left-hand side of the claim has been simplified to bottom \
             (--allow-vacuous accepts such branches)"
        ),
        "{rejected_stdout}"
    );

    let allowed = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(common)
        .arg("--allow-vacuous")
        .output()
        .unwrap();
    let allowed_stdout = String::from_utf8(allowed.stdout).unwrap();
    assert!(allowed.status.success(), "{allowed_stdout}");
    for claim in ["TRIVIAL-SPEC.ct1", "TRIVIAL-SPEC.ct2"] {
        assert!(
            allowed_stdout.contains(&format!("claim {claim}: proven")),
            "{allowed_stdout}"
        );
    }
}

/// A destination whose condition is false on the reached state covers none of it, so the whole
/// state is a stuck leaf. It is never reported as a vacuous branch, so `--allow-vacuous` cannot
/// turn these false claims into proofs, and the leaf is the same with or without the stuck check
/// because no rule applies to it.
#[test]
fn kprove_reports_a_refuted_destination_condition_as_a_stuck_leaf() {
    let (root, _) = fixture();
    fs::write(
        root.join("exist-probe.k"),
        r#"
module EXIST-PROBE
  imports INT
  syntax State ::= "start" | st(Int, Int) | "done"
  configuration <k> $PGM:State </k>
  rule <k> start => st(!N:Int, 7) </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        root.join("exist-spec.k"),
        r#"
requires "exist-probe.k"

module EXIST-SPEC
  imports EXIST-PROBE

  claim <k> start => st(?B:Int, ?A:Int) </k> ensures ?A ==Int 8 [label(ab-false)]
endmodule
"#,
    )
    .unwrap();
    fs::write(
        root.join("cell-probe.k"),
        r#"
module CELL-PROBE
  imports INT
  syntax State ::= "start" | "middle"
  configuration <k> $PGM:State </k> <n> 0 </n>
  rule <k> start => middle </k> <n> _ => 5 </n>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        root.join("ex-spec.k"),
        r#"
requires "cell-probe.k"

module EX-SPEC
  imports CELL-PROBE

  claim <k> start => middle </k> <n> _ => ?N </n> ensures ?N ==Int 7 [label(existential-wrong)]
endmodule
"#,
    )
    .unwrap();

    // `ab-false` fails without a certified refutation: its leaf's generated counter holds the
    // unevaluated function application `Gen0 +Int 1`. The leaf of `existential-wrong` is a
    // term of constructors and integers with no constraint, a certified refutation.
    let cases = [
        (
            "exist-spec.k",
            "EXIST-SPEC",
            "EXIST-PROBE",
            "ab-false",
            "Lblst'LParUndsCommUndsRParUnds'EXIST-PROBE",
            ("failed", "Stuck at depth 1"),
        ),
        (
            "ex-spec.k",
            "EX-SPEC",
            "CELL-PROBE",
            "existential-wrong",
            "Lbl'-LT-'n'-GT-'{}(\\dv{SortInt{}}(\"5\"))",
            ("disproved", "Stuck (certified) at depth 1"),
        ),
    ];
    for (specification, module, definition_module, claim, leaf_term, (verdict, leaf)) in cases {
        for flags in [
            &[][..],
            &["--allow-vacuous"][..],
            &["--disable-stuck-check"][..],
            &["--allow-vacuous", "--disable-stuck-check"][..],
        ] {
            let output = Command::new(env!("CARGO_BIN_EXE_krust"))
                .args([
                    "kprove",
                    root.join(specification).to_str().unwrap(),
                    "--main-module",
                    module,
                    "--definition-module",
                    definition_module,
                    "--depth",
                    "10",
                    "--claim",
                    claim,
                ])
                .args(flags)
                .stdin(Stdio::null())
                .output()
                .unwrap();
            let stdout = String::from_utf8(output.stdout).unwrap();
            let context = format!(
                "{claim} {flags:?}: {stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            );

            assert!(!output.status.success(), "{context}");
            assert!(
                stdout.contains(&format!("claim {claim}: {verdict}")),
                "{context}"
            );
            let leaves = stdout
                .lines()
                .filter(|line| line.contains(" at depth "))
                .map(str::trim)
                .collect::<Vec<_>>();
            assert_eq!(leaves, [leaf], "{context}");
            assert!(stdout.contains(leaf_term), "{context}");
            assert!(!stdout.contains("simplified to bottom"), "{context}");
        }
    }
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
    assert!(
        limited.status.success(),
        "{}",
        String::from_utf8_lossy(&limited.stderr)
    );
    let output = String::from_utf8(limited.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("334")"#), "{output}");
    assert!(!output.contains("Lblinc"), "{output}");
    assert!(!output.contains("Lblfoo"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

/// `run(I) => stuck(I)` rewrites although `stuck(1)` cannot be evaluated: the rewrite carries
/// `\ceil(stuck(1))` as an obligation instead of blocking. The leaf is printed in the
/// simplifier's normal form, where that conjunct is entailed by the term (`stuck(1)` sits under
/// total symbols only, and application is strict), so the output shows the unevaluated
/// application and no `\ceil` conjunct.
#[test]
fn krun_rewrites_to_an_unevaluated_partial_application_in_normal_form() {
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
    assert!(output.contains("Lblstuck"), "{output}");
    assert!(!output.contains("Lblrun"), "{output}");
    assert!(!output.contains(r"\ceil"), "{output}");

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
            "--syntax-module",
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

#[cfg(unix)]
#[test]
fn kcompile_generates_a_relocatable_glr_program_parser() {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::fs::PermissionsExt;

    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module BISON
  syntax Number ::= r"[A-Z]+" [token]
  syntax Pgm ::= Number
               | Pgm "+" Pgm [symbol(add), group(add)]
               | Pgm "*" Pgm [symbol(mul), group(mul)]
  syntax priority mul > add
  syntax left add
  syntax left mul
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let output_name = std::ffi::OsString::from_vec(b"bison-\xff-kompiled".to_vec());
    let output_directory = root.join(&output_name);
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .current_dir(&root)
        .args([
            "kcompile",
            definition.file_name().unwrap().to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
        ])
        .arg(&output_name)
        .arg("--gen-glr-bison-parser")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let primary = output_directory.join("parser_Pgm_BISON");
    let link = output_directory.join("parser_PGM");
    assert!(primary.is_file());
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("parser_Pgm_BISON"));

    let input = root.join("input.pgm");
    fs::write(&input, "A+B*C\n").unwrap();
    let parsed = Command::new(&link).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "Lbladd{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"A\")),Lblmul{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"B\")),inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"C\"))))\n"
    );

    let original_primary = fs::read(&primary).unwrap();
    let failing_cc = root.join("failing-cc");
    fs::write(
        &failing_cc,
        "#!/bin/sh\necho controlled-cc-failure >&2\nexit 23\n",
    )
    .unwrap();
    fs::set_permissions(&failing_cc, fs::Permissions::from_mode(0o755)).unwrap();
    let failed_replacement = Command::new(env!("CARGO_BIN_EXE_krust"))
        .current_dir(&root)
        .args([
            "kcompile",
            definition.file_name().unwrap().to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
        ])
        .arg(&output_name)
        .arg("--gen-glr-bison-parser")
        .env("KRUST_CC", &failing_cc)
        .output()
        .unwrap();
    assert!(!failed_replacement.status.success());
    assert!(
        String::from_utf8_lossy(&failed_replacement.stderr)
            .contains("C compiler failed with exit code 23: controlled-cc-failure")
    );
    assert_eq!(fs::read(&primary).unwrap(), original_primary);
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("parser_Pgm_BISON"));
    assert!(fs::read_dir(&output_directory).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".krust-bison")
    }));

    let replacement = Command::new(env!("CARGO_BIN_EXE_krust"))
        .current_dir(&root)
        .args([
            "kcompile",
            definition.file_name().unwrap().to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
        ])
        .arg(&output_name)
        .args(["--gen-bison-parser", "--bison-stack-max-depth", "4321"])
        .output()
        .unwrap();
    assert!(
        replacement.status.success(),
        "{}",
        String::from_utf8_lossy(&replacement.stderr)
    );
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("parser_Pgm_BISON"));
    let parsed = Command::new(&link).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "Lbladd{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"A\")),Lblmul{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"B\")),inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"C\"))))\n"
    );

    let relocated = root.join("relocated");
    fs::rename(&output_directory, &relocated).unwrap();
    let parsed = Command::new(relocated.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kcompile_generates_a_glr_parser_shared_library() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module BISON
  syntax Number ::= r"[A-Z]+" [token]
  syntax Pgm ::= Number
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let library_directory = root.join("library-kompiled");
    let executable_directory = root.join("executable-kompiled");
    let run = |directory: &Path, extra: &[&str]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
            directory.to_str().unwrap(),
            "--gen-glr-bison-parser",
        ]);
        command.args(extra);
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    };
    run(&library_directory, &["--bison-parser-library"]);
    run(&executable_directory, &[]);

    let library_name = format!("libparser_Pgm_BISON{}", std::env::consts::DLL_SUFFIX);
    let library = library_directory.join(&library_name);
    assert!(library.is_file());
    assert!(!library_directory.join("parser_Pgm_BISON").exists());
    assert_eq!(
        fs::read_link(library_directory.join("parser_PGM")).unwrap(),
        Path::new(&library_name)
    );

    let consumer_source = root.join("consumer.c");
    let consumer = root.join("consumer");
    fs::write(
        &consumer_source,
        "#include <stdio.h>\nchar *parse_Pgm(char *, char *);\nint main(int argc, char **argv) { printf(\"%s\\n\", parse_Pgm(argv[1], NULL)); }\n",
    )
    .unwrap();
    let compiled = Command::new("cc")
        .arg(&consumer_source)
        .arg(format!("-L{}", library_directory.display()))
        .arg("-lparser_Pgm_BISON")
        .args(["-o"])
        .arg(&consumer)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let input = root.join("input.pgm");
    fs::write(&input, "ABC\n").unwrap();
    let library_path_variable = if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else {
        "LD_LIBRARY_PATH"
    };
    let from_library = Command::new(&consumer)
        .arg(&input)
        .env(library_path_variable, &library_directory)
        .output()
        .unwrap();
    assert!(
        from_library.status.success(),
        "{}",
        String::from_utf8_lossy(&from_library.stderr)
    );
    let from_executable = Command::new(executable_directory.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(from_executable.status.success());
    assert_eq!(from_library.stdout, from_executable.stdout);

    let rejected = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "BISON",
            "--output-directory",
            root.join("rejected").to_str().unwrap(),
            "--bison-parser-library",
        ])
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains(
            "--bison-parser-library requires --gen-bison-parser or --gen-glr-bison-parser"
        )
    );

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kast_gen_parser_writes_a_standalone_lr_parser() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN-SYNTAX
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[0-9]+" [token]
  syntax Pgm ::= Int
endmodule

module MAIN
  imports MAIN-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let parser = root.join("standalone-parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN-SYNTAX",
            "--sort",
            "Pgm",
            "--gen-parser",
        ])
        .arg(&parser)
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    let input = root.join("input.pgm");
    fs::write(&input, "1\n").unwrap();
    let parsed = Command::new(&parser).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "inj{SortInt{}, SortPgm{}}(\\dv{SortInt{}}(\"1\"))\n"
    );
    let kompiled = root.join("main-kompiled");
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN-SYNTAX",
            "--output-directory",
            kompiled.to_str().unwrap(),
            "--gen-bison-parser",
        ])
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let compiled_parse = Command::new(kompiled.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    let standalone_parse = Command::new(&parser).arg(&input).output().unwrap();
    assert_eq!(standalone_parse.stdout, compiled_parse.stdout);

    for invalid in [
        vec!["--gen-parser", "out", "--expression", "1"],
        vec!["--gen-parser", "--gen-glr-parser", "out"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kast",
                definition.to_str().unwrap(),
                "--module",
                "MAIN-SYNTAX",
                "--sort",
                "Pgm",
            ])
            .args(invalid)
            .output()
            .unwrap();
        assert!(!output.status.success());
    }

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kast_gen_parser_keeps_byte_string_tokens() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r##"
module TOKENS
  syntax Bytes [hook(BYTES.Bytes)]
  syntax Bytes ::= r"b[\\\"](([ !#-\\[\\]-~])|([\\\\][tnfr\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]" [token]
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]" [token]
  syntax Pgm ::= Bytes | String
endmodule
"##,
    )
    .unwrap();
    let parser = root.join("tokens-parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "TOKENS",
            "--sort",
            "Pgm",
            "--gen-parser",
        ])
        .arg(&parser)
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    for (name, source, expected) in [
        (
            "bytes.pgm",
            "b\"\\x00\\x0f\"\n",
            "inj{SortBytes{}, SortPgm{}}(\\dv{SortBytes{}}(\"\\x00\\x0f\"))\n",
        ),
        (
            "string.pgm",
            "\"text\"\n",
            "inj{SortString{}, SortPgm{}}(\\dv{SortString{}}(\"text\"))\n",
        ),
    ] {
        let input = root.join(name);
        fs::write(&input, source).unwrap();
        let parsed = Command::new(&parser).arg(&input).output().unwrap();
        assert!(
            parsed.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&parsed.stderr)
        );
        assert_eq!(
            String::from_utf8(parsed.stdout).unwrap(),
            expected,
            "{name}"
        );
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_skips_bison_tools_when_the_configuration_has_no_pgm() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module NO-PGM
  syntax Value ::= "value"
  configuration <k> value </k>
endmodule
"#,
    )
    .unwrap();
    let output_directory = root.join("no-pgm-kompiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "NO-PGM",
            "--syntax-module",
            "NO-PGM",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--gen-glr-bison-parser",
        ])
        .env("KRUST_FLEX", root.join("must-not-run-flex"))
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!output_directory.join("parser_PGM").exists());
    assert!(fs::read_dir(&output_directory).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with("parser_")
    }));

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kcompile_generates_a_bounded_left_associative_nonempty_list_parser() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module NELISTS-SYNTAX
  syntax E ::= "e" [token]
  syntax Es ::= NeList{E, ","} [symbol(es)]
  syntax Pgm ::= Es
endmodule

module NELISTS
  imports NELISTS-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let output_directory = root.join("nelists-kompiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "NELISTS",
            "--syntax-module",
            "NELISTS-SYNTAX",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--gen-glr-bison-parser",
            "--bison-lists",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let input = root.join("input.pgm");
    fs::write(&input, "e,e\n").unwrap();
    let parsed = Command::new(output_directory.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "inj{SortEs{}, SortPgm{}}(Lbles{}(Lbles{}(Lbl'Stop'List'LBraQuot'es'QuotRBra'{}(),\\dv{SortE{}}(\"e\")),\\dv{SortE{}}(\"e\")))\n"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_rejects_missing_user_syntax_module_and_warns_on_missing_default() {
    let (root, definition) = fixture();
    let run = |name: &str, arguments: &[&str]| {
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
        command.args(arguments);
        command.output().unwrap()
    };

    let explicit = run("explicit", &["--syntax-module", "FOO"]);
    assert!(!explicit.status.success());
    assert!(
        String::from_utf8_lossy(&explicit.stderr)
            .contains("Could not find main syntax module with name FOO in definition."),
        "{}",
        String::from_utf8_lossy(&explicit.stderr)
    );

    let default = run("default", &["--warnings-to-errors"]);
    assert!(!default.status.success());
    assert!(
        String::from_utf8_lossy(&default.stderr).contains(
            "Could not find main syntax module with name MAIN-SYNTAX in definition.  Use --syntax-module to specify one. Using MAIN as default."
        ),
        "{}",
        String::from_utf8_lossy(&default.stderr)
    );

    let warning = "Could not find main syntax module with name MAIN-SYNTAX";
    let default_stderr = String::from_utf8_lossy(&default.stderr);
    assert_eq!(
        default_stderr.matches(warning).count(),
        1,
        "{default_stderr}"
    );
    assert!(
        default_stderr.contains("Error[MissingSyntaxModule]"),
        "{default_stderr}"
    );

    let normal = run("normal", &[]);
    let normal_stderr = String::from_utf8_lossy(&normal.stderr);
    assert!(normal.status.success(), "{normal_stderr}");
    assert_eq!(normal_stderr.matches(warning).count(), 1, "{normal_stderr}");
    assert!(
        normal_stderr.contains("Warning[MissingSyntaxModule]"),
        "{normal_stderr}"
    );

    let suppressed = run(
        "suppressed",
        &["--warnings", "none", "--warnings-to-errors"],
    );
    let suppressed_stderr = String::from_utf8_lossy(&suppressed.stderr);
    assert!(suppressed.status.success(), "{suppressed_stderr}");
    assert!(
        !suppressed_stderr.contains("MissingSyntaxModule"),
        "{suppressed_stderr}"
    );
    assert!(!suppressed_stderr.contains(warning), "{suppressed_stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn warning_flags_are_exposed_by_every_diagnostic_subcommand() {
    for command in ["kcompile", "kast", "krun", "kprove"] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([command, "--help"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{command}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let help = String::from_utf8(output.stdout).unwrap();
        assert!(help.contains("-w, --warnings <LEVEL>"), "{command}: {help}");
        assert!(help.contains("--warnings-to-errors"), "{command}: {help}");
    }
}

#[test]
fn singleton_overload_warnings_follow_the_disambiguation_grammar_and_policy() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/singletonOverload.k");
    let run = |name: &str, warning_args: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "SINGLETONOVERLOAD",
            "--syntax-module",
            "SINGLETONOVERLOAD-SYNTAX",
            "--backend",
            "rust",
            "--output-directory",
            output_directory.to_str().unwrap(),
        ]);
        command.args(warning_args);
        command.output().unwrap()
    };

    let normal = run("normal", &[]);
    let normal_stderr = String::from_utf8_lossy(&normal.stderr);
    assert!(normal.status.success(), "{normal_stderr}");
    assert_eq!(
        normal_stderr.matches("Warning[SingletonOverload]").count(),
        2,
        "{normal_stderr}"
    );

    let promoted = run("promoted", &["--warnings", "all", "--warnings-to-errors"]);
    let promoted_stderr = String::from_utf8_lossy(&promoted.stderr);
    assert!(!promoted.status.success(), "{promoted_stderr}");
    assert_eq!(
        promoted_stderr.matches("Error[SingletonOverload]").count(),
        2,
        "{promoted_stderr}"
    );

    let suppressed = run(
        "suppressed",
        &["--warnings", "none", "--warnings-to-errors"],
    );
    let suppressed_stderr = String::from_utf8_lossy(&suppressed.stderr);
    assert!(suppressed.status.success(), "{suppressed_stderr}");
    assert!(!suppressed_stderr.contains("SingletonOverload"));

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn warnings_to_errors_fails_kcompile_on_an_unused_variable() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/checkUnusedVar.k");
    let run = |name: &str, warning_args: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "CHECKUNUSEDVAR",
            "--output-directory",
            output_directory.to_str().unwrap(),
        ]);
        command.args(warning_args);
        command.output().unwrap()
    };

    let normal = run("normal", &[]);
    assert!(
        normal.status.success(),
        "{}",
        String::from_utf8_lossy(&normal.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&normal.stderr)
            .matches("Warning[UnusedVariable]")
            .count(),
        3
    );

    let error = run("error", &["--warnings-to-errors"]);
    assert!(!error.status.success());
    let stderr = String::from_utf8_lossy(&error.stderr);
    assert_eq!(
        stderr.matches("Error[UnusedVariable]").count(),
        3,
        "{stderr}"
    );
    assert!(!stderr.contains("Warning[UnusedVariable]"), "{stderr}");

    let none = run("none", &["--warnings", "none"]);
    assert!(
        none.status.success(),
        "{}",
        String::from_utf8_lossy(&none.stderr)
    );
    assert!(
        !String::from_utf8_lossy(&none.stderr).contains("UnusedVariable"),
        "{}",
        String::from_utf8_lossy(&none.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn configured_builtin_paths_are_exempt_after_canonicalization() {
    let (root, definition) = fixture();
    let builtin_directory = root.join("builtin");
    let noncanonical_directory = root.join("alias").join("..").join("builtin");
    fs::create_dir_all(root.join("alias")).unwrap();
    fs::create_dir_all(&builtin_directory).unwrap();
    fs::write(
        builtin_directory.join("builtin.k"),
        r#"
module BUILTIN
  syntax Builtin ::= "builtin"
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &definition,
        r#"
requires "builtin.k"

module MAIN
  imports BUILTIN
  syntax User ::= "user"
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--output-directory",
            root.join("compiled").to_str().unwrap(),
            "--builtin-directory",
            noncanonical_directory.to_str().unwrap(),
            "--no-prelude",
            "--warnings",
            "all",
            "--warnings-to-errors",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr.matches("Error[UnusedSymbol]").count(), 1, "{stderr}");
    assert!(
        stderr.contains("Symbol 'user_MAIN_User' defined but not used."),
        "{stderr}"
    );
    assert!(
        !stderr.contains("Symbol 'builtin_BUILTIN_Builtin' defined but not used."),
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_deprecated_configuration_reports_every_occurrence() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/deprecated.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "DEPRECATED",
            "--syntax-module",
            "DEPRECATED-SYNTAX",
            "--output-directory",
            root.join("compiled").to_str().unwrap(),
            "--warnings",
            "all",
            "--warnings-to-errors",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        stderr.matches("Error[DeprecatedProduction]").count(),
        11,
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_configuration_dependent_sort_predicate_is_rejected() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/invalidSortPredicate.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "INVALIDSORTPREDICATE",
            "--syntax-module",
            "INVALIDSORTPREDICATE",
            "--output-directory",
            root.join("compiled").to_str().unwrap(),
            "--warnings",
            "none",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "Invalid sort predicate isExp that depends directly or indirectly on the current configuration. Is it possible to replace the sort predicate with a regular function?"
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_proof_modules_reject_rules_and_new_syntax() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/checks");
    let semantics = fs::read_to_string(fixtures.join("errorClaim.k")).unwrap();
    let cases = [
        (
            "rule-spec.k",
            "RULE-SPEC",
            "Only claims and simplification rules are allowed in proof modules.",
        ),
        (
            "syntax-spec.k",
            "SYNTAX-SPEC",
            "Found syntax declaration in proof module. Only tokens for existing sorts are allowed.",
        ),
    ];
    for (file, module, message) in cases {
        let (root, definition) = fixture();
        let specification = fs::read_to_string(fixtures.join(file)).unwrap();
        fs::write(&definition, format!("{semantics}\n{specification}")).unwrap();
        for command in ["kprove", "kcompile"] {
            let mut invocation = Command::new(env!("CARGO_BIN_EXE_krust"));
            invocation.args([
                command,
                definition.to_str().unwrap(),
                "--main-module",
                module,
                "--definition-module",
                "ERRORCLAIM",
            ]);
            if command == "kcompile" {
                invocation
                    .arg("--for-proving")
                    .arg("--output-directory")
                    .arg(root.join("compiled"));
            }
            let output = invocation.output().unwrap();
            assert!(!output.status.success(), "{file}");
            assert!(
                String::from_utf8_lossy(&output.stderr).contains(message),
                "{file}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
}

fn kcompile_checks_fixture(root: &Path, file: &str, module: &str, backend: &str) -> Output {
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks")
        .join(file);
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            module,
            "--syntax-module",
            module,
            "--backend",
            backend,
            "--output-directory",
            root.join(file).with_extension("").to_str().unwrap(),
            "--warnings",
            "none",
        ])
        .output()
        .unwrap()
}

#[test]
fn reference_is_sort_predicates_outside_the_parsed_definition_are_accepted() {
    // reference: k/result/bin/kompile --backend haskell isSortPredicateOutsideClosure.k (exit 0)
    // reference: k/result/bin/kompile --backend haskell isSortPredicateBubbleModule.k (exit 0)
    let (root, _) = fixture();
    for (file, module) in [
        (
            "isSortPredicateOutsideClosure.k",
            "ISSORTPREDICATEOUTSIDECLOSURE",
        ),
        (
            "isSortPredicateBubbleModule.k",
            "ISSORTPREDICATEBUBBLEMODULE",
        ),
    ] {
        let output = kcompile_checks_fixture(&root, file, module, "haskell");
        assert!(
            output.status.success(),
            "{file}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_is_sort_predicate_conflicts_in_the_parsed_definition_are_rejected() {
    // reference: k/result/bin/kompile -w none --backend llvm checkIsSort.k (exit 113)
    // reference: k/result/bin/kompile --backend haskell isSortPredicateEntryModule.k (exit 113)
    let (root, _) = fixture();
    for (file, module, backend, predicates) in [
        (
            "checkIsSort.k",
            "CHECKISSORT",
            "llvm",
            &["isNonAddr", "isFoo"][..],
        ),
        (
            "isSortPredicateEntryModule.k",
            "ISSORTPREDICATEENTRYMODULE",
            "haskell",
            &["isRange"][..],
        ),
    ] {
        let output = kcompile_checks_fixture(&root, file, module, backend);
        assert!(!output.status.success(), "{file}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        for predicate in predicates {
            assert!(
                stderr.contains(&format!(
                    "Error[IsSortPredicateConflict]: Syntax declaration conflicts with automatically generated {predicate} predicate."
                )),
                "{file}: {stderr}"
            );
        }
    }
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
fn reference_kcompile_accepts_hook_namespace_list_spellings() {
    // reference: k/result/bin/kompile test.k --backend haskell --hook-namespaces "A B"
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/hooks");
    let expected = fs::read_to_string(fixtures.join("hook-attributes.txt")).unwrap();
    let (root, _) = fixture();

    for (name, namespaces) in [
        ("space", &["A B"][..]),
        ("comma", &["A,B"][..]),
        ("repeated", &["A", "B"][..]),
    ] {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "HOOKS",
            "--syntax-module",
            "HOOKS",
            "--backend",
            "llvm",
            "--output-directory",
            output_directory.to_str().unwrap(),
        ]);
        for namespace in namespaces {
            command.args(["--hook-namespaces", namespace]);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let kore = fs::read_to_string(output_directory.join("definition.kore")).unwrap();
        for hook in expected.lines() {
            assert!(kore.contains(hook), "{name} did not emit {hook}:\n{kore}");
        }
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_warns_when_a_plugin_hook_namespace_is_not_selected() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/hooks");
    let (root, _) = fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "HOOKS",
            "--syntax-module",
            "HOOKS",
            "--backend",
            "llvm",
            "--output-directory",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert_eq!(
        stderr.matches("UnadmittedHookNamespace").count(),
        2,
        "{stderr}"
    );
    assert!(stderr.contains("hook(A.f)"), "{stderr}");
    assert!(stderr.contains("hook(B.g)"), "{stderr}");

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

/// The BN128 section of `plugin/krypto.md` at blockchain-k-plugin `651a2db5`, the plugin the pinned
/// KEVM uses, verbatim in a module of the same name: its point productions carry no `symbol`
/// attribute, so their Kore labels are generated from the production.
const PINNED_PLUGIN_BN128: &str = r#"
module KRYPTO
    imports BOOL-SYNTAX
    imports INT-SYNTAX
    imports LIST

    syntax G1Point ::= "(" Int "," Int ")" [prefer]
    syntax G2Point ::= "(" Int "x" Int "," Int "x" Int ")"
    syntax G1Point ::= BN128Add(G1Point, G1Point) [function, hook(KRYPTO.bn128add)]
                     | BN128Mul(G1Point, Int)     [function, hook(KRYPTO.bn128mul)]

    syntax Bool ::= BN128AtePairing(List, List) [function, hook(KRYPTO.bn128ate)]

    syntax Bool ::= isValidPoint(G1Point) [function, hook(KRYPTO.bn128valid)]
                  | isValidPoint(G2Point) [function, symbol(isValidG2Point), hook(KRYPTO.bn128g2valid)]
endmodule

module MAIN
  imports INT
  imports BOOL
  imports LIST
  imports KRYPTO

  syntax G1Point ::= alt(Int, Int, Int)
  syntax Check ::= "valid" | "off-curve" | "other-constructor" | "g2-valid" | "add" | "mul"
                 | "pairing"
  syntax KItem ::= result(K)

  rule <k> valid => result(isValidPoint((1, 2))) </k>
  rule <k> off-curve => result(isValidPoint((1, 3))) </k>
  rule <k> other-constructor => result(isValidPoint(alt(1, 2, 0))) </k>
  rule <k> g2-valid => result(isValidPoint((
      10857046999023057135944570762232829481370756359578518086990519993285655852781
        x 11559732032986387107991004021392285783925812861821192530917403151452391805634,
      8495653923123431417604973247489272438418190587263600148770280649306958101930
        x 4082367875863433681332203403145435568316851327593401208105741076214120093531)))
  </k>
  rule <k> add => result(BN128Add((1, 2), (1, 2))) </k>
  rule <k> mul => result(BN128Mul((1, 2), 2)) </k>
  rule <k> pairing => result(BN128AtePairing(
    ListItem((1, 2))
      ListItem((1, 21888242871839275222246405745257275088696311157297823662689037894645226208581)),
    ListItem((
      10857046999023057135944570762232829481370756359578518086990519993285655852781
        x 11559732032986387107991004021392285783925812861821192530917403151452391805634,
      8495653923123431417604973247489272438418190587263600148770280649306958101930
        x 4082367875863433681332203403145435568316851327593401208105741076214120093531))
      ListItem((
        10857046999023057135944570762232829481370756359578518086990519993285655852781
          x 11559732032986387107991004021392285783925812861821192530917403151452391805634,
        8495653923123431417604973247489272438418190587263600148770280649306958101930
          x 4082367875863433681332203403145435568316851327593401208105741076214120093531))))
  </k>

  configuration <k> $PGM:Check </k>
endmodule
"#;

#[test]
fn krun_evaluates_bn128_hooks_on_the_pinned_plugin_point_productions() {
    let (root, definition) = fixture();
    fs::write(&definition, PINNED_PLUGIN_BN128).unwrap();
    let boolean = |value: &str| format!(r#"\dv{{SortBool{{}}}}("{value}")"#);
    let doubled = concat!(
        "Lbl'LParUndsCommUndsRParUnds'KRYPTO'Unds'G1Point'Unds'Int'Unds'Int{}(\n",
        "              \\dv{SortInt{}}(\"1368015179489954701390400359078579693043519447331113978918064868415326638035\"),\n",
        "              \\dv{SortInt{}}(\"9918110051302171585080402603319702774565515993150576347155970296011118125764\")\n",
    )
    .to_owned();
    for (check, expected) in [
        ("valid", boolean("true")),
        ("off-curve", boolean("false")),
        ("other-constructor", boolean("false")),
        ("g2-valid", boolean("true")),
        ("add", doubled.clone()),
        ("mul", doubled),
        ("pairing", boolean("true")),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "MAIN",
                "--sort",
                "Check",
                "--expression",
                check,
                "--depth",
                "10",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{check}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = String::from_utf8(output.stdout).unwrap();
        assert!(output.contains("Lblresult"), "{check}: {output}");
        assert!(output.contains(&expected), "{check}: {output}");
        assert!(!output.contains("BN128"), "{check}: {output}");
        assert!(!output.contains("isValid"), "{check}: {output}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_completes_star_cell_heating_with_one_or_two_cells() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/star-cell-heating");
    let definition = fixtures.join("test.k");
    for (program, thread_cells, next) in [
        ("one.cb10", 1, "1"),
        ("two.cb10", 2, "2"),
        ("two-late.cb10", 2, "2"),
    ] {
        let program_path = fixtures.join(program);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                program_path.to_str().unwrap(),
                "--main-module",
                "STAR-CELL-HEATING",
                "--syntax-module",
                "STAR-CELL-HEATING-SYNTAX",
                "--sort",
                "Stmt",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            stdout.matches("Lbl'-LT-'thread'-GT-'{}").count(),
            thread_cells,
            "{program}: {stdout}"
        );
        assert_eq!(
            stdout.matches("Lbl'-LT-'k'-GT-'{}(dotk{}())").count(),
            thread_cells,
            "{program}: {stdout}"
        );
        assert!(
            stdout.contains(&format!(
                "Lbl'-LT-'next'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{next}\"))"
            )),
            "{program}: {stdout}"
        );
    }

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            fixtures.join("two.cb10").to_str().unwrap(),
            "--main-module",
            "STAR-CELL-HEATING-SET",
            "--syntax-module",
            "STAR-CELL-HEATING-SYNTAX",
            "--sort",
            "Stmt",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "Set-cell variant: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    // The two completed, identical Set elements collapse by idempotence.
    assert_eq!(
        stdout.matches("Lbl'-LT-'task'-GT-'{}").count(),
        1,
        "{stdout}"
    );
    assert_eq!(
        stdout.matches("Lbl'-LT-'k'-GT-'{}(dotk{}())").count(),
        1,
        "{stdout}"
    );
    assert!(
        !stdout.contains("\\or{"),
        "any strategy must print one configuration: {stdout}"
    );
}

#[test]
fn krun_surface_pattern_projects_set_typed_star_cell() {
    // reference: workers/CB-18-evidence/star-cell-heating-set/ref-{one,two}-kKk.out and
    //   ref-{one,two}-kKKKk.out; the reference krun additionally prints _DotVar0/_DotVar1
    //   bindings that krust projects away. ref-two-d0-K.out binds KK to the injected Stmt program.
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/star-cell-heating");
    let definition = fixtures.join("test.k");
    for program in ["one.cb10", "two.cb10"] {
        for (surface_pattern, expected_binding) in [
            ("<k> .K </k>", None),
            ("<k> KK:K </k>", Some(parse_pattern("dotk{}()").unwrap())),
        ] {
            let output = Command::new(env!("CARGO_BIN_EXE_krust"))
                .args([
                    "krun",
                    definition.to_str().unwrap(),
                    fixtures.join(program).to_str().unwrap(),
                    "--main-module",
                    "STAR-CELL-HEATING-SET",
                    "--syntax-module",
                    "STAR-CELL-HEATING-SYNTAX",
                    "--sort",
                    "Stmt",
                    "--io",
                    "off",
                    "--pattern",
                    surface_pattern,
                ])
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{program}, {surface_pattern}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            let actual = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
            if let Some(expected_binding) = expected_binding {
                assert_eq!(
                    pattern_binding(&actual, "VarKK"),
                    Some(&expected_binding),
                    "{program}: {actual:?}"
                );
            } else {
                assert!(
                    matches!(actual, Pattern::Top { .. }),
                    "{program}: {actual:?}"
                );
            }
        }
    }

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            fixtures.join("two.cb10").to_str().unwrap(),
            "--main-module",
            "STAR-CELL-HEATING-SET",
            "--syntax-module",
            "STAR-CELL-HEATING-SYNTAX",
            "--sort",
            "Stmt",
            "--io",
            "off",
            "--depth",
            "0",
            "--pattern",
            "<k> KK:K </k>",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let binding = pattern_binding(&actual, "VarKK").expect("KK binding");
    let Pattern::Application { symbol, arguments } = binding else {
        panic!("expected K sequence, got {binding:?}");
    };
    assert_eq!(symbol.name, "kseq", "{binding:?}");
    let Some(Pattern::Application {
        symbol: injection, ..
    }) = arguments.first()
    else {
        panic!("expected injected Stmt at the head of {binding:?}");
    };
    assert_eq!(injection.name, "inj", "{binding:?}");
    assert_eq!(
        injection
            .sort_parameters
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["SortStmt{}", "SortKItem{}"],
        "{binding:?}"
    );
}

#[test]
fn krun_solves_map_keys_bound_by_a_star_set_cell_before_nested_sets() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/star-cell-map-nested-set");
    let definition = fixtures.join("test.k");
    for (program, cast_remains) in [
        ("neg-two.cb17", true),
        ("pos-two.cb17", false),
        ("pos2-two.cb17", false),
        ("two.cb17", false),
    ] {
        let program_path = fixtures.join(program);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                program_path.to_str().unwrap(),
                "--main-module",
                "STAR-CELL-MAP-NESTED-SET",
                "--syntax-module",
                "STAR-CELL-MAP-NESTED-SET-SYNTAX",
                "--sort",
                "Stmt",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            stdout.contains("Lblcast"),
            cast_remains,
            "{program}: {stdout}"
        );
        assert!(!stdout.contains("\\or{"), "{program}: {stdout}");
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

#[test]
fn reference_krun_evaluates_a_named_field_projection_program() {
    // reference: k/result/bin/kompile --backend llvm test.k && k/result/bin/krun 3.test (regression-new/record-llvm: `foo(test(5, 10, 15))` prints `10`)
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/inner/record-projection");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "TEST",
            "--syntax-module",
            "TEST",
            "--sort",
            "KItem",
            "--expression",
            "foo(test(5, 10, 15))",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("10")"#), "{output}");
    assert!(!output.contains("project"), "{output}");
}

#[test]
fn kcompile_writes_phase_timings_json() {
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
    let timings_path = root.join("kcompile-timings.json");
    let trace_path = root.join("kcompile-trace.json");
    let output_directory = root.join("compiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--timings",
            timings_path.to_str().unwrap(),
            "--trace",
            trace_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    assert!(output_directory.join("definition.kore").is_file());
    let trace: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&trace_path).unwrap()).unwrap();
    let events = trace.as_array().unwrap();
    assert!(events.iter().any(|event| event["name"] == "phase"));
    assert!(
        events
            .iter()
            .any(|event| event["args"]["aggregation_rule"].is_string())
    );
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    assert_eq!(timings["version"], k_rust::timings::TIMINGS_SCHEMA_VERSION);
    for key in [
        "load_seconds",
        "compile_seconds",
        "write_seconds",
        "load_wall_seconds",
        "compile_wall_seconds",
        "write_wall_seconds",
        "load_unattributed_seconds",
        "compile_unattributed_seconds",
        "write_unattributed_seconds",
        "total_wall_seconds",
    ] {
        assert!(timings[key].as_f64().unwrap() >= 0.0, "{key}: {timings}");
    }
    let phases = timings["phases"].as_array().unwrap();
    let names = phases
        .iter()
        .map(|phase| phase["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(names[0], "resolve entry source", "{names:?}");
    assert_eq!(names[1], "parse sources", "{names:?}");
    assert!(names.contains(&"lower files"), "{names:?}");
    assert!(names.contains(&"print definition.kore"), "{names:?}");
    assert_eq!(names.last(), Some(&"write artifacts"), "{names:?}");
    assert!(
        phases
            .iter()
            .all(|phase| phase["seconds"].as_f64().unwrap() >= 0.0),
        "{timings}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_writes_phase_timings_json() {
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
    let timings_path = root.join("krun-timings.json");
    let krun = Command::new(env!("CARGO_BIN_EXE_krust"))
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
            "--timings",
            timings_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        krun.status.success(),
        "{}",
        String::from_utf8_lossy(&krun.stderr)
    );
    let stdout = String::from_utf8(krun.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("42")"#), "{stdout}");
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    for key in [
        "program_parse_seconds",
        "config_vars_parse_seconds",
        "internalize_seconds",
        "execute_seconds",
        "output_seconds",
    ] {
        assert!(timings[key].as_f64().unwrap() >= 0.0, "{key}: {timings}");
    }
    let compile = &timings["compile"];
    assert_eq!(compile["version"], k_rust::timings::TIMINGS_SCHEMA_VERSION);
    assert!(
        compile["load_seconds"].as_f64().unwrap() >= 0.0,
        "{timings}"
    );
    assert!(
        compile["compile_seconds"].as_f64().unwrap() >= 0.0,
        "{timings}"
    );
    assert_eq!(compile["write_seconds"], 0.0, "{timings}");
    for key in [
        "load_wall_seconds",
        "compile_wall_seconds",
        "write_wall_seconds",
        "load_unattributed_seconds",
        "compile_unattributed_seconds",
        "write_unattributed_seconds",
        "total_wall_seconds",
    ] {
        assert!(compile[key].as_f64().unwrap() >= 0.0, "{key}: {timings}");
    }
    let names = compile["phases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|phase| phase["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(names[0], "resolve entry source", "{names:?}");
    assert!(names.contains(&"lower files"), "{names:?}");
    assert_eq!(names.last(), Some(&"print macros.kore"), "{names:?}");
    fs::remove_dir_all(root).unwrap();
}

fn rewrite_example() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/rewrite.k")
}

fn kcompile_rewrite_example(root: &Path, counters: Option<&Path>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .arg("kcompile")
        .arg(rewrite_example())
        .args(["--main-module", "REWRITE", "--output-directory"])
        .arg(root.join("compiled"))
        .env_remove("KRUST_COUNTERS");
    if let Some(counters) = counters {
        command.env("KRUST_COUNTERS", counters);
    }
    command.output().unwrap()
}

// Test builds enable the `measure` feature through the crate's own dev-dependency, so the dump is
// available here; a feature-off `krust` never reads `KRUST_COUNTERS`.
#[test]
fn krust_counters_writes_every_counter_in_schema_order_on_success_and_failure() {
    let (root, _) = fixture();
    let counters = root.join("counters.json");
    let output = kcompile_rewrite_example(&root, Some(&counters));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = fs::read_to_string(&counters).unwrap();
    let document: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(document["format"], "krust-counters");
    assert_eq!(
        document["version"],
        k_rust_kore::measure::COUNTER_SCHEMA_VERSION
    );
    let written = document["counters"].as_object().unwrap();
    let expected = k_rust_kore::measure::Counter::ALL.map(k_rust_kore::measure::Counter::name);
    assert_eq!(written.len(), expected.len());
    // Keys appear in `Counter::ALL` order so that diffs between runs are line-stable.
    let positions = expected
        .iter()
        .map(|name| text.find(&format!("\"{name}\":")).unwrap())
        .collect::<Vec<_>>();
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));
    assert!(written["kompile.resolve_calls"].as_u64().unwrap() > 0);
    // The prelude modules reachable from REWRITE carry rule bubbles too.
    assert!(written["kompile.rule_bubbles_parsed"].as_u64().unwrap() > 0);
    assert!(written["parser.parse_attempts"].as_u64().unwrap() > 0);
    assert_eq!(written["rewrite.steps"], 0);

    let failed_counters = root.join("failed-counters.json");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(root.join("missing.k"))
        .args(["--main-module", "REWRITE", "--output-directory"])
        .arg(root.join("failed"))
        .env("KRUST_COUNTERS", &failed_counters)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let document: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&failed_counters).unwrap()).unwrap();
    assert_eq!(
        document["counters"].as_object().unwrap().len(),
        k_rust_kore::measure::Counter::COUNT
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_writes_no_counter_file_without_krust_counters() {
    let (root, _) = fixture();
    let output = kcompile_rewrite_example(&root, None);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut entries = fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    entries.sort();
    assert_eq!(entries, ["base.k", "compiled", "definition.k"]);
    fs::remove_dir_all(root).unwrap();
}

/// Prove each named claim of an inlined specification on its own and return the verdict word
/// `krust kprove` reports for it (`proven`, `disproved`, `indeterminate`, ...), or `error` with
/// its diagnostic on standard error when the prover rejects the claim.
fn kprove_claim_verdicts(
    definition: (&str, &str),
    specification: (&str, &str),
    main_module: &str,
    definition_module: &str,
    claims: &[&str],
) -> Vec<(String, String)> {
    kprove_claim_leaves(
        definition,
        specification,
        main_module,
        definition_module,
        claims,
        &[],
    )
    .into_iter()
    .map(|(claim, verdict, _)| (claim, verdict))
    .collect()
}

/// Each claim's verdict word and the outcome word of each of its reported leaves
/// (`Stuck`, `Vacuous`, ...), in output order.
fn kprove_claim_leaves(
    definition: (&str, &str),
    specification: (&str, &str),
    main_module: &str,
    definition_module: &str,
    claims: &[&str],
    extra_args: &[&str],
) -> Vec<(String, String, Vec<String>)> {
    let (root, _) = fixture();
    fs::write(root.join(definition.0), definition.1).unwrap();
    let specification_path = root.join(specification.0);
    fs::write(&specification_path, specification.1).unwrap();
    let verdicts = claims
        .iter()
        .map(|claim| {
            let output = Command::new(env!("CARGO_BIN_EXE_krust"))
                .args([
                    "kprove",
                    specification_path.to_str().unwrap(),
                    "--main-module",
                    main_module,
                    "--definition-module",
                    definition_module,
                    "--depth",
                    "10",
                    "--claim",
                    claim,
                ])
                .args(extra_args)
                .output()
                .unwrap();
            let stdout = String::from_utf8(output.stdout).unwrap();
            let stderr = String::from_utf8_lossy(&output.stderr);
            let leaves = stdout
                .lines()
                .filter_map(|line| line.strip_prefix("  "))
                .filter_map(|line| line.split_once(" at depth "))
                .map(|(outcome, _)| outcome.to_owned())
                .collect::<Vec<_>>();
            let prefix = format!("claim {claim}: ");
            let verdict = stdout
                .lines()
                .find_map(|line| line.strip_prefix(&prefix))
                .and_then(|rest| rest.split_whitespace().next())
                .map(str::to_owned)
                .unwrap_or_else(|| {
                    eprintln!("{claim}: {}", stderr.trim());
                    "error".to_owned()
                });
            assert_eq!(
                output.status.success(),
                verdict == "proven",
                "{claim}: {stdout}\n{stderr}"
            );
            ((*claim).to_owned(), verdict, leaves)
        })
        .collect();
    fs::remove_dir_all(root).unwrap();
    verdicts
}

fn verdicts_of(leaves: &[(String, String, Vec<String>)]) -> Vec<(String, String)> {
    leaves
        .iter()
        .map(|(claim, verdict, _)| (claim.clone(), verdict.clone()))
        .collect()
}

/// A claim that ends `disproved` at exactly one leaf, a certified stuck leaf.
fn refuted_leaf(claim: &str) -> (String, String, Vec<String>) {
    (
        claim.to_owned(),
        "disproved".to_owned(),
        vec!["Stuck (certified)".to_owned()],
    )
}

/// A claim that ends `failed` at exactly one leaf, a stuck leaf that is not certified.
fn failed_stuck_leaf(claim: &str) -> (String, String, Vec<String>) {
    (
        claim.to_owned(),
        "failed".to_owned(),
        vec!["Stuck".to_owned()],
    )
}

fn expected_verdicts(expected: &[(&str, &str)]) -> Vec<(String, String)> {
    expected
        .iter()
        .map(|(claim, verdict)| ((*claim).to_owned(), (*verdict).to_owned()))
        .collect()
}

const EXIST_PROBE: &str = r#"
module EXIST-PROBE
  imports INT
  syntax State ::= "start" | st(Int, Int) | "done"
  configuration <k> $PGM:State </k>
  rule <k> start => st(!N:Int, 7) </k>
endmodule
"#;

/// A claim that does not name the generated counter says nothing about it, so a path that
/// instantiates a `!` variable (and so advances the counter) can prove it.
#[test]
fn kprove_claims_leave_the_generated_counter_to_the_path() {
    let specification = r#"
requires "exist-probe.k"

module EXIST-SPEC
  imports EXIST-PROBE

  claim <k> start => st(?B:Int, ?A:Int) </k> ensures ?A ==Int 7 [label(ab)]
  claim <k> start => st(?Z:Int, ?A:Int) </k> ensures ?A ==Int 7 [label(za)]
  claim <k> start => st(?B:Int, ?A:Int) </k> ensures ?A ==Int 8 [label(ab-false)]
endmodule
"#;
    assert_eq!(
        kprove_claim_verdicts(
            ("exist-probe.k", EXIST_PROBE),
            ("exist-spec.k", specification),
            "EXIST-SPEC",
            "EXIST-PROBE",
            &["ab", "za", "ab-false"],
        ),
        expected_verdicts(&[("ab", "proven"), ("za", "proven"), ("ab-false", "failed")]),
    );
}

/// A claim that names the generated counter states what it says about it.
#[test]
fn kprove_claims_naming_the_generated_counter_keep_their_statement() {
    let specification = r#"
requires "exist-probe.k"

module EXIST-SPEC2
  imports EXIST-PROBE

  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => C </generatedCounter> ensures ?A ==Int 7 [label(same-counter)]
  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => ?C2:Int </generatedCounter> ensures ?A ==Int 7 [label(exists-counter)]
  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => C +Int 1 </generatedCounter> ensures ?A ==Int 7 [label(incremented-counter)]
  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => C +Int 2 </generatedCounter> ensures ?A ==Int 7 [label(wrong-counter)]
endmodule
"#;
    assert_eq!(
        kprove_claim_verdicts(
            ("exist-probe.k", EXIST_PROBE),
            ("exist-spec2.k", specification),
            "EXIST-SPEC2",
            "EXIST-PROBE",
            &[
                "same-counter",
                "exists-counter",
                "incremented-counter",
                "wrong-counter"
            ],
        ),
        expected_verdicts(&[
            ("same-counter", "failed"),
            ("exists-counter", "proven"),
            ("incremented-counter", "proven"),
            ("wrong-counter", "failed"),
        ]),
    );
}

/// Both ways of writing a claim across a rule that allocates a fresh value prove: naming the
/// counter's advance, or leaving the counter out.
#[test]
fn kprove_fresh_value_claims_prove_with_and_without_the_counter() {
    let definition = r#"
module TEST
  imports INT
  syntax Pgm ::= "quux"
  configuration <k> $PGM:Pgm </k> <c1> .K </c1> <c2> .K </c2>
  rule <k> quux => .K </k> <c1> .K => !C:Int </c1> <c2> .K => !C:Int </c2>
endmodule
"#;
    let specification = r#"
requires "test.k"

module FRESH-SPEC
  imports TEST

  claim <k> quux => .K </k> <c1> .K => ?C </c1> <c2> .K => ?C </c2>
    <generatedCounter> GC => GC +Int 1 </generatedCounter> [label(explicit)]
  claim <k> quux => .K </k> <c1> .K => ?C </c1> <c2> .K => ?C </c2> [label(implicit)]
endmodule
"#;
    assert_eq!(
        kprove_claim_verdicts(
            ("test.k", definition),
            ("fresh-spec.k", specification),
            "FRESH-SPEC",
            "TEST",
            &["explicit", "implicit"],
        ),
        expected_verdicts(&[("explicit", "proven"), ("implicit", "proven")]),
    );
}

const CELL_PROBE: &str = r#"
module CELL-PROBE
  imports INT
  syntax State ::= "start" | "middle" | "done"
  configuration <k> $PGM:State </k> <n> 0 </n>
  rule <k> start => middle </k> <n> X => X +Int 1 </n>
endmodule
"#;

/// A universal variable of a claim, including the frame variable of a cell the claim leaves out,
/// denotes the same value in the reached state as in the initial one.
#[test]
fn kprove_universal_claim_variables_keep_their_initial_value() {
    let specification = r#"
requires "cell-probe.k"

module CELL-SPEC
  imports CELL-PROBE

  claim <k> start => middle </k> [label(unmentioned)]
  claim <k> start => middle </k> <n> X => X +Int 1 </n> [label(incremented)]
  claim <k> start => middle </k> <n> X => X </n> [label(unchanged)]
  claim <k> start => middle </k> <n> 3 </n> [label(constant)]
  claim <k> start => done </k> [label(unreachable)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("cell-probe.k", CELL_PROBE),
        ("cell-spec.k", specification),
        "CELL-SPEC",
        "CELL-PROBE",
        &[
            "unmentioned",
            "incremented",
            "unchanged",
            "constant",
            "unreachable",
        ],
        &[],
    );
    // The increment of an unmentioned cell falsifies the claim. The frame equation holds on part
    // of the reached state as far as the solver can tell (the two `<n>` values are opaque to it),
    // so the part where it fails continues and ends as a stuck leaf. That part is non-empty only
    // modulo the abstraction of the two cells, so the leaf is not certified: the claim fails.
    assert_eq!(leaves[0], failed_stuck_leaf("unmentioned"), "{leaves:?}");
    assert_eq!(
        verdicts_of(&leaves[1..]),
        expected_verdicts(&[
            ("incremented", "proven"),
            // The leaves of `unchanged` and `unreachable` hold `X +Int 1`, an unevaluated
            // function application; `constant`'s holds the value `4` of the matched `X = 3`.
            ("unchanged", "failed"),
            ("constant", "disproved"),
            ("unreachable", "failed"),
        ]),
    );
}

const CELL_PROBE2: &str = r#"
module CELL-PROBE2
  imports INT
  syntax State ::= "start" | "middle"
  configuration <k> $PGM:State </k> <n> 0 </n>
  rule <k> start => middle </k> <n> _ => 5 </n>
endmodule
"#;

const CELL_SPEC2: &str = r#"
requires "cell-probe2.k"

module CELL-SPEC2
  imports CELL-PROBE2

  claim <k> start => middle </k> <n> X => X </n> [label(free-unchanged)]
  claim <k> start => middle </k> <n> X => X </n> requires X ==Int 0 [label(constrained-unchanged)]
  claim <k> start => middle </k> <n> X => 5 </n> requires X ==Int 0 [label(constrained-set)]
  claim <k> start => middle </k> <n> 0 => 0 </n> [label(concrete-unchanged)]
endmodule
"#;

/// A universal claim variable denotes its initial value in the reached state, so the value the path
/// writes into its cell falsifies the claim whether or not the precondition constrains the variable.
#[test]
fn kprove_constrained_universal_claim_variables_are_checked() {
    let leaves = kprove_claim_leaves(
        ("cell-probe2.k", CELL_PROBE2),
        ("cell-spec2.k", CELL_SPEC2),
        "CELL-SPEC2",
        "CELL-PROBE2",
        &[
            "free-unchanged",
            "constrained-unchanged",
            "constrained-set",
            "concrete-unchanged",
        ],
        &[],
    );
    // `X = 5` holds on part of the reached state for an unconstrained `X`: that part is in the
    // destination, and the part where `X` differs from 5 has no successor. Its constraint
    // `¬(X = 5)` is over the integers only, so the leaf is a certified refutation.
    assert_eq!(leaves[0], refuted_leaf("free-unchanged"), "{leaves:?}");
    assert_eq!(
        verdicts_of(&leaves[1..]),
        expected_verdicts(&[
            ("constrained-unchanged", "disproved"),
            ("constrained-set", "proven"),
            ("concrete-unchanged", "disproved"),
        ]),
    );
}

/// A rule that only reads a cell the claim leaves out keeps the claim's frame; a rule that writes
/// one does not.
#[test]
fn kprove_unmentioned_cells_read_by_the_path_keep_the_frame() {
    let definition = r#"
module CELL-PROBE3
  imports INT
  syntax State ::= "start" | "middle" | "done"
  configuration <k> $PGM:State </k> <n> 0 </n> <m> 0 </m>
  rule <k> start => middle </k> <n> _ </n>
  rule <k> middle => done </k> <n> X </n> <m> _ => X </m>
endmodule
"#;
    let specification = r#"
requires "cell-probe3.k"

module CELL-SPEC3
  imports CELL-PROBE3

  claim <k> start => middle </k> [label(read-only)]
  claim <k> middle => done </k> <m> _ => ?M </m> [label(copied-exists)]
  claim <k> middle => done </k> <n> X </n> <m> _ => X </m> [label(copied-universal)]
  claim <k> middle => done </k> [label(copied-unmentioned)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("cell-probe3.k", definition),
        ("cell-spec3.k", specification),
        "CELL-SPEC3",
        "CELL-PROBE3",
        &[
            "read-only",
            "copied-exists",
            "copied-universal",
            "copied-unmentioned",
        ],
        &[],
    );
    assert_eq!(
        verdicts_of(&leaves[..3]),
        expected_verdicts(&[
            ("read-only", "proven"),
            ("copied-exists", "proven"),
            ("copied-universal", "proven"),
        ]),
    );
    // Copying `<n>` into `<m>` changes the unmentioned `<m>` wherever the two differ; that part
    // of the reached state has no successor, a stuck leaf. It is non-empty only modulo the
    // abstraction of the cells the frame equation compares, so the claim fails.
    assert_eq!(
        leaves[3],
        failed_stuck_leaf("copied-unmentioned"),
        "{leaves:?}"
    );
}

/// A destination that holds on part of a state closes that part; only the rest continues. The
/// covered part of `covered-then-stuck` (`X = 0`, already in the destination) would reach a state
/// outside it if it were rewritten further.
#[test]
fn kprove_a_contingent_destination_closes_the_covered_part() {
    let definition = r#"
module SPLIT-PROBE
  imports INT
  imports BOOL
  syntax State ::= s(Int, Int)
  configuration <k> $PGM:State </k>
  rule <k> s(0, X) => s(1, 5) </k> requires X =/=Int 0
  rule <k> s(0, X) => s(2, 5) </k> requires X ==Int 0
endmodule
"#;
    let specification = r#"
requires "split-probe.k"

module SPLIT-SPEC
  imports SPLIT-PROBE

  claim <k> s(0, _X) => s(?P:Int, ?V:Int) </k> ensures ?P *Int ?P ==Int ?P andBool (1 -Int ?P) *Int ?V ==Int 0 [label(covered-then-stuck)]
  claim <k> s(0, _X) => s(?P:Int, ?V:Int) </k> ensures ?P *Int ?P ==Int ?P andBool (1 -Int ?P) *Int (?V -Int 7) ==Int 0 [label(contingent-false)]
endmodule
"#;
    for extra in [&[][..], &["--disable-stuck-check"][..]] {
        let leaves = kprove_claim_leaves(
            ("split-probe.k", definition),
            ("split-spec.k", specification),
            "SPLIT-SPEC",
            "SPLIT-PROBE",
            &["covered-then-stuck", "contingent-false"],
            extra,
        );
        assert_eq!(
            verdicts_of(&leaves),
            expected_verdicts(&[
                ("covered-then-stuck", "proven"),
                ("contingent-false", "disproved"),
            ]),
            "{extra:?}: {leaves:?}"
        );
    }
}

/// A destination reached through a match remainder (`st(X)` against `st(0)`) is classified like
/// any other obligation: the part where `X = 0` is at the destination and closes, and the rest
/// can still rewrite, so it continues whatever the stuck check says. `remainder-rewritable` is
/// true (the rest takes the rule to `st(0)`). In `remainder-false` the rest reaches `st(0)`,
/// which is outside the destination `st(1)` and has no successor: a certified stuck leaf
/// (disproved).
#[test]
fn kprove_a_remainder_destination_continues_the_uncovered_part() {
    let definition = r#"
module REMAINDER-PROBE
  imports INT
  imports BOOL
  syntax State ::= st(Int)
  configuration <k> $PGM:State </k>
  rule <k> st(X) => st(0) </k> requires X =/=Int 0
endmodule
"#;
    let specification = r#"
requires "remainder-probe.k"

module REMAINDER-SPEC
  imports REMAINDER-PROBE

  claim <k> st(_X) => st(0) </k> [label(remainder-rewritable)]
  claim <k> st(_X) => st(1) </k> [label(remainder-false)]
endmodule
"#;
    for extra in [&[][..], &["--disable-stuck-check"][..]] {
        let leaves = kprove_claim_leaves(
            ("remainder-probe.k", definition),
            ("remainder-spec.k", specification),
            "REMAINDER-SPEC",
            "REMAINDER-PROBE",
            &["remainder-rewritable", "remainder-false"],
            extra,
        );
        assert_eq!(
            leaves[0],
            (
                "remainder-rewritable".to_owned(),
                "proven".to_owned(),
                Vec::new()
            ),
            "{extra:?}: {leaves:?}"
        );
        let (claim, verdict, outcomes) = &leaves[1];
        assert_eq!(
            (claim.as_str(), verdict.as_str()),
            ("remainder-false", "disproved"),
            "{extra:?}: {leaves:?}"
        );
        assert!(
            !outcomes.is_empty()
                && outcomes
                    .iter()
                    .all(|outcome| outcome == "Stuck (certified)"),
            "{extra:?}: {leaves:?}"
        );
    }
}

/// A remainder obligation (`0 = X` from `st(X)` against `st(0)`) that the simplifier refutes,
/// because together with the destination constraint it is false (`0 = X` with `X >Int 5`, or
/// `false`), is graded exactly as one the solver refutes: the stuck check stops the state at
/// depth 0, and without it the rule rewrites the state onward. `solver-refuted` and `simplifier-refuted` are
/// true; `solver-refuted-false` and `simplifier-refuted-false` are false (their destination
/// constraint fails on every state). Their reached `st(0)` refutes the obligation and has no
/// successor, so it is a stuck leaf in both modes.
#[test]
fn kprove_a_refuted_remainder_is_graded_alike_by_simplifier_and_solver() {
    let definition = r#"
module REMAINDER-PROBE
  imports INT
  imports BOOL
  syntax State ::= st(Int)
  configuration <k> $PGM:State </k>
  rule <k> st(X) => st(0) </k> requires X =/=Int 0
endmodule
"#;
    let specification = r#"
requires "remainder-probe.k"

module REMAINDER-SPEC
  imports REMAINDER-PROBE

  claim <k> st(X) => st(0) </k> requires X >Int 5 [label(solver-refuted)]
  claim <k> st(X) => st(0) </k> requires X >Int 5 ensures X >Int 5 [label(simplifier-refuted)]
  claim <k> st(X) => st(0) </k> requires X >Int 5 ensures X <Int 5 [label(solver-refuted-false)]
  claim <k> st(X) => st(0) </k> requires X >Int 5 ensures false [label(simplifier-refuted-false)]
endmodule
"#;
    let claims = [
        "solver-refuted",
        "simplifier-refuted",
        "solver-refuted-false",
        "simplifier-refuted-false",
    ];
    // The stuck check stops `st(X)` with `X >Int 5`, which still rewrites: a failed claim, not a
    // refutation. The reached `st(0)` of the false claims has no successor: a certified one.
    let stopped = || ("failed".to_owned(), vec!["Stuck".to_owned()]);
    let refuted = || ("disproved".to_owned(), vec!["Stuck (certified)".to_owned()]);
    for (extra, expected) in [
        (&[][..], [stopped(), stopped(), stopped(), stopped()]),
        (
            &["--disable-stuck-check"][..],
            [
                ("proven".to_owned(), Vec::new()),
                ("proven".to_owned(), Vec::new()),
                refuted(),
                refuted(),
            ],
        ),
    ] {
        let leaves = kprove_claim_leaves(
            ("remainder-probe.k", definition),
            ("remainder-spec.k", specification),
            "REMAINDER-SPEC",
            "REMAINDER-PROBE",
            &claims,
            extra,
        );
        let expected = claims
            .iter()
            .zip(expected)
            .map(|(claim, (verdict, outcomes))| ((*claim).to_owned(), verdict, outcomes))
            .collect::<Vec<_>>();
        assert_eq!(leaves, expected, "{extra:?}");
    }
}

/// Where `X =/=Int Y`, `q(X, Y)` rewrites to `q(Y, Y)`, which is stuck. The only witness for `?Z`
/// there is `Y`, so `?Z ==Int X` is refuted. The first state is split on the remainder of the
/// destination match (`X = Y` is covered). The rewritten part then refutes its obligation, and a
/// refuted obligation covers nothing: the whole of `q(Y, Y)` under `X =/=Int Y` is a stuck leaf.
/// That leaf is not an empty state, so accepting vacuous leaves cannot prove the claim.
#[test]
fn kprove_a_refuted_obligation_after_a_remainder_split_stays_stuck() {
    let definition = r#"
module SPLIT-PROBE
  imports INT
  imports BOOL
  syntax State ::= q(Int, Int)
  configuration <k> $PGM:State </k>
  rule <k> q(X, Y) => q(Y, Y) </k> requires X =/=Int Y
endmodule
"#;
    let specification = r#"
requires "split-probe.k"

module SPLIT-SPEC
  imports SPLIT-PROBE

  claim <k> q(X, Y) => q(?Z, ?Z) </k> ensures ?Z ==Int X [label(q-ens-false)]
endmodule
"#;
    for extra in [&[][..], &["--allow-vacuous"][..]] {
        let leaves = kprove_claim_leaves(
            ("split-probe.k", definition),
            ("split-spec.k", specification),
            "SPLIT-SPEC",
            "SPLIT-PROBE",
            &["q-ens-false"],
            extra,
        );
        assert_eq!(leaves, [refuted_leaf("q-ens-false")], "{extra:?}");
    }
}

/// A claim universal that the path overwrote still names its initial value, so the part of the
/// reached state where the destination fails on it is a certified stuck leaf (disproved),
/// whether or not vacuous leaves are accepted.
#[test]
fn kprove_an_overwritten_universal_keeps_the_uncovered_part() {
    let specification = r#"
requires "cell-probe2.k"

module REM-SPEC
  imports CELL-PROBE2

  claim <k> start => middle </k> <n> X => X +Int 1 </n> [label(free-remainder)]
endmodule
"#;
    for extra in [&[][..], &["--allow-vacuous"][..]] {
        let leaves = kprove_claim_leaves(
            ("cell-probe2.k", CELL_PROBE2),
            ("rem-spec.k", specification),
            "REM-SPEC",
            "CELL-PROBE2",
            &["free-remainder"],
            extra,
        );
        assert_eq!(leaves, [refuted_leaf("free-remainder")], "{extra:?}");
    }
}

/// `disproved` is reserved for a certified refutation. The ground all-path claim `start => stuck`
/// of the reference proof corpus reaches `done`, which has no successor, is outside the
/// destination, and has no constraint: its leaf is certified. A claim whose leaf is reached
/// through a circularity is not: the claim step summarises paths it does not follow, so the
/// leaf only fails the claim. Without the circularity the same leaf is certified.
#[test]
fn kprove_certifies_only_a_refutation_the_search_followed_step_by_step() {
    let definition = fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/mini-proof.k"),
    )
    .unwrap();
    let specification = r#"
requires "mini-proof.k"

module MINI-PROOF-SPEC
  imports MINI-PROOF

  claim <k> start => stuck </k> [label(claim-refuted)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("mini-proof.k", &definition),
        ("mini-proof-spec.k", specification),
        "MINI-PROOF-SPEC",
        "MINI-PROOF",
        &["claim-refuted"],
        &[],
    );
    assert_eq!(leaves, [refuted_leaf("claim-refuted")]);

    let definition = r#"
module CIRCULARITY-PROBE
  imports INT
  syntax State ::= a(Int) | b(Int) | c(Int) | d(Int)
  configuration <k> $PGM:State </k>
  rule <k> a(X) => b(X) </k>
  rule <k> b(X) => c(X) </k>
endmodule
"#;
    let specification = r#"
requires "circularity-probe.k"

module CIRCULARITY-SPEC
  imports CIRCULARITY-PROBE

  claim <k> b(X) => c(X) </k> [label(b-to-c), trusted]
  claim <k> a(X) => d(X) </k> [label(through-circularity)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("circularity-probe.k", definition),
        ("circularity-spec.k", specification),
        "CIRCULARITY-SPEC",
        "CIRCULARITY-PROBE",
        &["through-circularity"],
        // A claim selection keeps only the selected claims as circularities.
        &["--claim", "b-to-c"],
    );
    assert_eq!(leaves, [failed_stuck_leaf("through-circularity")]);

    let specification = r#"
requires "circularity-probe.k"

module DIRECT-SPEC
  imports CIRCULARITY-PROBE

  claim <k> a(X) => d(X) </k> [label(direct)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("circularity-probe.k", definition),
        ("direct-spec.k", specification),
        "DIRECT-SPEC",
        "CIRCULARITY-PROBE",
        &["direct"],
        &[],
    );
    assert_eq!(leaves, [refuted_leaf("direct")]);
}

/// A one-path claim is refuted by a leaf only when the trace kept every successor of every
/// configuration it followed; then that path is the only one. `start(I)` with `I <=Int 0` has the
/// one successor `bad`, since the two rules' conditions are disjoint, and `bad` has none: the
/// one-path claim `start(I) => good` is false there. When the rule tried first overlaps a later
/// one, the sequential step drops the later successor where both apply, and a rule whose
/// right-hand side chooses a value stands for many successors; the leaves those steps reach
/// only fail true claims.
#[test]
fn kprove_certifies_a_one_path_refutation_only_on_a_trace_that_kept_every_successor() {
    let definition = r#"
module ONE-PATH-PROBE
  imports INT
  syntax Pgm ::= start(Int) | "good" | "bad" | "pick" | val(Int)
  configuration <k> $PGM:Pgm </k>
  rule <k> start(I) => good </k> requires I >Int 0
  rule <k> start(I) => bad </k> requires I <=Int 0
  rule <k> pick => val(?X:Int) </k>
endmodule
"#;
    let specification = r#"
requires "one-path-probe.k"

module ONE-PATH-SPEC
  imports ONE-PATH-PROBE

  claim <k> start(I) => good </k> [label(disjoint), one-path]
  claim <k> pick => val(5) </k> [label(chosen-value), one-path]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("one-path-probe.k", definition),
        ("one-path-spec.k", specification),
        "ONE-PATH-SPEC",
        "ONE-PATH-PROBE",
        &["disjoint", "chosen-value"],
        &[],
    );
    assert_eq!(
        verdicts_of(&leaves),
        expected_verdicts(&[("disjoint", "disproved"), ("chosen-value", "failed")]),
        "{leaves:?}"
    );
    assert!(
        leaves[0].2.iter().any(|leaf| leaf == "Stuck (certified)"),
        "{leaves:?}"
    );

    // `bad` is tried first and covers `I ==Int 3`, where `good` also applies: the claim holds
    // there through `good`, which the sequential step drops.
    let definition = r#"
module OVERLAP-PROBE
  imports INT
  syntax Pgm ::= start(Int) | "good" | "bad"
  configuration <k> $PGM:Pgm </k>
  rule <k> start(I) => bad </k> requires I <Int 5
  rule <k> start(I) => good </k> requires I >Int 0
endmodule
"#;
    let specification = r#"
requires "overlap-probe.k"

module OVERLAP-SPEC
  imports OVERLAP-PROBE

  claim <k> start(3) => good </k> [label(overlap), one-path]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("overlap-probe.k", definition),
        ("overlap-spec.k", specification),
        "OVERLAP-SPEC",
        "OVERLAP-PROBE",
        &["overlap"],
        &[],
    );
    assert_eq!(leaves, [failed_stuck_leaf("overlap")]);
}

/// A leaf certifies a refutation through one of its configurations. A claim written with `...`
/// leaves its frame variable in the `<k>` cell once its code has run, so the leaf still rewrites
/// when the frame holds more code; its configuration with the empty frame `.K` has no successor
/// and the counter `1` fails `?M >Int 1`, which refutes the claim. When `.K` itself rewrites, that
/// configuration certifies nothing.
#[test]
fn kprove_certifies_a_leaf_through_its_empty_computation_instance() {
    let definition = r#"
module FRAME-PROBE
  imports INT
  syntax Pgm ::= count(Int)
  configuration <k> $PGM:Pgm </k> <n> 0 </n>
  rule <k> count(I) => count(I -Int 1) ... </k> <n> N => N +Int 1 </n> requires I >Int 0
  rule <k> count(0) => .K ... </k>
endmodule
"#;
    let specification = r#"
requires "frame-probe.k"

module FRAME-SPEC
  imports FRAME-PROBE

  claim <k> count(1) => .K ... </k> <n> 0 => ?M:Int </n> ensures ?M >Int 0 [label(frame-proven)]
  claim <k> count(1) => .K ... </k> <n> 0 => ?M:Int </n> ensures ?M >Int 1 [label(frame-refuted)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("frame-probe.k", definition),
        ("frame-spec.k", specification),
        "FRAME-SPEC",
        "FRAME-PROBE",
        &["frame-proven", "frame-refuted"],
        &[],
    );
    assert_eq!(
        verdicts_of(&leaves),
        expected_verdicts(&[("frame-proven", "proven"), ("frame-refuted", "disproved")]),
        "{leaves:?}"
    );
    assert_eq!(leaves[1], refuted_leaf("frame-refuted"));

    let definition = r#"
module RESTART-PROBE
  imports INT
  syntax Pgm ::= count(Int) | "halt"
  configuration <k> $PGM:Pgm </k> <n> 0 </n>
  rule <k> count(I) => count(I -Int 1) ... </k> <n> N => N +Int 1 </n> requires I >Int 0
  rule <k> count(0) => .K ... </k>
  rule <k> .K => halt </k>
endmodule
"#;
    let specification = r#"
requires "restart-probe.k"

module RESTART-SPEC
  imports RESTART-PROBE

  claim <k> count(1) => .K ... </k> <n> 0 => ?M:Int </n> ensures ?M >Int 1 [label(frame-restarts)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("restart-probe.k", definition),
        ("restart-spec.k", specification),
        "RESTART-SPEC",
        "RESTART-PROBE",
        &["frame-restarts"],
        &[],
    );
    assert_eq!(leaves, [failed_stuck_leaf("frame-restarts")]);
}
