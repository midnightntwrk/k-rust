#![cfg(feature = "cli")]
//! Reproducers of the "Backend behaviour, diagnostics and test adequacy" follow-ups
//! (`draft/open-issues-2026-10/FOLLOWUPS.md` §2.2). Each test is ignored while its item is open
//! and states the behaviour the item asks for; it fails on main `934d29e7`.

use std::{
    fs,
    path::PathBuf,
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

fn scratch() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "k-rust-backend-followups-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&root).unwrap();
    root
}

fn krust(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(args)
        .stdin(Stdio::null())
        .output()
        .unwrap()
}

/// Write `source` as `<module>.k` in a new scratch directory and `krun` the program `go` on it.
fn krun_go(module: &str, source: &str, extra: &[&str]) -> (Output, PathBuf) {
    let root = scratch();
    let file = root.join(format!("{}.k", module.to_lowercase()));
    fs::write(&file, source).unwrap();
    let mut args = vec![
        "krun",
        file.to_str().unwrap(),
        "-m",
        module,
        "-s",
        "Pgm",
        "-e",
        "go",
        "--io",
        "off",
    ];
    args.extend_from_slice(extra);
    let output = krust(&args);
    (output, root)
}

/// A sort hooked to `BYTES.Bytes` under another name than `Bytes` is a `Bytes` sort: its values
/// are byte strings, and `BYTES.length` of `b"abc"` is 3 whatever the sort is called. On main the
/// application halts the run as an unsupported hook on constructor-like arguments.
#[test]
#[ignore = "reproduces FOLLOWUPS: `BYTES` hooks recognize the sort only by its KORE name"]
fn bytes_hooks_evaluate_a_renamed_bytes_sort() {
    const SOURCE: &str = r#"
module MYBYTES
  imports INT
  syntax MyBytes [hook(BYTES.Bytes), token]
  syntax MyBytes ::= r"b[\\\"](([\\x20\\x21\\x23-\\x5B\\x5D-\\x7E])|([\\\\][tnfr\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]" [token]
  syntax Int ::= lengthMyBytes(MyBytes) [function, total, hook(BYTES.length)]
  syntax Pgm ::= MyBytes
  configuration <k> $PGM:Pgm </k>
  rule <k> B:MyBytes => lengthMyBytes(B) </k>
endmodule
"#;
    let root = scratch();
    let file = root.join("mybytes.k");
    fs::write(&file, SOURCE).unwrap();
    let output = krust(&[
        "krun",
        file.to_str().unwrap(),
        "-m",
        "MYBYTES",
        "-s",
        "Pgm",
        "-e",
        r#"b"abc""#,
        "--io",
        "off",
    ]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}{stderr}");
    assert!(stdout.contains(r#"\dv{SortInt{}}("3")"#), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// `replace` (hook `STRING.replace`, no evaluator here) has equations in `domains.md`, which the
/// compiled definition holds. Where they do not apply (a count that is not a value), the warning
/// must not say that the definition has no equations for it.
#[test]
#[ignore = "reproduces FOLLOWUPS: `STRING.replace` warning text is misleading"]
fn an_unevaluated_hook_with_equations_is_not_reported_as_having_none() {
    const SOURCE: &str = r#"
module REPLACE-COUNT
  imports STRING
  imports INT
  syntax Int ::= count() [function, no-evaluators]
  syntax Pgm ::= "go"
  configuration <k> $PGM:Pgm </k> <out> "" </out>
  rule <k> go => .K </k> <out> _ => replace("aa", "a", "b", count()) </out>
endmodule
"#;
    let (output, root) = krun_go("REPLACE-COUNT", SOURCE, &[]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains("hook STRING.replace was left unevaluated"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("no equations in the definition"),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// An undecided-condition warning gives its reason in words, not as a Rust `Debug` value, and
/// explains every backend-marked variable it prints (`Eq-hVarY` here is `f`'s variable `Y`,
/// which reached `h`'s subject while `f`'s `requires` was simplified). The cube sum is a query Z3
/// does not settle within 20 ms.
#[test]
#[ignore = "reproduces FOLLOWUPS: Opaque `krun` diagnostics"]
fn undecided_condition_warnings_explain_their_reason_and_variables() {
    const SOURCE: &str = r#"
module EQVAR
  imports INT
  syntax Int ::= a() [function, no-evaluators]
               | b() [function, no-evaluators]
               | h(Int) [function]
               | f(Int) [function]
  rule h(Z) => 0 requires Z *Int Z *Int Z +Int a() *Int a() *Int a() +Int b() *Int b() *Int b() ==Int 42
  rule f(X) => 1 requires h(Y) ==Int X
  syntax Pgm ::= "go"
  configuration <k> $PGM:Pgm </k> <out> 0 </out>
  rule <k> go => .K </k> <out> _ => f(0) </out>
endmodule
"#;
    let (output, root) = krun_go(
        "EQVAR",
        SOURCE,
        &["--smt-timeout", "20", "--smt-retry-limit", "0"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    let warnings = stderr
        .lines()
        .filter(|line| line.contains("remained undecided"))
        .collect::<Vec<_>>();
    assert!(!warnings.is_empty(), "{stderr}");
    let marked = regex::Regex::new(r"Eq-h[A-Za-z0-9'-]+").unwrap();
    for warning in warnings {
        assert!(!warning.contains("SmtUnknown("), "{warning}");
        for name in marked.find_iter(warning) {
            assert!(
                warning.contains(&format!("{} is ", name.as_str())),
                "{} is not explained: {warning}",
                name.as_str()
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}

/// `kast --batch-case` accepts every program the single-case `kast --output json` accepts and
/// writes the same term: here 62 nested negations, which the single case prints and the batch
/// refuses on main with serde_json's recursion limit.
#[test]
#[ignore = "reproduces FOLLOWUPS: `kast --batch-case` re-reads each case's pretty JSON into a `serde_json::Value`"]
fn kast_batch_accepts_what_a_single_case_accepts() {
    let root = scratch();
    let file = root.join("neg.k");
    fs::write(
        &file,
        "module NEG\n  imports INT-SYNTAX\n  syntax Exp ::= Int | \"-\" Exp\nendmodule\n",
    )
    .unwrap();
    let program = format!("{}1", "- ".repeat(62));
    let definition = file.to_str().unwrap();
    let single = krust(&[
        "kast", definition, "-m", "NEG", "-s", "Exp", "-e", &program, "--output", "json",
    ]);
    assert!(
        single.status.success(),
        "{}",
        String::from_utf8_lossy(&single.stderr)
    );
    let batch = krust(&[
        "kast",
        definition,
        "-m",
        "NEG",
        "--batch-case",
        "deep",
        "Exp",
        &program,
        "--output",
        "json",
    ]);
    assert!(
        batch.status.success(),
        "{}",
        String::from_utf8_lossy(&batch.stderr)
    );
    let compact = |bytes: &[u8]| {
        String::from_utf8_lossy(bytes)
            .chars()
            .filter(|character| !character.is_ascii_whitespace())
            .collect::<String>()
    };
    assert!(
        compact(&batch.stdout).contains(&compact(&single.stdout)),
        "the batch case's term differs from the single case's"
    );
    fs::remove_dir_all(root).unwrap();
}

/// When the system refuses to map a simplification stack segment (here under an address-space
/// limit), the run reports its stop alone: no `stacker` panic text precedes it.
#[test]
#[ignore = "reproduces FOLLOWUPS: Stacker panic text before `StackExhausted`"]
fn a_refused_stack_segment_prints_no_panic_text() {
    const SOURCE: &str = r#"
module DEEP
  imports INT
  syntax Nat ::= "z" | c(Nat)
  syntax Int ::= size(Nat) [function]
  rule size(z) => 0
  rule size(c(T)) => 1 +Int size(T)
  syntax Pgm ::= build(Int, Nat)
  configuration <k> $PGM:Pgm </k>
  rule <k> build(N, T) => build(N -Int 1, c(T)) ... </k> requires N >Int 0
  rule <k> build(0, T) => size(T) ... </k>
endmodule
"#;
    let root = scratch();
    let file = root.join("deep.k");
    fs::write(&file, SOURCE).unwrap();
    let compiled = root.join("deep-out");
    let compile = krust(&[
        "kcompile",
        file.to_str().unwrap(),
        "-m",
        "DEEP",
        "-o",
        compiled.to_str().unwrap(),
    ]);
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let output = Command::new("sh")
        .arg("-c")
        .arg(r#"ulimit -v 500000; exec "$0" krun --definition "$1" -s Pgm -e 'build(100000, z)' --io off"#)
        .arg(env!("CARGO_BIN_EXE_krust"))
        .arg(&compiled)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("panicked at"), "{stderr}");
    fs::remove_dir_all(root).unwrap();
}
