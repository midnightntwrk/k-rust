#![cfg(feature = "cli")]
//! Tests of the "Backend behaviour, diagnostics and test adequacy" follow-ups
//! (`draft/open-issues-2026-10/FOLLOWUPS.md` §2.2). The one ignored test states a behaviour krust
//! deliberately does not have; its `ignore` names the documented deviation it would contradict.

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

/// Read by its hook, a sort hooked to `BYTES.Bytes` under another name than `Bytes` would be a
/// `Bytes` sort, and `BYTES.length` of `b"abc"` would be 3 whatever the sort is called. krust
/// stores a domain value by its KORE sort's name, since a pattern outside the definition carries
/// only that name, so the renamed sort holds UTF-8 code points, and the `BYTES` hooks evaluate
/// values of `SortBytes` only: the application halts the run as an unsupported hook on
/// constructor-like arguments.
#[test]
#[ignore = "kept deviation (docs/compatibility.md, \"Strings and their literals\"): `BYTES` hooks \
            evaluate values of the sort named `Bytes` only, so a renamed `BYTES.Bytes` sort's \
            hook application halts the run as unsupported"]
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

/// An undecided-condition warning gives its reason in words, not as a Rust `Debug` value, and
/// explains every backend-marked variable it prints (`Eq-hVarY` here is `f`'s variable `Y`,
/// which reached `h`'s subject while `f`'s `requires` was simplified). The cube sum is a query Z3
/// does not settle within 20 ms.
#[test]
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
/// writes the same term: two spellings of one request give one answer. Here 62 nested
/// negations, past serde_json's default recursion limit of 128 nested values.
#[test]
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

/// `kcompile` a definition whose program `build(n, z)` builds the term `c^n(z)` in `n` rewrite
/// steps and then evaluates the recursive function `size` on it, which descends `n` levels in the
/// simplifier, and `krun` `build(levels, z)` on it once for each limit of `limits_kib`, with the
/// process's address space limited to that many KiB (`ulimit -v`).
fn krun_deep_under_address_limits(levels: usize, limits_kib: &[usize]) -> Vec<Output> {
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
    let outputs = limits_kib
        .iter()
        .map(|limit_kib| {
            Command::new("sh")
                .arg("-c")
                .arg(
                    r#"ulimit -v "$3"; exec "$0" krun --definition "$1" -s Pgm -e "build($2, z)" --io off"#,
                )
                .arg(env!("CARGO_BIN_EXE_krust"))
                .arg(&compiled)
                .arg(levels.to_string())
                .arg(limit_kib.to_string())
                .stdin(Stdio::null())
                .output()
                .unwrap()
        })
        .collect();
    fs::remove_dir_all(root).unwrap();
    outputs
}

/// A stop names the limit that stopped it. Under an address space of about 300 MB, far below the
/// thread's 1 GiB stack budget, a recursion 200,000 levels deep (about 5 KiB of stack per level
/// in a release build and more in the others, so several times the address space) fails: the
/// run does not succeed, and its stop never claims that a recursion exhausted the thread's
/// budget, which it did not reach. The recursion maps 16 MiB stack segments while the heap grows
/// by smaller steps, and which of the two requests the system refuses first depends on how far
/// the last segment left the address space from its limit; when the heap's is refused the
/// process aborts with the allocator's message instead of a stop. The limits below are spaced
/// by less than a segment, so the remaining room after the last segment differs between them,
/// and at least one run is stopped by the refusal to map a segment, with a stop that names it.
/// The `stacker` crate's own panic text for the refused mapping may print before the stop; it is
/// accepted output of a fail-fast stop, so only the stop is asserted.
#[test]
fn a_refused_stack_segment_stops_naming_the_refused_mapping() {
    let outputs = krun_deep_under_address_limits(200_000, &[300_000, 305_000, 310_000, 315_000]);
    let mut named = 0;
    for output in &outputs {
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{stderr}");
        let Some(stop) = stderr.lines().find(|line| line.starts_with("error: ")) else {
            continue;
        };
        assert!(
            stop.contains("simplification exhausted its native stack: the system refused to map"),
            "{stderr}"
        );
        assert!(!stop.contains("a recursion went too deep"), "{stderr}");
        named += 1;
    }
    assert!(named > 0, "no run was stopped by a refused segment");
}
