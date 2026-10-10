#![cfg(feature = "cli")]
//! Class tests of the definedness cluster that need the K frontend or the solver
//! (`draft/open-issues-2026-10/tickets/definedness-tickets.md`; the backend ones are in
//! `crates/k-rust-backend/tests/backend/definedness_classes.rs`).
//!
//! Each test states one invariant that follows from what the construct means and checks krust
//! against itself. They are ignored until the ticket that fixes their class lands, and each
//! fails on `934d29e7`.

use std::{
    fs,
    path::PathBuf,
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

/// A fresh directory for one compilation or run.
fn scratch() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let nonce = NEXT.fetch_add(1, Ordering::Relaxed);
    let root =
        std::env::temp_dir().join(format!("k-rust-definedness-{}-{nonce}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    root
}

fn krust(arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(arguments)
        .stdin(Stdio::null())
        .output()
        .unwrap()
}

/// Whether `kcompile` accepts `source` as the module `MAIN`, with its stderr.
fn kcompile_accepts(source: &str) -> (bool, String) {
    let root = scratch();
    let definition = root.join("definition.k");
    fs::write(&definition, source).unwrap();
    let output = krust(&[
        "kcompile",
        "-m",
        "MAIN",
        "-o",
        root.join("out").to_str().unwrap(),
        definition.to_str().unwrap(),
    ]);
    fs::remove_dir_all(&root).unwrap();
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// An equation matches its argument patterns as written, so a function application below its
/// root would match only a subject that spells the same application, never the value it
/// computes; once the instance carries the definedness of what its pattern consumes, such an
/// equation gives a value nowhere. That holds alike at every argument of a collection
/// constructor (a map key, a map value, a set element) and for a list update, which is a
/// function of a list rather than a way to write one: the frontend rejects every one of them,
/// with one verdict.
#[test]
fn a_function_application_is_admitted_alike_at_every_collection_hook_argument() {
    let rules = [
        ("map key", "rule fk(X, (pf(X) |-> V:Int) _M) => V"),
        ("map value", "rule fk(X, (X |-> pf(X)) _M) => 1"),
        ("set element", "rule fs(X, SetItem(pf(X)) _S) => 1"),
        ("list-update index", "rule fl(I, _L [ pi(I) <- 7 ]) => 1"),
        ("list-update value", "rule fl(I, _L [ I <- pi(I) ]) => 1"),
    ];
    let verdicts = rules
        .iter()
        .map(|(position, rule)| {
            let source = format!(
                r"
module MAIN
  imports INT
  imports MAP
  imports SET
  imports LIST
  syntax Foo ::= c() | d()
  syntax Foo ::= pf(Foo) [function]
  syntax Int ::= pi(Int) [function]
  syntax Int ::= fk(Foo, Map) [function] | fs(Foo, Set) [function] | fl(Int, List) [function]
  rule pf(c()) => c()
  rule pi(0) => 0
  {rule}
  configuration <k> $PGM:Int </k>
endmodule
"
            );
            let (accepted, stderr) = kcompile_accepts(&source);
            assert!(
                accepted
                    || stderr.contains("IllegalFunctionOnLhs")
                    || stderr.contains("Illegal function symbol"),
                "{position}: rejected for another reason: {stderr}"
            );
            (*position, accepted)
        })
        .collect::<Vec<_>>();
    assert!(
        verdicts.iter().all(|(_, accepted)| !*accepted),
        "an equation admits a computed position: {verdicts:?}"
    );
}

/// A rewrite rule reads a function application inside a key, value or element of a collection
/// by the value it computes once the variables in it are bound, alike at every argument of a
/// collection constructor: with `f(X) = X + 1`, each rule below applies to the configuration
/// whose collection holds the computed value, and to no other.
#[test]
fn a_rewrite_rule_reads_a_computed_collection_position_by_value() {
    let root = scratch();
    let definition = root.join("definition.k");
    fs::write(
        &definition,
        r"
module MAIN
  imports INT
  imports MAP
  imports SET
  imports LIST
  syntax Int ::= f(Int) [function]
  rule f(X) => X +Int 1
  syntax KItem ::= getk(Int) | getv(Int) | gets(Int) | getl(Int) | done(Int) [symbol(done)]
  configuration <k> $PGM:KItem </k> <m> 1 |-> 10 2 |-> 20 </m> <s> SetItem(2) SetItem(5) </s>
                <l> ListItem(2) </l>
  rule <k> getk(X) => done(V) ...</k> <m> ... f(X) |-> V ... </m>
  rule <k> getv(X) => done(K) ...</k> <m> ... K |-> f(X) ... </m>
  rule <k> gets(X) => done(X) ...</k> <s> ... SetItem(f(X)) ... </s>
  rule <k> getl(X) => done(X) ...</k> <l> ListItem(f(X)) </l>
endmodule
",
    )
    .unwrap();
    let out = root.join("out");
    let compiled = krust(&[
        "kcompile",
        "-m",
        "MAIN",
        "-o",
        out.to_str().unwrap(),
        definition.to_str().unwrap(),
    ]);
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let mut failures = Vec::new();
    for (program, expected) in [
        ("getk(1)", Some(20)),
        ("getv(19)", Some(2)),
        ("gets(1)", Some(1)),
        ("getl(1)", Some(1)),
        ("getk(5)", None),
        ("getv(29)", None),
        ("gets(0)", None),
        ("getl(0)", None),
    ] {
        let output = krust(&[
            "krun",
            "--definition",
            out.to_str().unwrap(),
            "--sort",
            "KItem",
            "--io",
            "off",
            "-e",
            program,
        ]);
        let stdout = String::from_utf8_lossy(&output.stdout).replace([' ', '\n'], "");
        let applied = match expected {
            Some(value) => {
                stdout.contains(&format!(r#"Lbldone{{}}(\dv{{SortInt{{}}}}("{value}"))"#))
            }
            None => !stdout.contains("Lbldone"),
        };
        if !output.status.success() || !applied {
            failures.push((program, expected, stdout));
        }
    }
    fs::remove_dir_all(&root).unwrap();
    assert!(failures.is_empty(), "{failures:#?}");
}

/// `f` is total, and its only equation has a variable its left-hand side does not bind, so an
/// attempt at `f(N)` is reported when the call stays in the result. The condition
/// `f(N) >Int N orBool f(N) <=Int N` holds for every value of `f(N)`. Wherever it sits (an
/// equation's `requires`, a rule's `requires` that the solver or the simplifier decides, or a
/// rule's `ensures`, which the right-hand side's own unit of the rule attempt decides),
/// every run ends in `done(20)`, with no call left anywhere, so the report of a call that no
/// state and no result holds explains nothing: the runs report alike, and none reports.
#[test]
fn a_condition_decided_for_every_value_of_a_call_reports_alike_wherever_it_sits() {
    let header = r"
module MAIN
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  syntax Int ::= k(Int) [function, total, symbol(k)]
  syntax KItem ::= step(Int) [symbol(step)]
  syntax KItem ::= done(Int) [symbol(done)]
  configuration <k> step(0) </k>
  rule [fu]: f(X) => Y requires Y ==Int X +Int 1
  rule <k> step(N) => done(N) </k> requires N >=Int 20
";
    let cases = [
        (
            "equation requires, solver-decided",
            r"
  rule [k1]: k(X) => 1 requires f(X) >Int X orBool f(X) <=Int X
  rule [k2]: k(_) => 2 [owise]
  rule <k> step(N) => step(N +Int k(N)) </k> requires N <Int 20
",
        ),
        (
            "rule requires, solver-decided",
            r"
  rule <k> step(N) => step(N +Int 1) </k> requires N <Int 20 andBool (f(N) >Int N orBool f(N) <=Int N)
",
        ),
        (
            "rule requires, simplifier-decided",
            r"
  rule <k> step(N) => step(N +Int 1) </k> requires N <Int 20 andBool (N >=Int 0 orBool f(N) ==Int 4)
",
        ),
        (
            "rule ensures, solver-decided",
            r"
  rule <k> step(N) => step(N +Int 1) </k> requires N <Int 20 ensures f(N) >Int N orBool f(N) <=Int N
",
        ),
    ];
    let mut reports = Vec::new();
    for (label, rules) in cases {
        let root = scratch();
        let definition = root.join("definition.k");
        fs::write(&definition, format!("{header}{rules}endmodule\n")).unwrap();
        let output = krust(&[
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
        ]);
        fs::remove_dir_all(&root).unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{label}: {stderr}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains(r#"Lbldone{}(\dv{SortInt{}}("20"))"#) && !stdout.contains("Lblf{}"),
            "{label}: {stdout}"
        );
        let warnings = stderr
            .lines()
            .filter(|line| line.starts_with("warning: equation "))
            .count();
        reports.push((label, warnings));
    }
    assert!(
        reports.iter().all(|(_, warnings)| *warnings == 0),
        "a report outlives every term it explains: {reports:?}"
    );
}

/// A rewrite step is a transition: its successor may denote only states some state of its
/// predecessor reaches. `{c |-> 1, Y |-> 2}` is a map only where `Y` is not `c`, so from
/// `f({c |-> 1, Y |-> 2})` the rule `f((c |-> _) M) => rest(M)` reaches `rest(Y |-> 2)` for every
/// `Y` but `c`; a successor `rest(Y |-> 2)` with no constraint also denotes `rest(c |-> 2)`,
/// which nothing reaches. The step must keep the dropped entry's distinctness (a constraint
/// that mentions `c`). The control binds the whole map to a variable, `g(M) => rest(M)`, and
/// keeps it.
#[test]
#[ignore = "reproduces FOLLOWUPS: Evaluator limit 1 (argument patterns) (a rewrite step drops the distinctness of a collection its pattern consumes, definedness-stepback.md)"]
fn a_rewrite_step_keeps_the_distinctness_of_a_collection_it_splits() {
    let root = scratch();
    let definition = root.join("definition.k");
    fs::write(
        &definition,
        r"
module MAIN
  imports INT
  imports MAP
  syntax Foo ::= c() [symbol(c)] | d() [symbol(d)]
  syntax KItem ::= f(Map) [symbol(f)] | g(Map) [symbol(g)] | rest(Map) [symbol(rest)]
  rule <k> f((c() |-> _:Int) M) => rest(M) ...</k>
  rule <k> g(M) => rest(M) ...</k>
  configuration <k> $PGM:KItem </k>
endmodule
",
    )
    .unwrap();
    let out = root.join("out");
    let compiled = krust(&[
        "kcompile",
        "-m",
        "MAIN",
        "-o",
        out.to_str().unwrap(),
        definition.to_str().unwrap(),
    ]);
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let entry = |key: &str, value: u32| {
        format!(
            r#"Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortFoo{{}}, SortKItem{{}}}}({key}), inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}")))"#
        )
    };
    let map = format!(
        "Lbl'Unds'Map'Unds'{{}}({}, {})",
        entry("Lblc{}()", 1),
        entry("VarY:SortFoo{}", 2)
    );
    let mut failures = Vec::new();
    for head in ["g", "f"] {
        let pattern = root.join(format!("{head}.kore"));
        fs::write(
            &pattern,
            format!(
                r#"Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(Lbl{head}{{}}({map}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\dv{{SortInt{{}}}}("0")))"#
            ),
        )
        .unwrap();
        let output = krust(&[
            "kore-exec",
            "-m",
            "MAIN",
            "-p",
            pattern.to_str().unwrap(),
            out.join("definition.kore").to_str().unwrap(),
        ]);
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        assert!(
            output.status.success() && stdout.contains("Lblrest{}"),
            "{head}: {stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if !stdout.contains("Lblc{}()") {
            failures.push((head, stdout));
        }
    }
    fs::remove_dir_all(&root).unwrap();
    assert!(
        failures.is_empty(),
        "a successor admits a state nothing reaches: {failures:#?}"
    );
}
