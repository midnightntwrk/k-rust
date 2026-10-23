//! The open-obligation round trip that the regeneration scripts and the gate rely on, through the
//! `k2lean` binary on the `peano` fixture: a name in `--open-obligations` becomes a `Prop`
//! statement (no theorem, no axiom, not under the axiom guard), and `open-from-log` turns the
//! errors of a Lake build log into exactly the names of the failed theorems.

use std::path::{Path, PathBuf};
use std::process::Command;

const PLUS_2: &str = "Eqn.«plus(_,_)_PEANO_Nat_Nat_Nat_2»";
const DOUBLE_1: &str = "Eqn.«double(_)_PEANO_Nat_Nat_1»";

fn tmp(name: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn gen_peano(out: &Path, open: Option<&Path>) -> String {
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/peano");
    let mut c = Command::new(env!("CARGO_BIN_EXE_k2lean"));
    c.arg("gen")
        .arg("--kore")
        .arg(fx.join("definition.kore"))
        .arg("--runtime")
        .arg(fx.join("runtime.json"));
    c.arg("--out")
        .arg(out)
        .args(["--name", "Peano", "--prelude", "../../prelude"]);
    if let Some(o) = open {
        c.arg("--open-obligations").arg(o);
    }
    let o = c.output().unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    String::from_utf8_lossy(&o.stderr).into_owned()
}

#[test]
fn open_obligation_is_a_statement_not_a_theorem() {
    let d = tmp("cli-open");
    let open = d.join("open.txt");
    std::fs::write(&open, format!("{PLUS_2}\n")).unwrap();
    let log = gen_peano(&d.join("out"), Some(&open));
    assert!(
        log.contains("11 equations and simplifications stated, 1 open"),
        "{log}"
    );
    let eqns = std::fs::read_to_string(d.join("out/Peano/Equations.lean")).unwrap();
    assert!(
        eqns.contains(&format!(
            "def {PLUS_2}.statement : Prop :=∀ (M : SortNat) (N : SortNat),"
        )),
        "{eqns}"
    );
    assert!(!eqns.contains(&format!("theorem {PLUS_2}")));
    assert!(eqns.contains("theorem Eqn.«plus(_,_)_PEANO_Nat_Nat_Nat_1»"));
    let guard = std::fs::read_to_string(d.join("out/PeanoTest/Axioms.lean")).unwrap();
    assert!(
        !guard.contains(PLUS_2),
        "an open obligation must not be under the axiom guard"
    );
    assert!(guard.contains("Peano.Eqn.«plus(_,_)_PEANO_Nat_Nat_Nat_1»"));
    assert!(!eqns.contains("\naxiom ") && !eqns.contains("sorry"));
}

#[test]
fn open_from_log_adds_exactly_the_failed_theorems() {
    let d = tmp("cli-log");
    gen_peano(&d.join("out"), None);
    let eq_file = d.join("out/Peano/Equations.lean");
    let text = std::fs::read_to_string(&eq_file).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    // an error inside DOUBLE_1's proof (two lines below its `theorem` line), one on PLUS_2's own
    // statement line, and a warning in another theorem (which must be ignored)
    let at = |name: &str| {
        lines
            .iter()
            .position(|l| l.starts_with(&format!("theorem {name} ")))
            .unwrap()
            + 1
    };
    let log = format!(
        "✖ [3/4] Building Peano.Equations\nerror: Peano/Equations.lean:{}:4: unsolved goals\nerror: Peano/Equations.lean:{}:140: unsolved goals\nwarning: Peano/Equations.lean:{}:2: unused variable\ninfo: Peano/Equations.lean:1:0: note\n",
        at(DOUBLE_1) + 2,
        at(PLUS_2),
        at("Eqn.«pick(_,_)_PEANO_Nat_B_Nat_1»") + 1,
    );
    std::fs::write(d.join("build.log"), log).unwrap();
    let open = d.join("open.txt");
    std::fs::write(&open, "Simp.s_kept\n").unwrap();
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("open-from-log")
        .args([&eq_file, &d.join("build.log"), &open])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let got = std::fs::read_to_string(&open).unwrap();
    let mut want = [DOUBLE_1, PLUS_2, "Simp.s_kept"];
    want.sort();
    assert_eq!(got, want.join("\n") + "\n");
}

/// `gen --sidecar` on the `counter` fixture (`<T> <k> … </k> <env> … </env> </T>`): the cell is
/// read through one projection per level, the declared sorts become projections out of `KItem`,
/// a case named in `open-invariant-cases.txt` is taken from the hand module (whose skeleton is
/// written once and then left alone), and the init theorem takes no hypothesis because `<env>`
/// starts as `.Map`.
#[test]
fn sidecar_invariant_reads_nested_cells_and_routes_open_cases_to_the_hand_module() {
    let d = tmp("cli-invariant");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/counter");
    let side = d.join("sidecar.json");
    std::fs::write(
        &side,
        r#"{"format": "k2lean-krs-sidecar", "version": 1, "cells": [
             {"cell": "Lbl'-LT-'env'-GT-'", "krs": "env: Map<Id, Int>", "collection": "Map", "key": "SortId", "value": "SortInt"}]}"#,
    )
    .unwrap();
    let out = d.join("out");
    std::fs::create_dir_all(&out).unwrap();
    std::fs::write(
        out.join("open-invariant-cases.txt"),
        "# a comment\n«incr»\n",
    )
    .unwrap();
    let run = || {
        let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
            .arg("gen")
            .arg("--kore")
            .arg(fx.join("definition.kore"))
            .arg("--runtime")
            .arg(fx.join("runtime.json"))
            .arg("--out")
            .arg(&out)
            .args([
                "--name",
                "Counter",
                "--prelude",
                "../../prelude",
                "--sidecar",
            ])
            .arg(&side)
            .output()
            .unwrap();
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    };
    run();
    let defs = std::fs::read_to_string(out.join("Counter/InvariantDefs.lean")).unwrap();
    assert!(
        defs.contains("def Invariant.cell_T : SortGeneratedTopCell → SortTCell"),
        "{defs}"
    );
    assert!(
        defs.contains("def Invariant.cell_env : SortTCell → SortEnvCell"),
        "{defs}"
    );
    assert!(
        defs.contains("(∃ y, proj_KItem_Id p.1 = some y) ∧ (∃ y, proj_KItem_Int p.2 = some y)"),
        "{defs}"
    );
    assert!(defs.contains("KPrelude.MapHook.EntriesOn Invariant.entry_env (Invariant.content_env (Invariant.cell_env (Invariant.cell_T c)))"), "{defs}");
    let thms = std::fs::read_to_string(out.join("Counter/Invariants.lean")).unwrap();
    assert!(thms.contains("import Counter.InvariantsHand"), "{thms}");
    assert!(
        thms.contains("theorem incr : Step.Case.incr Invariant := Invariant.hand.incr"),
        "{thms}"
    );
    assert!(
        thms.contains("theorem Invariant.init_holds (pgm : SortPgm) :"),
        "{thms}"
    );
    let open = std::fs::read_to_string(out.join("open-invariant-cases.txt")).unwrap();
    assert!(
        open.lines()
            .any(|l| l.starts_with("incr | Step.Case.incr Invariant | counter.k:")),
        "{open}"
    );
    let hand = out.join("Counter/InvariantsHand.lean");
    assert!(
        std::fs::read_to_string(&hand)
            .unwrap()
            .contains("-- theorem Invariant.hand.incr : Step.Case.incr Invariant")
    );
    // a second generation leaves the hand module as the user left it
    std::fs::write(&hand, "-- mine\n").unwrap();
    run();
    assert_eq!(std::fs::read_to_string(&hand).unwrap(), "-- mine\n");
}

/// `gen --invariant cntOk@cnt` on the `cellmap` fixture, where `<cnt>` is inside the cell map of
/// `<worker>`s: the part is lifted to "for every element", stated as `EntriesOn` of an element
/// predicate over the cell map read through one projection per level, the element predicate reads
/// the cell off the binding's value, and since the cell map is empty in `init` the init theorem is
/// proved by computation, with no hypothesis and no obligation.
#[test]
fn invariant_inside_a_cell_map_is_lifted_to_every_element() {
    let d = tmp("cli-cellmap");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/cellmap");
    let out = d.join("out");
    std::fs::create_dir_all(&out).unwrap();
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("gen")
        .arg("--kore")
        .arg(fx.join("definition.kore"))
        .arg("--runtime")
        .arg(fx.join("runtime.json"))
        .arg("--out")
        .arg(&out)
        .args([
            "--name",
            "CellMap",
            "--prelude",
            "../../prelude",
            "--invariant",
            "cntOk@cnt",
        ])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let defs = std::fs::read_to_string(out.join("CellMap/InvariantDefs.lean")).unwrap();
    assert!(
        defs.contains("def Invariant.content_workers : SortWorkersCell → SortWorkerCellMap"),
        "{defs}"
    );
    assert!(
        defs.contains("def Invariant.cell_cnt : SortWorkerCell → SortCntCell"),
        "{defs}"
    );
    assert!(defs.contains("def Invariant.cntOk_elem (p : SortWidCell × SortWorkerCell) : Prop :=\n  K.«cntOk(_)_CELLMAP_Bool_Int» (Invariant.content_cnt (Invariant.cell_cnt p.2)) = true"), "{defs}");
    assert!(defs.contains("KPrelude.MapHook.EntriesOn Invariant.cntOk_elem (Invariant.content_workers (Invariant.cell_workers (Invariant.cell_T c)))"), "{defs}");
    let thms = std::fs::read_to_string(out.join("CellMap/Invariants.lean")).unwrap();
    assert!(thms.contains("k2l_preserve [Invariant.cntOk, Invariant.cell_T, Invariant.cell_workers, Invariant.content_workers, Invariant.cell_cnt, Invariant.content_cnt, Invariant.cntOk_elem,"), "{thms}");
    assert!(thms.contains("theorem Invariant.init_holds (pgm : SortPgm) :\n    Invariant (init pgm) :=\n  (by simp only [Invariant, Invariant.cntOk,"), "{thms}");
    assert!(!thms.contains("Invariant.hand.init"), "{thms}");
}

fn gen_fixture(dir: &Path, out: &Path, ns: &str) {
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("gen")
        .arg("--kore")
        .arg(dir.join("definition.kore"))
        .arg("--runtime")
        .arg(dir.join("runtime.json"))
        .arg("--out")
        .arg(out)
        .args(["--name", ns, "--prelude", "../../prelude"])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
}

/// `k2lean diff` on two krust compilations of the `diff` fixture (`gate/fixtures/diff/{old,new}.k`,
/// whose header comment lists the edits): every line moved, one rule changed, three renamed with
/// an equal statement (a relabelling, a focus edit that renames a variable, a collision that adds
/// a digest), one renamed and changed, one added, one removed; and the hand-written references
/// that a user should revisit, from a Lean file and from a kind 1 `open-invariant-cases.txt`. A
/// generated file is not read, and a generation compared with itself has no difference.
#[test]
fn diff_names_the_changed_renamed_added_and_removed_rules_and_the_hand_cases_to_revisit() {
    let d = tmp("cli-diff");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/diff");
    gen_fixture(&fx.join("old"), &d.join("old"), "Diff");
    gen_fixture(&fx.join("new"), &d.join("new"), "Diff");
    let hand = d.join("hand");
    std::fs::create_dir_all(hand.join(".lake")).unwrap();
    std::fs::write(
        hand.join("Cases.lean"),
        "theorem a : Diff.Step.Case.start P := x\ntheorem b : Diff.Step.Case.«done(s(z))» P := x\ntheorem c : Diff.Step.Case.«done(s(s(N)))» P := x\nexample := Diff.App.«stop(s(s(N)))»\n  case start N g => exact h\n",
    )
    .unwrap();
    std::fs::write(
        hand.join("open-invariant-cases.txt"),
        "# kind 1\n«back(z)» | Step.Case.«back(z)» Invariant | old.k:15:3\n",
    )
    .unwrap();
    std::fs::write(
        hand.join("Gen.lean"),
        "/-! Generated by k2lean; do not edit. -/\nexample := Diff.Step.«halt(N)»\n",
    )
    .unwrap();
    std::fs::write(
        hand.join(".lake/Ignored.lean"),
        "example := Diff.Step.«halt(N)»\n",
    )
    .unwrap();
    let toml = d.join("diff.toml");
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("diff")
        .arg(d.join("old"))
        .arg(d.join("new"))
        .arg("--hand")
        .arg(&hand)
        .arg("--toml")
        .arg(&toml)
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&o.stdout);
    assert_eq!(
        o.status.code(),
        Some(1),
        "{out}{}",
        String::from_utf8_lossy(&o.stderr)
    );
    assert!(out.contains("7 -> 8 rules"), "{out}");
    assert!(out.contains("changed 1, added 2, removed 1, renamed 3 (same statement), renamed and changed 1 (suggested), context changed 0; unchanged 1 (1 moved)"), "{out}");
    assert!(
        out.contains("  «done(s(z))»  old.k:13:3 -> new.k:19:3: right-hand side differs"),
        "{out}"
    );
    assert!(
        out.contains("  start -> begin  old.k:11:3 -> new.k:17:3"),
        "{out}"
    );
    assert!(out.contains("  «back(s(N))» -> «back(s(M))»"), "{out}");
    assert!(out.contains("  «halt(N)» -> «halt(N:Nat) #"), "{out}");
    assert!(out.contains("  «stop(s(s(N)))» -> «stop(s(N))»?"), "{out}");
    assert!(out.contains("added:\n  «halt(N:Nat) #"), "{out}");
    assert!(out.contains("  «run(z)»  new.k:24:3"), "{out}");
    assert!(out.contains("removed:\n  «back(z)»  old.k:15:3"), "{out}");
    assert!(out.contains("(files read: 2)"), "{out}");
    assert!(out.contains("revisit 4 rule(s):"), "{out}");
    assert!(
        out.contains("  start: renamed to begin (same statement): rename the reference\n"),
        "{out}"
    );
    assert!(
        out.contains("  «done(s(z))»: changed (right-hand side differs)\n"),
        "{out}"
    );
    assert!(out.contains("  «back(z)»: removed\n"), "{out}");
    assert!(out.contains("open-invariant-cases.txt:2 (case)"), "{out}");
    assert!(out.contains("  «stop(s(s(N)))»: probably renamed to «stop(s(N))» and changed (left-hand side differs)\n"), "{out}");
    assert!(out.contains("Cases.lean:4 (app)"), "{out}");
    assert!(out.contains("Cases.lean:5 (case tag)"), "{out}");
    assert!(out.contains("  unaffected: «done(s(s(N)))»\n"), "{out}");
    assert!(
        !out.contains("«halt(N)»:"),
        "a generated file and .lake/ are not hand-written:\n{out}"
    );
    let t = std::fs::read_to_string(&toml).unwrap();
    assert!(
        t.contains("[summary]\n")
            && t.contains("changed = 1\n")
            && t.contains("[[revisit]]\nrule = \"«done(s(z))»\""),
        "{t}"
    );
    // the same generation twice
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("diff")
        .arg(d.join("old"))
        .arg(d.join("old"))
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&o.stdout);
    assert_eq!(o.status.code(), Some(0), "{out}");
    assert!(out.contains("changed 0, added 0, removed 0, renamed 0 (same statement), renamed and changed 0 (suggested), context changed 0; unchanged 7 (0 moved)"), "{out}");
}

/// `k2lean new-invariant` on the peano library: the kind 2 skeleton (lakefile requiring the
/// library and the prelude by relative paths, `Invariant`, `Cases` with the hand namespace and
/// `preserved`, `Run` with `init` at its configuration variable), never overwritten; then
/// `--from-log` inserts one stub per open rule (with the rule's variables introduced), once.
#[test]
fn new_invariant_writes_the_skeleton_once_and_adds_stubs_for_open_rules() {
    let d = tmp("cli-new-invariant");
    gen_peano(&d.join("lib"), None);
    std::fs::create_dir_all(d.join("prelude")).unwrap();
    let run = |extra: &[&str]| {
        let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
            .arg("new-invariant")
            .arg("--lib")
            .arg(d.join("lib"))
            .arg("--out")
            .arg(d.join("proj/PeanoInv"))
            .arg("--prelude")
            .arg(d.join("prelude"))
            .args(extra)
            .output()
            .unwrap();
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
        String::from_utf8_lossy(&o.stderr).into_owned()
    };
    let log = run(&[]);
    assert!(log.contains("wrote ") && !log.contains("kept "), "{log}");
    let p = d.join("proj/PeanoInv");
    let lake = std::fs::read_to_string(p.join("lakefile.lean")).unwrap();
    assert!(
        lake.contains(
            "require KPrelude from \"../../prelude\"\nrequire «Peano» from \"../../lib\"\n"
        ),
        "{lake}"
    );
    let cases = std::fs::read_to_string(p.join("PeanoInv/Cases.lean")).unwrap();
    assert!(cases.contains("theorem preserved : Preserved Peano.Step Invariant := by\n  k2l_preserve hand PeanoInv.hand\n"), "{cases}");
    let runf = std::fs::read_to_string(p.join("PeanoInv/Run.lean")).unwrap();
    assert!(
        runf.contains("theorem init_holds (pgm : Peano.SortPgm) : Invariant (Peano.init pgm) :="),
        "{runf}"
    );
    assert!(
        runf.contains("#k2l_assert_axioms preserved init_holds star stepsN"),
        "{runf}"
    );
    std::fs::write(p.join("PeanoInv/Invariant.lean"), "-- mine\n").unwrap();
    assert!(run(&[]).contains("kept "));
    assert_eq!(
        std::fs::read_to_string(p.join("PeanoInv/Invariant.lean")).unwrap(),
        "-- mine\n"
    );
    let blog = d.join("build.log");
    std::fs::write(&blog, "info: PeanoInv/Cases.lean:34:2: k2l_preserve: 1 of 2 rules closed; open: [«done(s(s(N)))»]\n").unwrap();
    let args = [
        "--from-log",
        blog.to_str().unwrap(),
        "--params",
        "(n : Nat)",
        "--pred",
        "Inv n",
    ];
    assert!(run(&args).contains("1 stub(s) added"));
    let cases = std::fs::read_to_string(p.join("PeanoInv/Cases.lean")).unwrap();
    assert!(cases.contains("theorem «done(s(s(N)))» (n : Nat) : Peano.Step.Case.«done(s(s(N)))» (Inv n) := by\n  intro N DotVar0\n  intro h\n  done\n"), "{cases}");
    assert!(
        cases.find("theorem «done(s(s(N)))»").unwrap()
            < cases.find("-- k2lean new-invariant --from-log").unwrap()
    );
    assert!(run(&args).contains("has a hand case already"));
    assert_eq!(
        cases,
        std::fs::read_to_string(p.join("PeanoInv/Cases.lean")).unwrap()
    );
}
