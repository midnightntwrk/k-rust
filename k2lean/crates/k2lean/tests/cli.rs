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
/// proved by computation, with no hypothesis and no obligation. The unfolding set has both
/// equations of `isCount`, the `owise` one included.
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
    assert!(
        thms.contains(
            "Eqn.«isCount(_)_CELLMAP_Bool_KItem_1», Eqn.«isCount(_)_CELLMAP_Bool_KItem_2»"
        ),
        "{thms}"
    );
    assert!(thms.contains("theorem Invariant.init_holds (pgm : SortPgm) :\n    Invariant (init pgm) :=\n  (by simp only [Invariant, Invariant.cntOk,"), "{thms}");
    assert!(!thms.contains("Invariant.hand.init"), "{thms}");
}

/// `gen --invariant even@v` on the `nested` fixture, where `<v>` is inside the cell map of
/// `<member>`s, which is inside the cell map of `<group>`s: the part is lifted over both, the
/// element predicate of a group being the inner collection's predicate of its members; `even` is
/// structurally recursive on `Nat` (`even(s(s(N))) => even(N)`), so its K equations join the
/// unfolding set instead of a note; init's collections are literals of closed cells, so the init
/// theorem is proved by computation.
#[test]
fn invariant_inside_two_nested_cell_maps_is_lifted_twice() {
    let d = tmp("cli-nested");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nested");
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
            "KNested",
            "--prelude",
            "../../prelude",
            "--invariant",
            "even@v",
        ])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(!err.contains("is neither a list fold"), "{err}");
    let defs = std::fs::read_to_string(out.join("KNested/InvariantDefs.lean")).unwrap();
    assert!(defs.contains("def Invariant.even_elem (p : SortMidCell × SortMemberCell) : Prop :=\n  K.«even(_)_NESTED_Bool_Nat» (Invariant.content_v (Invariant.cell_v p.2)) = some true"), "{defs}");
    assert!(defs.contains("def Invariant.even_in_group (p : SortGidCell × SortGroupCell) : Prop :=\n  KPrelude.MapHook.EntriesOn Invariant.even_elem (Invariant.content_members (Invariant.cell_members p.2))"), "{defs}");
    assert!(defs.contains("def Invariant.even (c : SortGeneratedTopCell) : Prop :=\n  KPrelude.MapHook.EntriesOn Invariant.even_in_group (Invariant.content_groups (Invariant.cell_groups c))"), "{defs}");
    let thms = std::fs::read_to_string(out.join("KNested/Invariants.lean")).unwrap();
    assert!(thms.contains("Invariant.even_elem, Invariant.even_in_group, Eqn.«even(_)_NESTED_Bool_Nat_1», Eqn.«even(_)_NESTED_Bool_Nat_2», Eqn.«even(_)_NESTED_Bool_Nat_3»"), "{thms}");
    assert!(thms.contains("theorem Invariant.init_holds (pgm : SortCmd) :\n    Invariant (init pgm) :=\n  (by simp only [Invariant, Invariant.even,"), "{thms}");
    assert!(!thms.contains("Invariant.hand.init"), "{thms}");
}

/// `gen --invariant storeNat@store` on the `range` fixture, whose `alloc` extends the store by
/// `fill(A, B, V)`, a map built by recursion on an `Int` range (`.Map` above `B`, `A |-> V` added
/// below): the definitions get the `@[k2l_coll]` lemma that its result binds `V` at each key,
/// from its two equations, which the collections closer applies to the map a rule binds, and import
/// the equations it names.
#[test]
fn a_map_built_on_an_int_range_gets_its_entries_lemma() {
    let d = tmp("cli-range");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/range");
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
            "KRange",
            "--prelude",
            "../../prelude",
            "--invariant",
            "storeNat@store",
        ])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let defs = std::fs::read_to_string(out.join("KRange/InvariantDefs.lean")).unwrap();
    // the lemma's proof names `fill`'s equations, so the definitions import them
    assert!(
        defs.starts_with("import KRange.Preserves\nimport KRange.Equations\n"),
        "{defs}"
    );
    let f = "K.«fill(_,_,_)_RANGE_Map_Int_Int_Int»";
    assert!(defs.contains(&format!("@[k2l_coll] theorem Invariant.«range_fill(_,_,_)_RANGE_Map_Int_Int_Int» {{Q : SortKItem × SortKItem → Prop}} {{a b : SortInt}} {{V : SortInt}} {{r : SortMap}}\n    (h : {f} a b V = some r) (hq : ∀ a, Q (SortKItem.inj_Int a, (SortKItem.inj_Int V))) : KPrelude.MapHook.EntriesOn Q r :=\n  KPrelude.MapHook.entriesOn_of_range (f := fun a => {f} a b V) (key := fun a => SortKItem.inj_Int a)\n    (fun a ha => by rw [Eqn.«fill(_,_,_)_RANGE_Map_Int_Int_Int_1»]; exact ha)\n    (fun a ha => by rw [Eqn.«fill(_,_,_)_RANGE_Map_Int_Int_Int_2»]; (try simp only [Option.bind_fun_some]); exact ha) hq h")), "{defs}");
    // `natVals` is a list fold, `storeNat` and `isNat` are not recursive: no other lemma
    assert_eq!(defs.matches("@[k2l_coll]").count(), 1, "{defs}");
}

/// `gen --invariant envsOk` on the `walk` fixture, whose invariant walks the `<workers>` cell map
/// and each worker's `<env>` map by free-key patterns: each walk gets its test of one binding,
/// read through projections (the cell map's key and the worker's `<wid>` read equal), and its
/// element-wise form `Invariant.f_walk`, and both join the unfolding set, instead of the note
/// that the recursion is neither a fold nor structural.
#[test]
fn map_walks_by_free_key_patterns_get_their_element_wise_form() {
    let d = tmp("cli-walk");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/walk");
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
            "KWalk",
            "--prelude",
            "../../prelude",
            "--invariant",
            "envsOk",
        ])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(!err.contains("is neither a map walk"), "{err}");
    let defs = std::fs::read_to_string(out.join("KWalk/InvariantDefs.lean")).unwrap();
    assert!(defs.contains("def Invariant.allIn_test (k : SortKItem) (v : SortKItem) (S : SortMap) : Prop :=\n  KPrelude.MapHook.inKeys v S = true"), "{defs}");
    assert!(defs.contains("def Invariant.workersIn_test (k : SortWidCell) (v : SortWorkerCell) (S : SortMap) : Prop :=\n  (Invariant.content_wid (Invariant.cell_wid v)) = (Invariant.content_wid k) ∧ (K.«allIn(_,_)_WALK_Bool_Map_Map» (Invariant.content_env (Invariant.cell_env v)) S) = some true"), "{defs}");
    assert!(defs.contains("theorem Invariant.workersIn_walk (m : SortWorkerCellMap) (S : SortMap) :\n    K.«workersIn(_,_)_WALK_Bool_WorkersCell_Map» (SortWorkersCell.«<workers>» m) S = some true ↔\n      KPrelude.MapHook.WF m ∧ KPrelude.MapHook.EntriesOn (fun q => Invariant.workersIn_test q.1 q.2 S) m := by"), "{defs}");
    let thms = std::fs::read_to_string(out.join("KWalk/Invariants.lean")).unwrap();
    assert!(thms.contains("Invariant.allIn_walk, Invariant.allIn_test, Invariant.workersIn_walk, Invariant.workersIn_test"), "{thms}");
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
/// that a user should revisit, from a Lean file and from a kind 1 `open-invariant-cases.txt`; one
/// function changed (`inc`), reported with the rule that calls it through another function
/// (`go(N)`, through `twice`), and the hand-written case of that rule and mention of the function to
/// revisit. A generated file is not read, and a generation compared with itself has no difference.
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
        "theorem a : Diff.Step.Case.start P := x\ntheorem b : Diff.Step.Case.«done(s(z))» P := x\ntheorem c : Diff.Step.Case.«done(s(s(N)))» P := x\nexample := Diff.App.«stop(s(s(N)))»\n  case start N g => exact h\ntheorem d : Diff.Step.Case.«go(N)» P := x\nexample := Eqn.«inc(_)_DIFF-SYNTAX_Nat_Nat_1»\n",
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
    assert!(out.contains("8 -> 9 rules"), "{out}");
    assert!(out.contains("changed 1, added 2, removed 1, renamed 3 (same statement), renamed and changed 1 (suggested), context changed 0; unchanged 2 (2 moved)"), "{out}");
    assert!(
        out.contains("  «done(s(z))»  old.k:14:3 -> new.k:21:3: right-hand side differs"),
        "{out}"
    );
    assert!(
        out.contains("  start -> begin  old.k:12:3 -> new.k:19:3"),
        "{out}"
    );
    assert!(out.contains("  «back(s(N))» -> «back(s(M))»"), "{out}");
    assert!(out.contains("  «halt(N)» -> «halt(N:Nat) #"), "{out}");
    assert!(out.contains("  «stop(s(s(N)))» -> «stop(s(N))»?"), "{out}");
    assert!(out.contains("added:\n  «halt(N:Nat) #"), "{out}");
    assert!(out.contains("  «run(z)»  new.k:26:3"), "{out}");
    assert!(out.contains("removed:\n  «back(z)»  old.k:16:3"), "{out}");
    assert!(out.contains("(files read: 2)"), "{out}");
    assert!(out.contains("revisit 5 rule(s):"), "{out}");
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
        out.contains("functions: changed 1, added 0, removed 0; unchanged 1\n"),
        "{out}"
    );
    assert!(
        out.contains(
            "functions changed:\n  inc(_)_DIFF-SYNTAX_Nat_Nat: called by 1 rule(s): «go(N)»\n"
        ),
        "{out}"
    );
    assert!(
        out.contains("  «go(N)»: calls the changed function(s) `inc(_)_DIFF-SYNTAX_Nat_Nat`\n"),
        "{out}"
    );
    assert!(
        out.contains("mentions of functions that changed or were removed (1):\n")
            && out.contains("Cases.lean:7 (inc(_)_DIFF-SYNTAX_Nat_Nat)"),
        "{out}"
    );
    assert!(
        !out.contains("«halt(N)»:"),
        "a generated file and .lake/ are not hand-written:\n{out}"
    );
    let t = std::fs::read_to_string(&toml).unwrap();
    assert!(
        t.contains("[summary]\n")
            && t.contains("changed = 1\n")
            && t.contains("[[revisit]]\nrule = \"«done(s(z))»\"")
            && t.contains("functions_changed = 1\n")
            && t.contains("[[function]]\nname = \"K.«inc(_)_DIFF-SYNTAX_Nat_Nat»\""),
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
    assert!(out.contains("changed 0, added 0, removed 0, renamed 0 (same statement), renamed and changed 0 (suggested), context changed 0; unchanged 8 (0 moved)"), "{out}");
    assert!(
        out.contains("functions: changed 0, added 0, removed 0; unchanged 2"),
        "{out}"
    );
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

fn relate_fixture(name: &str, out: &Path) -> std::process::Output {
    let fx = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
        .join("definition.kore");
    Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("relate")
        .arg("--kore-a")
        .arg(&fx)
        .args(["--name-a", "A", "--kore-b"])
        .arg(&fx)
        .args(["--name-b", "B", "--ns", "Rel", "--out"])
        .arg(out.join("Bisim.lean"))
        .arg("--report")
        .arg(out.join("correspondence.toml"))
        .output()
        .unwrap()
}

/// `relate` of two libraries that give every constructor the same position: `tr` keeps every
/// term's serialization, so map keys need no invariant (`Inv` is `True`); the cell map of
/// `<worker>`s is a typed collection sort with its own pointwise lemmas, and the free-key rule
/// `tick` is inverted through the translated map's bindings and stepped with `B`'s variables
/// given as translations.
#[test]
fn relate_with_kept_positions_states_the_bisimulation_without_a_key_invariant() {
    let d = tmp("cli-relate-cellmap");
    let o = relate_fixture("cellmap", &d);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let lean = std::fs::read_to_string(d.join("Bisim.lean")).unwrap();
    for want in [
        "def Inv (_ : A.SortGeneratedTopCell) : Prop := True",
        "theorem ser_tr_SortWorkerCellMap (a : A.SortWorkerCellMap) : B.ser_SortWorkerCellMap (tr_SortWorkerCellMap a) = A.ser_SortWorkerCellMap a",
        "theorem pres_SortWidCell : SAL.Pres tr_SortWidCell",
        "theorem map_bwd_SortWorkerCellMap",
        "    refine B.Step.tick (tr_SortKCell Gen3)",
        "theorem bisim : Bisimulation A.Step B.Step R",
    ] {
        assert!(lean.contains(want), "missing `{want}`");
    }
    let report = std::fs::read_to_string(d.join("correspondence.toml")).unwrap();
    assert!(
        report.contains("keeps every constructor's position"),
        "{report}"
    );
}

/// A function with a free-key equation (`MapHook.chooseFirst`) gets no commutation lemma, so
/// `relate` refuses the bisimulation with an error naming it (exit status 2), not a panic.
#[test]
fn relate_refuses_a_function_with_a_free_key_equation() {
    let d = tmp("cli-relate-freekey");
    let o = relate_fixture("freekey", &d);
    assert_eq!(o.status.code(), Some(2));
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(
        err.contains("relate: the function allNat(_)_FREEKEY_Bool_Map has an equation with a free-key map pattern"),
        "{err}"
    );
}

/// `confluence --report-only` on the `threadend` fixture: the end of a thread (its `<k>` empty) is
/// matched at the key `<id> _ </id>`, the step of a thread at a variable key; taken as one binding
/// (the classifier's same-binding mode), the two keys unify and the two `<k>` cells clash, so the
/// pair is not critical at one binding (it still is at two, where the end removes a binding).
#[test]
fn confluence_separates_a_thread_end_matched_at_a_constructor_key_at_one_binding() {
    let d = tmp("cli-confluence-threadend");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/threadend/definition.kore");
    let report = d.join("confluence.toml");
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args(["--name", "T", "--report-only", "true", "--report"])
        .arg(&report)
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let r = std::fs::read_to_string(&report).unwrap();
    assert!(r.contains("[one_binding]\nclash = 1\n\n"), "{r}");
    assert!(!r.contains("(one binding"), "{r}");
    assert!(
        r.contains("\"step | end (two bindings: the map's bindings change)\""),
        "{r}"
    );

/// `relate --split true` on the `peano` fixture: the bisimulation cut into a base module, one
/// module per simulation importing only what it uses, and the bisimulation module importing the
/// forward and backward simulations; the proof macros move to the base module, scoped.
#[test]
fn relate_split_writes_one_module_per_simulation() {
    let d = tmp("cli-relate-split");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/peano/definition.kore");
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("relate")
        .arg("--kore-a")
        .arg(&fx)
        .args(["--name-a", "A", "--kore-b"])
        .arg(&fx)
        .args(["--name-b", "B", "--ns", "Rel", "--split", "true", "--out"])
        .arg(d.join("Bisim.lean"))
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let read = |f: &str| std::fs::read_to_string(d.join(f)).unwrap();
    let base = read("Bisim/Base.lean");
    assert!(base.contains("theorem inv_step") && base.contains("scoped macro \"hpri_bwd\""));
    assert!(!base.contains("local macro"));
    for (m, import, thm) in [
        ("AppFwd", "Rel.Bisim.Base", "theorem app_fwd"),
        ("AppBwd", "Rel.Bisim.Base", "theorem app_bwd"),
        ("Forward", "Rel.Bisim.AppBwd", "theorem forward"),
        ("Backward", "Rel.Bisim.AppFwd", "theorem backward"),
    ] {
        let t = read(&format!("Bisim/{m}.lean"));
        assert!(t.starts_with(&format!("import {import}\n")), "{m}");
        assert!(t.contains(thm) && t.trim_end().ends_with("end Rel"), "{m}");
    }
    let main = read("Bisim.lean");
    assert!(main.starts_with("import Rel.Bisim.Forward\nimport Rel.Bisim.Backward\n"));
    assert!(main.contains("theorem bisim : Bisimulation A.Step B.Step R"));
}

/// `confluence --threads` on the `threadend` fixture: `step` updates one thread, `end` removes one
/// (a global rule); the module states `terminal_unique_of` from the two hypotheses, and the report
/// counts the pairs with `end` (3 ordered) as open and `step` against itself at one thread.
#[test]
fn confluence_threads_leaves_the_global_and_same_thread_pairs_open() {
    let d = tmp("cli-confluence-threads");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/threadend/definition.kore");
    let (out, report) = (d.join("Views.lean"), d.join("confluence.toml"));
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args(["--name", "T", "--ns", "TV", "--threads", "threads", "--obs", "ended", "--out"])
        .arg(&out)
        .arg("--report")
        .arg(&report)
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let r = std::fs::read_to_string(&report).unwrap();
    assert!(
        r.contains("[threads]\nrules = 2\nthread = 1\nshared = 0\nglobal = 1\n"),
        "{r}"
    );
    assert!(r.contains("open = 3\nopen-global = 3\n"), "{r}");
    assert!(r.contains("same-thread = 1\n"), "{r}");
    let v = std::fs::read_to_string(&out).unwrap();
    assert!(v.contains("| .step => .thread"), "{v}");
    assert!(v.contains("| .«end» => .global"), "{v}");
    assert!(
        v.contains("theorem terminal_unique_of (O : OpenJoins) (S : SameThreadJoins)"),
        "{v}"
    );
}
