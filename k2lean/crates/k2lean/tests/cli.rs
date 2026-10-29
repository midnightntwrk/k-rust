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
        log.contains("12 equations and simplifications stated, 1 open"),
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
    // every point of every run from `init` (INV-11)
    assert!(thms.contains("theorem Invariant.always {pgm : SortPgm} :\n    ∀ s, s 0 = init pgm → Paths.IsRun Step s → ∀ n, Invariant (s n) :=\n  Paths.always_of_preserved Invariant.preserved (Invariant.init_holds pgm)\n"), "{thms}");
    assert!(thms.contains("#k2l_assert_axioms Invariant.preserved Invariant.init_holds Invariant.star Invariant.stepsN Invariant.always\n"), "{thms}");
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
/// read through projections (the cell map's key and the worker's `<wid>` read equal; for `idsOk`,
/// whose step is the recursive call alone, that equality is the whole test), and its
/// element-wise form `Invariant.f_walk`, and both join the unfolding set, instead of the note
/// that the recursion is neither a fold nor structural; the walk of the `<workers>` cell's map
/// also gets the form at any cell (`Invariant.f_walk_cell`, through `Invariant.f_map`), which
/// rewrites the cell where a rule leaves it as a variable (the fixture's store rules).
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
    assert!(defs.contains("def Invariant.workersIn_map : SortWorkersCell → SortWorkerCellMap\n  | SortWorkersCell.«<workers>» x => x"), "{defs}");
    assert!(defs.contains("theorem Invariant.workersIn_walk_cell (w : SortWorkersCell) (S : SortMap) :\n    K.«workersIn(_,_)_WALK_Bool_WorkersCell_Map» w S = some true ↔"), "{defs}");
    assert!(!defs.contains("Invariant.allIn_walk_cell"), "{defs}");
    // `idsOk(<workers> <worker> … </worker> Ws </workers>) => idsOk(<workers> Ws </workers>)`: a walk
    // with no test of its own, whose binding passes when its key is its `<wid>`
    assert!(defs.contains("def Invariant.idsOk_test (k : SortWidCell) (v : SortWorkerCell) : Prop :=\n  (Invariant.content_wid (Invariant.cell_wid v)) = (Invariant.content_wid k)\n"), "{defs}");
    let thms = std::fs::read_to_string(out.join("KWalk/Invariants.lean")).unwrap();
    assert!(thms.contains("Invariant.allIn_walk, Invariant.allIn_test, Invariant.idsOk_walk, Invariant.idsOk_test, Invariant.idsOk_walk_cell, Invariant.idsOk_map, Invariant.workersIn_walk, Invariant.workersIn_test, Invariant.workersIn_walk_cell, Invariant.workersIn_map"), "{thms}");
}

/// `gen --invariant ok` on the `kfold` fixture, whose invariant folds `<k>` with `kOk` and a
/// partial test of one item `itemOk`, which calls `kOk` back on the continuation a `later(K)`
/// holds: the fold gets `Invariant.kAll` and its element-wise form `Invariant.kOk_iff`, by
/// structural recursion on the sequence (`SortK` is mutually inductive) from its two equations;
/// `itemOk`, recursive only through the fold, is unfolded by its equations, and its `owise`
/// equation is stated at every subsort of `KItem` (`Invariant.itemOk_owise_Cmd`), instead of
/// notes that the recursion is neither a walk, a fold nor structural.
#[test]
fn k_folds_get_their_element_wise_form() {
    let d = tmp("cli-kfold");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/kfold");
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
            "KKFold",
            "--prelude",
            "../../prelude",
            "--invariant",
            "ok",
        ])
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(!err.contains("is neither a map walk"), "{err}");
    let defs = std::fs::read_to_string(out.join("KKFold/InvariantDefs.lean")).unwrap();
    assert!(defs.contains("def Invariant.kAll (P : SortKItem → Prop) : SortK → Prop\n  | .dotk => True\n  | .kseq i k => P i ∧ Invariant.kAll P k"), "{defs}");
    assert!(defs.contains("theorem Invariant.kOk_iff : ∀ (k : SortK) (p1 : SortMap), K.«kOk(_,_)_KFOLD_Bool_K_Map» k p1 = some true ↔ Invariant.kAll (fun x => K.«itemOk(_,_)_KFOLD_Bool_KItem_Map» x p1 = some true) k\n  | .dotk, p1 => by simp only [Invariant.kAll, Eqn.«kOk(_,_)_KFOLD_Bool_K_Map_1»]"), "{defs}");
    assert!(defs.contains("theorem Invariant.itemOk_owise_Cmd (x : SortCmd) (a1 : SortMap) :\n    K.«itemOk(_,_)_KFOLD_Bool_KItem_Map» (SortKItem.inj_Cmd x) a1 = some true := by"), "{defs}");
    // the `<stack>` list fold, with the same partial test, from its two equations
    assert!(defs.contains("theorem Invariant.stackOk_iff (l : SortList) (p1 : SortMap) :\n    K.«stackOk(_,_)_KFOLD_Bool_List_Map» l p1 = some true ↔ KPrelude.ListHook.ElemsOn (fun x => K.«itemOk(_,_)_KFOLD_Bool_KItem_Map» x p1 = some true) l :=\n  KPrelude.ListHook.all_iff_of_eqns_partial"), "{defs}");
    let thms = std::fs::read_to_string(out.join("KKFold/Invariants.lean")).unwrap();
    assert!(thms.contains("Eqn.«itemOk(_,_)_KFOLD_Bool_KItem_Map_4», Eqn.«ok(_)_KFOLD_Bool_GeneratedTopCell_1», Invariant.stackOk_iff, Invariant.kOk_iff, Invariant.kAll, Invariant.itemOk_owise_Bool, Invariant.itemOk_owise_Cmd"), "{thms}");
    // the group reads the store through its keys only: monotone in it, by recursion along the
    // equations, and the walk `allIn` from its element-wise form; the closers' forms of both
    assert!(defs.contains("theorem Invariant.itemOk_mono {S S' : SortMap} (h : KPrelude.MapHook.KeysIncl S S') {x : SortKItem}\n    (hx : K.«itemOk(_,_)_KFOLD_Bool_KItem_Map» x S = some true) :\n    K.«itemOk(_,_)_KFOLD_Bool_KItem_Map» x S' = some true := by\n  by_cases hc1 : ∃ (L : SortInt), x = SortKItem.inj_KItem (SortKItem.Own.«use(_)» L)"), "{defs}");
    assert!(
        defs.contains("theorem Invariant.allIn_mono {S S' : SortMap}"),
        "{defs}"
    );
    assert!(
        defs.contains("@[k2l_coll] theorem Invariant.kOk_kAll_mono {S S' : SortMap} {k : SortK}"),
        "{defs}"
    );
    assert!(
        defs.contains(
            "@[k2l_coll] theorem Invariant.stackOk_elems_mono {S S' : SortMap} {l : SortList}"
        ),
        "{defs}"
    );
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
            "require k2lean from \"../../prelude\"\nrequire «Peano» from \"../../lib\"\n"
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
        runf.contains("theorem always {pgm : Peano.SortPgm} :\n    ∀ s, s 0 = Peano.init pgm → Paths.IsRun Peano.Step s → ∀ n, Invariant (s n) :=\n  Paths.always_of_preserved preserved (init_holds pgm)\n"),
        "{runf}"
    );
    assert!(
        runf.contains("#k2l_assert_axioms preserved init_holds star stepsN always\n"),
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

/// A recursive function with a free-key equation (`MapHook.chooseFirst`) gets no commutation
/// lemma, so `relate` refuses the bisimulation with an error naming it (exit status 2), not a panic.
#[test]
fn relate_refuses_a_recursive_function_with_a_free_key_equation() {
    let d = tmp("cli-relate-freekey");
    let o = relate_fixture("freekey", &d);
    assert_eq!(o.status.code(), Some(2));
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(
        err.contains("relate: the function allNat(_)_FREEKEY_Bool_Map has an equation with a free-key map pattern; its commutation with the translation is generated only for a non-recursive function"),
        "{err}"
    );
}

/// The fixtures `handoffseq` and `handoff` both declare `<T>`, over `<k>` and over `<tasks>`: a
/// symbol of the same name pairs only at the same sorts, so `<T>` has no counterpart and `relate`
/// refuses (exit status 2) instead of writing a translation that does not typecheck.
#[test]
fn relate_pairs_a_symbol_of_the_same_name_only_at_the_same_sorts() {
    let d = tmp("cli-relate-handoffseq");
    let fx = |n: &str| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures")
            .join(n)
            .join("definition.kore")
    };
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("relate")
        .arg("--kore-a")
        .arg(fx("handoffseq"))
        .args(["--name-a", "HandoffSeq", "--kore-b"])
        .arg(fx("handoff"))
        .args(["--name-b", "Handoff", "--ns", "Rel", "--out"])
        .arg(d.join("Bisim.lean"))
        .arg("--report")
        .arg(d.join("correspondence.toml"))
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(2));
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(
        err.contains("relate: constructors of HandoffSeq without a counterpart in Handoff: [")
            && err.contains("\"<T>\""),
        "{err}"
    );
    assert!(
        err.contains("\"<procs>\" = { b = \"<procs>\", how = \"same symbol\" }"),
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
    assert!(r.contains("[diagnostic.one_binding]\nclash = 1\n\n"), "{r}");
    assert!(!r.contains("(one binding"), "{r}");
    assert!(
        r.contains("\"step | end (two bindings: the map's bindings change)\""),
        "{r}"
    );
}

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
/// (a step that replaces its binding by nothing, matched at the key `<id> _ </id>`); the module
/// states `terminal_unique_of` from the two hypotheses, and the report counts two ends racing on
/// `<ended>` as open, and each rule against itself at one thread (`end`'s key, an empty `<k>`, is
/// disjoint from `step`'s).
#[test]
fn confluence_threads_views_a_message_to_a_named_process() {
    // `resume(Q)` in one process and `#suspended` in the process `<pid> Q`: the second binding's
    // key is named by the first, still two bindings of the process map
    let d = tmp("cli-confluence-utxo");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/utxo/definition.kore");
    let (out, report) = (d.join("Views.lean"), d.join("confluence.toml"));
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args([
            "--name",
            "Utxo",
            "--ns",
            "UV",
            "--threads",
            "procs",
            "--obs",
            "ledger",
            "--out",
        ])
        .arg(&out)
        .arg("--report")
        .arg(&report)
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let r = std::fs::read_to_string(&report).unwrap();
    assert!(
        r.contains("[threads]\nrules = 8\nthread = 8\nshared = 0\nglobal = 0\n"),
        "{r}"
    );
    assert!(
        r.contains("global = { slots = 0, generic = 0, hand = 0, open = 0, refuted = 0 }\ncells = { slots = 0,"),
        "{r}"
    );
    let v = std::fs::read_to_string(&out).unwrap();
    assert!(v.contains("| .resume => .thread"), "{v}");
    // `spend` reads its process's key again in the ledger (only the owner spends): still a step
    // at one binding of the process map
    assert!(v.contains("| .spend => .thread"), "{v}");
    // the relation bound beside the rule's variable `Q` (`create(Q, V)`) takes another name
    assert!(v.contains("fun k2l_Q k2l_hQ => k2l_hQ"), "{v}");
    // no sort `KResult`: no item is one, and `isKResult` is not referenced
    assert!(!v.contains("isKResult"), "{v}");
}

/// `confluence --threads` on the `utxo` fixture: every rule touching `<ledger>` changes it at one
/// binding (`create` inserts, `spend` removes), so the ledger is keyed (`MCh`) and only the pairs
/// whose bindings overlap are left, as `KeyJoins`; with ids derived from content, no fresh value,
/// two spawns are the one pair left in `OpenJoins` (both add a process).
#[test]
fn confluence_threads_views_a_map_cell_by_binding() {
    let d = tmp("cli-confluence-keyed");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/utxo/definition.kore");
    let (out, report) = (d.join("Views.lean"), d.join("confluence.toml"));
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args([
            "--name",
            "Utxo",
            "--ns",
            "UV",
            "--threads",
            "procs",
            "--obs",
            "ledger",
            "--out",
        ])
        .arg(&out)
        .arg("--report")
        .arg(&report)
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let r = std::fs::read_to_string(&report).unwrap();
    // create|create, spend|spend, create|spend, spend|create; without slots, every slot is open
    for x in [
        "attempted = false\n",
        "[premises.SameThreadJoins]\nkeys = { slots = 8, generic = 0, hand = 0, open = 8, refuted = 0 }\n",
        "insert = { slots = 1, generic = 0, hand = 0, open = 1, refuted = 0 }\n",
        "[premises.KeyJoins]\nkeys = { slots = 4, generic = 0, hand = 0, open = 4, refuted = 0 }\n",
    ] {
        assert!(r.contains(x), "{x}\n{r}");
    }
    let v = std::fs::read_to_string(&out).unwrap();
    assert!(v.contains("  ledger : Utxo.SortMap\n"), "{v}");
    assert!(v.contains("  ledger : MCh Utxo.SortMap := none\n"), "{v}");
    // spend removes a binding, create inserts one
    assert!(
        v.contains("MCh.small_of (.inl ⟨_, _, rfl⟩) (.inr rfl)")
            && v.contains("MCh.small_of (.inr rfl) (.inl ⟨_, _, rfl⟩)"),
        "{v}"
    );
    // a rule leaving the ledger alone has it as one variable, split into the cell and its map
    assert!(v.contains("  k2l_cases DotVar1\n"), "{v}");
    assert!(
        v.contains(
            "theorem terminal_unique_of (O : OpenJoins) (S : SameThreadJoins) (K : KeyJoins)"
        ),
        "{v}"
    );
    // `--obs ledger`: the projection and its corollary, under the same premises
    assert!(v.contains("def obs : Utxo.SortGeneratedTopCell"), "{v}");
    assert!(
        v.contains("theorem obs_confluent_of (O : OpenJoins) (S : SameThreadJoins) (K : KeyJoins)")
            && v.contains("  congrArg obs (terminal_unique_of O S K h₁ t₁ h₂ t₂)"),
        "{v}"
    );
}

/// `confluence --threads` on the `handoff` fixture: `resume-oid` reads its input's binding of `<vals>`
/// and adds its output beside it (`(I ↦ V) (o ↦ W)`), so `<vals>` is keyed with that change a read
/// and an insertion (`MCh.SmallR`); two resumes reading one input commute at their bindings
/// (`MCh.Shared`), and only the root's two forks are left in `OpenJoins`.
#[test]
fn confluence_threads_views_a_read_with_an_insertion_as_keyed() {
    let d = tmp("cli-confluence-handoff");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/handoff/definition.kore");
    let (out, report) = (d.join("Views.lean"), d.join("confluence.toml"));
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args([
            "--name",
            "Handoff",
            "--ns",
            "HV",
            "--threads",
            "tasks",
            "--out",
        ])
        .arg(&out)
        .arg("--report")
        .arg(&report)
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let r = std::fs::read_to_string(&report).unwrap();
    assert!(
        r.contains("cells = { slots = 0, generic = 0, hand = 0, open = 0, refuted = 0 }\npriority = { slots = 0, generic = 0, hand = 0, open = 0, refuted = 0 }\ninsert = { slots = 1,"),
        "{r}"
    );
    let v = std::fs::read_to_string(&out).unwrap();
    assert!(v.contains("  vals : MCh Handoff.SortMap := none\n"), "{v}");
    assert!(v.contains("c.procs.Small ∧ c.vals.SmallR"), "{v}");
    assert!(v.contains("MCh.smallR_extend hr_22"), "{v}");
    // `next` and `out` are parameters: everything is stated for every instance
    assert!(
        v.contains("namespace HV\n\nvariable [Handoff.Hooks]\n"),
        "{v}"
    );
}

/// `confluence --threads --assume-invariant NAME`: every premise holds at the configurations
/// satisfying `NAME`, the generic joins take it, and `terminal_unique_of` holds from one by
/// `NAME.preserved` (`--invariant-module` is imported); without the option the module is as before.
#[test]
fn confluence_threads_states_the_joins_under_a_program_hypothesis() {
    let d = tmp("cli-confluence-invariant");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/handoff/definition.kore");
    let run = |extra: &[&str], out: &Path| {
        let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
            .arg("confluence")
            .arg("--kore")
            .arg(&fx)
            .args(["--name", "Handoff", "--ns", "HV", "--threads", "tasks"])
            .args(extra)
            .arg("--out")
            .arg(out)
            .output()
            .unwrap();
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
        std::fs::read_to_string(out).unwrap()
    };
    let plain = run(&[], &d.join("Plain.lean"));
    let v = run(
        &[
            "--assume-invariant",
            "HV.Wf",
            "--invariant-module",
            "HV.Inv",
        ],
        &d.join("Views.lean"),
    );
    assert!(!plain.contains("HV.Wf"), "{plain}");
    assert!(
        v.contains("import Handoff.Preserves\nimport HV.Inv\n"),
        "{v}"
    );
    for premise in [
        "staticOK r₁ r₂ = false → ∀ {c c₁ c₂ : Handoff.SortGeneratedTopCell}, HV.Wf c → StepBy",
        "{a₁ b₁ ch₁ bs₁ a₂ b₂ ch₂ bs₂ k}, HV.Wf c → StepBy",
        "{ch₁ ch₂}, HV.Wf c → StepBy",
    ] {
        assert!(v.contains(premise), "{premise}\n{v}");
    }
    assert!(
        v.contains("terminal_unique_of_diamond (H := HV.Wf) StepEquiv.eq HV.Wf.preserved")
            && v.contains("(fun hinv h₁ h₂ => joins_of O S K hinv h₁ h₂) hinv h₁ t₁ h₂ t₂"),
        "{v}"
    );
}

/// `confluence` refuses the retired per-pair options, naming what replaced them, rather than
/// stating a theorem without them; the hand module and its list need slots, and without
/// `--threads` slots are required.
#[test]
fn confluence_refuses_retired_options() {
    let d = tmp("cli-confluence-refuse");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/utxo/definition.kore");
    for threads in [true, false] {
        for (k, v, msg) in [
            (
                "--hyp",
                "H",
                "--hyp is retired: a program hypothesis is `--assume-invariant NAME`",
            ),
            ("--hand-module", "M", "--hand-module needs --slots"),
            ("--open-joins", "open.txt", "--open-joins needs --slots"),
            ("--join", "local", "--join is retired"),
            ("--open", "open.txt", "--open is retired"),
        ] {
            let mut c = Command::new(env!("CARGO_BIN_EXE_k2lean"));
            c.arg("confluence")
                .arg("--kore")
                .arg(&fx)
                .args(["--name", "Utxo", "--ns", "UV", k, v, "--out"])
                .arg(d.join("Views.lean"));
            if threads {
                c.args(["--threads", "procs"]);
            }
            let o = c.output().unwrap();
            let e = String::from_utf8_lossy(&o.stderr);
            assert!(!o.status.success(), "{k}");
            assert!(e.contains(msg), "{k}: {e}");
        }
    }
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args(["--name", "Utxo", "--ns", "UV", "--out"])
        .arg(d.join("Views.lean"))
        .output()
        .unwrap();
    assert!(!o.status.success());
    assert!(String::from_utf8_lossy(&o.stderr).contains("--slots is required without --threads"));
}

/// `confluence` on the fixture `race`, whose workers have no `<k>`: by worker (`--threads
/// workers`), a key reads nothing of a worker, so each rule's pattern fits any; without
/// `--threads`, every rule is global and every ordered pair of rules a slot of `OpenJoins`. Two
/// workers' steps, and a step beside a spawn, are open slots the commuting attempt closes: the
/// instances named, the second's binders suffixed, each step after the other.
#[test]
fn confluence_slots_with_and_without_threads() {
    let d = tmp("cli-confluence-race");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/race/definition.kore");
    let run = |ns: &str, extra: &[&str]| {
        let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
            .arg("confluence")
            .arg("--kore")
            .arg(&fx)
            .args(["--name", "Race", "--ns", ns, "--obs", "acc"])
            .args(extra)
            .arg("--slots")
            .arg(d.join(format!("{ns}.Slots.lean")))
            .arg("--out")
            .arg(d.join(format!("{ns}.Views.lean")))
            .arg("--report")
            .arg(d.join(format!("{ns}.toml")))
            .output()
            .unwrap();
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
        let read = |f: String| std::fs::read_to_string(d.join(f)).unwrap();
        (
            read(format!("{ns}.Views.lean")),
            read(format!("{ns}.Slots.lean")),
            read(format!("{ns}.toml")),
        )
    };
    let (v, m, r) = run("RW", &["--threads", "workers"]);
    assert!(
        v.contains("def tkey (_ : Race.SortWorkerCell) : KeyView :=\n  ⟨0, fun _ => (\"dotk\", \"\"), false⟩")
            && v.contains("  | .work => [KeyPat.any]"),
        "{v}"
    );
    for x in [
        "obtain ⟨N_r, P_r, DotVar2_r, DotVar3_r, DotVar1_r, I_r, DotVar0_r, r_r, hr_r, e, rfl⟩ := i₂",
        "| (obtain ⟨R₂₁, m', a₁, a₂, a₃⟩ := MapHook.concat_element_comm_insert hm hr hr_r",
        "theorem terminal_unique {c n₁ n₂",
    ] {
        assert!(m.contains(x), "{x}\n{m}");
    }
    assert!(
        r.contains("[premises.SameThreadJoins]\nkeys = { slots = 1, generic = 1, hand = 0, open = 0, refuted = 0 }"),
        "{r}"
    );
    let (v, m, r) = run("RP", &[]);
    for x in [
        "def OpenJoins : Prop :=\n  ∀ r₁ r₂, OpenSlot r₁ r₂",
        "theorem view_of {c c' : Race.SortGeneratedTopCell} (h : Race.Step c c') : ∃ r, StepBy r c c' :=",
        "theorem obs_confluent_of (O : OpenJoins)",
        "def join.open.stop.stop.statement : Prop := OpenSlot .stop .stop",
    ] {
        assert!(v.contains(x), "{x}\n{v}");
    }
    assert!(!v.contains("SameThreadJoins") && !v.contains("tkey"), "{v}");
    assert!(
        m.contains("| (rcases MapHook.concat_element_same_or_comm hm hm_r hr hr_r with")
            && m.contains(
                "theorem openJoins_of : OpenJoins := by\n  intro r₁ r₂\n  cases r₁ <;> cases r₂\n"
            )
            && m.contains("terminal_unique_of (openJoins_of) h₁ t₁ h₂ t₂"),
        "{m}"
    );
    assert!(
        r.contains("[premises.OpenJoins]\npairs = { slots = 9, generic = 9, hand = 0, open = 0, refuted = 0 }"),
        "{r}"
    );
}

/// `confluence --threads --slots`: one obligation per pair of rules in a premise, its statement
/// in the views; a slot is attempted generically, proved by the hand module (`NAME | hand` in the
/// open-joins list) or open (a field of `Open`, the premise of `terminal_unique`). The views'
/// thread steps record their instance at the bindings they match (`StepAt`).
#[test]
fn confluence_threads_slots_split_the_premises() {
    let d = tmp("cli-confluence-slots");
    let fx =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/utxo/definition.kore");
    let run = |list: Option<&str>| {
        let mut c = Command::new(env!("CARGO_BIN_EXE_k2lean"));
        c.arg("confluence")
            .arg("--kore")
            .arg(&fx)
            .args([
                "--name",
                "Utxo",
                "--ns",
                "UV",
                "--threads",
                "procs",
                "--slots",
            ])
            .arg(d.join("Slots.lean"))
            .arg("--out")
            .arg(d.join("Views.lean"))
            .arg("--report")
            .arg(d.join("c.toml"));
        if let Some(l) = list {
            std::fs::write(d.join("open.txt"), l).unwrap();
            c.args(["--hand-module", "UV.Hand", "--open-joins"])
                .arg(d.join("open.txt"));
        }
        c.output().unwrap()
    };
    let o = run(None);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let v = std::fs::read_to_string(d.join("Views.lean")).unwrap();
    let m = std::fs::read_to_string(d.join("Slots.lean")).unwrap();
    for x in [
        "def StepAt : Rule →",
        "∧ StepAt r a c c'",
        "have hat : StepAt .resume _ _ _ :=",
        "def SameSlot (r₁ r₂ : Rule) : Prop :=",
        "KeyPat.pdisj r₁.pats r₂.pats = false →\n    SameSlot r₁ r₂",
        "∀ r₁ r₂, r₁.rank = r₂.rank → staticOK r₁ r₂ = true → KeySlot r₁ r₂",
        "∀ r₁ r₂, staticOK r₁ r₂ = false → OpenSlot r₁ r₂",
        "theorem kcompat_of",
        "def join.same.resume.resume.statement : Prop := SameSlot .resume .resume",
        "def join.open.spawn.spawn.statement : Prop := OpenSlot .spawn .spawn",
        // each keyed cell's map, and a step's change of it, for the key attempts
        "def ledgerOf : Utxo.SortGeneratedTopCell → Utxo.SortMap",
        "MCh.Step ch.ledger (ledgerOf c) (ledgerOf c') ∧ ch.ledger.Small",
    ] {
        assert!(v.contains(x), "{x}\n{v}");
    }
    // a key slot: the changes at their keys, else the instances alone
    assert!(
        m.contains("  have x₁ := ChOf.cells o₁\n")
            && m.contains("  try simp only [ledgerOf] at x₁ x₂\n  first\n    | (k2l_keyed hk\n"),
        "{m}"
    );
    // the two bindings of a rule that matches two processes
    assert!(
        m.contains("obtain e₁ | e₁ := MapHook.key_of_lookup_pair hp₁ l₁"),
        "{m}"
    );
    assert!(
        m.contains("theorem join.key.spend.spend : join.key.spend.spend.statement := by")
            && m.contains("theorem terminal_unique {c n₁ n₂")
            && !m.contains("structure Open"),
        "{m}"
    );
    // one slot by hand, one open
    let o = run(Some(
        "# a comment\njoin.key.spend.spend | hand\njoin.open.spawn.spawn\n",
    ));
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let m = std::fs::read_to_string(d.join("Slots.lean")).unwrap();
    let r = std::fs::read_to_string(d.join("c.toml")).unwrap();
    for x in [
        "import UV.Hand",
        "theorem join.key.spend.spend : join.key.spend.spend.statement := hand.join.key.spend.spend",
        "#k2l_proves join.key.spend.spend.statement hand.join.key.spend.spend",
        "structure Open : Prop where\n  «open.spawn.spawn» : join.open.spawn.spawn.statement",
        "case spawn.spawn => exact P.«open.spawn.spawn»",
        "theorem terminal_unique (P : Open) {c n₁ n₂",
    ] {
        assert!(m.contains(x), "{x}\n{m}");
    }
    assert!(
        r.contains("insert = { slots = 1, generic = 0, hand = 0, open = 1, refuted = 0 }")
            && r.contains("keys = { slots = 4, generic = 3, hand = 1, open = 0, refuted = 0 }")
            && r.contains("hand_slots = [\"join.key.spend.spend\"]\nopen_slots = [\"join.open.spawn.spawn\"]\nrefuted_slots = []\n"),
        "{r}"
    );
    // a name that is no slot
    let o = run(Some("join.open.seq.seq\n"));
    assert!(!o.status.success());
    assert!(String::from_utf8_lossy(&o.stderr).contains("join.open.seq.seq is not a slot"));
}

/// `confluence --slots` with a slot listed `| refuted` (the fixture `drf`, whose workers each write
/// `<acc>` once): the slots module states the hand module's refutation, checked by `#k2l_refuted`,
/// refutes the slot's premise at the slot's rules, and states no `terminal_unique`; the report
/// counts the slot refuted in its class. An unknown marker is refused.
#[test]
fn confluence_slots_refuted_refute_their_premise() {
    let d = tmp("cli-confluence-refuted");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/drf/definition.kore");
    let run = |list: &str| {
        std::fs::write(d.join("open.txt"), list).unwrap();
        Command::new(env!("CARGO_BIN_EXE_k2lean"))
            .arg("confluence")
            .arg("--kore")
            .arg(&fx)
            .args([
                "--name",
                "Drf",
                "--ns",
                "DV",
                "--threads",
                "workers",
                "--obs",
                "acc",
            ])
            .args(["--hand-module", "DV.Hand", "--slots"])
            .arg(d.join("Slots.lean"))
            .arg("--open-joins")
            .arg(d.join("open.txt"))
            .arg("--out")
            .arg(d.join("Views.lean"))
            .arg("--report")
            .arg(d.join("c.toml"))
            .output()
            .unwrap()
    };
    let o = run("join.open.put.put | refuted\n");
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let m = std::fs::read_to_string(d.join("Slots.lean")).unwrap();
    let r = std::fs::read_to_string(d.join("c.toml")).unwrap();
    for x in [
        "import DV.Hand",
        "theorem join.open.put.put.refuted : ¬ join.open.put.put.statement := hand.join.open.put.put.refuted\n\n#k2l_refuted join.open.put.put\n",
        "theorem openJoins_refuted : ¬ OpenJoins :=\n  fun h => join.open.put.put.refuted (h .put .put (by decide))",
        "theorem sameThreadJoins_of : SameThreadJoins",
    ] {
        assert!(m.contains(x), "{x}\n{m}");
    }
    assert!(
        !m.contains("theorem openJoins_of")
            && !m.contains("theorem terminal_unique")
            && !m.contains("theorem obs_confluent"),
        "{m}"
    );
    assert!(
        r.contains("cells = { slots = 2, generic = 1, hand = 0, open = 0, refuted = 1 }")
            && r.contains("refuted_slots = [\"join.open.put.put\"]"),
        "{r}"
    );
    // a same-thread slot refutes `SameThreadJoins`, its four guards decided
    let o = run("join.same.put.put | refuted\n");
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let m = std::fs::read_to_string(d.join("Slots.lean")).unwrap();
    assert!(
        m.contains("theorem sameThreadJoins_refuted : ¬ SameThreadJoins :=\n  fun h => join.same.put.put.refuted (h .put .put (by decide) (by decide) (by decide) (by decide))")
            && m.contains("theorem openJoins_of"),
        "{m}"
    );
    let o = run("join.open.put.put | false\n");
    assert!(!o.status.success());
    assert!(
        String::from_utf8_lossy(&o.stderr).contains("expected NAME, NAME | hand or NAME | refuted")
    );
}

#[test]
fn confluence_threads_views_a_thread_end_as_a_removal() {
    let d = tmp("cli-confluence-threads");
    let fx = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/threadend/definition.kore");
    let (out, report) = (d.join("Views.lean"), d.join("confluence.toml"));
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("confluence")
        .arg("--kore")
        .arg(&fx)
        .args([
            "--name",
            "T",
            "--ns",
            "TV",
            "--threads",
            "threads",
            "--obs",
            "ended",
            "--out",
        ])
        .arg(&out)
        .arg("--report")
        .arg(&report)
        .output()
        .unwrap();
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let r = std::fs::read_to_string(&report).unwrap();
    assert!(
        r.contains("[threads]\nrules = 2\nthread = 2\nshared = 0\nglobal = 0\n"),
        "{r}"
    );
    assert!(
        r.contains("[premises.OpenJoins]\nglobal = { slots = 0, generic = 0, hand = 0, open = 0, refuted = 0 }\ncells = { slots = 1,"),
        "{r}"
    );
    assert!(
        r.contains("[premises.SameThreadJoins]\nkeys = { slots = 2,"),
        "{r}"
    );
    let v = std::fs::read_to_string(&out).unwrap();
    assert!(v.contains("| .step => .thread"), "{v}");
    assert!(v.contains("| .«end» => .thread"), "{v}");
    assert!(v.contains("MapHook.concat_unit_left"), "{v}");
    assert!(
        v.contains("theorem terminal_unique_of (O : OpenJoins) (S : SameThreadJoins)"),
        "{v}"
    );
}

/// The non-recursive functions with free-key equations of the `pick` fixture (one free key, two,
/// and a partial one) commute with a translation that keeps every constructor's position: each
/// lemma rewrites the two free-key equations by `MapHook.dite_chooseFirst_pointwise`
/// (`k2l_choose`) and compares the continuations binding by binding (`choose_cont`).
#[test]
fn relate_proves_the_commutation_of_non_recursive_free_key_functions() {
    let d = tmp("cli-relate-pick");
    let o = relate_fixture("pick", &d);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let lean = std::fs::read_to_string(d.join("Bisim.lean")).unwrap();
    for f in [
        "hasNeg(_)_PICK_Bool_Map",
        "twoPos(_)_PICK_Bool_Map",
        "anyPos(_)_PICK_Int_Map",
    ] {
        assert!(
            lean.contains(&format!("B.K.«{f}» (tr_SortMap x0)")),
            "missing the lemma of {f}"
        );
    }
    assert_eq!(
        lean.matches("  k2l_choose pw_SortMap pres_SortKItem id\n")
            .count(),
        3
    );
    assert!(lean.contains("theorem bisim : Bisimulation A.Step B.Step R"));
}

fn gen_progress(fx: &str, out: &Path, ns: &str, extra: &[&str]) -> std::process::Output {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(fx);
    Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("gen")
        .arg("--kore")
        .arg(dir.join("definition.kore"))
        .arg("--runtime")
        .arg(dir.join("runtime.json"))
        .arg("--out")
        .arg(out)
        .args(["--name", ns, "--prelude", "../../prelude"])
        .args(extra)
        .output()
        .unwrap()
}

/// `gen --progress` (design.md §3.9) on the stack machine `vm`: one case per head of `<k>`, each
/// proved among the rules of its head only; a case marked `| refuted hand` becomes the third
/// outcome `Progress.Refuted` with its refutation checked, and the hand skeleton is written once; a
/// generation without `--progress` removes the modules.
#[test]
fn progress_states_one_case_per_head_and_a_refuted_head_is_a_third_outcome() {
    let d = tmp("cli-progress");
    let args = ["--invariant", "kOk@k", "--progress", "--ending", "halted@k"];
    let o = gen_progress("vm", &d, "KVm", &args);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    assert!(String::from_utf8_lossy(&o.stderr).contains("progress: 31 cases, 0 open"));
    let defs = std::fs::read_to_string(d.join("KVm/ProgressDefs.lean")).unwrap();
    assert_eq!(defs.matches("def Progress.case.").count(), 31);
    assert!(defs.contains("K.«halted(_)_VM_Bool_K» (Ending.content c) = true"));
    let thms = std::fs::read_to_string(d.join("KVm/Progress.lean")).unwrap();
    assert!(thms.contains(
        "k2l_progress [App.add, App.«add-underflow0», App.«add-underflow1»] => prog_close else prog_stuck\n  all_goals first | prog_stuck_deep | fail"
    ));
    // the goals the search leaves: the invariant unfolded and taken apart, then `simp` and the
    // closer's split in turn
    assert!(thms.contains("local macro \"prog_stuck_deep\" : tactic => `(tactic| (exfalso; (try simp only [Invariant, "));
    assert!(thms.contains("(try k2l_destruct); (repeat' (first | (simp_all ["));
    assert!(thms.contains("k2l_case_stuck))); done))"));
    assert!(
        thms.contains("set_option maxHeartbeats 2000000 in\ntheorem Progress.case.«Instr.add» :")
    );
    assert!(thms.contains("(hI : Invariant c) : Ending c ∨ App c := by"));
    assert!(!thms.contains("Progress.Refuted"));

    std::fs::write(
        d.join("open-progress-cases.txt"),
        "Progress.case.«Instr.pop» | refuted hand\n",
    )
    .unwrap();
    let o = gen_progress("vm", &d, "KVm", &args);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let thms = std::fs::read_to_string(d.join("KVm/Progress.lean")).unwrap();
    assert!(thms.contains("Ending c ∨ App c ∨ Progress.Refuted c := by"));
    assert!(thms.contains("#k2l_refuted Progress.case.«Instr.pop»"));
    assert!(!thms.contains("theorem Progress.case.«Instr.pop» :"));
    let hand = std::fs::read_to_string(d.join("KVm/ProgressHand.lean")).unwrap();
    assert!(hand.contains("-- theorem Progress.case.«Instr.pop».refuted"));
    std::fs::write(d.join("KVm/ProgressHand.lean"), "-- edited\n").unwrap();
    let o = gen_progress("vm", &d, "KVm", &args);
    assert!(o.status.success());
    assert_eq!(
        std::fs::read_to_string(d.join("KVm/ProgressHand.lean")).unwrap(),
        "-- edited\n"
    );

    let o = gen_progress("vm", &d, "KVm", &["--invariant", "kOk@k"]);
    assert!(o.status.success());
    assert!(!d.join("KVm/Progress.lean").exists() && !d.join("KVm/ProgressDefs.lean").exists());
}

/// `gen --progress` with priority ranks (design.md §3.9, SND-15) on `vmpri`, the stack machine with
/// `add`'s underflows at `priority(40)` and `pop`'s as `owise`: every case states `Progress.App`
/// (some rule of some rank applies), `Progress.App.least` gives the rank `Step` takes, and a case
/// still lists its head's rules, of every rank.
#[test]
fn progress_with_priority_ranks_states_that_some_rule_of_some_rank_applies() {
    let d = tmp("cli-progress-ranks");
    let args = ["--invariant", "kOk@k", "--progress", "--ending", "halted@k"];
    let o = gen_progress("vmpri", &d, "KVmPri", &args);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    assert!(String::from_utf8_lossy(&o.stderr).contains("progress: 31 cases, 0 open"));
    let defs = std::fs::read_to_string(d.join("KVmPri/ProgressDefs.lean")).unwrap();
    assert!(defs.contains(
        "def Progress.App (c : SortGeneratedTopCell) : Prop :=\n  ∃ i, KVmPri.App i c\n"
    ));
    assert!(defs.contains("(h : Progress.App c) : ∃ i, KVmPri.App i c ∧ ∀ j, j < i → ¬ KVmPri.App j c :=\n  KPrelude.Progress.exists_least h"));
    assert_eq!(defs.matches("def Progress.case.").count(), 31);
    assert_eq!(defs.matches("→ Progress.App (").count(), 31);
    let thms = std::fs::read_to_string(d.join("KVmPri/Progress.lean")).unwrap();
    assert!(thms.contains(
        "k2l_progress [App.«add-underflow0», App.«add-underflow1», App.add] => prog_close else prog_stuck"
    ));
    assert!(thms.contains("k2l_progress [App.pop, App.«pop-underflow»] => prog_close"));
    assert!(thms.contains("(hI : Invariant c) : Ending c ∨ Progress.App c := by"));
    assert!(thms.contains("∀ n, Ending (s n) ∨ Progress.App (s n) :="));
}

/// `gen --progress` with `<k>` in a cell map (design.md §3.9, SND-14) on the coroutines `coro`: one
/// case per head of an element's `<k>`, stated at the element's match with `Progress.Keys` and
/// `Progress.Above` (every element of a higher rank is an ending), the rules of a head read off
/// their first element, the partner lemma and `Keys` preserved per rule; a refuted case's head is
/// the third outcome at an element's match; an ending's cell outside the elements is refused.
#[test]
fn progress_at_a_cell_map_states_a_case_per_element_head_above_which_every_element_ends() {
    let d = tmp("cli-progress-coro");
    let args = ["--invariant", "kOk@k", "--progress", "--ending", "ended@k"];
    let o = gen_progress("coro", &d, "Coro", &args);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    assert!(String::from_utf8_lossy(&o.stderr).contains("progress: 36 cases, 0 open"));
    let defs = std::fs::read_to_string(d.join("Coro/ProgressDefs.lean")).unwrap();
    assert_eq!(defs.matches("def Progress.case.").count(), 36);
    assert!(defs.contains("def Progress.Keys (c : SortGeneratedTopCell) : Prop :="));
    assert!(defs.contains("K.«ended(_)_CORO_Bool_K» (Ending.content e) = true"));
    assert!(defs.contains(
        "∀ k e r, MapHook.concat (MapHook.element k e) r = some (Progress.map c) → Ending.elem e"
    ));
    assert!(defs.contains("Progress.Keys (SortGeneratedTopCell.«<generatedTop>» (SortTCell.«<T>» (SortProcsCell.«<procs>» m)) x0_1) → Progress.Above m kc"));
    let thms = std::fs::read_to_string(d.join("Coro/Progress.lean")).unwrap();
    assert!(thms.contains(
        "k2l_progress [App.resume, App.«resume-finished», App.«resume-failed», App.«resume-none»] => prog_close else prog_stuck partner (Progress.partner hm hK hA) rank prog_rank\n  all_goals first | prog_stuck_deep | fail"
    ));
    assert!(thms.contains("local macro \"prog_stuck_deep\" : tactic => `(tactic| (exfalso; clear hA hK; (try simp only [Invariant, "));
    assert!(thms.contains(
        "theorem Progress.Keys.case.spawn : Step.Case.spawn Progress.Keys := by k2l_keys"
    ));
    assert!(thms.contains("theorem Progress.partner {kc k' : SortPidCell}"));
    assert!(thms.contains("(hK : Progress.Keys c) : Ending c ∨ App 0 c := by"));
    assert!(thms.contains(
        "MapHook.exists_maximal (P := fun _ e => Ending.elem e) (Progress.rank (Progress.map c)) hx"
    ));
    assert!(defs.contains(
        "noncomputable def Progress.rank (_ : SortProcCellMap) (k : SortPidCell) (_ : SortProcCell) : Nat := sizeOf k"
    ));

    std::fs::write(
        d.join("open-progress-cases.txt"),
        "Progress.case.«Instr.resume(_)» | refuted hand\n",
    )
    .unwrap();
    let o = gen_progress("coro", &d, "Coro", &args);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let defs = std::fs::read_to_string(d.join("Coro/ProgressDefs.lean")).unwrap();
    assert!(
        defs.contains("x0_1 ∧ MapHook.concat (MapHook.element kc (SortProcCell.«<proc>» kc e0_1")
    );
    let thms = std::fs::read_to_string(d.join("Coro/Progress.lean")).unwrap();
    assert!(thms.contains("Ending c ∨ App 0 c ∨ Progress.Refuted c := by"));
    assert!(thms.contains("#k2l_refuted Progress.case.«Instr.resume(_)»"));

    let o = gen_progress(
        "coro",
        &d,
        "Coro",
        &["--progress", "--ending", "ended@procs"],
    );
    assert!(!o.status.success());
    assert!(
        String::from_utf8_lossy(&o.stderr)
            .contains("the ending's cell must be in the same elements")
    );
}

/// `gen --progress` under a kind 2 invariant (SND-14 slice 2b, design.md §3.9) on `handoff`: spelled
/// as `claims` takes it, `Invariant` is the Lean predicate and its preservation theorem; the modules go
/// to the package that holds it (`--progress-out`, under `--progress-prefix`) with the library's
/// hooks, and none is left in the library; each case adds the element fact (`--element-fact`) and the
/// rank is the author's, of the cell map (`--rank`); the hand skeleton imports the downstream module.
#[test]
fn progress_under_a_kind_2_invariant_is_written_where_the_invariant_is() {
    let d = tmp("cli-progress-kind2");
    let pkg = d.join("Pkg");
    let unfold = d.join("unfold.txt");
    std::fs::create_dir_all(&pkg).unwrap();
    std::fs::write(&unfold, "# the stuck closer's names\nPkg.TaskOk\n").unwrap();
    std::fs::create_dir_all(d.join("lib/Handoff")).unwrap();
    std::fs::write(d.join("lib/Handoff/Progress.lean"), "-- stale\n").unwrap();
    let args: Vec<String> = [
        "--progress",
        "--assume-invariant",
        "Pkg.Live",
        "--invariant-module",
        "Pkg.Live",
        "--invariant-preserved",
        "Pkg.Live.preserved",
        "--element-fact",
        "Pkg.Live.taskOk",
        "--rank",
        "Pkg.taskRank",
        "--progress-prefix",
        "Pkg",
    ]
    .iter()
    .map(|s| s.to_string())
    .chain([
        "--invariant-unfold".to_string(),
        unfold.display().to_string(),
        "--progress-out".to_string(),
        pkg.display().to_string(),
    ])
    .collect();
    let argv: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    let o = gen_progress("handoff", &d.join("lib"), "Handoff", &argv);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    assert!(String::from_utf8_lossy(&o.stderr).contains("progress: 37 cases, 0 open"));
    assert!(!d.join("lib/Handoff/Progress.lean").exists());
    let defs = std::fs::read_to_string(pkg.join("Pkg/ProgressDefs.lean")).unwrap();
    assert!(
        defs.contains("import Handoff.Preserves\nimport KPrelude.InvTactic\nimport Pkg.Live\n")
    );
    assert!(defs.contains("import KPrelude.Progress\nimport KPrelude.PendingTactic\n"));
    assert!(defs.contains("def Invariant (c : SortGeneratedTopCell) : Prop := Pkg.Live c"));
    assert!(
        defs.contains(
            "theorem Invariant.preserved : Preserved Step Invariant := Pkg.Live.preserved"
        )
    );
    assert!(defs.contains("Nat := Pkg.taskRank m k e"));
    assert!(defs.contains("namespace Handoff\n\nvariable [Hooks]\n"));
    let thms = std::fs::read_to_string(pkg.join("Pkg/Progress.lean")).unwrap();
    assert!(thms.starts_with("import Pkg.ProgressDefs\n"));
    assert!(thms.contains("namespace Handoff\n\nvariable [Hooks]\n"));
    assert!(thms.contains(
        "  have hF := Pkg.Live.taskOk hI hm\n  try simp [Pkg.TaskOk] at hF\n  k2l_destruct\n"
    ));
    assert!(thms.contains("Ending.elem, Invariant,") && thms.contains(", Pkg.TaskOk"));

    std::fs::write(
        pkg.join("open-progress-cases.txt"),
        "Progress.case.«Instr.resume(_,_,_)»\n",
    )
    .unwrap();
    let o = gen_progress("handoff", &d.join("lib"), "Handoff", &argv);
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    let hand = std::fs::read_to_string(pkg.join("Pkg/ProgressHand.lean")).unwrap();
    assert!(hand.starts_with("import Pkg.ProgressDefs\n"));
    assert!(hand.contains("namespace Handoff\n\nvariable [Hooks]\n"));

    let o = gen_progress(
        "handoff",
        &d.join("lib"),
        "Handoff",
        &["--progress", "--element-fact", "Pkg.Live.taskOk"],
    );
    assert!(!o.status.success());
    assert!(String::from_utf8_lossy(&o.stderr).contains("--element-fact needs --assume-invariant"));
}

/// `gen --invariant` at `init` when a cell holds configuration variables under constructors
/// (`<k> $PGM </k>` is `$PGM ~> .K`; in `coro`, the one `<proc>` of the cell map holds it): the part
/// is proved by computation for every program, with no hypothesis and no hand obligation; once
/// `init` is listed (its proof failed, `open-from-log`), the part's predicate at the content, written
/// as the term, is the hypothesis instead, and the list keeps it.
#[test]
fn invariant_init_over_configuration_variables_is_computed_or_its_content_is_the_hypothesis() {
    for (fx, ns, hyp) in [
        (
            "vm",
            "KVm",
            "(h_kOk : K.«kOk(_)_VM_Bool_K» (SortK.kseq (SortKItem.inj_Pgm pgm) SortK.dotk : SortK) = some true)",
        ),
        (
            "coro",
            "Coro",
            "(h_kOk : KPrelude.MapHook.EntriesOn Invariant.kOk_elem (KPrelude.MapHook.element (SortPidCell.«<pid>» SortPid.root) (SortProcCell.«<proc>» (SortPidCell.«<pid>» SortPid.root) (SortNonceCell.«<nonce>» (0 : Int)) (SortKCell.«<k>» (SortK.kseq (SortKItem.inj_Pgm pgm) SortK.dotk))) : SortProcCellMap))",
        ),
    ] {
        let d = tmp(&format!("cli-init-{fx}"));
        let o = gen_progress(fx, &d, ns, &["--invariant", "kOk@k"]);
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
        let thms = std::fs::read_to_string(d.join(ns).join("Invariants.lean")).unwrap();
        assert!(
            thms.contains("theorem Invariant.init_holds (pgm : SortPgm) :\n    Invariant (init pgm) :=\n  (by simp only [Invariant, Invariant.kOk,"),
            "{thms}"
        );
        assert!(
            !thms.contains("Invariant.hand.init")
                && !thms.contains(&format!("import {ns}.InvariantsHand"))
        );
        assert!(!d.join(ns).join("InvariantsHand.lean").exists());

        std::fs::write(d.join("open-invariant-cases.txt"), "Invariant.init_holds\n").unwrap();
        for _ in 0..2 {
            let o = gen_progress(fx, &d, ns, &["--invariant", "kOk@k"]);
            assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
            let thms = std::fs::read_to_string(d.join(ns).join("Invariants.lean")).unwrap();
            assert!(
                thms.contains(&format!("theorem Invariant.init_holds (pgm : SortPgm) {hyp} :\n    Invariant (init pgm) :=\n  h_kOk\n")),
                "{thms}"
            );
            assert!(thms.contains("Invariant.preserved.star h (Invariant.init_holds pgm h_kOk)"));
            assert!(!thms.contains("Invariant.hand.init"));
            assert!(!d.join(ns).join("InvariantsHand.lean").exists());
            let open = std::fs::read_to_string(d.join("open-invariant-cases.txt")).unwrap();
            assert!(open.lines().any(|l| l.starts_with("init | ")), "{open}");
        }
    }
}
