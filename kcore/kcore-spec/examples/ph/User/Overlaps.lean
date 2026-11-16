/-
  R4 (ARCHITECTURE.md §5) over the generated package `Ph` (`f2-examples/ph.k`, parameter hooks in its
  `requires`): the package proves determinism up to two overlaps for **every** interpretation H
  (`Ph.deterministic_except`). The overlaps are obligations on H: under an interpretation where
  `bad` and `ok` hold together the step branches (`overlap_real`); under one where `bad` never holds,
  the executable step lists one successor of `go(a)` (`goA_safe`), and under the data's own
  interpretation (nothing defined) none (`goA_none`).
-/
import Ph

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ph

open KCore

def goCfg (v : KCore.Sym) : GroundTerm :=
  .ctor topLabel [.ctor Sym.«<k>» [.ctor kseq [.ctor Sym.«go» [.ctor v []], .ctor dotk []]],
    .ctor counterLabel [.dv KCore.Srt.int (.int 0)]]

/-- An interpretation under which `ok(a)` and `bad(a)` both hold. -/
def Hboth : HookParams := ⟨fun f _ => if f == Sym.«ok» || f == Sym.«bad» then some (bool true) else none⟩
/-- An interpretation under which `ok(a)` holds and `bad` never does. -/
def Hsafe : HookParams :=
  ⟨fun f _ => if f == Sym.«ok» then some (bool true) else if f == Sym.«bad» then some (bool false) else none⟩

theorem goA_sorted : c.sortOf (goCfg Sym.«a») = some topCellSort := sortOf_of_T T_eq (by decide +kernel)
theorem goA_both : Det.witnessOK (c.withHooks Hboth) 1000 0 2 (goCfg Sym.«a») = true := by decide +kernel
theorem goA_safe : (Exec.successorsN (c.withHooks Hsafe) 1000 (goCfg Sym.«a»)).length = 1 := by decide +kernel
theorem goA_none : Exec.successorsN c 1000 (goCfg Sym.«a») = [] := by decide +kernel

/-- The overlap of rules 0 and 2 is real under `Hboth`: both apply at `go(a)` and the step branches. -/
theorem overlap_real : ∃ x : Config (c.withHooks Hboth),
    ∃ (hi : 0 < (c.withHooks Hboth).rules.length) (hj : 2 < (c.withHooks Hboth).rules.length),
      Det.Applies (c.withHooks Hboth) (c.withHooks Hboth).rules[0] x.val ∧
      Det.Applies (c.withHooks Hboth) (c.withHooks Hboth).rules[2] x.val ∧
      ∃ y y' : Config (c.withHooks Hboth), Step (c.withHooks Hboth) x y ∧ Step (c.withHooks Hboth) x y' ∧ y ≠ y' :=
  ⟨⟨goCfg Sym.«a», goA_sorted⟩, Det.witnessed_of (c := c.withHooks Hboth) ((Semantics.ok_withHooks _ _).trans ok)
    ((Semantics.srReady_withHooks _ _).trans srReady) ((Semantics.matchReady_withHooks _ _).trans matchReady)
    (x := ⟨goCfg Sym.«a», goA_sorted⟩) goA_both⟩

/-- info: 'Ph.deterministic_except' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deterministic_except
/-- info: 'Ph.overlap_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overlap_real

end Ph
