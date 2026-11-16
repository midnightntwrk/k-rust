/-
  kink IMP (`f2-examples/imp.kore`) over its generated package `KinkImp`: the package's
  `deterministic_except` lists two overlaps as obligations, and both are real: `/` and `+` are
  `strict`, so either operand can be heated first. Each witness is a configuration where both rules
  apply and the step branches (`Det.witnessOK`, one kernel decision each).
-/
import KinkImp

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KinkImp

open KCore

/-- `<generatedTop> <T> <k> op(x, y) ~> . </k> <state> .Map </state> </T> <generatedCounter> 0 </generatedCounter> </generatedTop>` -/
def opCfg (op : KCore.Sym) : GroundTerm :=
  .ctor topLabel [.ctor Sym.«<T>» [.ctor Sym.«<k>» [.ctor kseq [.inj Srt.«AExp» KCore.Srt.kitem (.ctor op
      [.inj KCore.Srt.ident Srt.«AExp» (.dv KCore.Srt.ident (.tok "x")),
       .inj KCore.Srt.ident Srt.«AExp» (.dv KCore.Srt.ident (.tok "y"))]), .ctor dotk []]],
    .ctor Sym.«<state>» [.map KCore.Srt.map []]], .ctor counterLabel [.dv KCore.Srt.int (.int 0)]]
def divCfg : GroundTerm := opCfg Sym.«_/__IMP-SYNTAX_AExp_AExp_AExp»
def addCfg : GroundTerm := opCfg Sym.«_+__IMP-SYNTAX_AExp_AExp_AExp»

theorem divCfg_sorted : c.sortOf divCfg = some topCellSort := sortOf_of_T T_eq (by decide +kernel)
theorem addCfg_sorted : c.sortOf addCfg = some topCellSort := sortOf_of_T T_eq (by decide +kernel)
theorem div_witness : Det.witnessOK c 1000 17 19 divCfg = true := by decide +kernel
theorem add_witness : Det.witnessOK c 1000 21 23 addCfg = true := by decide +kernel

/-- Every overlap the package lists is real: at some configuration both of its rules apply and the
step branches. -/
theorem overlaps_witnessed : ∀ o ∈ ovl, ∃ x : Config c,
    ∃ (hi : o.1 < c.rules.length) (hj : o.2 < c.rules.length),
      Det.Applies c c.rules[o.1] x.val ∧ Det.Applies c c.rules[o.2] x.val ∧
      ∃ y y' : Config c, Step c x y ∧ Step c x y' ∧ y ≠ y' := by
  intro o ho
  simp only [ovl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ⟨⟨divCfg, divCfg_sorted⟩, Det.witnessed_of ok srReady matchReady (x := ⟨divCfg, divCfg_sorted⟩) div_witness⟩
  · exact ⟨⟨addCfg, addCfg_sorted⟩, Det.witnessed_of ok srReady matchReady (x := ⟨addCfg, addCfg_sorted⟩) add_witness⟩

/-- info: 'KinkImp.overlaps_witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overlaps_witnessed

/-- info: 'KinkImp.deterministic_except' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deterministic_except

end KinkImp
