/-
  A condition with a binder of a sort that is not confined, in the value model at a transition T
  (`KCore.Faithful.holds_stdI_fixed`, `Faithful.Model.holds_atT_fixed`, KcoreSpec/HoldsModelFixed.lean).
  Run from the package root: `lake env lean -j1 test/HoldsModelFixed.lean`. Kernel-checked
  (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore` (as `test/HoldsModel.lean`).
  - `pOrEx`: `Z ∈ 3 ∨ ∃ B:Int. (Z ∈ B ∧ B = 4)`, Z of Int: the binder B is of Int, which is not
    confined and is in `valueSorts`, and the body fixes B by `B = 4`. `Cond.bound` refuses it and
    `Cond.boundV c c.valueSorts.contains` accepts it (`conds_ok`).
  - `pNotEx`: `¬ pOrEx`, the binder under two connectives.
  - `pFree`: `∃ B:Int. Z ∈ B`: the body fixes Z by B and not B, so both refuse it.
  `holds_atT_fixed` and `holds_stdI_fixed` at `pOrEx` and `pNotEx`, the truth value from
  `holds_decided` under `FnHyp`; `Cond.boundV_none` and `Cond.boundV_of_bound` at instances.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HoldsModelFixedT

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)

def pOrEx : Cond :=
  .or (.mem Srt.int (.var 0) (i 3))
    (.ex Srt.int (.and (.mem Srt.int (.var 0) (.var 1)) (.equals Srt.int (.var 1) (i 4))))
def pNotEx : Cond := .not pOrEx
def pFree : Cond := .ex Srt.int (.mem Srt.int (.var 0) (.var 1))
def pBool : Cond := .ex Srt.bool (.equals Srt.bool (.var 1) (.dv Srt.bool (.bool true)))

theorem coreOK : c.coreOK = true := by decide +kernel

theorem conds_ok :
    c.confined Srt.int = false ∧ c.valueSorts.contains Srt.int = true ∧
    (c.condOK [Srt.int] pOrEx = true ∧ Cond.bound c 1 pOrEx = false ∧
      Cond.boundV c c.valueSorts.contains 1 pOrEx = true) ∧
    (c.condOK [Srt.int] pNotEx = true ∧ Cond.bound c 1 pNotEx = false ∧
      Cond.boundV c c.valueSorts.contains 1 pNotEx = true) ∧
    (c.condOK [Srt.int] pFree = true ∧ Cond.bound c 1 pFree = false ∧
      Cond.boundV c c.valueSorts.contains 1 pFree = false) ∧
    (Cond.bound c 1 pBool = true ∧ Cond.boundV c c.valueSorts.contains 1 pBool = true) := by
  decide +kernel

/-- Every sort of `valueSorts` is numbered. -/
theorem hval : ∀ s, c.valueSorts.contains s = true → s < nRegSorts + c.sortNames.length := by
  have h : c.valueSorts.all (fun s => decide (s < nRegSorts + c.sortNames.length)) = true := by
    decide +kernel
  intro s hs
  have := List.all_eq_true.mp h s (by simpa using hs)
  simpa using this

example : Cond.boundV c (fun _ => false) 1 pOrEx = Cond.bound c 1 pOrEx := Cond.boundV_none c pOrEx 1
example : Cond.boundV c c.valueSorts.contains 1 pBool = true :=
  Cond.boundV_of_bound c _ pBool 1 conds_ok.2.2.2.2.2.1

section
open Faithful Faithful.Model

variable (hf : FnHyp c) (T : GroundTerm → GroundTerm → Prop)
include hf

theorem hModel : HypModelCore c :=
  hypModel_of_fn coreOK (fnModel_of_fnHyp coreOK hf).1 (fnModel_of_fnHyp coreOK hf).2

/-- The recursion reads `Cond.boundV` in the value model. -/
example : HoldsShape.BoundReads c (stdI_T c T) (Cond.boundV c c.valueSorts.contains) :=
  boundReads_boundV_stdI (hModel hf) hval

example {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pOrEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hh : Holds c 1 σ pOrEx b) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx)).interpret (stdI_T c T) e a ↔
      b = true :=
  holds_atT_fixed (hModel hf) hval pOrEx conds_ok.2.2.1.1 conds_ok.2.2.1.2.2 hP hr hk hS hh a ha

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pOrEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pOrEx true :=
  holds_stdI_fixed (hModel hf) T hval pOrEx conds_ok.2.2.1.1 conds_ok.2.2.1.2.2 hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pOrEx conds_ok.2.2.1.1 (hr.sortedCond hP)) a ha

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pNotEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pNotEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pNotEx)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pNotEx true :=
  holds_stdI_fixed (hModel hf) T hval pNotEx conds_ok.2.2.2.1.1 conds_ok.2.2.2.1.2.2 hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pNotEx conds_ok.2.2.2.1.1 (hr.sortedCond hP)) a ha

end

#print axioms KCore.Faithful.holds_stdI_fixed
#print axioms KCore.Faithful.Model.holds_atT_fixed
#print axioms KCore.HoldsShape.holds_denB
#print axioms KCore.Cond.boundV_of_bound
#print axioms KCore.Cond.boundV_none

end HoldsModelFixedT
