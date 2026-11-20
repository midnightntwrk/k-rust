/-
  A condition with a binder of a sort that is not confined, in the value model at a transition T
  (`KCore.Faithful.holds_stdI_fixed`, `Faithful.Model.holds_atT_fixed`, KcoreSpec/HoldsModelFixed.lean;
  `Faithful.holds_stdI`, `Faithful.Model.boundReads_boundV_stdI`, KcoreSpec/HoldsModel.lean).
  Run from the package root: `lake env lean -j1 test/HoldsModelFixed.lean`. Kernel-checked
  (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore` (as `test/HoldsModel.lean`).
  - `pOrEx`: `Z ∈ 3 ∨ ∃ B:Int. (Z ∈ B ∧ B = 4)`, Z of Int: the binder B is of Int, which is not
    confined and has a value (`Semantics.hasValue`), and the body fixes B by `B = 4`. `Cond.bound`
    accepts it, as `Cond.boundV c c.hasValue` does (`Cond.bound_eq_boundV`); `Cond.boundConf`, which
    reads the binder's sort alone, refuses it (`conds_ok`).
  - `pNotEx`: `¬ pOrEx`, the binder under two connectives.
  - `pFree`: `∃ B:Int. Z ∈ B`: the body fixes Z by B and not B, so all three refuse it.
  `holds_atT_fixed`, `holds_stdI_fixed` and `holds_stdI` at `pOrEx` and `pNotEx`, the truth value
  from `holds_decided` under `FnHyp`; `Cond.boundV_hasValue_of_bound` at an instance; `hval`, the
  premise of `holds_stdI_fixed`, by `hasValue_value`.
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

theorem coreOK : c.coreOK = true := by decide_cheap

theorem conds_ok :
    c.confined Srt.int = false ∧ c.hasValue Srt.int = true ∧
    (c.condOK [Srt.int] pOrEx = true ∧ Cond.bound c 1 pOrEx = true ∧
      Cond.boundConf c 1 pOrEx = false) ∧
    (c.condOK [Srt.int] pNotEx = true ∧ Cond.bound c 1 pNotEx = true ∧
      Cond.boundConf c 1 pNotEx = false) ∧
    (c.condOK [Srt.int] pFree = true ∧ Cond.bound c 1 pFree = false ∧
      Cond.boundConf c 1 pFree = false) ∧
    (Cond.bound c 1 pBool = true ∧ Cond.boundConf c 1 pBool = true) := by
  decide +kernel

/-- `Cond.bound` is `Cond.boundV` at `c.hasValue`. -/
theorem boundV_pOrEx : Cond.boundV c c.hasValue 1 pOrEx = true := by
  rw [← Cond.bound_eq_boundV]; exact conds_ok.2.2.1.2.1
theorem boundV_pNotEx : Cond.boundV c c.hasValue 1 pNotEx = true := by
  rw [← Cond.bound_eq_boundV]; exact conds_ok.2.2.2.1.2.1

example : Cond.boundV c c.hasValue 1 pBool = true :=
  Cond.boundV_hasValue_of_bound c pBool 1 conds_ok.2.2.2.2.2.1

section
open Faithful Faithful.Model

variable (hf : FnHyp c) (T : GroundTerm → GroundTerm → Prop)
include hf

theorem hModel : HypModelCore c :=
  hypModel_of_fn coreOK (fnModel_of_fnHyp coreOK hf).1

/-- A sort `hasValue` accepts is numbered: it has a value (`hasValue_value`, on `coreOK`), whose
sort is numbered in the model. -/
theorem hval : ∀ s, c.hasValue s = true → s < nRegSorts + c.sortNames.length := fun _ hs =>
  let ⟨_, hv⟩ := hasValue_value coreOK hs; sortOf_numbered (hModel hf) hv

/-- The recursion reads `Cond.boundV` at `c.hasValue`, and `Cond.bound`, in the value model. -/
example : HoldsShape.BoundReads c (stdI_T c T) (Cond.boundV c c.hasValue) :=
  boundReads_boundV_stdI (hModel hf) (hval hf)
example : HoldsShape.BoundReads c (stdI_T c T) (Cond.bound c) :=
  boundReads_bound_stdI (hModel hf)

example {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pOrEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hh : Holds c 1 σ pOrEx b) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx)).interpret (stdI_T c T) e a ↔
      b = true :=
  holds_atT_fixed (hModel hf) (hval hf) pOrEx conds_ok.2.2.1.1 boundV_pOrEx hP hr hk hS hh a ha

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pOrEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pOrEx true :=
  holds_stdI_fixed (hModel hf) T (hval hf) pOrEx conds_ok.2.2.1.1 boundV_pOrEx hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pOrEx conds_ok.2.2.1.1 (hr.sortedCond hP)) a ha

/-- `holds_stdI` itself, over `Cond.bound`, at `pOrEx`. -/
example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pOrEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pOrEx)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pOrEx true :=
  holds_stdI (hModel hf) T pOrEx conds_ok.2.2.1.1 conds_ok.2.2.1.2.1 hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pOrEx conds_ok.2.2.1.1 (hr.sortedCond hP)) a ha

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pNotEx, j < 1 → P j) (hr : ReadsT c [Srt.int] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pNotEx), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c S) pNotEx)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pNotEx true :=
  holds_stdI_fixed (hModel hf) T (hval hf) pNotEx conds_ok.2.2.2.1.1 boundV_pNotEx hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pNotEx conds_ok.2.2.2.1.1 (hr.sortedCond hP)) a ha

end

#print axioms KCore.Faithful.holds_stdI_fixed
#print axioms KCore.Faithful.Model.holds_atT_fixed
#print axioms KCore.HoldsShape.holds_denB
#print axioms KCore.Cond.bound_eq_boundV
#print axioms KCore.Cond.boundV_hasValue_of_bound
#print axioms KCore.Cond.bound_of_boundV_valued
#print axioms KCore.Semantics.clausePlainEx_of_valued
#print axioms KCore.Semantics.hasValue_of_valued
#print axioms KCore.hasValue_value_of
#print axioms KCore.Faithful.Model.boundReads_bound_stdI

end HoldsModelFixedT
