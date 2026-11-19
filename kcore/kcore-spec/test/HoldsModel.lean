/-
  A rule's conditions in the value model at a transition T (`KCore.Faithful.holds_stdI`,
  `Faithful.Model.holds_atT`). Run from the package root: `lake env lean -j1 test/HoldsModel.lean`.
  Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore` (as `test/ExRules.lean`):
  `a(Exp)` and `b()` of sort Exp (symbols 385, 386), `<generatedCounter>(Int)` (73) of the counter
  cell's sort. Each condition below has `condOK` and `Cond.bound` (decided), and the lemma is read at
  it in the value model at any T, under `FnDet` and `FnSolves`:
  - `pNot`: `not (and (mem Z a(b)) (mem Z G))`, Z and G of Exp (the pre of a complement on a left side);
  - `pOr`: `or (mem Z b) (mem Z a(b))` (the post of a connective on a right side);
  - `pCeil`: `ceil (X *Int 2)`; `pEq`: `equals (X ==Int 1) true`, X of Int;
  - `pEx`: `∃ B:Bool. B = true`; `pAll`: `∀ B:Bool. B ∈ true ∨ B ∈ false`;
  - `pMatch`: `∃ X:Int. C ∈ <generatedCounter>(X)`, C of the counter cell's sort, X held by the pattern
    under a constructor.
  `holds_stdI` at `pNot`, `pOr` and `pMatch`, the truth value from `holds_decided` under `FnHyp`.
  `HoldsShape.holds_entailsCEx` at `pNot` in any model of `Γc`, with `holds_true`, `holds_false` and
  `holds_unique` there.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HoldsModelT

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)
def tt : Term := .dv Srt.bool (.bool true)
def ff : Term := .dv Srt.bool (.bool false)
def tA (t : Term) : Term := .app 385 [t]
def tB : Term := .app 386 []

/-- The counter cell's sort (the second variable of the text's rule). -/
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

example : c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 73 = "Lbl'-LT-'generatedCounter'-GT-'" ∧
    c.sortName 32 = "Exp" := by
  decide +kernel

def pNot : Cond := .not (.and (.mem 32 (.var 0) (tA tB)) (.mem 32 (.var 0) (.var 1)))
def pOr : Cond := .or (.mem 32 (.var 0) tB) (.mem 32 (.var 0) (tA tB))
def pCeil : Cond := .ceil Srt.int (.app intMul [.var 0, i 2])
def pEq : Cond := .equals Srt.bool (.app intEq [.var 0, i 1]) tt
def pEx : Cond := .ex Srt.bool (.equals Srt.bool (.var 1) tt)
def pAll : Cond := .all Srt.bool (.or (.mem Srt.bool (.var 0) tt) (.mem Srt.bool (.var 0) ff))
noncomputable def pMatch : Cond := .exMatch [Srt.int] sC (.app 73 [.var 1]) (.var 0) .top

theorem coreOK : c.coreOK = true := by decide_cheap

theorem conds_ok :
    (c.condOK [32, 32] pNot = true ∧ Cond.bound c 2 pNot = true) ∧
    (c.condOK [32] pOr = true ∧ Cond.bound c 1 pOr = true) ∧
    (c.condOK [Srt.int] pCeil = true ∧ Cond.bound c 1 pCeil = true) ∧
    (c.condOK [Srt.int] pEq = true ∧ Cond.bound c 1 pEq = true) ∧
    (c.condOK [Srt.int] pEx = true ∧ Cond.bound c 1 pEx = true) ∧
    (c.condOK [] pAll = true ∧ Cond.bound c 0 pAll = true) ∧
    (c.condOK [sC] pMatch = true ∧ Cond.bound c 1 pMatch = true) := by
  decide +kernel

/-- The binder of `pMatch` is held by its pattern under a constructor, not by a confined sort; the
binders of `pEx` and `pAll` are of the confined sort Bool. -/
example : (ctorOccs c (.app 73 [.var 1])).contains 1 = true ∧ c.confined Srt.int = false ∧
    c.confined Srt.bool = true := by
  decide +kernel

section
open Faithful Faithful.Model

variable (hd : FnDet c) (hs : FnSolves c) (T : GroundTerm → GroundTerm → Prop)
include hd hs

/-! ## The reading at each shape -/

omit hd hs in
/-- `holds_atT` at a condition with its two facts, every other premise explicit. -/
theorem holdsAt (h : HypModelCore c) (p : Cond) (vars : List Srt) (hok : c.condOK vars p = true)
    (hbd : Cond.bound c vars.length p = true) :
    ∀ (P : Nat → Prop) (σ : Subst) (b : Bool) (tbl : KoreAML.VarTable) (e : ML.Valuation Elem) (S : Srt),
      (∀ j ∈ varOccsCond vars.length p, j < vars.length → P j) → ReadsT c vars P σ tbl e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
      S < nRegSorts + c.sortNames.length → Holds c vars.length σ p b → ∀ a, InSort c S a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔ b = true) :=
  fun _ _ _ _ _ _ hP hr hk hS hh a ha => holds_atT (T := T) h p hok hbd hP hr hk hS hh a ha

example := holdsAt T (hypModel_of_fn coreOK hd hs) pNot [32, 32] conds_ok.1.1 conds_ok.1.2
example := holdsAt T (hypModel_of_fn coreOK hd hs) pOr [32] conds_ok.2.1.1 conds_ok.2.1.2
example := holdsAt T (hypModel_of_fn coreOK hd hs) pCeil [Srt.int] conds_ok.2.2.1.1 conds_ok.2.2.1.2
example := holdsAt T (hypModel_of_fn coreOK hd hs) pEq [Srt.int] conds_ok.2.2.2.1.1 conds_ok.2.2.2.1.2
example := holdsAt T (hypModel_of_fn coreOK hd hs) pEx [Srt.int] conds_ok.2.2.2.2.1.1 conds_ok.2.2.2.2.1.2
example := holdsAt T (hypModel_of_fn coreOK hd hs) pAll [] conds_ok.2.2.2.2.2.1.1 conds_ok.2.2.2.2.2.1.2
example := holdsAt T (hypModel_of_fn coreOK hd hs) pMatch [sC] conds_ok.2.2.2.2.2.2.1 conds_ok.2.2.2.2.2.2.2

/-- The case lemmas at their shapes. -/
example : HoldsT c T pNot := holdsT_not (hypModel_of_fn coreOK hd hs)
  (holdsT_and (holdsT_mem (hypModel_of_fn coreOK hd hs) 32 (.var 0) (tA tB))
    (holdsT_mem (hypModel_of_fn coreOK hd hs) 32 (.var 0) (.var 1)))
example : HoldsT c T pOr := holdsT_or (hypModel_of_fn coreOK hd hs)
  (holdsT_mem (hypModel_of_fn coreOK hd hs) 32 (.var 0) tB) (holdsT_mem (hypModel_of_fn coreOK hd hs) 32 (.var 0) (tA tB))
example : HoldsT c T pCeil := holdsT_ceil (hypModel_of_fn coreOK hd hs) Srt.int (.app intMul [.var 0, i 2])
example : HoldsT c T pEq := holdsT_equals (hypModel_of_fn coreOK hd hs) Srt.bool (.app intEq [.var 0, i 1]) tt
example : HoldsT c T pEx := holdsT_ex (hypModel_of_fn coreOK hd hs) Srt.bool
  (holdsT_equals (hypModel_of_fn coreOK hd hs) Srt.bool (.var 1) tt)
example : HoldsT c T pAll := holdsT_all (hypModel_of_fn coreOK hd hs) Srt.bool
  (holdsT_or (hypModel_of_fn coreOK hd hs) (holdsT_mem (hypModel_of_fn coreOK hd hs) Srt.bool (.var 0) tt)
    (holdsT_mem (hypModel_of_fn coreOK hd hs) Srt.bool (.var 0) ff))
example : HoldsT c T pMatch := holdsT_exMatch (hypModel_of_fn coreOK hd hs) [Srt.int] sC (.app 73 [.var 1]) (.var 0)
  (holdsT_top (hypModel_of_fn coreOK hd hs))
example : HoldsT c T (.implies .top .bot) :=
  holdsT_implies (hypModel_of_fn coreOK hd hs) (holdsT_top (hypModel_of_fn coreOK hd hs)) holdsT_bot

/-- `holds_atoms` at the atoms of `pCeil`, `pEq` and `pOr`. -/
example : HoldsT c T pCeil := (holds_atoms (hypModel_of_fn coreOK hd hs)).1 Srt.int (.app intMul [.var 0, i 2])
example : HoldsT c T pEq := (holds_atoms (hypModel_of_fn coreOK hd hs)).2.1 Srt.bool (.app intEq [.var 0, i 1]) tt
example : HoldsT c T (.mem 32 (.var 0) tB) := (holds_atoms (hypModel_of_fn coreOK hd hs)).2.2 32 (.var 0) tB

end

/-! ## Where the condition has a truth value: exactly where it is `true` -/

section
open Faithful Faithful.Model

variable (hf : FnHyp c) (T : GroundTerm → GroundTerm → Prop)
include hf

theorem hModel : HypModelCore c :=
  hypModel_of_fn coreOK (fnModel_of_fnHyp coreOK hf).1 (fnModel_of_fnHyp coreOK hf).2

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 2 pNot, j < 2 → P j) (hr : ReadsT c [32, 32] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [32, 32]) (srtOf c S) pNot), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [32, 32]) (srtOf c S) pNot)).interpret (stdI_T c T) e a ↔
      Holds c 2 σ pNot true :=
  holds_stdI (hModel hf) T pNot conds_ok.1.1 conds_ok.1.2 hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pNot conds_ok.1.1 (hr.sortedCond hP)) a ha

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pOr, j < 1 → P j) (hr : ReadsT c [32] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [32]) (srtOf c S) pOr), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [32]) (srtOf c S) pOr)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pOr true :=
  holds_stdI (hModel hf) T pOr conds_ok.2.1.1 conds_ok.2.1.2 hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pOr conds_ok.2.1.1 (hr.sortedCond hP)) a ha

example {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation Elem} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 1 pMatch, j < 1 → P j) (hr : ReadsT c [sC] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [sC]) (srtOf c S) pMatch), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [sC]) (srtOf c S) pMatch)).interpret (stdI_T c T) e a ↔
      Holds c 1 σ pMatch true :=
  holds_stdI (hModel hf) T pMatch conds_ok.2.2.2.2.2.2.1 conds_ok.2.2.2.2.2.2.2 hP hr hk hS
    (holds_decided (hypSound_of_core coreOK) hf.1 pMatch conds_ok.2.2.2.2.2.2.1 (hr.sortedCond hP)) a ha

end

/-! ## The helper facts at instances -/

open Faithful Faithful.Model in
/-- Bool is numbered by being confined; `X *Int 2`'s sort Int by the term's. -/
example (hd : FnDet c) (hs : FnSolves c) :
    Srt.bool < nRegSorts + c.sortNames.length ∧ Srt.int < nRegSorts + c.sortNames.length :=
  ⟨confined_numberedStdI (hypModel_of_fn coreOK hd hs) (by decide +kernel),
   sortOfTerm_numStdI (hypModel_of_fn coreOK hd hs) (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl
     (vars := [Srt.int]) (.app intMul [.var 0, i 2]) (by decide +kernel) (fun j hj s' hs' => by
       simp [varOccs, varOccsList, i] at hj
       subst hj
       simp at hs'
       subst hs'
       decide +kernel)⟩

open Faithful in
example : canonVars c [32] ++ [Cond.binder c (canonVars c [32]).length Srt.bool] = canonVars c [32, Srt.bool] :=
  Model.canonVars_snocStdI c [32] Srt.bool

example : ∀ j ∈ ctorOccs c (.app 73 [.var 1]), j ∈ varOccs (.app 73 [.var 1]) :=
  Faithful.Model.ctorOccs_varOccsStdI (c := c) _

/-! ## The lemma in every model of `Γc` -/

section
open ML Faithful Faithful.Model HoldsShape

/-- `holds_entailsCEx` at `pNot`, which holds no binder, in any model of `Γc`. -/
theorem entailsNot {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    HoldsDen' c I pNot :=
  holds_entailsCEx (Semantics.coreOK_iff_ex.mp coreOK) hIc hc pNot fun hb => absurd hb (by decide +kernel)

/-- Its two halves and the uniqueness of the truth value at `pNot`. -/
example {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : ML.Valuation M} {S : Srt}
    (hP : ∀ j ∈ varOccsCond 2 pNot, j < 2 → P j) (hr : Reads c I [32, 32] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [32, 32]) (srtOf c S) pNot), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : M)
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a) :
    (Holds c 2 σ pNot true →
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [32, 32]) (srtOf c S) pNot)).interpret I e a) ∧
    (Holds c 2 σ pNot false →
      (KoreAML.tr ⟨tbl, []⟩ (.not (srtOf c S) (Cond.kore c (canonVars c [32, 32]) (srtOf c S) pNot))).interpret I e a) ∧
    (Holds c 2 σ pNot true → Holds c 2 σ pNot false → False) :=
  ⟨fun hh => holds_true (entailsNot hIc hc) conds_ok.1.1 conds_ok.1.2 hP hr hk hS hh a ha,
   fun hh => holds_false (entailsNot hIc hc) conds_ok.1.1 conds_ok.1.2 hP hr hk hS hh a ha,
   fun ht hf => holds_unique (entailsNot hIc hc) conds_ok.1.1 conds_ok.1.2 hP hr hk hS ⟨a, ha⟩ ht hf⟩

end

end HoldsModelT
