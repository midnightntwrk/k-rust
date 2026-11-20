/-
  A condition's predicate at the sort variable `R` (`KCore.Faithful.cond_crossAt`,
  `HoldsShape.holds_atR`, `HoldsShape.holds_entails_atR`, `Faithful.Model.holdsT_atR`). Run from the
  package root: `lake env lean -j1 test/CondResort.lean`. Kernel-checked (`decide +kernel`).

  The semantics and the conditions are `test/HoldsModel.lean`'s (the reader's for
  `f2-examples/symrule.kompile.kore`): `pNot` without a binder, `pEx` and `pAll` over the confined
  sort Bool, `pMatch` with a binder its pattern holds under a constructor.
  - `crossEx`: in any model of `Γ c`, `pEx` at `R` holds at an element of the sort `R` is given iff
    `pEx` at Int holds at an element of Int (`cond_crossAt`, a binder included, no fact about
    confined sorts).
  - `entailsNotR`: the Holds lemma at `R` for `pNot` in any model of `Γc` (`holds_entails_atR`).
  - `modelR`: the Holds lemma at `R` in the value model at any T, at `pNot`, `pEx`, `pAll` and
    `pMatch` (`holdsT_atR`).
  - the variables of `pMatch`'s pattern at Int are variables of its pattern at `R`, decided, and
    by `condKore_varsOf_resort`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace CondResortT

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)
def tt : Term := .dv Srt.bool (.bool true)
def ff : Term := .dv Srt.bool (.bool false)
def tA (t : Term) : Term := .app 385 [t]
def tB : Term := .app 386 []

/-- The counter cell's sort (the second variable of the text's rule). -/
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

def pNot : Cond := .not (.and (.mem 32 (.var 0) (tA tB)) (.mem 32 (.var 0) (.var 1)))
def pEx : Cond := .ex Srt.bool (.equals Srt.bool (.var 1) tt)
def pAll : Cond := .all Srt.bool (.or (.mem Srt.bool (.var 0) tt) (.mem Srt.bool (.var 0) ff))
noncomputable def pMatch : Cond := .exMatch [Srt.int] sC (.app 73 [.var 1]) (.var 0) .top

theorem coreOK : c.coreOK = true := by decide_cheap

theorem conds_ok :
    (c.condOK [32, 32] pNot = true ∧ Cond.bound c 2 pNot = true) ∧
    (c.condOK [Srt.int] pEx = true ∧ Cond.bound c 1 pEx = true) ∧
    (c.condOK [] pAll = true ∧ Cond.bound c 0 pAll = true) ∧
    (c.condOK [sC] pMatch = true ∧ Cond.bound c 1 pMatch = true) := by
  decide +kernel

/-! ## In every model of `Γ c` and of `Γc` -/

section
open ML Faithful Faithful.Model HoldsShape

/-- `cond_crossAt` at `pEx`, in any model of `Γ c`: no premise about what the binder ranges over. -/
theorem crossEx {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {τS τR : M}
    (hτS : ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (a : M),
      (KoreAML.trSort tbl (srtOf c Srt.int)).interpret I e a ↔ a = τS)
    (hσS : KoreAML.IsSort I τS) (hσR : KoreAML.IsSort I τR)
    {tbl : KoreAML.VarTable} {e : Valuation M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) KoreAML.R pEx), k ∈ tbl)
    (hRm : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hf : ∀ j ∈ varOccsCond 1 pEx, canonKey c [Srt.int] j ∈ tbl ∧
      InS I (c.sortName ([Srt.int].getD j 0)) (e.evalEvar (tbl.ev (canonKey c [Srt.int] j))))
    (hR : e.evalEvar (tbl.ev (.sortVar "R")) = τR) (m m' : M)
    (hm : KoreAML.Inh I τR m) (hm' : KoreAML.Inh I τS m') :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) KoreAML.R pEx)).interpret I e m ↔
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [Srt.int]) (srtOf c Srt.int) pEx)).interpret I e m' := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  exact cond_crossAt (defOK hI) (sat_sigItem hI sig_ceilDef) (fun hs => srt_den hI hs)
    (termsInSort_of_core coreOK hI) hτS hσS hσR pEx conds_ok.2.1.1 hk hRm hf hR m m' hm hm'

/-- `holds_entails_atR` at `pNot`, which holds no binder, in any model of `Γc`: at the sort the
valuation gives `R`, the truth value `Holds` gives. -/
theorem entailsNotR {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hP : ∀ j ∈ varOccsCond 2 pNot, j < 2 → P j) (hr : Reads c I [32, 32] P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [32, 32]) KoreAML.R pNot), k ∈ tbl)
    (hRm : KoreAML.VarKey.sortVar "R" ∈ tbl) {σr : M}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr : KoreAML.IsSort I σr)
    (hh : Holds c 2 σ pNot b) (a : M) (ha : KoreAML.Inh I σr a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c [32, 32]) KoreAML.R pNot)).interpret I e a ↔ b = true :=
  holds_entails_atR coreOK hIc hc pNot (fun hb => absurd hb (by decide +kernel))
    conds_ok.1.1 conds_ok.1.2 hP hr hk hRm hR hσr hh a ha

end

/-! ## In the value model -/

section
open ML Faithful Faithful.Model

variable (hd : FnDet c) (T : GroundTerm → GroundTerm → Prop)

/-- `holdsT_atR` at a condition with its two facts, every other premise explicit. -/
theorem modelR (h : HypModelCore c) (p : Cond) (vars : List Srt) (hok : c.condOK vars p = true)
    (hbd : Cond.bound c vars.length p = true) :
    ∀ (P : Nat → Prop) (σ : Subst) (b : Bool) (tbl : KoreAML.VarTable) (e : Valuation Elem),
      (∀ j ∈ varOccsCond vars.length p, j < vars.length → P j) → ReadsT c vars P σ tbl e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) KoreAML.R p), k ∈ tbl) →
      KoreAML.VarKey.sortVar "R" ∈ tbl →
      KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) →
      Holds c vars.length σ p b →
      ∀ a, KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a →
        ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) KoreAML.R p)).interpret (stdI_T c T) e a ↔ b = true) :=
  fun _ _ _ _ _ hP hr hk hRm hσr hh a ha => holdsT_atR (T := T) h p hok hbd hP hr hk hRm hσr hh a ha

include hd

example := modelR T (hypModel_of_fn coreOK hd) pNot [32, 32] conds_ok.1.1 conds_ok.1.2
example := modelR T (hypModel_of_fn coreOK hd) pEx [Srt.int] conds_ok.2.1.1 conds_ok.2.1.2
example := modelR T (hypModel_of_fn coreOK hd) pAll [] conds_ok.2.2.1.1 conds_ok.2.2.1.2
example := modelR T (hypModel_of_fn coreOK hd) pMatch [sC] conds_ok.2.2.2.1 conds_ok.2.2.2.2

/-- The value model has `TermsInSort`. -/
example : TermsInSort c (stdI_T c T) := termsInSort_stdI (hypModel_of_fn coreOK hd)

end

/-! ## The variables of the two patterns -/

section
open Faithful

example : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [sC]) (srtOf c Srt.int) pMatch),
    k ∈ KoreAML.varsOf (Cond.kore c (canonVars c [sC]) KoreAML.R pMatch) :=
  condKore_varsOf_resort (sortVarsOf_srtOf c Srt.int) pMatch _

/-- The pattern at `R` holds `R`, which the pattern at Int does not. -/
example : KoreAML.VarKey.sortVar "R" ∈ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) KoreAML.R pEx) ∧
    KoreAML.VarKey.sortVar "R" ∉ KoreAML.varsOf (Cond.kore c (canonVars c [Srt.int]) (srtOf c Srt.int) pEx) := by
  decide +kernel

end

end CondResortT

#print axioms CondResortT.crossEx
#print axioms CondResortT.entailsNotR
#print axioms CondResortT.modelR
