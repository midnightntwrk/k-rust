/-
  A projection's pattern, functional and injective in every model of `Γ`, on construct fixture
  e7-projuser (`f2-examples/e7-projuser.kompile.kore`, `test/constructs/fixtures/e7-projuser`).
  Run from the package root: `lake env lean -j1 test/ProjPatInj.lean`.
  - The text states `project:Cmd`'s equation at `kseq(inj{Cmd,KItem}(K), dotk)`, and Γ has no
    symbol `project:Cmd`. Cmd is below KItem and K and KItem are constructor sorts (decided by the
    kernel), so in every interpretation that satisfies `Γ c` the pattern is one element of K at
    each element of Cmd (`cmd_fun`) and different elements at different ones (`cmd_inj`).
  - `projBelowB c "Cmd"` holds, and so do `projBelowB c "K"` and `projBelowB c "KItem"`; the
    pattern of Cmd's projection as `projSelPat` gives it is functional and injective through
    `projSel_fun`, `projSel_inj` (`cmd_sel_fun`, `cmd_sel_inj`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore ML Faithful

namespace ProjPatInj

definition_of defn from "f2-examples/e7-projuser.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The sort Cmd of the definition. -/
noncomputable def cmd : Srt := nRegSorts + c.sortNames.idxOf "Cmd"

theorem cmd_name : c.sortName cmd = "Cmd" := by decide +kernel

theorem cmd_below : (cmd, Srt.kitem) ∈ c.subsorts := by decide +kernel

theorem k_cons : Srt.k ∈ consSorts c := by decide +kernel

theorem kitem_cons : Srt.kitem ∈ consSorts c := by decide +kernel

theorem cmd_projBelow : GenEqs.projBelowB c "Cmd" = true := by decide +kernel

theorem k_projBelow : GenEqs.projBelowB c "K" = true := by decide +kernel

theorem kitem_projBelow : GenEqs.projBelowB c "KItem" = true := by decide +kernel

/-- `kseq(inj{Cmd,KItem}(v), dotk)` is one element of K at each element `v` of Cmd. -/
theorem cmd_fun {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {e : Valuation M} {φ : KoreAML.P} {v : M} (hφ : ∀ m, φ.interpret I e m ↔ m = v)
    (hv : Faithful.InS I (c.sortName cmd) v) :
    ∃ y, Faithful.InS I (c.sortName Srt.k) y ∧
      ∀ m, (GenEqs.projInjPat c (c.sortName cmd) φ).interpret I e m ↔ m = y :=
  GenEqs.projPat_fun hI cmd_below k_cons kitem_cons hφ hv

/-- `kseq(inj{Cmd,KItem}(v), dotk)` and `kseq(inj{Cmd,KItem}(v'), dotk)` at elements of Cmd are
the same only where `v = v'`. -/
theorem cmd_inj {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {e e' : Valuation M} {φ φ' : KoreAML.P} {v v' : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hφ' : ∀ m, φ'.interpret I e' m ↔ m = v')
    (hv : Faithful.InS I (c.sortName cmd) v) (hv' : Faithful.InS I (c.sortName cmd) v')
    (heq : ∀ m, (GenEqs.projInjPat c (c.sortName cmd) φ).interpret I e m ↔
      (GenEqs.projInjPat c (c.sortName cmd) φ').interpret I e' m) : v = v' :=
  GenEqs.projPat_inj hI cmd_below k_cons kitem_cons hφ hφ' hv hv' heq

theorem cmd_sel_fun {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {e : Valuation M} {φ : KoreAML.P} {v : M} (hφ : ∀ m, φ.interpret I e m ↔ m = v)
    (hv : Faithful.InS I "Cmd" v) :
    ∃ y, Faithful.InS I "K" y ∧ ∀ m, (GenEqs.projSelPat c "Cmd" φ).interpret I e m ↔ m = y :=
  GenEqs.projSel_fun hI cmd_projBelow hφ hv

theorem cmd_sel_inj {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {e e' : Valuation M} {φ φ' : KoreAML.P} {v v' : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hφ' : ∀ m, φ'.interpret I e' m ↔ m = v')
    (hv : Faithful.InS I "Cmd" v) (hv' : Faithful.InS I "Cmd" v')
    (heq : ∀ m, (GenEqs.projSelPat c "Cmd" φ).interpret I e m ↔
      (GenEqs.projSelPat c "Cmd" φ').interpret I e' m) : v = v' :=
  GenEqs.projSel_inj hI cmd_projBelow hφ hφ' hv hv' heq

end ProjPatInj

#check @KCore.GenEqs.projPat_fun
#check @KCore.GenEqs.projPat_inj
#check @KCore.GenEqs.projItemPat_fun
#check @KCore.GenEqs.projItemPat_inj
#check @KCore.GenEqs.projBelowB
#check @KCore.GenEqs.projBelowB_spec
#check @KCore.GenEqs.projSel_fun
#check @KCore.GenEqs.projSel_inj
#check @ProjPatInj.cmd_fun
#check @ProjPatInj.cmd_inj
#check @ProjPatInj.cmd_sel_fun
#check @ProjPatInj.cmd_sel_inj
#print axioms ProjPatInj.cmd_inj
#print axioms ProjPatInj.cmd_sel_inj
