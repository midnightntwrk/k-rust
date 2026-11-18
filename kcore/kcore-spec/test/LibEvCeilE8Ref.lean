/-
  The six definedness lemmas over set variables that `--disable-ceil-simplification-rules` removes,
  on `f2-examples/e8-ref.kompile.kore` (the text of fixture e8-ref, kompiled with R-12's options):
  refuted at values, for every interpretation H, and their companions at sets of at most one value,
  from the library's statements (KcoreSpec/LibEvCeil.lean). They are the tie class set-variable
  lemma (direction refuted) of `tieClasses`. The text of fixture e8-disable-ceil-simplification-rules
  holds the other sentences of e8-ref's user module and none of these six.
  Run from the package root: `lake env lean test/LibEvCeilE8Ref.lean`.

  - 153 (`%Int`, domains.md 1393), 154 (`/Int`, 1392), 157 (`modInt`, 1394):
    `#Ceil(@I1 f @I2) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)`;
    at `@I1 = {0}`, `@I2 = {1, 0}`: `0 f 1` has a value and `0 =/=Int 0` is `false`.
  - 155 (`<<Int`, 1396), 156 (`>>Int`, 1395): the same with `@I2 >=Int 0`;
    at `@I1 = {0}`, `@I2 = {0, -1}`: `0 f 0` has a value and `-1 >=Int 0` is `false`.
  - 312, kompile's lemma `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)`;
    at `@K0 = @K1 = {0}` (the KItem injection of 0), `@Rest = {.Map, 0 |-> 0}`.

  For each sentence `n`: `sn_at` (in every model of Γ the sentence fails at a valuation meeting
  `AtValues` and `SetVarsAtValues`), `sn_refuted` (Γ with it has no model) and `sn_one` (the
  companion: it holds at every valuation at values whose set variables hold at most one element).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvCeilE8Ref

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e8-ref.kompile.kore"
definition_of defn from "f2-examples/e8-ref.kompile.kore"
user_axioms U from "f2-examples/e8-ref.kompile.kore" module "REF"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- What a refutation at values gives: Γ with the sentence has no model. -/
theorem refuted_of_at {c' : Semantics} {ad : AxiomDecl} {φ : KoreAML.P}
    (hat : ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' →
      ∃ e : Valuation M, AtValues c' I e ad.ax ∧ SetVarsAtValues c' I e ad.ax ∧ ¬ φ.interpret I e default) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' → ¬ (I ⊧ᴵ φ) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := hat M I hI
  exact hn (hax e default)

/-! ## The Int lemmas -/

theorem t153 : (trS U.ax153).pat = (trAxiom [] [] U.ax153).pat := by decide +kernel
theorem t154 : (trS U.ax154).pat = (trAxiom [] [] U.ax154).pat := by decide +kernel
theorem t155 : (trS U.ax155).pat = (trAxiom [] [] U.ax155).pat := by decide +kernel
theorem t156 : (trS U.ax156).pat = (trAxiom [] [] U.ax156).pat := by decide +kernel
theorem t157 : (trS U.ax157).pat = (trAxiom [] [] U.ax157).pat := by decide +kernel

theorem s153_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax153.ax ∧ SetVarsAtValues (cH H) I e U.ax153.ax ∧
      ¬ (trS U.ax153).pat.interpret I e default := by
  rw [t153]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax153 (by decide +kernel) (by decide +kernel) hI
theorem s154_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax154.ax ∧ SetVarsAtValues (cH H) I e U.ax154.ax ∧
      ¬ (trS U.ax154).pat.interpret I e default := by
  rw [t154]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax154
    (by decide +kernel) (by decide +kernel) hI
theorem s157_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax157.ax ∧ SetVarsAtValues (cH H) I e U.ax157.ax ∧
      ¬ (trS U.ax157).pat.interpret I e default := by
  rw [t157]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax157
    (by decide +kernel) (by decide +kernel) hI
theorem s155_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax155.ax ∧ SetVarsAtValues (cH H) I e U.ax155.ax ∧
      ¬ (trS U.ax155).pat.interpret I e default := by
  rw [t155]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax155
    (by decide +kernel) (by decide +kernel) hI
theorem s156_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax156.ax ∧ SetVarsAtValues (cH H) I e U.ax156.ax ∧
      ¬ (trS U.ax156).pat.interpret I e default := by
  rw [t156]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax156
    (by decide +kernel) (by decide +kernel) hI

theorem s153_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax153).pat) := refuted_of_at (s153_at H)
theorem s154_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax154).pat) := refuted_of_at (s154_at H)
theorem s155_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax155).pat) := refuted_of_at (s155_at H)
theorem s156_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax156).pat) := refuted_of_at (s156_at H)
theorem s157_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax157).pat) := refuted_of_at (s157_at H)

theorem s153_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax153 (trS U.ax153).pat := by
  rw [t153]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax153 (by decide +kernel) (by decide +kernel)
theorem s154_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax154 (trS U.ax154).pat := by
  rw [t154]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax154 (by decide +kernel) (by decide +kernel)
theorem s155_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax155 (trS U.ax155).pat := by
  rw [t155]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax155 (by decide +kernel) (by decide +kernel)
theorem s156_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax156 (trS U.ax156).pat := by
  rw [t156]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax156 (by decide +kernel) (by decide +kernel)
theorem s157_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax157 (trS U.ax157).pat := by
  rw [t157]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax157 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma -/

theorem t312 : (trS U.ax312).pat = (trAxiom [] [] U.ax312).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel

theorem s312_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax312.ax ∧ SetVarsAtValues (cH H) I e U.ax312.ax ∧
      ¬ (trS U.ax312).pat.interpret I e default := by
  rw [t312]
  exact LibEv.ceilMap_refuted_at (coreOKH H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax312 (by decide +kernel) (by decide +kernel) hI

theorem s312_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax312).pat) := refuted_of_at (s312_at H)

theorem s312_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax312 (trS U.ax312).pat := by
  rw [t312]
  exact LibEv.ceilMap_one (coreOKH H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax312 (by decide +kernel) (by decide +kernel)

end KCore.LibEvCeilE8Ref

#check @KCore.LibEv.SvEqn.refuted_at
#check @KCore.LibEv.SvEqn.entailed_one
/-- info: 'KCore.LibEvCeilE8Ref.s153_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s153_refuted
/-- info: 'KCore.LibEvCeilE8Ref.s154_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s154_refuted
/-- info: 'KCore.LibEvCeilE8Ref.s155_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s155_refuted
/-- info: 'KCore.LibEvCeilE8Ref.s156_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s156_refuted
/-- info: 'KCore.LibEvCeilE8Ref.s157_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s157_refuted
/-- info: 'KCore.LibEvCeilE8Ref.s312_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s312_refuted
/-- info: 'KCore.LibEvCeilE8Ref.s153_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s153_one
/-- info: 'KCore.LibEvCeilE8Ref.s154_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s154_one
/-- info: 'KCore.LibEvCeilE8Ref.s155_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s155_one
/-- info: 'KCore.LibEvCeilE8Ref.s156_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s156_one
/-- info: 'KCore.LibEvCeilE8Ref.s157_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s157_one
/-- info: 'KCore.LibEvCeilE8Ref.s312_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilE8Ref.s312_one
