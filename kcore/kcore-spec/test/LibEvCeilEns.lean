/-
  The library's definedness lemmas over set variables on `f2-examples/ens.kompile.kore`: refuted at
  values, for every interpretation H, and their companions at sets of at most one value, from the
  library's statements (KcoreSpec/LibEvCeil.lean).
  Run from the package root: `lake env lean test/LibEvCeilEns.lean`.

  - 126 (`%Int`, domains.md 1393), 127 (`/Int`, 1392), 130 (`modInt`, 1394):
    `#Ceil(@I1 f @I2) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)`;
    at `@I1 = {0}`, `@I2 = {1, 0}`: `0 f 1` has a value and `0 =/=Int 0` is `false`.
  - 128 (`<<Int`, 1396), 129 (`>>Int`, 1395): the same with `@I2 >=Int 0`;
    at `@I1 = {0}`, `@I2 = {0, -1}`: `0 f 0` has a value and `-1 >=Int 0` is `false`.
  - 266, kompile's lemma `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)`;
    at `@K0 = @K1 = {0}` (the KItem injection of 0), `@Rest = {.Map, 0 |-> 0}`.

  For each sentence `n`: `sn_at` (in every model of Γ the sentence fails at a valuation meeting
  `AtValues` and `SetVarsAtValues`), `sn_refuted` (Γ with it has no model) and `sn_one` (the
  companion: it holds at every valuation at values whose set variables hold at most one element).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvCeilEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

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

theorem t126 : (trS U.ax126).pat = (trAxiom [] [] U.ax126).pat := by decide +kernel
theorem t127 : (trS U.ax127).pat = (trAxiom [] [] U.ax127).pat := by decide +kernel
theorem t128 : (trS U.ax128).pat = (trAxiom [] [] U.ax128).pat := by decide +kernel
theorem t129 : (trS U.ax129).pat = (trAxiom [] [] U.ax129).pat := by decide +kernel
theorem t130 : (trS U.ax130).pat = (trAxiom [] [] U.ax130).pat := by decide +kernel

theorem s126_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax126.ax ∧ SetVarsAtValues (cH H) I e U.ax126.ax ∧
      ¬ (trS U.ax126).pat.interpret I e default := by
  rw [t126]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax126 (by decide +kernel) (by decide +kernel) hI
theorem s127_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax127.ax ∧ SetVarsAtValues (cH H) I e U.ax127.ax ∧
      ¬ (trS U.ax127).pat.interpret I e default := by
  rw [t127]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax127
    (by decide +kernel) (by decide +kernel) hI
theorem s130_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax130.ax ∧ SetVarsAtValues (cH H) I e U.ax130.ax ∧
      ¬ (trS U.ax130).pat.interpret I e default := by
  rw [t130]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax130
    (by decide +kernel) (by decide +kernel) hI
theorem s128_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax128.ax ∧ SetVarsAtValues (cH H) I e U.ax128.ax ∧
      ¬ (trS U.ax128).pat.interpret I e default := by
  rw [t128]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax128
    (by decide +kernel) (by decide +kernel) hI
theorem s129_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax129.ax ∧ SetVarsAtValues (cH H) I e U.ax129.ax ∧
      ¬ (trS U.ax129).pat.interpret I e default := by
  rw [t129]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax129
    (by decide +kernel) (by decide +kernel) hI

theorem s126_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax126).pat) := refuted_of_at (s126_at H)
theorem s127_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax127).pat) := refuted_of_at (s127_at H)
theorem s128_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax128).pat) := refuted_of_at (s128_at H)
theorem s129_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax129).pat) := refuted_of_at (s129_at H)
theorem s130_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax130).pat) := refuted_of_at (s130_at H)

theorem s126_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax126 (trS U.ax126).pat := by
  rw [t126]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax126 (by decide +kernel) (by decide +kernel)
theorem s127_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax127 (trS U.ax127).pat := by
  rw [t127]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax127 (by decide +kernel) (by decide +kernel)
theorem s128_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax128 (trS U.ax128).pat := by
  rw [t128]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax128 (by decide +kernel) (by decide +kernel)
theorem s129_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax129 (trS U.ax129).pat := by
  rw [t129]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax129 (by decide +kernel) (by decide +kernel)
theorem s130_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax130 (trS U.ax130).pat := by
  rw [t130]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax130 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma -/

theorem t266 : (trS U.ax266).pat = (trAxiom [] [] U.ax266).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel

theorem s266_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax266.ax ∧ SetVarsAtValues (cH H) I e U.ax266.ax ∧
      ¬ (trS U.ax266).pat.interpret I e default := by
  rw [t266]
  exact LibEv.ceilMap_refuted_at (coreOKH H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax266 (by decide +kernel) (by decide +kernel) hI

theorem s266_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax266).pat) := refuted_of_at (s266_at H)

theorem s266_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax266 (trS U.ax266).pat := by
  rw [t266]
  exact LibEv.ceilMap_one (coreOKH H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax266 (by decide +kernel) (by decide +kernel)

end KCore.LibEvCeilEns

#check @KCore.LibEv.SvEqn.refuted_at
#check @KCore.LibEv.SvEqn.entailed_one
/-- info: 'KCore.LibEvCeilEns.s126_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s126_refuted
/-- info: 'KCore.LibEvCeilEns.s127_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s127_refuted
/-- info: 'KCore.LibEvCeilEns.s128_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s128_refuted
/-- info: 'KCore.LibEvCeilEns.s129_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s129_refuted
/-- info: 'KCore.LibEvCeilEns.s130_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s130_refuted
/-- info: 'KCore.LibEvCeilEns.s266_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s266_refuted
/-- info: 'KCore.LibEvCeilEns.s126_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s126_one
/-- info: 'KCore.LibEvCeilEns.s127_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s127_one
/-- info: 'KCore.LibEvCeilEns.s128_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s128_one
/-- info: 'KCore.LibEvCeilEns.s129_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s129_one
/-- info: 'KCore.LibEvCeilEns.s130_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s130_one
/-- info: 'KCore.LibEvCeilEns.s266_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilEns.s266_one
