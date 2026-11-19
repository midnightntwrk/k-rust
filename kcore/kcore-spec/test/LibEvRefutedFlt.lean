/-
  The classes set idempotence and set-variable lemma on `f2-examples/silentflt.kompile.kore`
  (FLOAT, STRING, BYTES and SET imported, user module `SILENTFLT`): each sentence refuted, for every
  interpretation H, from the library's statements (KcoreSpec/SetIdemColl.lean,
  KcoreSpec/LibEvCeil.lean). Run from the package root: `lake env lean -j1 test/LibEvRefutedFlt.lean`.

  - Set idempotence, 87 (`_Set_(K, K) = K`): `setIdemTextOK` decides that the sentence is the
    idempotence sentence of the set collection `_Set_`, whose key sort has a value, so Γ with it has
    no model (`idem_refuted`, `setColl_idem_refuted_text`).
  - Set-variable lemmas: 196 (`%Int`, domains.md 1393), 197 (`/Int`, 1392), 200 (`modInt`, 1394):
    `#Ceil(@I1 f @I2) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)`, at
    `@I1 = {0}`, `@I2 = {1, 0}`: `0 f 1` has a value and `0 =/=Int 0` is `false`; 198 (`<<Int`,
    1396), 199 (`>>Int`, 1395), the same with `@I2 >=Int 0`, at `@I1 = {0}`, `@I2 = {0, -1}`: `0 f 0`
    has a value and `-1 >=Int 0` is `false`; 381, kompile's lemma
    `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)`, at
    `@K0 = @K1 = {0}` (the KItem injection of 0), `@Rest = {.Map, 0 |-> 0}`. For each sentence `n`:
    `sn_at` (in every model of Γ the sentence fails at a valuation meeting `AtValues` and
    `SetVarsAtValues`), `sn_refuted` (Γ with it has no model) and `sn_one` (it holds at every
    valuation at values whose set variables hold at most one element).

  These are the sentences test/LibEvClassesFlt.lean leaves out of the classes hooked functional,
  collection law and library.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvRefutedFlt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-! ## Set idempotence (87) -/

theorem idem_ok : setIdemTextOK c "Lbl'Unds'Set'Unds'" "K" U.ax87 = true := by decide +kernel
theorem idem_trS : (trS U.ax87).pat = (trAxiom [] [] U.ax87).pat := by decide +kernel

/-- **Sentence 87 is refuted, for every H**: Γ with it has no model. -/
theorem idem_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax87).pat) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  intro M hM I hI hax
  rw [idem_trS] at hax
  exact setColl_idem_refuted_text c H idem_ok M hM I hI hax

/-! ## The set-variable lemmas -/

/-- What a refutation at values gives: Γ with the sentence has no model. -/
theorem refuted_of_at {c' : Semantics} {ad : AxiomDecl} {φ : KoreAML.P}
    (hat : ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' →
      ∃ e : Valuation M, AtValues c' I e ad.ax ∧ SetVarsAtValues c' I e ad.ax ∧ ¬ φ.interpret I e default) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' → ¬ (I ⊧ᴵ φ) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := hat M I hI
  exact hn (hax e default)

theorem t196 : (trS U.ax196).pat = (trAxiom [] [] U.ax196).pat := by decide +kernel
theorem t197 : (trS U.ax197).pat = (trAxiom [] [] U.ax197).pat := by decide +kernel
theorem t198 : (trS U.ax198).pat = (trAxiom [] [] U.ax198).pat := by decide +kernel
theorem t199 : (trS U.ax199).pat = (trAxiom [] [] U.ax199).pat := by decide +kernel
theorem t200 : (trS U.ax200).pat = (trAxiom [] [] U.ax200).pat := by decide +kernel

theorem s196_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax196.ax ∧ SetVarsAtValues (cH H) I e U.ax196.ax ∧
      ¬ (trS U.ax196).pat.interpret I e default := by
  rw [t196]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax196 (by decide +kernel) (by decide +kernel) hI
theorem s197_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax197.ax ∧ SetVarsAtValues (cH H) I e U.ax197.ax ∧
      ¬ (trS U.ax197).pat.interpret I e default := by
  rw [t197]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax197
    (by decide +kernel) (by decide +kernel) hI
theorem s200_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax200.ax ∧ SetVarsAtValues (cH H) I e U.ax200.ax ∧
      ¬ (trS U.ax200).pat.interpret I e default := by
  rw [t200]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax200
    (by decide +kernel) (by decide +kernel) hI
theorem s198_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax198.ax ∧ SetVarsAtValues (cH H) I e U.ax198.ax ∧
      ¬ (trS U.ax198).pat.interpret I e default := by
  rw [t198]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax198
    (by decide +kernel) (by decide +kernel) hI
theorem s199_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax199.ax ∧ SetVarsAtValues (cH H) I e U.ax199.ax ∧
      ¬ (trS U.ax199).pat.interpret I e default := by
  rw [t199]
  exact LibEv.ceilInt_refuted_at (coreOKH H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax199
    (by decide +kernel) (by decide +kernel) hI

theorem s196_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax196).pat) := refuted_of_at (s196_at H)
theorem s197_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax197).pat) := refuted_of_at (s197_at H)
theorem s198_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax198).pat) := refuted_of_at (s198_at H)
theorem s199_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax199).pat) := refuted_of_at (s199_at H)
theorem s200_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax200).pat) := refuted_of_at (s200_at H)

theorem s196_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax196 (trS U.ax196).pat := by
  rw [t196]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax196 (by decide +kernel) (by decide +kernel)
theorem s197_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax197 (trS U.ax197).pat := by
  rw [t197]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax197 (by decide +kernel) (by decide +kernel)
theorem s198_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax198 (trS U.ax198).pat := by
  rw [t198]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax198 (by decide +kernel) (by decide +kernel)
theorem s199_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax199 (trS U.ax199).pat := by
  rw [t199]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax199 (by decide +kernel) (by decide +kernel)
theorem s200_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax200 (trS U.ax200).pat := by
  rw [t200]
  exact LibEv.ceilInt_one (coreOKH H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax200 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma (381) -/

theorem t381 : (trS U.ax381).pat = (trAxiom [] [] U.ax381).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel

theorem s381_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax381.ax ∧ SetVarsAtValues (cH H) I e U.ax381.ax ∧
      ¬ (trS U.ax381).pat.interpret I e default := by
  rw [t381]
  exact LibEv.ceilMap_refuted_at (coreOKH H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax381 (by decide +kernel) (by decide +kernel) hI

theorem s381_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax381).pat) := refuted_of_at (s381_at H)

theorem s381_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax381 (trS U.ax381).pat := by
  rw [t381]
  exact LibEv.ceilMap_one (coreOKH H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax381 (by decide +kernel) (by decide +kernel)

/-- The sentences refuted here: set idempotence, then the six set-variable lemmas. -/
theorem refuted_indices : [U.ax87, U.ax196, U.ax197, U.ax198, U.ax199, U.ax200, U.ax381].map (·.index) =
    [87, 196, 197, 198, 199, 200, 381] := by decide +kernel

end KCore.LibEvRefutedFlt

/-- info: 'KCore.LibEvRefutedFlt.idem_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.idem_refuted
/-- info: 'KCore.LibEvRefutedFlt.s196_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s196_refuted
/-- info: 'KCore.LibEvRefutedFlt.s197_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s197_refuted
/-- info: 'KCore.LibEvRefutedFlt.s198_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s198_refuted
/-- info: 'KCore.LibEvRefutedFlt.s199_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s199_refuted
/-- info: 'KCore.LibEvRefutedFlt.s200_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s200_refuted
/-- info: 'KCore.LibEvRefutedFlt.s381_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s381_refuted
/-- info: 'KCore.LibEvRefutedFlt.s196_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s196_one
/-- info: 'KCore.LibEvRefutedFlt.s197_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s197_one
/-- info: 'KCore.LibEvRefutedFlt.s198_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s198_one
/-- info: 'KCore.LibEvRefutedFlt.s199_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s199_one
/-- info: 'KCore.LibEvRefutedFlt.s200_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s200_one
/-- info: 'KCore.LibEvRefutedFlt.s381_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRefutedFlt.s381_one
