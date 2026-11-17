/-
  KCore. `HeldBack` in every model of `Γc`, for a set of held symbols.

  `HeldBackAll c H`: in every model of `Γc`, each symbol of H that is no constructor has `HeldBack`
  with the signature a right side's context gives it. It is what the statements over every model
  (`sound_at_held`, `exact_held`, `famEx_values_held`) ask of H. The symbols `Semantics.holds`
  names have it under `coreOK` (`heldBackAll_holds`, by `collHeld_back`).
-/
import KcoreSpec.CompeteHeld

set_option autoImplicit false

namespace KCore

open ML Faithful

/-- In every model of `Γc`, each symbol of H that is no constructor has `HeldBack` with the
signature a right side's context gives it. -/
def HeldBackAll (c : Semantics) (H : Sym → Bool) : Prop :=
  ∀ {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc c →
    ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k

/-- The symbols `Semantics.holds` names have `HeldBack` in every model of `Γc`. -/
theorem heldBackAll_holds {c : Semantics} (h : c.coreOK = true) : HeldBackAll c c.holds := by
  intro M _ I hI f k hc hh hk
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  exact collHeld_back (fun φ hφ => hI φ (Or.inl hφ)) hg hsc.trans hph hcs hcso hc hh hk

/-- `HeldBackAll` passes to a smaller set of symbols. -/
theorem HeldBackAll.mono {c : Semantics} {H H' : Sym → Bool} (hH : ∀ f, H f = true → H' f = true)
    (hb : HeldBackAll c H') : HeldBackAll c H :=
  fun I hI f k hc hh hk => hb I hI f k hc (hH f hh) hk

end KCore
