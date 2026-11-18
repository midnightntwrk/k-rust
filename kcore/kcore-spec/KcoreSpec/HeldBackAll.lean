/-
  KCore. `HeldBack` in every model of `Γc`, for a set of held symbols.

  `HeldBackAll c H`: in every model of `Γc`, each symbol of H that is no constructor has `HeldBack`
  with the signature a right side's context gives it. It is what the statements over every model
  (`sound_at_heldCEx`, `exact_heldCEx`, `famEx_values_heldCEx`) ask of H. Those statements do not name H:
  where the rules have `rulePlainHeldH` at the symbols `Semantics.holds` names, and those symbols
  have `HeldBackAll` if the definition reads a confined sort, some H has both
  (`heldFacts_of_rules`): a definition that reads no confined sort has no rule with a variable its
  left side leaves open, and its rules have `rulePlainHeldH` at no symbol.
-/
import KcoreSpec.CompetePP
import KcoreSpec.StepValuesHeld

set_option autoImplicit false

namespace KCore

open ML Faithful

/-- In every model of `Γc`, each symbol of H that is no constructor has `HeldBack` with the
signature a right side's context gives it. -/
def HeldBackAll (c : Semantics) (H : Sym → Bool) : Prop :=
  ∀ {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc c →
    ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k

/-- `HeldBackAll` passes to a smaller set of symbols. -/
theorem HeldBackAll.mono {c : Semantics} {H H' : Sym → Bool} (hH : ∀ f, H f = true → H' f = true)
    (hb : HeldBackAll c H') : HeldBackAll c H :=
  fun I hI f k hc hh hk => hb I hI f k hc (hH f hh) hk

/-- A rule whose left side binds each of its variables has `rulePlainHeldH` at every set of
symbols. -/
theorem Semantics.rulePlainHeldH_of_opens_nil {c : Semantics} (H : Sym → Bool) {r : Rule}
    (ho : r.opens = []) : c.rulePlainHeldH H r = true := by
  simp [Semantics.rulePlainHeldH, Rule.reqOpen, Rule.openCondVars, ho]

/-- **Some set of symbols has the rules' facts and `HeldBackAll`**, where the rules have
`rulePlainHeldH` at the symbols `Semantics.holds` names and those symbols have `HeldBackAll` if the
definition reads a confined sort. A definition that reads none has no rule with an open variable,
and the set is the empty one. -/
theorem heldFacts_of_rules {c : Semantics}
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH c.holds r = true)
    (hbk : c.readsConfined = true → HeldBackAll c c.holds) :
    ∃ H : Sym → Bool, (∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) ∧
      HeldBackAll c H := by
  cases hr : c.readsConfined with
  | true => exact ⟨c.holds, hrules, hbk hr⟩
  | false =>
    exact ⟨fun _ => false, fun r hm => ⟨(hrules r hm).1,
      Semantics.rulePlainHeldH_of_opens_nil _ ((Semantics.opens_of_readsConfined hr).1 r hm)⟩,
      fun _ _ _ _ _ hh => Bool.noConfusion hh⟩

end KCore
