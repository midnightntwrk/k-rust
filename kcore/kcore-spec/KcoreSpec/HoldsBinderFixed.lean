/-
  KCore. The Holds lemma over `Cond.boundV` in every model of `Γc` of a definition with `coreOK`,
  under the clause hypothesis of `sound_at` (`holds_entails_fixed`): `holds_den_fixed`
  (HoldsDenFixed.lean) with the atoms' facts of `termSoundEx`.
-/
import KcoreSpec.HoldsDenFixed
import KcoreSpec.TermSoundCEx

set_option autoImplicit false

namespace KCore

open ML Faithful HoldsShape

namespace CE

section HoldsBinderFixed
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The Holds lemma over `Cond.boundV` in every model of `Γc`**: `holds_entailsCEx` with
`Cond.boundV c val` for `Cond.bound c`, `val` true only at sorts with a value (`Cond.bound c` is
the instance at `c.valued`, `Cond.bound_eq_boundV`). -/
theorem holds_entails_fixed (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) : HoldsDenB (Cond.boundV c val) c I p :=
  holds_den_fixed h hIc (atomFacts_of_core h hIc (termSoundEx (Semantics.coreOK_iff_ex.mp h) hIc hc)) hval p hrc

end HoldsBinderFixed

end CE

end KCore
