/-
  The extension of a model of the theory without the detached names satisfies the constructors'
  premises that name nothing of `D`, and with them every premise of the signature, the constructors
  and the collections that names nothing of `D` (KcoreSpec/ConsTransferCons.lean): the statements
  exist as stated and depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`. Run
  from the package root: `lake env lean test/ConsTransferCons.lean`.
-/
import KcoreSpec.ConsTransferCons

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hlaw : ∀ p ∈ c.params, p.raw = true →
      ¬ D (.sort ("Sort" ++ c.sortName p.sig.result)) ∧ ¬ D (.symbol (c.symName p.sig.name)) ∧
      ∃ σ, KoreAML.IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName p.sig.result)) a ↔ a = σ) (hI : I ⊧ᴵP Γown c D)
    {φ : KoreAML.P} (hφ : ΓCons c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ :=
  sat_own_cons hD hlaw hI hφ hn

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hlaw : ∀ p ∈ c.params, p.raw = true →
      ¬ D (.sort ("Sort" ++ c.sortName p.sig.result)) ∧ ¬ D (.symbol (c.symName p.sig.name)) ∧
      ∃ σ, KoreAML.IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName p.sig.result)) a ↔ a = σ) (hI : I ⊧ᴵP Γown c D)
    {φ : KoreAML.P} (hφ : ΓSig c φ ∨ ΓCons c φ ∨ ΓColls c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) :
    extModel c D I ⊧ᴵ φ :=
  sat_own_sig_cons hD hlaw hI hφ hn

/-- The items at uncovered arguments and the no-junk item hold without the definition's facts. -/
example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hDI : KoreAML.DefOK I) (N : String) (g g' : KoreAML.Gen)
    (ug ug' : Option (List (List String))) (gs : List KoreAML.Gen)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.distUncItem N g g' ug ug').pat, ¬ D σ)
    (h : I ⊧ᴵ (KoreAML.Cons.distUncItem N g g' ug ug').pat)
    (hn' : ∀ σ ∈ psyms (KoreAML.Cons.noJunkItem N gs).pat, ¬ D σ)
    (h' : I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat) :
    (extModel c D I ⊧ᴵ (KoreAML.Cons.distUncItem N g g' ug ug').pat) ∧
      (extModel c D I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat) :=
  ⟨sat_distUnc_cs hD hDI N g g' ug ug' hn h, sat_noJunk_cs hD hDI N gs hn' h'⟩

/-- info: 'KCore.Cons.sat_own_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_cons

/-- info: 'KCore.Cons.sat_own_sig_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_sig_cons
