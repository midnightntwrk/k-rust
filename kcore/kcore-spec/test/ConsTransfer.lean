/-
  The transfer of premises to the extension of a model (KcoreSpec/ConsTransfer.lean,
  KcoreSpec/ConsTransferInst.lean): the statements exist as stated and depend on no axiom but
  `propext`, `Classical.choice` and `Quot.sound`. Run from the package root:
  `lake env lean test/ConsTransfer.lean`.
-/
import KcoreSpec.ConsTransferInst

open KCore KCore.Cons ML Faithful

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The embedding clauses hold of the free extension, and it interprets `⌈_⌉` as definedness. -/
example : Function.Injective (Sum.inl : M → Ext M) ∧
    (∀ σ, ¬ D σ → ∀ m, (Sum.inl m : Ext M) ∈ (extModel c D I).evalSymb σ ↔ m ∈ I.evalSymb σ) ∧
    (∀ a b m, (Sum.inl m : Ext M) ∈ (extModel c D I).evalApp (.inl a) (.inl b) ↔ m ∈ I.evalApp a b) :=
  ext_embeds c D I

example : KoreAML.DefOK (extModel c D I) := ext_defOK c D I

/-- Application of old elements gives no added element, whatever symbols the elements are in. -/
example (a b : M) (n : Added M) : ¬ (extModel c D I).evalApp (.inl a) (.inl b) (.inr n) := app_inl_inl_inr

example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) {gs : List (EVar × KoreAML.P)}
    (hs : ∀ p ∈ gs, OwnSorted D [] [] .ex p.2) {body : KoreAML.P} {k : OwnKind}
    (hb : OwnSorted D (gs.map (·.1)) [] k body) (hk : k = .pred ∨ k = .co)
    (h : I ⊧ᴵ KoreAML.guarded (memGs gs) body) : extModel c D I ⊧ᴵ KoreAML.guarded (memGs gs) body :=
  transfer hD hI hs hb hk h

example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) {gs : List (EVar × KoreAML.P)}
    (hs : ∀ p ∈ gs, OwnSorted D [] [] .ex p.2) {body : KoreAML.P} {k : OwnKind}
    (hb : OwnSorted D (gs.map (·.1)) [] k body)
    (h : extModel c D I ⊧ᴵ KoreAML.guarded (memGs gs) body) : I ⊧ᴵ KoreAML.guarded (memGs gs) body :=
  transfer_back hD hI hs hb h

/-- A no-junk item (`μ`). -/
example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) (k : CollSig)
    (hs : ¬ D (.sort ("Sort" ++ c.sortName k.sort))) (hkey : ¬ D (.sort ("Sort" ++ c.sortName k.key)))
    (hval : ¬ D (.sort ("Sort" ++ c.sortName (valSort k))))
    (hu : ¬ D (.symbol (c.symName k.unit))) (he : ¬ D (.symbol (c.symName k.elem)))
    (hc : ¬ D (.symbol (c.symName k.concat))) (h : I ⊧ᴵ collNoJunk c k) :
    extModel c D I ⊧ᴵ collNoJunk c k :=
  transfer_collNoJunk hD hI k hs hkey hval hu he hc h

/-- An equation with its sort variable. -/
example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) (k : ParamSig)
    (hn : ¬ D (.sort ("Sort" ++ c.sortName k.sig.result))) (hf : ¬ D (.symbol (c.symName k.sig.name)))
    (hSs : ∃ σ, KoreAML.IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName k.sig.result)) a ↔ a = σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩).pat :=
  transfer_idem hD hI hc k hn hf hSs h

end

/-- info: 'KCore.Cons.ext_embeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.ext_embeds
/-- info: 'KCore.Cons.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer
/-- info: 'KCore.Cons.transfer_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_back
/-- info: 'KCore.Cons.transfer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_equation
/-- info: 'KCore.Cons.transfer_collNoJunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_collNoJunk
/-- info: 'KCore.Cons.transfer_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_idem
