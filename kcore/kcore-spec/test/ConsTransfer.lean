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

/-- The associativity sentence of an open generator. -/
example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) (k : ParamSig)
    (hn : ¬ D (.sort ("Sort" ++ c.sortName k.sig.result))) (hf : ¬ D (.symbol (c.symName k.sig.name)))
    (hSs : ∃ σ, KoreAML.IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName k.sig.result)) a ↔ a = σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩).pat :=
  transfer_assoc hD hI hc k hn hf hSs h

/-- A sentence at its sort variable. -/
example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat)
    {O : String → Prop}
    (hO : ∀ N, O N → ¬ D (.sort N) ∧ ∃ σ, KoreAML.IsSort I σ ∧ ∀ a, I.evalSymb (.sort N) a ↔ a = σ)
    {R : EVar} (hRt : R ≠ KoreAML.topVar) (hne : ∃ τ, KoreAML.IsSort I τ ∧ ∃ m, KoreAML.Inh I τ m)
    {G : List (EVar × String)} (hG : ∀ p ∈ G, ¬ D (.sort p.2)) (hR : R ∉ G.map (·.1)) {π : KoreAML.P}
    (hπ : RPred D O R G π)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.sortGuard R :: memGs (G.map fun p => (p.1, KoreAML.sym (.sort p.2))))
      (π ≡ KoreAML.inhOf (.evar R))) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.sortGuard R :: memGs (G.map fun p => (p.1, KoreAML.sym (.sort p.2))))
      (π ≡ KoreAML.inhOf (.evar R)) :=
  transfer_R hD hI hc hO hRt hne hG hR hπ h

/-- A function equation with its sort variable: the equation of the clause `f(A) = A`. -/
example (hD : ∀ σ, D σ → plainSym σ) (hI : KoreAML.DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat)
    (hne : ∃ τ, KoreAML.IsSort I τ ∧ ∃ m, KoreAML.Inh I τ m) (f s : String)
    (hn : ¬ D (.sort ("Sort" ++ s))) (hf : ¬ D (.symbol f))
    (hSs : ∃ σ, KoreAML.IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ s)) a ↔ a = σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := fnEqIdPat f s, attributes := [] }⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := fnEqIdPat f s, attributes := [] }⟩).pat :=
  transfer_fnEq hD hI hc hne f s hn hf hSs h

end

/-- `fnEqIdPat` is the pattern `equationAx` writes for a clause with one argument pattern, a
variable, that variable as right side, no `requires` and no `ensures`. -/
example (f s : String) :
    KoreAML.equationAx f [s] s (premise [s] none [KoreAML.ev "VarA" (KoreAML.srt s)])
      (KoreAML.ev "VarA" (KoreAML.srt s)) (.top (KoreAML.srt s)) [] =
    .axiom { sortVars := [KoreAML.Rv], pattern := fnEqIdPat f s, attributes := [] } := rfl

/-- A quantifier at the sort variable `R` may bind one of the free variables: `∃x:N. ⊤_R` where `x`
is free at the sort `N'`. -/
example {D : KoreAML.Sym → Prop} {O : String → Prop} {R x : EVar} {N N' : String} (hN : O N) (hx : x ≠ R) :
    RPred D O R [(x, N')] (KoreAML.sExists x (KoreAML.sym (.sort N)) (KoreAML.sTop (.evar R))) :=
  .ex hN hx .top

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
/-- info: 'KCore.Cons.transfer_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_R
/-- info: 'KCore.Cons.transfer_fnEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_fnEq

/-- info: 'KCore.Cons.transfer_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.transfer_assoc
