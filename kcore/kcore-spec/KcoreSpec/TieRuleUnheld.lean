/-
  KCore, outside the cone: a rewrite axiom of the text with a variable that Γ's item of a rule read
  from it does not hold, in the direction from the text to Γ's item (W1). For a tie file where the
  reader drops a variable of a sort with an exhibited value: a left-side `\exists` whose body does
  not hold its variable (`existsAsVariable`), and a disjunct of a left-side `\or` that does not hold
  a variable of the axiom (`orSplit`).

  The sentence states its rewrite for every element of the variable's sort; Γ's item states it
  without the variable. The first entails the second where the sort has an element, and only
  there: at a sort without one the sentence's guard never holds and it states nothing. The element
  is a premise of each lemma (`InS I n a`), which a tie file takes from the item of `ΓDomains` for a
  value of the sort (`elem_of_value`).

  - `drop_var`: the item of `\rewrites{C}(L, r)` with the guards of `fT` entails the item with the
    guards of `fG`, where `fT` is `fG` and the variable x, x is free in no guard of `fG` and not in
    the rewrite, and x's sort has an element.
  - `rule_w1_drop`: the same from a sentence's translation that is the first item up to the indices
    of its variables, to `trAxiom` of Γ's axiom (as `TieRuleLhs.rule_w1`, whose free variables of
    the text's form are all Γ's).
  - `sub_exists_unheld`: `φ` is in `\exists x. φ` where x is not free in `φ` and x's sort has an
    element.
  - `app1_inh`: what a symbol of one argument builds from an element of its argument sort is in its
    result sort (`ΓSig`'s arity item), so that a disjunct `f(X)` is in `\or{S}(f(X), _)`.
-/
import KcoreSpec.TieRuleLhs

set_option autoImplicit false

namespace KCore

namespace TieRuleUnheld

open ML Faithful KoreAML

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern in which x is not free denotes the same where x's value is changed. -/
theorem interp_upd_unheld {ψ : P} {e : Valuation M} {x : EVar} {a : M} (h : ψ.isFreeEvar x = false) (m : M) :
    ψ.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ↔ ψ.interpret I e m :=
  @only_free_var_relevant KoreAML.Sym M I ψ (Function.update e.evalEvar x a) e.evalEvar e.evalSvar e.evalSvar
    (fun y hy => by
      by_cases hxy : y = x
      · subst hxy; rw [h] at hy; cases hy
      · simp [Function.update, hxy])
    (fun _ _ => rfl) m

/-- **A value of the sort `s` gives an element of `s`**, in a model of the domains. -/
theorem elem_of_value [Inhabited M] (hD : DefOK I) {c : Semantics} (hDom : I ⊧ᴵP ΓDomains c) {v : GroundTerm}
    {s : Srt} (hv : c.sortOf v = some s) {n : String} (hn : c.sortName s = n) : ∃ a, InS I n a := by
  obtain ⟨a, -, h2⟩ := TieRhs.den_single_dom hD hDom hv KoreAML.val0
  rw [hn] at h2
  exact ⟨a, h2⟩

/-- **The rule axiom without a variable its sides do not hold.** The item of `\rewrites{C}(L, r)`
with the guards of `fT` holds in `I`; `fT` is `fG` and the variable x of the sort n, which is free
in no guard of `fG` and not in the rewrite; the sort n has an element. Then the item with the
guards of `fG` holds at every valuation. -/
theorem drop_var [Inhabited M] (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort}
    {L r : Kore.Pattern} {x : Kore.EVar} {n : String} (hx : x.sort = KoreAML.srt n)
    (h : I ⊧ᴵ TieRuleLhs.itemAt t fT C L r) (hT : ∀ k ∈ fT, k = evarKey x ∨ k ∈ fG)
    (hbody : (tr ⟨t, []⟩ (.rewrites C L r) ≡ inhOf (trSort t C)).isFreeEvar (t.ev (evarKey x)) = false)
    (hgd : ∀ k ∈ fG, (guardOf t k).isFreeEvar (t.ev (evarKey x)) = false)
    (hex : ∃ a, InS I n a) (e : Valuation M) (m : M) :
    (TieRuleLhs.itemAt t fG C L r).interpret I e m := by
  obtain ⟨a, ha⟩ := hex
  have h1 := h ⟨Function.update e.evalEvar (t.ev (evarKey x)) a, e.evalSvar⟩ m
  unfold TieRuleLhs.itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  refine (interp_upd_unheld hbody m).mp (h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => ?_))
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
  rcases hT k hk with rfl | hk'
  · rw [TieRuleLhs.guard_evarKey hD, hx, trSort_srt]
    exact (inS_iff _).mpr (by
      show InS I n (Function.update e.evalEvar (t.ev (evarKey x)) a (t.ev (evarKey x)))
      rw [Function.update_same]; exact ha)
  · exact (interp_upd_unheld (hgd k hk') m).mpr (hg _ (List.mem_map_of_mem hk'))

/-- **`φ` is in `\exists x. φ`**, where x is not free in `φ` and x's sort n has an element. -/
theorem sub_exists_unheld [Inhabited M] (hD : DefOK I) {t : VarTable} {x : Kore.EVar} {R : Kore.KSort}
    {φ : Kore.Pattern} {n : String} (hx : x.sort = KoreAML.srt n) (hex : ∃ a, InS I n a)
    (hfree : (tr ⟨t, []⟩ φ).isFreeEvar (t.ev (evarKey x)) = false) {e : Valuation M} (b : M) :
    (tr ⟨t, []⟩ φ).interpret I e b → (tr ⟨t, []⟩ (.exist R x φ)).interpret I e b := by
  intro h
  obtain ⟨a, ha⟩ := hex
  have hT : tr ⟨t, []⟩ (.exist R x φ) = sExists (t.ev (evarKey x)) (trSort t x.sort) (tr ⟨t, []⟩ φ) := by rw [tr]
  rw [hT, interp_sExists]
  refine ⟨a, ?_, (interp_upd_unheld hfree b).mpr h⟩
  rw [interp_member hD, hx, trSort_srt]
  exact (inS_iff _).mpr (by
    show InS I n (Function.update e.evalEvar (t.ev (evarKey x)) a (t.ev (evarKey x)))
    rw [Function.update_same]; exact ha)

/-- **The arity of a symbol of one argument, from `ΓSig`**: what `k` builds from a pattern whose
elements are in its argument sort is in its result sort. -/
theorem app1_inh [Inhabited M] (hD : DefOK I) {c : Semantics} (hS : I ⊧ᴵP ΓSig c) {k : CtorSig} {s : Srt}
    (hk : k ∈ kernelSyms c) (hargs : k.args = [s]) (hno : instDecode? (c.symName k.name) = none)
    {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I (c.sortName s) b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c k.name [p])).interpret I e m) : InS I (c.sortName k.result) m := by
  rw [tr_symApp, trArgs_appList, interp_appList] at h
  obtain ⟨a, ha, bs, hbs, hm⟩ := h
  simp only [List.map_cons, List.map_nil] at hbs
  cases hbs with
  | cons hb0 hbs =>
    cases hbs
    have hit : I ⊧ᴵ (symArityItem c k).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity hk, rfl⟩))
    rw [symArityItem_noInst hno] at hit
    rw [symHead_noInst (c := c) hno] at ha
    unfold KoreAML.arityItem at hit
    dsimp only [KoreAML.paramTable, List.map_nil] at hit
    have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
    unfold srtOf at hinc
    rw [trSort_srt] at hinc
    apply (inS_iff (I := I) KoreAML.val0).mp
    apply hinc
    rw [interp_appList]
    refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [_], ?_, hm⟩
    simp only [hargs, List.map_cons, List.map_nil, trSort_srt]
    exact .cons ((inS_iff _).mpr (hp _ hb0)) .nil

/-- **W1 for a rule read without a variable of its axiom.** `p` is Γ's axiom `\rewrites{C}(L', r)`;
the sentence's translation `tp` is the item of `\rewrites{C}(L, r)` at `p`'s table with the guards
of `fT`, under the renaming `ren` of its free variables' indices; `fT` are free variables of `p`
and the variable x of the sort n, which `p` does not hold; where the guards of `fT` hold, every
element of `L'` is one of `L`; the sort n has an element. Then a model of the sentence is a model
of Γ's item. -/
theorem rule_w1_drop [Inhabited M] (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r : Kore.Pattern}
    {fT : List VarKey} {tp : P} {ren : List (Nat × Nat)} {x : Kore.EVar} {n : String}
    (hx : x.sort = KoreAML.srt n) (hp : TieRuleLhs.rwParts p = some (C, L', r))
    (hsame : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p) fT C L r) ren = some tp)
    (hT : ∀ k ∈ fT, k = evarKey x ∨ k ∈ (freeOf [] p).eraseDups)
    (hbody : (tr ⟨tableOf [] p, []⟩ (.rewrites C L' r) ≡ inhOf (trSort (tableOf [] p) C)).isFreeEvar
      ((tableOf [] p).ev (evarKey x)) = false)
    (hgd : ∀ k ∈ (freeOf [] p).eraseDups,
      (guardOf (tableOf [] p) k).isFreeEvar ((tableOf [] p).ev (evarKey x)) = false)
    (hex : ∃ a, InS I n a) (h : I ⊧ᴵ tp)
    (hL : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
        ∀ a, (tr ⟨tableOf [] p, []⟩ L').interpret I e a → (tr ⟨tableOf [] p, []⟩ L).interpret I e a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat := by
  have hpe := TieRuleLhs.rwParts_eq hp
  have h1 : I ⊧ᴵ TieRuleLhs.itemAt (tableOf [] p) fT C L' r := fun e m =>
    TieRuleLhs.lhs_entails hD (fT := fT) (fG := fT) (fun _ hk => hk) ((TiePair.renSeq_iff hsame).mp h) e m (hL e m)
  intro e m
  have h2 := TieRuleLhs.trAxiom_rule C L' r
  rw [← hpe] at h2
  rw [h2]
  exact drop_var hD hx h1 hT hbody hgd hex e m

end

end TieRuleUnheld

end KCore
