/-
  KCore, outside the cone: a rewrite axiom whose right side the text writes in another form than
  Γ's item, in the direction from the text to Γ's item (W1). For a tie file where a reading note
  rewrites a rule's right side (`andAsEnsures`, `bottomAsEnsures`, a `\bottom` conjoined on the
  right side), beside `TieRuleLhs` (the left side).

  - `sides_entail`: the item of `\rewrites{C}(L, r)` with the guards of `fT` entails the item of
    `\rewrites{C}(L', r')` with the guards of `fG ⊇ fT`, where at every valuation at which the
    guards of `fG` hold every element of `L'` is one of `L` and every element of `r` is one of
    `r'` (`•` is monotone). `rule_w1_rhs`: the same from a sentence's translation, to `trAxiom`
    of Γ's axiom. `left_empty_of_right_empty`: an axiom whose right side holds nothing states
    that its left side holds nothing.
  - An application context with a hole that holds nothing holds nothing (`fill_empty`,
    `tr_fill_empty`); an element of a filled context gives an element of the hole
    (`fill_witness`). `\ceil` of a pattern that holds nothing holds nothing (`ceil_empty`), as
    does `\exists` over one (`exist_empty`) and a conjunction with such a conjunct (`and_empty`).
  - `andPred_sub`, `andPred_sup`: a right side `K[A ∧ {x = y}] ∧ \top{C}`, the predicate
    `\equals{Bool, S}(x, y)` conjoined under the application context K at the sort S of its
    hole, against `K[A] ∧ {x = y}`, the predicate `\equals{Bool, C}(x, y)` conjoined at the sort
    C of the whole. Every element of the first is one of the second; the converse where the
    elements of A are elements of S.
-/
import KcoreSpec.TieRuleLhs
import KcoreSpec.TieRhsEmpty

set_option autoImplicit false

namespace KCore

namespace TieRuleRhs

open ML Faithful KoreAML

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A rule axiom entails the one with a smaller left side and a larger right side.** The item of
`\rewrites{C}(L, r)` with the guards of `fT` holds in `I`; at the valuation `e`, where the guards
of `fG ⊇ fT` hold, every element of `L'` is an element of `L` and every element of `r` is an
element of `r'`. Then the item of `\rewrites{C}(L', r')` with the guards of `fG` holds at `e`. -/
theorem sides_entail (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort} {L L' r r' : Kore.Pattern}
    (hsub : ∀ k ∈ fT, k ∈ fG) (h : I ⊧ᴵ TieRuleLhs.itemAt t fT C L r) (e : Valuation M) (m : M)
    (hL : (∀ k ∈ fG, (guardOf t k).interpret I e m) →
      ∀ a, (tr ⟨t, []⟩ L').interpret I e a → (tr ⟨t, []⟩ L).interpret I e a)
    (hR : (∀ k ∈ fG, (guardOf t k).interpret I e m) →
      ∀ b, (tr ⟨t, []⟩ r).interpret I e b → (tr ⟨t, []⟩ r').interpret I e b) :
    (TieRuleLhs.itemAt t fG C L' r').interpret I e m := by
  have h1 := h e m
  unfold TieRuleLhs.itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ fG, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg' k (hsub k hk))
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  have hT : ∀ X Y, tr ⟨t, []⟩ (.rewrites C X Y) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ Y) :=
    fun X Y => by rw [tr]
  rw [hT] at h3 ⊢
  unfold sRewrites at h3 ⊢
  rw [interp_sImp] at h3 ⊢
  refine ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => ?_⟩⟩
  have h4 := (h3.mpr ht').2 (hL hg' a hl)
  unfold sNext at h4 ⊢
  obtain ⟨nx, b, hnx, hb, happ⟩ := interp_app.mp h4
  exact interp_app.mpr ⟨nx, b, hnx, hR hg' b hb, happ⟩

/-- **W1 for a rule whose two sides Γ reads in another form.** `p` is Γ's axiom
`\rewrites{C}(L', r')`; the sentence's translation `tp` is the item of `\rewrites{C}(L, r)` at
`p`'s table with the guards of `fT`, under the renaming `ren` of its free variables' indices; `fT`
are free variables of `p`; and where the guards of `p`'s free variables hold, every element of
`L'` is one of `L` and every element of `r` is one of `r'`. Then a model of the sentence is a model
of Γ's item. -/
theorem rule_w1_rhs (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r r' : Kore.Pattern} {fT : List VarKey}
    {tp : P} {ren : List (Nat × Nat)} (hp : TieRuleLhs.rwParts p = some (C, L', r'))
    (hsame : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p) fT C L r) ren = some tp)
    (hsub : fT.all (fun k => (freeOf [] p).eraseDups.contains k) = true) (h : I ⊧ᴵ tp)
    (hL : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p).eraseDups, (guardOf (tableOf [] p) k).interpret I e m) →
        ∀ a, (tr ⟨tableOf [] p, []⟩ L').interpret I e a → (tr ⟨tableOf [] p, []⟩ L).interpret I e a)
    (hR : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p).eraseDups, (guardOf (tableOf [] p) k).interpret I e m) →
        ∀ b, (tr ⟨tableOf [] p, []⟩ r).interpret I e b → (tr ⟨tableOf [] p, []⟩ r').interpret I e b) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat := by
  have hpe := TieRuleLhs.rwParts_eq hp
  intro e m
  have h1 := sides_entail hD (fT := fT) (fG := (freeOf [] p).eraseDups) (C := C) (L := L) (L' := L') (r := r) (r' := r')
    (fun k hk => List.contains_iff_mem.mp (List.all_eq_true.mp hsub k hk))
    ((TiePair.renSeq_iff hsame).mp h) e m (hL e m) (hR e m)
  have h2 := TieRuleLhs.trAxiom_rule C L' r'
  rw [← hpe] at h2
  rw [h2]; exact h1

/-- **A rule axiom with a right side that holds nothing states that its left side holds nothing.**
The item of `\rewrites{C}(L, r)` holds in `I`; at the valuation `e` the guards hold, `r` holds
nothing, and the elements of `L` are elements of the sort C. Then `L` holds nothing at `e`: an
element of it would have a successor among the elements of `r`. -/
theorem left_empty_of_right_empty (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
    (h : I ⊧ᴵ TieRuleLhs.itemAt t f C L r) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ f, (guardOf t k).interpret I e m)
    (hr : ∀ b, ¬ (tr ⟨t, []⟩ r).interpret I e b)
    (hLC : ∀ a, (tr ⟨t, []⟩ L).interpret I e a → (inhOf (trSort t C)).interpret I e a) (a : M) :
    ¬ (tr ⟨t, []⟩ L).interpret I e a := by
  intro hl
  have h1 := h e m
  unfold TieRuleLhs.itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg k hk)
  rw [interp_equal hD] at h2
  have h3 := (h2 a).mpr (hLC a hl)
  have hT : tr ⟨t, []⟩ (.rewrites C L r) = sRewrites (trSort t C) (tr ⟨t, []⟩ L) (tr ⟨t, []⟩ r) := by rw [tr]
  rw [hT] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  have h4 := h3.2 hl
  unfold sNext at h4
  obtain ⟨_, b, _, hb, _⟩ := interp_app.mp h4
  exact hr b hb

/-- An element of a filled application context gives an element of the hole. -/
theorem fill_witness {φ : P} {e : Valuation M} :
    ∀ (C : CutCtx) (m : M), (C.fill φ).interpret I e m → ∃ a, φ.interpret I e a
  | .hole, m, hm => ⟨m, hm⟩
  | .fn C _, _, hm => by
    obtain ⟨a, _, ha, _, _⟩ := interp_app.mp hm
    exact fill_witness C a ha
  | .arg _ C, _, hm => by
    obtain ⟨_, b, _, hb, _⟩ := interp_app.mp hm
    exact fill_witness C b hb

/-- **An application context whose hole holds nothing holds nothing.** -/
theorem fill_empty {φ : P} {e : Valuation M} (h : ∀ a, ¬ φ.interpret I e a) (C : CutCtx) (m : M) :
    ¬ (C.fill φ).interpret I e m := fun hm => by
  obtain ⟨a, ha⟩ := fill_witness C m hm
  exact h a ha

/-- **A KORE application context whose hole holds nothing holds nothing under `tr`**, no head on
the path to the hole an alias. -/
theorem tr_fill_empty (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true) {p : Kore.Pattern} {e : Valuation M}
    (h : ∀ a, ¬ (tr ctx p).interpret I e a) (m : M) : ¬ (tr ctx (K.fill p)).interpret I e m := by
  rw [tr_cutCtx ctx p K hK]
  exact fill_empty h _ m

/-- `\ceil` of a pattern that holds nothing holds nothing. -/
theorem ceil_empty {ctx : Ctx} {S S' : Kore.KSort} {p : Kore.Pattern} {e : Valuation M}
    (h : ∀ a, ¬ (tr ctx p).interpret I e a) (m : M) : ¬ (tr ctx (.ceil S S' p)).interpret I e m := by
  have hT : tr ctx (.ceil S S' p) = sCeil (trSort ctx.vars S) (trSort ctx.vars S') (tr ctx p) := by rw [tr]
  rw [hT, interp_sCeil_raw]
  rintro ⟨_, _, x, _, _, hx, _⟩
  exact h x hx

/-- A conjunction with a conjunct that holds nothing holds nothing. -/
theorem and_empty {ctx : Ctx} {S : Kore.KSort} {ps : List Kore.Pattern} {q : Kore.Pattern} {e : Valuation M}
    (hq : q ∈ ps) (h : ∀ a, ¬ (tr ctx q).interpret I e a) (m : M) : ¬ (tr ctx (.and S ps)).interpret I e m := by
  rw [interp_and (List.ne_nil_of_mem hq)]
  exact fun hm => h m (hm q hq)

/-- `\exists` over a pattern that holds nothing at any value of the bound variable holds nothing. -/
theorem exist_empty {t : VarTable} {R : Kore.KSort} {x : Kore.EVar} {p : Kore.Pattern} {e : Valuation M}
    (h : ∀ (a b : M), ¬ (tr ⟨t, []⟩ p).interpret I
      ⟨Function.update e.evalEvar (t.ev (evarKey x)) a, e.evalSvar⟩ b) (m : M) :
    ¬ (tr ⟨t, []⟩ (.exist R x p)).interpret I e m := by
  have hT : tr ⟨t, []⟩ (.exist R x p) = sExists (t.ev (evarKey x)) (trSort t x.sort) (tr ⟨t, []⟩ p) := by rw [tr]
  rw [hT, interp_sExists]
  rintro ⟨a, _, ha⟩
  exact h a m ha

end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A predicate conjoined under an application context holds where it does conjoined on the
whole.** Every element of `K[A ∧ \equals{Bool, S}(x, y)] ∧ \top{C}` is an element of
`K[A] ∧ \equals{Bool, C}(x, y)`: an element of the first gives an element of the hole, where the
equality at S holds, so `x` and `y` hold the same elements of Bool, which is the equality at C at
an element of C. -/
theorem andPred_sub (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {K : KoreCutCtx}
    (hK : K.noAlias ⟨t, []⟩ = true) {C S : Kore.KSort} {A x y : Kore.Pattern} {σB σS σC : M} {e : Valuation M}
    (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB)
    (hSS : ∀ a, (trSort t S).interpret I e a ↔ a = σS) (hSC : ∀ a, (trSort t C).interpret I e a ↔ a = σC)
    (hσB : IsSort I σB) (hσS : IsSort I σS) (hσC : IsSort I σC)
    (hC : (trSort t C).isFreeEvar topVar = false) (b : M)
    (h : (tr ⟨t, []⟩ (.and C [K.fill (.and S [A, .equals (srt "Bool") S x y]), .top C])).interpret I e b) :
    (tr ⟨t, []⟩ (.and C [K.fill A, .equals (srt "Bool") C x y])).interpret I e b := by
  rw [tr_and2, interp_sAnd] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hT : tr ⟨t, []⟩ (.top C) = sTop (trSort t C) := by rw [tr]
  rw [hT, interp_sTop hD hC, interp_inhOf_of hSC] at h2
  have hE : ∀ S', tr ⟨t, []⟩ (.equals (srt "Bool") S' x y) =
      sEquals (trSort t (srt "Bool")) (trSort t S') (tr ⟨t, []⟩ x) (tr ⟨t, []⟩ y) := fun S' => by rw [tr]
  have h1' := h1
  rw [tr_cutCtx _ _ K hK] at h1'
  obtain ⟨a, ha⟩ := fill_witness _ b h1'
  rw [tr_and2, interp_sAnd, hE, interp_sEquals hD hc hSB hSS hσB hσS] at ha
  refine ⟨TieRuleLhs.tr_fill_mono _ K hK (fun a' ha' => ?_) b h1, ?_⟩
  · rw [tr_and2, interp_sAnd] at ha'; exact ha'.1
  · rw [hE, interp_sEquals hD hc hSB hSC hσB hσC]; exact ⟨h2, ha.2.2⟩

/-- **The converse**, where the elements of `A` are elements of the hole's sort S: every element of
`K[A] ∧ \equals{Bool, C}(x, y)` is an element of `K[A ∧ \equals{Bool, S}(x, y)] ∧ \top{C}`. -/
theorem andPred_sup (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {K : KoreCutCtx}
    (hK : K.noAlias ⟨t, []⟩ = true) {C S : Kore.KSort} {A x y : Kore.Pattern} {σB σS σC : M} {e : Valuation M}
    (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB)
    (hSS : ∀ a, (trSort t S).interpret I e a ↔ a = σS) (hSC : ∀ a, (trSort t C).interpret I e a ↔ a = σC)
    (hσB : IsSort I σB) (hσS : IsSort I σS) (hσC : IsSort I σC)
    (hC : (trSort t C).isFreeEvar topVar = false)
    (hA : ∀ a, (tr ⟨t, []⟩ A).interpret I e a → Inh I σS a) (b : M)
    (h : (tr ⟨t, []⟩ (.and C [K.fill A, .equals (srt "Bool") C x y])).interpret I e b) :
    (tr ⟨t, []⟩ (.and C [K.fill (.and S [A, .equals (srt "Bool") S x y]), .top C])).interpret I e b := by
  rw [tr_and2, interp_sAnd] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hT : tr ⟨t, []⟩ (.top C) = sTop (trSort t C) := by rw [tr]
  have hE : ∀ S', tr ⟨t, []⟩ (.equals (srt "Bool") S' x y) =
      sEquals (trSort t (srt "Bool")) (trSort t S') (tr ⟨t, []⟩ x) (tr ⟨t, []⟩ y) := fun S' => by rw [tr]
  rw [hE, interp_sEquals hD hc hSB hSC hσB hσC] at h2
  refine ⟨TieRuleLhs.tr_fill_mono _ K hK (fun a' ha' => ?_) b h1, ?_⟩
  · rw [tr_and2, interp_sAnd, hE, interp_sEquals hD hc hSB hSS hσB hσS]
    exact ⟨ha', hA a' ha', h2.2⟩
  · rw [hT, interp_sTop hD hC, interp_inhOf_of hSC]; exact h2.1

end

end TieRuleRhs

end KCore
