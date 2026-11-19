/-
  KCore, outside the cone: a rule whose right side holds a conjunction of two terms under
  applications, read through the cut (`ReadingNote.andTermsCut`, `Parse.andCut`), against the right
  side as the text writes it. For a tie file.

  - `noRead_of_notFree`: a pattern in which x is not free does not read x. `sidesFreeB`,
    `sidesNoRead_of_free`: the same for the side patterns of a context, as a decision.
  - `rule_and_in_top`, `rule_and_var_top`: `KoreAML.rule_and_in` and `KoreAML.rule_and_var` where
    the conjunct E beside the term holds only elements of the outer sort (the `ensures` `\top{C}`
    of a rule without one). The inclusion of the filled context in the outer sort, a premise of
    the two, is then not asked: the element is one of E.
  - `rw_entails`: the item of `\rewrites{C}(L, r)` gives the item of `\rewrites{C}(L', r')` at a
    valuation where `L' ⊆ L` and `r ⊆ r'` (a rewrite axiom is antitone in its left side and
    monotone in its right side, `•` being an application).
  - `rule_w1_rhs`: W1 for a rule both of whose sides Γ reads in another form: a model of the
    sentence is a model of Γ's item. `rule_w2_rhs`: W2 at a valuation: Γ's item gives the sentence
    there.
-/
import KcoreSpec.TieRuleLhs
import KcoreSpec.RuleAndIn

set_option autoImplicit false

namespace KCore

namespace TieRuleRhsAnd

open ML Faithful KoreAML

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern in which x is not free does not read x. -/
theorem noRead_of_notFree {x : EVar} {ψ : P} (h : ψ.isFreeEvar x = false) : NoReadCut I x ψ := by
  intro e a m
  exact @only_free_var_relevant KoreAML.Sym M I ψ (Function.update e.evalEvar x a) e.evalEvar e.evalSvar e.evalSvar
    (fun y hy => by
      have hne : y ≠ x := fun hyx => by rw [hyx, h] at hy; cases hy
      simp [Function.update, hne])
    (fun _ _ => rfl) m

/-- x is free in no side pattern of `K.toCut ctx`: at each layer the head with the arguments
before the hole, and each argument after it. -/
def sidesFreeB (ctx : Ctx) (x : EVar) : KoreCutCtx → Bool
  | .hole => true
  | .app h ss pre C post =>
    !(trArgs ctx (trSortApp ctx.vars (sym (.symbol h.ident.name)) ss) pre).isFreeEvar x &&
      post.all (fun q => !(tr ctx q).isFreeEvar x) && sidesFreeB ctx x C

theorem sidesNoRead_of_free {ctx : Ctx} {x : EVar} : ∀ (K : KoreCutCtx), sidesFreeB ctx x K = true →
    K.SidesNoRead I ctx x
  | .hole, _ => trivial
  | .app h ss pre C post, hK => by
    simp only [sidesFreeB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hK
    exact ⟨noRead_of_notFree hK.1.1, fun q hq => noRead_of_notFree (hK.1.2 q hq), sidesNoRead_of_free C hK.2⟩

/-- **The fresh form, the conjunct E in the outer sort**:
`\exists{C}(Z:S, \and{C}(K[Z], E, \and{C}(\in{S,C}(Z, t), \in{S,C}(Z, u))))` is
`\and{C}(K[\and{S}(t, u)], E)`, where every element of E is in C. -/
theorem rule_and_in_top [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (z : Kore.EVar) (hz : z.sort = S) (t u E : Kore.Pattern)
    (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ctx (ctx.vars.ev (evarKey z)))
    (ht : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx t))
    (hu : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx u))
    (hE : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx E))
    (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
    (hCz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars C))
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hin : ∀ a, (tr ctx (.and S [t, u])).interpret I e a → Inh I σ a)
    (hEs : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E,
        .and C [.in S C (.var (.evar z)) t, .in S C (.var (.evar z)) u]]))).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [t, u]), E])).interpret I e m := by
  have hand : tr ctx (.and S [t, u]) = sAnd (tr ctx t) (tr ctx u) := by simp only [tr, trAndList]
  have hl : tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E,
        .and C [.in S C (.var (.evar z)) t, .in S C (.var (.evar z)) u]])) =
      sExists (ctx.vars.ev (evarKey z)) (trSort ctx.vars S)
        (sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey z)))) (sAnd (tr ctx E)
          (sAnd (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey z))) (tr ctx t))
            (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey z))) (tr ctx u))))) := by
    simp only [tr, trAndList, hz]
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hr : tr ctx (.and C [K.fill (.and S [t, u]), E]) =
      sAnd ((K.toCut ctx).fill (sAnd (tr ctx t) (tr ctx u))) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK, hand]
  rw [hand] at hin
  rw [hl, hr, interp_sExists, interp_sAnd,
    cut_sem (ctx.vars.ev (evarKey z)) _ (K.toCut ctx) (KoreCutCtx.toCut_fresh K hsides) e m]
  generalize ctx.vars.ev (evarKey z) = x at *
  have hSu : ∀ a b, (trSort ctx.vars S).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ :=
    fun a b => (hSz e a b).trans (hS b)
  have hCu : ∀ a b, (trSort ctx.vars C).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ' :=
    fun a b => (hCz e a b).trans (hC b)
  have hup : ∀ a, Function.update e.evalEvar x a x = a := fun a => by simp
  constructor
  · rintro ⟨a, hxa, hbody⟩
    simp only [interp_sAnd] at hbody
    obtain ⟨hCx, hE', hint, hinu⟩ := hbody
    rw [interp_member hD, interp_inhOf_of (hSu a)] at hxa
    have h1 := (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx t) m).mp hint
    have h2 := (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx u) m).mp hinu
    have h1' : (tr ctx t).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a := by
      have := h1.1; rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a] at this
      exact this
    have h2' : (tr ctx u).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a := by
      have := h2.1; rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a] at this
      exact this
    exact ⟨⟨a, interp_sAnd.mpr ⟨(ht e a a).mp h1', (hu e a a).mp h2'⟩, hCx⟩, (hE e a m).mp hE'⟩
  · rintro ⟨⟨a, hta, hCx⟩, hEm⟩
    have hφ := interp_sAnd.mp hta
    have hIa : Inh I σ a := hin a hta
    have hm' : Inh I σ' m := hEs m hEm
    have hxa : Inh I σ ((⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x) := by
      rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a]
      exact hIa
    refine ⟨a, ?_, ?_⟩
    · rw [interp_member hD, interp_inhOf_of (hSu a)]; exact hxa
    · simp only [interp_sAnd]
      refine ⟨hCx, (hE e a m).mpr hEm,
        (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx t) m).mpr ⟨?_, hm'⟩,
        (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx u) m).mpr ⟨?_, hm'⟩⟩
      · rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a]
        exact (ht e a a).mpr hφ.1
      · rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a]
        exact (hu e a a).mpr hφ.2

/-- **The variable form, the conjunct E in the outer sort**: `\and{C}(K[V], E, \in{S,C}(V, u))` is
`\and{C}(K[\and{S}(V, u)], E)`, where every element of E is in C. -/
theorem rule_and_var_top [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (v : Kore.EVar) (u E : Kore.Pattern) (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hv : Inh I σ (e.evalEvar (ctx.vars.ev (evarKey v))))
    (hEs : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u])).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E])).interpret I e m := by
  have hand : tr ctx (.and S [.var (.evar v), u]) =
      sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u) := by simp only [tr, trAndList]
  have hfillv : tr ctx (K.fill (.var (.evar v))) =
      (K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v))) := by
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hl : tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u]) =
      sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v)))) (sAnd (tr ctx E)
        (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) := by
    simp only [tr, trAndList]
    rw [hfillv]
  have hr : tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E]) =
      sAnd ((K.toCut ctx).fill (sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK, hand]
  rw [hl, hr, interp_sAnd, interp_sAnd, interp_sAnd, CutCtx.fill_evar_and,
    mem_iff_cut hD hc hS hC hσ hσ' _ hv]
  constructor
  · rintro ⟨hCx, hEm, hu, -⟩; exact ⟨⟨hu, hCx⟩, hEm⟩
  · rintro ⟨⟨hu, hCx⟩, hEm⟩; exact ⟨hCx, hEm, hu, hEs m hEm⟩

/-- `\top{C}` holds only elements of C, where C denotes one sort. -/
theorem top_inh (hD : DefOK I) {t : VarTable} {C : Kore.KSort} {e : Valuation M} {σ' : M}
    (hCf : (trSort t C).isFreeEvar topVar = false)
    (hC : ∀ a, (trSort t C).interpret I e a ↔ a = σ') (m : M)
    (h : (tr ⟨t, []⟩ (.top C)).interpret I e m) : Inh I σ' m := by
  rw [tr, interp_sTop hD hCf m] at h
  exact (interp_inhOf_of hC).mp h

/-- **A rewrite axiom entails the one with a smaller left side and a larger right side.** The item
of `\rewrites{C}(L, r)` with the guards of `fT` holds in `I`; at the valuation `e`, where the guards
of `fG ⊇ fT` hold, every element of `L'` is one of `L` and every element of `r` is one of `r'`.
Then the item of `\rewrites{C}(L', r')` with the guards of `fG` holds at `e`. -/
theorem rw_entails (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort} {L L' r r' : Kore.Pattern}
    (hsub : ∀ k ∈ fT, k ∈ fG) (h : I ⊧ᴵ TieRuleLhs.itemAt t fT C L r) (e : Valuation M) (m : M)
    (hLR : (∀ k ∈ fG, (guardOf t k).interpret I e m) →
      (∀ a, (tr ⟨t, []⟩ L').interpret I e a → (tr ⟨t, []⟩ L).interpret I e a) ∧
        ∀ a, (tr ⟨t, []⟩ r).interpret I e a → (tr ⟨t, []⟩ r').interpret I e a) :
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
  obtain ⟨hL, hR⟩ := hLR hg'
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  have hT : ∀ X Y, tr ⟨t, []⟩ (.rewrites C X Y) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ Y) :=
    fun X Y => by rw [tr]
  rw [hT] at h3 ⊢
  unfold sRewrites at h3 ⊢
  rw [interp_sImp] at h3 ⊢
  refine ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => ?_⟩⟩
  have hn := (h3.mpr ht').2 (hL a hl)
  unfold sNext at hn ⊢
  obtain ⟨nx, b, hnx, hb, happ⟩ := interp_app.mp hn
  exact interp_app.mpr ⟨nx, b, hnx, hR b hb, happ⟩

/-- **W1 for a rule both of whose sides Γ reads in another form.** `p` is Γ's axiom
`\rewrites{C}(L', r')`; the sentence's translation `tp` is the item of `\rewrites{C}(L, r)` at `p`'s
table with the guards of `fT`, under the renaming `ren` of its free variables' indices; `fT` are
free variables of `p`; and where the guards of `p`'s free variables hold, every element of `L'` is
one of `L` and every element of `r` is one of `r'`. Then a model of the sentence is a model of Γ's
item. -/
theorem rule_w1_rhs (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r r' : Kore.Pattern} {fT : List VarKey}
    {tp : P} {ren : List (Nat × Nat)} (hp : TieRuleLhs.rwParts p = some (C, L', r'))
    (hsame : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p) fT C L r) ren = some tp)
    (hsub : fT.all (fun k => (freeOf [] p).eraseDups.contains k) = true) (h : I ⊧ᴵ tp)
    (hLR : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p).eraseDups, (guardOf (tableOf [] p) k).interpret I e m) →
        (∀ a, (tr ⟨tableOf [] p, []⟩ L').interpret I e a → (tr ⟨tableOf [] p, []⟩ L).interpret I e a) ∧
          ∀ a, (tr ⟨tableOf [] p, []⟩ r).interpret I e a → (tr ⟨tableOf [] p, []⟩ r').interpret I e a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat := by
  have hpe := TieRuleLhs.rwParts_eq hp
  intro e m
  have h1 := rw_entails hD (fT := fT) (fG := (freeOf [] p).eraseDups) (C := C) (L := L) (L' := L') (r := r) (r' := r')
    (fun k hk => List.contains_iff_mem.mp (List.all_eq_true.mp hsub k hk))
    ((TiePair.renSeq_iff hsame).mp h) e m (hLR e m)
  have h2 := TieRuleLhs.trAxiom_rule C L' r'
  rw [← hpe] at h2
  rw [h2]; exact h1

/-- **W2 at a valuation, for a rule both of whose sides Γ reads in another form.** `p` is Γ's axiom
`\rewrites{C}(L', r')`, whose item holds in `I`; the sentence's translation is the item of
`\rewrites{C}(L, r)` at `p`'s table with the guards of `fT`, which hold every free variable of `p`;
at the valuation `e`, where the guards of `fT` hold, every element of `L` is one of `L'` and every
element of `r'` is one of `r`. Then the sentence's item holds at `e`. -/
theorem rule_w2_rhs (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r r' : Kore.Pattern} {fT : List VarKey}
    (hp : TieRuleLhs.rwParts p = some (C, L', r'))
    (hsub : ∀ k ∈ (freeOf [] p).eraseDups, k ∈ fT)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat) (e : Valuation M) (m : M)
    (hLR : (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      (∀ a, (tr ⟨tableOf [] p, []⟩ L).interpret I e a → (tr ⟨tableOf [] p, []⟩ L').interpret I e a) ∧
        ∀ a, (tr ⟨tableOf [] p, []⟩ r').interpret I e a → (tr ⟨tableOf [] p, []⟩ r).interpret I e a) :
    (TieRuleLhs.itemAt (tableOf [] p) fT C L r).interpret I e m := by
  rw [TieRuleLhs.rwParts_eq hp, TieRuleLhs.trAxiom_rule] at h
  rw [← TieRuleLhs.rwParts_eq hp] at h
  exact rw_entails hD hsub h e m hLR

end

end TieRuleRhsAnd

end KCore
