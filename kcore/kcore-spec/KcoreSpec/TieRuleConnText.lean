/-
  KCore, outside the cone: a rewrite axiom one of whose sides the text writes with a connective at
  a term position under applications, where Γ's item writes the position through a reading
  (`connectiveCut`, `Parse.connRuleBody`; `lhsAndCut`, `Parse.lhsAndCut`), against the sentence as
  the text writes it, in every model of the signature. For a tie file.

  - What the cut's theorems (`KoreAML.rule_cut_mem`, `rule_and_pred`) ask of the table and the
    interpretation, from the patterns and from `ΓSig`:
    `noRead_of_notFree`: a pattern in which a variable is not free does not read it
    (`NoReadCut`); `sidesFree`, `sidesNoRead_of_free`: the same for the side patterns of an
    application context, as a decision on the context; `sort_sig`: in a model of `ΓSig` a numbered
    sort's pattern denotes one sort, at every table and valuation, and reads no variable;
    `top_noRead`, `top_inh`: `\top{C}` reads no variable the sort pattern does not hold, and its
    elements are C's.
  - `rule_cut_mem_in`: `KoreAML.rule_cut_mem` where every element of the conjunct E is in the
    outer sort (E is `\top{C}`, a rule's `ensures`), in place of every element of the filled
    context being in it: the membership q is read only at an element of `K[φ] ∧ E`.
  - `item_transfer`: the item of `\rewrites{C}(L, r)` with the guards of `fT` entails, at a
    valuation, the item of `\rewrites{C}(L', r')` with the guards of `fG ⊇ fT`, where under those
    guards every element of `L'` is one of `L` and every element of `r` one of `r'`
    (`TieRuleLhs.lhs_entails` with the right side changed as well: `•` is monotone).
    `rule_w1_sides`: from a sentence's translation, the item of `(L, r)` at the table of Γ's axiom
    up to the indices of its variables, to `trAxiom` of Γ's axiom `\rewrites{C}(L', r')`.
    `rule_w2_sides`: from `trAxiom` of Γ's axiom to the sentence's translation, where the free
    variables of Γ's axiom are the sentence's, every element of `L` is one of `L'` and every
    element of `r'` one of `r`.
  - `and_sub`: a conjunction is inside the conjunction of some of its operands.
-/
import KcoreSpec.TieRuleLhs
import KcoreSpec.RuleConnIn
import KcoreSpec.InertEv

set_option autoImplicit false

namespace KCore

namespace TieRuleConnText

open ML Faithful KoreAML

/-- No side pattern of the context holds the variable x free. -/
def sidesFree (ctx : Ctx) (x : EVar) : KoreCutCtx → Bool
  | .hole => true
  | .app h ss pre C post =>
    !(trArgs ctx (trSortApp ctx.vars (sym (.symbol h.ident.name)) ss) pre).isFreeEvar x &&
      post.all (fun q => !(tr ctx q).isFreeEvar x) && sidesFree ctx x C

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern in which x is not free does not read x. -/
theorem noRead_of_notFree {ψ : P} {x : EVar} (h : ψ.isFreeEvar x = false) : NoReadCut I x ψ := by
  intro e a m
  exact only_free_var_relevant _ _ _ _ (fun y hy => by
    have : y ≠ x := by
      rintro rfl
      rw [h] at hy; cases hy
    simp [Function.update, this]) (fun _ _ => rfl) m

/-- The side patterns of a context none of which holds x free do not read x. -/
theorem sidesNoRead_of_free {ctx : Ctx} {x : EVar} : ∀ (K : KoreCutCtx), sidesFree ctx x K = true →
    K.SidesNoRead I ctx x
  | .hole, _ => trivial
  | .app h ss pre C post, hK => by
    unfold sidesFree at hK
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hK
    exact ⟨noRead_of_notFree hK.1.1, fun q hq => noRead_of_notFree (hK.1.2 q hq), sidesNoRead_of_free C hK.2⟩

/-- In a model of the signature, the pattern of a numbered sort denotes one sort at every table and
valuation, and reads no variable. -/
theorem sort_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) {s : Srt}
    (hs : s < nRegSorts + c.sortNames.length) {n : String} (hn : c.sortName s = n) :
    ∃ σ, IsSort I σ ∧ (∀ (t : VarTable) (e : Valuation M) (a : M), (trSort t (srt n)).interpret I e a ↔ a = σ) ∧
      ∀ (t : VarTable) (x : EVar), NoReadCut I x (trSort t (srt n)) := by
  obtain ⟨σ, h1, h2⟩ := TieRhs.sortSing_sig hD hSig hs
  rw [hn] at h1
  refine ⟨σ, h2, fun t e a => by rw [trSort_srt]; exact h1 a, fun t x e a m => ?_⟩
  rw [trSort_srt]; exact Iff.rfl

/-- `\top{C}` reads no variable that C's pattern does not read. -/
theorem top_noRead (hD : DefOK I) {t : VarTable} {C : Kore.KSort} {x : EVar}
    (hCx : NoReadCut I x (trSort t C)) : NoReadCut I x (tr ⟨t, []⟩ (.top C)) := by
  intro e a m
  simp only [tr]
  rw [interp_sTop hD (InertEv.trSort_topFresh t C), interp_sTop hD (InertEv.trSort_topFresh t C),
    interp_inhOf, interp_inhOf]
  exact exists_congr fun τ => and_congr_left' (hCx e a τ)

/-- Every element of `\top{C}` is in C. -/
theorem top_inh (hD : DefOK I) {t : VarTable} {C : Kore.KSort} {e : Valuation M} {σ' : M}
    (hC : ∀ a, (trSort t C).interpret I e a ↔ a = σ') (m : M)
    (h : (tr ⟨t, []⟩ (.top C)).interpret I e m) : Inh I σ' m := by
  simp only [tr] at h
  rw [interp_sTop hD (InertEv.trSort_topFresh t C)] at h
  exact (interp_inhOf_of hC).mp h

/-- **The cut with the membership as a predicate, the outer sort read from E**:
`\exists{C}(Z:S, \and{C}(K[Z], E, q))` is `\and{C}(K[φ], E)`, q the membership of Z in φ, where
every element of E is in C. -/
theorem rule_cut_mem_in (hD : DefOK I)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (z : Kore.EVar) (hz : z.sort = S) (φ q E : Kore.Pattern)
    (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ctx (ctx.vars.ev (evarKey z)))
    (hφ : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx φ))
    (hE : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx E))
    (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hq : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q φ)
    (hin : ∀ a, (tr ctx φ).interpret I e a → Inh I σ a)
    (hEin : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      (tr ctx (.and C [K.fill φ, E])).interpret I e m := by
  have hl : tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E, q])) =
      sExists (ctx.vars.ev (evarKey z)) (trSort ctx.vars S)
        (sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey z)))) (sAnd (tr ctx E) (tr ctx q))) := by
    simp only [tr, trAndList, hz]
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hr : tr ctx (.and C [K.fill φ, E]) = sAnd ((K.toCut ctx).fill (tr ctx φ)) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK]
  rw [hl, hr, interp_sExists, interp_sAnd,
    cut_sem (ctx.vars.ev (evarKey z)) _ (K.toCut ctx) (KoreCutCtx.toCut_fresh K hsides) e m]
  generalize ctx.vars.ev (evarKey z) = x at *
  have hSu : ∀ a b, (trSort ctx.vars S).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ :=
    fun a b => (hSz e a b).trans (hS b)
  have hup : ∀ a, (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a :=
    fun a => by simp
  constructor
  · rintro ⟨a, hxa, hbody⟩
    simp only [interp_sAnd] at hbody
    obtain ⟨hCx, hE', hmem⟩ := hbody
    rw [interp_member hD, interp_inhOf_of (hSu a), hup a] at hxa
    exact ⟨⟨a, (hφ e a a).mp ((hq a hxa m).mp hmem).1, hCx⟩, (hE e a m).mp hE'⟩
  · rintro ⟨⟨a, hφa, hCx⟩, hEm⟩
    have hIa : Inh I σ a := hin a hφa
    refine ⟨a, ?_, ?_⟩
    · rw [interp_member hD, interp_inhOf_of (hSu a), hup a]; exact hIa
    · simp only [interp_sAnd]
      exact ⟨hCx, (hE e a m).mpr hEm, (hq a hIa m).mpr ⟨(hφ e a a).mpr hφa, hEin m hEm⟩⟩

/-- A conjunction is inside the conjunction of some of its operands. -/
theorem and_sub {t : VarTable} {C C' : Kore.KSort} {ps qs : List Kore.Pattern} (hq : qs ≠ [])
    (h : ∀ q ∈ qs, q ∈ ps) {e : Valuation M} (a : M) (ha : (tr ⟨t, []⟩ (.and C ps)).interpret I e a) :
    (tr ⟨t, []⟩ (.and C' qs)).interpret I e a := by
  have hp : ps ≠ [] := by
    rintro rfl
    cases qs with
    | nil => exact hq rfl
    | cons q _ => exact absurd (h q (List.mem_cons_self ..)) (List.not_mem_nil)
  rw [interp_and hp] at ha
  rw [interp_and hq]
  exact fun q hq' => ha q (h q hq')

/-- **A rule axiom entails the one with a smaller left side and a larger right side.** The item of
`\rewrites{C}(L, r)` with the guards of `fT` holds in `I`; at the valuation `e`, where the guards of
`fG ⊇ fT` hold, every element of `L'` is one of `L` and every element of `r` one of `r'`. Then the
item of `\rewrites{C}(L', r')` with the guards of `fG` holds at `e`. -/
theorem item_transfer (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort}
    {L L' r r' : Kore.Pattern} (hsub : ∀ k ∈ fT, k ∈ fG) (h : I ⊧ᴵ TieRuleLhs.itemAt t fT C L r)
    (e : Valuation M) (m : M)
    (hL : (∀ k ∈ fG, (guardOf t k).interpret I e m) →
      ∀ a, (tr ⟨t, []⟩ L').interpret I e a → (tr ⟨t, []⟩ L).interpret I e a)
    (hr : (∀ k ∈ fG, (guardOf t k).interpret I e m) →
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
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  have hT : ∀ X Y, tr ⟨t, []⟩ (.rewrites C X Y) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ Y) :=
    fun X Y => by rw [tr]
  rw [hT] at h3 ⊢
  unfold sRewrites at h3 ⊢
  rw [interp_sImp] at h3 ⊢
  refine ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => ?_⟩⟩
  have hn := (h3.mpr ht').2 (hL hg' a hl)
  unfold sNext at hn ⊢
  obtain ⟨x, b, hx, hb, happ⟩ := interp_app.mp hn
  exact interp_app.mpr ⟨x, b, hx, hr hg' b hb, happ⟩

/-- **W1 for a rule whose two sides Γ reads in another form.** `p` is Γ's axiom
`\rewrites{C}(L', r')`; the sentence's translation `tp` is the item of `\rewrites{C}(L, r)` at `p`'s
table with the guards of `fT`, under the renaming `ren` of its free variables' indices; `fT` are
free variables of `p`; and where the guards of `p`'s free variables hold, every element of `L'` is
one of `L` and every element of `r` one of `r'`. Then a model of the sentence is a model of Γ's
item. -/
theorem rule_w1_sides (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r r' : Kore.Pattern}
    {fT : List VarKey} {tp : P} {ren : List (Nat × Nat)} (hp : TieRuleLhs.rwParts p = some (C, L', r'))
    (hsame : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p) fT C L r) ren = some tp)
    (hsub : fT.all (fun k => (freeOf [] p).eraseDups.contains k) = true) (h : I ⊧ᴵ tp)
    (hL : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p).eraseDups, (guardOf (tableOf [] p) k).interpret I e m) →
        ∀ a, (tr ⟨tableOf [] p, []⟩ L').interpret I e a → (tr ⟨tableOf [] p, []⟩ L).interpret I e a)
    (hr : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p).eraseDups, (guardOf (tableOf [] p) k).interpret I e m) →
        ∀ a, (tr ⟨tableOf [] p, []⟩ r).interpret I e a → (tr ⟨tableOf [] p, []⟩ r').interpret I e a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat := by
  have hpe := TieRuleLhs.rwParts_eq hp
  intro e m
  have h1 := item_transfer hD (fT := fT) (fG := (freeOf [] p).eraseDups) (C := C) (L := L) (L' := L')
    (r := r) (r' := r') (fun k hk => List.contains_iff_mem.mp (List.all_eq_true.mp hsub k hk))
    ((TiePair.renSeq_iff hsame).mp h) e m (hL e m) (hr e m)
  have h2 := TieRuleLhs.trAxiom_rule C L' r'
  rw [← hpe] at h2
  rw [h2]; exact h1

/-- **W2 for a rule whose two sides Γ reads in another form.** `p` is Γ's axiom
`\rewrites{C}(L', r')`, which holds in `I`; the sentence's translation `tp` is the item of
`\rewrites{C}(L, r)` at `p`'s table with the guards of `fT`, under the renaming `ren`; every free
variable of `p` is in `fT`; and where the guards of `fT` hold, every element of `L` is one of `L'`
and every element of `r'` one of `r`. Then the sentence holds in `I`. -/
theorem rule_w2_sides (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r r' : Kore.Pattern}
    {fT : List VarKey} {tp : P} {ren : List (Nat × Nat)} (hp : TieRuleLhs.rwParts p = some (C, L', r'))
    (hsame : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p) fT C L r) ren = some tp)
    (hsub : ∀ k ∈ (freeOf [] p).eraseDups, k ∈ fT)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat)
    (hL : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      ∀ a, (tr ⟨tableOf [] p, []⟩ L).interpret I e a → (tr ⟨tableOf [] p, []⟩ L').interpret I e a)
    (hr : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      ∀ a, (tr ⟨tableOf [] p, []⟩ r').interpret I e a → (tr ⟨tableOf [] p, []⟩ r).interpret I e a) :
    I ⊧ᴵ tp := by
  have hpe := TieRuleLhs.rwParts_eq hp
  rw [hpe, TieRuleLhs.trAxiom_rule] at h
  rw [← hpe] at h
  exact (TiePair.renSeq_iff hsame).mpr fun e m => item_transfer hD hsub h e m (hL e m) (hr e m)

end

end TieRuleConnText

end KCore
