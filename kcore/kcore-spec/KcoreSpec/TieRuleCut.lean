/-
  KCore, outside the cone: a rewrite axiom whose left side holds an application `φ` under
  applications, `K[φ]`, against Γ's item of the rule read with the application cut
  (`Parse.ovlCut`): the left side `K[V]`, V a variable of the rule, with the conjunct `V ∈ φ`.

  `K[φ]` is the union of `K[b]` over the elements b of φ in every interpretation
  (`KoreAML.cut_sem`), and `(∃V. ψ) → •R` is `∀V. (ψ → •R)` for V free in neither side.

  - `cutLeft_sub`: at one valuation, every element of Γ's left side
    `K[V] ∧ rest ∧ V ∈ φ ∧ extra` is one of the text's `K[φ] ∧ rest` (the membership gives V's
    value as an element of φ, and a context is monotone). `openCut_w1`: so the text's sentence
    gives Γ's item (W1).
  - `item_w2`: Γ's item with a variable x more gives the text's item at a valuation where every
    element of the text's left side is one of Γ's at some value of x at which Γ's guards hold.
    `cutLeft_split`: an element of `K[φ] ∧ rest` is one of `K[V] ∧ rest ∧ V ∈ φ ∧ extra` at V an
    element b of φ, where b is in V's sort and the conjuncts of `extra` hold of the element.
    `openCut_w2`: so Γ's item gives the text's sentence (W2) where every element of φ is in V's
    sort and the conjuncts Γ adds beside the membership (`extra`: the negation of the rules of a
    smaller priority, the definedness of the right side) hold of every element of the text's left
    side. `openCut_tie`: the two together.
  - `cutFreshB`: the decisions that V is free in nothing but its own occurrence and membership.
  - `rightDefined_of_Γ`: the conjunct `⌈r ∧ ⊤⌉` of `extra` holds in every model of Γ, of every
    element of the rule's sort, where the guards of the variables hold, for a right side `r` built
    of variables and of constructors whose Cons-Fun items Γ has (`builtB`, `funsInB`): such a
    pattern denotes one element of its sort (`builtB_one`, by Cons-Fun at the arguments' elements).
    `rightDefined_of_funs`: the same from the Cons-Fun items alone.
-/
import KcoreSpec.TieRuleLhs
import KcoreSpec.TieFRRead

set_option autoImplicit false

namespace KCore

namespace TieRuleCut

open ML Faithful KoreAML
open TieRuleLhs (itemAt rwParts rwParts_eq trAxiom_rule)

/-- No side pattern of the context's translation holds x free. -/
def sidesFreshB (ctx : Ctx) (x : EVar) : KoreCutCtx → Bool
  | .hole => true
  | .app h ss pre C post =>
    !(trArgs ctx (trSortApp ctx.vars (sym (.symbol h.ident.name)) ss) pre).isFreeEvar x &&
      post.all (fun q => !(tr ctx q).isFreeEvar x) && sidesFreshB ctx x C

/-- The variable of the cut, `x`, is free in no part of the two items but its own occurrence and
its membership: the context's sides, φ, the other conjuncts, the sort, the right side under next
and the guards of the text's variables; and the sort's pattern does not hold `topVar`. -/
def cutFreshB (t : VarTable) (fT : List VarKey) (C : Kore.KSort) (K : KoreCutCtx) (V : Kore.EVar)
    (φ r : Kore.Pattern) (rest extra : List Kore.Pattern) : Bool :=
  let x := t.ev (evarKey V)
  sidesFreshB ⟨t, []⟩ x K && !(tr ⟨t, []⟩ φ).isFreeEvar x &&
    (rest ++ extra).all (fun q => !(tr ⟨t, []⟩ q).isFreeEvar x) &&
    !(inhOf (trSort t C)).isFreeEvar x && !(sNext (tr ⟨t, []⟩ r)).isFreeEvar x &&
    fT.all (fun k => !(guardOf t k).isFreeEvar x) && !(trSort t C).isFreeEvar topVar

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern in which x is not free does not read x. -/
theorem notFree_cut {ψ : P} {x : EVar} (h : ψ.isFreeEvar x = false) : NoReadCut I x ψ :=
  fun e _ m => only_free_var_relevant _ _ _ _ (fun y hy => by
    have hne : y ≠ x := by rintro rfl; rw [h] at hy; cases hy
    simp [Function.update, hne]) (fun _ _ => rfl) m

theorem sidesFresh_noRead {ctx : Ctx} {x : EVar} :
    ∀ (K : KoreCutCtx), sidesFreshB ctx x K = true → K.SidesNoRead I ctx x
  | .hole, _ => trivial
  | .app h ss pre C post, hK => by
    simp only [sidesFreshB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hK
    exact ⟨notFree_cut hK.1.1, fun q hq => notFree_cut (hK.1.2 q hq), sidesFresh_noRead C hK.2⟩

/-- The translation of an element variable is the variable of its key. -/
theorem tr_evarCut (t : VarTable) (V : Kore.EVar) :
    tr ⟨t, []⟩ (.var (.evar V)) = .evar (t.ev (evarKey V)) := by
  simp [tr]

/-- **Γ's left side is in the text's.** At one valuation, an element of
`K[V] ∧ rest ∧ V ∈ φ ∧ extra` is an element of `K[φ] ∧ rest`. -/
theorem cutLeft_sub {t : VarTable} {C : Kore.KSort} {K : KoreCutCtx} (hK : K.noAlias ⟨t, []⟩ = true)
    {V : Kore.EVar} {φ : Kore.Pattern} {rest extra : List Kore.Pattern} (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ (.and C (K.fill (.var (.evar V)) :: (rest ++ .in V.sort C (.var (.evar V)) φ :: extra)))).interpret I e a) :
    (tr ⟨t, []⟩ (.and C (K.fill φ :: rest))).interpret I e a := by
  rw [interp_and (List.cons_ne_nil _ _)] at h ⊢
  have hin := h (.in V.sort C (.var (.evar V)) φ)
    (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hT : tr ⟨t, []⟩ (.in V.sort C (.var (.evar V)) φ) =
      sIn (trSort t V.sort) (trSort t C) (.evar (t.ev (evarKey V))) (tr ⟨t, []⟩ φ) := by simp only [tr]
  rw [hT] at hin
  unfold sIn at hin
  obtain ⟨_, _, y, -, -, hy, -⟩ := interp_sCeil_raw.mp hin
  rw [interp_sAnd, interp_evar] at hy
  have hsub : ∀ a', (tr ⟨t, []⟩ (.var (.evar V))).interpret I e a' → (tr ⟨t, []⟩ φ).interpret I e a' := by
    intro a' ha'
    rw [tr_evarCut, interp_evar] at ha'
    rw [ha', ← hy.1]; exact hy.2
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact TieRuleLhs.tr_fill_mono _ K hK hsub a (h _ List.mem_cons_self)
  · exact h p (List.mem_cons_of_mem _ (List.mem_append_left _ hp))

/-- **W1 for a rule read through the cut.** `p` is Γ's axiom
`\rewrites{C}(K[V] ∧ rest ∧ V ∈ φ ∧ extra, r)`; the sentence's translation `tp` is the item of
`\rewrites{C}(K[φ] ∧ rest, r)` at `p`'s table with the guards of `fT`, under the renaming `ren`.
Then a model of the sentence is a model of Γ's item. -/
theorem openCut_w1 (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {K : KoreCutCtx} {V : Kore.EVar}
    {φ r : Kore.Pattern} {rest extra : List Kore.Pattern} {fT : List VarKey} {tp : P} {ren : List (Nat × Nat)}
    (hp : rwParts p =
      some (C, .and C (K.fill (.var (.evar V)) :: (rest ++ .in V.sort C (.var (.evar V)) φ :: extra)), r))
    (hK : K.noAlias ⟨tableOf [] p, []⟩ = true)
    (hsame : TiePair.renSeq (itemAt (tableOf [] p) fT C (.and C (K.fill φ :: rest)) r) ren = some tp)
    (hsub : fT.all (fun k => (freeOf [] p).eraseDups.contains k) = true) (h : I ⊧ᴵ tp) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat :=
  TieRuleLhs.rule_w1 hD hp hsame hsub h fun e _ _ a ha => cutLeft_sub hK e a ha

/-- **Γ's item with a variable more gives the text's.** The item of `\rewrites{C}(L', r)` with the
guards of `fG` holds in `I`; x is free neither in the sort nor in the right side; at the valuation
`e`, where the guards of `fT` hold, every element of `L` is an element of `L'` at some value of x
at which the guards of `fG` hold. Then the item of `\rewrites{C}(L, r)` with the guards of `fT`
holds at `e`. -/
theorem item_w2 (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort} {L L' r : Kore.Pattern}
    {x : EVar} (h : I ⊧ᴵ itemAt t fG C L' r)
    (hC : (inhOf (trSort t C)).isFreeEvar x = false) (hr : (sNext (tr ⟨t, []⟩ r)).isFreeEvar x = false)
    (e : Valuation M) (m : M)
    (hL : (∀ k ∈ fT, (guardOf t k).interpret I e m) → ∀ a, (tr ⟨t, []⟩ L).interpret I e a →
      ∃ b, (∀ k ∈ fG, (guardOf t k).interpret I ⟨Function.update e.evalEvar x b, e.evalSvar⟩ m) ∧
        (tr ⟨t, []⟩ L').interpret I ⟨Function.update e.evalEvar x b, e.evalSvar⟩ a) :
    (itemAt t fT C L r).interpret I e m := by
  unfold itemAt
  rw [interpret_impl]
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ fT, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  rw [interp_equal hD]
  intro a
  have hT : ∀ X, tr ⟨t, []⟩ (.rewrites C X r) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ r) :=
    fun X => by rw [tr]
  rw [hT]
  unfold sRewrites
  rw [interp_sImp]
  refine ⟨fun hf => hf.1, fun hs => ⟨hs, fun hl => ?_⟩⟩
  obtain ⟨b, hgb, hlb⟩ := hL hg' a hl
  have h1 := h ⟨Function.update e.evalEvar x b, e.evalSvar⟩ m
  unfold itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun ψ hψ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hψ
    exact hgb k hk)
  rw [interp_equal hD] at h2
  have h3 := h2 a
  rw [hT] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  exact (notFree_cut hr e b a).mp ((h3.mpr ((notFree_cut hC e b a).mpr hs)).2 hlb)

/-- **An element of the text's left side is one of Γ's, at an element of φ.** At the valuation
`e`, `a` is an element of `K[φ] ∧ rest` and of the sort of C, and the conjuncts of `extra` hold of
it; every element of φ is in V's sort; V's variable is free in nothing but its own occurrences.
Then at some element b of φ, in V's sort, as V's value, `a` is an element of
`K[V] ∧ rest ∧ V ∈ φ ∧ extra`. -/
theorem cutLeft_split [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {C : Kore.KSort}
    {K : KoreCutCtx} (hK : K.noAlias ⟨t, []⟩ = true) {V : Kore.EVar} {φ : Kore.Pattern}
    {rest extra : List Kore.Pattern}
    (hKx : sidesFreshB ⟨t, []⟩ (t.ev (evarKey V)) K = true)
    (hφx : (tr ⟨t, []⟩ φ).isFreeEvar (t.ev (evarKey V)) = false)
    (hrx : ∀ q ∈ rest ++ extra, (tr ⟨t, []⟩ q).isFreeEvar (t.ev (evarKey V)) = false)
    {σ σ' : M} (hS : ∀ (e : Valuation M) a, (trSort t V.sort).interpret I e a ↔ a = σ)
    (hS' : ∀ (e : Valuation M) a, (trSort t C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ') (e : Valuation M)
    (hφs : ∀ b, (tr ⟨t, []⟩ φ).interpret I e b → Inh I σ b) (a : M) (ha : Inh I σ' a)
    (hx : ∀ q ∈ extra, (tr ⟨t, []⟩ q).interpret I e a)
    (h : (tr ⟨t, []⟩ (.and C (K.fill φ :: rest))).interpret I e a) :
    ∃ b, Inh I σ b ∧
      (tr ⟨t, []⟩ (.and C (K.fill (.var (.evar V)) :: (rest ++ .in V.sort C (.var (.evar V)) φ :: extra)))).interpret I
        ⟨Function.update e.evalEvar (t.ev (evarKey V)) b, e.evalSvar⟩ a := by
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hKφ := h _ List.mem_cons_self
  rw [tr_cutCtx _ _ K hK] at hKφ
  obtain ⟨b, hb, hKb⟩ := (cut_sem (t.ev (evarKey V)) (tr ⟨t, []⟩ φ) (K.toCut ⟨t, []⟩)
    (KoreCutCtx.toCut_fresh K (sidesFresh_noRead K hKx)) e a).mp hKφ
  refine ⟨b, hφs b hb, ?_⟩
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [tr_cutCtx _ _ K hK, tr_evarCut]; exact hKb
  rcases List.mem_append.mp hp with hp | hp
  · exact (notFree_cut (hrx p (List.mem_append_left _ hp)) e b a).mpr (h p (List.mem_cons_of_mem _ hp))
  rcases List.mem_cons.mp hp with rfl | hp
  · have hT : tr ⟨t, []⟩ (.in V.sort C (.var (.evar V)) φ) =
        sIn (trSort t V.sort) (trSort t C) (.evar (t.ev (evarKey V))) (tr ⟨t, []⟩ φ) := by simp only [tr]
    have hval : (⟨Function.update e.evalEvar (t.ev (evarKey V)) b, e.evalSvar⟩ : Valuation M).evalEvar
        (t.ev (evarKey V)) = b := by simp
    rw [hT, interp_sIn hD hc (hS _) (hS' _) hσ hσ' (fun a' ha' => by
      rw [interp_evar, hval] at ha'
      rw [ha']; exact hφs b hb) a]
    refine ⟨⟨b, ?_, (notFree_cut hφx e b b).mpr hb⟩, ha⟩
    rw [interp_evar, hval]
  · exact (notFree_cut (hrx p (List.mem_append_right _ hp)) e b a).mpr (hx p hp)

/-- **W2 for a rule read through the cut.** `p` is Γ's axiom
`\rewrites{C}(K[V] ∧ rest ∧ V ∈ φ ∧ extra, r)`, whose free variables are those of `fT` and V; the
sentence's translation `tp` is the item of `\rewrites{C}(K[φ] ∧ rest, r)` at `p`'s table with the
guards of `fT`, under the renaming `ren`; `\top{C}` is a conjunct of `rest`; V is free in nothing
but its occurrence and its membership (`cutFreshB`); the sorts of V and C denote sorts. Where the
guards of `fT` hold, every element of φ is in V's sort (`hφs`) and the conjuncts of `extra` hold
of every element of the text's left side (`hguard`). Then a model of Γ's item is a model of the
sentence. -/
theorem openCut_w2 [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {p : Kore.Pattern} {C : Kore.KSort}
    {K : KoreCutCtx} {V : Kore.EVar} {φ r : Kore.Pattern} {rest extra : List Kore.Pattern} {fT : List VarKey}
    {tp : P} {ren : List (Nat × Nat)}
    (hp : rwParts p =
      some (C, .and C (K.fill (.var (.evar V)) :: (rest ++ .in V.sort C (.var (.evar V)) φ :: extra)), r))
    (hK : K.noAlias ⟨tableOf [] p, []⟩ = true)
    (hsame : TiePair.renSeq (itemAt (tableOf [] p) fT C (.and C (K.fill φ :: rest)) r) ren = some tp)
    (hfG : (freeOf [] p).eraseDups.all (fun k => fT.contains k || k == evarKey V) = true)
    (htop : .top C ∈ rest)
    (hfresh : cutFreshB (tableOf [] p) fT C K V φ r rest extra = true)
    {σ σ' : M} (hS : ∀ (e : Valuation M) a, (trSort (tableOf [] p) V.sort).interpret I e a ↔ a = σ)
    (hS' : ∀ (e : Valuation M) a, (trSort (tableOf [] p) C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hφs : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      ∀ b, (tr ⟨tableOf [] p, []⟩ φ).interpret I e b → Inh I σ b)
    (hguard : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      ∀ a, (tr ⟨tableOf [] p, []⟩ (.and C (K.fill φ :: rest))).interpret I e a →
        ∀ q ∈ extra, (tr ⟨tableOf [] p, []⟩ q).interpret I e a)
    (hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat) : I ⊧ᴵ tp := by
  refine (TiePair.renSeq_iff hsame).mpr ?_
  have hpe := rwParts_eq hp
  have h2 := trAxiom_rule C (.and C (K.fill (.var (.evar V)) :: (rest ++ .in V.sort C (.var (.evar V)) φ :: extra))) r
  rw [← hpe] at h2
  rw [h2] at hg
  simp only [cutFreshB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hfresh
  obtain ⟨⟨⟨⟨⟨⟨hKx, hφx⟩, hrx⟩, hCx⟩, hrn⟩, hgx⟩, hCt⟩ := hfresh
  intro e m
  refine item_w2 hD hg hCx hrn e m fun hgT a ha => ?_
  have haC : Inh I σ' a := by
    have h1 := (interp_and (List.cons_ne_nil _ _)).mp ha (.top C)
      (List.mem_cons_of_mem _ htop)
    simp only [tr] at h1
    rw [interp_sTop hD hCt, interp_inhOf_of (hS' e)] at h1
    exact h1
  obtain ⟨b, hbσ, hlb⟩ := cutLeft_split hD hc hK hKx hφx hrx hS hS' hσ hσ' e (hφs e m hgT) a haC
    (hguard e m hgT a ha) ha
  refine ⟨b, fun k hk => ?_, hlb⟩
  have hk' := List.all_eq_true.mp hfG k hk
  rcases Bool.or_eq_true_iff.mp hk' with hk' | hk'
  · have hkT := List.contains_iff_mem.mp hk'
    exact (notFree_cut (hgx k hkT) e b m).mpr (hgT k hkT)
  · rw [beq_iff_eq.mp hk', TieRuleLhs.guard_evarKey hD, interp_inhOf_of (hS _)]
    show Inh I σ (Function.update e.evalEvar _ b _)
    rw [Function.update_same]; exact hbσ

/-- **The tie of a rule read through the cut**: under the premises of `openCut_w2`, the sentence
and Γ's item of the rule hold in the same interpretations. -/
theorem openCut_tie [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {p : Kore.Pattern} {C : Kore.KSort}
    {K : KoreCutCtx} {V : Kore.EVar} {φ r : Kore.Pattern} {rest extra : List Kore.Pattern} {fT : List VarKey}
    {tp : P} {ren : List (Nat × Nat)}
    (hp : rwParts p =
      some (C, .and C (K.fill (.var (.evar V)) :: (rest ++ .in V.sort C (.var (.evar V)) φ :: extra)), r))
    (hK : K.noAlias ⟨tableOf [] p, []⟩ = true)
    (hsame : TiePair.renSeq (itemAt (tableOf [] p) fT C (.and C (K.fill φ :: rest)) r) ren = some tp)
    (hsub : fT.all (fun k => (freeOf [] p).eraseDups.contains k) = true)
    (hfG : (freeOf [] p).eraseDups.all (fun k => fT.contains k || k == evarKey V) = true)
    (htop : .top C ∈ rest)
    (hfresh : cutFreshB (tableOf [] p) fT C K V φ r rest extra = true)
    {σ σ' : M} (hS : ∀ (e : Valuation M) a, (trSort (tableOf [] p) V.sort).interpret I e a ↔ a = σ)
    (hS' : ∀ (e : Valuation M) a, (trSort (tableOf [] p) C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hφs : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      ∀ b, (tr ⟨tableOf [] p, []⟩ φ).interpret I e b → Inh I σ b)
    (hguard : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p) k).interpret I e m) →
      ∀ a, (tr ⟨tableOf [] p, []⟩ (.and C (K.fill φ :: rest))).interpret I e a →
        ∀ q ∈ extra, (tr ⟨tableOf [] p, []⟩ q).interpret I e a) :
    (I ⊧ᴵ tp) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat) :=
  ⟨openCut_w1 hD hp hK hsame hsub,
   openCut_w2 hD hc hp hK hsame hfG htop hfresh hS hS' hσ hσ' hφs hguard⟩

end

/-! ## The definedness of a right side built of constructors -/

mutual
/-- `p` is of the sort named `s` and is built of the element variables of `fT` and of
applications, without sort arguments, of the constructors of `gs` (each with the name of the sort
its Cons-Fun item is of) to arguments built so, of the constructor's argument sorts. -/
def builtB (gs : List (String × KoreAML.CtorSig)) (fT : List VarKey) : Kore.Pattern → String → Bool
  | .var (.evar x), s => decide (x.sort = srt s) && fT.contains (evarKey x)
  | .app h ss ps, s =>
    match ss, gs.find? (fun g => g.1 == s && g.2.name == h.ident.name) with
    | [], some g => builtArgsB gs fT ps g.2.args
    | _, _ => false
  | _, _ => false
  termination_by structural p => p
def builtArgsB (gs : List (String × KoreAML.CtorSig)) (fT : List VarKey) : List Kore.Pattern → List String → Bool
  | [], [] => true
  | p :: ps, s :: ss => builtB gs fT p s && builtArgsB gs fT ps ss
  | _, _ => false
  termination_by structural ps => ps
end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- ψ denotes one element, an element of the sort named `s`. -/
def OneIn (I : Interpretation KoreAML.Sym M) (e : Valuation M) (s : String) (ψ : P) : Prop :=
  ∃ y, InS I s y ∧ ∀ m, ψ.interpret I e m ↔ m = y

omit [Inhabited M] in
/-- Patterns that each denote one element denote, as a list, the list of those elements. -/
theorem all2_one {t : VarTable} {e : Valuation M} {ps : List Kore.Pattern} {xs : List M}
    (h : All2 (fun p x => ∀ m, (tr ⟨t, []⟩ p).interpret I e m ↔ m = x) ps xs) :
    ∀ bs, All2 (fun p b => (tr ⟨t, []⟩ p).interpret I e b) ps bs ↔ bs = xs := by
  induction h with
  | nil => intro bs; constructor
           · intro h; cases h; rfl
           · rintro rfl; exact .nil
  | cons h1 _ ih =>
    intro bs; constructor
    · intro h; cases h with
      | cons hb hbs => rw [(h1 _).mp hb, (ih _).mp hbs]
    · rintro rfl; exact .cons ((h1 _).mpr rfl) ((ih _).mpr rfl)

variable {gs : List (String × KoreAML.CtorSig)} {fT : List VarKey} {t : VarTable}
  {e : Valuation M} {m0 : M}

mutual
/-- A pattern with `builtB` denotes one element, of its sort, where the guards of `fT` hold and
each constructor of `gs` has its Cons-Fun item. -/
theorem builtB_one (hD : DefOK I) (hgs : ∀ g ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g.1 (.ctor g.2)).pat)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m0) :
    ∀ (p : Kore.Pattern) (s : String), builtB gs fT p s = true → OneIn I e s (tr ⟨t, []⟩ p)
  | .var (.evar x), s, h => by
    rw [builtB, Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := (TieRuleLhs.guard_evarKey hD).mp (hg _ (List.contains_iff_mem.mp h.2))
    rw [h.1, trSort_srt] at h1
    refine ⟨_, (inS_iff e).mp h1, fun m => ?_⟩
    rw [tr_evarCut, interp_evar]
  | .app hd ss ps, s, h => by
    cases ss with
    | cons => simp [builtB] at h
    | nil =>
    cases hf : gs.find? (fun g => g.1 == s && g.2.name == hd.ident.name) with
    | none => simp [builtB, hf] at h
    | some g =>
      simp only [builtB, hf] at h
      have hmem := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
      obtain ⟨xs, hall, hl, hxs⟩ := builtArgsB_one hD hgs hg ps g.2.args h
      obtain ⟨y, hy, hyu⟩ := fun_at hD (hgs g hmem) hl hxs
      refine ⟨y, hp.1 ▸ hy, fun m => ?_⟩
      rw [TieFRRead.tr_app, TieFRRead.trArgs_iff, ← hyu m]
      unfold GS
      simp only [trSortApp, genHead, interp_sym, hp.2]
      constructor
      · rintro ⟨a, ha, bs, hbs, happ⟩
        rw [(all2_one hall bs).mp hbs] at happ
        exact ⟨a, ha, happ⟩
      · rintro ⟨a, ha, happ⟩
        exact ⟨a, ha, xs, (all2_one hall xs).mpr rfl, happ⟩
  | .var (.svar _), _, h => by simp [builtB] at h
  | .string _, _, h => by simp [builtB] at h
theorem builtArgsB_one (hD : DefOK I) (hgs : ∀ g ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g.1 (.ctor g.2)).pat)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m0) :
    ∀ (ps : List Kore.Pattern) (ss : List String), builtArgsB gs fT ps ss = true →
      ∃ xs : List M, All2 (fun p x => ∀ m, (tr ⟨t, []⟩ p).interpret I e m ↔ m = x) ps xs ∧
        xs.length = ss.length ∧ ∀ (i : Nat) x s, xs[i]? = some x → ss[i]? = some s → InS I s x
  | [], [], _ => ⟨[], .nil, rfl, fun i x s hx _ => by simp at hx⟩
  | p :: ps, s :: ss, h => by
    rw [builtArgsB, Bool.and_eq_true] at h
    obtain ⟨y, hy, hyu⟩ := builtB_one hD hgs hg p s h.1
    obtain ⟨xs, hall, hl, hxs⟩ := builtArgsB_one hD hgs hg ps ss h.2
    refine ⟨y :: xs, .cons hyu hall, by simp [hl], fun i x s' hx hs => ?_⟩
    cases i with
    | zero => simp at hx hs; rw [← hx, ← hs]; exact hy
    | succ i => simp at hx hs; exact hxs i x s' hx hs
  | [], _ :: _, h => by simp [builtArgsB] at h
  | _ :: _, [], h => by simp [builtArgsB] at h
end

/-- **The right side of a rule is defined, from Cons-Fun.** In a model of definedness where each
constructor of `gs` has its Cons-Fun item, at a valuation where the guards of `fT` hold, the
right side `\and{s}(r, \top{s}())` with `r` built of the variables of `fT` and the constructors
of `gs` (`builtB`) holds one element of the sort `s`, so `⌈r ∧ ⊤⌉` holds of every element of
`s`. -/
theorem rightDefined_of_funs (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (hgs : ∀ g ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g.1 (.ctor g.2)).pat) {s : String} {r : Kore.Pattern}
    (hb : builtB gs fT r s = true) {σ : M} (hS : ∀ a, I.evalSymb (.sort ("Sort" ++ s)) a ↔ a = σ)
    (hσ : IsSort I σ) (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m0) (a : M)
    (ha : (inhOf (trSort t (srt s))).interpret I e a) :
    (tr ⟨t, []⟩ (.ceil (srt s) (srt s) (.and (srt s) [r, .top (srt s)]))).interpret I e a := by
  obtain ⟨y, hy, hyu⟩ := builtB_one hD hgs hg r s hb
  have hS' : ∀ (e' : Valuation M) b, (trSort t (srt s)).interpret I e' b ↔ b = σ := fun e' b => by
    rw [trSort_srt, interp_sym]; exact hS b
  have hyσ : Inh I σ y := (interp_inhOf_of (hS' e)).mp (by rw [trSort_srt]; exact (inS_iff e).mpr hy)
  have hT : ∀ φ, tr ⟨t, []⟩ (.ceil (srt s) (srt s) φ) =
      sCeil (trSort t (srt s)) (trSort t (srt s)) (tr ⟨t, []⟩ φ) := fun φ => by rw [tr]
  have htop : ∀ b, (tr ⟨t, []⟩ (.top (srt s))).interpret I e b ↔ Inh I σ b := fun b => by
    have h1 : tr ⟨t, []⟩ (.top (srt s)) = sTop (trSort t (srt s)) := by rw [tr]
    rw [h1, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of (hS' e)]
  rw [hT, interp_sCeil hD hc (hS' e) (hS' e) hσ hσ (fun b hb' =>
    (htop b).mp ((interp_and (List.cons_ne_nil _ _)).mp hb' _ (List.mem_cons_of_mem _ List.mem_cons_self)))]
  refine ⟨⟨y, (interp_and (List.cons_ne_nil _ _)).mpr fun p hp => ?_⟩, (interp_inhOf_of (hS' e)).mp ha⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact (hyu y).mpr rfl
  · rw [List.mem_singleton.mp hp]; exact (htop y).mpr hyσ

end

/-- Γ of `c` has the Cons-Fun item of each constructor of `gs`, of the sort named beside it. -/
def funsInB (c : Semantics) (gs : List (String × KoreAML.CtorSig)) : Bool :=
  gs.all fun g => (consItemsK c).any fun it => decide (it.pat = (KoreAML.Cons.funItem g.1 (.ctor g.2)).pat)

kernel_rfl funsInB_withHooks : ∀ (c : Semantics) (H : HookParams) (gs : List (String × KoreAML.CtorSig)),
  funsInB (c.withHooks H) gs = funsInB c gs

/-- **The right side of a rule is defined, in a model of Γ.** For a right side
`\and{N}(r, \top{N}())` whose `r` is built of the variables of `fT` and of constructors whose
Cons-Fun items Γ has (`funsInB`, `builtB`): where the guards of `fT` hold, `⌈r ∧ ⊤⌉` holds of
every element of the sort N. This is the conjunct Γ's item of a rule adds to the text's left
side, of every element of that left side (which `\top{N}()` keeps in N). -/
theorem rightDefined_of_Γ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics} [OvlOK c]
    (hI : I ⊧ᴵP Γ c) {gs : List (String × KoreAML.CtorSig)} {fT : List VarKey} {t : VarTable} {N : Srt}
    {r : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length) (hin : funsInB c gs = true)
    (hb : builtB gs fT r (c.sortName N) = true) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m) (a : M)
    (ha : (inhOf (trSort t (srtOf c N))).interpret I e a) :
    (tr ⟨t, []⟩ (.ceil (srtOf c N) (srtOf c N) (.and (srtOf c N) [r, .top (srtOf c N)]))).interpret I e a := by
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI hN
  refine rightDefined_of_funs (defOK hI) (sat_sigItem hI sig_ceilDef) (fun g hg' => ?_) hb hσ1 hσ2 hg a ha
  obtain ⟨it, hit, hpat⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin g hg')
  rw [← of_decide_eq_true hpat]
  exact sat_cons hI (Or.inl ⟨it, hit, rfl⟩)

end TieRuleCut

end KCore
