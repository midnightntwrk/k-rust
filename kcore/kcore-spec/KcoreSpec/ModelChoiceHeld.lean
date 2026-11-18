/-
  KCore. The value model at a transition, for rules with `rulePlainHeldH`.

  `closureDisjunct_held`, `satStepGoal_held` and `stdI_T_model_held_fns` are the `_pp` statements
  of ModelChoicePP.lean with the per-rule fact `rulePlainHeldH c H` in place of `rulePlainPP`. The
  proofs read `ruleSorted` only: the conjunct is carried, so H is any set of symbols.
-/
import KcoreSpec.ModelChoicePP
import KcoreSpec.SatRuleHeld
import KcoreSpec.ModelFnsDecided

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

variable {H : Sym → Bool}

/-- **A `StepVAt` step by a rule is in its disjunct of the closure, at any T.** `closureDisjunct_T`
for a rule with `ruleSorted` and `rulePlainHeldH` (not asked to be one of the definition's), among
rules with those facts: x̄ read as σ off ē. -/
theorem closureDisjunct_held (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainHeldH H r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true) {T : GroundTerm → GroundTerm → Prop}
    {σ : Subst} {x yv : GroundTerm} (hst : StepVAt c r σ x yv) (hx : c.sortOf x = some topCellSort)
    (off : Nat) (y : EVar)
    (hy_ne : ∀ k ∈ List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r),
      y ≠ KoreAML.VarTable.ev (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r)) k)
    (e1 : Valuation Elem) (he1 : e1.evalEvar y = .val yv) :
    (KoreAML.closureDisjunct [] off y (prioRuleK c r)).2.interpret (stdI_T c T) e1 (.val x) := by
  have hn := h.namesK
  obtain ⟨hσ, hmatch, hreq, hpre, heval, hens, hpost, hprio⟩ := hst
  have hnum := rule_vars_numCN h hs
  obtain ⟨L, hPL, hLv, hLf, hLread⟩ := rule_premise_held h hrules hs hp
  let P := prioRuleK c r
  let tbl : KoreAML.VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] P
  have hin_tbl : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ hk))
  have hinL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => hin_tbl k (by
    show _ ∈ KoreAML.varsOf (prioRuleK c r)
    rw [hPL, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk))
  have hinQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => hin_tbl k (by
      show _ ∈ KoreAML.varsOf (prioRuleK c r)
      rw [hPL, KoreAML.varsOf]
      exact List.mem_append_right _ (varsOf_post_ruleRight hs hk))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hinL _ (hLv i hi)
  let nx := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have hnx : ∀ i, i ∈ nx ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by
    simp only [nx, List.mem_filter, List.mem_range, Bool.not_eq_true']
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun hm => by rw [List.contains_iff_mem.mpr hm] at h2; cases h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, Bool.eq_false_iff.mpr (fun hc => h2 (List.contains_iff_mem.mp hc))⟩⟩
  have hk' : ∀ i < r.vars.length, i ∈ nx → canonKey c r.vars i ∈ tbl := fun i hi _ => hkeys i hi
  let f : Nat → Elem := fun j => .val ((σ.lookup j).getD default)
  let e' := setV c tbl r.vars nx f e1
  have hval : ∀ i < r.vars.length, ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hvar : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
    intro i hi hx m
    rw [AtT.var_read]
    show m = (setV c tbl r.vars nx f e1).evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [setV_on hk' hi ((hnx i).mpr ⟨hi, hx⟩)]
    obtain ⟨w, hw, -⟩ := hval i hi
    simp [f, hw]
  have he'y : e'.evalEvar y = .val yv := by
    show (if h : _ then _ else _) = _
    rw [dif_neg]
    · exact he1
    rintro ⟨i, hi, -, he⟩
    exact hy_ne _ (hkeys i hi) he
  have hLx : (KoreAML.tr ⟨tbl, []⟩ L).interpret (stdI_T c T) e' (.val x) :=
    (hLread T tbl e' σ x hinL hx (fun i hi _ => hval i hi) hvar).mpr
      ⟨hmatch, hreq, hpre, hprio, σ, yv, fun _ _ _ => rfl, hσ, heval, hens, hpost⟩
  have hRy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret (stdI_T c T) e' (.val yv) :=
    (ruleRight_read_held h hs hp hkeys hinQ (fun i hi _ => hval i hi) hvar _).mpr
      ⟨σ, yv, fun _ _ _ => rfl, hσ, heval, hens, hpost, rfl⟩
  have hdisj : (KoreAML.closureDisjunct [] off y P).2 =
      ((evarsOf (KoreAML.freeOf [] P).eraseDups).foldr
        (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ)
        (KoreAML.tr ⟨tbl, []⟩ L ⋀ (y ∈∈ KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)))) := by
    unfold KoreAML.closureDisjunct
    simp only [tbl]
    simp only [P, hPL]
    rfl
  rw [hdisj]
  have hfree : ∀ ks ∈ evarsOf (KoreAML.freeOf [] P).eraseDups, ∃ i < r.vars.length, i ∉ r.exs ∧
      ks.1 = canonKey c r.vars i ∧ ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, nm, hnm⟩ := mem_filterMap_evar hks
    obtain ⟨i, hi, hx, he⟩ := freeOf_prio_pp (fun r' hr' => (hrules r' hr').1) hs (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, hx, he, ?_⟩
    rw [he, canonKey_eq c hi] at hnm
    injection hnm with _ h2
    exact h2.symm
  refine sExists_foldr_intro_T _ e1 e' _ (fun z hz => ?_) rfl ?_ ?_
  · show (if h : _ then _ else _) = _
    rw [dif_neg]
    rintro ⟨i, hi, hix, rfl⟩
    obtain ⟨-, hx⟩ := (hnx i).mp hix
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] P := by
      show _ ∈ KoreAML.freeOf [] (prioRuleK c r)
      rw [hPL, KoreAML.freeOf]
      exact List.mem_append_left _ (hLf i hi hx)
    have hks := evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    exact hz _ hks (by rw [canonKey_eq c hi])
  · intro ks hks
    obtain ⟨i, hi, hx, h1, h2⟩ := hfree ks hks
    refine ⟨_, h2, ?_⟩
    rw [h1]
    show InS (stdI_T c T) _ ((setV c tbl r.vars nx f e1).evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [setV_on hk' hi ((hnx i).mpr ⟨hi, hx⟩)]
    obtain ⟨v, hv, hsv⟩ := hval i hi
    show InS (stdI_T c T) _ (Elem.val ((σ.lookup i).getD default))
    rw [hv, Option.getD_some]
    exact (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mpr hsv
  · rw [interpret_conj]
    refine ⟨hLx, ?_⟩
    rw [KoreAML.interp_member AtT.defOK_std, he'y]
    exact hRy

/-- **The step's closure holds in the value model at T** where every T step between configurations
is a `StepV` step (`hsub`): `satStepGoal_T` for rules with `ruleSorted` and `rulePlainHeldH`. -/
theorem satStepGoal_held (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y) :
    stdI_T c T ⊧ᴵP Γstep c := by
  rintro φ rfl
  rw [stepClosure_pat]
  dsimp only
  intro e m
  generalize hy : (⟨tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y
  have hall : ∀ (x : EVar) (φ : KoreAML.P) (e : Valuation Elem) (m : Elem),
      (∀ a, φ.interpret (stdI_T c T) ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m) →
        (∀∀ x φ).interpret (stdI_T c T) e m := by
    intro x φ e m h'
    unfold Pattern.universal
    rw [interpret_neg, interpret_exists]
    rintro ⟨a, ha⟩
    rw [interpret_neg] at ha
    exact ha (h' a)
  refine hall y _ e m fun a => ?_
  let e1 : Valuation Elem := ⟨Function.update e.evalEvar y a, e.evalSvar⟩
  show (KoreAML.sNext (.evar y) ⊆⊆ _ : KoreAML.P).interpret (stdI_T c T) e1 m
  rw [KoreAML.interp_included AtT.defOK_std]
  intro x0 hx0
  unfold KoreAML.sNext at hx0
  rw [KoreAML.interp_app] at hx0
  obtain ⟨a0, b0, ha0, hb0, hab⟩ := hx0
  have ha0' : a0 = .app .next [] := ha0
  subst ha0'
  have hb0a : b0 = e1.evalEvar y := hb0
  have hst : StepE_T c T x0 b0 := hab
  cases x0 with
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim
  | val x =>
  cases b0 with
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim
  | val yv =>
  obtain ⟨hx, hyv, hT⟩ := hst
  obtain ⟨r, σ, hr, hstep⟩ := hsub x yv hx hyv hT
  obtain ⟨hs, hp⟩ := hrules r hr
  obtain ⟨off, hoff, hmem⟩ := stepF_mem y (c.rules.map (prioRuleK c)) ([], [], 0) (prioRuleK c r)
    (List.mem_map.mpr ⟨r, hr, rfl⟩)
  refine AtT.disjList_intro hmem (closureDisjunct_held h hrules hs hp hstep hx off y (fun k hk he => ?_) e1 hb0a.symm)
  have h1 := index_le hk
  have hoff' : off + (KoreAML.tableOf [] (prioRuleK c r)).length ≤ tablesLen (c.rules.map (prioRuleK c)) 0 := hoff
  rw [← he, ← hy] at h1
  have h2 : (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r)).length =
      off + (KoreAML.tableOf [] (prioRuleK c r)).length := by simp
  simp only at h1
  omega

end Model

end Faithful

open ML Faithful Faithful.Model

/-- **The value model at a transition T is a model of `Γc` with the step's closure**, for rules with
`ruleSorted` and `rulePlainHeldH`: `stdI_T_modelCEx` with `StepV` for `StepM` in `hsub` and `StepVBy` for
`StepMBy` in `hall` and `hsome`, and `stdI_T_modelCEx`'s `hl` (the open generators' laws hold in the
value model), where the value model satisfies the functions' equations (`hFns`). -/
theorem stdI_T_model_held_fns (c : Semantics) {H : Sym → Bool} (h : c.coreOK = true) (hm : HypModelCore c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hFns : stdI_T c T ⊧ᴵP ΓFns c)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c) := by
  obtain ⟨hSig, hCons, hDom, hColls, -, hFb, hBool⟩ := model_parts_T hm h hl T hFns
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact hSig φ hφ
    · exact hCons φ hφ
    · exact hDom φ hφ
    · exact hColls φ hφ
    · exact hFns φ hφ
    · exact satRulesGoal_held hm hrules T hall hsome φ hφ
    · exact hFb φ hφ
  · obtain ⟨-, hl, rfl⟩ := hφ
    exact hBool hl
  · exact satStepGoal_held hm hrules T hsub φ hφ

end KCore
