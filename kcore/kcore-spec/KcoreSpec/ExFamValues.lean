/-
  KCore. A value among the instances of an application, for a rule with existential variables, in
  any model of `Γc c`.

  `famEx c r σ` is `∃ō. (ō = σ(ō) ∧ ∃ē. (rhs ∧ ens))`, ō the variables other than the existential
  ones ē (`famEx_eqEx`). An element m of it is, under the binders, at a valuation that gives each
  variable of ō the element of its value under σ and each of ē an element of its sort, in the
  right side and in `⌈ens = true⌉`. Where m is the element of a value, each existential variable's
  element is a value's: by arm A of `rulePlainEx` the right side holds it under constructors
  (`ctorOccs_witnessed`), by arm B its sort is confined (`confined_value`). So the valuation gives
  every variable the element of a value of its sort; its substitution, beside σ off the rule's
  variables, agrees with σ off ē, is well sorted, makes the `ensures` `true`, and evaluates the right
  side to a value whose element is m: that value is m's (`famEx_value_ex`).

  `famEx_values_ex` is `famEx_values`' conclusion: read in the value model (`stdI_model_ex`), a
  configuration y entailed in `famEx c r σ` for a step by r under σ is the right side at a σ' that
  differs from σ at ē only; the left side, the `requires` and the competitors do not read ē, so
  `StepBy c r σ' x y`.
-/
import KcoreSpec.ExChoice
import KcoreSpec.OpenFamOpen
import KcoreSpec.OpenRuleStepCl
import KcoreSpec.RhsValues
import KcoreSpec.Totals

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule whose `post` is `\top`: the variables other than the
existential ones bound and fixed to their values under σ, the right side `∃ē. (rhs ∧ ens)`. -/
theorem famEx_eqEx {r : Rule} (hpost : r.post = .top) (hlt : ∀ i ∈ r.exs, i < r.vars.length) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
        fun i => ((canonVars c r.vars).getD i default).kore)
      (.and (srtOf c topCellSort) (fixK c r σ ((List.range r.vars.length).filter fun i => !r.exs.contains i) ++
        [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBody c r)]))) := by
  unfold famEx
  dsimp only
  rw [Model.ruleRight_eqEx hpost hlt, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1), List.map_map]
  rfl

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A value among the instances of an application is the right side at an extension of σ on
the existential variables**, in a model of `Γc`, for a rule with `ruleSorted` and `rulePlainEx`
(not asked to be one of the definition's), where every function has a result at arguments of its
sorts: a configuration y whose element is in `famEx c r σ`, σ well sorted, is the right side's
value under a well-sorted σ' that differs from σ at the existential variables only, with a true
`ensures`. `hrc`: that the definition reads a confined sort where an existential variable is of
one. -/
theorem famEx_value_ex (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
    (hrc : r.exs.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) (y : Config c)
    (e : Valuation M) (hm : (famEx c r σ).interpret I e (elemOf c I y.val)) :
    ∃ σ' : Subst, (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
      EvalTerm c σ' r.rhs (some y.val) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  have hneg := (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI))
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨-, hpost₀⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hfixed : ∀ i, i ∈ (List.range r.vars.length).filter (fun i => !r.exs.contains i) ↔
      i < r.vars.length ∧ i ∉ r.exs := fun i => by simp
  rw [famEx_eqEx hpost₀ hlt] at hm
  unfold KoreAML.denB at hm
  generalize htbl : KoreAML.tableOf [] _ = tbl at hm
  -- every variable of the rule has its key in the table
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := by
    intro i hi
    rw [← htbl]
    unfold KoreAML.tableOf
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    by_cases hx : i ∈ r.exs
    · refine Model.varsOf_existsAll_bodyEx ?_ _
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx)
    · exact varsOf_existsAll_binder _
        (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩))
  have hsortB : ∀ i < r.vars.length,
      (vs.getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    show ((canonVars c r.vars).getD i default).kore.sort = _
    rw [canonVars_getD c hi]; rfl
  have hinjB : ∀ {l : List Nat}, (∀ i ∈ l, i < r.vars.length) → l.Nodup →
      ((l.map fun i => (vs.getD i default).kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    intro l hl hnd
    rw [List.map_map]
    refine List.pairwise_map.mpr (hnd.imp_of_mem fun {i j} hi hj hne he => hne ?_)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi)) (hkeys j (hl j hj)) he)
  -- the binders of the variables other than the existential ones
  obtain ⟨e', -, hguard1, hb⟩ := existsAll_elim hD _ e _
    (hinjB (fun i hi => ((hfixed i).mp hi).1) (List.nodup_range.filter _))
    (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i ((hfixed i).mp hi).1⟩) hm
  rw [interp_and (by simp)] at hb
  have hinner := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
  -- the binders of the existential variables
  obtain ⟨e'', hoff, hguard2, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' _
    (hinjB hlt hexnd) (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i (hlt i hi)⟩)
    hinner
  unfold Model.ruleRightBody at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  -- off the existential variables, e'' is e'
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      e''.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have := canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)
    exact hx (this ▸ hj)
  -- the variables other than the existential ones are the elements of their values under σ
  have hfix : ∀ i < r.vars.length, i ∉ r.exs → ∃ g, σ.lookup i = some g ∧ c.sortOf g = some (r.vars.getD i 0) ∧
      elemOf c I g = e''.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hi hx
    have hsi : r.vars[i]? = some (r.vars.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    obtain ⟨g, hg', hgs⟩ := hσ i _ hsi
    refine ⟨g, hg', hgs, ?_⟩
    have hvi : (canonVars c r.vars)[i]? = some ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hpm : Kore.Pattern.equals (srtOf c (r.vars.getD i 0)) (srtOf c topCellSort)
        (.var (.evar ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)).kore)) (g.kore c) ∈
        fixK c r σ ((List.range r.vars.length).filter fun i => !r.exs.contains i) := by
      unfold fixK
      refine List.mem_filterMap.mpr ⟨i, (hfixed i).mpr ⟨hi, hx⟩, ?_⟩
      simp only [hvi, hsi, hg']
    have hx' := ((fixEq_iff hIΓ (sortOf_numbered_of hs0 (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hgs)
      hgs _).mp (hb _ (List.mem_append_left _ hpm))).2
    rw [hoffE i hi hx]
    show elemOf c I g = e'.evalEvar (tbl.ev (KoreAML.evarKey ((canonVars c r.vars).getD i default).kore))
    rw [List.getD_eq_getElem?_getD, hvi, Option.getD_some, hx']
  -- every variable's element is in its sort
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard2 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx) _ (hsortB i hi)
    · rw [hoffE i hi hx]
      exact hguard1 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩)) _
        (hsortB i hi)
  -- every variable is the element of a value of its sort: an existential one by arm A or B
  have hopens : ∀ i ∈ r.opens, (ctorOccs c r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ r.condVars.contains i = true := by
    intro i hi
    have hp' := hp
    simp only [Semantics.rulePlainEx, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp'
    rcases hp'.2.1 i hi with (hA | hB) | ⟨hC, -⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr hC)
  have hwit : ∀ i < r.vars.length, Witnessed c I tbl vs r.vars e'' i := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]
        exact ⟨hi, by simpa using (hexs i hx).2.1⟩
      rcases hopens i hop with hA | hB | hC
      · exact ctorOccs_witnessed hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hrhss
          y.property hbody.1 i (List.contains_iff_mem.mp hA)
      · obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
        rw [hvs] at hB
        have hcs' : c.confined s = true := hB
        have hrc' := hrc (List.any_eq_true.mpr ⟨i, hx, by rw [hvs]; exact hB⟩)
        have hin' := hin i hi
        rw [List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
        obtain ⟨v, hv, hden⟩ := confined_value h hrc' hI hcs' e'' _ ((inS_iff e'').mpr hin')
        have hel := ((elemOf_spec hIΓ hv e'').1 _).mpr rfl
        exact witnessed_of hvs hv ((hden _).mp hel)
      · exact absurd (List.contains_iff_mem.mp hC) (hexs i hx).2.2
    · obtain ⟨g, -, hgs, hge⟩ := hfix i hi hx
      exact ⟨g, hgs, hge⟩
  -- the substitution: the valuation's on the rule's variables, σ beyond them
  let σ₀ := substOf c I tbl vs r.vars e''
  obtain ⟨hσ₀, hag₀⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  have hkeys₀ : ∀ i, i ∈ σ₀.map (·.1) ↔ i < r.vars.length := fun i => by simp [σ₀, substOf]
  let σ' := σ₀ ++ σ
  have hlk : ∀ i < r.vars.length, σ'.lookup i = σ₀.lookup i := fun i hi =>
    lookup_append_of_mem σ₀ σ ((hkeys₀ i).mpr hi)
  have hσ' : c.WellSorted r.vars σ' := fun i s hi => by
    rw [hlk i (List.getElem?_eq_some_iff.mp hi).1]; exact hσ₀ i s hi
  have hag' : Agrees c I tbl vs σ' e'' := fun i v hi hv => by
    rw [hlk i (by rw [canonVars_length] at hi; exact hi)] at hv
    exact hag₀ i v hi hv
  have hagree : ∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i := by
    intro i hx
    by_cases hi : i < r.vars.length
    · rw [hlk i hi]
      obtain ⟨g, hg', hgs, hge⟩ := hfix i hi hx
      rw [hg']
      exact substOf_var hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
        (List.getElem?_eq_getElem hi)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hgs; exact hgs) hge
    · exact lookup_append_of_not_mem σ₀ σ (fun hm' => hi ((hkeys₀ i).mp hm'))
  -- the `ensures` holds, so it evaluates to `true`
  have hensT : ∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true)) := by
    intro t ht
    have hq := hbody.2
    rw [ht] at hq
    exact evalTrue_of_model h hft hI hcw hσ' hag' (hensS t ht) hq
  -- the right side evaluates to a value whose element is y's: y
  obtain ⟨v, hv⟩ := Model.evalTerm_total hs0 hft fns_headsOK hσ' hrhss
  have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph
    (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ'
    (canonVars_length c r.vars) hag' hrhss _).mp hbody.1
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ' hrhss rfl
    have h1 : (den c yv).interpret I e (elemOf c I y.val) := ((den_closed c yv).interp e'' e _).mp hbR
    have h2 : elemOf c I y.val = elemOf c I yv := ((elemOf_spec hIΓ hyv e).1 _).mp h1
    have hyy : y.val = yv := values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg y.property) y.property hyv h2
    rw [← hyy] at hv
    exact ⟨σ', hagree, hσ', hv, hensT⟩

end

end Faithful

open ML Faithful Faithful.Model

/-- **A value in the instances of an application is a step by it**, for a semantics that `coreOK`
accepts whose functions meet `FnHyp` and whose rules have `ruleSorted` and `rulePlainEx`:
`famEx_values`' conclusion. Read in the value model (`stdI_model_ex`), y is the right side at a σ'
that differs from σ at the existential variables only (`famEx_value_ex`); the left side, the
`requires` and the competitors do not read them. -/
theorem famEx_values_ex (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y := by
  obtain ⟨y₀, hs₀⟩ := hs
  have hI := stdI_model_ex c h (hypModel_of_fnHyp h hf) (clausePreDecided_of_fnHyp h hf) hf.2.2.2.2.2 hrules
  have hIc : stdI c ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : stdI c ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have h1 := hy hIc KoreAML.val0 (elemOf c (stdI c) y.val)
  rw [interpret_impl] at h1
  have h2 := h1 (((elemOf_spec hIΓ y.property _).1 _).mpr rfl)
  obtain ⟨hsr, hpr⟩ := hrules r hs₀.mem
  obtain ⟨hpre, hpost⟩ := Semantics.rulePlainEx_top hpr
  obtain ⟨-, -, -, -, -, -, hexs⟩ := ruleSorted_partsEx hsr hpr
  have hrc : r.exs.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    have hop : i ∈ r.opens := by
      simp only [Rule.opens, List.mem_filter, List.mem_range]
      exact ⟨(hexs i hi).1, by simpa using (hexs i hi).2.1⟩
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hs₀.mem, by simp [List.ne_nil_of_mem hop]⟩
  obtain ⟨σ', hag, hσ', hev, hens⟩ :=
    famEx_value_ex h hf.1 hIc hf.2.2.2.2.1.2 hsr hpr hrc hs₀.hσ y _ h2
  refine ⟨σ', hag, hs₀.mem, hσ', PatVal.congr_lookup hs₀.hmatch fun j hj => hag j fun hx => (hexs j hx).2.1 hj,
    fun t ht => Exec.EvalTerm.congr (hs₀.hreq t ht) fun j hj => (hag j fun hx => (hexs j hx).2.2 ?_).symm,
    hpre ▸ .top, hev, hens, hpost ▸ .top, hs₀.hprio⟩
  simp only [Rule.condVars, ht, Option.map_some, Option.getD_some, List.mem_append]
  exact Or.inl hj

end KCore
