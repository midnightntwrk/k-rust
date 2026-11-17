/-
  KCore. A value in the instances of an application is a step, for rules with `rulePlainHeldH`.

  `famEx_value_held` is `famEx_value_pp` for a rule with `rulePlainHeldH c H`, in a model where
  each symbol of H that is no constructor has `HeldBack`: an existential variable the right side
  holds under H is a value's by `occsUnder_witnessed`; no cut holds an existential variable,
  which is no condition variable. `famEx_values_held` is `famEx_values_pp` from the per-rule
  facts, under `HeldBackAll c H`.
-/
import KcoreSpec.FamExValuesPP
import KcoreSpec.ModelChoiceHeld
import KcoreSpec.HeldBackAll

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

open KoreAML (DefOK VarTable)

open HoldsShape (hasBinder)

section

variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

variable {H : Sym → Bool}

/-- **An instance's value gives a substitution**, in a model of `Γc`: y's element in `famEx c r σ`
gives a σ' that is σ off the existential variables, well sorted, under which the right side
evaluates to y, the `ensures` to `true` and `post` holds. A `post` with a binder asks
`readsConfined`. -/
theorem famEx_value_held (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hrc : r.exs.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) (y : Config c)
    (e : Valuation M) (hm : (famEx c r σ).interpret I e (elemOf c I y.val)) :
    ∃ σ' : Subst, (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
      EvalTerm c σ' r.rhs (some y.val) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
      Holds c r.vars.length σ' r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  have hneg := (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI))
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs, -, hokQ, -, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hfixed : ∀ i, i ∈ (List.range r.vars.length).filter (fun i => !r.exs.contains i) ↔
      i < r.vars.length ∧ i ∉ r.exs := fun i => by simp
  rw [famEx_eqPPx hlt] at hm
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
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => by
      rw [← htbl]
      unfold KoreAML.tableOf
      refine List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx ?_ _))
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      unfold Model.ruleRightBodyPP
      exact Model.varsOf_existsAll_bodyEx (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk) _
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
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c vs r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' (elemOf c I y.val) :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
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
  have hopens : ∀ i ∈ r.opens, (occsUnder c H r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ r.condVars.contains i = true := by
    intro i hi
    rcases Semantics.rulePlainHeldH_opens hp i hi with (hA | hB | hM) | ⟨hC, -⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr (List.contains_iff_mem.mpr
        (List.mem_append_right _ (memHeldH_condVar r.vars.length hM).2)))
    · exact Or.inr (Or.inr (List.contains_iff_mem.mpr hC))
  have hwit : ∀ i < r.vars.length, Witnessed c I tbl vs r.vars e'' i := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]
        exact ⟨hi, by simpa using (hexs i hx).2.1⟩
      rcases hopens i hop with hA | hB | hC
      · exact occsUnder_witnessed hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hback hrhss
          y.property hyR i (List.contains_iff_mem.mp hA)
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
    have hq := hensR
    rw [ht] at hq
    exact evalTrue_of_model h hft hI hcw hσ' hag' (hensS t ht) hq
  -- the right side evaluates to a value whose element is y's: y
  obtain ⟨v, hv⟩ := Model.evalTerm_total hs0 hft fns_headsOK hσ' hrhss
  have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph
    (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ'
    (canonVars_length c r.vars) hag' hrhss _).mp hyR
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ' hrhss rfl
    have h1 : (den c yv).interpret I e (elemOf c I y.val) := ((den_closed c yv).interp e'' e _).mp hbR
    have h2 : elemOf c I y.val = elemOf c I yv := ((elemOf_spec hIΓ hyv e).1 _).mp h1
    have hyy : y.val = yv := values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg y.property) y.property hyv h2
    rw [← hyy] at hv
    exact ⟨σ', hagree, hσ', hv, hensT,
      holds_of_conjPP h hft hI hcw hokQ hbdQ hrcQ hσ' hag' hkeys hkQ (elemOf_top hIΓ y tbl e'') hpostR⟩

end

end Faithful

open ML Faithful Faithful.Model

/-- **A value in the instances of an application is a step by the rule**, for rules with
`ruleSorted` and `rulePlainHeldH` (a `pre` and a `post` allowed): `famEx_values`'s statement from the
per-rule facts. -/
theorem famEx_values_held (c : Semantics) {H : Sym → Bool} (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y := by
  obtain ⟨y₀, hs₀⟩ := hs
  obtain ⟨M, hinh, I, hI, -⟩ := has_model_choice_held c h hf hrules (Step c) (fun _ _ hst => hst)
    (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
  haveI := hinh
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have h1 := hy hIc KoreAML.val0 (elemOf c I y.val)
  rw [interpret_impl] at h1
  have h2 := h1 (((elemOf_spec hIΓ y.property _).1 _).mpr rfl)
  obtain ⟨hsr, hpr⟩ := hrules r hs₀.mem
  obtain ⟨-, -, -, -, -, -, hexs, -, -, -, -⟩ := ruleSorted_partsPP hsr
  have hrc : r.exs.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    have hop : i ∈ r.opens := by
      simp only [Rule.opens, List.mem_filter, List.mem_range]
      exact ⟨(hexs i hi).1, by simpa using (hexs i hi).2.1⟩
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hs₀.mem, by simp [List.ne_nil_of_mem hop]⟩
  obtain ⟨σ', hag, hσ', hev, hens, hpost⟩ :=
    famEx_value_held h hf.1 hIc (hbk I hIc) hf.2.2.2.2.1.2 hsr hpr hrc (readsConfined_of_post hs₀.mem) hs₀.hσ y _ h2
  refine ⟨σ', hag, hs₀.mem, hσ', PatVal.congr_lookup hs₀.hmatch fun j hj => hag j fun hx => (hexs j hx).2.1 hj,
    fun t ht => Exec.EvalTerm.congr (hs₀.hreq t ht) fun j hj => (hag j fun hx => (hexs j hx).2.2 ?_).symm,
    hs₀.hpre.congr_NI fun j hj => (hag j fun hx => (hexs j hx).2.2 (List.mem_append_right _ hj)).symm,
    hev, hens, hpost, hs₀.hprio⟩
  simp only [Rule.condVars, ht, Option.map_some, Option.getD_some, List.mem_append]
  exact Or.inl hj

end KCore
