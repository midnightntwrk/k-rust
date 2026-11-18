/-
  KCore. The outcomes of a match of a rule with a `pre` and a `post` are among any values that hold
  its steps.

  `famOpen c r σ` is `∃v̄. (l̄ = ⟦σ⟧ ∧ ⌈req = true⌉ ∧ pre ∧ ∃ē. (rhs ∧ ⌈ens = true⌉ ∧ post))`, l̄ the
  variables of the left side (`famOpen_eqPP`). In a model of `Γc`, an element m in it gives a
  valuation of the rule's variables in their sorts; an open variable is of a confined sort (`hcf`),
  so it is the element of a value, and the valuation is a substitution σ' that is σ on the left
  side, under which the `requires` and `ensures` evaluate to `true` and the right side to a value y
  whose pattern holds m (`FnTerminates`). m is in the configuration sort (the `requires` conjunct),
  and a condition's patterns hold at an element of that sort exactly where `Holds` says `true`
  (`holds_of_conjPP`): `pre`, moved inside the binder of ē, which it does not read (`conj_congrPP`),
  and `post` (`famOpen_stepPP`).

  `famOpen_values_pp` is `famOpen_values`'s statement for a rule with `ruleSorted`; `rulePlainPP`
  is not read, and is not a hypothesis.
-/
import KcoreSpec.CompletePP
import KcoreSpec.ExFamOpen
import KcoreSpec.OpenSplit

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An element of an open family is a successor's**, in a model of `Γc`, for a rule with
`ruleSorted` whose open variables are of confined sorts, whatever its predicates: m in
`famOpen c r σ` gives a configuration y whose pattern holds m and a σ' that is σ on the left side,
with every premise of `StepBy c r σ' x y` but the rule's membership and the competitors,
`Holds … pre true` and `Holds … post true` included. A binder in a predicate asks
`readsConfined`. -/
theorem famOpen_stepPP (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {x : Config c} {σ : Subst} (hσ : c.WellSortedAt r.vars (varOccs r.lhs) σ) (hmatch : PatVal c σ r.lhs x.val)
    (e : Valuation M) (m : M) (hm : (famOpen c r σ).interpret I e m) :
    ∃ (y : Config c) (σ' : Subst), (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧
      c.WellSorted r.vars σ' ∧ PatVal c σ' r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ' t (some (bool true))) ∧
      Holds c r.vars.length σ' r.pre true ∧ EvalTerm c σ' r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧ Holds c r.vars.length σ' r.post true ∧
      (den c y.val).interpret I e m := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  have hneg := (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI))
  obtain ⟨hlhs, -, hreqs, hensS, hrhss, hexnd, hexs, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hfixed : ∀ i, i ∈ (List.range r.vars.length).filter (fun i => !r.exs.contains i) ↔
      i < r.vars.length ∧ i ∉ r.exs := fun i => by simp
  -- the left side's and the `requires`' variables are not existential
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hnxP : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi)⟩
  rw [famOpen_eqPP hlt σ] at hm
  unfold KoreAML.denB at hm
  obtain ⟨hkeys, hkP, hkQ⟩ := famOpen_keysPP (c := c) (r := r) (σ := σ)
  generalize KoreAML.tableOf [] (famOpenPatPP c r σ) = tbl at hm hkeys hkP hkQ
  unfold famOpenPatPP at hm
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
  obtain ⟨e', -, hguard1, hb⟩ := existsAll_elim hD _ e m
    (hinjB (fun i hi => ((hfixed i).mp hi).1) (List.nodup_range.filter _))
    (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i ((hfixed i).mp hi).1⟩) hm
  rw [interp_and (by simp)] at hb
  have hreqm := hb _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))
  have hprem : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' m :=
    fun φ hφ => hb φ (List.mem_append_left _ (List.mem_append_right _ hφ))
  have hinner := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
  -- the binders of the existential variables
  obtain ⟨e'', hoff, hguard2, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' m
    (hinjB hlt hexnd) (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i (hlt i hi)⟩)
    hinner
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c vs r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' m :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  -- off the existential variables, e'' is e'
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      e''.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have := canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)
    exact hx (this ▸ hj)
  -- every variable's element is in its sort
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard2 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx) _ (hsortB i hi)
    · rw [hoffE i hi hx]
      exact hguard1 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩)) _
        (hsortB i hi)
  -- the left side's variables are the elements of their values under σ
  have hfix : ∀ i ∈ varOccs r.lhs, ∃ g, σ.lookup i = some g ∧ c.sortOf g = some (r.vars.getD i 0) ∧
      elemOf c I g = e''.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hiL
    obtain ⟨hi, hx⟩ := hnxL i hiL
    have hsi : r.vars[i]? = some (r.vars.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    obtain ⟨g, hg', hgs⟩ := hσ i hiL _ hsi
    refine ⟨g, hg', hgs, ?_⟩
    have hvi : (canonVars c r.vars)[i]? = some ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hpm : Kore.Pattern.equals (srtOf c (r.vars.getD i 0)) (srtOf c topCellSort)
        (.var (.evar ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)).kore)) (g.kore c) ∈
        fixK c r σ (varOccs r.lhs) := by
      unfold fixK
      refine List.mem_filterMap.mpr ⟨i, hiL, ?_⟩
      simp only [hvi, hsi, hg']
    have hx' := ((fixEq_iff hIΓ (sortOf_numbered_of hs0 (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hgs)
      hgs m).mp (hb _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hpm))))).2
    rw [hoffE i hi hx]
    show elemOf c I g = e'.evalEvar (tbl.ev (KoreAML.evarKey ((canonVars c r.vars).getD i default).kore))
    rw [List.getD_eq_getElem?_getD, hvi, Option.getD_some, hx']
  -- every variable is the element of a value of its sort: one outside the left side is open, so of
  -- a confined sort
  have hwit : ∀ i < r.vars.length, Witnessed c I tbl vs r.vars e'' i := by
    intro i hi
    by_cases hiL : i ∈ varOccs r.lhs
    · obtain ⟨g, -, hgs, hge⟩ := hfix i hiL
      exact ⟨g, hgs, hge⟩
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hiL⟩
      obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
      have hB := hcf i hop
      rw [hvs] at hB
      have hcs' : c.confined s = true := hB
      have hrc' := hrc (List.any_eq_true.mpr ⟨i, hop, by rw [hvs]; exact hB⟩)
      have hin' := hin i hi
      rw [List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
      obtain ⟨v, hv, hden⟩ := confined_value h hrc' hI hcs' e'' _ ((inS_iff e'').mpr hin')
      have hel := ((elemOf_spec hIΓ hv e'').1 _).mpr rfl
      exact witnessed_of hvs hv ((hden _).mp hel)
  let σ' := substOf c I tbl vs r.vars e''
  obtain ⟨hσ', hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  -- σ' is σ on the left side's variables
  have hagL : ∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i := by
    intro i hiL
    obtain ⟨g, hg', hgs, hge⟩ := hfix i hiL
    have hi := (hnxL i hiL).1
    rw [hg']
    exact substOf_var hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
      (List.getElem?_eq_getElem hi) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hgs; exact hgs)
      hge
  have hmatch' : PatVal c σ' r.lhs x.val := PatVal.congr_lookup hmatch hagL
  -- the conditions hold, so they evaluate to `true`
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e'' m :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl e'')
  have hreqT : ∀ t, r.req = some t → EvalTerm c σ' t (some (bool true)) := by
    intro t ht
    have hq := hreqR
    rw [ht] at hq
    exact evalTrue_of_model h hft hI hcw hσ' hag (hreqs t ht) hq
  have hensT : ∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true)) := by
    intro t ht
    have hq := hensR
    rw [ht] at hq
    exact evalTrue_of_model h hft hI hcw hσ' hag (hensS t ht) hq
  -- `pre` and `post` hold at m, an element of the configuration sort: they hold at σ'
  have hinC : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e'' m :=
    reqPat_inhSplit hIΓ hreqm tbl e''
  have hpreR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' m :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hnxP i hi).1)
      (fun i hi => (hoffE i (hnxP i hi).1 (hnxP i hi).2).symm) hprem
  have hpreT : Holds c r.vars.length σ' r.pre true :=
    holds_of_conjPP h hft hI hcw hokP hbdP hrcP hσ' hag hkeys hkP hinC hpreR
  have hpostT : Holds c r.vars.length σ' r.post true :=
    holds_of_conjPP h hft hI hcw hokQ hbdQ hrcQ hσ' hag hkeys hkQ hinC hpostR
  -- the right side evaluates to a value whose element is m
  obtain ⟨v, hv⟩ := Model.evalTerm_total hs0 hft fns_headsOK hσ' hrhss
  have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
    hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ' (canonVars_length c r.vars) hag hrhss m).mp hyR
  cases v with
  | none => exact hbR.elim
  | some yv =>
    exact ⟨⟨yv, EvalTerm.sorted hsc hv fns_headsOK hσ' hrhss rfl⟩, σ', hagL, hσ', hmatch', hreqT, hpreT, hv,
      hensT, hpostT, ((den_closed c yv).interp e'' e m).mp hbR⟩

end

end Faithful

open ML Faithful Faithful.Model

/-- **The outcomes of a match are among any values that hold its steps**, for a rule with a `pre`
and a `post`: `famOpen_values`'s statement from `ruleSorted` of the rule. -/
theorem famOpen_values_pp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (hs : c.ruleSorted r = true)
    (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys) :
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) := by
  have hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hr, by simp [List.ne_nil_of_mem hi]⟩
  intro M _ I hI e m
  rw [interpret_impl]
  intro hm
  obtain ⟨hσat, hmatch, hprio⟩ := hu
  obtain ⟨y, σ', hagL, hσ', hm', hrq, hpr, hev, hen, hpo, hy⟩ :=
    famOpen_stepPP h hf.1 hI hf.2.2.2.2.1.2 hs hcf hrc (readsConfined_of_pre hr) (readsConfined_of_post hr)
      hσat hmatch e m hm
  exact disjList_of_mem (List.mem_map_of_mem (hys y ⟨σ', hagL, ⟨hr, hσ', hm', hrq, hpr, hev, hen, hpo, hprio⟩⟩)) hy

end KCore
