/-
  KCore. The outcomes of a match of a rule that may have existential variables, its open variables
  of confined sorts, in any model of `Γc c`.

  `famOpen c r σ` binds the variables other than the existential ones; the existential ones are
  bound by `∃ē` in r's right side `∃ē. (rhs ∧ ens)` (`famOpen_eqEx`). An element m of it is, under
  both groups of binders, at a valuation that gives every variable of r an element of its sort, the
  variables of the left side the elements of their values under σ (the left side holds no
  existential variable), m in `⌈req = true⌉` (which holds none either), in `rhs` and in
  `⌈ens = true⌉`. Every variable outside the left side, an existential one included, is open, so of
  a confined sort, and its element is a value's (`confined_value`). So, as for a rule without
  existential variables, the valuation's substitution σ' agrees with σ on the left side's variables,
  matches x, makes the conditions `true`, and the right side evaluates under it to a value whose
  element is m (`famOpen_stepEx`). For a rule of the definition with an unblocked match σ, that is
  a step `StepBy c r σ' x y` (`famOpen_values_ex`).
-/
import KcoreSpec.ExComplete
import KcoreSpec.OpenFamOpen

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An outcome of a match is a step's successor, at values**, for a rule with `ruleSorted` and
`rulePlainEx` (not asked to be one of the definition's) whose open variables are of confined sorts:
in a model of `Γc`, an element of `famOpen c r σ`, σ well sorted on the left side's variables and
matching x, is the element of a configuration y that is the right side's value under a σ' that
agrees with σ on the left side's variables and has every premise of `StepBy c r σ' x y` but the
rule's membership and `hprio`. -/
theorem famOpen_stepEx (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
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
  obtain ⟨hlhs, -, hreqs, hensS, hrhss, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨hpre₀, hpost₀⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hfixed : ∀ i, i ∈ (List.range r.vars.length).filter (fun i => !r.exs.contains i) ↔
      i < r.vars.length ∧ i ∉ r.exs := fun i => by simp
  -- the left side's and the `requires`' variables are not existential
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  rw [famOpen_eqEx hpre₀ hpost₀ hlt σ] at hm
  unfold KoreAML.denB at hm
  generalize htbl : KoreAML.tableOf [] (famOpenPatEx c r σ) = tbl at hm
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => by
    rw [← htbl]; exact famOpen_keysEx i hi
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
  have hreqm := hb _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hinner := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
  -- the binders of the existential variables
  obtain ⟨e'', hoff, hguard2, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' m
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
      hgs m).mp (hb _ (List.mem_append_left _ (List.mem_append_left _ hpm)))).2
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
    have hq := hbody.2
    rw [ht] at hq
    exact evalTrue_of_model h hft hI hcw hσ' hag (hensS t ht) hq
  -- the right side evaluates to a value whose element is m
  obtain ⟨v, hv⟩ := Model.evalTerm_total hs0 hft fns_headsOK hσ' hrhss
  have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
    hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ' (canonVars_length c r.vars) hag hrhss m).mp hbody.1
  cases v with
  | none => exact hbR.elim
  | some yv =>
    exact ⟨⟨yv, EvalTerm.sorted hsc hv fns_headsOK hσ' hrhss rfl⟩, σ', hagL, hσ', hmatch', hreqT, hpre₀ ▸ .top, hv,
      hensT, hpost₀ ▸ .top, ((den_closed c yv).interp e'' e m).mp hbR⟩

end

end Faithful

open ML Faithful

/-- **The outcomes of a match are, in every model, among any values that hold its steps**, for a
rule of the definition with `ruleSorted` and `rulePlainEx` whose open variables are of confined
sorts: `famOpen_values`' conclusion, from `famOpen_stepEx`. That the definition reads a confined
sort is read from the rule (an open variable). -/
theorem famOpen_values_ex (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
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
    famOpen_stepEx h hf.1 hI hf.2.2.2.2.1.2 hs hp hcf hrc hσat hmatch e m hm
  exact disjList_of_mem (List.mem_map_of_mem (hys y ⟨σ', hagL, ⟨hr, hσ', hm', hrq, hpr, hev, hen, hpo, hprio⟩⟩)) hy

end KCore
