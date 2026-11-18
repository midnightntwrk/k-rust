/-
  KCore. Soundness at a step by a rule whose left side need not bind every variable, in any model
  of `Γc c`.

  A step `StepBy c r σ x y` gives every variable of r a value (`WellSorted r.vars σ`). At the
  valuation that gives each of r's variables the element of its value, x's element is in the left
  part of r's axiom: in the left side and `⌈req = true⌉` (`patVal_den4`, `reqPat_holds`), in
  `⌈right⌉`, and in no competitor's `applies`. A competitor r' does not apply at values
  (`hprio`); where its `applies` held in the model, the left side of r' would match x
  (`applies_matchOpen`), so the condition on its closed open conditions is asked only of a
  competitor that matches x (`not_applies_guardedOpen`, from `not_applies_of_notApplies`). So the
  axiom gives x's element a successor in r's right side, the element of y (`successor_of_axiomOpen`,
  `step_soundOpen`). The instances of the step, `famEx c r σ`, are y's element, every variable being
  fixed (`famEx_denOpen`). `sound_at_open` is `sound_at`'s conclusion, for a definition whose rules
  have `ruleSorted` and `rulePlainOpen`.
-/
import KcoreSpec.OpenSplit

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## The instances of a step -/

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule with `rulePlainOpen` (not asked to be one of the
definition's): every variable is fixed to its value under σ. -/
theorem famEx_eqOpen {r : Rule} (hp : c.rulePlainOpen r = true) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (List.range r.vars.length) ++
        [.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]]))) := by
  obtain ⟨hex, -, hpost⟩ := Semantics.rulePlainOpen_top hp
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famEx, ruleRight, hex, hpost, List.contains_nil, Bool.not_false, Cond.conj, Cond.isTop, ite_true,
    List.filterMap_nil, List.foldr_nil, List.append_nil]
  rw [hf, hv]

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The instances of a step are its successor**, in every model of `Γc`, for a rule with
`ruleSorted` and `rulePlainOpen` (not asked to be one of the definition's), at a σ that gives every
variable a value, under which the right side evaluates to y and the `ensures` to `true`. -/
theorem famEx_denOpen (h : c.coreOK = true) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainOpen r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {y : Config c}
    (heval : EvalTerm c σ r.rhs (some y.val)) (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) (e : Valuation M) (m : M) :
    (famEx c r σ).interpret I e m ↔ (den c y.val).interpret I e m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hIc))
  obtain ⟨-, -, -, hensS, hrhss⟩ := Model.ruleSorted_partsOpen hs hp
  have hsorts := sortsNumbered_of_core h
  have hov := Semantics.coreOK_ovls h
  rw [famEx_eqOpen hp]
  unfold KoreAML.denB
  generalize htbl : KoreAML.tableOf [] _ = tbl
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => by
    rw [← htbl]; exact canonKey_mem_existsAll hi
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  constructor
  · intro hm
    obtain ⟨e', -, -, hb⟩ := existsAll_elim hD _ e m hnd hsrt hm
    rw [interp_and (hne _ _)] at hb
    have hag := agrees_of_fixK hI hs0 hsorts hov hσ (is := List.range r.vars.length)
      (fun i hi => List.mem_range.mpr hi) (fun p hp => hb p (List.mem_append_left _ hp))
    have hRm := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [tr_and2, KoreAML.interp_sAnd] at hRm
    have := (evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag
      hrhss m).mp hRm.1
    exact ((den_closed c y.val).interp e' e m).mp this
  · intro hm
    have hmy : m = elemOf c I y.val := ((elemOf_spec hI y.property e).1 m).mp hm
    have hag := overV_agrees hI hkeys hσ (e := e)
    refine existsAll_intro_at hD _ e (overV c I tbl r.vars σ e) m hnd hsrt (fun z hz => ?_) rfl
      (fun b hb n hn => ?_) ?_
    · refine overV_off fun i hi he => hz _ ?_ he
      have hlt : i < (canonVars c r.vars).length := by rw [canonVars_length]; exact hi
      show ((canonVars c r.vars).getD i default).kore ∈ (canonVars c r.vars).map KoreAML.Var.kore
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    · obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
      have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
        rw [canonVars_getD c hi]; rfl
      rw [hs'] at hn
      rw [← srt_inj hn]
      show InS I _ ((overV c I tbl r.vars σ e).evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [overV_at hkeys hi]
      obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
      rw [hw]
      exact (inS_iff e).mp (elemOf_spec hI hsw e).2
    · have hinC : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I
          (overV c I tbl r.vars σ e) m := by
        rw [hmy]
        have := (elemOf_spec hI y.property (overV c I tbl r.vars σ e)).2
        unfold srtOf; rw [trSort_srt]; exact this
      rw [interp_and (hne _ _)]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold fixK at hp
        obtain ⟨i, -, hpi⟩ := List.mem_filterMap.mp hp
        split at hpi
        · rename_i v s g hv hsi hg'
          cases hpi
          have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
          obtain ⟨w, hw, hsw⟩ := hσ i s hsi
          rw [hg'] at hw; cases hw
          refine (fixEq_iff hI (sortOf_numbered_of hs0 hsorts hov hsw) hsw m).mpr ⟨hinC, ?_⟩
          have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
            unfold canonKey
            rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
          rw [hvk, overV_at hkeys hi, hg', Option.getD_some]
        · cases hpi
      · rw [List.mem_singleton.mp hp, tr_and2, KoreAML.interp_sAnd]
        refine ⟨(evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag
          hrhss m).mpr (((den_closed c y.val).interp e _ m).mp hm), reqPat_holds hI (fun t ht b =>
            evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag
              (hensS t ht) b) hinC⟩

end


/-! ## A competitor whose `applies` holds matches -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A rule whose `applies` holds at x's element has a left side that matches x**, in a model of
`Γ`, for a rule with `ruleSorted` and `rulePlainOpen`. -/
theorem applies_matchOpen (h : c.coreOK = true) (hIΓ : I ⊧ᴵP Γ c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) {x : Config c}
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation M)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val)) :
    ∃ σ', PatVal c σ' r.lhs x.val := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hpre, -⟩ := Semantics.rulePlainOpen_top hp
  let vs := canonVars c r.vars
  let n := r.vars.length
  let C := srtOf c topCellSort
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  rw [applies_eq hpre] at hm
  change (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll C ((l.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))]))).interpret I e (elemOf c I x.val) at hm
  rw [hbs] at hm
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  obtain ⟨e', -, hguard, hbody⟩ := existsAll_elim hD _ e _ hnd hsrt hm
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  have hinL : ∀ i < n, i ∈ r.leftVars → InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi hil => hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
      (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  -- the other variables: the configuration sort and x's element
  let e1 := fillV c tbl r.vars r.leftVars (elemOf c I x.val) e'
  have hoff1 : ∀ i < n, i ∈ r.leftVars → e1.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  have hvsl : vs.length = r.leftSorts.length := by rw [canonVars_length, Rule.leftSorts_length]
  have hin1 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e1.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi => by
      rw [Rule.leftSorts_length] at hi
      by_cases hil : i ∈ r.leftVars
      · rw [Rule.leftSorts_getD hi hil, hoff1 i hi hil]; exact hinL i hi hil
      · have hw : Witnessed c I tbl vs r.leftSorts e1 i :=
          ⟨x.val, by rw [Rule.leftSorts_getD_off hi hil]; exact x.property, (fillV_on hi hil).symm⟩
        obtain ⟨v, hv, he⟩ := hw
        rw [← he]; exact (inS_iff e1).mp (elemOf_spec hIΓ hv e1).2
  have hlhsL : ∀ i ∈ varOccs r.lhs, i ∈ r.leftVars := fun i hi => List.mem_append_left _ hi
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := Exec.sortOfTerm_vars hlhs
  have hlx1 := (tr_kore_congr r.lhs (fun i hi => (hoff1 i (hltL i hi) (hlhsL i hi)).symm) _).mp hbody.1
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact hlhs
  obtain ⟨hpv, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPat_of_sorted hph' hlhs')
    (OvlOK.nf_bridge inferInstance hlhs') x.property hlx1
  exact ⟨_, hpv⟩

/-- **A competitor that does not apply does not apply in a model of `Γc`**, the condition on its
closed open conditions asked only where its left side matches x: `not_applies_of_notApplies`, its
`applies` holding only where the left side matches (`applies_matchOpen`). -/
theorem not_applies_guardedOpen (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    {x : Config c} (hw : r.needsWitness c = true → (∃ σ', PatVal c σ' r.lhs x.val) → r.CondDecided c)
    (hna : NotApplies c r x.val)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := fun hm =>
  not_applies_of_notApplies h hI hcw hs hp hlarger hrc
    (fun hn => hw hn (applies_matchOpen h (fun φ hφ => hI φ (Or.inl hφ)) hs hp hkeys e hm)) hna hkeys e hm

end


/-! ## The successor a rule's axiom gives -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A rule's axiom, read in a model**, for a rule with `ruleSorted` and `rulePlainOpen` whose
axiom the model satisfies (not asked to be one of the definition's), whatever its left part `L`: at a
σ that gives every variable a value, where x's element is in `L` under every valuation that agrees
with σ, x has y as a successor. -/
theorem successor_of_axiomOpen (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat)
    {L : Kore.Pattern}
    (hpat : prioRuleK c r = .rewrites (srtOf c topCellSort) L
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]))
    (hVin : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L)
    (hfree : ∀ k ∈ KoreAML.freeOf [] L, ∃ i < r.vars.length, k = canonKey c r.vars i)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {x y : Config c} (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hL : ∀ (tbl : VarTable) (e : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) →
      Agrees c I tbl (canonVars c r.vars) σ e →
      (∀ b, (KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))])).interpret I e b ↔
          (den c y.val).interpret I e b) →
      (KoreAML.tr ⟨tbl, []⟩ L).interpret I e (elemOf c I x.val))
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (den c y.val)).interpret I e m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hIc))
  have hD := defOK hI
  obtain ⟨-, -, -, hensS, hrhss⟩ := Model.ruleSorted_partsOpen hs hp
  rw [hpat] at hax
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let ax : Kore.Axiom :=
    { sortVars := [], pattern := .rewrites C L (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]),
      attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  let e' : Valuation M := valOf tbl (ruleVal c I r.vars.length σ)
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hVmem : ∀ i, i < r.vars.length → canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hVin i hi)
  have hVv : ∀ i, i < r.vars.length → e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      (match σ.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [ruleVal]
    rw [varIdx_eq hi]
    all_goals rfl
  have hvsort : ∀ i, i < r.vars.length → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  -- the free variables of the right side are the rule's
  have hfreeR : ∀ k, k ∈ KoreAML.freeOf [] (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) →
      ∃ i, i < r.vars.length ∧ k = canonKey c r.vars i := by
    intro k hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs r.rhs hk
      exact ⟨i, varOccs_lt r.rhs hrhss i hi, rfl⟩
    · cases hq : r.ens with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t hk
          exact ⟨i, varOccs_lt t (hensS t hq) i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
  have hfree' : ∀ k, k ∈ KoreAML.freeOf [] ax.pattern → ∃ i, i < r.vars.length ∧ k = canonKey c r.vars i := by
    intro k hk
    change k ∈ KoreAML.freeOf [] (.rewrites C L _) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, h⟩ := hfree k hk; exact ⟨i, hi, h⟩
    · exact hfreeR k hk
  have hgd : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, rfl⟩ := hfree' k hk'
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hVv i hi, hw]
    exact (elemOf_spec hI hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hI x.property e'
  have hxa : elemOf c I x.val = a := (ha _).mp ((elemOf_spec hI x.property e').1 _ |>.mpr rfl)
  have hP := (KoreAML.trAxiom_at hD hax e' hgd a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ ax.pattern).interpret I e' a := hP
  change (KoreAML.tr ⟨tbl, []⟩ (.rewrites C L _)).interpret I e' a at hP'
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hrhsR : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.rhs)).interpret I e' b ↔ (den c y.val).interpret I e' b :=
    fun b => evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b
  have hrightR := right_den hI hrhsR (fun a' ha' => reqPat_holds hI (fun t ht b =>
    evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht) b) ha')
  have hL' := himp (by rw [← hxa]; exact hL tbl e' hvarsL hag hrightR)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  have hby := (hrhsR b).mp hb.1
  have hma : m = a := by
    have := ((den_closed c x.val).interp e e' m).mp hm
    exact (ha m).mp this
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, ((den_closed c y.val).interp e' e b).mp hby, happ⟩

/-- **Step soundness at values, for a rule with open variables.** For a rule r with `ruleSorted` and
`rulePlainOpen` whose axiom a model of `Γc` satisfies (not asked to be one of the definition's), in a
definition whose rules have both, where each competitor of r has a rule of a larger priority: at a σ
with every premise of `StepBy c r σ x y` but the rule's membership, where each competitor that
matches x and needs a witness has decided conditions, x has y as a successor. -/
theorem step_soundOpen (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat)
    (hlarger : ∀ r' ∈ c.rules, r'.prio < r.prio → c.rules.any (fun r'' => r'.prio < r''.prio) = true)
    {σ : Subst} {x y : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (den c y.val)).interpret I e m := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hneg := (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI))
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, hreqs, -, -⟩ := Model.ruleSorted_partsOpen hs hp
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.rulePlainOpen_top hp
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  -- the free variables of the left part are the rule's
  have hfreeL : ∀ {L : Kore.Pattern}, prioRuleK c r = .rewrites C L R →
      ∀ k ∈ KoreAML.freeOf [] L, ∃ i < r.vars.length, k = canonKey c r.vars i := fun hP k hk =>
    freeOf_prioSplit hrules hs hp (by rw [hP, KoreAML.freeOf]; exact List.mem_append_left _ hk)
  -- the left side and the `requires` at x's element, under a valuation that agrees with σ
  have hlr : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl vs σ e' →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e' (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat C (r.req.map (Term.kore c vs)))).interpret I e' (elemOf c I x.val) :=
    fun tbl e' hag =>
      ⟨(patVal_den4 hIΓ hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch (OvlOK.nf_bridge inferInstance hlhs)).2 _ |>.mpr
        ((elemOf_spec hIΓ x.property e').1 _ |>.mpr rfl),
       reqPat_holds hIΓ (fun t ht b => evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hI) (hreq t ht) fns_headsOK hσ
        (canonVars_length c r.vars) hag (hreqs t ht) b) (elemOf_top hIΓ x tbl e')⟩
  by_cases hce : comps.isEmpty
  · -- no competitor
    have hpat : prioRuleK c r = .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .ceil C C R]) R := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce]
    refine successor_of_axiomOpen h hI hcw hs hp hax hpat (fun i hi => (Model.rule_keys_open hs hp
      (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) i hi).2) (hfreeL hpat) hσ heval hens
      (fun tbl e' _ hag hrhsR => ?_) e m hm
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    exact ⟨(hlr tbl e' hag).1, (hlr tbl e' hag).2, ceil_rhs_at hIΓ hrhsR (elemOf_top hIΓ x tbl e')⟩
  · -- competitors: none applies in the model
    have hpat : prioRuleK c r = .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .not C (anyOfC C comps), .ceil C C R]) R := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce]
    refine successor_of_axiomOpen h hI hcw hs hp hax hpat (fun i hi => (Model.rule_keys_open hs hp
      (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) i hi).2)
      (hfreeL hpat) hσ heval hens (fun tbl e' hkeysL hag hrhsR => ?_) e m hm
    rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    refine ⟨(hlr tbl e' hag).1, (hlr tbl e' hag).2, ?_, ceil_rhs_at hIΓ hrhsR (elemOf_top hIΓ x tbl e')⟩
    rw [KoreAML.tr, KoreAML.interp_sNot]
    refine ⟨anyOfC_empty hD (by
      show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
      rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hr'm, hlt⟩ := List.mem_filter.mp hr'
      have hlt' : r'.prio < r.prio := by simpa using hlt
      have hrc' : r'.opens.any (fun i => (r'.vars[i]?.map c.confined).getD false) = true →
          c.readsConfined = true := fun hany => by
        obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
        simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
        exact Or.inl ⟨r', hr'm, by simp [List.ne_nil_of_mem hi]⟩
      refine not_applies_guardedOpen h hI hcw (hrules r' hr'm).1 (hrules r' hr'm).2 (hlarger r' hr'm hlt') hrc'
        (hw r' hr'm hlt') (hprio r' hr'm hlt') (fun i hi hil => hkeysL _ ?_) e'
      refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr'm hlt')
        (Model.varsOf_appliesOpen (Semantics.rulePlainOpen_top (hrules r' hr'm).2).2.1 hi hil))
    · have hxs := elemOf_spec hIΓ x.property e'
      show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
      rw [trSort_srt]
      exact hxs.2

end

end Faithful

open ML Faithful

/-- `•φ` depends only on the set φ denotes. -/
theorem sNext_congr {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} {φ ψ : KoreAML.P}
    (h : ∀ a, φ.interpret I e a ↔ ψ.interpret I e a) {m : M}
    (hm : (KoreAML.sNext φ).interpret I e m) : (KoreAML.sNext ψ).interpret I e m := by
  unfold KoreAML.sNext at hm ⊢
  rw [KoreAML.interp_app] at hm ⊢
  obtain ⟨n, b, hn, hb, happ⟩ := hm
  exact ⟨n, b, hn, (h b).mp hb, happ⟩

/-- **Soundness at a step by a rule whose left side need not bind every variable**: `sound_at`'s
conclusion, for a semantics that `coreOK` accepts whose rules have `ruleSorted` and
`rulePlainOpen`: in every model of `Γc`, x has a successor among the instances of the application,
and y is one of them. The competitors of r whose left side matches x have decided closed
conditions. -/
theorem sound_at_open (c : Semantics) (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) := by
  obtain ⟨hsr, hpr⟩ := hrules r hs.mem
  refine ⟨?_, ?_⟩
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    intro hx
    have hst := step_soundOpen h hrules hI hcw hsr hpr (sat_rules hIΓ (Or.inl ⟨_, List.mem_map.mpr ⟨r, hs.mem, rfl⟩, rfl⟩))
      (fun r' _ hlt => List.any_eq_true.mpr ⟨r, hs.mem, by simpa using hlt⟩) hs.hσ hs.hmatch hs.hreq hs.heval
      hs.hens hs.hprio hw e m hx
    exact sNext_congr (fun a => (famEx_denOpen h hsr hpr hs.hσ hs.heval hs.hens hI hcw e a).symm) hst
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    exact (famEx_denOpen h hsr hpr hs.hσ hs.heval hs.hens hI hcw e m).mpr

end KCore
