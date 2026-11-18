/-
  KCore. A competitor whose open condition variables are of confined sorts or held by a cut.

  `notApplies_memHeld` is `applies_iff_pp`'s statement for a rule with `rulePlainHeldH c H` (its
  competition conjunct reads "of a confined sort, or held by a cut of `pre`"), in a model of `Γc`
  where each symbol of H that is no constructor has `HeldBack`: x's element is outside the rule's
  `applies` pattern exactly where the rule does not apply to x. Right to left
  (`not_applies_of_notApplies_held`): the binders of `applies` are the left side's and the
  conditions' variables; an open condition variable a cut holds is a value's element because the
  cut's variable is the left side's, a value's, and `pre` holds at x's element
  (`memHeldH_witnessedAt` at the sorts `Rule.leftSorts`); where some open condition variable is
  neither of a confined sort nor held by a cut, the conditions are closed, `needsWitness` holds
  and they are decided, as for `rulePlainPP`.
-/
import KcoreSpec.CompetePP
import KcoreSpec.StepValuesHeld

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A competitor with a cut that does not apply does not apply in a model of `Γc`.** For a rule
with `ruleSorted` and `rulePlainHeldH c H` and a rule of a larger priority, where its conditions
are decided when `needsWitness` holds and each symbol of H that is no constructor has `HeldBack`:
if it does not apply to x at values, x's element is not in its `applies` pattern. -/
theorem not_applies_of_notApplies_held (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {x : Config c} (hna : NotApplies c r x.val)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  intro hm
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, -⟩, hbdP⟩, -⟩, -⟩ := hs'
  have hreqS : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreqK; simpa [reqOK] using hreqK
  let vs := canonVars c r.vars
  let n := r.vars.length
  let C := srtOf c topCellSort
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hpreL : ∀ i ∈ varOccsCond n r.pre, i < n ∧ i ∈ r.leftVars := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, List.mem_append_right _ (List.mem_append_right _ hi)⟩
  rw [Model.applies_eqPP r] at hm
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
  obtain ⟨hlx, hreqx, hprex⟩ := (interp_bodyPPI _ _ _ _ _ _).mp hbody
  -- the binders are in their sorts
  have hinL : ∀ i < n, i ∈ r.leftVars → InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi hil => hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
      (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  -- the other variables: the configuration sort and x's element
  let a := elemOf c I x.val
  let e1 := fillV c tbl r.vars r.leftVars a e'
  have hoff1 : ∀ i < n, i ∈ r.leftVars → e1.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  have hvsl : vs.length = r.leftSorts.length := by rw [canonVars_length, Rule.leftSorts_length]
  have hwitF : ∀ i < n, i ∉ r.leftVars → Witnessed c I tbl vs r.leftSorts e1 i := fun i hi hil =>
    ⟨x.val, by rw [Rule.leftSorts_getD_off hi hil]; exact x.property, (fillV_on hi hil).symm⟩
  have hin1 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e1.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi => by
      rw [Rule.leftSorts_length] at hi
      by_cases hil : i ∈ r.leftVars
      · rw [Rule.leftSorts_getD hi hil, hoff1 i hi hil]; exact hinL i hi hil
      · obtain ⟨v, hv, he⟩ := hwitF i hi hil
        rw [← he]; exact (inS_iff e1).mp (elemOf_spec hIΓ hv e1).2
  have hlhsL : ∀ i ∈ varOccs r.lhs, i ∈ r.leftVars := fun i hi => List.mem_append_left _ hi
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := Exec.sortOfTerm_vars hlhs
  have hlx1 := (tr_kore_congr r.lhs (fun i hi => (hoff1 i (hltL i hi) (hlhsL i hi)).symm) _).mp hlx
  have hreq1 : ∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat C (some (Term.kore c vs t)))).interpret I e1
      (elemOf c I x.val) := fun t ht => by
    rw [ht] at hreqx
    exact (tr_reqPat_congr hIΓ (fun i hi => (hoff1 i (Exec.sortOfTerm_vars (hreqS t ht) i hi)
      (Rule.req_leftVars ht i hi)).symm) _).mp hreqx
  -- `pre`'s conjuncts read e1 as e'
  have hpre1 : ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e1 (elemOf c I x.val) :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hpreL i hi).1 (hpreL i hi).2)
      (fun i hi => (hoff1 i (hpreL i hi).1 (hpreL i hi).2).symm) hprex
  have hsortsL : ∀ (t : Term), (∀ i ∈ varOccs t, i < n ∧ i ∈ r.leftVars) → ∀ (x' : TermCtx),
      sortOfTerm x' r.leftSorts t = sortOfTerm x' r.vars t := fun t ht x' =>
    sortOfTerm_congr t fun i hi => Rule.leftSorts_getElem? (ht i hi).1 (ht i hi).2
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [hsortsL r.lhs (fun i hi => ⟨hltL i hi, hlhsL i hi⟩)]; exact hlhs
  have hreqS' : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.leftSorts t = some Srt.bool :=
    fun t ht => by
      rw [hsortsL t (fun i hi => ⟨Exec.sortOfTerm_vars (hreqS t ht) i hi, Rule.req_leftVars ht i hi⟩)]
      exact hreqS t ht
  -- a valuation of the left side's variables in their sorts where every variable is a value's,
  -- x's element in `pre`'s conjuncts, contradicts `NotApplies`
  have hwsAt : ∀ σ, c.WellSorted r.leftSorts σ → c.WellSortedAt r.vars r.leftVars σ := fun σ hσ i hi s hs => by
    have hlt : i < n := (List.getElem?_eq_some_iff.mp hs).1
    exact hσ i s (by rw [Rule.leftSorts_getElem? hlt hi]; exact hs)
  have hfin : ∀ (e2 : Valuation M), (∀ i < r.leftSorts.length, Witnessed c I tbl vs r.leftSorts e2 i) →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e2 (elemOf c I x.val) →
      (∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat C (some (Term.kore c vs t)))).interpret I e2
        (elemOf c I x.val) ∨ EvalTerm c (substOf c I tbl vs r.leftSorts e2) t (some (bool true))) →
      (∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e2 (elemOf c I x.val)) → False := by
    intro e2 hwit2 hl2 hr2 hpre2
    have hin2 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) :=
      fun i hi => by obtain ⟨v, hv, he⟩ := hwit2 i hi; rw [← he]; exact (inS_iff e2).mp (elemOf_spec hIΓ hv e2).2
    obtain ⟨hpv, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin2 (collPat_of_sorted hph' hlhs')
      (Semantics.lhs_nf OvlOK.ok hr hlhs') x.property hl2
    obtain ⟨hσ2, hag2⟩ := substOf_ok hIΓ hg hsc.trans hvsl hwit2
    obtain ⟨t, v, ht, he, hv⟩ : ∃ t v, r.req = some t ∧ EvalTerm c (substOf c I tbl vs r.leftSorts e2) t v ∧
        v ≠ some (bool true) := by
      cases hna _ (hwsAt _ hσ2) hpv with
      | intro ht he hv => exact ⟨_, _, ht, he, hv⟩
      | pre hf =>
        -- `pre` false: x's element is not in its pattern
        have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre)
            (substOf c I tbl vs r.leftSorts e2) tbl e2 := reads_of_agreesAt hag2 fun i hi => by
          obtain ⟨hlt, hil⟩ := hpreL i hi
          obtain ⟨v, hv, hsv⟩ := hσ2 i (r.vars.getD i 0) (by
            rw [Rule.leftSorts_getElem? hlt hil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
          exact ⟨hlt, hkeys i hlt hil, v, hv, hsv⟩
        exact Bool.noConfusion ((conj_iff_holdsPP h hI hcw hokP hbdP hrcP hreads hkP (inh_top_PP hIΓ x tbl e2) hf).mp
          hpre2)
    have hden := evalTerm_den4Cl hIΓ hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw) he fns_headsOK hσ2 hvsl hag2 (hreqS' t ht)
    rcases hr2 t ht with hm2 | htrue
    · obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
      exact reqFalse_empty hIΓ (S' := C) (fun a => by unfold C srtOf; rw [trSort_srt]; exact hσC1 a) hσC2 hv
        (fun u hu => EvalTerm.sorted hsc he fns_headsOK hσ2 (hreqS' t ht) hu) hden _ hm2
    · have hdenT := evalTerm_den4Cl hIΓ hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw) htrue fns_headsOK hσ2 hvsl hag2
        (hreqS' t ht)
      have hTm : Res c I e2 (some (bool true)) (elemOf c I (bool true)) :=
        ((elemOf_spec hIΓ (sortOf_bool true) e2).1 _).mpr rfl
      have hVm := (hden _).mp ((hdenT _).mpr hTm)
      cases v with
      | none => exact hVm
      | some u =>
        have hu := EvalTerm.sorted hsc he fns_headsOK hσ2 (hreqS' t ht) rfl
        have heq : elemOf c I (bool true) = elemOf c I u := ((elemOf_spec hIΓ hu e2).1 _).mp hVm
        exact hv (congrArg some (values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hu) hu (sortOf_bool true)
          heq.symm))
  -- the open condition variables, by the competition conjunct
  have hcomp := Semantics.rulePlainHeldH_compete hp hlarger
  -- a variable of the left side's conditions that the left side does not hold is open
  have hopen : ∀ i < n, i ∈ r.leftVars → i ∉ varOccs r.lhs → i ∈ r.openCondVars := fun i hi hil hnl => by
    have hcv : i ∈ r.condVars := by
      rcases List.mem_append.mp hil with h' | h'
      · exact absurd h' hnl
      · exact h'
    refine List.mem_filter.mpr ⟨?_, by simpa using hcv⟩
    simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hnl⟩
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPat_of_sorted hph' hlhs')
    (Semantics.lhs_nf OvlOK.ok hr hlhs') x.property hlx1
  by_cases hconf : ∀ i ∈ r.openCondVars, (r.vars[i]?.map c.confined).getD false = true ∨
      memHeldH c H (varOccs r.lhs) r.pre i = true
  · -- every open condition variable is of a confined sort or held by a cut: it is a value's
    refine hfin e1 (fun i hi => ?_) hlx1 (fun t ht => Or.inl (hreq1 t ht)) hpre1
    rw [Rule.leftSorts_length] at hi
    by_cases hil : i ∈ r.leftVars
    · by_cases hL : i ∈ varOccs r.lhs
      · exact hwitL i hL
      · have hoc := hopen i hi hil hL
        rcases hconf i hoc with hcf | hM
        rotate_left
        · -- held by a cut: the cut's variable is the left side's, a value's
          have hvarsP : ∀ q ∈ r.pre.conjuncts, ∀ j ∈ varOccsCond n q, j < n ∧ j ∈ r.leftVars :=
            fun q hq j hj => hpreL j (conjuncts_varOccs n r.pre q hq j hj)
          exact memHeldH_witnessedAt hIΓ hg hsc.trans hnn.1 hvsl hin1 fns_headsOK hback hwitL
            (fun s v t hq => by
              obtain ⟨h1, h2, h3⟩ := conjuncts_memOK hokP hq
              have hv := hvarsP _ hq v (by
                rw [varOccsCond, varOccs]; exact List.mem_append_left _ (List.mem_singleton.mpr rfl))
              refine ⟨by rw [Rule.leftSorts_getElem? hv.1 hv.2]; exact h1, ?_, h3⟩
              rw [hsortsL t (fun j hj => hvarsP _ hq j (by rw [varOccsCond]; exact List.mem_append_right _ hj))]
              exact h2)
            top_numbered (hpre1 _ (by simp [Cond.conj, memHeldH_not_top hM, C])) i hM
        obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
        have hcs' : c.confined s = true := by rw [hvs] at hcf; exact hcf
        have hin' := hin1 i (by rw [Rule.leftSorts_length]; exact hi)
        rw [Rule.leftSorts_getD hi hil, List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
        obtain ⟨v, hv, hden⟩ := confined_value h
          (hrc (List.any_eq_true.mpr ⟨i, (List.mem_filter.mp hoc).1, by rw [hvs]; exact hcs'⟩)) hI hcs' e1 _
          ((inS_iff e1).mpr hin')
        have hel := ((elemOf_spec hIΓ hv e1).1 _).mpr rfl
        exact witnessed_of (by rw [Rule.leftSorts_getElem? hi hil]; exact hvs) hv ((hden _).mp hel)
    · exact hwitF i hi hil
  -- otherwise the conditions are closed, and `needsWitness` holds
  obtain ⟨i0, hi0, hi0n⟩ : ∃ i ∈ r.openCondVars, ¬ ((r.vars[i]?.map c.confined).getD false = true ∨
      memHeldH c H (varOccs r.lhs) r.pre i = true) :=
    Classical.byContradiction fun hne => hconf fun i hi => Classical.byContradiction fun hg' => hne ⟨i, hi, hg'⟩
  have hconf' : r.openCondVars.all (fun i => (r.vars[i]?.map c.confined).getD false) = false :=
    List.all_eq_false.mpr ⟨i0, hi0, fun hc => hi0n (Or.inl hc)⟩
  have hro : r.reqOpen = true := by
    unfold Rule.reqOpen
    cases h' : r.openCondVars with
    | nil => rw [h'] at hi0; cases hi0
    | cons _ _ => rfl
  have hrcl : r.reqClosed = true := by
    rcases hcomp with h1 | h2 | h3
    · rw [hro] at h1; cases h1
    · exact absurd h2 hconf
    · exact h3
  have hnw : r.needsWitness c = true := by
    unfold Rule.needsWitness; rw [hro, hrcl, hconf']; rfl
  have hcvl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs := fun j hj hjl => by
    have hc2 := hrcl
    unfold Rule.reqClosed at hc2
    have := List.all_eq_true.mp hc2 j hj
    rw [List.contains_iff_mem.mpr hjl] at this
    exact absurd this (by decide)
  have hcvn : ∀ j ∈ r.condVars, j < n := fun j hj => by
    rcases List.mem_append.mp hj with hj | hj
    · cases ht : r.req with
      | none => simp [ht] at hj
      | some t =>
        simp only [ht, Option.map_some, Option.getD_some] at hj
        exact Exec.sortOfTerm_vars (hreqS t ht) j hj
    · exact varOccsCond_lt_twoT r.pre hokP j hj
  rcases hw hnw with hW | href
  · -- witnessed: the witness's values at the conditions' variables, x's match elsewhere
    obtain ⟨σw, hσw, hreqw, hprew⟩ := hW
    have hkeysC : ∀ i < r.vars.length, i ∈ r.condVars → canonKey c r.vars i ∈ tbl :=
      fun i hi hc => hkeys i hi (List.mem_append_right _ hc)
    let e2 := setV c tbl r.vars r.condVars (fun j => elemOf c I ((σw.lookup j).getD default)) e1
    have hσwv : ∀ i < n, i ∈ r.condVars → ∃ w, σw.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
      fun i hi hc => hσw i hc _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hon2 : ∀ i < n, i ∈ r.condVars → ∀ w, σw.lookup i = some w →
        e2.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I w := fun i hi hc w hw' => by
      show (setV c tbl r.vars r.condVars _ e1).evalEvar (tbl.ev (canonKey c r.vars i)) = _
      rw [setV_on hkeysC hi hc, hw', Option.getD_some]
    have hwit2 : ∀ i < r.leftSorts.length, Witnessed c I tbl vs r.leftSorts e2 i := fun i hi => by
      rw [Rule.leftSorts_length] at hi
      by_cases hc : i ∈ r.condVars
      · obtain ⟨w, hw', hws⟩ := hσwv i hi hc
        refine ⟨w, by rw [Rule.leftSorts_getD hi (List.mem_append_right _ hc)]; exact hws, ?_⟩
        exact (hon2 i hi hc w hw').symm
      · obtain ⟨v, hv, he⟩ : Witnessed c I tbl vs r.leftSorts e1 i := by
          by_cases hil : i ∈ r.leftVars
          · rcases List.mem_append.mp hil with hL | hL
            · exact hwitL i hL
            · exact absurd hL hc
          · exact hwitF i hi hil
        refine ⟨v, hv, ?_⟩
        show _ = (setV c tbl r.vars r.condVars _ e1).evalEvar (tbl.ev (canonKey c r.vars i))
        rw [setV_off hkeysC hi hc]; exact he
    have hl2 : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e2 (elemOf c I x.val) :=
      (tr_kore_congr r.lhs (fun i hi => (setV_off (f := fun j => elemOf c I ((σw.lookup j).getD default)) hkeysC
        (hltL i hi) (fun hc => hcvl i hc hi)).symm) _).mp hlx1
    -- `pre` holds at σw, which e2 reads at `pre`'s variables
    have hpre2 : ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e2 (elemOf c I x.val) := by
      have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre) σw tbl e2 := fun i hi => by
        have hlt := varOccsCond_lt_twoT r.pre hokP i hi
        have hc : i ∈ r.condVars := List.mem_append_right _ hi
        obtain ⟨w, hw', hws⟩ := hσwv i hlt hc
        refine ⟨hlt, hkeysC i hlt hc, w, hw', hws, fun m => ?_⟩
        rw [hon2 i hlt hc w hw']
        exact ((elemOf_spec hIΓ hws e2).1 m).symm
      exact (conj_iff_holdsPP h hI hcw hokP hbdP hrcP hreads hkP (inh_top_PP hIΓ x tbl e2) hprew).mpr rfl
    refine hfin e2 hwit2 hl2 (fun t ht => Or.inr (Exec.EvalTerm.congr (hreqw t ht) fun i hi => ?_)) hpre2
    have hc : i ∈ r.condVars := by
      simp only [Rule.condVars, ht, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
    have hi' := hcvn i hc
    obtain ⟨w, hw', hws⟩ := hσwv i hi' hc
    have hin2 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) :=
      fun i hi => by obtain ⟨v, hv, he⟩ := hwit2 i hi; rw [← he]; exact (inS_iff e2).mp (elemOf_spec hIΓ hv e2).2
    have hvi : r.leftSorts[i]? = some (r.vars.getD i 0) := by
      rw [Rule.leftSorts_getElem? hi' (List.mem_append_right _ hc), List.getElem?_eq_getElem hi',
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [hw', substOf_var hIΓ hg hsc.trans hnn.1 hvsl hin2 hvi hws (hon2 i hi' hc w hw').symm]
  · -- refuted: but the conditions hold at the binders
    exact cond_not_refuted_pp h hI hs (fun i hi hc => hkeys i hi (List.mem_append_right _ hc)) hkP
      (fun i hi hc => hinL i hi (List.mem_append_right _ hc)) hreqx hprex href

/-- **A competitor with a cut, in a model of `Γc`**: for a rule with `ruleSorted` and
`rulePlainHeldH c H` and a rule of a larger priority, its conditions decided when `needsWitness`
holds, in a model where each symbol of H that is no constructor has `HeldBack`, where its
`requires` has a result and its `pre` a truth value at each match, x's element is outside its
`applies` pattern exactly where it does not apply to x. -/
theorem notApplies_memHeld (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c) {x : Config c}
    (hd : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) ↔
      NotApplies c r x.val :=
  ⟨notApplies_of_not_applies_pp h hI hcw hs hrcP hd hkeys hkP e,
   fun hna => not_applies_of_notApplies_held h hI hcw hback hs hp hlarger hrc hrcP hw hna hkeys hkP e⟩

end

end Faithful

end KCore
