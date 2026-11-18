/-
  KCore. The instances of a step by a rule without existential variables are its successor
  (`famEx_denPPCEx`), with the competitor and condition lemmas it and the completeness lemmas read,
  for a semantics `coreOKEx` accepts, the evaluations of terms
  read by `HoldsShape.termSoundEx`'s block (`evalTerm_den4ClQ`, `holds_entailsCEx`).
-/
import KcoreSpec.TermSoundCEx
import KcoreSpec.SoundPP
import KcoreSpec.FamExValuesPP
import KcoreSpec.ModelChoiceHeld
import KcoreSpec.HeldBackAll
import KcoreSpec.CompetePP
import KcoreSpec.StepValuesHeld

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
variable {H : Sym → Bool}

/-- **A refuted condition contradicts a valuation**, for a rule with predicates: where x's element
is in `⌈req = true⌉` and `pre` at a valuation that gives the condition variables elements of their
sorts, through a table holding their keys, the conditions are not refuted. -/
theorem cond_not_refuted_ppCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.condVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∈ r.condVars → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)))) {m : M}
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e m)
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e m) :
    ¬ r.Refuted c := by
  intro href
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  haveI : OvlOK c := (hypSoundEx_of_coreEx h).2.2.2.2.2.2.2.2
  have hD := defOK hIΓ
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs'
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let l := (List.range r.vars.length).filter r.condVars.contains
  have hl : ∀ i ∈ l, i < r.vars.length := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hml : ∀ i < r.vars.length, i ∈ r.condVars → i ∈ l := fun i hi hc =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hc⟩
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  have hK : r.condK c = KoreAML.existsAll C ((l.map (vs.getD · default)).map KoreAML.Var.kore)
      (.and C ([reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre)) := by
    unfold Rule.condK
    rw [← hbs]
  unfold Rule.Refuted at href
  rw [hK] at href
  unfold KoreAML.denB at href
  generalize htbl : KoreAML.tableOf [] _ = tbl2 at href
  have hkeys2 : ∀ i < r.vars.length, i ∈ l → canonKey c r.vars i ∈ tbl2 := fun i _ hil => by
    rw [← htbl]; unfold KoreAML.tableOf canonKey
    exact List.mem_eraseDups.mpr (List.mem_append_right _
      (mem_varsOf_existsAll (List.mem_map_of_mem (List.mem_map_of_mem hil))))
  let e' := moveV c tbl tbl2 r.vars l e
  have hneg := href hI e' m
  rw [interpret_neg] at hneg
  apply hneg
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl2.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys2 i (hl i hi) hi) (hkeys2 j (hl j hj) hj) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  refine existsAll_intro_at hD _ e' e' m hnd hsrt (fun _ _ => rfl) rfl (fun b hb n hn => ?_) ?_
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c (hl i hil)]; rfl
    change ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n at hn
    rw [hs'] at hn
    rw [← srt_inj hn]
    show InS I _ (e'.evalEvar (tbl2.ev (canonKey c r.vars i)))
    rw [moveV_at hkeys2 (hl i hil) hil]
    exact hin i (hl i hil) (by simpa using (List.mem_filter.mp hil).2)
  · refine (interp_and (by simp)).mpr fun φ hφ => ?_
    rcases List.mem_append.mp hφ with hφ | hφ
    · rw [List.mem_singleton.mp hφ]
      cases hq : r.req with
      | none =>
        show (KoreAML.tr ⟨tbl2, []⟩ (.top C)).interpret I e' m
        rw [KoreAML.tr, KoreAML.interp_sTop hD Model.srtOf_free_stdI]
        exact reqPat_inhSplit hIΓ hreqm tbl2 e'
      | some t =>
        have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
          rw [hq] at hreqK; simpa [reqOK] using hreqK
        have hlt : ∀ i ∈ varOccs t, i < r.vars.length := Exec.sortOfTerm_vars htS
        have hcv : ∀ i ∈ varOccs t, i ∈ r.condVars := fun i hi => by
          simp only [Rule.condVars, hq, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
        rw [hq] at hreqm
        exact (tr_reqPat_congr hIΓ (fun i hi => moveV_at hkeys2 (hlt i hi) (hml i (hlt i hi) (hcv i hi))) m).mpr
          hreqm
    · by_cases hT : r.pre.isTop = true
      · simp [Cond.conj, hT] at hφ
      · obtain rfl : φ = Cond.kore c vs C r.pre := by simpa [Cond.conj, hT] using hφ
        refine (tr_condKore_twoT hD r.pre hokP (fun k hk0 => ⟨hkP k hk0, ?_⟩) (fun i hi => ?_) m).mp
          (hprem _ (by simp [Cond.conj, hT]))
        · rw [← htbl]; unfold KoreAML.tableOf
          exact List.mem_eraseDups.mpr (List.mem_append_right _ (HoldsShape.varsOf_existsAll_bodyHF
            (Model.varsOf_and_mem (List.mem_append_right _ (by simp [Cond.conj, hT, vs, C])) hk0) _))
        · have hlt := varOccsCond_lt_twoT r.pre hokP i hi
          have hc : i ∈ r.condVars := List.mem_append_right _ hi
          exact ⟨hkeys i hlt hc, hkeys2 i hlt (hml i hlt hc), (moveV_at hkeys2 hlt (hml i hlt hc)).symm⟩

/-- **The conjuncts a predicate adds to a sentence, in a model of `Γc`** (none for `\top`): at an
element of the configuration sort they hold exactly where its truth value is `true`, at a σ the
valuation reads at the predicate's free variables, the keys of its pattern in the table. -/
theorem conj_iff_holdsPPCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst} {tbl : VarTable} {e : Valuation M}
    (hr : Reads c I vars (fun i => i ∈ varOccsCond vars.length p) σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    {b : Bool} (hh : Holds c vars.length σ p b) :
    (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) ↔
      b = true := by
  by_cases hT : p.isTop = true
  · obtain rfl := Cond.eq_top_of_isTop hT
    cases hh
    simp [Cond.conj, Cond.isTop]
  · have hc : Cond.conj c (canonVars c vars) (srtOf c topCellSort) p =
        [Cond.kore c (canonVars c vars) (srtOf c topCellSort) p] := by simp [Cond.conj, hT]
    rw [hc]
    simp only [List.mem_singleton, forall_eq]
    exact HoldsShape.holds_entailsCEx h hI hcw p hrc hok hbd (fun i hi _ => hi) hr hk top_numbered hh a ha

/-- **A rule with a `pre` that applies at values applies in a model of `Γc`.** For a rule with
`ruleSorted`, a σ that gives the variables of its left side and conditions values, matches x, makes
the `requires` `true` and `pre` `true`: x's element is in the rule's `applies` pattern. The keys of
the left side's and the conditions' variables and of `pre`'s pattern are in the table. -/
theorem applies_of_values_ppCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    {x : Config c} {σ : Subst}
    (hσ : c.WellSortedAt r.vars r.leftVars σ) (hpv : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
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
  rw [Model.applies_eqPP r]
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  -- σ on the left side's and conditions' variables, x's value elsewhere
  let σ' : Subst := (List.range n).map fun i => (i, if r.leftVars.contains i then (σ.lookup i).getD default else x.val)
  have hσ'l : ∀ i < n, σ'.lookup i = some (if r.leftVars.contains i then (σ.lookup i).getD default else x.val) :=
    fun i hi => by
      simp only [σ']
      rw [List.range_eq_range', lookup_range', if_pos ⟨Nat.zero_le _, by omega⟩]
  have hσv : ∀ i < n, i ∈ r.leftVars → ∃ w, σ.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
    fun i hi hil => hσ i hil _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hσ'L : ∀ i < n, i ∈ r.leftVars → σ'.lookup i = σ.lookup i := fun i hi hil => by
    obtain ⟨w, hw, -⟩ := hσv i hi hil
    rw [hσ'l i hi, if_pos (by simpa using hil), hw, Option.getD_some]
  have hσ'O : ∀ i < n, i ∉ r.leftVars → σ'.lookup i = some x.val := fun i hi hil => by
    rw [hσ'l i hi, if_neg (by simpa using hil)]
  have hvsl : vs.length = r.leftSorts.length := by rw [canonVars_length, Rule.leftSorts_length]
  have hσ' : c.WellSorted r.leftSorts σ' := fun i s hs' => by
    have hlt : i < n := by have := (List.getElem?_eq_some_iff.mp hs').1; rwa [Rule.leftSorts_length] at this
    by_cases hil : i ∈ r.leftVars
    · obtain ⟨w, hw, hws⟩ := hσv i hlt hil
      refine ⟨w, by rw [hσ'L i hlt hil, hw], ?_⟩
      rw [Rule.leftSorts_getElem? hlt hil] at hs'
      rw [hws, List.getD_eq_getElem?_getD, hs', Option.getD_some]
    · refine ⟨x.val, hσ'O i hlt hil, ?_⟩
      have := Rule.leftSorts_getD_off hlt hil
      rw [List.getD_eq_getElem?_getD, hs', Option.getD_some] at this
      rw [this]; exact x.property
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := Exec.sortOfTerm_vars hlhs
  have hlhsL : ∀ i ∈ varOccs r.lhs, i ∈ r.leftVars := fun i hi => List.mem_append_left _ hi
  have hpv' : PatVal c σ' r.lhs x.val := PatVal.congr_lookup hpv fun j hj => hσ'L j (hltL j hj) (hlhsL j hj)
  have hreqLt : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < n ∧ i ∈ r.leftVars := fun t ht i hi =>
    ⟨Exec.sortOfTerm_vars (hreqS t ht) i hi, Rule.req_leftVars ht i hi⟩
  have hreq' : ∀ t, r.req = some t → EvalTerm c σ' t (some (bool true)) := fun t ht =>
    Exec.EvalTerm.congr (hreq t ht) fun i hi => (hσ'L i (hreqLt t ht i hi).1 (hreqLt t ht i hi).2).symm
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact hlhs
  have hlhsN' : sortOfTerm c.patCtxNF r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact Semantics.ruleSorted_lhs_nf c hs
  have hreqS' : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.leftSorts t = some Srt.bool :=
    fun t ht => by
      rw [sortOfTerm_congr t fun i hi => Rule.leftSorts_getElem? (hreqLt t ht i hi).1 (hreqLt t ht i hi).2]
      exact hreqS t ht
  -- the valuation: σ''s elements at the binders, and x's element at the other variables
  let f : Nat → M := fun j => elemOf c I ((σ'.lookup j).getD default)
  let e3 := setV c tbl r.vars r.leftVars f e
  let e4 := fillV c tbl r.vars r.leftVars (elemOf c I x.val) e3
  have h4 : ∀ i < n, e4.evalEvar (tbl.ev (keyAt vs i)) = f i := fun i hi => by
    by_cases hil : i ∈ r.leftVars
    · show (fillV c tbl r.vars r.leftVars _ e3).evalEvar (tbl.ev (canonKey c r.vars i)) = _
      rw [fillV_off hkeys hi hil]; exact setV_on hkeys hi hil
    · show (fillV c tbl r.vars r.leftVars _ e3).evalEvar (tbl.ev (canonKey c r.vars i)) = _
      rw [fillV_on hi hil]; show _ = elemOf c I ((σ'.lookup i).getD default)
      rw [hσ'O i hi hil, Option.getD_some]
  have hag : Agrees c I tbl vs σ' e4 := fun i v hi hv m => by
    rw [canonVars_length] at hi
    have hvs' := hσ' i (r.leftSorts.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Rule.leftSorts_length]; exact hi)]; rfl)
    obtain ⟨w, hw, hws⟩ := hvs'
    rw [hv] at hw; cases hw
    show m = e4.evalEvar (tbl.ev (keyAt vs i)) ↔ _
    rw [h4 i hi]; show m = elemOf c I ((σ'.lookup i).getD default) ↔ _
    rw [hv, Option.getD_some]
    exact ((elemOf_spec hIΓ hws e4).1 m).symm
  have hxs := elemOf_spec hIΓ x.property e4
  have hlx4 := ((patVal_den4 hIΓ hnn.1 hph hsc.trans hσ' hvsl hag hpv' hlhsN').2 _).mpr ((hxs.1 _).mpr rfl)
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
  have hreq4 := reqPat_holds hIΓ (vs := vs) (q := r.req) (fun t ht b =>
    evalTerm_den4ClQ hIΓ hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) (neg_of_coreClEx hI (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_coreEx h hI)) (HoldsShape.preReadAll_of_coreEx h hI) (clauseExRead_all_of_coreEx h hI) (hreq' t ht) fns_headsOK hσ' hvsl hag (hreqS' t ht) b)
    (by have := hxs.2; unfold srtOf; rw [trSort_srt]; exact this)
  -- e3 agrees with e4 at the left side's and conditions' variables, and with e off the binders
  have h34 : ∀ i < n, i ∈ r.leftVars → e4.evalEvar (tbl.ev (keyAt vs i)) = e3.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  -- `pre` is `true` at σ, which e3 reads at `pre`'s variables
  have hpre3 : ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e3 (elemOf c I x.val) := by
    have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre) σ tbl e3 := fun i hi => by
      have hlt := varOccsCond_lt_twoT r.pre hokP i hi
      have hil : i ∈ r.leftVars := List.mem_append_right _ (List.mem_append_right _ hi)
      obtain ⟨w, hw, hws⟩ := hσv i hlt hil
      refine ⟨hlt, hkeys i hlt hil, w, hw, hws, fun m => ?_⟩
      have hon : e3.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I w := by
        show (setV c tbl r.vars r.leftVars f e).evalEvar (tbl.ev (canonKey c r.vars i)) = _
        rw [setV_on hkeys hlt hil]
        show elemOf c I ((σ'.lookup i).getD default) = _
        rw [hσ'L i hlt hil, hw, Option.getD_some]
      rw [hon]
      exact ((elemOf_spec hIΓ hws e3).1 m).symm
    exact (conj_iff_holdsPPCEx h hI hcw hokP hbdP hrcP hreads hkP (inh_top_PP hIΓ x tbl e3) hpre).mpr rfl
  refine existsAll_intro_at hD _ e e3 _ hnd hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_
  · show (if h : _ then _ else _) = _
    rw [dif_neg]
    rintro ⟨i, hi, hil, rfl⟩
    exact hz _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) rfl
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c (hl i hil)]; rfl
    change ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt k at hk
    rw [hs'] at hk
    rw [← srt_inj hk]
    show InS I _ (e3.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [setV_on hkeys (hl i hil) (hlm i hil)]
    obtain ⟨w, hw, hws⟩ := hσv i (hl i hil) (hlm i hil)
    show InS I _ (elemOf c I ((σ'.lookup i).getD default))
    rw [hσ'L i (hl i hil) (hlm i hil), hw, Option.getD_some]
    exact (inS_iff e3).mp (elemOf_spec hIΓ hws e3).2
  · refine (interp_bodyPPI _ _ _ _ _ _).mpr
      ⟨(tr_kore_congr r.lhs (fun i hi => h34 i (hltL i hi) (hlhsL i hi)) _).mp hlx4, ?_, hpre3⟩
    cases hq : r.req with
    | none =>
      rw [hq] at hreq4
      have hT : ∀ (tb : VarTable) (ev : Valuation M),
          (KoreAML.tr ⟨tb, []⟩ (reqPat C none)).interpret I ev (elemOf c I x.val) ↔
          (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName topCellSort)))).interpret I ev (elemOf c I x.val) :=
        fun tb ev => by
          simp only [reqPat]
          rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold C srtOf; rw [trSort_srt]; rfl)]
          unfold C srtOf; rw [trSort_srt]
      exact (hT tbl e3).mpr (((KoreAML.Closed.sym _).app (KoreAML.Closed.sym _)).interp e4 e3 _ |>.mp ((hT tbl e4).mp hreq4))
    | some t =>
      rw [hq] at hreq4
      exact (tr_reqPat_congr hIΓ (fun i hi => h34 i (hreqLt t hq i hi).1 (hreqLt t hq i hi).2) _).mp hreq4

/-- **A competitor with a `pre` that does not apply in a model does not apply at values**, where its
`requires` has a result and its `pre` a truth value at each match (the first conjunct of
`StepDecided` for the rule): for a rule with `ruleSorted`, if x's element is not in its `applies`
pattern at a valuation, then `NotApplies`. -/
theorem notApplies_of_not_applies_ppCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hrcP : hasBinder r.pre = true → c.readsConfined = true) {x : Config c}
    (hd : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M)
    (hna : ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val)) :
    NotApplies c r x.val := by
  intro σ hσ hpv
  obtain ⟨hdq, b, hb⟩ := hd σ hσ hpv
  have key : (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → RuleReqFails c σ r := fun hq => by
    cases b with
    | true => exact absurd (applies_of_values_ppCEx h hI hcw hs hrcP hσ hpv hq hb hkeys hkP e) hna
    | false => exact .pre hb
  cases ht : r.req with
  | none => exact key fun t h' => by rw [ht] at h'; cases h'
  | some t =>
    obtain ⟨v, hv⟩ := hdq t ht
    by_cases hvt : v = some (bool true)
    · refine key fun t' h' => ?_
      rw [ht] at h'; cases h'; rw [hvt] at hv; exact hv
    · exact RuleReqFails.intro ht hv hvt

/-- **A condition's conjuncts hold at one element of the sentence's sort iff at any other** (R3,
`successor_split_ppCEx`'s `hpred`): in a model of `Γ c` of a definition `coreOKEx` accepts, for a
well-sorted condition p at a numbered sort S, through a table holding the keys of its pattern's
variables, at a valuation that gives each free variable of p an element of its sort. -/
theorem cond_pred_transferCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) {vars : List Srt} {p : Cond}
    (hok : c.condOK vars p = true) {S : Srt} (hS : S < nRegSorts + c.sortNames.length)
    {tbl : VarTable} {e : Valuation M} {a a' : M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hf : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a)
    (ha' : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a') :
    (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c S) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) →
      ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c S) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a' := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  obtain ⟨τS, hσS, hτS⟩ := srt_den hI hS
  have hP := cond_predAt hI (defOK hI) (sat_sigItem hI sig_ceilDef) hg hτS hσS p hok hk hf a a'
    ((KoreAML.interp_inhOf_of (hτS tbl e)).mp ha) ((KoreAML.interp_inhOf_of (hτS tbl e)).mp ha')
  intro hall φ hφ
  have hφ' := hφ
  unfold Cond.conj at hφ
  split at hφ
  · cases hφ
  · rw [List.mem_singleton] at hφ
    subst hφ
    exact hP.mp (hall _ hφ')

/-- `cond_pred_transferCEx` at the configuration sort, in the form of `successor_split_ppCEx`'s `hpred`
with its two hypotheses: the table holds the pattern's keys, and the valuation gives each free
variable of the condition an element of its sort. -/
theorem cond_pred_transfer_topCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) {vars : List Srt} {p : Cond}
    (hok : c.condOK vars p = true) :
    ∀ (tbl : VarTable) (e : Valuation M) (a a' : M),
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl) →
      (∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
        InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a →
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a' →
      (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) →
      ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a' :=
  fun _ _ _ _ hk hf ha ha' => cond_pred_transferCEx h hI hok top_numbered hk hf ha ha'

/-- **The instances of a step are its successor**, in every model of `Γc`, for a rule with
`ruleSorted` and no existential variable (not asked to be one of the definition's; its `post` need
not be `\top`), at a σ that gives every variable a value, under which the right side evaluates to
y, the `ensures` to `true` and `post` holds; a `post` with a binder asks `readsConfined`. -/
theorem famEx_denPPCEx (h : c.coreOKEx = true) {r : Rule} (hs : c.ruleSorted r = true) (hex : r.exs = [])
    (hrc : hasBinder r.post = true → c.readsConfined = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {y : Config c}
    (heval : EvalTerm c σ r.rhs (some y.val)) (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) (e : Valuation M) (m : M) :
    (famEx c r σ).interpret I e m ↔ (den c y.val).interpret I e m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hneg := (neg_of_coreClEx hIc (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_coreEx h hIc))
  obtain ⟨-, -, -, hensS, hrhss, -, -, -, hokQ, -, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hsorts := sortsNumbered_of_coreEx h
  have hov := Semantics.coreOKEx_ovls h
  rw [famEx_eqPP hex]
  unfold KoreAML.denB
  generalize htbl : KoreAML.tableOf [] _ = tbl
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => by
    rw [← htbl]; exact canonKey_mem_existsAll hi
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => by
      rw [← htbl]
      unfold KoreAML.tableOf
      refine List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx ?_ _))
      exact Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _))
        (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk)
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  have hne2 : ∀ (l : List Kore.Pattern) (p q : Kore.Pattern), [p, q] ++ l ≠ [] := fun l p q => by simp
  constructor
  · intro hm
    obtain ⟨e', -, -, hb⟩ := existsAll_elim hD _ e m hnd hsrt hm
    rw [interp_and (hne _ _)] at hb
    have hag := agrees_of_fixKCl hI hs0.2.2.2.1 hsorts hov hσ (is := List.range r.vars.length)
      (fun i hi => List.mem_range.mpr hi) (fun p hp => hb p (List.mem_append_left _ hp))
    have hRm := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [interp_and (hne2 _ _ _)] at hRm
    have := (evalTerm_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg (HoldsShape.preReadAll_of_coreEx h hIc) (clauseExRead_all_of_coreEx h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag
      hrhss m).mp (hRm _ (by simp))
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
          refine (fixEq_iff hI (sortOf_numbered_ofCEx hs0 hsorts hov hsw) hsw m).mpr ⟨hinC, ?_⟩
          have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
            unfold canonKey
            rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
          rw [hvk, overV_at hkeys hi, hg', Option.getD_some]
        · cases hpi
      · rw [List.mem_singleton.mp hp, interp_and (hne2 _ _ _)]
        intro q hq
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact (evalTerm_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg (HoldsShape.preReadAll_of_coreEx h hIc) (clauseExRead_all_of_coreEx h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag
            hrhss m).mpr (((den_closed c y.val).interp e _ m).mp hm)
        · exact reqPat_holds hI (fun t ht b =>
            evalTerm_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg (HoldsShape.preReadAll_of_coreEx h hIc) (clauseExRead_all_of_coreEx h hIc) (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag
              (hensS t ht) b) hinC
        · have hT : r.post.isTop = false := by
            cases hT : r.post.isTop
            · rfl
            · simp [Cond.conj, hT] at hq
          have hq' : q = Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post := by
            simpa [Cond.conj, hT] using hq
          subst hq'
          have hr := reads_of_agrees hσ hag (P := fun i => i ∈ varOccsCond r.vars.length r.post)
            fun i hi => ⟨varOccsCond_lt_twoT r.post hokQ i hi, hkeys i (varOccsCond_lt_twoT r.post hokQ i hi)⟩
          exact (HoldsShape.holds_entailsCEx h hIc hcw r.post hrc hokQ hbdQ (fun i hi _ => hi) hr hkQ top_numbered
            hpost m hinC).mpr rfl

end

end Faithful

end KCore
