/-
  KCore. A successor's valuation can be taken at values, for a rule with predicates.

  For a well-sorted rule with `rulePlainPP` (its `pre` and `post` need not be `\top`), in a model of
  `Γc`, at a valuation of its variables in their sorts where x's element lies in the left side,
  `⌈req = true⌉` and `pre`, and y's element in the right side, `⌈ens = true⌉` and `post`: a σ of
  values with every premise of `StepBy` but the rule's membership and `hprio`, `Holds … pre true`
  and `Holds … post true` included (`rule_step_values_pp`).

  - Where the valuation gives every variable the element of a value (`rule_step_of_witnessed_pp`):
    the predicates have a truth value at its substitution (`holds_decided`), and in a model of `Γc`
    a predicate holds at an element exactly where that value is `true` (`holds_entails`), so both
    are `true` (`holds_of_conjPP`).
  - Arms A and B (`rule_step_AB_pp`): the valuation is one of values.
  - Arm C (`rule_step_C_pp`): the conditions' variables take the witness's values σw. `pre` holds
    x's element under the changed valuation, which reads σw at `pre`'s variables, because
    `Holds … pre true` at σw (`Witnessed`); `post` holds y's element there as under the first
    valuation, which it agrees with at `post`'s variables, none of which is a condition variable
    (`condApart`; `tr_condKore_twoT` with one table).
  - A refuted condition contradicts the valuation (`cond_not_refuted_pp`): x's element is in
    `∃ō. (⌈req = true⌉ ∧ pre)` under the table of that sentence (`tr_condKore_twoT`).
-/
import KcoreSpec.OpenRuleStepCl
import KcoreSpec.CondTwoTables
import KcoreSpec.ClausePreCore
import KcoreSpec.HoldsDecided
import KcoreSpec.OpenSplit
import KcoreSpec.PredPlain

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A predicate that holds at an element is `true`**, in a model of `Γc`, at a σ that gives its
free variables values whose elements the valuation gives them. -/
theorem holdsTrue_of_memPP (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst}
    (hσ : c.WellSortedAt vars (varOccsCond vars.length p) σ) {tbl : VarTable} {e : Valuation M}
    (hr : Reads c I vars (fun i => i ∈ varOccsCond vars.length p) σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p)).interpret I e a) :
    Holds c vars.length σ p true := by
  obtain ⟨b, hb⟩ := holds_decided (hypSound_of_core h) hft p hok hσ
  have hiff := HoldsShape.holds_entails h hI hcw p hrc hok hbd (fun i hi _ => hi) hr hk top_numbered hb a ha
  rw [hiff.mp hm] at hb
  exact hb

/-- `holdsTrue_of_memPP` over the conjuncts a predicate adds to a sentence (none for `\top`), at a
σ well sorted on every variable that agrees with the valuation. -/
theorem holds_of_conjPP (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst} (hσ : c.WellSorted vars σ)
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (hm : ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    Holds c vars.length σ p true := by
  by_cases hT : p.isTop = true
  · rw [Cond.eq_top_of_isTop hT]; exact .top
  · refine holdsTrue_of_memPP h hft hI hcw hok hbd hrc (hσ.at _)
      (reads_of_agrees hσ hag fun i hi => ⟨varOccsCond_lt_twoT p hok i hi, hkeys i (varOccsCond_lt_twoT p hok i hi)⟩)
      hk ha (hm _ ?_)
    simp [Cond.conj, hT]

/-- An element of a configuration is in the configuration sort, under every table. -/
theorem inh_top_PP (hIΓ : I ⊧ᴵP Γ c) (x : Config c) (tbl : VarTable) (e : Valuation M) :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e (elemOf c I x.val) := by
  rw [trSort_srtOf_twoT]
  exact (elemOf_spec hIΓ x.property e).2

/-- **The step a valuation gives, where it gives every variable a value**, for a rule with
predicates: `rule_step_of_witnessed`'s conclusion, x's element in `pre` and y's in `post` read by
the Holds lemma. -/
theorem rule_step_of_witnessed_pp (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hwit : ∀ i < r.vars.length, Witnessed c I tbl (canonVars c r.vars) r.vars e i) (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val))
    (hreq : ∀ t, r.req = some t →
      EvalTerm c (substOf c I tbl (canonVars c r.vars) r.vars e) t (some (bool true))) :
    let σ := substOf c I tbl (canonVars c r.vars) r.vars e
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, -, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, hokQ⟩, hbdP⟩, hbdQ⟩, -⟩ := hs'
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := fun i hi => by
    obtain ⟨v, hv, he⟩ := hwit i hi
    rw [← he]; exact (inS_iff e).mp (elemOf_spec hIΓ hv e).2
  obtain ⟨hmatch, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) hlhs x.property hl
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hensK; simpa [reqOK] using hensK
  refine ⟨hσ, hmatch, hreq,
    holds_of_conjPP h hft hI hcw hokP hbdP hrcP hσ hag hkeys hkP (inh_top_PP hIΓ x tbl e) hprem, ?_,
    fun t ht => evalTrue_of_model h hft hI hcw hσ hag (hensS t ht) (hens t ht),
    holds_of_conjPP h hft hI hcw hokQ hbdQ hrcQ hσ hag hkeys hkQ (inh_top_PP hIΓ y tbl e) hpostm⟩
  obtain ⟨v, hv⟩ := Model.evalTerm_total (hypSound_of_core h) hft fns_headsOK hσ hrhs
  have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
    (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI)) (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK
    hσ (canonVars_length c r.vars) hag hrhs _).mp hy
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhs rfl
    have he : elemOf c I yv = elemOf c I y.val := (((elemOf_spec hIΓ hyv e).1 _).mp hbR).symm
    rw [values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hyv) hyv y.property he] at hv
    exact hv

/-- **Arms A and B, for a rule with predicates.** Where every open variable passes arm A or B,
the valuation's substitution has every premise of `StepBy` but the rule's membership and
`hprio`. -/
theorem rule_step_AB_pp (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hAB : r.opens.all (r.armAB c) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : ∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val)) :
    let σ := substOf c I tbl (canonVars c r.vars) r.vars e
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have hwit := rule_witnessed_all h hIΓ hs hin x hl fun i hop =>
    rule_witnessed h hI hs hin x y hl hy i (List.getElem?_eq_some_iff.mp
      (List.getElem?_eq_getElem (by simp only [Rule.opens, List.mem_filter, List.mem_range] at hop; exact hop.1))).1
      (Or.inr (List.all_eq_true.mp hAB i hop)) (fun hc => hrc (List.any_eq_true.mpr ⟨i, hop, hc⟩))
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
    (canonVars_length c r.vars) hwit
  exact rule_step_of_witnessed_pp h hft hI hcw hs hrcP hrcQ hkeys hkP hkQ hwit x y hl hprem hy hens hpostm
    fun t ht => evalTrue_of_model h hft hI hcw hσ hag (by rw [ht] at hreqK; simpa [reqOK] using hreqK) (hreqm t ht)

/-- **A refuted condition contradicts a valuation**, for a rule with predicates: where x's element
is in `⌈req = true⌉` and `pre` at a valuation that gives the condition variables elements of their
sorts, through a table holding their keys, the conditions are not refuted. -/
theorem cond_not_refuted_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
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
  haveI : OvlOK c := (hypSound_of_core h).2.2.2.2.2.2.2.2
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

/-- **Arm C, for a rule with predicates.** Where the conditions are witnessed by values σw (their
`requires` `true`, their `pre` holding), none of their variables is held by the left side, the
right side, the `ensures` or `post`, and every other open variable passes arm A or B: the
valuation that gives the conditions' variables σw's values and keeps the others has a substitution
with every premise of `StepBy` but the rule's membership and `hprio`. -/
theorem rule_step_C_pp (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (harm : ∀ i ∈ r.opens, i ∉ r.condVars → r.armAB c i = true)
    (hcl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs) (hcr : ∀ j ∈ r.condVars, j ∉ varOccs r.rhs)
    (hce : ∀ j ∈ r.condVars, ∀ t, r.ens = some t → j ∉ varOccs t)
    (hcq : ∀ j ∈ r.condVars, j ∉ varOccsCond r.vars.length r.post)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {σw : Subst} (hσw : c.WellSortedAt r.vars r.condVars σw)
    (hreqw : ∀ t, r.req = some t → EvalTerm c σw t (some (bool true)))
    (hprew : Holds c r.vars.length σw r.pre true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, hokQ⟩, hbdP⟩, -⟩, -⟩ := hs'
  let vs := canonVars c r.vars
  let n := r.vars.length
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) hlhs x.property hl
  have hwe : ∀ i < n, i ∉ r.condVars → Witnessed c I tbl vs r.vars e i := fun i hi hc => by
    by_cases hL : (varOccs r.lhs).contains i = true
    · exact hwitL i (List.contains_iff_mem.mp hL)
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hL⟩
      exact rule_witnessed h hI hs hin x y hl hy i hi (Or.inr (harm i hop hc))
        (fun hc' => hrc (List.any_eq_true.mpr ⟨i, hop, hc'⟩))
  let σmix : Subst := (List.range n).map fun i => (i, if r.condVars.contains i then (σw.lookup i).getD default
    else pick c I (r.vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i))))
  have hmix : ∀ i < n, σmix.lookup i = some (if r.condVars.contains i then (σw.lookup i).getD default
      else pick c I (r.vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i)))) := fun i hi => by
    simp only [σmix]
    rw [List.range_eq_range', lookup_range', if_pos ⟨Nat.zero_le _, by omega⟩]
  let e'' := overV c I tbl r.vars σmix e
  have hoff : ∀ i < n, i ∉ r.condVars →
      e''.evalEvar (tbl.ev (keyAt vs i)) = e.evalEvar (tbl.ev (keyAt vs i)) := fun i hi hc => by
    show (overV c I tbl r.vars σmix e).evalEvar (tbl.ev (canonKey c r.vars i)) = _
    rw [overV_at hkeys hi, hmix i hi, if_neg (by simpa using hc), Option.getD_some]
    exact (pick_spec (hwe i hi hc)).2
  have hon : ∀ i < n, i ∈ r.condVars → ∀ w, σw.lookup i = some w →
      e''.evalEvar (tbl.ev (keyAt vs i)) = elemOf c I w := fun i hi hc w hw => by
    show (overV c I tbl r.vars σmix e).evalEvar (tbl.ev (canonKey c r.vars i)) = _
    rw [overV_at hkeys hi, hmix i hi, if_pos (by simpa using hc), hw, Option.getD_some, Option.getD_some]
  have hσwv : ∀ i < n, i ∈ r.condVars → ∃ w, σw.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
    fun i hi hc => hσw i hc _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hwit : ∀ i < n, Witnessed c I tbl vs r.vars e'' i := fun i hi => by
    by_cases hc : i ∈ r.condVars
    · obtain ⟨w, hw, hws⟩ := hσwv i hi hc
      exact ⟨w, hws, (hon i hi hc w hw).symm⟩
    · obtain ⟨v, hv, he⟩ := hwe i hi hc
      exact ⟨v, hv, by rw [hoff i hi hc]; exact he⟩
  have hin'' : ∀ i < n, InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt vs i))) := fun i hi => by
    obtain ⟨v, hv, he⟩ := hwit i hi
    rw [← he]; exact (inS_iff e'').mp (elemOf_spec hIΓ hv e'').2
  have hag : ∀ (T : Term), (∀ i ∈ varOccs T, i < n) → (∀ j ∈ r.condVars, j ∉ varOccs T) →
      ∀ i ∈ varOccs T, e.evalEvar (tbl.ev (keyAt vs i)) = e''.evalEvar (tbl.ev (keyAt vs i)) :=
    fun T hlt hT i hi => (hoff i (hlt i hi) (fun hc => hT i hc hi)).symm
  have hl'' := (tr_kore_congr r.lhs (hag r.lhs (Exec.sortOfTerm_vars hlhs) hcl) _).mp hl
  have hy'' := (tr_kore_congr r.rhs (hag r.rhs (Exec.sortOfTerm_vars hrhs) hcr) _).mp hy
  have hens'' : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c vs t)))).interpret I e'' (elemOf c I y.val) := fun t ht => by
    have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
      rw [ht] at hensK; simpa [reqOK] using hensK
    exact (tr_reqPat_congr hIΓ (hag t (Exec.sortOfTerm_vars htS) (fun j hj => hce j hj t ht)) _).mp (hens t ht)
  -- `post` holds no condition variable: it reads e'' as e
  have hpost'' : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' (elemOf c I y.val) := fun φ hφ => by
    by_cases hT : r.post.isTop = true
    · simp [Cond.conj, hT] at hφ
    · obtain rfl : φ = Cond.kore c vs (srtOf c topCellSort) r.post := by simpa [Cond.conj, hT] using hφ
      refine (tr_condKore_twoT hD r.post hokQ (fun k hk0 => ⟨hkQ k hk0, hkQ k hk0⟩) (fun i hi => ?_) _).mp
        (hpostm _ (by simp [Cond.conj, hT]))
      have hlt := varOccsCond_lt_twoT r.post hokQ i hi
      exact ⟨hkeys i hlt, hkeys i hlt, (hoff i hlt (fun hc => hcq i hc hi)).symm⟩
  -- `pre` holds at σw, which e'' reads at `pre`'s variables
  have hpre'' : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' (elemOf c I x.val) := fun φ hφ => by
    by_cases hT : r.pre.isTop = true
    · simp [Cond.conj, hT] at hφ
    · obtain rfl : φ = Cond.kore c vs (srtOf c topCellSort) r.pre := by simpa [Cond.conj, hT] using hφ
      have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre) σw tbl e'' := fun i hi => by
        have hlt := varOccsCond_lt_twoT r.pre hokP i hi
        have hc : i ∈ r.condVars := List.mem_append_right _ hi
        obtain ⟨w, hw, hws⟩ := hσwv i hlt hc
        refine ⟨hlt, hkeys i hlt, w, hw, hws, fun m => ?_⟩
        have hon' : e''.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I w := hon i hlt hc w hw
        rw [hon']
        exact ((elemOf_spec hIΓ hws e'').1 m).symm
      exact (HoldsShape.holds_entails h hI hcw r.pre hrcP hokP hbdP (fun i hi _ => hi) hreads hkP top_numbered
        hprew _ (inh_top_PP hIΓ x tbl e'')).mpr rfl
  have hreq'' : ∀ t, r.req = some t → EvalTerm c (substOf c I tbl vs r.vars e'') t (some (bool true)) :=
    fun t ht => Exec.EvalTerm.congr (hreqw t ht) fun i hi => by
      have hc : i ∈ r.condVars := by
        simp only [Rule.condVars, ht, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
      obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
      have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
        rw [ht] at hreqK; simpa [reqOK] using hreqK
      have hi' := Exec.sortOfTerm_vars htS i hi
      obtain ⟨w, hw, hws⟩ := hσwv i hi' hc
      rw [hw, substOf_var hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin''
        (List.getElem?_eq_getElem hi') (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at hws; exact hws)
        (hon i hi' hc w hw).symm]
  exact ⟨_, rule_step_of_witnessed_pp h hft hI hcw hs hrcP hrcQ hkeys hkP hkQ hwit x y hl'' hpre'' hy'' hens''
    hpost'' hreq''⟩

/-- **A successor's valuation can be taken at values, for a rule with predicates** (any model of
`Γc`). For a well-sorted rule with `rulePlainPP`, at a valuation of its variables in their sorts
where x's element lies in the left side, `⌈req = true⌉` and `pre`, and y's element in the right
side, `⌈ens = true⌉` and `post`: a σ of values with every premise of `StepBy` but the rule's
membership and `hprio`. Each open variable passes arm A, B or C; under arm C the conditions are
closed and `needsWitness` holds, so they are decided: `Refuted` fails at the valuation
(`cond_not_refuted_pp`), and `Witnessed` gives values to all of `condVars`, none of which the left
side, the right side, the `ensures` or `post` holds (`rule_step_C_pp`). The keys of the
predicates' variables are in the table, and a predicate with a binder is read where the definition
reads a confined sort. -/
theorem rule_step_values_pp (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainPP r = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hensm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.ens.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hreq' : ∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I x.val) := fun t ht => by
    rw [ht] at hreqm; exact hreqm
  have hens' : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val) := fun t ht => by
    rw [ht] at hensm; exact hensm
  by_cases hAB : r.opens.all (r.armAB c) = true
  · exact ⟨_, rule_step_AB_pp h hft hI hcw hs hAB hrc hrcP hrcQ hkeys hkP hkQ hin x y hl hreq' hprem hy hens' hpostm⟩
  -- an open variable passes arm C only
  have hp' := hp
  simp only [Semantics.rulePlainPP, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp'
  obtain ⟨harms, -⟩ := hp'
  obtain ⟨i, hio, hiAB⟩ : ∃ i ∈ r.opens, r.armAB c i = false := by
    refine Classical.byContradiction fun hne => hAB (List.all_eq_true.mpr fun i hi => ?_)
    cases hb : r.armAB c i
    · exact absurd ⟨i, hi, hb⟩ hne
    · rfl
  have hiC := harms i hio
  simp only [Rule.armAB, Bool.or_eq_false_iff] at hiAB
  rw [hiAB.1, hiAB.2] at hiC
  simp only [Bool.false_eq_true, false_or, Bool.not_eq_eq_eq_not, Bool.not_true] at hiC
  obtain ⟨hic, hclosed, hapart⟩ := hiC
  -- so the conditions are closed and `needsWitness` holds
  have hnw : r.needsWitness c = true := by
    have hoc : i ∈ r.openCondVars := List.mem_filter.mpr ⟨hio, hic⟩
    have h1 : r.reqOpen = true := by
      unfold Rule.reqOpen
      cases h' : r.openCondVars with
      | nil => rw [h'] at hoc; cases hoc
      | cons _ _ => rfl
    have h3 : (r.openCondVars.all fun i => (r.vars[i]?.map c.confined).getD false) = false :=
      List.all_eq_false.mpr ⟨i, hoc, by rw [hiAB.2]; exact Bool.false_ne_true⟩
    unfold Rule.needsWitness
    rw [h1, hclosed, h3]; rfl
  rcases hw hnw with hW | href
  · obtain ⟨σw, hσw, hreqw, hprew⟩ := hW
    have hcl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs := fun j hj hjl => by
      have hc2 := hclosed
      unfold Rule.reqClosed at hc2
      have := List.all_eq_true.mp hc2 j hj
      rw [List.contains_iff_mem.mpr hjl] at this
      exact absurd this (by decide)
    have hrest : ∀ j ∈ r.condVars, j ∉ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
        varOccsCond r.vars.length r.post := fun j hj hjr => by
      have := hapart j hj
      rw [List.contains_iff_mem.mpr hjr] at this
      exact absurd this (by decide)
    refine rule_step_C_pp h hft hI hcw hs (fun j hjo hjc => ?_) hcl
      (fun j hj hjr => hrest j hj (List.mem_append_left _ (List.mem_append_left _ hjr)))
      (fun j hj t' ht' hjt => hrest j hj (List.mem_append_left _ (List.mem_append_right _ (by rw [ht']; exact hjt))))
      (fun j hj hjq => hrest j hj (List.mem_append_right _ hjq))
      hrc hrcP hrcQ hσw hreqw hprew hkeys hkP hkQ hin x y hl hy hens' hpostm
    · have hj := harms j hjo
      simp only [Rule.armAB, Bool.or_eq_true]
      rcases hj with (hA | hB) | ⟨hjc', -⟩
      · exact Or.inl hA
      · exact Or.inr hB
      · exact absurd (List.contains_iff_mem.mp hjc') hjc
  · exact (cond_not_refuted_pp h hI hs (fun i hi _ => hkeys i hi) hkP (fun i hi _ => hin i hi) hreqm hprem href).elim

end

end Faithful

end KCore
