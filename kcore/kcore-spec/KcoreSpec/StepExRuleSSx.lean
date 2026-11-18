/-
  KCore. The successor's step and the competitors' readings for a rule whose left side need not
  bind every variable, in any model of `Γc c` of a semantics `coreOKEx` accepts, whose functions'
  clauses may bind variables by `\exists`.

  These are the lemmas of OpenSuccessor.lean and OpenRuleStepCl.lean that read the definition,
  for `coreOKEx`: what they read of it is `HypSoundCoreEx` (`hypSoundEx_of_coreEx`), the
  constructors' and confined sorts' values (`confined_valueCEx`), each term's result having a
  result where every function has one (`evalTerm_totalCl`, from `SortCtx` and `OvlOK`), and each
  term's result being what it denotes in the model (`HoldsShape.termSoundEx`), where a clause with
  existential variables is read by `ClauseExRead`.

  - A valuation of a rule's variables in their sorts gives the element of a value of its sort to
    each variable of arm A or B (`rule_witnessedSSx`), to every variable where every open one has
    one (`rule_witnessed_allSSx`); a condition that holds is not refuted (`cond_not_refutedSSx`).
  - A condition that holds in the model evaluates to `true` (`evalTrue_of_modelSSx`); a valuation
    at values gives the step's premises (`rule_step_of_witnessedSSx`), for arms A and B
    (`rule_step_ABSSx`), arm C (`rule_step_CSSx`) and every arm (`rule_step_valuesSSx`).
  - A rule that applies at values applies in the model (`applies_of_valuesSSx`), and where its
    `requires` has a result at each match, `¬applies` at a valuation gives `NotApplies`
    (`notApplies_of_not_appliesSSx`).
-/
import KcoreSpec.TermSoundCEx
import KcoreSpec.OpenCompete
import KcoreSpec.OpenClauseFn
import KcoreSpec.ClausePreCore
import KcoreSpec.RightHeldStep

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A successor's valuation at the variables of arms A and B.** In a model of `Γc c`, at a
valuation of the variables of a well-sorted rule in their sorts where the element of x lies in the
rule's left side and the element of y in its right side, the valuation gives the element of a value
of its sort to each variable held by the left side, held by the right side under constructors only,
or of a confined sort (the last where the definition reads a confined sort). -/
theorem rule_witnessedSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (i : Nat) (hi : i < r.vars.length)
    (harm : (varOccs r.lhs).contains i = true ∨ r.armAB c i = true)
    (hrc : (r.vars[i]?.map c.confined).getD false = true → c.readsConfined = true) :
    Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hlhs, -, -, hrhs⟩ := Semantics.ruleSorted_parts c hs
  rcases harm with hL | hAB
  · obtain ⟨-, hwit⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
      (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
    exact hwit i (List.contains_iff_mem.mp hL)
  simp only [Rule.armAB, Bool.or_eq_true] at hAB
  rcases hAB with hA | hB
  · exact ctorOccs_witnessed hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hrhs y.property hy
      i (List.contains_iff_mem.mp hA)
  · obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
    rw [hvs] at hB
    have hcs' : c.confined s = true := hB
    have hrc' := hrc (by rw [hvs]; exact hB)
    have hin' := hin i hi
    rw [List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
    obtain ⟨v, hv, hden⟩ := confined_valueCEx h hrc' hI hcs' e _ ((inS_iff e).mpr hin')
    have hel := ((elemOf_spec hIΓ hv e).1 _).mpr rfl
    exact witnessed_of hvs hv ((hden _).mp hel)


/-- Each variable is held by the left side or open: where each open variable is given the element
of a value of its sort, so is every variable. -/
theorem rule_witnessed_allSSx (h : c.coreOKEx = true) (hIΓ : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hop : ∀ i ∈ r.opens, Witnessed c I tbl (canonVars c r.vars) r.vars e i) :
    ∀ i < r.vars.length, Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  intro i hi
  by_cases hL : (varOccs r.lhs).contains i = true
  · exact hwitL i (List.contains_iff_mem.mp hL)
  · exact hop i (by simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hL⟩)


/-- **A condition that holds is not refuted.** In a model of `Γc`, where `⌈req = true⌉` holds at
a valuation of the conditions' variables in their sorts, the rule's conditions `∃ō. ⌈req = true⌉`
(`Rule.condK`, the predicate `\top`) are satisfied, so `Rule.Refuted` fails. -/
theorem cond_not_refuted_atSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    (hpre : r.pre = .top) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∈ r.condVars → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    {t : Term} (ht : r.req = some t) {m : M}
    (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c r.vars) t)))).interpret
      I e m) :
    ¬ r.Refuted c := by
  intro href
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  haveI : OvlOK c := (hypSoundEx_of_coreEx h).2.2.2.2.2.2.2.2
  have hD := defOK hIΓ
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
    rw [ht] at hreqK; simpa [reqOK] using hreqK
  have hlt : ∀ i ∈ varOccs t, i < r.vars.length := Exec.sortOfTerm_vars htS
  have hcv : ∀ i ∈ varOccs t, i ∈ r.condVars := fun i hi => by
    simp only [Rule.condVars, ht, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let l := (List.range r.vars.length).filter r.condVars.contains
  have hl : ∀ i ∈ l, i < r.vars.length := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  have hK : r.condK c = KoreAML.existsAll C ((l.map (vs.getD · default)).map KoreAML.Var.kore)
      (.and C [reqPat C (some (Term.kore c vs t))]) := by
    unfold Rule.condK
    rw [← hbs]
    simp [ht, hpre, Cond.conj, Cond.isTop, vs, l, C]
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
  · show (KoreAML.tr ⟨tbl2, []⟩ (.and C [reqPat C (some (Term.kore c vs t))])).interpret I e' m
    rw [KoreAML.tr]
    simp only [KoreAML.trAndList]
    exact (tr_reqPat_congr hIΓ (fun i hi => moveV_at hkeys2 (hlt i hi)
      (List.mem_filter.mpr ⟨List.mem_range.mpr (hlt i hi), by simpa using hcv i hi⟩)) m).mpr hm

/-- `cond_not_refuted_atSSx` at a valuation of every variable in its sort. -/
theorem cond_not_refutedSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    (hpre : r.pre = .top) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    {t : Term} (ht : r.req = some t) {m : M}
    (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c r.vars) t)))).interpret
      I e m) :
    ¬ r.Refuted c :=
  cond_not_refuted_atSSx h hI hs hpre (fun i hi _ => hin i hi) ht hm


/-- **A condition that holds in a model evaluates to `true`**: under a well-sorted σ that agrees
with the valuation, a Bool term whose `⌈t = true⌉` holds has the result `true`, where every
function has a result at arguments of its sorts. -/
theorem evalTrue_of_modelSSx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {vars : List Srt}
    {σ : Subst} (hσ : c.WellSorted vars σ) {tbl : VarTable} {e : Valuation M}
    (hag : Agrees c I tbl (canonVars c vars) σ e) {t : Term}
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some Srt.bool) {m : M}
    (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c vars) t)))).interpret
      I e m) :
    EvalTerm c σ t (some (bool true)) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
  obtain ⟨v, hv⟩ := Model.evalTerm_totalCl hsc hno hft fns_headsOK hσ ht
  by_cases hvt : v = some (bool true)
  · rw [hvt] at hv; exact hv
  · exact absurd hm (reqFalse_empty hIΓ (S' := srtOf c topCellSort)
      (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2 hvt
      (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ ht hu)
      (HoldsShape.termSoundEx h hI hcw hv hσ (canonVars_length c vars) hag ht) m)

/-- **The step a valuation gives, where it gives every variable a value.** For a well-sorted rule
with `rulePlainOpen`, in a model of `Γc`, at a valuation that gives every variable of the rule the
element of a value of its sort, with x's element in the left side and y's in the right side and
the `ensures`, and the `requires` `true` under the valuation's substitution: that substitution has
every premise of `Step.rule` but the rule's membership and `hprio`. -/
theorem rule_step_of_witnessedSSx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) {tbl : VarTable} {e : Valuation M}
    (hwit : ∀ i < r.vars.length, Witnessed c I tbl (canonVars c r.vars) r.vars e i) (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val))
    (hreq : ∀ t, r.req = some t →
      EvalTerm c (substOf c I tbl (canonVars c r.vars) r.vars e) t (some (bool true))) :
    let σ := substOf c I tbl (canonVars c r.vars) r.vars e
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, -, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hpre, hpost⟩ := Semantics.rulePlainOpen_top hp
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := fun i hi => by
    obtain ⟨v, hv, he⟩ := hwit i hi
    rw [← he]; exact (inS_iff e).mp (elemOf_spec hIΓ hv e).2
  obtain ⟨hmatch, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hensK; simpa [reqOK] using hensK
  refine ⟨hσ, hmatch, hreq, hpre ▸ .top, ?_, fun t ht => evalTrue_of_modelSSx h hft hI hcw hσ hag (hensS t ht) (hens t ht),
    hpost ▸ .top⟩
  obtain ⟨v, hv⟩ := Model.evalTerm_totalCl hsc hno hft fns_headsOK hσ hrhs
  have hbR := (HoldsShape.termSoundEx h hI hcw hv hσ (canonVars_length c r.vars)
    hag hrhs _).mp hy
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhs rfl
    have he : elemOf c I yv = elemOf c I y.val := (((elemOf_spec hIΓ hyv e).1 _).mp hbR).symm
    rw [values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hyv) hyv y.property he] at hv
    exact hv

/-- **Case A and B, the step.** Where every open variable passes arm A or B, the valuation's
substitution has every premise of `Step.rule` but the rule's membership and `hprio`. -/
theorem rule_step_ABSSx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) (hAB : r.opens.all (r.armAB c) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : ∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val)) :
    let σ := substOf c I tbl (canonVars c r.vars) r.vars e
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have hwit := rule_witnessed_allSSx h hIΓ hs hin x hl fun i hop =>
    rule_witnessedSSx h hI hs hin x y hl hy i (List.getElem?_eq_some_iff.mp
      (List.getElem?_eq_getElem (by simp only [Rule.opens, List.mem_filter, List.mem_range] at hop; exact hop.1))).1
      (Or.inr (List.all_eq_true.mp hAB i hop)) (fun hc => hrc (List.any_eq_true.mpr ⟨i, hop, hc⟩))
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg (sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)).trans
    (canonVars_length c r.vars) hwit
  exact rule_step_of_witnessedSSx h hft hI hcw hs hp hwit x y hl hy hens fun t ht =>
    evalTrue_of_modelSSx h hft hI hcw hσ hag (by rw [ht] at hreqK; simpa [reqOK] using hreqK) (hreqm t ht)



variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Case C, the step.** Where the conditions are witnessed by values σw, and none of their
variables is held by the left side, the right side or the `ensures`, and every other open variable
passes arm A or B: the valuation that gives the conditions' variables σw's values and keeps the
others has a substitution with every premise of `Step.rule` but the rule's membership and
`hprio`. -/
theorem rule_step_CSSx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
    (harm : ∀ i ∈ r.opens, i ∉ r.condVars → r.armAB c i = true)
    (hcl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs) (hcr : ∀ j ∈ r.condVars, j ∉ varOccs r.rhs)
    (hce : ∀ j ∈ r.condVars, ∀ t, r.ens = some t → j ∉ varOccs t)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    {σw : Subst} (hσw : c.WellSortedAt r.vars r.condVars σw)
    (hreqw : ∀ t, r.req = some t → EvalTerm c σw t (some (bool true)))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, -, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  let vs := canonVars c r.vars
  let n := r.vars.length
  -- the variables outside the conditions are witnessed at e
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  have hwe : ∀ i < n, i ∉ r.condVars → Witnessed c I tbl vs r.vars e i := fun i hi hc => by
    by_cases hL : (varOccs r.lhs).contains i = true
    · exact hwitL i (List.contains_iff_mem.mp hL)
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hL⟩
      exact rule_witnessedSSx h hI hs hin x y hl hy i hi (Or.inr (harm i hop hc))
        (fun hc' => hrc (List.any_eq_true.mpr ⟨i, hop, hc'⟩))
  -- σw's values at the conditions' variables, the valuation's elsewhere
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
  -- the left side, the right side and the `ensures` do not read the conditions' variables
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
  -- the `requires`, from σw
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
  exact ⟨_, rule_step_of_witnessedSSx h hft hI hcw hs hp hwit x y hl'' hy'' hens'' hreq''⟩


variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A successor's valuation can be taken at values** (any model of `Γc`). For a well-sorted rule
with `rulePlainOpen`, at a valuation of its variables in their sorts where x's element lies in the
left side and `⌈req = true⌉`, and y's element in the right side and `⌈ens = true⌉`: a σ of values
with every premise of `Step.rule` but the rule's membership and `hprio`. Each open variable passes
arm A (`ctorOccs_witnessed`), arm B (`confined_value`) or arm C: then the conditions are closed and
`needsWitness` holds, so they are decided; `Refuted` fails at the valuation (`cond_not_refutedSSx`),
and `Witnessed` gives values to all of `condVars`, none of which the left side, the right side or
the `ensures` holds (`rule_step_CSSx`). -/
theorem rule_step_valuesSSx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hensm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.ens.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I y.val)) :
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
  · exact ⟨_, rule_step_ABSSx h hft hI hcw hs hp hAB hrc hin x y hl hreq' hy hens'⟩
  -- an open variable passes arm C only
  have hp' := hp
  simp only [Semantics.rulePlainOpen, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp'
  obtain ⟨⟨⟨-, hpre0⟩, -⟩, harms, -⟩ := hp'
  have hpre : r.pre = .top := Cond.eq_top_of_isTop hpre0
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
  -- the conditions are the `requires`
  obtain ⟨t, ht⟩ : ∃ t, r.req = some t := by
    cases h' : r.req with
    | none =>
      have : r.condVars = [] := by
        show (r.req.map varOccs).getD [] ++ varOccsCond r.vars.length r.pre = []
        rw [h', hpre]; rfl
      rw [this] at hic; cases hic
    | some t => exact ⟨t, rfl⟩
  rcases hw hnw with hW | href
  · obtain ⟨σw, hσw, hreqw, -⟩ := hW
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
    refine rule_step_CSSx h hft hI hcw hs hp (fun j hjo hjc => ?_) hcl
      (fun j hj hjr => hrest j hj (List.mem_append_left _ (List.mem_append_left _ hjr)))
      (fun j hj t' ht' hjt => hrest j hj (List.mem_append_left _ (List.mem_append_right _ (by rw [ht']; exact hjt))))
      hrc hσw hreqw hkeys hin x y hl hy hens'
    · have hj := harms j hjo
      simp only [Rule.armAB, Bool.or_eq_true]
      rcases hj with (hA | hB) | ⟨hjc', -⟩
      · exact Or.inl hA
      · exact Or.inr hB
      · exact absurd (List.contains_iff_mem.mp hjc') hjc
  · exact (cond_not_refutedSSx h hI hs hpre hin ht (hreq' t ht) href).elim


/-- **A rule that applies at values applies in a model.** For a rule with `ruleSorted` and
`rulePlainOpen`, a σ that gives the variables of its left side and conditions values, matches x and
makes the `requires` `true`: x's element is in the rule's `applies` pattern. No arm is read. -/
theorem applies_of_valuesSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) {x : Config c} {σ : Subst}
    (hσ : c.WellSortedAt r.vars r.leftVars σ) (hpv : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation M) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hpre, -⟩ := Semantics.rulePlainOpen_top hp
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
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  rw [applies_eq hpre]
  change (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll C ((l.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))]))).interpret I e (elemOf c I x.val)
  rw [hbs]
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
    HoldsShape.termSoundEx h hI hcw (hreq' t ht) hσ' hvsl hag (hreqS' t ht) b)
    (by have := hxs.2; unfold srtOf; rw [trSort_srt]; exact this)
  -- e3 agrees with e4 at the left side's and conditions' variables, and with e off the binders
  have h34 : ∀ i < n, i ∈ r.leftVars → e4.evalEvar (tbl.ev (keyAt vs i)) = e3.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
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
  · rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨(tr_kore_congr r.lhs (fun i hi => h34 i (hltL i hi) (hlhsL i hi)) _).mp hlx4, ?_⟩
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
      exact (hT tbl e3).mpr (((Closed.sym _).app (Closed.sym _)).interp e4 e3 _ |>.mp ((hT tbl e4).mp hreq4))
    | some t =>
      rw [hq] at hreq4
      exact (tr_reqPat_congr hIΓ (fun i hi => h34 i (hreqLt t hq i hi).1 (hreqLt t hq i hi).2) _).mp hreq4

/-- **A competitor that does not apply in a model does not apply at values**, where its `requires`
has a result at each match (the first conjunct of `StepDecided` for the rule): for a rule with
`ruleSorted` and `rulePlainOpen`, if x's element is not in its `applies` pattern at a valuation,
then `NotApplies`. No arm is read. -/
theorem notApplies_of_not_appliesSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) {x : Config c}
    (hd : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation M)
    (hna : ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val)) :
    NotApplies c r x.val := by
  intro σ hσ hpv
  obtain ⟨-, hpre, -⟩ := Semantics.rulePlainOpen_top hp
  cases ht : r.req with
  | none =>
    exact absurd (applies_of_valuesSSx h hI hcw hs hp hσ hpv (fun t h' => by rw [ht] at h'; cases h') hkeys e) hna
  | some t =>
    obtain ⟨v, hv⟩ := (hd σ hσ hpv).1 t ht
    by_cases hvt : v = some (bool true)
    · refine absurd (applies_of_valuesSSx h hI hcw hs hp hσ hpv (fun t' h' => ?_) hkeys e) hna
      rw [ht] at h'; cases h'; rw [hvt] at hv; exact hv
    · exact RuleReqFails.intro ht hv hvt


end

end Faithful

end KCore
