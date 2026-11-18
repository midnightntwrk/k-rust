/-
  KCore. Exactness right to left, for a semantics `coreOKEx` accepts, whose functions' clauses
  may bind variables by `\exists` and whose rules may have existential variables.

  In any model of `Γc` with the step's closure, a successor b of x's element in y's element is
  given by the axiom of a rule r at a valuation of r's variables other than the existential ones,
  each in its sort (`step_successor_axiomEx`, which reads nothing of the functions); b is in r's
  right side `∃ē. (rhs ∧ ens)`. Inside the binders ē, with the existential variables read as
  ordinary ones (`ruleDropExs`), the valuation gives a σ of values with every premise of
  `StepBy c r σ x y` but the rule's membership and the competitors' (`stepVals_of_right_exSSx`, from
  `rule_step_valuesSSx`). A competitor's `requires` has a result at each match, its variables being
  the left side's (`evalTerm_total_atCl`), and x's element is in no competitor's `applies`, so no
  competitor applies at values (`successor_prio_exSSx`). So `Step c x y`
  (`step_of_successor_exCEx_of`, from the three parts of `FnHyp` the step reads, and
  `step_of_successor_exCEx` under `FnHyp`).
-/
import KcoreSpec.StepExRuleSSx
import KcoreSpec.ExComplete
import KcoreSpec.OpenClauseModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The values of a successor in a rule's right side, for a rule that may have existential
variables**, for a semantics `coreOKEx` accepts. For a rule r with `ruleSorted` and `rulePlainEx`
(not asked to be one of the definition's), in a model of `Γc`, at a valuation that gives each of
r's variables other than the existential ones an element of its sort, where x's element is in r's
left side and in `⌈req = true⌉` and y's element is in r's right side `∃ē. (rhs ∧ ens)`: a σ of
values with every premise of `StepBy c r σ x y` but the rule's membership and the competitors'. -/
theorem stepVals_of_right_exSSx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  obtain ⟨-, -, -, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  obtain ⟨hlhs, -, hreqs, -, -, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨-, hpost₀⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  -- the left side's and the `requires`' variables are not existential
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  -- inside `∃ē`: a valuation that agrees with e off ē and gives ē elements of their sorts
  rw [Model.ruleRight_eqEx hpost₀ hlt] at hy
  obtain ⟨eR, hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hy
  unfold Model.ruleRightBody at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  obtain ⟨hyR, hensR⟩ := hbody
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      eR.evalEvar (tbl.ev (canonKey c r.vars i)) = e.evalEvar (tbl.ev (canonKey c r.vars i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
  -- there every variable of r, existential or not, is in its sort
  have hinR : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (eR.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (by rw [canonVars_getD c hi]; rfl)
    · show InS I _ (eR.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoffE i hi hx]; exact hin i hi hx
  have hlR : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I eR (elemOf c I x.val) :=
    (tr_kore_congr r.lhs (fun i hi => (hoffE i (hnxL i hi).1 (hnxL i hi).2).symm) _).mp hl
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I eR (elemOf c I x.val) :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl eR)
  -- with the existential variables read as ordinary ones, the step's values
  exact rule_step_valuesSSx (r := ruleDropExs r) h hft hI hcw (ruleSorted_dropExs hs) (rulePlainOpen_dropExs hp)
    hrc hw hkeys hinR x y hlR hreqR hyR hensR


/-- **No competitor applies at values**, for a rule r of a definition `coreOKEx` accepts whose rules
have `ruleSorted` and `rulePlainEx` and whose functions have a result at arguments of their sorts,
in a model of `Γc`, at a valuation under a table holding the variables of the competitors' left
sides where x's element is in no competitor's `applies`. A competitor, read with its existential
variables as ordinary ones, has `\top` predicates, and its `requires` reads only the left side's
variables, so it has a result at each match (`evalTerm_total_atCl`); then `¬applies` gives
`NotApplies` (`notApplies_of_not_appliesSSx`, `notApplies_ofDropExs`). -/
theorem successor_prio_exSSx (h : c.coreOKEx = true) (hft : FnTerminates c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x : Config c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    {tbl : VarTable}
    (hkeysC : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
      canonKey c r'.vars i ∈ tbl)
    {e : Valuation M}
    (hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio →
      ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e (elemOf c I x.val)) :
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  intro r' hr' hlt'
  have hs' := ruleSorted_dropExs (hrules r' hr').1
  have hp' := rulePlainOpen_dropExs (hrules r' hr').2
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs'
  obtain ⟨-, hpre, -⟩ := Semantics.rulePlainOpen_top hp'
  have hd : ∀ σ, c.WellSortedAt (ruleDropExs r').vars (ruleDropExs r').leftVars σ →
      PatVal c σ (ruleDropExs r').lhs x.val →
      (∀ t, (ruleDropExs r').req = some t → ∃ v, EvalTerm c σ t v) ∧
        ∃ b, Holds c (ruleDropExs r').vars.length σ (ruleDropExs r').pre b := fun σ hσ _ =>
    ⟨fun t ht => evalTerm_total_atCl hsc hno hft fns_headsOK hσ (Rule.req_leftVars ht)
        (by rw [ht] at hreqK; simpa [reqOK] using hreqK),
      ⟨true, hpre ▸ .top⟩⟩
  exact notApplies_ofDropExs (notApplies_of_not_appliesSSx (r := ruleDropExs r') h hI hcw hs' hp' hd
    (hkeysC r' hr' hlt') e (hcomp r' hr' hlt'))

end

end Faithful

open ML Faithful

/-- **A successor in a model is a step**, for a semantics that `coreOKEx` accepts whose functions
have a result at arguments of their sorts (`FnTerminates`), whose rules' and clauses' conditions
are decided where `needsWitness` holds (`OpenDecided`), and whose rules have `ruleSorted` and
`rulePlainEx`: in a model of `Γc` with the step's closure, where x's element has a successor in
y's element, `Step c x y`. -/
theorem step_of_successor_exCEx_of (c : Semantics) (h : c.coreOKEx = true) (hft : FnTerminates c)
    (hod : OpenDecided c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y := by
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkeysC, hin, hl, hreq, hcomp, hy⟩ :=
    step_successor_axiomEx hrules x hI e _ hs
  have hbe : b = elemOf c I y.val := ((elemOf_spec hIΓ y.property e).1 b).mp hb
  subst hbe
  obtain ⟨hsr, hpr⟩ := hrules r hr
  have hprio := successor_prio_exSSx h hft hrules x hIc hod.2 hkeysC hcomp
  have hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hr, by simp [List.ne_nil_of_mem hi]⟩
  obtain ⟨σ, hσ, hm, hrq, hpre, hev, hen, hpo⟩ := stepVals_of_right_exSSx h hft hIc hod.2 hsr hpr hrc
    (hod.1 r hr) hkeys hin x y hl hreq hy
  exact step_iff_by.mpr ⟨r, σ, ⟨hr, hσ, hm, hrq, hpre, hev, hen, hpo, hprio⟩⟩

/-- **A successor in a model is a step**, for a semantics that `coreOKEx` accepts whose functions
meet `FnHyp` and whose rules have `ruleSorted` and `rulePlainEx`; the functions' clauses may bind variables by
`\exists`. -/
theorem step_of_successor_exCEx (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y :=
  step_of_successor_exCEx_of c h hf.1 hf.2.2.2.2.1 hrules hI x y e hs

end KCore
