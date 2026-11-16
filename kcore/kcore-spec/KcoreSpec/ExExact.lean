/-
  KCore. Exactness, for a definition whose rules may have existential variables.

  - Left to right, in the value model at `T := Step` (`has_model_choice_ex`): every step of `Step`,
    of a rule with existential variables or not, is a step of the model.
  - Right to left, in any model of `Γc` with the step's closure: a successor b of x's element in y's
    element is given by the axiom of a rule r at a valuation of r's variables other than the
    existential ones, each in its sort (`step_successor_axiomEx`); b is in r's right side
    `∃ē. (rhs ∧ ens)`. The binders ē give a valuation that agrees with the first off ē and gives ē
    elements of their sorts; there every variable of r is in its sort, x's element is in the left
    side and in `⌈req = true⌉`, and b is in `rhs ∧ ens`. With the existential variables read as
    ordinary ones (`ruleDropExs`, which changes no premise of `StepBy` but the list `exs`, which
    `StepBy` does not read) that is a σ of values with every premise of `StepBy c r σ x y` but
    the rule's membership and the competitors' (`stepVals_of_right_ex`). No competitor applies at
    values (`successor_split_ex`, under `StepDecided`). So `Step c x y` (`step_of_successor_ex`).
-/
import KcoreSpec.ExComplete
import KcoreSpec.ExConsistent

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The values of a successor in a rule's right side, for a rule that may have existential
variables.** For a rule r with `ruleSorted` and `rulePlainEx` (not asked to be one of the
definition's), in a model of `Γc`, at a valuation that gives each of r's variables other than the
existential ones an element of its sort, where x's element is in r's left side and in
`⌈req = true⌉` and y's element is in r's right side `∃ē. (rhs ∧ ens)`: a σ of values with every
premise of `StepBy c r σ x y` but the rule's membership and the competitors'. -/
theorem stepVals_of_right_ex (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
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
  obtain ⟨-, -, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
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
  exact rule_step_values (r := ruleDropExs r) h hft hI hcw (ruleSorted_dropExs hs) (rulePlainOpen_dropExs hp)
    hrc hw hkeys hinR x y hlR hreqR hyR hensR

end

end Faithful

open ML Faithful

/-- **A successor in a model is a step**, for a semantics that `coreOK` accepts whose functions meet
`FnHyp` and whose rules have `ruleSorted` and `rulePlainEx`: in a model of `Γc` with the step's
closure, where x's element has a successor in y's element, `Step c x y`. -/
theorem step_of_successor_ex (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y := by
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hd := stepDecided_of_rules_ex (hypSound_of_core h) hf.1 hrules x.val
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkeysC, hin, hl, hreq, hcomp, hy⟩ :=
    step_successor_axiomEx hrules x hI e _ hs
  have hbe : b = elemOf c I y.val := ((elemOf_spec hIΓ y.property e).1 b).mp hb
  subst hbe
  obtain ⟨hsr, hpr⟩ := hrules r hr
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    rcases successor_split_ex h hrules x hd hIc hf.2.2.2.2.1.2 hsr hpr (hd r hr) hkeys hkeysC hin hl hreq hcomp hy with
      ⟨-, y', σ, hst, -⟩ | ⟨-, σ, hu, -⟩
    · exact (hst hr).hprio
    · exact hu.2.2
  have hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hr, by simp [List.ne_nil_of_mem hi]⟩
  obtain ⟨σ, hσ, hm, hrq, hpre, hev, hen, hpo⟩ := stepVals_of_right_ex h hf.1 hIc hf.2.2.2.2.1.2 hsr hpr hrc
    (hf.2.2.2.2.1.1 r hr) hkeys hin x y hl hreq hy
  exact step_iff_by.mpr ⟨r, σ, ⟨hr, hσ, hm, hrq, hpre, hev, hen, hpo, hprio⟩⟩

/-- **Exactness of a definition whose rules may have existential variables**: `ExactC`, for a
semantics that `coreOK` accepts whose functions meet `FnHyp` and whose rules have `ruleSorted` and
`rulePlainEx`. Left to right in the value model (`has_model_choice_ex` at `T := Step`), right to
left in any model (`step_of_successor_ex`). -/
theorem exact_ex (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) : ExactC c := by
  intro x y
  constructor
  · intro hs
    obtain ⟨M, hM, I, hI, hT⟩ := has_model_choice_ex c h hf hrules (Step c) (fun _ _ hst => hst)
      (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
      (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
    exact ⟨M, hM, I, hI, (hT x y).mp hs⟩
  · rintro ⟨M, hM, I, hI, hn⟩
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret I e m := Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret I e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    rw [((elemOf_spec hIΓ x.property e).1 m).mp h1] at h2
    exact step_of_successor_ex c h hf hrules hI x y e h2

end KCore
