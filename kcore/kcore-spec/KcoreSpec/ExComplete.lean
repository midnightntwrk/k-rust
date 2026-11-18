/-
  KCore. Completeness at a configuration, for a definition whose rules may have existential
  variables, in any model of `Γc` with the step's closure.

  The step's closure gives a successor b of x a disjunct, the axiom of a rule r of the definition
  at a valuation of r's variables other than the existential ones, each in its sort
  (`step_successor_axiomEx`): x's element is in the left side, in `⌈req = true⌉` and in no
  competitor's `applies`; b is in r's right side `∃ē. (rhs ∧ ens)`. The binders ē of the right side
  give a valuation that agrees with the first off ē and gives ē elements of their sorts; there the
  left side binds the variables it holds at values, and b is in `rhs ∧ ens`. A competitor that
  does not apply in the model does not apply at values, read with its existential variables as
  ordinary ones (`ruleDropExs`: its `applies` and its `NotApplies` are the same). Then
  (`successor_split_ex`):
  - where r's left side binds every variable (`r.opens = []`, so r has no existential variable), b is
    the element of the value r's right side evaluates to: a step of `Step`;
  - otherwise b is in `famOpen c r σ` at the match σ: the variables of r other than ē take the
    valuation's elements under `famOpen`'s outer binders, and ē theirs under `∃ē`.
  `complete_at_ex`: every successor is in an outcome of any list holding those.
-/
import KcoreSpec.ExSound
import KcoreSpec.OpenComplete

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

/-! ## A rule with its existential variables read as ordinary ones does not apply where it does not -/

section
variable {c : Semantics}

/-- `NotApplies` reads the left side and the conditions only: read with its existential variables
as ordinary ones, a rule does not apply exactly where it does not. -/
theorem notApplies_ofDropExs {r : Rule} {x : GroundTerm} (hna : NotApplies c (ruleDropExs r) x) :
    NotApplies c r x := fun σ hσ hm => by
  cases hna σ hσ hm with
  | intro ht he hv => exact .intro ht he hv
  | pre hb => exact .pre hb

end

/-! ## The pattern `famOpen` reads, for a rule with `rulePlainEx` -/

section
variable {c : Semantics}

/-- `famOpen`'s pattern for a rule with `\top` predicates: the variables other than the existential
ones bound, those of the left side fixed to their values under σ, the `requires`, and the right side
`∃ē. (rhs ∧ ens)`. -/
def famOpenPatEx (c : Semantics) (r : Rule) (σ : Subst) : Kore.Pattern :=
  KoreAML.existsAll (srtOf c topCellSort)
    (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
      fun i => ((canonVars c r.vars).getD i default).kore)
    (.and (srtOf c topCellSort) (fixK c r σ (varOccs r.lhs) ++
      [reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
      [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBody c r)]))

/-- The pattern `famOpen` reads, for a rule whose predicates are `\top` (not asked to be one of the
definition's). -/
theorem famOpen_eqEx {r : Rule} (hpre : r.pre = .top) (hpost : r.post = .top)
    (hlt : ∀ i ∈ r.exs, i < r.vars.length) (σ : Subst) :
    famOpen c r σ = KoreAML.denB (famOpenPatEx c r σ) := by
  unfold famOpen famOpenPatEx
  dsimp only
  rw [Model.ruleRight_eqEx hpost hlt, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1), List.map_map]
  simp only [hpre, Cond.conj, Cond.isTop, ite_true, List.append_nil]
  rfl

/-- Every variable of a rule has its key in the table of `famOpen`'s pattern. -/
theorem famOpen_keysEx {r : Rule} {σ : Subst} :
    ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.tableOf [] (famOpenPatEx c r σ) := by
  intro i hi
  unfold KoreAML.tableOf famOpenPatEx
  refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
  by_cases hx : i ∈ r.exs
  · refine Model.varsOf_existsAll_bodyEx ?_ _
    refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
    exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx)
  · exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore)
      (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hx⟩))

end

/-! ## A valuation moved to another table at listed variables -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

open Classical in
/-- The valuation that gives the canonical variables of `vars` listed in `is`, through `tbl'`, the
elements `src` gives them through `tbl`, and agrees with `base` elsewhere. -/
noncomputable def copyVEx (c : Semantics) (tbl tbl' : VarTable) (vars : List Srt) (is : List Nat)
    (src base : Valuation M) : Valuation M :=
  ⟨fun x => if h : ∃ i < vars.length, i ∈ is ∧ x = tbl'.ev (canonKey c vars i)
    then src.evalEvar (tbl.ev (canonKey c vars (Classical.choose h))) else base.evalEvar x, base.evalSvar⟩

theorem copyVEx_at {tbl tbl' : VarTable} {vars : List Srt} {is : List Nat} {src base : Valuation M}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl') {i : Nat} (hi : i < vars.length) (his : i ∈ is) :
    (copyVEx c tbl tbl' vars is src base).evalEvar (tbl'.ev (canonKey c vars i)) =
      src.evalEvar (tbl.ev (canonKey c vars i)) := by
  have hex : ∃ j < vars.length, j ∈ is ∧ tbl'.ev (canonKey c vars i) = tbl'.ev (canonKey c vars j) :=
    ⟨i, hi, his, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, -, hje⟩ := Classical.choose_spec hex
  rw [(canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys _ hj) hje)).symm]

theorem copyVEx_off {tbl tbl' : VarTable} {vars : List Srt} {is : List Nat} {src base : Valuation M} {x : EVar}
    (hx : ∀ i < vars.length, i ∈ is → x ≠ tbl'.ev (canonKey c vars i)) :
    (copyVEx c tbl tbl' vars is src base).evalEvar x = base.evalEvar x := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (fun ⟨i, hi, his, he⟩ => hx i hi his he)]

end

/-! ## The axiom of a rule with `rulePlainEx`, in any model -/

section
variable {c : Semantics}

/-- **A rule's axiom `\rewrites(L, ∃ē. (rhs ∧ ens))`, its left part `L` read**, for a rule with
`ruleSorted` and `rulePlainEx` (not asked to be one of the definition's) in a definition whose rules
have both: every variable of the rule is a variable of `L`, those other than ē occur free in it, the
canonical variables of the left sides and conditions of its competitors are among `L`'s, and an
element of `L` is in the left side and in `⌈req = true⌉`, and in no competitor's `applies`. -/
theorem rule_partsEx {M : Type} {I : Interpretation KoreAML.Sym M}
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ i < r.vars.length, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] L) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
        canonKey c r'.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.tr ⟨tbl, []⟩ L).interpret I e a →
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e a ∧
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret
          I e a ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio →
          ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e a := by
  obtain ⟨-, hocc, -, -, -, -, -⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨hpre₀, -⟩ := Semantics.rulePlainEx_top hp
  obtain ⟨hRf, hRv⟩ := Model.ruleRight_keysEx hs hp
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let n := r.vars.length
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  -- the keys of the parts
  have hreqK : ∀ {k : KoreAML.VarKey} {p : Kore.Pattern}, k ∈ KoreAML.freeOf [] p → k ∈ KoreAML.varsOf p →
      k ∈ KoreAML.freeOf [] (reqPat C (some p)) ∧ k ∈ KoreAML.varsOf (reqPat C (some p)) := fun hf hv => by
    simp only [reqPat]
    rw [KoreAML.freeOf, KoreAML.varsOf]
    exact ⟨List.mem_append_left _ hf, List.mem_append_left _ (List.mem_append_right _ hv)⟩
  have hceilK : ∀ {k : KoreAML.VarKey}, (k ∈ KoreAML.freeOf [] (ruleRight c r) →
      k ∈ KoreAML.freeOf [] (.ceil C C (ruleRight c r))) ∧
      (k ∈ KoreAML.varsOf (ruleRight c r) → k ∈ KoreAML.varsOf (.ceil C C (ruleRight c r))) :=
    ⟨fun hk => by rw [KoreAML.freeOf]; exact hk,
     fun hk => by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk⟩
  have hkeys : ∀ {ps : List Kore.Pattern},
      Term.kore c vs r.lhs ∈ ps → reqPat C (r.req.map (Term.kore c vs)) ∈ ps → .ceil C C (ruleRight c r) ∈ ps →
      (∀ i < n, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps)) ∧
      (∀ i < n, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) := by
    intro ps h1 h2 h3
    have hpart : ∀ i < n, (i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) ∧
        canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps) := by
      intro i hi
      by_cases hx : i ∈ r.exs
      · exact ⟨fun h' => absurd hx h', Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inl hx)))⟩
      rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h1 (Model.kore_freeOf c vs r.lhs hL),
          Model.varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)⟩
      · rw [ht] at h2
        obtain ⟨hf, hv⟩ := hreqK (Model.kore_freeOf c vs t hit) (varsOf_kore c vs t hit)
        exact ⟨fun _ => Model.freeOf_and_memOpen h2 hf, Model.varsOf_and_mem h2 hv⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inl hR))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inl hR))))⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr ⟨t, ht, hit⟩))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr ⟨t, ht, hit⟩))))⟩
    exact ⟨fun i hi => (hpart i hi).2, fun i hi hx => (hpart i hi).1 hx⟩
  by_cases hce : comps.isEmpty
  · have hnone : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio := fun r' hr' hlt => by
      have := hcomp r' hr' hlt
      rw [List.isEmpty_iff.mp hce] at this
      exact absurd this List.not_mem_nil
    obtain ⟨hk1, hk2⟩ := hkeys (ps := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .ceil C C (ruleRight c r)]) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    refine ⟨_, by rw [Model.prioRuleK_preTop hpre₀]; dsimp only; rw [if_pos hce], hk1, hk2,
      fun r' hr' hlt => absurd hlt (hnone r' hr'), fun tbl e a h => ?_⟩
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
    exact ⟨h.1, h.2.1, fun r' hr' hlt => absurd hlt (hnone r' hr')⟩
  · obtain ⟨hk1, hk2⟩ := hkeys (ps := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .not C (anyOfC C comps), .ceil C C (ruleRight c r)]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    refine ⟨_, by rw [Model.prioRuleK_preTop hpre₀]; dsimp only; rw [if_neg hce], hk1, hk2,
      fun r' hr' hlt i hi hil => ?_, fun tbl e a h => ?_⟩
    · refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr' hlt)
        (Model.varsOf_appliesOpen (Semantics.rulePlainEx_top (hrules r' hr').2).1 hi hil))
    · rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      rw [KoreAML.tr, KoreAML.interp_sNot] at h3
      exact ⟨h1, h2, fun r' hr' hlt happ => h3.1 (anyOfC_of_mem h3.2 (hcomp r' hr' hlt) happ)⟩

end

/-! ## The successor a disjunct of the step's closure gives -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The successor a rule's axiom gives, in two cases, for a rule that may have existential
variables.** For a rule r with `ruleSorted` and `rulePlainEx` (not asked to be one of the
definition's) in a definition whose rules have both, in a model of `Γc`, at a valuation of r's
variables other than the existential ones in their sorts where x's element is in r's left side, in
`⌈req = true⌉` and in no competitor's `applies`, and b is in r's right side `∃ē. (rhs ∧ ens)`, where
the step at x is decided (`StepDecided`, and its conjuncts for r): there is an unblocked match σ of r
at x, and
- where r's left side binds every variable, b is the element of a configuration y with every premise
  of `StepBy c r σ x y` but the rule's membership;
- otherwise b is in `famOpen c r σ`. -/
theorem successor_split_ex (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
    (hdr : (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val) →
      (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
        (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
      (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x.val →
        (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
          (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
          ∃ b, Holds c r.vars.length σ r.post b))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkeysC : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
      canonKey c r'.vars i ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio →
      ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e (elemOf c I x.val))
    {b : M} (hy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e b) :
    (r.opens = [] ∧ ∃ (y : Config c) (σ : Subst), (r ∈ c.rules → StepBy c r σ x y) ∧ b = elemOf c I y.val) ∨
    (r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ ∀ e', (famOpen c r σ).interpret I e' b) := by
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
  have hinR : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (eR.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (by rw [canonVars_getD c hi]; rfl)
    · show InS I _ (eR.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoffE i hi hx]; exact hin i hi hx
  have hlR : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I eR (elemOf c I x.val) :=
    (tr_kore_congr r.lhs (fun i hi => (hoffE i (hnxL i hi).1 (hnxL i hi).2).symm) _).mp hl
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c vs)))).interpret I eR (elemOf c I x.val) :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl eR)
  let σ := substOf c I tbl vs r.vars eR
  -- the left side binds the variables it holds at values
  obtain ⟨hmatch, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hinR
    (collPat_of_sorted hph' hlhs) hlhs x.property hlR
  -- no rule of a smaller priority applies at values: it would apply in the model
  have hnoapp : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val :=
    fun r' hr' hlt' ⟨σ', hσ', hpv', hreq', _⟩ => hcomp r' hr' hlt'
      (applies_of_values (r := ruleDropExs r') h hI hcw (ruleSorted_dropExs (hrules r' hr').1)
        (rulePlainOpen_dropExs (hrules r' hr').2) hσ' hpv' hreq' (hkeysC r' hr' hlt') e)
  -- so none applies, at values, where its `requires` has a result at each match
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    intro r' hr' hlt'
    have hun : ∀ r'' ∈ c.rules, r''.prio < r'.prio → ¬ RuleApplies c r'' x.val :=
      fun r'' hr'' hlt'' => hnoapp r'' hr'' (Nat.lt_trans hlt'' hlt')
    exact notApplies_ofDropExs (notApplies_of_not_applies (r := ruleDropExs r') h hI hcw
      (ruleSorted_dropExs (hrules r' hr').1) (rulePlainOpen_dropExs (hrules r' hr').2) (hd r' hr' hun).1
      (hkeysC r' hr' hlt') e (hcomp r' hr' hlt'))
  by_cases hop : r.opens = []
  · -- every variable is held by the left side: the step of `StepDecided`
    left
    refine ⟨hop, ?_⟩
    have hbinds := Rule.lhs_of_opens_nilSplit hop
    obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwitL i (hbinds i hi))
    have hdr' := hdr hnoapp
    obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
    have hSC : ∀ a, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I eR a ↔ a = σC := fun a => by
      unfold srtOf; rw [trSort_srt]; exact hσC1 a
    -- a condition the element satisfies evaluates to `true`, where it has a result
    have htrue : ∀ (q : Option Term) (m : M), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
        (∀ t, q = some t → ∃ v, EvalTerm c σ t v) →
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I eR m →
        ∀ t, q = some t → EvalTerm c σ t (some (bool true)) := by
      intro q m hqs hqv hqm t ht
      obtain ⟨v, hv⟩ := hqv t ht
      by_cases hvt : v = some (bool true)
      · rw [hvt] at hv; exact hv
      · exfalso
        rw [ht] at hqm
        exact reqFalse_empty hIΓ hSC hσC2 hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hqs t ht) hu)
          (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
            hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag (hqs t ht)) _ hqm
    have hreqT := htrue r.req _ hreqs (hdr'.1 σ (hσ.at _) hmatch).1 hreqR
    have hrest := hdr'.2 σ hσ hmatch hreqT (hpre₀ ▸ .top)
    have hensT := htrue r.ens _ hensS hrest.2.1 hensR
    obtain ⟨v, hv⟩ := hrest.1
    have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
      hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp hyR
    cases v with
    | none => exact hbR.elim
    | some yv =>
      have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhss rfl
      refine ⟨⟨yv, hyv⟩, σ, fun hmem => ⟨hmem, hσ, hmatch, hreqT, hpre₀ ▸ .top, hv, hensT, hpost₀ ▸ .top, hprio⟩, ?_⟩
      exact ((elemOf_spec hIΓ hyv eR).1 b).mp (((den_closed c yv).interp eR eR b).mp hbR)
  -- an open variable: the valuation, moved to `famOpen`'s variables, satisfies its body at b
  right
  refine ⟨hop, σ, ⟨fun i hi s hsi => ?_, hmatch, hprio⟩, fun e' => ?_⟩
  · have hlti : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
    obtain ⟨h1, -⟩ := pick_spec (hwitL i hi)
    refine ⟨_, substOf_lookup hlti, ?_⟩
    rw [h1, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
  rw [famOpen_eqEx hpre₀ hpost₀ hlt]
  unfold KoreAML.denB
  have hkf := famOpen_keysEx (c := c) (r := r) (σ := σ)
  generalize KoreAML.tableOf [] (famOpenPatEx c r σ) = tf at hkf ⊢
  unfold famOpenPatEx
  let outer := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have houter : ∀ i, i ∈ outer ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by simp [outer]
  have hol : ∀ i ∈ outer, i < r.vars.length := fun i hi => ((houter i).mp hi).1
  have hsortB : ∀ i < r.vars.length,
      ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    rw [canonVars_getD c hi]; rfl
  let e₁ := copyVEx c tbl tf r.vars outer eR e'
  let e₂ := copyVSplit c tbl tf r.vars eR e₁
  have hat₁ : ∀ i < r.vars.length, i ∉ r.exs →
      e₁.evalEvar (tf.ev (keyAt vs i)) = eR.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hx => copyVEx_at hkf hi ((houter i).mpr ⟨hi, hx⟩)
  have hat₂ : ∀ i < r.vars.length, e₂.evalEvar (tf.ev (keyAt vs i)) = eR.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi => copyVSplit_at hkf hi
  have hinC : (KoreAML.inhOf (KoreAML.trSort tf (srtOf c topCellSort))).interpret I e₁ b :=
    reqPat_inhSplit hIΓ hensR tf e₁
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  refine existsAll_intro_at hD _ e' e₁ b (binders_nodupEx hkf hol (List.nodup_range.filter _)) (binders_sortEx hol)
    (fun z hz => copyVEx_off fun i hi his he => hz _ (List.mem_map_of_mem his) he) rfl
    (fun b' hb' n hn => ?_) ?_
  · obtain ⟨i, hio, rfl⟩ := List.mem_map.mp hb'
    have hi := hol i hio
    rw [hsortB i hi] at hn
    rw [← srt_inj hn]
    show InS I _ (e₁.evalEvar (tf.ev (canonKey c r.vars i)))
    rw [copyVEx_at hkf hi hio]
    exact hinR i hi
  rw [interp_and (hne _ _)]
  intro p hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  · -- the left side's variables, fixed to their values under σ
    unfold fixK at hp'
    obtain ⟨i, hiL, hpi⟩ := List.mem_filterMap.mp hp'
    split at hpi
    · rename_i v s g hv hsi hg'
      cases hpi
      have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
      obtain ⟨hgs, hge⟩ := pick_spec (hwitL i hiL)
      rw [substOf_lookup hi] at hg'
      cases hg'
      have hgs' : c.sortOf (pick c I (r.vars.getD i 0) (eR.evalEvar (tbl.ev (keyAt vs i)))) = some s := by
        rw [hgs, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
      refine (fixEq_iff hIΓ (sortOf_numbered_of hs0 (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hgs') hgs'
        b).mpr ⟨hinC, ?_⟩
      have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
        unfold canonKey
        rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
      rw [hvk]
      exact (hat₁ i hi (hnxL i hiL).2).trans hge.symm
    · cases hpi
  · -- the `requires`, from x's element
    rw [List.mem_singleton.mp hp']
    exact reqPat_transferSplit hIΓ (fun t ht i hi => (hat₁ i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqR hinC
  · -- inside `∃ē`, the existential variables at their elements under the binders
    rw [List.mem_singleton.mp hp']
    refine existsAll_intro_at hD _ e₁ e₂ b (binders_nodupEx hkf hlt hexnd) (binders_sortEx hlt) (fun z hz => ?_) rfl
      (fun b' hb' n hn => ?_) ?_
    · by_cases hk : ∃ i < r.vars.length, z = tf.ev (canonKey c r.vars i)
      · obtain ⟨i, hi, rfl⟩ := hk
        have hx : i ∉ r.exs := fun hx => hz _ (List.mem_map_of_mem hx) rfl
        exact (hat₂ i hi).trans (hat₁ i hi hx).symm
      · exact copyVSplit_off fun i hi he => hk ⟨i, hi, he⟩
    · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb'
      have hi := hlt i hix
      rw [hsortB i hi] at hn
      rw [← srt_inj hn]
      show InS I _ (e₂.evalEvar (tf.ev (keyAt vs i)))
      rw [hat₂ i hi]
      exact hinR i hi
    · unfold Model.ruleRightBody
      rw [tr_and2, KoreAML.interp_sAnd]
      exact ⟨(tr_kore_congr r.rhs (fun i hi => (hat₂ i (varOccs_lt r.rhs hrhss i hi)).symm) b).mp hyR,
        reqPat_transferSplit hIΓ (fun t ht i hi => (hat₂ i (varOccs_lt t (hensS t ht) i hi)).symm) hensR
          (reqPat_inhSplit hIΓ hensR tf e₂)⟩

open Classical in
/-- **A successor of a configuration, at the axiom of a rule that may have existential variables**:
with the step's closure, in every model of `Γc c`, for a definition whose rules have `ruleSorted` and
`rulePlainEx`, a successor b of x's element that lies in a pattern ψ is given by the axiom of a rule r
of the definition at a valuation of r's variables other than the existential ones in their sorts,
under a table holding r's variables and the variables of the left sides of r's competitors: x's
element is in r's left side, in `⌈req = true⌉` and in no competitor's `applies`, and b is in r's
right side `∃ē. (rhs ∧ ens)`. -/
theorem step_successor_axiomEx
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x : Config c) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧ ∃ r ∈ c.rules, ∃ (tbl : VarTable) (e2 : Valuation M),
      (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
        canonKey c r'.vars i ∈ tbl) ∧
      (∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
        (e2.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)))) ∧
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e2 (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
        (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e2 (elemOf c I x.val) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio →
        ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e2 (elemOf c I x.val)) ∧
      (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e2 b := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hD := defOK hIΓ
  have hnext := hs
  unfold KoreAML.sNext at hnext
  rw [KoreAML.interp_app] at hnext
  obtain ⟨n0, b, hn0, hb, happ⟩ := hnext
  refine ⟨b, hb, ?_⟩
  -- the closure axiom, at `y := b`
  have hcl := hI _ (Or.inr rfl) e (elemOf c I x.val)
  rw [Model.stepClosure_pat] at hcl
  dsimp only at hcl
  generalize hy : (⟨Model.tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y at hcl
  let e1 : Valuation M := ⟨Function.update e.evalEvar y b, e.evalSvar⟩
  have hψ : (KoreAML.sNext (.evar y) ⊆⊆
      KoreAML.disjList ((c.rules.map (prioRuleK c)).foldl (Model.stepF y) ([], [], 0)).2.1).interpret I e1
        (elemOf c I x.val) := by
    unfold Pattern.universal at hcl
    rw [interpret_neg, interpret_exists] at hcl
    exact Classical.byContradiction fun hc => hcl ⟨b, by rw [interpret_neg]; exact hc⟩
  rw [KoreAML.interp_included hD] at hψ
  have hdisj := hψ (elemOf c I x.val) (by
    unfold KoreAML.sNext
    rw [KoreAML.interp_app]
    exact ⟨n0, b, hn0, by show b = Function.update e.evalEvar y b y; simp, happ⟩)
  obtain ⟨φ, hφ, hφm⟩ := disjList_mem hdisj
  rcases stepF_cases y _ _ φ hφ with hφ | ⟨p, hp, off, hoff, rfl⟩
  · exact absurd hφ List.not_mem_nil
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hsr, hpr⟩ := hrules r hr
  obtain ⟨L, hPL, hLv, hLf, hLcomp, hLread⟩ := rule_partsEx (I := I) hrules hsr hpr
  let C := srtOf c topCellSort
  let R : Kore.Pattern := ruleRight c r
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i :=
    fun k hk => Model.freeOf_prio_T hrules hsr hpr (by rw [hPL]; exact hk)
  rw [hPL] at hφm hoff
  rw [closureDisjunct_rewrites] at hφm
  -- the table of the disjunct
  let tbl : VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites C L R)
  have hin_tbl : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ (by
      simp only [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ hk))))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hin_tbl _ (hLv i hi)
  have hy_ne : ∀ k ∈ tbl, y ≠ tbl.ev k := by
    intro k hk he
    have h1 := Model.index_le hk
    have hoff' : off + (KoreAML.tableOf [] (.rewrites C L R)).length ≤ Model.tablesLen (c.rules.map (prioRuleK c)) 0 :=
      hoff
    rw [← he, ← hy] at h1
    have h2 : tbl.length = off + (KoreAML.tableOf [] (.rewrites C L R)).length := by simp [tbl]
    simp only at h1
    omega
  -- the binders of the disjunct are the rule's variables other than the existential ones
  let free := Model.evarsOf (KoreAML.freeOf [] (.rewrites C L R)).eraseDups
  have hfree : ∀ ks ∈ free, ∃ i < r.vars.length, ks.1 = canonKey c r.vars i ∧
      ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, n, hn⟩ := Model.mem_filterMap_evar hks
    obtain ⟨i, hi, -, he⟩ := hfreeP _ (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, he, ?_⟩
    rw [he, canonKey_eq c hi] at hn
    injection hn with _ h2
    exact h2.symm
  obtain ⟨e2, he2, hguard, hbody⟩ := sExists_foldr_elim hD free e1 _
    (fun ks hks ks' hks' heq => by
      obtain ⟨i, hi, h1, h2⟩ := hfree ks hks
      obtain ⟨j, hj, h1', h2'⟩ := hfree ks' hks'
      have hij := canonKey_inj hi hj (by rw [← h1, ← h1']; exact ev_inj (h1 ▸ hkeys i hi) (h1' ▸ hkeys j hj) heq)
      subst hij
      rw [h2, h2'])
    (fun ks hks => by obtain ⟨i, -, -, h2⟩ := hfree ks hks; exact ⟨_, h2⟩) hφm
  have he2y : e2.evalEvar y = b := by
    rw [he2 y (fun ks hks => by
      obtain ⟨i, hi, h1, -⟩ := hfree ks hks
      rw [h1]; exact hy_ne _ (hkeys i hi))]
    show Function.update e.evalEvar y b y = b
    simp
  rw [interpret_conj] at hbody
  obtain ⟨hL, hRm⟩ := hbody
  rw [KoreAML.interp_member hD, he2y] at hRm
  change (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e2 b at hRm
  obtain ⟨hl, hreq, hcomp⟩ := hLread tbl e2 _ hL
  -- the valuation gives each of the rule's variables but the existential ones an element of its sort
  have hin : ∀ i < r.vars.length, i ∉ r.exs →
      InS I (c.sortName (r.vars.getD i 0)) (e2.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := by
    intro i hi hx
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] (.rewrites C L R) := by
      rw [KoreAML.freeOf]; exact List.mem_append_left _ (hLf i hi hx)
    have hks := Model.evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    have := hguard _ hks _ rfl
    show InS I _ (e2.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [canonKey_eq c hi]
    exact this
  exact ⟨r, hr, tbl, e2, hkeys, fun r' hr' hlt i hi hil => hin_tbl _ (hLcomp r' hr' hlt i hi hil), hin, hl, hreq,
    hcomp, hRm⟩

/-- **A successor of a configuration, in two cases, for rules that may have existential
variables**: with the step's closure, in every model of `Γc c`, for a definition whose rules have
`ruleSorted` and `rulePlainEx`, where the evaluations the step at x reads have results
(`StepDecided`), a successor of x's element that lies in a pattern ψ is the element of a
configuration y with `StepBy c r σ x y` for a rule r whose left side binds every variable, or lies in
`famOpen c r σ` for a rule r of the definition with an open variable and an unblocked match σ of r
at x. -/
theorem step_successor_ex (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧
      ((∃ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] ∧ StepBy c r σ x y ∧ b = elemOf c I y.val) ∨
       (∃ r ∈ c.rules, r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ (famOpen c r σ).interpret I e b)) := by
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkeysC, hin, hl, hreq, hcomp, hy⟩ :=
    step_successor_axiomEx hrules x hI e ψ hs
  refine ⟨b, hb, ?_⟩
  obtain ⟨hsr, hpr⟩ := hrules r hr
  rcases successor_split_ex h hrules x hd (fun φ hφ => hI φ (Or.inl hφ)) hcw hsr hpr (hd r hr) hkeys hkeysC hin hl
      hreq hcomp hy with
    ⟨hop, y', σ, hst, hbe⟩ | ⟨hop, σ, hu, hfam⟩
  · exact Or.inl ⟨y', r, σ, hop, hst hr, hbe⟩
  · exact Or.inr ⟨r, hr, hop, σ, hu, hfam e⟩

end

end Faithful

open ML Faithful

/-- **Completeness at a configuration, for a definition whose rules may have existential
variables**: `complete_at`'s conclusion, for a semantics that `coreOK` accepts whose rules have
`ruleSorted` and `rulePlainEx`, where the evaluations the step at x reads have results
(`StepDecided`): with the step's closure, every successor of x is in an outcome of `os`, any list
holding the successors by the rules whose left side binds every variable and, for each unblocked
match of another rule, a family at a substitution that agrees with it on the left side's variables.
A rule with an existential variable has an open one (the existential variables are not the left
side's), so its successors stand under `famOpen`. -/
theorem complete_at_ex (c : Semantics) (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x : Config c) (hd : StepDecided c x.val) (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) := by
  intro M _ I hI e m
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  rw [interpret_impl]
  intro hmx
  have hmx' : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp hmx
  subst hmx'
  unfold KoreAML.allNext
  rw [interpret_neg]
  intro hnext
  obtain ⟨b, hb, hcase⟩ := step_successor_ex h hrules x hd hI hcw e _ hnext
  rw [interpret_neg] at hb
  rcases hcase with ⟨y, r, σ, hop, hs, rfl⟩ | ⟨r, hr, hop, σ, hu, hfo⟩
  · exact hb (disjList_of_mem (List.mem_map_of_mem (hval y r σ hop hs))
      (((elemOf_spec hIΓ y.property e).1 _).mpr rfl))
  · obtain ⟨σ', hag, hmem⟩ := hfam r hr hop σ hu
    refine hb (disjList_of_mem (List.mem_map_of_mem hmem) ?_)
    show (famOpen c r σ').interpret I e b
    rw [famOpen_congrOpen c r hag]
    exact hfo

/-- Every configuration is `StepDecided` where every function has a result at arguments of its
sorts and every rule is well sorted with `rulePlainEx`. -/
theorem stepDecided_of_rules_ex {c : Semantics} (h : HypSoundCore c) (hft : FnTerminates c)
    (hr : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) (x : GroundTerm) :
    StepDecided c x :=
  stepDecided_pp h hft (fun r hmem => (hr r hmem).1) x

end KCore
