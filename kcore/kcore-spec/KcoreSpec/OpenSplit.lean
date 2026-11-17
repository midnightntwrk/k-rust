/-
  KCore. A successor of a configuration, in a model of `Γc` with the step's closure, for a
  definition whose rules' left sides need not bind every variable.

  The step's closure gives the successor b of x a disjunct, the axiom of a rule r of the definition
  at a valuation of r's variables in their sorts: x's element is in the left side, in
  `⌈req = true⌉` and in no competitor's `applies`; b is in the right side and in `⌈ens = true⌉`.
  The left side binds the variables it holds at values (`patVal_backC`), and the competitors that
  do not apply in the model do not apply at values (`applies_of_values`,
  `notApplies_of_not_applies`, under `StepDecided`), so the valuation's substitution is an
  unblocked match of r at x. Then (`successor_split_rule`):
  - where r's left side binds every variable (`r.opens = []`), the valuation gives every variable a
    value, and b is the element of the value r's right side evaluates to: a step of `Step`;
  - otherwise b is in `famOpen c r σ` at that match σ: the valuation itself, moved to `famOpen`'s
    variables, satisfies its body at b (`famOpen_of_split`).
  `step_successor_axiomOpen` gives, for a successor in any pattern ψ, the rule and the valuation of
  its axiom; `step_successor_open` is the two cases for it. Of the rules they read
  `ruleSorted` and `rulePlainOpen`, given as a hypothesis; of the configuration, `StepDecided`.
-/
import KcoreSpec.OpenConsistent
import KcoreSpec.FaithfulFamilies
import KcoreSpec.OpenRuleStepCl

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## `⌈t = true⌉` at another element of the configuration sort -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- An element in `⌈q⌉` (`reqPat`) is in the configuration sort, under any table and valuation. -/
theorem reqPat_inhSplit (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {e : Valuation M} {q : Option Kore.Pattern}
    {m : M} (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) q)).interpret I e m)
    (tbl' : VarTable) (e' : Valuation M) :
    (KoreAML.inhOf (KoreAML.trSort tbl' (srtOf c topCellSort))).interpret I e' m := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hSC : ∀ (tb : VarTable) (ev : Valuation M) b, (KoreAML.trSort tb (srtOf c topCellSort)).interpret I ev b ↔
      b = σC := fun tb ev b => by unfold srtOf; rw [trSort_srt]; exact hσC1 b
  have hinh : Inh I σC m := by
    cases q with
    | none =>
      simp only [reqPat] at hm
      rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl),
        KoreAML.interp_inhOf_of (hSC tbl e)] at hm
      exact hm
    | some t =>
      simp only [reqPat] at hm
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) (hSC tbl e) hσB2 hσC2] at hm
      exact hm.1
  exact (KoreAML.interp_inhOf_of (hSC tbl' e')).mpr hinh

/-- **`⌈t = true⌉` moves to another element of the configuration sort, and to another table and
valuation that give the term's variables the same elements.** -/
theorem reqPat_transferSplit (hI : I ⊧ᴵP Γ c) [OvlOK c] {vs : List KoreAML.Var} {tbl tbl' : VarTable}
    {e e' : Valuation M} {q : Option Term}
    (h : ∀ t, q = some t → ∀ i ∈ varOccs t, e.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl'.ev (keyAt vs i)))
    {m m' : M} (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I e m)
    (hm' : (KoreAML.inhOf (KoreAML.trSort tbl' (srtOf c topCellSort))).interpret I e' m') :
    (KoreAML.tr ⟨tbl', []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I e' m' := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hSC : ∀ (tb : VarTable) (ev : Valuation M) b, (KoreAML.trSort tb (srtOf c topCellSort)).interpret I ev b ↔
      b = σC := fun tb ev b => by unfold srtOf; rw [trSort_srt]; exact hσC1 b
  cases hq : q with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl)]
    exact hm'
  | some t =>
    rw [hq] at hm
    have hm2 := (tr_reqPat_congr hI (h t hq) m).mp hm
    simp only [Option.map_some, reqPat] at hm2 ⊢
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) (hSC tbl' e') hσB2 hσC2] at hm2 ⊢
    exact ⟨(KoreAML.interp_inhOf_of (hSC tbl' e')).mp hm', hm2.2⟩

end


/-! ## A valuation moved to another table -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

open Classical in
/-- The valuation that gives the canonical variables of `vars`, through `tbl'`, the elements `src`
gives them through `tbl`, and agrees with `base` elsewhere. -/
noncomputable def copyVSplit (c : Semantics) (tbl tbl' : VarTable) (vars : List Srt) (src base : Valuation M) :
    Valuation M :=
  ⟨fun x => if h : ∃ i < vars.length, x = tbl'.ev (canonKey c vars i)
    then src.evalEvar (tbl.ev (canonKey c vars (Classical.choose h))) else base.evalEvar x, base.evalSvar⟩

theorem copyVSplit_at {tbl tbl' : VarTable} {vars : List Srt} {src base : Valuation M}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl') {i : Nat} (hi : i < vars.length) :
    (copyVSplit c tbl tbl' vars src base).evalEvar (tbl'.ev (canonKey c vars i)) =
      src.evalEvar (tbl.ev (canonKey c vars i)) := by
  have hex : ∃ j < vars.length, tbl'.ev (canonKey c vars i) = tbl'.ev (canonKey c vars j) := ⟨i, hi, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, hje⟩ := Classical.choose_spec hex
  rw [(canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys _ hj) hje)).symm]

theorem copyVSplit_off {tbl tbl' : VarTable} {vars : List Srt} {src base : Valuation M} {x : EVar}
    (hx : ∀ i < vars.length, x ≠ tbl'.ev (canonKey c vars i)) :
    (copyVSplit c tbl tbl' vars src base).evalEvar x = base.evalEvar x := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (fun ⟨i, hi, he⟩ => hx i hi he)]

end


/-! ## The pattern `famOpen` reads, for a rule with `rulePlainOpen` -/

section
variable {c : Semantics}

/-- The pattern `famOpen` reads, for a rule with `rulePlainOpen` (not asked to be one of the
definition's): every variable is bound, those of the left side fixed to their values under σ. -/
theorem famOpen_eqSplit {r : Rule} (hp : c.rulePlainOpen r = true) (σ : Subst) :
    famOpen c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (varOccs r.lhs) ++
        [reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
        [.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]]))) := by
  obtain ⟨hex, hpre, hpost⟩ := Semantics.rulePlainOpen_top hp
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famOpen, ruleRight, hex, hpre, hpost, List.contains_nil, Bool.not_false, Cond.conj, Cond.isTop,
    ite_true, List.filterMap_nil, List.foldr_nil, List.append_nil]
  rw [hf, hv]

/-- A rule whose left side binds no fewer than all its variables. -/
theorem Rule.lhs_of_opens_nilSplit {r : Rule} (h : r.opens = []) : ∀ i < r.vars.length, i ∈ varOccs r.lhs := by
  intro i hi
  refine Classical.byContradiction fun hn => ?_
  have : i ∈ r.opens := by
    simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hn⟩
  rw [h] at this; cases this

end


/-! ## The axiom of a rule with `rulePlainOpen`, in any model -/

section
variable {c : Semantics}

/-- The free variables of the axiom of a rule with `ruleSorted` and `rulePlainOpen`, in a
definition whose rules have both, are its own. -/
theorem freeOf_prioSplit (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] (prioRuleK c r)) : ∃ i < r.vars.length, k = canonKey c r.vars i := by
  obtain ⟨hlhs, -, hreqs, hens, hrhss⟩ := Model.ruleSorted_partsOpen hs hp
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.rulePlainOpen_top hp
  have hparts : ∀ {k : KoreAML.VarKey},
      (k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.lhs) ∨
        k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))) ∨
        k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.rhs) ∨
        k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars))))) →
      ∃ i < r.vars.length, k = canonKey c r.vars i := by
    intro k hk
    have hq : ∀ (q : Option Term), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
        k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (q.map (Term.kore c (canonVars c r.vars)))) →
        ∃ i < r.vars.length, k = canonKey c r.vars i := by
      intro q hqs hk
      cases hq : q with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
          exact ⟨i, varOccs_lt t (hqs t hq) i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
    rcases hk with hk | hk | hk | hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.lhs hk
      exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
    · exact hq r.req hreqs hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.rhs hk
      exact ⟨i, varOccs_lt r.rhs hrhss i hi, rfl⟩
    · exact hq r.ens hens hk
  rw [prioRuleK_top hex₀ hpre₀ hpost₀] at hk
  dsimp only at hk
  split at hk
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk | hk) | hk
    · exact hparts (Or.inl hk)
    · exact hparts (Or.inr (Or.inl hk))
    · exact hparts (Or.inr (Or.inr hk))
    · exact hparts (Or.inr (Or.inr hk))
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk | hk | hk) | hk
    · exact hparts (Or.inl hk)
    · exact hparts (Or.inr (Or.inl hk))
    · exfalso
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hs', hp'⟩ := hrules r' (List.mem_filter.mp hr').1
      obtain ⟨hlhs', -, hreqs', -, -⟩ := Model.ruleSorted_partsOpen hs' hp'
      exact Model.freeOf_appliesOpen hlhs' (fun t ht i hi => varOccs_lt t (hreqs' t ht) i hi)
        (Semantics.rulePlainOpen_top hp').2.1 hk
    · exact hparts (Or.inr (Or.inr hk))
    · exact hparts (Or.inr (Or.inr hk))

/-- **A rule's axiom `\rewrites(L, R)`, its left part `L` read**, for a rule with `ruleSorted` and
`rulePlainOpen` in a definition whose rules have both: the rule's variables occur free in `L`, the
canonical variables of the left sides and conditions of its competitors are among `L`'s, and an
element of `L` is in the left side and in `⌈req = true⌉`, and in no competitor's `applies`. -/
theorem rule_partsSplit {M : Type} {I : Interpretation KoreAML.Sym M}
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L
        (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.freeOf [] L ∧ canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
        canonKey c r'.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.tr ⟨tbl, []⟩ L).interpret I e a →
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e a ∧
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret
          I e a ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio →
          ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e a := by
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.rulePlainOpen_top hp
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  by_cases hce : comps.isEmpty
  · have hnone : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio := fun r' hr' hlt => by
      have := hcomp r' hr' hlt
      rw [List.isEmpty_iff.mp hce] at this
      exact absurd this List.not_mem_nil
    refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce],
      Model.rule_keys_open hs hp (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      fun r' hr' hlt => absurd hlt (hnone r' hr'), fun tbl e a h => ?_⟩
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
    exact ⟨h.1, h.2.1, fun r' hr' hlt => absurd hlt (hnone r' hr')⟩
  · refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .not C (anyOfC C comps),
        .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce],
      Model.rule_keys_open hs hp (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
      fun r' hr' hlt i hi hil => ?_, fun tbl e a h => ?_⟩
    · refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr' hlt)
        (Model.varsOf_appliesOpen (Semantics.rulePlainOpen_top (hrules r' hr').2).2.1 hi hil))
    · rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      rw [KoreAML.tr, KoreAML.interp_sNot] at h3
      exact ⟨h1, h2, fun r' hr' hlt happ => h3.1 (anyOfC_of_mem h3.2 (hcomp r' hr' hlt) happ)⟩

end


/-! ## The successor a disjunct of the step's closure gives -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The successor a rule's axiom gives, in two cases.** For a rule r with `ruleSorted` and
`rulePlainOpen` (not asked to be one of the definition's) in a definition whose rules have both,
in a model of `Γc`, at a valuation of r's variables in their sorts where x's element is in r's left
side, in `⌈req = true⌉` and in no competitor's `applies`, and b is in r's right side and
`⌈ens = true⌉`, where the step at x is decided (`StepDecided`, and its conjuncts for r): the
valuation's substitution σ is an unblocked match of r at x, and
- where r's left side binds every variable, b is the element of a configuration y with every premise
  of `StepBy c r σ x y` but the rule's membership;
- otherwise b is in `famOpen c r σ`. -/
theorem successor_split_rule (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
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
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio →
      ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e (elemOf c I x.val))
    {b : M} (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e b)
    (hensm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.ens.map (Term.kore c (canonVars c r.vars))))).interpret I e b) :
    (r.opens = [] ∧ ∃ (y : Config c) (σ : Subst), (r ∈ c.rules → StepBy c r σ x y) ∧ b = elemOf c I y.val) ∨
    (r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ ∀ e', (famOpen c r σ).interpret I e' b) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  have hneg := (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI))
  obtain ⟨hlhs, -, hensK, hrhss⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, -, hreqs, hensS, -⟩ := Model.ruleSorted_partsOpen hs hp
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.rulePlainOpen_top hp
  let vs := canonVars c r.vars
  let σ := substOf c I tbl vs r.vars e
  -- the left side binds the variables it holds at values
  obtain ⟨hmatch, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) hlhs x.property hl
  -- no rule of a smaller priority applies at values: it would apply in the model
  have hnoapp : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val :=
    fun r' hr' hlt ⟨σ', hσ', hpv', hreq', _⟩ => hcomp r' hr' hlt
      (applies_of_values h hI hcw (hrules r' hr').1 (hrules r' hr').2 hσ' hpv' hreq' (hkeysC r' hr' hlt) e)
  -- so none applies, at values, where its `requires` has a result at each match
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    intro r' hr' hlt
    have hun : ∀ r'' ∈ c.rules, r''.prio < r'.prio → ¬ RuleApplies c r'' x.val :=
      fun r'' hr'' hlt' => hnoapp r'' hr'' (Nat.lt_trans hlt' hlt)
    exact notApplies_of_not_applies h hI hcw (hrules r' hr').1 (hrules r' hr').2 (hd r' hr' hun).1
      (hkeysC r' hr' hlt) e (hcomp r' hr' hlt)
  by_cases hop : r.opens = []
  · -- every variable is held by the left side: the step of `StepDecided`
    left
    refine ⟨hop, ?_⟩
    have hbinds := Rule.lhs_of_opens_nilSplit hop
    obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwitL i (hbinds i hi))
    have hdr' := hdr hnoapp
    obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
    have hSC : ∀ a, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e a ↔ a = σC := fun a => by
      unfold srtOf; rw [trSort_srt]; exact hσC1 a
    -- a condition the element satisfies evaluates to `true`, where it has a result
    have htrue : ∀ (q : Option Term) (m : M), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
        (∀ t, q = some t → ∃ v, EvalTerm c σ t v) →
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I e m →
        ∀ t, q = some t → EvalTerm c σ t (some (bool true)) := by
      intro q m hqs hqv hqm t ht
      obtain ⟨v, hv⟩ := hqv t ht
      by_cases hvt : v = some (bool true)
      · rw [hvt] at hv; exact hv
      · exfalso
        rw [ht] at hqm
        exact reqFalse_empty hIΓ hSC hσC2 hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hqs t ht) hu)
          (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag (hqs t ht)) _ hqm
    have hreqT := htrue r.req _ hreqs (hdr'.1 σ (hσ.at _) hmatch).1 hreqm
    have hrest := hdr'.2 σ hσ hmatch hreqT (hpre₀ ▸ .top)
    have hensT := htrue r.ens _ hensS hrest.2.1 hensm
    obtain ⟨v, hv⟩ := hrest.1
    have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp hy
    cases v with
    | none => exact hbR.elim
    | some yv =>
      have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhss rfl
      refine ⟨⟨yv, hyv⟩, σ, fun hmem => ⟨hmem, hσ, hmatch, hreqT, hpre₀ ▸ .top, hv, hensT, hpost₀ ▸ .top, hprio⟩, ?_⟩
      exact ((elemOf_spec hIΓ hyv e).1 b).mp (((den_closed c yv).interp e e b).mp hbR)
  -- an open variable: the valuation, moved to `famOpen`'s variables, satisfies its body at b
  right
  refine ⟨hop, σ, ⟨fun i hi s hsi => ?_, hmatch, hprio⟩, fun e' => ?_⟩
  · have hlt : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
    obtain ⟨h1, -⟩ := pick_spec (hwitL i hi)
    refine ⟨_, substOf_lookup hlt, ?_⟩
    rw [h1, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
  rw [famOpen_eqSplit hp]
  unfold KoreAML.denB
  generalize htbl : KoreAML.tableOf [] _ = tbl2
  have hkeys2 : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl2 := fun i hi => by
    rw [← htbl]; exact canonKey_mem_existsAll hi
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys2
  let e2 := copyVSplit c tbl tbl2 r.vars e e'
  have hat : ∀ i < r.vars.length, e2.evalEvar (tbl2.ev (keyAt vs i)) = e.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi => copyVSplit_at hkeys2 hi
  have hinC : (KoreAML.inhOf (KoreAML.trSort tbl2 (srtOf c topCellSort))).interpret I e2 b :=
    reqPat_inhSplit hIΓ hensm tbl2 e2
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  refine existsAll_intro_at hD _ e' e2 b hnd hsrt (fun z hz => ?_) rfl (fun b' hb' n hn => ?_) ?_
  · refine copyVSplit_off fun i hi he => hz _ ?_ he
    have hlt : i < (canonVars c r.vars).length := by rw [canonVars_length]; exact hi
    show ((canonVars c r.vars).getD i default).kore ∈ (canonVars c r.vars).map KoreAML.Var.kore
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  · obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb'
    have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c hi]; rfl
    rw [hs'] at hn
    rw [← srt_inj hn]
    show InS I _ (e2.evalEvar (tbl2.ev (canonKey c r.vars i)))
    rw [copyVSplit_at hkeys2 hi]
    exact hin i hi
  · rw [interp_and (hne _ _)]
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
        have hgs' : c.sortOf (pick c I (r.vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i)))) = some s := by
          rw [hgs, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
        refine (fixEq_iff hIΓ (sortOf_numbered_of hs0 (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hgs') hgs'
          b).mpr ⟨hinC, ?_⟩
        have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
          unfold canonKey
          rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
        rw [hvk, copyVSplit_at hkeys2 hi]
        exact hge.symm
      · cases hpi
    · -- the `requires`, from x's element
      rw [List.mem_singleton.mp hp']
      exact reqPat_transferSplit hIΓ (fun t ht i hi => (hat i (varOccs_lt t (hreqs t ht) i hi)).symm) hreqm hinC
    · -- the right side and the `ensures`, at b
      rw [List.mem_singleton.mp hp', tr_and2, KoreAML.interp_sAnd]
      exact ⟨(tr_kore_congr r.rhs (fun i hi => (hat i (varOccs_lt r.rhs hrhss i hi)).symm) b).mp hy,
        reqPat_transferSplit hIΓ (fun t ht i hi => (hat i (varOccs_lt t (hensS t ht) i hi)).symm) hensm hinC⟩

open Classical in
/-- **A successor of a configuration, at the axiom of a rule**: with the step's closure, in every
model of `Γc c`, for a definition whose rules have `ruleSorted` and `rulePlainOpen`, a successor b of
x's element that lies in a pattern ψ is given by the axiom of a rule r of the definition at a
valuation of r's variables in their sorts, under a table holding r's variables and the variables of
the left sides of r's competitors: x's element is in r's left side, in `⌈req = true⌉` and in no
competitor's `applies`, and b is in r's right side and in `⌈ens = true⌉`. -/
theorem step_successor_axiomOpen
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    (x : Config c) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧ ∃ r ∈ c.rules, ∃ (tbl : VarTable) (e2 : Valuation M),
      (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
        canonKey c r'.vars i ∈ tbl) ∧
      (∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
        (e2.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)))) ∧
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e2 (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
        (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e2 (elemOf c I x.val) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio →
        ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e2 (elemOf c I x.val)) ∧
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e2 b ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
        (r.ens.map (Term.kore c (canonVars c r.vars))))).interpret I e2 b := by
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
  obtain ⟨L, hPL, hLkeys, hLcomp, hLread⟩ := rule_partsSplit (I := I) hrules hsr hpr
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, k = canonKey c r.vars i :=
    fun k hk => freeOf_prioSplit hrules hsr hpr (by rw [hPL]; exact hk)
  rw [hPL] at hφm hoff
  rw [closureDisjunct_rewrites] at hφm
  -- the table of the disjunct
  let tbl : VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites C L R)
  have hin_tbl : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ (by
      simp only [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ hk))))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hin_tbl _ (hLkeys i hi).2
  have hy_ne : ∀ k ∈ tbl, y ≠ tbl.ev k := by
    intro k hk he
    have h1 := Model.index_le hk
    have hoff' : off + (KoreAML.tableOf [] (.rewrites C L R)).length ≤ Model.tablesLen (c.rules.map (prioRuleK c)) 0 :=
      hoff
    rw [← he, ← hy] at h1
    have h2 : tbl.length = off + (KoreAML.tableOf [] (.rewrites C L R)).length := by simp [tbl]
    simp only at h1
    omega
  -- the binders of the disjunct are the rule's variables
  let free := Model.evarsOf (KoreAML.freeOf [] (.rewrites C L R)).eraseDups
  have hfree : ∀ ks ∈ free, ∃ i < r.vars.length, ks.1 = canonKey c r.vars i ∧
      ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, n, hn⟩ := Model.mem_filterMap_evar hks
    obtain ⟨i, hi, he⟩ := hfreeP _ (List.mem_eraseDups.mp hk1)
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
  change (KoreAML.tr ⟨tbl, []⟩ (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])).interpret
    I e2 b at hRm
  rw [tr_and2, KoreAML.interp_sAnd] at hRm
  obtain ⟨hl, hreq, hcomp⟩ := hLread tbl e2 _ hL
  -- the valuation gives each of the rule's variables an element of its sort
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] (.rewrites C L R) := by
      rw [KoreAML.freeOf]; exact List.mem_append_left _ (hLkeys i hi).1
    have hks := Model.evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    have := hguard _ hks _ rfl
    show InS I _ (e2.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [canonKey_eq c hi]
    exact this
  exact ⟨r, hr, tbl, e2, hkeys, fun r' hr' hlt i hi hil => hin_tbl _ (hLcomp r' hr' hlt i hi hil), hin, hl, hreq,
    hcomp, hRm.1, hRm.2⟩

/-- **A successor of a configuration, in two cases**: with the step's closure, in every model of
`Γc c`, for a definition whose rules have `ruleSorted` and `rulePlainOpen`, where the evaluations the
step at x reads have results (`StepDecided`), a successor of x's element that lies in a pattern ψ is
the element of a configuration y with `StepBy c r σ x y` for a rule r whose left side binds every
variable, or lies in `famOpen c r σ` for a rule r of the definition with an open variable and an
unblocked match σ of r at x. -/
theorem step_successor_open (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧
      ((∃ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] ∧ StepBy c r σ x y ∧ b = elemOf c I y.val) ∨
       (∃ r ∈ c.rules, r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ (famOpen c r σ).interpret I e b)) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkeysC, hin, hl, hreq, hcomp, hy, hens⟩ :=
    step_successor_axiomOpen hrules x hI e ψ hs
  refine ⟨b, hb, ?_⟩
  obtain ⟨hsr, hpr⟩ := hrules r hr
  rcases successor_split_rule h hrules x hd (fun φ hφ => hI φ (Or.inl hφ)) hcw hsr hpr (hd r hr) hkeys hkeysC hin hl hreq hcomp hy hens with
    ⟨hop, y', σ, hst, hbe⟩ | ⟨hop, σ, hu, hfam⟩
  · exact Or.inl ⟨y', r, σ, hop, hst hr, hbe⟩
  · exact Or.inr ⟨r, hr, hop, σ, hu, hfam e⟩

end

end Faithful

end KCore
