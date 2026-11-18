/-
  KCore. The step's closure and the model for rules with `pre` and `post`: the value model at a
  transition T, its step read by `StepV`.

  - `freeOf_condKore`: a free variable of a well-sorted condition's pattern is a variable of the
    condition in scope, not among the bound keys (the converse of `condKore_keys`).
  - `freeOf_appliesPP`: a well-sorted rule's `applies` pattern has no free variable, for any `pre`.
  - `freeOf_ruleRightPP`, `freeOf_prio_pp`: the free variables of a well-sorted rule's right side
    and axiom are variables of the rule other than its existential ones.
  - `closureDisjunct_pp`, `satStepGoal_pp`: `closureDisjunct_T`, `satStepGoal_T` with `StepVAt` and
    `StepV` for `StepMAt` and `StepM`.
  - `stdI_T_model_pp_fns`: `stdI_T c T` is a model of `Γc` with the step's closure, for rules with
    `rulePlainPP`, the functions' equations a hypothesis.
  - `stepVBy_of_stepBy` (`FnDet`) and `stepBy_of_stepVBy` (`coreOK`, `FnDet`, `FnTerminates`):
    the bridge between `StepBy` and `StepVBy` at configurations.
-/
import KcoreSpec.SatRulePP
import KcoreSpec.ExChoice
import KcoreSpec.SoundDefs
import KcoreSpec.CondTwoTables
import KcoreSpec.CondKoreVars
import KcoreSpec.ModelFnsDecided

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## Free variables -/

/-- A member of a condition's conjuncts is its pattern. -/
theorem mem_condConj {vs : List KoreAML.Var} {S : Kore.KSort} {p : Cond} {φ : Kore.Pattern}
    (h : φ ∈ Cond.conj c vs S p) : φ = Cond.kore c vs S p := by
  unfold Cond.conj at h
  split at h
  · cases h
  · simpa using h

/-- **A well-sorted rule's `applies` pattern has no free variable**, whatever its `pre`: it binds
the variables of its left side and conditions, the only ones it holds. -/
theorem freeOf_appliesPP {r : Rule} (hs : c.ruleSorted r = true)
    {bound : List KoreAML.VarKey} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf bound (applies c r (canonRulePres r))) : False := by
  obtain ⟨hlhs, -, hreqs, -, -, -, -, hokP, -⟩ := ruleSorted_partsPP hs
  rw [applies_eqPP r] at hk
  let vs := canonVars c r.vars
  let l := (List.range r.vars.length).filter r.leftVars.contains
  obtain ⟨bound', hb', hk⟩ := freeOf_existsAll (S := srtOf c topCellSort)
    ((l.map (vs.getD · default)).map KoreAML.Var.kore) hk
  have hbound : ∀ i < r.vars.length, i ∈ r.leftVars → bound'.contains (canonKey c r.vars i) = true := fun i hi hil =>
    (hb' _).mpr (Or.inl (List.mem_map_of_mem (List.mem_map_of_mem (List.mem_map_of_mem
      (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩)))))
  obtain ⟨φ, hφ, hk⟩ := mem_freeOf_and hk
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hφ
  rcases hφ with rfl | rfl | hφ
  · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs r.lhs hk
    have h2 : bound'.contains (canonKey c r.vars i) = true :=
      hbound i (varOccs_lt r.lhs hlhs i hi) (List.mem_append_left _ hi)
    rw [canonKey_eqKore, hb] at h2; cases h2
  · cases hq : r.req with
    | none =>
      rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t hk
        have h2 : bound'.contains (canonKey c r.vars i) = true :=
          hbound i (varOccs_lt t (hreqs t hq) i hi)
            (List.mem_append_right _ (List.mem_append_left _ (by rw [hq]; exact hi)))
        rw [canonKey_eqKore, hb] at h2; cases h2
      · rw [KoreAML.freeOf] at hk; cases hk
  · rw [mem_condConj hφ] at hk
    obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore _ r.pre hokP hk
    have h2 : bound'.contains (canonKey c r.vars i) = true :=
      hbound i (varOccsCond_lt_twoT r.pre hokP i hi) (List.mem_append_right _ (List.mem_append_right _ hi))
    rw [hb] at h2; cases h2

/-- The free variables of a well-sorted rule's right side `∃ē. (rhs ∧ ens ∧ post)` are variables
of the rule other than its existential ones. -/
theorem freeOf_ruleRightPP {r : Rule} (hs : c.ruleSorted r = true)
    {k : KoreAML.VarKey} (hk : k ∈ KoreAML.freeOf [] (ruleRight c r)) :
    ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := by
  obtain ⟨-, -, -, hensS, hrhss, -, hexs, -, hokQ, -⟩ := ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  rw [ruleRight_eqPP hlt, freeOf_existsAll_eqEx, List.append_nil] at hk
  have hB : ∀ i, i ∈ r.exs →
      ((ruleExBinders c r).map KoreAML.evarKey).reverse.contains (canonKey c r.vars i) = true :=
    fun i hx => by
      rw [ruleExBinders_keys]
      exact List.contains_iff_mem.mpr (List.mem_reverse.mpr (List.mem_map_of_mem hx))
  have hterm : ∀ (t : Term), sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t ≠ none →
      k ∈ KoreAML.freeOf ((ruleExBinders c r).map KoreAML.evarKey).reverse (Term.kore c vs t) →
      ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := by
    intro t ht hk
    obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t hk
    obtain ⟨s, hts⟩ := Option.ne_none_iff_exists'.mp ht
    refine ⟨i, varOccs_lt t hts i hi, fun hx => ?_, rfl⟩
    have := hB i hx
    rw [show canonKey c r.vars i = KoreAML.evarKey (vs.getD i default).kore from rfl, hb] at this
    cases this
  unfold ruleRightBodyPP at hk
  obtain ⟨φ, hφ, hk⟩ := mem_freeOf_and hk
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hφ
  rcases hφ with rfl | rfl | hφ
  · exact hterm r.rhs (by rw [hrhss]; exact Option.some_ne_none _) hk
  · cases hq : r.ens with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hterm t (by rw [hensS t hq]; exact Option.some_ne_none _) hk
      · rw [KoreAML.freeOf] at hk; cases hk
  · rw [mem_condConj hφ] at hk
    obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore _ r.post hokQ hk
    refine ⟨i, varOccsCond_lt_twoT r.post hokQ i hi, fun hx => ?_, rfl⟩
    rw [hB i hx] at hb; cases hb

/-- **The free variables of a well-sorted rule's axiom**, among well-sorted rules, are variables of
the rule other than its existential ones; no `pre` or `post` is asked to be `\top`. -/
theorem freeOf_prio_pp (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] (prioRuleK c r)) :
    ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := by
  obtain ⟨hlhs, -, hreqs, -, -, -, hexs, hokP, -⟩ := ruleSorted_partsPP hs
  have hR := fun {k} (h' : k ∈ KoreAML.freeOf [] (ruleRight c r)) => freeOf_ruleRightPP hs h'
  have hL : ∀ {k : KoreAML.VarKey}, k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.lhs) →
      ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := fun hk => by
    obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.lhs hk
    exact ⟨i, varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi, rfl⟩
  have hQ : ∀ {k : KoreAML.VarKey},
      k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))) →
      ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := fun hk => by
    cases hq : r.req with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact ⟨i, varOccs_lt t (hreqs t hq) i hi,
          fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [hq]; exact hi)), rfl⟩
      · rw [KoreAML.freeOf] at hk; cases hk
  have hP : ∀ {φ : Kore.Pattern} {k : KoreAML.VarKey},
      φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre → k ∈ KoreAML.freeOf [] φ →
      ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := fun hφ hk => by
    rw [mem_condConj hφ] at hk
    obtain ⟨-, i, hi, rfl⟩ := freeOf_condKore _ r.pre hokP hk
    exact ⟨i, varOccsCond_lt_twoT r.pre hokP i hi,
      fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi), rfl⟩
  have hD : ∀ {k : KoreAML.VarKey}, k ∈ KoreAML.freeOf [] (.ceil (srtOf c topCellSort) (srtOf c topCellSort)
      (ruleRight c r)) → ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := fun hk => by
    rw [KoreAML.freeOf] at hk; exact hR hk
  unfold prioRuleK at hk
  dsimp only at hk
  split at hk
  · rw [KoreAML.freeOf, List.mem_append] at hk
    rcases hk with hk | hk
    · obtain ⟨φ, hφ, hk⟩ := mem_freeOf_and hk
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.mem_singleton,
        List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl | hφ | rfl
      · exact hL hk
      · exact hQ hk
      · exact hP hφ hk
      · exact hD hk
    · exact hR hk
  · rw [KoreAML.freeOf, List.mem_append] at hk
    rcases hk with hk | hk
    · obtain ⟨φ, hφ, hk⟩ := mem_freeOf_and hk
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.mem_singleton,
        List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl | hφ | rfl | rfl
      · exact hL hk
      · exact hQ hk
      · exact hP hφ hk
      · exfalso
        rw [KoreAML.freeOf] at hk
        obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
        exact freeOf_appliesPP (hrules r' (List.mem_filter.mp hr').1) hk
      · exact hD hk
    · exact hR hk

/-! ## The step's closure -/

/-- **A `StepVAt` step by a rule is in its disjunct of the closure, at any T.** `closureDisjunct_T`
for a rule with `ruleSorted` and `rulePlainPP` (not asked to be one of the definition's), among
rules with those facts: x̄ read as σ off ē. -/
theorem closureDisjunct_pp (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainPP r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainPP r = true) {T : GroundTerm → GroundTerm → Prop}
    {σ : Subst} {x yv : GroundTerm} (hst : StepVAt c r σ x yv) (hx : c.sortOf x = some topCellSort)
    (off : Nat) (y : EVar)
    (hy_ne : ∀ k ∈ List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r),
      y ≠ KoreAML.VarTable.ev (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r)) k)
    (e1 : Valuation Elem) (he1 : e1.evalEvar y = .val yv) :
    (KoreAML.closureDisjunct [] off y (prioRuleK c r)).2.interpret (stdI_T c T) e1 (.val x) := by
  have hn := h.namesK
  obtain ⟨hσ, hmatch, hreq, hpre, heval, hens, hpost, hprio⟩ := hst
  have hnum := rule_vars_numCN h hs
  obtain ⟨L, hPL, hLv, hLf, hLread⟩ := rule_premise_pp h hrules hs hp
  let P := prioRuleK c r
  let tbl : KoreAML.VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] P
  have hin_tbl : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ hk))
  have hinL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => hin_tbl k (by
    show _ ∈ KoreAML.varsOf (prioRuleK c r)
    rw [hPL, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk))
  have hinQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => hin_tbl k (by
      show _ ∈ KoreAML.varsOf (prioRuleK c r)
      rw [hPL, KoreAML.varsOf]
      exact List.mem_append_right _ (varsOf_post_ruleRight hs hk))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hinL _ (hLv i hi)
  let nx := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have hnx : ∀ i, i ∈ nx ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by
    simp only [nx, List.mem_filter, List.mem_range, Bool.not_eq_true']
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun hm => by rw [List.contains_iff_mem.mpr hm] at h2; cases h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, Bool.eq_false_iff.mpr (fun hc => h2 (List.contains_iff_mem.mp hc))⟩⟩
  have hk' : ∀ i < r.vars.length, i ∈ nx → canonKey c r.vars i ∈ tbl := fun i hi _ => hkeys i hi
  let f : Nat → Elem := fun j => .val ((σ.lookup j).getD default)
  let e' := setV c tbl r.vars nx f e1
  have hval : ∀ i < r.vars.length, ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hvar : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
    intro i hi hx m
    rw [AtT.var_read]
    show m = (setV c tbl r.vars nx f e1).evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [setV_on hk' hi ((hnx i).mpr ⟨hi, hx⟩)]
    obtain ⟨w, hw, -⟩ := hval i hi
    simp [f, hw]
  have he'y : e'.evalEvar y = .val yv := by
    show (if h : _ then _ else _) = _
    rw [dif_neg]
    · exact he1
    rintro ⟨i, hi, -, he⟩
    exact hy_ne _ (hkeys i hi) he
  have hLx : (KoreAML.tr ⟨tbl, []⟩ L).interpret (stdI_T c T) e' (.val x) :=
    (hLread T tbl e' σ x hinL hx (fun i hi _ => hval i hi) hvar).mpr
      ⟨hmatch, hreq, hpre, hprio, σ, yv, fun _ _ _ => rfl, hσ, heval, hens, hpost⟩
  have hRy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret (stdI_T c T) e' (.val yv) :=
    (ruleRight_read_pp h hs hp hkeys hinQ (fun i hi _ => hval i hi) hvar _).mpr
      ⟨σ, yv, fun _ _ _ => rfl, hσ, heval, hens, hpost, rfl⟩
  have hdisj : (KoreAML.closureDisjunct [] off y P).2 =
      ((evarsOf (KoreAML.freeOf [] P).eraseDups).foldr
        (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ)
        (KoreAML.tr ⟨tbl, []⟩ L ⋀ (y ∈∈ KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)))) := by
    unfold KoreAML.closureDisjunct
    simp only [tbl]
    simp only [P, hPL]
    rfl
  rw [hdisj]
  have hfree : ∀ ks ∈ evarsOf (KoreAML.freeOf [] P).eraseDups, ∃ i < r.vars.length, i ∉ r.exs ∧
      ks.1 = canonKey c r.vars i ∧ ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, nm, hnm⟩ := mem_filterMap_evar hks
    obtain ⟨i, hi, hx, he⟩ := freeOf_prio_pp (fun r' hr' => (hrules r' hr').1) hs (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, hx, he, ?_⟩
    rw [he, canonKey_eq c hi] at hnm
    injection hnm with _ h2
    exact h2.symm
  refine sExists_foldr_intro_T _ e1 e' _ (fun z hz => ?_) rfl ?_ ?_
  · show (if h : _ then _ else _) = _
    rw [dif_neg]
    rintro ⟨i, hi, hix, rfl⟩
    obtain ⟨-, hx⟩ := (hnx i).mp hix
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] P := by
      show _ ∈ KoreAML.freeOf [] (prioRuleK c r)
      rw [hPL, KoreAML.freeOf]
      exact List.mem_append_left _ (hLf i hi hx)
    have hks := evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    exact hz _ hks (by rw [canonKey_eq c hi])
  · intro ks hks
    obtain ⟨i, hi, hx, h1, h2⟩ := hfree ks hks
    refine ⟨_, h2, ?_⟩
    rw [h1]
    show InS (stdI_T c T) _ ((setV c tbl r.vars nx f e1).evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [setV_on hk' hi ((hnx i).mpr ⟨hi, hx⟩)]
    obtain ⟨v, hv, hsv⟩ := hval i hi
    show InS (stdI_T c T) _ (Elem.val ((σ.lookup i).getD default))
    rw [hv, Option.getD_some]
    exact (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mpr hsv
  · rw [interpret_conj]
    refine ⟨hLx, ?_⟩
    rw [KoreAML.interp_member AtT.defOK_std, he'y]
    exact hRy

/-- **The step's closure holds in the value model at T** where every T step between configurations
is a `StepV` step (`hsub`): `satStepGoal_T` for rules with `ruleSorted` and `rulePlainPP`. -/
theorem satStepGoal_pp (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y) :
    stdI_T c T ⊧ᴵP Γstep c := by
  rintro φ rfl
  rw [stepClosure_pat]
  dsimp only
  intro e m
  generalize hy : (⟨tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y
  have hall : ∀ (x : EVar) (φ : KoreAML.P) (e : Valuation Elem) (m : Elem),
      (∀ a, φ.interpret (stdI_T c T) ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m) →
        (∀∀ x φ).interpret (stdI_T c T) e m := by
    intro x φ e m h'
    unfold Pattern.universal
    rw [interpret_neg, interpret_exists]
    rintro ⟨a, ha⟩
    rw [interpret_neg] at ha
    exact ha (h' a)
  refine hall y _ e m fun a => ?_
  let e1 : Valuation Elem := ⟨Function.update e.evalEvar y a, e.evalSvar⟩
  show (KoreAML.sNext (.evar y) ⊆⊆ _ : KoreAML.P).interpret (stdI_T c T) e1 m
  rw [KoreAML.interp_included AtT.defOK_std]
  intro x0 hx0
  unfold KoreAML.sNext at hx0
  rw [KoreAML.interp_app] at hx0
  obtain ⟨a0, b0, ha0, hb0, hab⟩ := hx0
  have ha0' : a0 = .app .next [] := ha0
  subst ha0'
  have hb0a : b0 = e1.evalEvar y := hb0
  have hst : StepE_T c T x0 b0 := hab
  cases x0 with
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim
  | val x =>
  cases b0 with
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim
  | val yv =>
  obtain ⟨hx, hyv, hT⟩ := hst
  obtain ⟨r, σ, hr, hstep⟩ := hsub x yv hx hyv hT
  obtain ⟨hs, hp⟩ := hrules r hr
  obtain ⟨off, hoff, hmem⟩ := stepF_mem y (c.rules.map (prioRuleK c)) ([], [], 0) (prioRuleK c r)
    (List.mem_map.mpr ⟨r, hr, rfl⟩)
  refine AtT.disjList_intro hmem (closureDisjunct_pp h hrules hs hp hstep hx off y (fun k hk he => ?_) e1 hb0a.symm)
  have h1 := index_le hk
  have hoff' : off + (KoreAML.tableOf [] (prioRuleK c r)).length ≤ tablesLen (c.rules.map (prioRuleK c)) 0 := hoff
  rw [← he, ← hy] at h1
  have h2 : (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r)).length =
      off + (KoreAML.tableOf [] (prioRuleK c r)).length := by simp
  simp only at h1
  omega

end Model

end Faithful

open ML Faithful Faithful.Model

/-! ## The model -/

/-- **The value model at a transition T is a model of `Γc` with the step's closure**, for rules with
`ruleSorted` and `rulePlainPP`: `stdI_T_modelCEx` with `StepV` for `StepM` in `hsub` and `StepVBy` for
`StepMBy` in `hall` and `hsome`, and `stdI_T_modelCEx`'s `hl` (the open generators' laws hold in the
value model), where the value model satisfies the functions' equations (`hFns`). -/
theorem stdI_T_model_pp_fns (c : Semantics) (h : c.coreOK = true) (hm : HypModelCore c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hFns : stdI_T c T ⊧ᴵP ΓFns c)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c) := by
  obtain ⟨hSig, hCons, hDom, hColls, -, hFb, hBool⟩ := model_parts_T hm h hl T hFns
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact hSig φ hφ
    · exact hCons φ hφ
    · exact hDom φ hφ
    · exact hColls φ hφ
    · exact hFns φ hφ
    · exact satRulesGoal_pp hm hrules T hall hsome φ hφ
    · exact hFb φ hφ
  · obtain ⟨-, hl, rfl⟩ := hφ
    exact hBool hl
  · exact satStepGoal_pp hm hrules T hsub φ hφ

/-! ## `StepBy` and `StepVBy` -/

/-- **A `StepBy` step is a `StepVBy` step**, where a term has at most one result (`FnDet`): `pre`
and `post` hold, so are true in the value model (`holds_trueV`), and a competitor that `NotApplies`
excludes has, at each of its matches, a `requires` result other than `true` or a false `pre`. -/
theorem stepVBy_of_stepBy {c : Semantics} (hfd : FnDet c) {r : Rule} {σ : Subst} {x y : Config c}
    (hb : StepBy c r σ x y) : StepVBy c r σ x.val y.val := by
  refine ⟨hb.mem, hb.hσ, hb.hmatch, hb.hreq, (holds_trueV hfd hb.hpre).mpr rfl, hb.heval, hb.hens,
    (holds_trueV hfd hb.hpost).mpr rfl, fun r' hr' hlt hA => ?_⟩
  obtain ⟨σ', hσ', hm', hq', hpre'⟩ := hA
  cases hb.hprio r' hr' hlt σ' hσ' hm' with
  | intro ht he hv => exact hv (EvalTerm.functional_of_fnDet hfd he (hq' _ ht))
  | pre hf => exact Bool.false_ne_true ((holds_trueV hfd hf).mp hpre')

/-- **A `StepVBy` step between configurations is a `StepBy` step**, for a semantics that `coreOK`
accepts where a term has at most one result and every function terminates, whose rules are well
sorted: `pre`, `post` and each competitor's `pre` have truth values (`holds_decided`), which the
value model's truth gives (`holds_trueV`); a competitor's `requires` has a result at each of its
matches (`Rule.decided_pp`). -/
theorem stepBy_of_stepVBy {c : Semantics} (h : c.coreOK = true) (hfd : FnDet c) (hft : FnTerminates c)
    (hsr : ∀ r' ∈ c.rules, c.ruleSorted r' = true)
    {r : Rule} {σ : Subst} {x y : Config c} (hb : StepVBy c r σ x.val y.val) : StepBy c r σ x y := by
  obtain ⟨hr, hσ, hm, hreq, hpre, hev, hens, hpost, hprio⟩ := hb
  have hsc := hypSound_of_core h
  obtain ⟨-, -, -, -, -, -, -, hokP, hokQ, -⟩ := ruleSorted_partsPP (hsr r hr)
  have htrue : ∀ {p : Cond}, c.condOK r.vars p = true → TrueV c r.vars.length σ p →
      Holds c r.vars.length σ p true := fun {p} hok ht => by
    obtain ⟨b, hb⟩ := holds_decided hsc hft p hok (hσ.at _)
    rw [(holds_trueV hfd hb).mp ht] at hb
    exact hb
  refine ⟨hr, hσ, hm, hreq, htrue hokP hpre, hev, hens, htrue hokQ hpost, fun r' hr' hlt σ' hσ' hm' => ?_⟩
  obtain ⟨hdq, b, hb⟩ := (Faithful.Rule.decided_pp hsc hft (hsr r' hr') x.val).1 σ' hσ' hm'
  by_cases hq : ∀ t, r'.req = some t → EvalTerm c σ' t (some (bool true))
  · cases b with
    | false => exact .pre hb
    | true => exact (hprio r' hr' hlt ⟨σ', hσ', hm', hq, (holds_trueV hfd hb).mpr rfl⟩).elim
  · obtain ⟨t, ht, hne⟩ : ∃ t, r'.req = some t ∧ ¬ EvalTerm c σ' t (some (bool true)) := by
      exact Classical.byContradiction fun hc =>
        hq fun t ht => Classical.byContradiction fun hn => hc ⟨t, ht, hn⟩
    obtain ⟨v, hv⟩ := hdq t ht
    exact .intro ht hv fun he => hne (he ▸ hv)

end KCore
