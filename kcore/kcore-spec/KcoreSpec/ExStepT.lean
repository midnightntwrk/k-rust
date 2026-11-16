/-
  KCore. The value model at a transition T satisfies the step's closure where every T step between
  configurations is a `StepM` step (`hsub`), for rules with existential variables.

  The closure axiom is `∀y. •y ⊆ ⋁_r ∃x̄_r. (L_r ∧ y ∈ ∃ē_r. (rhs_r ∧ ens_r))`, x̄_r the free
  variables of rule r's axiom: those of the rule but its existential ones (`freeOf_prio_T`). A
  `StepMAt` step by r from x to y under σ puts x in r's disjunct: x̄_r read as σ gives x in L_r
  (`rule_premise_T`, with σ itself for the ⌈∃ē. …⌉ conjunct), and y in the right side
  (`ruleRight_read_T`, with σ at ē) (`closureDisjunct_T`).

  - `freeOf_ruleRightEx`, `freeOf_prio_T`: the free variables of a rule's right side and axiom are
    its own, none of them existential.
  - `closureDisjunct_T`: a `StepMAt` step by a rule with `ruleSorted` and `rulePlainEx` (not asked
    to be one of the definition's) is in its disjunct of the closure, at any T.
  - `satStepGoal_T`: the value model at T satisfies `Γstep c` where every T step is a `StepM` step,
    for a definition whose rules have `ruleSorted` and `rulePlainEx`, taken per rule.
-/
import KcoreSpec.ExModelT

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- The free variables of a rule's right side are variables of the rule other than its existential
ones. -/
theorem freeOf_ruleRightEx {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
    {k : KoreAML.VarKey} (hk : k ∈ KoreAML.freeOf [] (ruleRight c r)) :
    ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := by
  obtain ⟨-, -, -, hensS, hrhss, -, hexs⟩ := ruleSorted_partsEx hs hp
  obtain ⟨-, hpost⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  rw [ruleRight_eqEx hpost hlt, freeOf_existsAll_eqEx] at hk
  -- a variable the binders hold is existential
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
  unfold ruleRightBody at hk
  rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
  simp only [List.append_nil, List.mem_append] at hk
  rcases hk with hk | hk
  · exact hterm r.rhs (by rw [hrhss]; exact Option.some_ne_none _) hk
  · cases hq : r.ens with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hterm t (by rw [hensS t hq]; exact Option.some_ne_none _) hk
      · rw [KoreAML.freeOf] at hk; cases hk

/-- The free variables of the axiom of a rule with `ruleSorted` and `rulePlainEx`, among rules with
those facts, are variables of the rule other than its existential ones. -/
theorem freeOf_prio_T (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] (prioRuleK c r)) :
    ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i := by
  obtain ⟨hlhs, -, hreqs, -, -, -, hexs⟩ := ruleSorted_partsEx hs hp
  obtain ⟨hpre₀, -⟩ := Semantics.rulePlainEx_top hp
  have hR := fun {k} (h' : k ∈ KoreAML.freeOf [] (ruleRight c r)) => freeOf_ruleRightEx hs hp h'
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
  rw [prioRuleK_preTop hpre₀] at hk
  dsimp only at hk
  split at hk
  · simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk | hk) | hk
    · exact hL hk
    · exact hQ hk
    · exact hR hk
    · exact hR hk
  · simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk | hk | hk) | hk
    · exact hL hk
    · exact hQ hk
    · exfalso
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hs', hp'⟩ := hrules r' (List.mem_filter.mp hr').1
      obtain ⟨hlhs', -, hreqs', -, -, -⟩ := ruleSorted_partsEx hs' hp'
      exact freeOf_appliesOpen hlhs' (fun t ht i hi => varOccs_lt t (hreqs' t ht) i hi)
        (Semantics.rulePlainEx_top hp').1 hk
    · exact hR hk
    · exact hR hk

theorem sExists_foldr_intro_T {T : GroundTerm → GroundTerm → Prop} {tbl : KoreAML.VarTable} {body : KoreAML.P} :
    ∀ (free : List (KoreAML.VarKey × Kore.KSort)) (e e' : Valuation Elem) (m : Elem),
    (∀ x, (∀ ks ∈ free, x ≠ tbl.ev ks.1) → e'.evalEvar x = e.evalEvar x) →
    e'.evalSvar = e.evalSvar →
    (∀ ks ∈ free, ∃ n, ks.2 = KoreAML.srt n ∧ InS (stdI_T c T) n (e'.evalEvar (tbl.ev ks.1))) →
    body.interpret (stdI_T c T) e' m →
    (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body).interpret
      (stdI_T c T) e m
  | [], e, e', m, hoff, hsv, _, hb => by
    have : e' = e := by
      cases e; cases e'
      simp only at hsv
      subst hsv
      congr 1
      funext x
      exact hoff x (fun _ h => absurd h List.not_mem_nil)
    subst this
    exact hb
  | (k, s) :: free, e, e', m, hoff, hsv, hg, hb => by
    show (KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s)
      (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body)).interpret
        (stdI_T c T) e m
    rw [KoreAML.interp_sExists]
    refine ⟨e'.evalEvar (tbl.ev k), ?_, ?_⟩
    · rw [KoreAML.interp_member AtT.defOK_std]
      simp only [Function.update_same]
      obtain ⟨n, hn, hin⟩ := hg (k, s) (List.mem_cons_self ..)
      simp only at hn
      rw [hn, trSort_srt]
      exact (inS_iff _).mpr hin
    · refine sExists_foldr_intro_T free _ e' m (fun x hx => ?_) hsv
        (fun ks hks => hg ks (List.mem_cons_of_mem _ hks)) hb
      show e'.evalEvar x = Function.update e.evalEvar (tbl.ev k) (e'.evalEvar (tbl.ev k)) x
      by_cases hxk : x = tbl.ev k
      · subst hxk; simp only [Function.update_same]
      · rw [Function.update_noteq hxk]
        exact hoff x (fun ks hks => by
          rcases List.mem_cons.mp hks with rfl | hks
          · exact hxk
          · exact hx ks hks)

/-- **A step by a rule is in its disjunct of the closure, at any T.** For a rule with `ruleSorted`
and `rulePlainEx` (not asked to be one of the definition's), among rules with those facts: a
`StepMAt` step from the configuration x to y, y the value of the closure's variable, puts x in the
rule's disjunct `∃x̄. (L ∧ y ∈ ∃ē. (rhs ∧ ens))`, x̄ read as σ off ē. -/
theorem closureDisjunct_T (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) {T : GroundTerm → GroundTerm → Prop}
    {σ : Subst} {x yv : GroundTerm} (hst : StepMAt c r σ x yv) (hx : c.sortOf x = some topCellSort)
    (off : Nat) (y : EVar)
    (hy_ne : ∀ k ∈ List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r),
      y ≠ KoreAML.VarTable.ev (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r)) k)
    (e1 : Valuation Elem) (he1 : e1.evalEvar y = .val yv) :
    (KoreAML.closureDisjunct [] off y (prioRuleK c r)).2.interpret (stdI_T c T) e1 (.val x) := by
  have hn := h.namesK
  obtain ⟨hσ, hmatch, hreq, heval, hens, hprio⟩ := hst
  have hnum := rule_vars_numEx h hs hp
  obtain ⟨L, hPL, hLv, hLf, hLread⟩ := rule_premise_T h hrules hs hp
  let P := prioRuleK c r
  let tbl : KoreAML.VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] P
  have hin_tbl : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ hk))
  have hinL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => hin_tbl k (by
    show _ ∈ KoreAML.varsOf (prioRuleK c r)
    rw [hPL, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hinL _ (hLv i hi)
  -- the valuation of the rule's variables but the existential ones, which are bound
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
      ⟨hmatch, hreq, hprio, σ, yv, fun _ _ _ => rfl, hσ, heval, hens⟩
  have hRy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret (stdI_T c T) e' (.val yv) :=
    (ruleRight_read_T h hs hp hkeys (fun i hi _ => hval i hi) hvar _).mpr
      ⟨σ, yv, fun _ _ _ => rfl, hσ, heval, hens, rfl⟩
  -- the disjunct's existentials
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
    obtain ⟨i, hi, hx, he⟩ := freeOf_prio_T hrules hs hp (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, hx, he, ?_⟩
    rw [he, canonKey_eq c hi] at hnm
    injection hnm with _ h2
    exact h2.symm
  refine sExists_foldr_intro_T _ e1 e' _ (fun z hz => ?_) rfl ?_ ?_
  · -- off the binders the valuation is unchanged
    show (if h : _ then _ else _) = _
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

/-- **The step's closure holds in the value model at T**, for a definition whose rules have
`ruleSorted` and `rulePlainEx`, taken per rule, where every T step between configurations is a
`StepM` step (`hsub`): each T successor of a configuration lies in the right side `∃ē. (rhs ∧ ens)`
of the rule that gives it, the configuration in that rule's left part. -/
theorem satStepGoal_T (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepM c x y) :
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
  obtain ⟨r, hr, σ, hstep⟩ := hsub x yv hx hyv hT
  obtain ⟨hs, hp⟩ := hrules r hr
  obtain ⟨off, hoff, hmem⟩ := stepF_mem y (c.rules.map (prioRuleK c)) ([], [], 0) (prioRuleK c r)
    (List.mem_map.mpr ⟨r, hr, rfl⟩)
  refine AtT.disjList_intro hmem (closureDisjunct_T h hrules hs hp hstep hx off y (fun k hk he => ?_) e1 hb0a.symm)
  have h1 := index_le hk
  have hoff' : off + (KoreAML.tableOf [] (prioRuleK c r)).length ≤ tablesLen (c.rules.map (prioRuleK c)) 0 := hoff
  rw [← he, ← hy] at h1
  have h2 : (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (prioRuleK c r)).length =
      off + (KoreAML.tableOf [] (prioRuleK c r)).length := by simp
  simp only at h1
  omega

end Model

end Faithful

end KCore
