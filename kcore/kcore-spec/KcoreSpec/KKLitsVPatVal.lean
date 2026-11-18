import KcoreSpec.KKLitsVEval

/-!
# What a match of `d₀ d` binds has a `kore.k` form

Under `execReady d` and `encodable d`, the value a substitution gives a variable of a clause's
patterns or of a rule's left side is `litsV`, wherever the substitution gives that variable a value
of its sort (`WellSortedAt`, which `Eval`, `Fails` and a rule's match all state). The reason is the
variable's sort, never `Float`. A pattern is well sorted in a left side's context (`patCtxAll`), at
its function's argument sorts or the configuration sort. Every sort that context reads at an
argument position is one the signatures name (`sigSorts`) or an argument sort of a map, set or list
pattern symbol, and a variable inside an injection's source has the injection's source sort, a
subsort, which `sigSorts` names too. Under `encodable`, `sigSorts` names no `Float`, and a value of
a sort other than `Float` is `litsV` (`litsV_of_sorted`). So neither the match (`PatVal`) nor the
matched value is read.
-/

set_option autoImplicit false

namespace KCore.KK

theorem lookupSig_mem_kpv {heads : List CtorSig} {f : Sym} {k : CtorSig}
    (h : lookupSig heads f = some k) : k ∈ heads := by
  rw [lookupSig_eq] at h
  exact List.mem_of_find?_eq_some h

mutual
/-- In a context whose heads take no `Float` argument and whose subsorts have no `Float` below, a
variable of a term of a sort other than `Float` has a sort other than `Float`. -/
theorem varOccs_sort_kpv {x : TermCtx} {vars : List Srt}
    (hk : ∀ k ∈ x.heads, ∀ s ∈ k.args, s ≠ Srt.float)
    (hsub : ∀ a b, (a, b) ∈ x.subs → a ≠ Srt.float) :
    ∀ {t : Term} {s : Srt}, sortOfTerm x vars t = some s → s ≠ Srt.float →
      ∀ i ∈ varOccs t, ∃ s', vars[i]? = some s' ∧ s' ≠ Srt.float
  | .var j, s, h, hs, i, hi => by
    simp only [varOccs, List.mem_singleton] at hi
    subst hi
    exact ⟨s, sortOfTerm_var.mp h, hs⟩
  | .dv _ _, _, _, _, i, hi => by simp [varOccs] at hi
  | .app f ts, s, h, _, i, hi => by
    obtain ⟨k, hl, hargs, _⟩ := sortOfTerm_app.mp h
    exact varOccsList_sort_kpv hk hsub hargs (hk k (lookupSig_mem_kpv hl)) i
      (by simpa [varOccs] using hi)
  | .inj a b t, s, h, _, i, hi => by
    obtain ⟨hab, ht, _⟩ := sortOfTerm_inj.mp h
    exact varOccs_sort_kpv hk hsub ht (hsub a b hab) i (by simpa [varOccs] using hi)
  | .as t j, s, h, hs, i, hi => by
    obtain ⟨hj, ht⟩ := Exec.sortOfTerm_as h
    simp only [varOccs, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact varOccs_sort_kpv hk hsub ht hs i hi
    · exact ⟨s, hj, hs⟩
theorem varOccsList_sort_kpv {x : TermCtx} {vars : List Srt}
    (hk : ∀ k ∈ x.heads, ∀ s ∈ k.args, s ≠ Srt.float)
    (hsub : ∀ a b, (a, b) ∈ x.subs → a ≠ Srt.float) :
    ∀ {ts : List Term} {ss : List Srt}, sortsOfTerms x vars ts = some ss →
      (∀ s ∈ ss, s ≠ Srt.float) → ∀ i ∈ varOccsList ts, ∃ s', vars[i]? = some s' ∧ s' ≠ Srt.float
  | [], _, _, _, i, hi => by simp [varOccsList] at hi
  | t :: ts, ss, h, hss, i, hi => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
    simp only [varOccsList, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccs_sort_kpv hk hsub h1 (hss s (by simp)) i hi
    · exact varOccsList_sort_kpv hk hsub h2 (fun s' h' => hss s' (by simp [h'])) i hi
end

/-- The map pattern symbols take no `Float` argument. -/
theorem patternHookSigs_kpv :
    (hookSigs.filter (patternHooks.contains ·.name)).all (fun k => !k.args.contains Srt.float) =
      true := by decide

/-- The set and list pattern symbols take no `Float` argument. -/
theorem collPatternHookSigs_kpv :
    (hookSigs.filter (collPatternHooks.contains ·.name)).all (fun k => !k.args.contains Srt.float) =
      true := by decide

theorem noFloatArg_kpv {L : List CtorSig}
    (h : L.all (fun k => !k.args.contains Srt.float) = true) {k : CtorSig} (hk : k ∈ L) :
    ∀ s ∈ k.args, s ≠ Srt.float := by
  intro s hs he
  subst he
  have := List.all_eq_true.mp h k hk
  simp only [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false] at this
  exact this _ hs (beq_self_eq_true _)

/-- Under `encodable c`, no head of a left side's context takes a `Float` argument. -/
theorem patCtxAll_heads_kpv {c : Semantics} (hc : encodable c = true) :
    ∀ k ∈ c.patCtxAll.heads, ∀ s ∈ k.args, s ≠ Srt.float := by
  obtain ⟨ho, -, hf⟩ := encodable_facts hc
  have hne : ∀ {x}, x ∈ sigSorts c → x ≠ Srt.float := fun hx he => hf (he ▸ hx)
  intro k hk
  simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs, Semantics.ovlSigs, ho,
    List.map_nil, List.append_nil, List.mem_append] at hk
  rcases hk with (hk | hk) | hk | hk
  · exact fun s hs => hne (sigSorts_ctor_kel hk hs)
  · exact noFloatArg_kpv patternHookSigs_kpv hk
  · exact noFloatArg_kpv collPatternHookSigs_kpv hk
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact fun s hs => hne (sigSorts_param_kel (List.mem_filter.mp hp).1 hs)

/-- Under `encodable c`, no subsort of `c` is `Float`. -/
theorem patCtxAll_subs_kpv {c : Semantics} (hc : encodable c = true) :
    ∀ a b, (a, b) ∈ c.patCtxAll.subs → a ≠ Srt.float := by
  obtain ⟨-, -, hf⟩ := encodable_facts hc
  intro a b hab he
  exact hf (he ▸ sigSorts_sub_kel hab)

theorem sigSorts_fnArg_kpv {c : Semantics} {fn : Fn} (hfn : fn ∈ c.allFns) {s : Srt}
    (hs : s ∈ fn.args) : s ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inl (.inl (.inr ⟨fn, hfn, .inr hs⟩)))

/-- A clause's patterns, under `sortedOK`, have their function's argument sorts in a left side's
context: the user's functions by `clauseSorted`, the sort predicates by their definition. -/
theorem clause_patSorts_kpv {c : Semantics} (hok : c.sortedOK = true) {fn : Fn}
    (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args := by
  rcases List.mem_append.mp hfn with hfn | hfn
  · have h' := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at h'
    have := h'.1.2 fn hfn cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.1.1.1.1
  · exact sortsOfTerms_heads _ _ _ _ (sortPreds_ctx hfn cl hcl).1

/-- A substitution that gives a variable of a sort other than `Float` a value of its sort gives it a
`litsV` value, under `encodable`. -/
theorem litsV_wellSortedAt_kpv {c : Semantics} (hc : encodable c = true) {vars : List Srt}
    {is : List Nat} {σ : Subst} (hσ : c.WellSortedAt vars is σ) {i : Nat} (his : i ∈ is)
    (hs : ∃ s, vars[i]? = some s ∧ s ≠ Srt.float) {v : GroundTerm} (hv : σ.lookup i = some v) :
    litsV v = true := by
  obtain ⟨s, hs, hsf⟩ := hs
  obtain ⟨w, hw, hws⟩ := hσ i his s hs
  rw [hv] at hw; cases hw
  exact litsV_of_sorted hc hws hsf

/-- A variable of a clause's patterns, in `d₀ d`, has a sort other than `Float`. -/
theorem clause_patVar_sort_kpv {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) {i : Nat} (hi : i ∈ varOccsList cl.pats) :
    ∃ s, cl.vars[i]? = some s ∧ s ≠ Srt.float := by
  obtain ⟨hok, -, -, hc⟩ := d₀_facts_kkv hx he
  obtain ⟨-, -, hf⟩ := encodable_facts hc
  exact varOccsList_sort_kpv (patCtxAll_heads_kpv hc) (patCtxAll_subs_kpv hc)
    (clause_patSorts_kpv hok hfn hcl)
    (fun s hs he => hf (he ▸ sigSorts_fnArg_kpv hfn hs)) i hi

/-- A variable of a rule's left side, in `d₀ d`, has a sort other than `Float`. -/
theorem rule_patVar_sort_kpv {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {r : Rule} (hr : r ∈ (d₀ d).rules) {i : Nat}
    (hi : i ∈ varOccs r.lhs) : ∃ s, r.vars[i]? = some s ∧ s ≠ Srt.float := by
  obtain ⟨hok, -, -, hc⟩ := d₀_facts_kkv hx he
  have h' := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at h'
  have hs := h'.2 r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at hs
  exact varOccs_sort_kpv (patCtxAll_heads_kpv hc) (patCtxAll_subs_kpv hc)
    (sortOfTerm_all_of_nf hs.1.1.1.1.1.1.1.1.1.1) (by decide) i hi

/-- **What a clause's match binds is `litsV`.** A substitution that gives the variables `is` values
of their sorts gives each variable of a clause's patterns among them a value whose literals have a
`kore.k` form. `Eval`'s clauses give `WellSorted` (`litsV_patVar_clause_ws`), `Fails` gives
`WellSortedAt` at `leftVars`, which holds the patterns' variables. -/
theorem litsV_patVar_clause {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) {is : List Nat} {σ : Subst} (hσ : (d₀ d).WellSortedAt cl.vars is σ)
    {i : Nat} (hi : i ∈ varOccsList cl.pats) (his : i ∈ is) {v : GroundTerm}
    (hv : σ.lookup i = some v) : litsV v = true :=
  litsV_wellSortedAt_kpv (d₀_facts_kkv hx he).2.2.2 hσ his (clause_patVar_sort_kpv hx he hfn hcl hi)
    hv

/-- What a clause's match binds under a well-sorted substitution is `litsV`. -/
theorem litsV_patVar_clause_ws {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) {σ : Subst} (hσ : (d₀ d).WellSorted cl.vars σ) {i : Nat}
    (hi : i ∈ varOccsList cl.pats) {v : GroundTerm} (hv : σ.lookup i = some v) : litsV v = true :=
  litsV_patVar_clause hx he hfn hcl (is := [i]) (fun j _ s hs => hσ j s hs) hi (by simp) hv

/-- **What a rule's match binds is `litsV`.** A substitution that gives the variables `is` values
of their sorts gives each variable of a rule's left side among them a value whose literals have a
`kore.k` form. -/
theorem litsV_patVar_rule {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {r : Rule} (hr : r ∈ (d₀ d).rules) {is : List Nat} {σ : Subst}
    (hσ : (d₀ d).WellSortedAt r.vars is σ) {i : Nat} (hi : i ∈ varOccs r.lhs) (his : i ∈ is)
    {v : GroundTerm} (hv : σ.lookup i = some v) : litsV v = true :=
  litsV_wellSortedAt_kpv (d₀_facts_kkv hx he).2.2.2 hσ his (rule_patVar_sort_kpv hx he hr hi) hv

/-- What a rule's match binds under a well-sorted substitution is `litsV`. -/
theorem litsV_patVar_rule_ws {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {r : Rule} (hr : r ∈ (d₀ d).rules) {σ : Subst}
    (hσ : (d₀ d).WellSorted r.vars σ) {i : Nat} (hi : i ∈ varOccs r.lhs) {v : GroundTerm}
    (hv : σ.lookup i = some v) : litsV v = true :=
  litsV_patVar_rule hx he hr (is := [i]) (fun j _ s hs => hσ j s hs) hi (by simp) hv

end KCore.KK
