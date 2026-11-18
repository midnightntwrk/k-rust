import KcoreSpec.KKEncLemmas

/-!
# What an evaluation of `d₀ d` produces has a `kore.k` form

Under `execReady d` and `encodable d`, every value an evaluation of `d₀ d` produces is `litsV`: its
literals have a `kore.k` form, so `enc` writes no `bot` in it. The reason is the value's sort. A
function's result has its result sort (`Eval.sorted_of_all`), which `sigSorts` names; a right side
of a clause has its function's result sort, a right side of a rule the configuration sort, a
`requires` and an `ensures` the sort `Bool` (`clauseSorted`, `ruleSorted`); none is `Float`, and
under `encodable` a value of a sort other than `Float` is `litsV` (`litsV_of_sorted`). No literal
of an argument or of the substitution is read: a variable's value has the variable's sort, and
the evaluation's value the term's.
-/

set_option autoImplicit false

namespace KCore.KK

/-- What `execReady` and `encodable` give `d₀ d`. -/
theorem d₀_facts_kkv {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true) :
    (d₀ d).sortedOK = true ∧ (d₀ d).srReady = true ∧ (d₀ d).OvlCase ∧ encodable (d₀ d) = true := by
  have hx' : CExec.execReady (d₀ d) = true := (CExec.execReady_withHooks d _).trans hx
  have hc : encodable (d₀ d) = true := by
    rw [← encDef_isSome, encDef_withHooks, encDef_isSome]; exact he
  simp only [CExec.execReady, Bool.and_eq_true] at hx'
  exact ⟨hx'.1.1.1.1.1.1, hx'.1.1.1.1.1.2, .inl (encodable_facts hc).1, hc⟩

theorem sigSorts_fn_kkv {c : Semantics} {fn : Fn} (hfn : fn ∈ c.allFns) : fn.result ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inl (.inl (.inr ⟨fn, hfn, .inl rfl⟩)))

/-- A function of `d₀ d` at arguments of its argument sorts produces a value whose literals have
a `kore.k` form. -/
theorem eval_litsV {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true)
    {f : Sym} {vs : List GroundTerm} {v : GroundTerm} (h : Eval (d₀ d) f vs (some v)) {fn : Fn}
    (hfn : (d₀ d).lookupFn f = some fn) (hvs : (d₀ d).sortsOf vs = some fn.args) : litsV v = true := by
  obtain ⟨hok, hsr, hov, hc⟩ := d₀_facts_kkv hx he
  have hs := Eval.sorted_of_all hok hsr hov h hfn hvs
  have hm := sigSorts_fn_kkv (lookupFn_spec hfn).1
  exact litsV_of_sorted hc hs fun e => (encodable_facts hc).2.2 (e ▸ hm)

/-- A term of a sort other than `Float`, evaluated in `d₀ d` under a well-sorted substitution,
produces a value whose literals have a `kore.k` form. -/
theorem evalTerm_litsV_sorted_kkv {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {L : List CtorSig} (hL : HeadsOK (d₀ d) L) {vars : List Srt}
    {σ : Subst} (hσ : (d₀ d).WellSorted vars σ) {t : Term} {s : Srt}
    (ht : sortOfTerm ((d₀ d).rhsCtx L) vars t = some s) (hs : s ≠ Srt.float) {v : GroundTerm}
    (h : EvalTerm (d₀ d) σ t (some v)) : litsV v = true := by
  obtain ⟨hok, hsr, hov, hc⟩ := d₀_facts_kkv hx he
  exact litsV_of_sorted hc (EvalTerm.sorted (sortCtx_of_all hok hsr hov) h hL hσ ht rfl) hs

theorem headsOK_fns_kkv (c : Semantics) : HeadsOK c (c.fns.map Fn.sig) := by
  intro k hk
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
  exact ⟨g, List.mem_append_left _ hg, rfl⟩

theorem reqOK_some_kkv {x : TermCtx} {vs : List Srt} {o : Option Term} (h : reqOK x vs o = true)
    {t : Term} (ht : o = some t) : sortOfTerm x vs t = some Srt.bool := by
  subst ht; simpa [reqOK] using h

/-- The `requires`, right side and `ensures` of a clause of `d₀ d`, evaluated under a substitution
well sorted on the clause's variables, produce values whose literals have a `kore.k` form. -/
theorem evalTerm_litsV_clause {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) {σ : Subst} (hσ : (d₀ d).WellSorted cl.vars σ) {t : Term}
    (ht : t ∈ cl.req.toList ++ [cl.rhs] ++ cl.ens.toList) {v : GroundTerm}
    (h : EvalTerm (d₀ d) σ t (some v)) : litsV v = true := by
  obtain ⟨hok, -, -, hc⟩ := d₀_facts_kkv hx he
  have hbool : Srt.bool ≠ Srt.float := by decide
  have hres : fn.result ≠ Srt.float := fun e => (encodable_facts hc).2.2 (e ▸ sigSorts_fn_kkv hfn)
  obtain ⟨L, hL, hreq, hrhs, hens⟩ : ∃ L, HeadsOK (d₀ d) L ∧
      reqOK ((d₀ d).rhsCtx L) cl.vars cl.req = true ∧
      sortOfTerm ((d₀ d).rhsCtx L) cl.vars cl.rhs = some fn.result ∧
      reqOK ((d₀ d).rhsCtx L) cl.vars cl.ens = true := by
    rcases List.mem_append.mp hfn with hfn | hfn
    · have h' := Semantics.sortedOK_sorted hok
      simp only [Bool.and_eq_true, List.all_eq_true] at h'
      have := h'.1.2 fn hfn cl hcl
      simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨_, headsOK_fns_kkv _, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2⟩
    · obtain ⟨-, -, -, h1, h2, h3⟩ := sortPreds_ctx hfn cl hcl
      exact ⟨[], (fun k hk => nomatch hk : HeadsOK (d₀ d) []), h1, h2, h3⟩
  simp only [List.mem_append, Option.mem_toList, List.mem_singleton] at ht
  rcases ht with (ht | rfl) | ht
  · exact evalTerm_litsV_sorted_kkv hx he hL hσ (reqOK_some_kkv hreq ht) hbool h
  · exact evalTerm_litsV_sorted_kkv hx he hL hσ hrhs hres h
  · exact evalTerm_litsV_sorted_kkv hx he hL hσ (reqOK_some_kkv hens ht) hbool h

/-- The `requires`, right side and `ensures` of a rule of `d₀ d`, evaluated under a substitution
well sorted on the rule's variables, produce values whose literals have a `kore.k` form. -/
theorem evalTerm_litsV_rule {d : Semantics} (hx : CExec.execReady d = true)
    (he : encodable d = true) {r : Rule} (hr : r ∈ (d₀ d).rules) {σ : Subst}
    (hσ : (d₀ d).WellSorted r.vars σ) {t : Term} (ht : t ∈ r.req.toList ++ [r.rhs] ++ r.ens.toList)
    {v : GroundTerm} (h : EvalTerm (d₀ d) σ t (some v)) : litsV v = true := by
  obtain ⟨hok, -, -, -⟩ := d₀_facts_kkv hx he
  have hbool : Srt.bool ≠ Srt.float := by decide
  have htop : topCellSort ≠ Srt.float := by decide
  have h' := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at h'
  have hs := h'.2 r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at hs
  simp only [List.mem_append, Option.mem_toList, List.mem_singleton] at ht
  rcases ht with (ht | rfl) | ht
  · exact evalTerm_litsV_sorted_kkv hx he (headsOK_fns_kkv _) hσ
      (reqOK_some_kkv hs.1.1.1.1.1.1.2 ht) hbool h
  · exact evalTerm_litsV_sorted_kkv hx he (headsOK_fns_kkv _) hσ hs.2 htop h
  · exact evalTerm_litsV_sorted_kkv hx he (headsOK_fns_kkv _) hσ
      (reqOK_some_kkv hs.1.1.1.1.2 ht) hbool h

end KCore.KK
