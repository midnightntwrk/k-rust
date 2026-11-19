/-
  The step cases of the induction on an evaluation of kore.k (User.SpecMotive) at the functions
  that evaluate terms: `eval`, `evalTs`, `strictHook` (and `ensure`, User.SpecMotive's
  `stepCase_ensure`).

  A step case holds one constructor of `Eval` at the function, with `Spec` at each call its
  premises make. Every equation of `eval` and `evalTs` is a plain clause of priority 50 (no
  `requires`, `ensures`, predicate or existential variable), so where one equation's patterns
  match the arguments under a well-sorted substitution, the constructor is `clause` at an equation
  whose patterns match, with its right side evaluated under that equation's substitution
  (`byClause_plain_kst`). The equations of `eval` have patterns of pairwise distinct heads, so at a
  term of a given head the equation is that head's, and its right side's calls are read off
  (`eval_ap_inv_kst`, …).

  - `eval` at the instance of a term (`EvalForm.term`): a variable's instance is the encoding of
    its value, which `eval` gives back (`eval_value`); a literal's is `iv`, `bv` or `tk`, which
    `ev-int`, `ev-bool`, `ev-tok` give back; an injection's is `ij`, and `mkInj` at the encoding of
    the argument's result is the encoding of the injected result; an application's is read as
    `encTerm` reads it (`readApp`): a constructor or a function is `ap`, evaluated by `apply` at
    the results of `evalTs`, an interpreted symbol with an operation code is `hk`, evaluated by
    `strictHook`, and `=/=Bool` is `hk 22 [hk 23 As]`, whose inner term is the instance of the
    application of `==Bool` to the same arguments; an application of a collection symbol (`cb`) is
    the case `CbStep_kst`, which the step case at `eval` takes as its hypothesis.
  - `eval` at an element, an entry and a right side with its ensures: `mkEl`, `mkKv`, `ensure` at
    the results of the terms.
  - `evalTs`: each term in turn.
  - `strictHook` at a code and the encodings of results: the hook lemmas of User.HooksScalar and
    User.HooksColl where all results are values, `hook-bot` where one is `bot`.

  The object side: the term is sorted (`TermOK_ksm`), so its arguments are sorted at the
  signature its head is found under (`sortOfTerm`), their values have those sorts
  (`EvalTerm.sorted_at`), and a sort of a signature `encodable` admits is not `Float`, so the values'
  literals have kore.k forms (`litsV_of_sorted`).
-/
import User.SpecMotive
import User.EvalValue
import User.HooksScalar
import User.HooksColl
import User.CollVal

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## Inverting a call of a function with plain clauses -/

section Inv
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

variable {R : CallRel}

theorem EvalTermR.var_inv_kst {σ : Subst} {i : Nat} {r : Option GroundTerm}
    (h : EvalTermR c₀ R σ (.var i) r) : r = σ.lookup i := by
  generalize ht : Term.var i = t at h
  cases h with
  | var => cases ht; rfl
  | _ => cases ht

/-- An application of a function (neither a constructor nor a hook nor a parameter nor an
overloading symbol) is a call at its arguments' results, or undefined where one is. -/
theorem EvalTermR.call_inv_kst {σ : Subst} {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c₀.isCtor f = false) (hh : isHook f = false) (hp : c₀.isParam f = false)
    (ho : c₀.isOvl f = false) (h : EvalTermR c₀ R σ (.app f ts) r) :
    ∃ rs, EvalTermsR c₀ R σ ts rs ∧
      ((∃ vs, allSome rs = some vs ∧ R f vs r) ∨ (allSome rs = none ∧ r = none)) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | hook _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | param _ _ h _ _ => cases ht; rw [hp] at h; cases h
  | call _ _ hts hvs hf _ => cases ht; exact ⟨_, hts, .inl ⟨_, hvs, hf⟩⟩
  | callUndef _ _ hts hvs _ => cases ht; exact ⟨_, hts, .inr ⟨hvs, rfl⟩⟩
  | ovl _ h _ => cases ht; rw [ho] at h; cases h
  | ovlFn _ h => cases ht; rw [ho] at h; cases h
  | _ => cases ht

/-- A constructor application is the constructor term of its arguments' results. -/
theorem EvalTermR.ctor_inv_kst {σ : Subst} {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c₀.isCtor f = true) (h : EvalTermR c₀ R σ (.app f ts) r) :
    ∃ rs, EvalTermsR c₀ R σ ts rs ∧ r = (allSome rs).map (.ctor f) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor _ hts => cases ht; exact ⟨_, hts, rfl⟩
  | hook h _ _ _ _ => cases ht; rw [hc] at h; cases h
  | param h _ _ _ _ => cases ht; rw [hc] at h; cases h
  | call h _ _ _ _ _ => cases ht; rw [hc] at h; cases h
  | callUndef h _ _ _ _ => cases ht; rw [hc] at h; cases h
  | ovl h _ _ => cases ht; rw [hc] at h; cases h
  | ovlFn h _ => cases ht; rw [hc] at h; cases h
  | _ => cases ht

/-- **A call of a function whose clauses are plain.** Where every clause of `f` has no `requires`,
`ensures`, predicate or existential variable, and some clause's patterns match the arguments under
a well-sorted substitution, the constructor of a `ByClause` derivation is `clause`: some clause's
patterns match under a substitution under which its right side has the result. -/
theorem byClause_plain_kst {f : Sym} {fn : Fn} {vs : List GroundTerm} {r : Option GroundTerm}
    (hb : ByClause c₀ R f vs r) (hfn : c₀.lookupFn f = some fn)
    (hpl : ∀ cl ∈ fn.clauses, cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top)
    {cl₀ : Clause} (hcl₀ : cl₀ ∈ fn.clauses) {σ₀ : Subst} (hσ₀ : c₀.WellSorted cl₀.vars σ₀)
    (hp₀ : PatVals c₀ σ₀ cl₀.pats vs) :
    ∃ cl ∈ fn.clauses, ∃ σ, PatVals c₀ σ cl.pats vs ∧ EvalTermR c₀ R σ cl.rhs r := by
  cases hb with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact ⟨_, hmem, _, hmatch, hrhs⟩
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    obtain ⟨hq, -, -, hpre⟩ := hpl cl₀ hcl₀
    cases hnone cl₀ hcl₀ with
    | intro h =>
      cases h σ₀ (hσ₀.at _) hp₀ with
      | intro ht _ _ => rw [hq] at ht; cases ht
      | pre hf => rw [hpre] at hf; cases hf
  | ensFails hfn' hmem _ _ _ _ _ _ ht =>
    rw [hfn] at hfn'; cases hfn'
    rw [(hpl _ hmem).2.1] at ht; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hpl _ hmem).2.2.1 hne
  | exNone hfn' hmem hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hpl _ hmem).2.2.1 hne

/-- A call at two variables with values. -/
theorem EvalTermR.call2_kst {σ : Subst} {g : Sym} {i j : Nat} {a b : GroundTerm}
    {r : Option GroundTerm} (hc : c₀.isCtor g = false) (hh : isHook g = false)
    (hp : c₀.isParam g = false) (ho : c₀.isOvl g = false) (hi : σ.lookup i = some a)
    (hj : σ.lookup j = some b) (h : EvalTermR c₀ R σ (.app g [.var i, .var j]) r) : R g [a, b] r := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  rcases hts with _ | ⟨e0, _ | ⟨e1, _ | _⟩⟩
  rw [EvalTermR.var_inv_kst e0, EvalTermR.var_inv_kst e1, hi, hj] at hcase
  rcases hcase with ⟨vs, hvs, hR⟩ | ⟨hn, -⟩
  · simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
    subst hvs; exact hR
  · simp [allSome] at hn

/-- `allSome` at two results. -/
theorem allSome_two_kst {a b : Option GroundTerm} {ws : List GroundTerm}
    (h : allSome [a, b] = some ws) : ∃ x y, a = some x ∧ b = some y ∧ ws = [x, y] := by
  cases a <;> cases b <;> simp [allSome] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem allSome_two_none_kst {a b : Option GroundTerm} (h : allSome [a, b] = none) :
    a = none ∨ b = none := by
  cases a <;> cases b <;> simp [allSome] at h <;> simp

/-- `allSome` at two values and one result. -/
theorem allSome_ss_kst {a b : GroundTerm} {q : Option GroundTerm} {vs : List GroundTerm}
    (h : allSome [some a, some b, q] = some vs) : ∃ y, q = some y ∧ vs = [a, b, y] := by
  cases q <;> simp [allSome] at h ⊢
  exact h.symm

theorem allSome_ss_none_kst {a b : GroundTerm} {q : Option GroundTerm}
    (h : allSome [some a, some b, q] = none) : q = none := by
  cases q <;> simp [allSome] at h ⊢

/-- `allSome` at one value and one result. -/
theorem allSome_s_kst {a : GroundTerm} {q : Option GroundTerm} {vs : List GroundTerm}
    (h : allSome [some a, q] = some vs) : ∃ y, q = some y ∧ vs = [a, y] := by
  cases q <;> simp [allSome] at h ⊢
  exact h.symm

theorem allSome_s_none_kst {a : GroundTerm} {q : Option GroundTerm}
    (h : allSome [some a, q] = none) : q = none := by
  cases q <;> simp [allSome] at h ⊢

/-- `allSome` at one result. -/
theorem allSome_one_kst {q : Option GroundTerm} {vs : List GroundTerm}
    (h : allSome [q] = some vs) : ∃ y, q = some y ∧ vs = [y] := by
  cases q <;> simp [allSome] at h ⊢
  exact h.symm

theorem allSome_one_none_kst {q : Option GroundTerm} (h : allSome [q] = none) : q = none := by
  cases q <;> simp [allSome] at h ⊢

/-- A call at two variables with values and one more term, as `apply(D, F, evalTs(D, As))` and
`colOf(K, C, evalTs(D, Ps))` are. -/
theorem EvalTermR.call3_kst {σ : Subst} {g : Sym} {i j : Nat} {a b : GroundTerm} {t : Term}
    {r : Option GroundTerm} (hc : c₀.isCtor g = false) (hh : isHook g = false)
    (hp : c₀.isParam g = false) (ho : c₀.isOvl g = false) (hi : σ.lookup i = some a)
    (hj : σ.lookup j = some b) (h : EvalTermR c₀ R σ (.app g [.var i, .var j, t]) r) :
    ∃ q, EvalTermR c₀ R σ t q ∧ ((∃ y, q = some y ∧ R g [a, b, y] r) ∨ (q = none ∧ r = none)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  rcases hts with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩⟩
  rw [EvalTermR.var_inv_kst e0, EvalTermR.var_inv_kst e1, hi, hj] at hcase
  refine ⟨_, e2, ?_⟩
  rcases hcase with ⟨vs, hvs, hR⟩ | ⟨hn, hr⟩
  · obtain ⟨y, rfl, rfl⟩ := allSome_ss_kst hvs
    exact .inl ⟨y, rfl, hR⟩
  · exact .inr ⟨allSome_ss_none_kst hn, hr⟩

/-- A call at one variable with a value and one more term, as `strictHook(O, evalTs(D, As))`
is. -/
theorem EvalTermR.call2t_kst {σ : Subst} {g : Sym} {i : Nat} {a : GroundTerm} {t : Term}
    {r : Option GroundTerm} (hc : c₀.isCtor g = false) (hh : isHook g = false)
    (hp : c₀.isParam g = false) (ho : c₀.isOvl g = false) (hi : σ.lookup i = some a)
    (h : EvalTermR c₀ R σ (.app g [.var i, t]) r) :
    ∃ q, EvalTermR c₀ R σ t q ∧ ((∃ y, q = some y ∧ R g [a, y] r) ∨ (q = none ∧ r = none)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  rcases hts with _ | ⟨e0, _ | ⟨e1, _ | _⟩⟩
  rw [EvalTermR.var_inv_kst e0, hi] at hcase
  refine ⟨_, e1, ?_⟩
  rcases hcase with ⟨vs, hvs, hR⟩ | ⟨hn, hr⟩
  · obtain ⟨y, rfl, rfl⟩ := allSome_s_kst hvs
    exact .inl ⟨y, rfl, hR⟩
  · exact .inr ⟨allSome_s_none_kst hn, hr⟩

/-- A call at one term. -/
theorem EvalTermR.call1t_kst {σ : Subst} {g : Sym} {t : Term} {r : Option GroundTerm}
    (hc : c₀.isCtor g = false) (hh : isHook g = false) (hp : c₀.isParam g = false)
    (ho : c₀.isOvl g = false) (h : EvalTermR c₀ R σ (.app g [t]) r) :
    ∃ q, EvalTermR c₀ R σ t q ∧ ((∃ y, q = some y ∧ R g [y] r) ∨ (q = none ∧ r = none)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  rcases hts with _ | ⟨e0, _ | _⟩
  refine ⟨_, e0, ?_⟩
  rcases hcase with ⟨vs, hvs, hR⟩ | ⟨hn, hr⟩
  · obtain ⟨y, rfl, rfl⟩ := allSome_one_kst hvs
    exact .inl ⟨y, rfl, hR⟩
  · exact .inr ⟨allSome_one_none_kst hn, hr⟩

/-- A call at two terms. -/
theorem EvalTermR.call2tt_kst {σ : Subst} {g : Sym} {t u : Term} {r : Option GroundTerm}
    (hc : c₀.isCtor g = false) (hh : isHook g = false) (hp : c₀.isParam g = false)
    (ho : c₀.isOvl g = false) (h : EvalTermR c₀ R σ (.app g [t, u]) r) :
    ∃ q q', EvalTermR c₀ R σ t q ∧ EvalTermR c₀ R σ u q' ∧
      ((∃ y y', q = some y ∧ q' = some y' ∧ R g [y, y'] r) ∨ ((q = none ∨ q' = none) ∧ r = none)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  rcases hts with _ | ⟨e0, _ | ⟨e1, _ | _⟩⟩
  refine ⟨_, _, e0, e1, ?_⟩
  rcases hcase with ⟨vs, hvs, hR⟩ | ⟨hn, hr⟩
  · obtain ⟨x, y, rfl, rfl, rfl⟩ := allSome_two_kst hvs
    exact .inl ⟨x, y, rfl, rfl, hR⟩
  · exact .inr ⟨allSome_two_none_kst hn, hr⟩

theorem evalPlain_kst : ∀ cl ∈ EvalV.evalDef_kev.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by
  intro cl hcl
  simp only [EvalV.evalDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem evalTsPlain_kst : ∀ cl ∈ EvalV.evalTsDef_kev.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by
  intro cl hcl
  simp only [EvalV.evalTsDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A clause of `eval` whose pattern has another head than the argument does not match it. -/
macro "kst_mismatch" : tactic => `(tactic| first
  | (refine (patCtor_ne_kht ‹PatVal _ _ (.app _ _) _› (emb_ne_kht ?_)).elim; simp [headOf]; done)
  | (refine (patCtor_ne_kht (PatVal.as_inv ‹PatVal _ _ (.as _ _) _›).1 (emb_ne_kht ?_)).elim;
      simp [headOf]; done))

set_option hygiene false in
/-- The 11 clauses of `eval`, each with the two patterns inverted (as `h0`, `h1`). -/
macro "kst_evalCases" hmem:ident hmatch:ident : tactic => `(tactic| (
  simp only [EvalV.evalDef_kev, List.mem_cons, List.not_mem_nil, or_false] at $hmem:ident
  rcases $hmem:ident with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases $hmatch:ident with _ | ⟨h0, _ | ⟨h1, _ | _⟩⟩))

/-- **`ev-app` inverted.** -/
theorem eval_ap_inv_kst {E : D} {f : Int} {qs : List T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.ap f qs)] r) :
    ∃ rs, R 467 [embD E, embTs qs] rs ∧
      ((∃ y, rs = some y ∧ R 448 [embD E, .dv 3 (.int f), y] r) ∨ (rs = none ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_self ..) (σ₀ := enumFrom 0 [embD E, .dv 3 (.int f), embTs qs])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int f) (.cons (embTs_sorted_c₀ qs) .nil))))
    (.cons (.var rfl) (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨hf, _ | ⟨ha, _ | _⟩⟩
  have hd := PatVal.var_inv h0
  have hf := PatVal.var_inv hf
  have ha := PatVal.var_inv ha
  obtain ⟨q, hq, hcase⟩ := EvalTermR.call3_kst notCtor_448 notHook_448 notParam_448
    (by decide +kernel) hd hf hrhs
  exact ⟨q, EvalTermR.call2_kst notCtor_467 notHook_467 notParam_467 (by decide +kernel) hd ha hq, hcase⟩

/-- **`ev-hook` inverted.** -/
theorem eval_hk_inv_kst {E : D} {o : Int} {qs : List T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.hk o qs)] r) :
    ∃ rs, R 467 [embD E, embTs qs] rs ∧
      ((∃ y, rs = some y ∧ R 508 [.dv 3 (.int o), y] r) ∨ (rs = none ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) (σ₀ := enumFrom 0 [embD E, .dv 3 (.int o), embTs qs])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int o) (.cons (embTs_sorted_c₀ qs) .nil))))
    (.cons (.var rfl) (.cons (.ctor ctor_423 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨hf, _ | ⟨ha, _ | _⟩⟩
  have hd := PatVal.var_inv h0
  have hf := PatVal.var_inv hf
  have ha := PatVal.var_inv ha
  obtain ⟨q, hq, hcase⟩ := EvalTermR.call2t_kst notCtor_508 notHook_508 notParam_508
    (by decide +kernel) hf hrhs
  exact ⟨q, EvalTermR.call2_kst notCtor_467 notHook_467 notParam_467 (by decide +kernel) hd ha hq, hcase⟩

/-- **`ev-inj` inverted.** -/
theorem eval_ij_inv_kst {E : D} {a b : Int} {p : T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.ij a b p)] r) :
    ∃ rs, R 464 [embD E, emb p] rs ∧
      ((∃ y, rs = some y ∧ R 493 [.dv 3 (.int a), .dv 3 (.int b), y] r) ∨ (rs = none ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) (σ₀ := enumFrom 0 [embD E, .dv 3 (.int a), .dv 3 (.int b), emb p])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int a) (.cons (sort_int b)
      (.cons (emb_sorted_c₀ p) .nil)))))
    (.cons (.var rfl) (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨ha, _ | ⟨hb', _ | ⟨hp, _ | _⟩⟩⟩
  have hd := PatVal.var_inv h0
  have ha := PatVal.var_inv ha
  have hb' := PatVal.var_inv hb'
  have hp := PatVal.var_inv hp
  obtain ⟨q, hq, hcase⟩ := EvalTermR.call3_kst notCtor_493 notHook_493 notParam_493
    (by decide +kernel) ha hb' hrhs
  exact ⟨q, EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd hp hq, hcase⟩

/-- **`ev-col` inverted.** -/
theorem eval_cb_inv_kst {E : D} {k : Kind} {c : Int} {ps : List T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.cb k c ps)] r) :
    ∃ rs, R 467 [embD E, embTs ps] rs ∧
      ((∃ y, rs = some y ∧ R 459 [embK k, .dv 3 (.int c), y] r) ∨ (rs = none ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (σ₀ := enumFrom 0 [embD E, embK k, .dv 3 (.int c), embTs ps])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embK_sorted_c₀ k) (.cons (sort_int c)
      (.cons (embTs_sorted_c₀ ps) .nil)))))
    (.cons (.var rfl) (.cons (.ctor ctor_414 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨hk, _ | ⟨hc, _ | ⟨hp, _ | _⟩⟩⟩
  have hd := PatVal.var_inv h0
  have hk := PatVal.var_inv hk
  have hc := PatVal.var_inv hc
  have hp := PatVal.var_inv hp
  obtain ⟨q, hq, hcase⟩ := EvalTermR.call3_kst notCtor_459 notHook_459 notParam_459
    (by decide +kernel) hk hc hrhs
  exact ⟨q, EvalTermR.call2_kst notCtor_467 notHook_467 notParam_467 (by decide +kernel) hd hp hq, hcase⟩

/-- **`ev-el` inverted.** -/
theorem eval_el_inv_kst {E : D} {p : T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.el p)] r) :
    ∃ rs, R 464 [embD E, emb p] rs ∧
      ((∃ y, rs = some y ∧ R 492 [y] r) ∨ (rs = none ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (σ₀ := enumFrom 0 [embD E, emb p])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ p) .nil)))
    (.cons (.var rfl) (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨hp, _ | _⟩
  have hd := PatVal.var_inv h0
  have hp := PatVal.var_inv hp
  obtain ⟨q, hq, hcase⟩ := EvalTermR.call1t_kst notCtor_492 notHook_492 notParam_492
    (by decide +kernel) hrhs
  exact ⟨q, EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd hp hq, hcase⟩

/-- **`ev-kv` inverted.** -/
theorem eval_kv_inv_kst {E : D} {a v : T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.kv a v)] r) :
    ∃ ra rv, R 464 [embD E, emb a] ra ∧ R 464 [embD E, emb v] rv ∧
      ((∃ ya yv, ra = some ya ∧ rv = some yv ∧ R 494 [ya, yv] r) ∨ ((ra = none ∨ rv = none) ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))) (σ₀ := enumFrom 0 [embD E, emb a, emb v])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) .nil))))
    (.cons (.var rfl) (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨ha, _ | ⟨hv, _ | _⟩⟩
  have hd := PatVal.var_inv h0
  have ha := PatVal.var_inv ha
  have hv := PatVal.var_inv hv
  obtain ⟨q, q', hq, hq', hcase⟩ := EvalTermR.call2tt_kst notCtor_494 notHook_494 notParam_494
    (by decide +kernel) hrhs
  exact ⟨q, q', EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd ha hq,
    EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd hv hq', hcase⟩

/-- **`ev-en` inverted**: `ensure(eval(D, E), eval(D, T))`. -/
theorem eval_en_inv_kst {E : D} {p e : T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 464 [embD E, emb (.en p e)] r) :
    ∃ re rt, R 464 [embD E, emb e] re ∧ R 464 [embD E, emb p] rt ∧
      ((∃ ye yt, re = some ye ∧ rt = some yt ∧ R 463 [ye, yt] r) ∨ ((re = none ∨ rt = none) ∧ r = none)) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalDef_lookup_kev evalPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (σ₀ := enumFrom 0 [embD E, emb p, emb e])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ p) (.cons (emb_sorted_c₀ e) .nil))))
    (.cons (.var rfl) (.cons (.ctor ctor_420 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
  kst_evalCases hmem hmatch
  all_goals try kst_mismatch
  obtain ⟨xs, he, hxs⟩ := pv_ctor h1
  cases he
  rcases hxs with _ | ⟨hp, _ | ⟨he', _ | _⟩⟩
  have hd := PatVal.var_inv h0
  have hp := PatVal.var_inv hp
  have he' := PatVal.var_inv he'
  obtain ⟨q, q', hq, hq', hcase⟩ := EvalTermR.call2tt_kst notCtor_463 notHook_463 notParam_463
    (by decide +kernel) hrhs
  exact ⟨q, q', EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd he' hq,
    EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd hp hq', hcase⟩

/-- **`evs-nil` inverted.** -/
theorem evalTs_nil_inv_kst {E : D} {r : Option GroundTerm}
    (hb : ByClause c₀ R 467 [embD E, embTs []] r) : r = some (embTs []) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalTsDef_lookup_kev evalTsPlain_kst
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (σ₀ := enumFrom 0 [embD E, embTs []])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ []) .nil)))
    (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil))
  simp only [EvalV.evalTsDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | _⟩⟩
  · exact (patCtor_ne_kht h1 (fun ws h => by cases h)).elim
  · rw [EvalTermR.var_inv_kst hrhs]
    exact (PatVal.as_inv h1).2

/-- **`evs-cons` inverted.** -/
theorem evalTs_cons_inv_kst {E : D} {t : T} {ts : List T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 467 [embD E, embTs (t :: ts)] r) :
    ∃ q q', R 464 [embD E, emb t] q ∧ R 467 [embD E, embTs ts] q' ∧
      r = (allSome [q, q']).map (.ctor 407) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.evalTsDef_lookup_kev evalTsPlain_kst
    (List.mem_cons_self ..) (σ₀ := enumFrom 0 [embD E, emb t, embTs ts])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) .nil))))
    (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
  simp only [EvalV.evalTsDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | _⟩⟩
  · obtain ⟨xs, he, hxs⟩ := pv_ctor h1
    cases he
    rcases hxs with _ | ⟨ht, _ | ⟨hts, _ | _⟩⟩
    have hd := PatVal.var_inv h0
    have ht := PatVal.var_inv ht
    have hts := PatVal.var_inv hts
    obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst ctor_407 hrhs
    rcases hrs with _ | ⟨e0, _ | ⟨e1, _ | _⟩⟩
    exact ⟨_, _, EvalTermR.call2_kst notCtor_464 notHook_464 notParam_464 (by decide +kernel) hd ht e0,
      EvalTermR.call2_kst notCtor_467 notHook_467 notParam_467 (by decide +kernel) hd hts e1, rfl⟩
  · exact (patCtor_ne_kht (PatVal.as_inv h1).1 (fun ws h => by cases h)).elim

end Inv

/-! ## The object side: arguments, sorts and literals -/

section Obj
variable {d : Semantics}

/-- The instances of the arguments, one by one. -/
theorem inst_args_kst {σ : Subst} : ∀ {ts : List Term} {qs ts' : List T},
    encTermsWith d encLit ts = some qs → instTsF qs (bindOfSubst σ) = some ts' →
    Each₂_ksm (fun tm t => Inst d σ tm t) ts ts'
  | [], qs, ts', h, h' => by
    rw [encTerms_nil_kmf d h, instTsF] at h'; cases h'; exact .nil
  | t :: ts, qs, ts', h, h' => by
    obtain ⟨q, qs', h1, h2, rfl⟩ := encTerms_cons_kmf d h
    rw [instTsF] at h'
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact .cons ⟨q, h1, hu⟩ (inst_args_kst h2 hus)

/-- A sorted subterm of a term `σ` gives a meaning is a term `σ` gives a meaning. -/
theorem termOK_of_kst {σ : Subst} {L : List CtorSig} {vars : List Srt} {tm : Term} {s : Srt}
    (hL : HeadsOK (d₀ d) L) (hs : sortOfTerm ((d₀ d).rhsCtx L) vars tm = some s) {is : List Nat}
    (hsub : ∀ i ∈ varOccs tm, i ∈ is) (hw : (d₀ d).WellSortedAt vars is σ)
    (hl : ∀ i ∈ is, ∀ v, σ.lookup i = some v → litsV v = true) : TermOK_ksm d σ tm :=
  ⟨L, vars, s, hL, hs, fun i hi => hw i (hsub i hi), fun i hi => hl i (hsub i hi)⟩

/-- Sorted arguments with their instances are forms `eval` is asked for. -/
theorem args_is_kst {σ : Subst} {L : List CtorSig} {vars : List Srt} (hL : HeadsOK (d₀ d) L)
    {is : List Nat} (hw : (d₀ d).WellSortedAt vars is σ)
    (hl : ∀ i ∈ is, ∀ v, σ.lookup i = some v → litsV v = true) :
    ∀ {ts : List Term} {ss : List Srt} {ts' : List T},
    sortsOfTerms ((d₀ d).rhsCtx L) vars ts = some ss → (∀ i ∈ varOccsList ts, i ∈ is) →
    Each₂_ksm (fun tm t => Inst d σ tm t) ts ts' →
    Each₂_ksm (fun q t => q.Is d σ t) (ts.map EvalForm.term) ts'
  | [], _, _, _, _, h => by cases h; exact .nil
  | t :: ts, ss, _, hs, hsub, .cons hi hrest => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp hs
    refine .cons ⟨termOK_of_kst hL h1 (fun i h => hsub i ?_) hw hl, hi⟩
      (args_is_kst hL hw hl h2 (fun i h => hsub i ?_) hrest)
    · rw [varOccsList]; exact List.mem_append_left _ h
    · rw [varOccsList]; exact List.mem_append_right _ h

/-- What the object semantics gives terms, read back as results. -/
theorem gives_terms_kst {σ : Subst} : ∀ {ts : List Term} {us : List T},
    Each₂_ksm (fun q u => q.Gives d σ u) (ts.map EvalForm.term) us →
    ∃ os, us = os.map encR ∧ EvalTerms (d₀ d) σ ts os
  | [], us, h => by cases h; exact ⟨[], rfl, .nil⟩
  | t :: ts, us, h => by
    cases h with
    | cons h hs =>
      obtain ⟨o, rfl, he⟩ := h
      obtain ⟨os, rfl, hes⟩ := gives_terms_kst hs
      exact ⟨o :: os, rfl, .cons he hes⟩

/-- Each value of sorted arguments has the sort of its position. -/
theorem evalTerms_mem_sorted_kst (hc : SortCtx (d₀ d)) {σ : Subst} {L : List CtorSig}
    {vars : List Srt} (hL : HeadsOK (d₀ d) L) :
    ∀ {ts : List Term} {os : List (Option GroundTerm)} {ss : List Srt},
    EvalTerms (d₀ d) σ ts os → sortsOfTerms ((d₀ d).rhsCtx L) vars ts = some ss →
    (d₀ d).WellSortedAt vars (varOccsList ts) σ →
    ∀ v, some v ∈ os → ∃ s ∈ ss, (d₀ d).sortOf v = some s
  | [], _, _, h, _, _, v, hv => by cases h; cases hv
  | t :: ts, os, ss, h, hs, hw, v, hv => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨s, ss', e1, e2, rfl⟩ := sortsOfTerms_cons.mp hs
      rcases List.mem_cons.mp hv with he | he
      · exact ⟨s, List.mem_cons_self .., Faithful.EvalTerm.sorted_at hc h1 hL
          (fun i hi => hw i (by rw [varOccsList]; exact List.mem_append_left _ hi)) e1 he.symm⟩
      · obtain ⟨s', hm, hs'⟩ := evalTerms_mem_sorted_kst hc hL h2 e2
          (fun i hi => hw i (by rw [varOccsList]; exact List.mem_append_right _ hi)) v he
        exact ⟨s', List.mem_cons_of_mem _ hm, hs'⟩

/-- An argument sort of a function is one `sigSorts` names. -/
theorem sigSorts_fnArg_kst {c : Semantics} {fn : Fn} (hfn : fn ∈ c.allFns) {s : Srt} (hs : s ∈ fn.args) :
    s ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inl (.inl (.inr ⟨fn, hfn, .inr hs⟩)))

/-- `==Bool` is no collection symbol. -/
theorem collSymOf_boolEq_kst : collSymOf d boolEq = none := by
  unfold collSymOf
  rw [if_pos (by decide)]
  decide +kernel

/-- What `execReady` and `encodable` give the proofs below. -/
theorem sortCtx_kst (hr : CExec.execReady d = true) (hc : encodable d = true) : SortCtx (d₀ d) :=
  let ⟨hok, hsr, hov, _⟩ := d₀_facts_kkv hr hc
  sortCtx_of_all hok hsr hov

/-- A value of a sort other than `Float` has kore.k literals. -/
theorem litsV_kst (hr : CExec.execReady d = true) (hc : encodable d = true) {v : GroundTerm} {s : Srt}
    (hv : (d₀ d).sortOf v = some s) (hs : s ≠ Srt.float) : litsV v = true :=
  litsV_of_sorted (d₀_facts_kkv hr hc).2.2.2 hv hs

/-- The argument sorts of the interpreted symbols with an operation code, and of `=/=Bool`, are not
`Float`. -/
theorem hookArgs_float_kst : ((boolNe :: hookCodes.map (·.1)).all fun f =>
    match lookupSig hookSigs f with
    | some k => !k.args.contains Srt.float
    | none => false) = true := by decide +kernel

theorem hookArgs_ne_float_kst {f : Sym} (hf : f ∈ boolNe :: hookCodes.map (·.1)) {k : CtorSig}
    (hk : lookupSig hookSigs f = some k) {s : Srt} (hs : s ∈ k.args) : s ≠ Srt.float := by
  have h := List.all_eq_true.mp hookArgs_float_kst f hf
  simp only [hk] at h
  intro e
  subst e
  simp [hs] at h

/-- C4 at the interpreted symbols kore.k reads as operations: none is a constructor. -/
theorem hookHeads_kst (hc : encodable d = true) {f : Sym} (hf : f ∈ boolNe :: hookCodes.map (·.1)) :
    d.isCtor f = false := by
  simp only [encodable, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  simp only [headsOK, Bool.and_eq_true, List.all_eq_true] at h4
  have h := h4.2 f hf
  cases hct : d.isCtor f
  · rfl
  · simp [hct] at h

/-- A symbol with an operation code is one of `hookCodes`. -/
theorem opOf_heads_kst {f : Sym} {o : Int} (h : opOf f = some o) :
    f ∈ boolNe :: hookCodes.map (·.1) :=
  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(f, o), opOf_mem_khs h, rfl⟩)

theorem lookupSig_ctor_none_kst {c : Semantics} {f : Sym} (hct : c.isCtor f = false) :
    lookupSig c.ctorSigs f = none := by
  cases h : lookupSig c.ctorSigs f with
  | none => rfl
  | some k => simp [Semantics.isCtor, h] at hct

/-- The signature a non-constructor interpreted symbol is found under among the right sides'
heads is its `hookSigs` one. -/
theorem rhs_lookup_hook_kst {c : Semantics} {L : List CtorSig} {f : Sym} {k : CtorSig}
    (hct : c.isCtor f = false) (hh : isHook f = true) (hk : lookupSig (c.rhsCtx L).heads f = some k) :
    lookupSig hookSigs f = some k := by
  obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hh
  simp only [Semantics.rhsCtx, List.append_assoc] at hk
  rw [lookupSig_append_of_none (lookupSig_ctor_none_kst hct), lookupSig_append_of_some hk₀] at hk
  rw [hk₀, hk]

/-- The signature a constructor is found under among the right sides' heads is one of its
constructor signatures. -/
theorem rhs_lookup_ctor_kst {c : Semantics} {L : List CtorSig} {f : Sym} {k : CtorSig}
    (hct : c.isCtor f = true) (hk : lookupSig (c.rhsCtx L).heads f = some k) : k ∈ c.ctorSigs := by
  obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hct
  simp only [Semantics.rhsCtx, List.append_assoc] at hk
  rw [lookupSig_append_of_some hk₀] at hk
  cases hk
  exact (lookupSig_spec hk₀).1

/-- The signature a function (no constructor, hook or parameter) is found under among the right
sides' heads is its own. -/
theorem rhs_lookup_fn_kst {c : Semantics} (hc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L)
    {f : Sym} {k : CtorSig} {fn : Fn} (hct : c.isCtor f = false) (hh : isHook f = false)
    (hp : c.isParam f = false) (hfn : c.lookupFn f = some fn)
    (hk : lookupSig (c.rhsCtx L).heads f = some k) : k = fn.sig := by
  simp only [Semantics.rhsCtx, List.append_assoc] at hk
  rw [lookupSig_append_of_none (lookupSig_ctor_none_kst hct),
    lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hh),
    lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at hk
  obtain ⟨hkL, hkn⟩ := lookupSig_spec (rhs_lookup_fn hc hfn hk)
  obtain ⟨fn', hfn', rfl⟩ := headsOK_preds hL k hkL
  have hlook : c.lookupFn f = some fn' := by
    rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn'
  rw [hlook] at hfn
  cases hfn
  rfl

/-- C4: a constructor labels no function. -/
theorem lookupFn_ctor_kst (hc : encodable d = true) {f : Sym} (hct : d.isCtor f = true) :
    d.lookupFn f = none := by
  cases h : d.lookupFn f with
  | none => rfl
  | some fn =>
    obtain ⟨hm, hl⟩ := lookupFn_spec h
    have := (encodable_heads_kev hc).2 f (List.mem_map.mpr ⟨fn, hm, hl⟩)
    rw [hct] at this; cases this

/-- An interpreted symbol has a value of `hook` at every argument list. -/
theorem hook_isSome_kst {f : Sym} (h : isHook f = true) (vs : List GroundTerm) :
    (hook f vs).isSome = true := by
  unfold isHook hook at *
  cases hf : hookTrie.find f with
  | none => rw [hf] at h; cases h
  | some g => rfl

/-- `hookRes` at `d₀ d` and an interpreted symbol is the value of its result. -/
theorem hookRes_join_kst {f : Sym} (h : isHook f = true) (vs : List GroundTerm) :
    (d₀ d).hookRes f vs = some ((d₀ d).hookRes f vs).join := by
  rw [Semantics.hookRes_withHooks_none]
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hook_isSome_kst h vs)
  rw [hx]; rfl

/-- An application of an interpreted symbol: the arguments' results and what `hookRes` gives them. -/
theorem EvalTerm.hook_inv_kst {c : Semantics} {σ : Subst} {f : Sym} {ts : List Term}
    {r : Option GroundTerm} (hc : c.isCtor f = false) (hh : isHook f = true)
    (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ (∀ vs, allSome rs = some vs → c.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | hook _ _ hts hh' hund => cases ht; exact ⟨_, hts, hh', hund⟩
  | param _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hh] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | ovl _ ho _ => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | ovlFn _ ho => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | _ => cases ht

/-- `mkInj` at the encoding of a result whose value has kore.k literals is the encoding of the
injected result. -/
theorem mkInjF_encR_kst (a b : Srt) {o : Option GroundTerm} (lv : ∀ v, o = some v → litsV v = true) :
    mkInjF a b (encR o) = some (encR (o.map (injNormal a b))) := by
  cases o with
  | none => rfl
  | some v =>
    cases v with
    | inj a' x w => simp only [encR, enc, mkInjF, Option.map_some, injNormal]
    | _ =>
      simp only [encR, Option.map_some, injNormal]
      rw [mkInjF_enc a b rfl (lv _ rfl)]
      simp [enc]

end Obj

/-! ## `eval` at a term's instance -/

section EvalTerm
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts EvalV
variable {d : Semantics} {E : D}

/-- The case of a collection construction: `eval` at the instance of an application of a
collection symbol. -/
def CbStep_kst (d : Semantics) (E : D) : Prop :=
  CExec.execReady d = true → encDef d = some E → ∀ (σ : Subst) (f : Sym) (ts : List Term) (t : T) (r : Option GroundTerm),
    ByClause c₀ (Called d E) 464 [embD E, emb t] r → TermOK_ksm d σ (.app f ts) →
    Inst d σ (.app f ts) t → d.isCtor f = false → (collSymOf d f).isSome = true →
    ∃ o, r = some (emb (encR o)) ∧ EvalTerm (d₀ d) σ (.app f ts) o

/-- `evalTs` at the arguments' instances: the encodings of their results. -/
theorem evalTs_args_kst {σ : Subst} {L : List CtorSig} {vars : List Srt} {ts : List Term}
    {ss : List Srt} {ts' : List T} {rs : Option GroundTerm}
    (hR : Called d E 467 [embD E, embTs ts'] rs) (hL : HeadsOK (d₀ d) L)
    (hs : sortsOfTerms ((d₀ d).rhsCtx L) vars ts = some ss)
    (hw : (d₀ d).WellSortedAt vars (varOccsList ts) σ)
    (hl : ∀ i ∈ varOccsList ts, ∀ v, σ.lookup i = some v → litsV v = true)
    (hi : Each₂_ksm (fun tm t => Inst d σ tm t) ts ts') :
    ∃ os, rs = some (embTs (os.map encR)) ∧ EvalTerms (d₀ d) σ ts os := by
  obtain ⟨us, hus, hg⟩ := (Spec_evalTs d E _ _).mp hR.2 σ (ts.map EvalForm.term) ts' rfl
    (args_is_kst hL hw hl hs (fun _ h => h) hi)
  obtain ⟨os, rfl, hos⟩ := gives_terms_kst hg
  exact ⟨os, hus, hos⟩

/-- The values of sorted arguments at sorts other than `Float` have kore.k literals. -/
theorem args_litsV_kst (hr : CExec.execReady d = true) (hc : encodable d = true) {σ : Subst}
    {L : List CtorSig} {vars : List Srt} (hL : HeadsOK (d₀ d) L) {ts : List Term} {ss : List Srt}
    {os : List (Option GroundTerm)} (hos : EvalTerms (d₀ d) σ ts os)
    (hs : sortsOfTerms ((d₀ d).rhsCtx L) vars ts = some ss)
    (hw : (d₀ d).WellSortedAt vars (varOccsList ts) σ) (hf : ∀ s ∈ ss, s ≠ Srt.float) :
    ∀ v, some v ∈ os → litsV v = true := fun v hv => by
  obtain ⟨s, hm, hsv⟩ := evalTerms_mem_sorted_kst (sortCtx_kst hr hc) hL hos hs hw v hv
  exact litsV_kst hr hc hsv (hf s hm)

/-- **`eval` at a term's instance**, given the case of a collection construction. -/
theorem eval_term_kst (hr : CExec.execReady d = true) (hE : encDef d = some E) (hcb : CbStep_kst d E)
    {σ : Subst} {tm : Term} {t : T} {r : Option GroundTerm}
    (hb : ByClause c₀ (Called d E) 464 [embD E, emb t] r) (hok : TermOK_ksm d σ tm)
    (hi : Inst d σ tm t) : ∃ o, r = some (emb (encR o)) ∧ EvalTerm (d₀ d) σ tm o := by
  have hc : encodable d = true := by rw [← encDef_isSome, hE]; rfl
  have heval : Eval (K₀ sig) 464 [embD E, emb t] r := hb.eval_of_and
  have hok' := hok
  obtain ⟨L, vars, s, hL, hs, hw, hl⟩ := hok
  cases tm with
  | var i =>
    obtain ⟨w, hwi, rfl⟩ := Inst_var_iff_kin.mp hi
    obtain ⟨w', hw', hsw⟩ := hw i (by simp [varOccs]) s (sortOfTerm_var.mp hs)
    rw [hwi] at hw'; cases hw'
    rw [eval_value_iff hE (noRaw_kev hr hE) hsw (hl i (by simp [varOccs]) w hwi)] at heval
    exact ⟨some w, heval, by rw [← hwi]; exact .var⟩
  | dv s' l =>
    obtain ⟨p, hp, ht⟩ := hi
    rw [encTerm_dv_kmf] at hp
    have he := enc_dv_of_encLit hp
    refine ⟨some (.dv s' l), ?_, .dv⟩
    rw [encR, he]
    rcases encLit_some hp with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩
    · rw [instF] at ht; cases ht
      exact (evalF_iff (eval_iv_kev E i)).mp heval
    · rw [instF] at ht; cases ht
      exact (evalF_iff (eval_bv_kev E b)).mp heval
    · rw [instF] at ht; cases ht
      exact (evalF_iff (eval_tk_kev E s' x)).mp heval
  | inj a b tm' =>
    obtain ⟨p, hp, ht⟩ := hi
    rw [encTerm_inj_kmf] at hp
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
    rw [instF] at ht
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨hab, hs', -⟩ := sortOfTerm_inj.mp hs
    have hok1 : TermOK_ksm d σ tm' :=
      termOK_of_kst hL hs' (fun i h => by rw [varOccs]; exact h) hw hl
    obtain ⟨q, hq, hcase⟩ := eval_ij_inv_kst hb
    obtain ⟨o, rfl, ho⟩ := Spec.eval_term hq.2 hok1 ⟨p', hp', ht'⟩
    rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
    · cases hy
      have lv : ∀ v, o = some v → litsV v = true := fun v hv =>
        litsV_kst hr hc (Faithful.EvalTerm.sorted_at (sortCtx_kst hr hc) ho hL
          (fun i h => hw i (by rw [varOccs]; exact h)) hs' hv)
          (fun e => (encodable_facts hc).2.2 (e ▸ sigSorts_sub_kel hab))
      have h1 := (mkInjF.eval_iff a b (encR o)).mp hR.1
      rw [mkInjF_encR_kst a b lv] at h1
      exact ⟨_, h1, .inj ho⟩
    · cases hn
  | as tm' i =>
    obtain ⟨p, hp, ht⟩ := hi
    rw [encTerm_as_kmf] at hp
    obtain ⟨p', -, rfl⟩ := Option.map_eq_some_iff.mp hp
    rw [instF] at ht; cases ht
  | app f ts =>
    obtain ⟨k, hk, hargs, rfl⟩ := sortOfTerm_app.mp hs
    have hw' : (d₀ d).WellSortedAt vars (varOccsList ts) σ := fun i h => hw i (by rw [varOccs]; exact h)
    have hl' : ∀ i ∈ varOccsList ts, ∀ v, σ.lookup i = some v → litsV v = true :=
      fun i h => hl i (by rw [varOccs]; exact h)
    have hsc := sortCtx_kst hr hc
    obtain ⟨p, hp0, ht⟩ := hi
    have hp := hp0
    rw [encTerm_app_kmf] at hp
    unfold readApp at hp
    by_cases hct : d.isCtor f = true
    · -- a constructor: `ap`, evaluated by `apply` as the constructor term
      rw [if_pos hct] at hp
      obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp hp
      rw [instF] at ht
      obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨rs, hrs, hcase⟩ := eval_ap_inv_kst hb
      obtain ⟨os, rfl, hos⟩ := evalTs_args_kst hrs hL hargs hw' hl' (inst_args_kst hqs hts')
      rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
      · cases hy
        have hkc := rhs_lookup_ctor_kst hct hk
        have hlv := args_litsV_kst hr hc hL hos hargs hw' fun s hs e =>
          (encodable_facts hc).2.2 (e ▸ sigSorts_ctor_kel hkc hs)
        obtain ⟨hnone, hsome⟩ := (Spec_apply d E _ _).mp hR.2 f os rfl hlv
        refine ⟨(allSome os).map (.ctor f), ?_, .ctor hct hos⟩
        cases hws : allSome os with
        | none => exact hnone hws
        | some ws =>
          have := (hsome ws hws).1 (lookupFn_ctor_kst hc hct)
          rw [this]; rfl
      · cases hn
    rw [if_neg hct] at hp
    have hct' : d.isCtor f = false := by simpa using hct
    cases hcs : collSymOf d f with
    | some x =>
      -- a collection symbol
      exact hcb hr hE σ f ts t r hb hok' ⟨p, hp0, ht⟩ hct' (by rw [hcs]; rfl)
    | none =>
    rw [hcs] at hp
    dsimp only at hp
    by_cases hh : isHook f = true
    · rw [if_pos hh] at hp
      have hkh := rhs_lookup_hook_kst hct' hh hk
      cases ho : opOf f with
      | some o =>
        -- an interpreted symbol with a code: `hk`, evaluated by `strictHook`
        rw [ho] at hp
        dsimp only at hp
        obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp hp
        rw [instF] at ht
        obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp ht
        obtain ⟨rs, hrs, hcase⟩ := eval_hk_inv_kst hb
        obtain ⟨os, rfl, hos⟩ := evalTs_args_kst hrs hL hargs hw' hl' (inst_args_kst hqs hts')
        rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
        · cases hy
          have hlv := args_litsV_kst hr hc hL hos hargs hw' fun s hs =>
            hookArgs_ne_float_kst (opOf_heads_kst ho) hkh hs
          have hres := (Spec_strictHook d E _ _).mp hR.2 f o os ho rfl hlv fun ws hws =>
            ⟨k, hkh, Faithful.EvalTerms.sorted_at hsc hos hL hw' hargs hws⟩
          refine ⟨_, hres, .hook hct' hh hos (fun ws hws => ?_) (fun hn => by rw [hn]; rfl)⟩
          simp only [hws, Option.bind_some]
          exact hookRes_join_kst hh ws
        · cases hn
      | none =>
        -- `=/=Bool`: `hk 22 [hk 23 As]`, the inner term the instance of `==Bool` at the arguments
        rw [ho] at hp
        dsimp only at hp
        obtain ⟨qs, hqs, hd⟩ := Option.bind_eq_some_iff.mp hp
        unfold derivedHook at hd
        split at hd
        · rename_i hfb
          have hfb : f = boolNe := beq_iff_eq.mp hfb
          subst hfb
          cases hd
          rw [instF] at ht
          obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp ht
          rw [instTsF] at hus
          obtain ⟨x, hx, hus⟩ := Option.bind_eq_some_iff.mp hus
          rw [instTsF] at hus
          obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hus
          cases ha
          rw [instF] at hx
          obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp hx
          have hctE : d.isCtor boolEq = false := hookHeads_kst hc (by decide)
          rw [show lookupSig hookSigs boolNe = some ⟨boolNe, [Srt.bool, Srt.bool], Srt.bool⟩ by
            decide +kernel] at hkh
          cases hkh
          -- the inner term: the application of `==Bool` to the same arguments
          have hsE : sortOfTerm ((d₀ d).rhsCtx L) vars (.app boolEq ts) = some Srt.bool := by
            refine sortOfTerm_app.mpr ⟨⟨boolEq, [Srt.bool, Srt.bool], Srt.bool⟩, ?_, hargs, rfl⟩
            simp only [Semantics.rhsCtx, List.append_assoc]
            rw [lookupSig_append_of_none (lookupSig_ctor_none_kst (c := d₀ d) hctE),
              lookupSig_append_of_some
                (show lookupSig hookSigs boolEq = some ⟨boolEq, [Srt.bool, Srt.bool], Srt.bool⟩ by
                  decide +kernel)]
          have hwE : (d₀ d).WellSortedAt vars (varOccs (.app boolEq ts)) σ :=
            fun i h => hw i (by rw [varOccs] at h ⊢; exact h)
          have hokE : TermOK_ksm d σ (.app boolEq ts) :=
            termOK_of_kst hL hsE (fun i h => by rw [varOccs] at h ⊢; exact h) hw hl
          have hencE : encTerm d (.app boolEq ts) = some (.hk 23 qs) := by
            rw [encTerm_app_kmf]
            unfold readApp
            rw [if_neg (by simp [hctE]), collSymOf_boolEq_kst]
            simp [hqs, show isHook boolEq = true by decide, show opOf boolEq = some 23 by decide]
          obtain ⟨rs, hrs, hcase⟩ := eval_hk_inv_kst hb
          obtain ⟨us, hus, hg⟩ := (Spec_evalTs d E _ _).mp hrs.2 σ [.term (.app boolEq ts)]
            [.hk 23 ts'] rfl (.cons ⟨hokE, ⟨_, hencE, by rw [instF, hts']; rfl⟩⟩ .nil)
          rcases hg with _ | ⟨⟨o1, rfl, ho1⟩, hg'⟩
          cases hg'
          rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
          · rw [hus] at hy; cases hy
            have hs1 : ∀ v, o1 = some v → (d₀ d).sortOf v = some Srt.bool := fun v hv =>
              Faithful.EvalTerm.sorted_at hsc ho1 hL hwE hsE hv
            have hlv1 : ∀ v, some v ∈ [o1] → litsV v = true := fun v hv => by
              rw [List.mem_singleton] at hv
              exact litsV_kst hr hc (hs1 v hv.symm) (by decide)
            have hres := (Spec_strictHook d E _ _).mp hR.2 boolNot 22 [o1] (by decide) rfl hlv1
              (fun ws hws => by
                cases o1 with
                | none => simp [allSome] at hws
                | some v =>
                  simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hws
                  subst hws
                  exact ⟨⟨boolNot, [Srt.bool], Srt.bool⟩, by decide +kernel, sortsOf_cons.mpr ⟨_, _, hs1 v rfl, sortsOf_nil, rfl⟩⟩)
            obtain ⟨rs', hrs', hh1, hund1⟩ := EvalTerm.hook_inv_kst (c := d₀ d) hctE (by decide) ho1
            refine ⟨(allSome rs').bind fun ws => ((d₀ d).hookRes boolNe ws).join, ?_,
              .hook hct' hh hrs' (fun ws hws => ?_) (fun hn => by rw [hn]; rfl)⟩
            · rw [hres]
              cases hws : allSome rs' with
              | none => rw [hund1 hws]; rfl
              | some ws =>
                have e1 := hh1 ws hws
                rw [hookRes_join_kst (d := d) (f := boolEq) (by decide) ws] at e1
                cases e1
                simp only [Semantics.hookRes_withHooks_none, Option.bind_some]
                rw [boolNe_comp]
                cases (hook boolEq ws).join <;> rfl
            · simp only [hws, Option.bind_some]
              exact hookRes_join_kst hh ws
          · rw [hus] at hn; cases hn
        · cases hd
    · rw [if_neg hh] at hp
      have hh' : isHook f = false := by simpa using hh
      by_cases hpar : d.isParam f = true
      · rw [if_pos hpar] at hp; cases hp
      rw [if_neg hpar] at hp
      have hpar' : d.isParam f = false := by simpa using hpar
      by_cases hfn : (d.lookupFn f).isSome = true
      · -- a function: `ap`, evaluated by `apply` as a call of the function
        rw [if_pos hfn] at hp
        obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp hfn
        have hkf := rhs_lookup_fn_kst hsc hL hct' hh' hpar' hfn hk
        subst hkf
        obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp hp
        rw [instF] at ht
        obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp ht
        obtain ⟨rs, hrs, hcase⟩ := eval_ap_inv_kst hb
        obtain ⟨os, rfl, hos⟩ := evalTs_args_kst hrs hL hargs hw' hl' (inst_args_kst hqs hts')
        rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
        · cases hy
          have hmf := (lookupFn_spec hfn).1
          have hlv := args_litsV_kst hr hc hL hos hargs hw' fun s hs e =>
            (encodable_facts hc).2.2 (e ▸ sigSorts_fnArg_kst hmf hs)
          obtain ⟨hnone, hsome⟩ := (Spec_apply d E _ _).mp hR.2 f os rfl hlv
          cases hws : allSome os with
          | none => exact ⟨none, hnone hws, .callUndef hct' hh' hos hws hpar'⟩
          | some ws =>
            obtain ⟨o, hro, hev⟩ := (hsome ws hws).2 fn hfn
              (Faithful.EvalTerms.sorted_at hsc hos hL hw' hargs hws)
            exact ⟨o, hro, .call hct' hh' hos hws hev hpar'⟩
        · cases hn
      · rw [if_neg hfn] at hp; cases hp

/-! ## The step cases -/

/-- `hasBot` at the encodings of results one of which has no value. -/
theorem hasBotF_of_none_kst : ∀ {os : List (Option GroundTerm)}, allSome os = none →
    hasBotF (os.map encR) = true
  | [], h => by simp [allSome] at h
  | none :: os, _ => by simp [hasBotF, encR]
  | some v :: os, h => by
    simp only [allSome, Option.bind_some, Option.map_eq_none_iff] at h
    simp only [List.map_cons, hasBotF, hasBotF_of_none_kst h, Bool.or_true]

/-- **The step case at `eval`**, given the case of a collection construction. -/
theorem stepCase_eval_of_kst (hcb : CbStep_kst d E) : StepCase d E 464 := fun hr hE vs r hb =>
  (Spec_eval d E vs r).mpr fun σ q t hvs hq => by
    subst hvs
    cases q with
    | term tm =>
      obtain ⟨hok, hi⟩ := hq
      obtain ⟨o, hro, ho⟩ := eval_term_kst hr hE hcb hb hok hi
      exact ⟨encR o, hro, o, rfl, ho⟩
    | el x =>
      obtain ⟨hok, p, hi, rfl⟩ := hq
      obtain ⟨rs, hrs, hcase⟩ := eval_el_inv_kst hb
      obtain ⟨o, rfl, ho⟩ := Spec.eval_term hrs.2 hok hi
      rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
      · cases hy
        have h1 := (Gen.mkElF.eval_iff (encR o)).mp hR.1
        refine ⟨mkElV_ksm (encR o), ?_, o, rfl, ho⟩
        rw [h1]
        cases encR o <;> rfl
      · cases hn
    | kv a v =>
      obtain ⟨hoka, hokv, p, q, hp, hq, rfl⟩ := hq
      obtain ⟨ra, rv, hra, hrv, hcase⟩ := eval_kv_inv_kst hb
      obtain ⟨oa, rfl, hoa⟩ := Spec.eval_term hra.2 hoka hp
      obtain ⟨ov, rfl, hov⟩ := Spec.eval_term hrv.2 hokv hq
      rcases hcase with ⟨ya, yv, hya, hyv, hR⟩ | ⟨hn | hn, -⟩
      · cases hya; cases hyv
        exact ⟨_, (mkKvF.eval_iff (encR oa) (encR ov)).mp hR.1, oa, ov, rfl, hoa, hov⟩
      · cases hn
      · cases hn
    | en rhs e =>
      obtain ⟨hokr, hoke, p, q, hp, hq, rfl⟩ := hq
      obtain ⟨re, rt, hre, hrt, hcase⟩ := eval_en_inv_kst hb
      obtain ⟨w, rfl, hw⟩ := Spec.eval_term hre.2 hoke hq
      obtain ⟨o, rfl, ho⟩ := Spec.eval_term hrt.2 hokr hp
      rcases hcase with ⟨ye, yt, hye, hyt, hR⟩ | ⟨hn | hn, -⟩
      · cases hye; cases hyt
        exact ⟨_, (ensureF.eval_iff (encR w) (encR o)).mp hR.1, o, w, rfl, ho, hw⟩
      · cases hn
      · cases hn

/-- **The step case at `evalTs`.** -/
theorem stepCase_evalTs_kst : StepCase d E 467 := fun _ _ vs r hb =>
  (Spec_evalTs d E vs r).mpr fun σ qs ts hvs hqs => by
    subst hvs
    cases hqs with
    | nil => exact ⟨[], evalTs_nil_inv_kst hb, .nil⟩
    | cons hq hqs' =>
      rename_i q t qs' ts'
      obtain ⟨r1, r2, h1, h2, rfl⟩ := evalTs_cons_inv_kst hb
      obtain ⟨u, rfl, hu⟩ := (Spec_eval d E _ _).mp h1.2 σ q t rfl hq
      obtain ⟨us, rfl, hus⟩ := (Spec_evalTs d E _ _).mp h2.2 σ qs' ts' rfl hqs'
      exact ⟨u :: us, rfl, .cons hu hus⟩

/-- **The step case at `strictHook`.** -/
theorem stepCase_strictHook_kst : StepCase d E 508 := fun _ _ vs r hb =>
  (Spec_strictHook d E vs r).mpr fun f o os hfo hvs hl hs => by
    subst hvs
    have he : Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (os.map encR)] r := hb.eval_of_and
    cases hws : allSome os with
    | none =>
      have hbot := hasBotF_of_none_kst hws
      have h1 := strictHook_eval_khs o (os.map encR) (r := .bot) (fun h => by rw [hbot] at h; cases h)
      rw [strictT_of_khs (fun _ => rfl)] at h1
      rw [(evalF_iff h1).mp he]; rfl
    | some ws =>
      have hos := allSome_eq_map hws
      subst hos
      have henc : (ws.map some).map encR = encTs ws := by
        rw [List.map_map, encTs_eq_map]; rfl
      rw [henc] at he
      have hl' : ∀ v ∈ ws, litsV v = true := fun v hv => hl v (List.mem_map_of_mem hv)
      obtain ⟨k, hk, hsk⟩ := hs ws hws
      have hsa : SortedArgs_khs (d₀ d) f ws := ⟨k, hk, hsk⟩
      have hev : Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs ws)]
          (some (emb (encR ((d₀ d).hookRes f ws).join))) := by
        by_cases hco : o < 40 ∨ 70 ≤ o
        · exact hooks_scalar hfo hco ws (fun _ => hsa) (fun _ => hl')
        · exact hooks_coll hfo (by omega) ws hsa hl'
      rw [(evalF_iff hev).mp he]; rfl

/-- **The step cases of the terms**: `eval`, `evalTs`, `ensure` and `strictHook`, given the case of a
collection construction (`CbStep_kst`). -/
theorem stepCases_terms_kst (hcb : CbStep_kst d E) :
    StepCase d E 464 ∧ StepCase d E 467 ∧ StepCase d E 463 ∧ StepCase d E 508 :=
  ⟨stepCase_eval_of_kst hcb, stepCase_evalTs_kst, stepCase_ensure d E, stepCase_strictHook_kst⟩

end EvalTerm


/-! ## Instances -/

section Instances
open _root_.KK EvalV

/-- `evs-nil` at an evaluation of kore.k: `evalTs(D, .Ts)` is `.Ts`. -/
example (E : D) : some (embTs []) = some (embTs []) :=
  evalTs_nil_inv_kst (R := Eval c₀) (Eval.byClause_iff.mp (evalTs_kev E [] (fun _ h => nomatch h)))

/-- `ev-inj` at an evaluation of kore.k: `eval(D, ij(3, 1, iv(7)))` calls `eval(D, iv(7))`. -/
example (E : D) : ∃ rs, Eval c₀ 464 [embD E, emb (.iv 7)] rs ∧
    ((∃ y, rs = some y ∧ Eval c₀ 493 [.dv 3 (.int 3), .dv 3 (.int 1), y] (some (emb (.ij 3 1 (.iv 7))))) ∨
      (rs = none ∧ some (emb (.ij 3 1 (.iv 7))) = none)) :=
  eval_ij_inv_kst (R := Eval c₀) (Eval.byClause_iff.mp (eval_ij_kev E 3 1 (eval_iv_kev E 7) rfl))

end Instances

/-! ## Checks -/

#check @byClause_plain_kst
#check @eval_term_kst
#check @stepCase_eval_of_kst
#check @stepCase_evalTs_kst
#check @stepCase_strictHook_kst
#check @stepCases_terms_kst

open Lean in
#eval show CoreM Unit from do
  for n in [``byClause_plain_kst, ``eval_ap_inv_kst, ``eval_hk_inv_kst, ``eval_ij_inv_kst,
      ``eval_cb_inv_kst, ``eval_el_inv_kst, ``eval_kv_inv_kst, ``eval_en_inv_kst,
      ``evalTs_nil_inv_kst, ``evalTs_cons_inv_kst, ``eval_term_kst, ``stepCase_eval_of_kst,
      ``stepCase_evalTs_kst, ``stepCase_strictHook_kst, ``stepCases_terms_kst] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
