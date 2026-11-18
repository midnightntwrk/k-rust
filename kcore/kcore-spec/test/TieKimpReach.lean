/-
  Row imp: kimp's semantics has no point where every clause of a function fails, and its rules and
  equations apply no symbol with a silent point, kernel-checked on the generated package's
  semantics `RefKimp.defn.sem` (`examples/ref-kimp/RefKimp/definition.kore`), for every
  interpretation H. So the interpretation's choices in Γ (`ΓFallback`) are never reached by a term
  the text writes: the function-rest premises are empty, and the hooked symbols' silent points are
  points of symbols no rule or equation applies.
  Run from the package root with the package built (test/imp-tie-atvalues.sh does both).

  - `fns_catchAll`: each of the semantics' 20 functions (the sort predicates; `c.fns` is empty)
    has a clause whose one pattern is a variable of the argument's sort, with no `requires` and
    the predicate `\top`.
  - `not_fails_catchAll`: such a clause does not fail at any argument of that sort, under any
    semantics.
  - `no_rest`: at every argument list of a function's argument sorts some clause does not fail,
    for every H; so every premise of `ΓFallback (cH H)` is at a silent point of an interpreted
    symbol (`no_rest_premise`).
  - `conds_top`: every rule's and every clause's predicates `pre` and `post` are `\top`;
    `silent_unapplied`: no symbol applied by a term of a rule (sides, `requires`, `ensures`) or of
    a function's clause (patterns, right side, `requires`, `ensures`) has a key of `silentTable`.
-/
import RefKimp.Sound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimpReach

open KCore

noncomputable abbrev c : Semantics := RefKimp.defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-! ## No failing clause -/

/-- The term is the variable 0. -/
def isVar0T : Term → Bool
  | .var 0 => true
  | _ => false

theorem isVar0T_eq {p : Term} (h : isVar0T p = true) : p = .var 0 := by
  cases p with
  | var i => cases i with
    | zero => rfl
    | succ => simp [isVar0T] at h
  | _ => simp [isVar0T] at h

theorem isTop_eqK {p : Cond} (h : p.isTop = true) : p = .top := by
  cases p <;> simp [Cond.isTop] at h ⊢

/-- The clause of `fn` binds its one argument to a variable of the argument's sort, with no
`requires` and the predicate `\top`. -/
def catchAll (fn : Fn) (cl : Clause) : Bool :=
  (match cl.pats with
    | [p] => isVar0T p
    | _ => false) &&
  decide (cl.vars = fn.args) && fn.args.length == 1 && cl.req.isNone && cl.pre.isTop

/-- **A clause of that form does not fail** at an argument of the function's sort. -/
theorem not_fails_catchAll {c' : Semantics} {fn : Fn} {cl : Clause} (h : catchAll fn cl = true)
    {vs : List GroundTerm} (hvs : c'.sortsOf vs = some fn.args) : ¬ Fails c' vs cl := by
  simp only [catchAll, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨hp, hv⟩, hl⟩, hr⟩, hpre⟩ := h
  have hpats : cl.pats = [.var 0] := by
    revert hp; cases hpc : cl.pats with
    | nil => simp
    | cons p ps => cases ps with
      | nil => intro hp; exact congrArg (· :: []) (isVar0T_eq hp)
      | cons => simp
  have hpre' := isTop_eqK hpre
  obtain ⟨s, hs⟩ : ∃ s, fn.args = [s] := by
    match hfa : fn.args, hl with
    | [s], _ => exact ⟨s, rfl⟩
  rw [hs] at hvs
  obtain ⟨v, rfl, hsv⟩ : ∃ v, vs = [v] ∧ c'.sortOf v = some s := by
    match vs, hvs with
    | v :: ws, hvs =>
      obtain ⟨h1, h2⟩ := OvlLaws.sortsOf_cons_iff.mp hvs
      exact ⟨v, by rw [KCore.Faithful.sortsOf_nil_eq h2], h1⟩
  intro hf
  cases hf with
  | intro hall =>
    have hσ : c'.WellSortedAt cl.vars cl.leftVars [(0, v)] := by
      intro i _ s' hi
      rw [hv, hs] at hi
      match i, hi with
      | 0, hi => exact ⟨v, rfl, by cases hi; exact hsv⟩
    have hm : PatVals c' [(0, v)] cl.pats [v] := by
      rw [hpats]; exact .cons (.var rfl) .nil
    cases hall _ hσ hm with
    | intro ht _ _ => rw [hr] at ht; cases ht
    | pre hh => rw [hpre'] at hh; cases hh

/-- **Every function has such a clause.** -/
theorem fns_catchAll : c.allFns.all (fun fn => fn.clauses.any (catchAll fn)) = true := by decide +kernel

theorem fns_count : c.fns = [] ∧ c.allFns.length = 20 := ⟨by decide +kernel, by decide +kernel⟩

kernel_rfl allFns_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).allFns = c.allFns

/-- **No point where every clause fails**, for every H: at every argument list of a function's
argument sorts, some clause of the function does not fail. -/
theorem no_rest (H : HookParams) : ∀ fn ∈ (cH H).allFns, ∀ vs, (cH H).sortsOf vs = some fn.args →
    ∃ cl ∈ fn.clauses, ¬ Fails (cH H) vs cl := by
  intro fn hfn vs hvs
  rw [allFns_withHooks] at hfn
  obtain ⟨cl, hcl, hca⟩ := List.any_eq_true.mp (List.all_eq_true.mp fns_catchAll fn hfn)
  exact ⟨cl, hcl, not_fails_catchAll hca hvs⟩

/-- **Every premise the interpretation decides is at a silent point of an interpreted symbol**:
the function-rest part of `ΓFallback (cH H)` is empty, for every H. -/
theorem no_rest_premise (H : HookParams) : ∀ φ, Faithful.ΓFallback (cH H) φ →
    ∃ (k : CtorSig) (vs : List GroundTerm), k ∈ hookSigs ∧ silent k.name vs = true := by
  intro φ h
  rcases h with ⟨k, vs, hk, -, -, hs, -⟩ | ⟨fn, vs, hfn, hvs, hall, -⟩
  · exact ⟨k, vs, hk, hs⟩
  · obtain ⟨cl, hcl, hn⟩ := no_rest H fn hfn vs hvs
    exact absurd (hall cl hcl) hn

/-! ## No silent point applied -/

/-- The terms of the sort predicates' clauses: patterns, right sides, `requires`, `ensures`. -/
noncomputable def predTerms : List Term :=
  c.sortPreds.flatMap fun f => f.clauses.flatMap fun cl => cl.pats ++ [cl.rhs] ++ cl.req.toList ++ cl.ens.toList

/-- Every rule's and every clause's predicates are `\top`: no condition holds a term. -/
theorem conds_top : (c.rules.all fun r => r.pre.isTop && r.post.isTop) = true ∧
    (c.allFns.all fun f => f.clauses.all fun cl => cl.pre.isTop && cl.post.isTop) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **No term of a rule or of a function's clause applies a symbol with a key of
`silentTable`** (`c.terms` holds the rules' and the user functions' terms, `predTerms` the sort
predicates'). -/
theorem silent_unapplied : (Term.symsList (c.terms ++ predTerms)).all (fun f => !silentKey f) = true := by
  decide +kernel

end KCore.TieKimpReach

/-- info: 'KCore.TieKimpReach.no_rest_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpReach.no_rest_premise
/-- info: 'KCore.TieKimpReach.silent_unapplied' does not depend on any axioms -/
#guard_msgs in #print axioms KCore.TieKimpReach.silent_unapplied
/-- info: 'KCore.TieKimpReach.conds_top' depends on axioms: [propext] -/
#guard_msgs in #print axioms KCore.TieKimpReach.conds_top
