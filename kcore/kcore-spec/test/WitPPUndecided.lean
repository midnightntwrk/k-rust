/-
  The witness of findings/R3-consistent-pp-shape-decision.md section 3.2: the hypotheses of the pinned `consistent_of` (`coreOK`, `FnDet`,
  `FnSolves`, `ClausePreDecided`, `OpenLaws`) do not give a condition over a function call a truth value under `Holds`.
  Run from the package root: `lake env lean -j1 test/WitPPUndecided.lean`.

  `c₀` is `FnSolvesWitness.c` with the one equation `f(X) => f(X)` (`f : Int → Int`) in place of its
  two, and no rule. Kernel-checked here:
  - `coreOK`: `c₀.coreOK = true` (by decision);
  - `f_none`: `f` has no `Eval` result at an Int: every derivation of `f(w)` holds one of `f(w)` in
    the clause's right-hand side, and `Eval.rest` asks the clause to fail at `[w]`, which at the
    well-sorted σ `[(0, w)]` asks a `requires` the clause does not have. The sort hypothesis is
    needed: at an argument that is no Int no σ is well sorted, the clause fails vacuously and
    `Eval.rest` gives the rest (`rest_illSorted`, at the Bool `true`);
  - `fnDet`, `fnSolves` (`fnSolves'` for any rule list), `openLaws`; `not_fnHyp` (`FnHyp`'s first
    conjunct fails: `f(0)` has no result, so `c₀` is outside the hypotheses of the theorems that read `FnHyp`);
  - `p := ¬⌈f(0)⌉` has `condOK` and `Cond.bound` (`p_ok`) and no `Holds` derivation at any σ and
    any number of variables in scope (`p_undecided`).
  `Eval`, `EvalTerm` and `Holds` do not read the rules: `f_none'` and `p_undecided'` state the same of
  `cR rs`, `c₀` with any rule list `rs`.

  The rule-bearing part: `c₁`, `c₀` with one closed rule from `x₀` to `x₀` whose `pre` is `p`.
  `rulesPlain` does not ask a rule's `pre` and `post` to be `⊤`, so `c₁` has `rulesPlain` and
  `coreOK` (`c₁_rulesPlain`, `c₁_coreOK`), and its rule's `pre` has no `Holds` derivation
  (`c₁_undecided`): under `coreOK` a rule's predicate need not have a truth value. `c₁` meets the
  hypotheses of the pinned `consistent_of` (`c₁_coreOK`, `c₁_fnDet`, `c₁_fnSolves`,
  `c₁_openLaws`, and `ClausePreDecided`, its clauses' predicates being `⊤`), so `Consistent c₁` (`c₁_consistent`), at that theorem's pinned type. `c₁` has no
  `Step` and no `StepM` step at all (`c₁_no_step`, `c₁_no_stepM`): both ask `Holds … pre true`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.WitPPUndecided

open FnSolvesWitness (F)
open Faithful.UndefRhsWitness (kIds)

/-- `f(X) => f(X)`. -/
def cl : Clause := ⟨[Srt.int], [.var 0], none, .app F [.var 0], none, 50, false, [], .top, .top⟩

def fF : Fn := ⟨F, [Srt.int], Srt.int, [cl], false⟩

/-- `c₀` with the rules `rs`. -/
def cR (rs : List Rule) : Semantics := { FnSolvesWitness.c with fns := [fF], rules := rs }

/-- The rule-free definition. -/
def c₀ : Semantics := cR []

/-- `¬⌈f(0)⌉`. -/
def p : Cond := .not (.ceil Srt.int (.app F [.dv Srt.int (.int 0)]))

def i0 : GroundTerm := .dv Srt.int (.int 0)

theorem coreOK : c₀.coreOK = true := by decide_cheap

section AnyRules

variable (rs : List Rule)

theorem lookupF : (cR rs).lookupFn F = some fF := rfl
theorem isCtorF : (cR rs).isCtor F = false := rfl
theorem isHookF : isHook F = false := by decide +kernel
theorem isParamF : (cR rs).isParam F = false := rfl
theorem isOvlF : (cR rs).isOvl F = false := rfl

theorem i0_int : (cR rs).sortOf i0 = some Srt.int := rfl

/-- `f` has no result at an Int, whatever the rules. -/
theorem f_none' {w : GroundTerm} (hw : (cR rs).sortOf w = some Srt.int) {res : Option GroundTerm} :
    ¬ Eval (cR rs) F [w] res := by
  intro hv
  exact Eval.rec (c := cR rs)
    (motive_1 := fun f vs _ _ => f = F → ∀ w, vs = [w] → (cR rs).sortOf w = some Srt.int → False)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun σ t _ _ => t = .app F [.var 0] →
      ∀ w, σ.lookup 0 = some w → (cR rs).sortOf w = some Srt.int → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True) (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ cl' _ _} hfn hmem _ hmatch _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf w hvs hw => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      cases hmatch with
      | cons h1 _ => cases h1 with | var hl => exact ihrhs rfl w hl hw)
    (fun hfn hnone _ => fun hf w hvs hw => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      obtain ⟨h⟩ := hnone cl (by simp [fF])
      have hσ : (cR rs).WellSortedAt cl.vars cl.leftVars [(0, w)] := fun i _ s hi => by
        match i, hi with
        | 0, hi => simp only [cl, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨w, rfl, hw⟩
        | _ + 1, hi => simp [cl] at hi
      cases h [(0, w)] hσ (.cons (.var rfl) .nil) with
      | intro ht _ _ => simp [cl] at ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp))
    (fun {_ _ _ cl' _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf w hvs _ => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      simp [cl] at ht)
    (fun {_ _ _ cl' _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf w hvs _ => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact hne rfl)
    (fun {_ _ _ cl' _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf w hvs _ => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact hne rfl)
    (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ => trivial)
    (fun h => by cases h)
    (fun h => by cases h)
    (fun _ _ h => by cases h)
    (fun hk _ _ h => by cases h; exact absurd hk (by rw [isCtorF]; decide))
    (fun _ hhk _ _ _ _ h => by cases h; exact absurd hhk (by rw [isHookF]; decide))
    (fun _ _ hp _ _ _ h => by cases h; exact absurd hp (by rw [isParamF]; decide))
    (fun _ _ hts hvs _ _ _ ihf => fun h w hl hw => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [hl] at hvs
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        exact ihf rfl w hvs.symm hw)
    (fun _ _ hts hvs _ _ => fun h w hl _ => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [hl] at hvs
        simp [allSome] at hvs)
    (fun _ ho _ _ _ h => by cases h; exact absurd ho (by rw [isOvlF]; decide))
    (fun _ ho _ _ _ _ _ _ _ h => by cases h; exact absurd ho (by rw [isOvlF]; decide))
    trivial
    (fun _ _ _ _ => trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    hv rfl w rfl hw

/-- `f(t)` has no result where `t` has the one result `w`, an Int. -/
theorem appF_none' {σ : Subst} {t : Term} {w : GroundTerm} (ht : ∀ r, EvalTerm (cR rs) σ t r → r = some w)
    (hw : (cR rs).sortOf w = some Srt.int) {r : Option GroundTerm} : ¬ EvalTerm (cR rs) σ (.app F [t]) r := by
  intro h
  cases h with
  | ctor hk _ => exact absurd hk (by rw [isCtorF]; decide)
  | hook _ hhk _ _ _ => exact absurd hhk (by rw [isHookF]; decide)
  | param _ _ hp _ _ => exact absurd hp (by rw [isParamF]; decide)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 h2 =>
      cases h2
      rw [ht _ h1] at hvs
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      exact f_none' rs hw hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 h2 => cases h2; rw [ht _ h1] at hvs; simp [allSome] at hvs
  | ovl _ ho _ => exact absurd ho (by rw [isOvlF]; decide)
  | ovlFn _ ho => exact absurd ho (by rw [isOvlF]; decide)

/-- `¬⌈f(0)⌉` has no truth value, whatever the rules. -/
theorem p_undecided' : ∀ n σ b, ¬ Holds (cR rs) n σ p b := by
  intro n σ b h
  cases h with
  | not h =>
    cases h with
    | ceil h => exact appF_none' rs (fun r h => by cases h; rfl) (i0_int rs) h

/-- **`FnSolves`**, whatever the rules: at an argument of `f`'s sort both sides are false
(`f_none'`; the right-hand side is `f(X)` at the argument). -/
theorem fnSolves' : FnSolves (cR rs) := by
  intro fn hfn vs _ cl' hcl' σ hdec v
  simp only [cR, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst hfn
  simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hcl'
  subst hcl'
  refine Iff.trans ?_ (Clause.gives_iff_noExs rfl rfl ((wellSortedAt_univ rfl).mp hdec.1.1) v).symm
  obtain ⟨⟨hσ, hm, _, _⟩, _⟩ := hdec
  cases hm with
  | cons h1 h2 =>
    cases h2
    cases h1 with
    | var hl =>
      rename_i w
      obtain ⟨w', hw', hs⟩ := (wellSortedAt_univ rfl).mp hσ 0 Srt.int rfl
      rw [hl] at hw'; cases hw'
      exact ⟨fun h => absurd h (f_none' rs hs),
        fun ⟨h, _⟩ => absurd h (appF_none' rs (fun r h => by cases h; exact hl) hs)⟩

end AnyRules

theorem f_none {w : GroundTerm} (hw : c₀.sortOf w = some Srt.int) {res : Option GroundTerm} :
    ¬ Eval c₀ F [w] res := f_none' [] hw

/-- At an argument that is no Int the clause fails vacuously and `Eval.rest` gives a result. -/
theorem rest_illSorted : Eval c₀ F [bool true] (c₀.fnRest fF [bool true]) :=
  .rest (lookupF []) fun cl' hcl' => by
    simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hcl'
    subst hcl'
    refine ⟨fun σ hσ hm => ?_⟩
    cases hm with
    | cons h1 _ =>
      cases h1 with
      | var hl =>
        obtain ⟨v, hv, hs⟩ := hσ 0 (by simp [Clause.leftVars, cl, varOccsList, varOccs]) Srt.int rfl
        rw [hl] at hv; cases hv
        exact absurd hs (by decide +kernel)

/-- **`FnDet`**: the deciders confirm coherence, as for `FnSolvesWitness.c`. -/
theorem fnDet : FnDet c₀ := by
  have hok : c₀.sortedOK = true := by decide +kernel
  have hsr : c₀.srReady = true := by decide +kernel
  have hmr : c₀.matchReady = true := by decide +kernel
  have hag : c₀.agreeObligations = [] := by decide +kernel
  have hcf : c₀.clausesFixed = true := by decide +kernel
  refine fnDet_of_coherent (coherentAll_of_parts
    (matchIndependentAll_of_sortedOK hok hmr (.of_fixed hcf (Exec.matchCtx_of hmr).noOvl)) fun f fn hfn => ?_)
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK hok hsr hmr (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

/-- **`FnSolves`**. -/
theorem fnSolves : FnSolves c₀ := fnSolves' []

theorem openLaws : OpenLaws c₀ := openLaws_of_plain (by decide +kernel)

/-- `c₀` is outside `FnHyp`: `f(0)` has no result. -/
theorem not_fnHyp : ¬ FnHyp c₀ := fun h => by
  obtain ⟨r, hr⟩ := h.1 fF (by simp [c₀, cR]) [i0] (by decide +kernel)
  exact f_none (i0_int []) hr

theorem p_ok : c₀.condOK [] p = true ∧ Cond.bound c₀ 0 p = true := by decide +kernel

theorem p_undecided : ∀ n σ b, ¬ Holds c₀ n σ p b := p_undecided' []

/-! ## The rule-bearing definition, today -/

/-- The closed configuration `<k> .K </k> <generatedCounter> 0 </generatedCounter>`. -/
def x₀ : Term := .app topLabel [.app kIds.label [.app dotk []], .app counterLabel [.dv Srt.int (.int 0)]]

/-- A rule without variables from `x₀` to `x₀` whose `pre` is `p`. -/
def r : Rule := { vars := [], lhs := x₀, req := none, rhs := x₀, ens := none, prio := 50, pre := p }

def c₁ : Semantics := cR [r]

/-- `rulesPlain` accepts `c₁` (its rule's `pre` is not `⊤`), the rule is well sorted, and `c₁` has
`coreOK`. -/
theorem c₁_rulesPlain : c₁.rulesPlain = true := by decide +kernel
theorem c₁_ruleSorted : c₁.rules.all c₁.ruleSorted = true := by decide +kernel
theorem c₁_coreOK : c₁.coreOK = true := by decide_cheap

theorem c₁_undecided : ∀ n σ b, ¬ Holds c₁ n σ r.pre b := p_undecided' [r]

/-- **`FnDet`** of `c₁`: the deciders confirm coherence, as for `c₀`. -/
theorem c₁_fnDet : FnDet c₁ := by
  have hok : c₁.sortedOK = true := by decide +kernel
  have hsr : c₁.srReady = true := by decide +kernel
  have hmr : c₁.matchReady = true := by decide +kernel
  have hag : c₁.agreeObligations = [] := by decide +kernel
  have hcf : c₁.clausesFixed = true := by decide +kernel
  refine fnDet_of_coherent (coherentAll_of_parts
    (matchIndependentAll_of_sortedOK hok hmr (.of_fixed hcf (Exec.matchCtx_of hmr).noOvl)) fun f fn hfn => ?_)
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK hok hsr hmr (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

theorem c₁_fnSolves : FnSolves c₁ := fnSolves' [r]

theorem c₁_openLaws : OpenLaws c₁ := openLaws_of_plain (by decide +kernel)

/-- **`Consistent c₁`**, by the pinned `consistent_of` at its hypotheses: the rule's `pre` has no
truth value under `Holds`, and `Γc` with the step's closure has a model nevertheless. -/
theorem c₁_consistent : Consistent c₁ := consistent_of c₁ c₁_coreOK c₁_fnDet c₁_fnSolves
  (clausePreDecided_of_isTop (by decide +kernel)) c₁_openLaws

/-- **No `Step` of `c₁`**: its one rule asks `Holds … pre true`. -/
theorem c₁_no_step (x y : Config c₁) : ¬ Step c₁ x y := by
  intro h
  cases h with
  | rule r' mem _ _ _ _ hpre _ _ _ _ =>
    simp only [c₁, cR, List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    exact c₁_undecided _ _ _ hpre

/-- **No `StepM` step of `c₁`**, for the same reason. -/
theorem c₁_no_stepM (x y : GroundTerm) : ¬ Faithful.Model.StepM c₁ x y := by
  rintro ⟨r', mem, σ, -, -, -, hpre, -⟩
  simp only [c₁, cR, List.mem_cons, List.not_mem_nil, or_false] at mem
  subst mem
  exact c₁_undecided _ _ _ hpre

/-- info: 'KCore.WitPPUndecided.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coreOK

/-- info: 'KCore.WitPPUndecided.fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnDet

/-- info: 'KCore.WitPPUndecided.fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSolves

/-- info: 'KCore.WitPPUndecided.p_undecided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p_undecided

/-- info: 'KCore.WitPPUndecided.not_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_fnHyp

/-- info: 'KCore.WitPPUndecided.c₁_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c₁_coreOK

/-- info: 'KCore.WitPPUndecided.c₁_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c₁_fnDet

/-- info: 'KCore.WitPPUndecided.c₁_fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c₁_fnSolves

/-- info: 'KCore.WitPPUndecided.c₁_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c₁_consistent

/-- info: 'KCore.WitPPUndecided.c₁_no_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c₁_no_step

/-- info: 'KCore.WitPPUndecided.c₁_no_stepM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c₁_no_stepM

end KCore.WitPPUndecided
