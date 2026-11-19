/-
  The fixture e2-clause-genless-arg: `syntax S ::= "a" | c(Empty)` (`syntax Empty`, no production),
  `isC(S)` total with `isC(c(_)) => true` and `isC(_) => false [owise]`, and `f(Int)` with
  `rule f(_) => 1 requires isC(H:S) [unboundVariables(H)]` beside `rule f(_) => 0 [owise]`. The
  text is `f2-examples/clgenless.kompile.kore`. Run from the package root:
  `lake env lean -j1 test/TieClauseGenless.lean`.

  - How f evaluates on c: `isC` is `false` at every value of S (`isC_false`: `isC(c(_)) => true`
    applies under no substitution, Empty having no value), so the first clause of `f` fails at
    every argument (`clG_fails`) and `f(0)` is 0 (`eval_f0`). c's functions have one result
    (`fnDet`) and evaluation solves their equations (`fnSolves`).
  - The text determines no value of `f(0)` (C7 form (c), `f0_undetermined`): the reading's theory
    with the step's closure entails neither that `f(0)` has no element nor that it is a value of
    Int. In the model of `KCore.EmptyInh` in which Empty holds an element `e` (`cP := EmptyInh.plus
    c 33`, a model of c's theory: `model`), `c(e)` is an element of S at which `isC` is true, so the
    first clause's equation at `H = c(e)` makes `f(0)` the element of 1 (`f0_is_1`). In the value
    model of c, where `f(0)` is 0, `f(0) = 1` fails (`f0_not_1`).
  - The clause's `CondDecided`, which the account lists as owed, is false (`owed_false`): it is not
    `Witnessed` (H must be a value of S, and `isC` is `true` at none: `not_witnessed`), and it is
    not `Refuted`: were it decided, every model of Γc would read `f(0)` as `Eval` gives it, 0,
    while the model of `cP` makes it 1.
  - Soundness fails on this text (`step_not_sound`). The rule `<k> go </k> => <k> f(0) </k>` takes
    `<k> go </k>` to `<k> 0 </k>` (`stepBy_go`, by `eval_f0`). In the model of `cP`, a model of c's
    theory, the instances of that application (`famEx`) are the same pattern's in `cP`
    (`famEx_plusG`), where the rule gives `<k> 1 </k>` (`stepByP_go`) and no clause owes a fact, so
    they hold `<k> 1 </k>` alone, and `<k> 0 </k>` is apart from it: `den y ⇒ famEx` is not valid
    (`famEx_not_valid`). With `coreOK`, `fnDet`, `fnSolves` and the model, only the clause's
    `CondDecided` fails (`clause_hyp_needed`): the statements' hypothesis on the clauses is necessary.

  The clauses are written by hand and shown to be the reader's (`text`). The hypotheses of
  `EmptyInh.premises_sub` and `FnHyp cP` are those of `test/ModelEmptyInhabited.lean` (namespace
  `EmptyInhFixtures.Genless`), restated here; they hold at the interpretation the parsed data
  carries, `HookParams.none`, which is the H the statements' negations are witnessed at.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseGenless

open KCore ML Faithful Faithful.Model KoreAML EmptyInh

definition_of defn from "f2-examples/clgenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable abbrev cP : Semantics := plus c 33

theorem names : c.symName 389 = "Lblf" ∧ c.symName 390 = "LblisC" ∧ c.symName 387 = "Lblc" ∧
    c.sortName 32 = "S" ∧ c.sortName 33 = "Empty" ∧ eSym c = 391 := by
  decide +kernel

/-- The parsed data's interpretation is `HookParams.none`. -/
theorem cH_none : cH HookParams.none = c := rfl

/-! ## The clauses -/

/-- `f(X) => 1 requires isC(H)`, X:Int, H:S -/
def clG : Clause :=
  { vars := [Srt.int, 32], pats := [.var 0], req := some (.app 390 [.var 1]), rhs := .dv Srt.int (.int 1),
    ens := none }
/-- `f(_) => 0 [owise]` -/
def clO : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .dv Srt.int (.int 0), ens := none, prio := 200 }
def fG : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := [clG, clO] }
/-- `isC(c(_)) => true` -/
def ic1 : Clause := { vars := [33], pats := [.app 387 [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(_) => false [owise]` -/
def ic2 : Clause := { vars := [32], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def fIsC : Fn := { label := 390, args := [32], result := Srt.bool, clauses := [ic1, ic2], total := true }

theorem text : c.fns = [fG, fIsC] := by rfl
theorem lookupF : c.lookupFn 389 = some fG := by rfl
theorem lookupIsC : c.lookupFn 390 = some fIsC := by rfl

def i0 : GroundTerm := .dv Srt.int (.int 0)
def i1 : GroundTerm := .dv Srt.int (.int 1)
/-- `c(e)`, the element of S over Empty's element in `cP`. -/
noncomputable def ce : GroundTerm := .ctor 387 [eVal c]

theorem i0_sort : c.sortOf i0 = some Srt.int := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩
theorem i1_sort : c.sortOf i1 = some Srt.int := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩

/-! ## The facts on Empty -/

theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens 33 = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.subsorts.all (fun p => p.2 != 33) = true ∧
    c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

theorem sortOf_e : cP.sortOf (eVal c) = some 33 :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some 33) : v = eVal c :=
  value_E_eq empty.1 facts.1 noRaw empty.2.1 empty.2.2.1 empty.2.2.2.1 empty.2.2.2.2 h

theorem e_not_c : c.sortOf (eVal c) = none := by decide +kernel

/-- **No value of c has sort Empty.** -/
theorem no_E (v : GroundTerm) : c.sortOf v ≠ some 33 := fun h => by
  have e := value_eq (sortOf_plus h)
  subst e
  rw [e_not_c] at h; cases h

/-! ## How `f` evaluates on c -/

/-- `isC(c(_)) => true` fails at every argument: its pattern's variable is of Empty. -/
theorem ic1_fails (vs : List GroundTerm) : Fails c vs ic1 := .intro fun σ hσ _ => by
  obtain ⟨w, -, hw⟩ := hσ 0 (by decide) 33 rfl
  exact absurd hw (no_E w)

/-- **`isC` is `false` at every value of S**, by its `[owise]` clause. -/
theorem isC_false {v : GroundTerm} (hv : c.sortOf v = some 32) : Eval c 390 [v] (some (bool false)) :=
  .clause (cl := ic2) (σ := [(0, v)]) lookupIsC (by simp [fIsC])
    (fun i s hs => by
      cases i with
      | zero => cases (show some (32 : Srt) = some s from hs); exact ⟨v, rfl, hv⟩
      | succ i => cases (show (none : Option Srt) = some s from hs))
    (.cons (.var rfl) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact ic1_fails _
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `isC(H)` under a σ giving H a value of S: `false`. -/
theorem call_isC {σ : Subst} {v : GroundTerm} (h1 : σ.lookup 1 = some v) (hv : c.sortOf v = some 32) :
    EvalTerm c σ (.app 390 [.var 1]) (some (bool false)) :=
  .call (vs := [v]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) (by rw [h1]; rfl) (isC_false hv)
    (by decide +kernel)

/-- **The first clause of `f` fails at every argument**: H is a value of S, at which `isC` is
`false`. -/
theorem clG_fails (vs : List GroundTerm) : Fails c vs clG := .intro fun σ hσ _ => by
  obtain ⟨v, h1, hv⟩ := hσ 1 (by decide) 32 rfl
  exact .intro rfl (call_isC h1 hv) (by simp [bool])

/-- **`f(0)` is 0**, by the `[owise]` clause. -/
theorem eval_f0 : Eval c 389 [i0] (some i0) :=
  .clause (cl := clO) (σ := [(0, i0)]) lookupF (by simp [fG])
    (fun i s hs => by
      cases i with
      | zero => cases (show some Srt.int = some s from hs); exact ⟨i0, rfl, i0_sort⟩
      | succ i => cases (show (none : Option Srt) = some s from hs))
    (.cons (.var rfl) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fG, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact clG_fails _
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

theorem clauses_cases {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    cl = clG ∨ cl = clO ∨ cl = ic1 ∨ cl = ic2 := by
  rw [text] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · simp only [fG, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl <;> simp
  · simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl <;> simp

theorem matchAll : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl := by
  intro fn hfn cl hcl
  have hx : cl.exs = [] := by
    rcases clauses_cases hfn hcl with rfl | rfl | rfl | rfl <;> rfl
  have he : cl.ens = none := by
    rcases clauses_cases hfn hcl with rfl | rfl | rfl | rfl <;> rfl
  have hr : varOccs cl.rhs = [] := by
    rcases clauses_cases hfn hcl with rfl | rfl | rfl | rfl <;> rfl
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [he] at ht; cases ht⟩
  rw [hr] at hi; cases hi

theorem agreeAll : ∀ fn ∈ c.fns, ClausesAgree c fn := by
  intro fn hfn
  rw [text] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · intro cl cl' hp hcomp
    have hp' : (cl, cl') = (clG, clO) := by simpa [pairs, fG] using hp
    cases hp'
    exact absurd hcomp (not_compete (by decide))
  · intro cl cl' hp hcomp
    have hp' : (cl, cl') = (ic1, ic2) := by simpa [pairs, fIsC] using hp
    cases hp'
    exact absurd hcomp (not_compete (by decide))

/-- **c's functions have one result.** -/
theorem fnDet : FnDet c := Faithful.fnDet_of_agree agreeAll matchAll

/-- Each clause's `requires` has a result under every σ well sorted on its left variables. -/
theorem reqRes {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst}
    (hσ : c.WellSortedAt cl.vars cl.leftVars σ) :
    (∀ t, cl.req = some t → ∃ r, EvalTerm c σ t r) ∧ ∃ b, Holds c cl.vars.length σ cl.pre b := by
  rcases clauses_cases hfn hcl with rfl | rfl | rfl | rfl
  · refine ⟨fun t ht => ?_, true, .top⟩
    cases ht
    obtain ⟨v, h1, hv⟩ := hσ 1 (by decide) 32 rfl
    exact ⟨_, call_isC h1 hv⟩
  all_goals exact ⟨(fun t ht => by cases ht), true, .top⟩

/-- **Evaluation solves c's equations.** -/
theorem fnSolves : FnSolves c := by
  refine fnSolves_of_parts_lookup (fun fn hfn => ?_) fnDet (fun fn hfn cl hcl => ?_) ?_ ?_
  · rw [text] at hfn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl
    · exact lookupF
    · exact lookupIsC
  · rcases clauses_cases hfn hcl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · intro fn hfn _ _ _ _ _ cl' hcl' _ _ σ' hσ' _
    exact reqRes hfn hcl' hσ'
  · intro fn hfn _ _ _ cl' σ' _ hcl' _ _ _
    rcases clauses_cases hfn hcl' with rfl | rfl | rfl | rfl <;>
      exact ⟨_, Or.inl ⟨(fun t ht => by cases ht), .dv⟩⟩

/-! ## `f(0) = 1` fails in the value model of c -/

/-- What `consistent_ofCl` asks of c beside the functions' facts, decided. -/
theorem decided : c.sortedOKCl = true ∧ c.srReady = true ∧ c.faithCoreOK = true ∧
    patHooksApart c = true ∧ c.idsOK = true ∧ c.ovls = [] ∧ c.subsorts.all (fun p => p.1 != p.2) = true := by
  decide_cheap

instance ovl : OvlOK c := OvlOK.of_nil decided.2.2.2.2.2.1 decided.2.2.2.2.2.2

theorem fG_mem : fG ∈ c.allFns := List.mem_append_left _ (by rw [text]; simp)

/-- **`f(0) = 1` is not entailed**: in the value model `f(0)` is 0. -/
theorem f0_not_1 : ¬ ((Γc c ∪ Γstep c) ⊧ (TiePair.app c 389 [i0] ≡ den c i1)) :=
  vmApp_fn_not_entailed c decided.1 decided.2.1 decided.2.2.1 decided.2.2.2.1 decided.2.2.2.2.1 fnDet fnSolves
    (clausePreDecided_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))
    fG_mem (vs := [i0]) (ss := [Srt.int]) (by decide +kernel) rfl eval_f0 (s := Srt.int) (by decide +kernel)
    (by decide)

/-! ## The second model (the hypotheses of `EmptyInh.premises_sub` and `FnHyp cP`) -/

theorem openLawsP : OpenLaws cP := by
  intro k hk _
  have hk' : k ∈ c.params ++ [eParam c 33] := hk
  rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩

/-- The `[owise]` clauses of `f` and `isC` do not fail at a value of their argument sort. -/
theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [text] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · obtain ⟨v, rfl, hv⟩ := EmptyInh.sortsOf_single hvs
    exact ⟨clO, by simp [fG], not_fails_var rfl rfl rfl rfl hv⟩
  · obtain ⟨v, rfl, hv⟩ := EmptyInh.sortsOf_single hvs
    exact ⟨ic2, by simp [fIsC], not_fails_var rfl rfl rfl rfl hv⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

/-- The rank `isC` before `f` shows both terminate; only `f`'s first clause is named, for match
independence; no clause owes its `CondDecided` in `cP`. -/
theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [] ∧
    cP.rankObligations [390, 389] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [390, 389] [] = [] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [(389, 0)] ∧ cP.owedRules = [] ∧
    cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem textP : cP.fns = [fG, fIsC] := text

theorem lookupFP : cP.lookupFn 389 = some fG :=
  lookupFn_of_core coreP (show fG ∈ cP.fns by rw [textP]; simp)

theorem lookupIsCP : cP.lookupFn 390 = some fIsC :=
  lookupFn_of_core coreP (show fIsC ∈ cP.fns by rw [textP]; simp)

theorem lookupFP_eq {fn : Fn} (h : cP.lookupFn 389 = some fn) : fn = fG :=
  Option.some.inj (h.symm.trans lookupFP)

theorem matchG : MatchIndependent cP clG := by
  have hx : clG.exs = [] := rfl
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  cases hi

theorem oblP : FnObligations cP [390, 389] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, howR, howC⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf => (by rw [hagr] at hf; cases hf), fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩, openLawsP⟩
  rw [hmat, List.mem_singleton] at hp
  subst hp
  have e := lookupFP_eq hfn
  subst e
  simp only [fG, List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact matchG

theorem fnHypP : FnHyp cP :=
  fnHyp_of_fnObligationsN coreP (by rw [namedP.2.1]; intro f hf; cases hf) ParamsTotal.nil oblP

theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

/-! ## `f(0)` in the second model: 1 -/

theorem ce_sort : cP.sortOf ce = some 32 :=
  sortOf_ctor_intro ⟨⟨387, [33], 32⟩, by decide +kernel, sortsOf_cons.mpr ⟨_, _, sortOf_e, sortsOf_nil, rfl⟩, rfl⟩

/-- **`isC(c(e))` is `true` in `cP`**, by `isC(c(_)) => true`. -/
theorem isC_ce : Eval cP 390 [ce] (some (bool true)) :=
  .clause (cl := ic1) (σ := [(0, eVal c)]) lookupIsCP (by simp [fIsC])
    (fun i s hs => by
      cases i with
      | zero => cases (show some (33 : Srt) = some s from hs); exact ⟨_, rfl, sortOf_e⟩
      | succ i => cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `X ↦ 0`, `H ↦ c(e)`. -/
noncomputable def σce : Subst := [(0, i0), (1, ce)]

theorem ws_ce : cP.WellSorted clG.vars σce := fun i s hs => by
  match i, hs with
  | 0, hs => cases (show some Srt.int = some s from hs); exact ⟨i0, rfl, sortOf_plus i0_sort⟩
  | 1, hs => cases (show some (32 : Srt) = some s from hs); exact ⟨ce, rfl, ce_sort⟩
  | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)

theorem req_ce : EvalTerm cP σce (.app 390 [.var 1]) (some (bool true)) :=
  .call (vs := [ce]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) rfl isC_ce (by decide +kernel)

/-- **The equation at `H = c(e)`**: in a model of `cP`'s Γc, `f(0)` is 1. -/
theorem f0_is_1 {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hΓc : I ⊧ᴵP Γc cP)
    (e0 : Valuation M) (m : M) :
    (TiePair.app c 389 [i0]).interpret I e0 m ↔ (den c i1).interpret I e0 m := by
  have hΓ : I ⊧ᴵP Γ cP := fun φ hφ => hΓc φ (Or.inl hφ)
  obtain ⟨hsok, hsr', hnn, -, -, -, -, -, hno⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hfnm := (lookupFn_spec lookupFP).1
  have hts : HoldsShape.TermSound cP I := HoldsShape.termSoundEx (Semantics.coreOK_iff_ex.mp coreP) hΓc
    (openClauses_of_owed (by rw [namedP.2.2.2.2.2.2.2]; intro p hp; cases hp))
  have hr1 : ∀ v, some i1 = some v → cP.sortOf v = some fG.result := fun v hv => by
    cases hv; exact sortOf_plus i1_sort
  have ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees cP I tbl (canonVars cP clG.vars) σce e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight cP fG clG)).interpret I e m ↔ Res cP I e (some i1) m :=
    fun tbl e hag => right_iff hΓ hnn hfnm hr1
      (fun m => hts (EvalTerm.dv) ws_ce (canonVars_length _ _) hag
        (show sortOfTerm _ clG.vars clG.rhs = some Srt.int by decide +kernel) m)
      (fun t h => by cases h)
  have ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees cP I tbl (canonVars cP clG.vars) σce e →
      ∀ t, clG.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore cP (canonVars cP clG.vars) t)).interpret I e m ↔
        (den cP (bool true)).interpret I e m := fun tbl e hag t ht m => by
    cases ht
    exact hts req_ce ws_ce (canonVars_length _ _) hag
      (show sortOfTerm _ clG.vars (.app 390 [.var 1]) = some Srt.bool by decide +kernel) m
  have hws : cP.sortsOf [i0] = some fG.args := sortsOf_cons.mpr ⟨_, _, sortOf_plus i0_sort, sortsOf_nil, rfl⟩
  have h := clause_eq_open hΓ hnn htr lookupFP (by simp [fG] : clG ∈ fG.clauses) (by decide) rfl rfl hws ws_ce
    (.cons (.var rfl) .nil) (by decide +kernel) (by decide +kernel) (by decide)
    (fun t h => by cases h; decide) (by decide) (fun t h => by cases h) hr1 ihreq ihrhs e0 m
  unfold TiePair.app
  rw [← symApp_plus (E := 33), ← koreList_plus_fun (E := 33), ← den_plus (E := 33)]
  exact h

/-! ## The expectation (C7 form (c)) -/

/-- **The text determines no value of `f(0)`**: over all H, the reading's theory with the step's
closure entails neither that `f(0)` has no element nor that it is any value of Int. At
`HookParams.none`, the model in which Empty holds `e` makes `f(0)` the element of 1, which rules
out `⊥` and every value but 1; the value model, where `f(0)` is 0, rules out 1. -/
theorem f0_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧ (TiePair.app (cH H) 389 [i0] ≡ ⊥)) ∧
    ∀ v, c.sortOf v = some Srt.int →
      ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧ (TiePair.app (cH H) 389 [i0] ≡ den (cH H) v)) := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hP φ (Or.inl (Or.inl hφ))
  have hD := defOK hΓP
  have hspec := elemOf_spec hΓP (sortOf_plus i1_sort) KoreAML.val0
  have hfe : ∀ m, (TiePair.app c 389 [i0]).interpret I KoreAML.val0 m ↔ m = elemOf cP I i1 := fun m =>
    (f0_is_1 hΓcP _ m).trans (by rw [← den_plus (E := 33)]; exact hspec.1 m)
  refine ⟨fun h => ?_, fun v hv h => ?_⟩
  · have h1 := h HookParams.none hc KoreAML.val0 (elemOf cP I i1)
    rw [cH_none, KoreAML.interp_equal hD] at h1
    have := ((h1 (elemOf cP I i1)).mp ((hfe _).mpr rfl))
    simp at this
  · by_cases hv1 : v = i1
    · subst hv1
      exact f0_not_1 (h HookParams.none)
    · have h1 := h HookParams.none hc KoreAML.val0 (elemOf cP I i1)
      rw [cH_none, KoreAML.interp_equal hD] at h1
      have hvP : cP.sortOf v = some Srt.int := sortOf_plus hv
      have hspecv := elemOf_spec hΓP hvP KoreAML.val0
      have hm := (h1 (elemOf cP I i1)).mp ((hfe _).mpr rfl)
      rw [← den_plus (E := 33)] at hm
      have heq : elemOf cP I i1 = elemOf cP I v := (hspecv.1 _).mp hm
      obtain ⟨hsok, hsr', -, hg, -, -, -, -, hno⟩ := hypSound_of_core coreP
      haveI : OvlOK cP := hno
      have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
      exact hv1 (values_apart hΓP hg htr (apartSort_of_sorted hg hvP) (sortOf_plus i1_sort) hvP heq).symm

/-! ## The owed `CondDecided` of the first clause is false -/

/-- **The clause is not `Witnessed`**: H must be a value of S, and `isC` is `false` there. -/
theorem not_witnessed : ¬ clG.Witnessed c := by
  rintro ⟨σ, hσ, hreq, -⟩
  obtain ⟨v, hv, hvs⟩ := hσ 1 (by decide) 32 rfl
  have he := (hreq _ rfl).1
  have hf := EvalTerm.functional_of_fnDet fnDet he (call_isC hv hvs)
  simp [bool] at hf

/-- **The clause's `CondDecided`, owed by the account, is false.** Were it decided, every model of
Γc would read `f(0)` as `Eval` gives it, 0; the model of `cP` makes it 1, and 0 and 1 are apart. -/
theorem owed_false : ¬ clG.CondDecided c := by
  intro hd
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hc φ (Or.inl hφ)
  have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hP φ (Or.inl (Or.inl hφ))
  have hcore : c.coreOK = true := by decide_cheap
  have hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
    intro fn hfn cl hcl hw
    rcases clauses_cases hfn hcl with rfl | rfl | rfl | rfl
    · exact hd
    all_goals exact absurd hw (by decide +kernel)
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core hcore
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hneg := neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (Semantics.fnsNoExs_of_all (by decide +kernel))) hsr (Semantics.coreOK_parts hcore).2.1 hph
    hcw (HoldsShape.preReadAll_of_core hcore hIc)
  have h0 := eval_den4ClPre hI hnn hsc hph
    (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK_noExs hok (Semantics.fnsNoExs_of_all (by decide +kernel)))) hneg
    (HoldsShape.preReadAll_of_core hcore hIc) eval_f0 lookupF (sortsOf_cons.mpr ⟨_, _, i0_sort, sortsOf_nil, rfl⟩)
  have hspec1 := elemOf_spec hΓP (sortOf_plus i1_sort) KoreAML.val0
  have hspec0 := elemOf_spec hΓP (sortOf_plus i0_sort) KoreAML.val0
  have hm1 : (TiePair.app c 389 [i0]).interpret I KoreAML.val0 (elemOf cP I i1) :=
    (f0_is_1 hΓcP _ _).mpr (by rw [← den_plus (E := 33)]; exact (hspec1.1 _).mpr rfl)
  unfold TiePair.app at hm1
  have hm0 := (h0 KoreAML.val0 _).mp hm1
  change (den c i0).interpret I KoreAML.val0 (elemOf cP I i1) at hm0
  rw [← den_plus (E := 33)] at hm0
  have heq : elemOf cP I i1 = elemOf cP I i0 := (hspec0.1 _).mp hm0
  obtain ⟨hsokP, hsrP, -, hgP, -, -, -, -, hnoP⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hnoP
  have htrP := (sortCtx_of_all hsokP hsrP (OvlOK.ovlCase hnoP)).trans
  have := values_apart hΓP hgP htrP (apartSort_of_sorted hgP (sortOf_plus i1_sort)) (sortOf_plus i1_sort)
    (sortOf_plus i0_sort) heq
  simp [i0, i1] at this

/-! ## Soundness fails at the step of `go` -/

/-- `<k>`, the k cell. -/
def kC : Sym := 384
/-- `go`. -/
def goS : Sym := 388

/-- `<k> go ~> .K </k> V0 => <k> f(0) ~> .K </k> V0`, the text's rule, V0 the counter cell. -/
def rG : Rule :=
  { vars := [Srt.counter],
    lhs := .app topLabel [.app kC [.app kseq [.app goS [], .app dotk []]], .var 0], req := none,
    rhs := .app topLabel [.app kC [.app kseq [.inj Srt.int Srt.kitem (.app 389 [.dv Srt.int (.int 0)]),
      .app dotk []]], .var 0],
    ens := none, prio := 50 }

theorem rules_eq : c.rules = [rG] := by rfl

theorem names_go : c.symName kC = "Lbl'-LT-'k'-GT-'" ∧ c.symName goS = "Lblgo" := by
  decide +kernel

/-- `<k> t ~> .K </k>` with the counter cell at 0. -/
def cfgG (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kC [.ctor kseq [t, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- The counter cell at 0. -/
def u0 : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]
def xv : GroundTerm := cfgG (.ctor goS [])
def y0v : GroundTerm := cfgG (injNormal Srt.int Srt.kitem i0)
def y1v : GroundTerm := cfgG (injNormal Srt.int Srt.kitem i1)

theorem cfg_sorts : c.sortOf xv = some topCellSort ∧ c.sortOf y0v = some topCellSort ∧
    c.sortOf y1v = some topCellSort ∧ c.sortOf u0 = some Srt.counter := by
  decide +kernel

/-- `<k> go </k>`. -/
def xG : Config c := ⟨xv, cfg_sorts.1⟩
/-- `<k> 0 </k>`. -/
def y0 : Config c := ⟨y0v, cfg_sorts.2.1⟩
/-- `<k> go </k>` in `cP`. -/
def xP : Config cP := ⟨xv, sortOf_plus cfg_sorts.1⟩
/-- `<k> 1 </k>` in `cP`. -/
def y1P : Config cP := ⟨y1v, sortOf_plus cfg_sorts.2.2.1⟩

/-- `V0 ↦ <generatedCounter> 0 </generatedCounter>`. -/
def σG : Subst := [(0, u0)]

theorem syms_go : c.isCtor topLabel = true ∧ c.isCtor kC = true ∧ c.isCtor kseq = true ∧
    c.isCtor goS = true ∧ c.isCtor dotk = true ∧ c.isCtor 389 = false ∧ isHook 389 = false ∧
    c.isParam 389 = false := by
  decide +kernel

theorem syms_goP : cP.isCtor topLabel = true ∧ cP.isCtor kC = true ∧ cP.isCtor kseq = true ∧
    cP.isCtor goS = true ∧ cP.isCtor dotk = true ∧ cP.isCtor 389 = false ∧ cP.isParam 389 = false := by
  decide +kernel

/-- **`f(0)` is 1 in `cP`**, by the first clause at `H = c(e)`. -/
theorem evalP_f0 : Eval cP 389 [i0] (some i1) :=
  .clause (cl := clG) (σ := σce) lookupFP (by simp [fG]) ws_ce (.cons (.var rfl) .nil)
    (fun t ht => by cases ht; exact req_ce) .top
    (fun cl' hcl' _ hlt => by
      simp only [fG, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- **The step of `go`**: the rule takes `<k> go </k>` to `<k> 0 </k>` under `σG`, `f(0)` being 0
(`eval_f0`). -/
theorem stepBy_go : StepBy c rG σG xG y0 where
  mem := by rw [rules_eq]; exact List.mem_singleton_self _
  hσ := fun i s hs => by
    match i, hs with
    | 0, hs => cases (show some Srt.counter = some s from hs); exact ⟨u0, rfl, cfg_sorts.2.2.2⟩
    | _ + 1, hs => cases (show (none : Option Srt) = some s from hs)
  hmatch := .ctor syms_go.1 (.cons (.ctor syms_go.2.1 (.cons (.ctor syms_go.2.2.1
    (.cons (.ctor syms_go.2.2.2.1 .nil) (.cons (.ctor syms_go.2.2.2.2.1 .nil) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun _ h => nomatch h
  hpre := .top
  heval := .ctor syms_go.1 (.cons (.ctor syms_go.2.1 (.cons (.ctor syms_go.2.2.1
    (.cons (.inj (.call (vs := [i0]) syms_go.2.2.2.2.2.1 syms_go.2.2.2.2.2.2.1 (.cons .dv .nil) rfl eval_f0
      syms_go.2.2.2.2.2.2.2)) (.cons (.ctor syms_go.2.2.2.2.1 .nil) .nil))) .nil)) (.cons .var .nil))
  hens := fun _ h => nomatch h
  hpost := .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq, List.mem_singleton] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

theorem step_go : Step c xG y0 := step_iff_by.mpr ⟨rG, σG, stepBy_go⟩

/-- The same rule in `cP` takes `<k> go </k>` to `<k> 1 </k>`, `f(0)` being 1 there (`evalP_f0`). -/
theorem stepByP_go : StepBy cP rG σG xP y1P where
  mem := by
    show rG ∈ c.rules
    rw [rules_eq]; exact List.mem_singleton_self _
  hσ := fun i s hs => by
    match i, hs with
    | 0, hs => cases (show some Srt.counter = some s from hs); exact ⟨u0, rfl, sortOf_plus cfg_sorts.2.2.2⟩
    | _ + 1, hs => cases (show (none : Option Srt) = some s from hs)
  hmatch := .ctor syms_goP.1 (.cons (.ctor syms_goP.2.1 (.cons (.ctor syms_goP.2.2.1
    (.cons (.ctor syms_goP.2.2.2.1 .nil) (.cons (.ctor syms_goP.2.2.2.2.1 .nil) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun _ h => nomatch h
  hpre := .top
  heval := .ctor syms_goP.1 (.cons (.ctor syms_goP.2.1 (.cons (.ctor syms_goP.2.2.1
    (.cons (.inj (.call (vs := [i0]) syms_goP.2.2.2.2.2.1 syms_go.2.2.2.2.2.2.1 (.cons .dv .nil) rfl evalP_f0
      syms_goP.2.2.2.2.2.2)) (.cons (.ctor syms_goP.2.2.2.2.1 .nil) .nil))) .nil)) (.cons .var .nil))
  hens := fun _ h => nomatch h
  hpost := .top
  hprio := fun r' hr' hlt => by
    change r' ∈ c.rules at hr'
    rw [rules_eq, List.mem_singleton] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

/-- The instances of the application read names only: the same pattern in c and `cP`. -/
theorem famEx_plusG : famEx cP rG σG = famEx c rG σG := by
  simp only [famEx, fixK, ruleRight, Cond.conj, termKore_plus_fun, condKore_plus_fun, gKore_plus]
  rfl

/-- What `famEx_denCl_exNil` asks of `cP` beside the model and the step, decided. -/
theorem decidedP : cP.clausesPreTop = true ∧ cP.sortedOKCl = true ∧ cP.srReady = true ∧
    cP.faithCoreOK = true ∧ patHooksApart cP = true ∧ cP.overloadsOK = true := by
  decide_cheap

/-- **The conjunct `den y ⇒ famEx` of soundness is not valid at the step of `go`.** In the model of
`cP` (`model`), a model of c's theory through `sub`, the instances of the application are those of
the same rule in `cP` (`famEx_plusG`), where no clause owes a fact and the rule gives `<k> 1 </k>`
(`stepByP_go`, `famEx_denCl_exNil`); `<k> 0 </k>`, which `Step` gives, is apart from it. -/
theorem famEx_not_valid : ¬ (Γc c ⊧ (den c y0.val ⇒ famEx c rG σG)) := by
  intro h
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hc φ (Or.inl hφ)
  have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hP φ (Or.inl (Or.inl hφ))
  obtain ⟨hsokP, hsrP, -, hgP, -, -, -, -, hnoP⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hnoP
  have htrP := (sortCtx_of_all hsokP hsrP (OvlOK.ovlCase hnoP)).trans
  have hs0 : cP.sortOf y0v = some topCellSort := sortOf_plus cfg_sorts.2.1
  have hs1 : cP.sortOf y1v = some topCellSort := sortOf_plus cfg_sorts.2.2.1
  have hspec0 := elemOf_spec hΓP hs0 KoreAML.val0
  have hspec1 := elemOf_spec hΓP hs1 KoreAML.val0
  have hy0 : (den c y0v).interpret I KoreAML.val0 (elemOf cP I y0v) := by
    rw [← den_plus (E := 33)]; exact (hspec0.1 _).mpr rfl
  have hfam : (famEx c rG σG).interpret I KoreAML.val0 (elemOf cP I y0v) := h hIc KoreAML.val0 _ hy0
  rw [← famEx_plusG] at hfam
  have hcP : ∀ fn ∈ cP.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cP = true → cl.CondDecided cP :=
    openClauses_of_owed (by rw [namedP.2.2.2.2.2.2.2]; intro p hp; cases hp)
  obtain ⟨hpt, hok, hsr, hfa, hph, hov⟩ := decidedP
  have hy1 := (famEx_denCl_exNil (hpreTop := hpt) hΓcP hok hsr hfa hph hov hcP stepByP_go rfl rfl
    KoreAML.val0 _).mp hfam
  have heq : elemOf cP I y0v = elemOf cP I y1v := (hspec1.1 _).mp hy1
  have := values_apart hΓP hgP htrP (apartSort_of_sorted hgP hs0) hs0 hs1 heq
  simp [y0v, y1v, cfgG, injNormal, i0, i1] at this

/-- **Soundness fails on this text.** -/
theorem step_not_sound : ¬ SoundC c := fun h => famEx_not_valid (h.2 xG y0 rG σG stepBy_go).2

/-- **The clause side of the functions' hypothesis is necessary**: c meets `coreOK`, its functions
have one result, evaluation solves their equations, its theory with the step's closure has a model,
and `Step` takes `<k> go </k>` to `<k> 0 </k>`; still soundness fails (`step_not_sound`), the
clause's `CondDecided` being false (`owed_false`). -/
theorem clause_hyp_needed : c.coreOK = true ∧ FnDet c ∧ FnSolves c ∧ Consistent c ∧ Step c xG y0 ∧
    ¬ clG.CondDecided c ∧ ¬ SoundC c := by
  obtain ⟨M, hM, I, -, hc⟩ := model
  exact ⟨by decide_cheap, fnDet, fnSolves, ⟨M, hM, I, hc⟩, step_go, owed_false, step_not_sound⟩

end KCore.TieClauseGenless

/-- info: 'KCore.TieClauseGenless.f0_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseGenless.f0_undetermined
/-- info: 'KCore.TieClauseGenless.owed_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseGenless.owed_false
/-- info: 'KCore.TieClauseGenless.eval_f0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseGenless.eval_f0
/-- info: 'KCore.TieClauseGenless.step_not_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseGenless.step_not_sound
/-- info: 'KCore.TieClauseGenless.clause_hyp_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseGenless.clause_hyp_needed
