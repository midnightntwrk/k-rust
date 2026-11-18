/-
  The held-named form of `FnHyp`'s derivation (`fnHyp_of_fnObligationsN`, FnObligations.lean) at a
  function whose clause holds a variable of a sort with a value that `Semantics.valued` does not
  exhibit: the first of `HeldOwed`'s two facts, shown by exhibiting the value. Run from the package
  root: `lake env lean -j1 test/HeldNamed.lean`. Kernel-checked (`decide +kernel`).

  The semantics `cS` is the reader's for `f2-examples/opencl.kompile.kore` (`opencl.k`: Int, Bool,
  the function `g(Int)` with `g(_) => 0 [owise]`, the total predicate `isC`, the rule
  `<k> go => g(f()) </k>`), with `f` made a function of the clauses
  - `clS`, `f() => 0 requires false ensures Y:Float ==Float Y`: Y is of Float, which has values
    (`0.0`) but is not Int, Bool, the result of a constructor without arguments, or a sort of which
    the search exhibits a value (`Parse.exhibit?` seeds no Float literal), so `valued` does not
    accept it, and neither the patterns nor the `requires` hold it: `rightValued` fails and `f` is
    held-named (`Semantics.heldObligations`);
  - `clOne`, `f() => 1`, at the same priority.
  `cS` is `coreOK`.

  - `heldS`: what is owed of `f` (`HeldOwed`) by its first fact, `HeldFn`: Y's sort has the value
    `0.0`. No result of `f` is shown by hand.
  - `oblS`: the rank and the totality decider name no function; `f`'s agreement and `clS`'s match
    independence are named and shown by hand (`clS` applies nowhere, its `requires` being `false`).
  - `fnHypS`: `FnHyp cS` from `fnHyp_of_fnObligationsN`. The termination of `f` there is the
    rank decider's, run with the held variables of `f` (`terminates_of_rankLN`): `clS` fails at a
    match extended to Y, and `clOne` decides.
  - The pinned `sound_hyp` and `exact_hyp` at it.

  The second fact (a result, where the sort has no value) is instantiated at `c3` of
  test/OpenClausePins.lean (`fnHyp3N`); the owed fact refuted, at `cE` of
  test/OpenClauseConsistent.lean (`not_heldOwedE`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HeldNamedTest

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols the clauses name. -/
example : c.symName 391 = "Lblf" ∧ c.symName 389 = "Lblg" ∧ c.symName 390 = "LblisC" := by
  decide +kernel

/-- `f() => 0 requires false ensures Y:Float ==Float Y` -/
def clS : Clause :=
  { vars := [Srt.float], pats := [], req := some (.dv Srt.bool (.bool false)), rhs := .dv Srt.int (.int 0),
    ens := some (.app floatEq [.var 0, .var 0]) }
/-- `f() => 1` -/
def clOne : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 1), ens := none }

/-- `f` with the clauses `clS` and `clOne`. -/
def fS : Fn := { label := 391, args := [], result := Srt.int, clauses := [clS, clOne] }

/-- `c` with `f` a function of the clauses `clS` and `clOne`. -/
noncomputable def cS : Semantics := { c with fns := c.fns ++ [fS], params := c.params.filter (·.sig.name != 391) }

/-- Float is not `valued`; `clS`'s variable is outside its patterns and conditions, so
`rightValued` fails and `f` is the one held-named function; `coreOK` holds at `cS`. -/
theorem shape : cS.valued Srt.float = false ∧ clS.leftVars = [] ∧ cS.rightValued = false ∧
    cS.heldObligations = [391] ∧ cS.coreOK = true := by
  decide_cheap

theorem coreS : cS.coreOK = true := shape.2.2.2.2

/-- The Float `+0.0` at double precision (significand 53 bits, exponent 11 bits). -/
def fltV : GroundTerm := .dv Srt.float (.float 53 11 0)

/-- `fltV` is a value of Float. -/
theorem sortOf_fltV0 : cS.sortOf fltV = some Srt.float := by decide +kernel

/-- `fltV` is a value of Float under every interpretation of the parameters: `sortOf` of a literal
reads no parameter. -/
theorem sortOf_fltV (H : HookParams) : (cS.withHooks H).sortOf fltV = some Srt.float :=
  (Semantics.sortOf_withHooks_rawFree cS H (v := fltV) rfl).trans sortOf_fltV0

/-- A rank of `cS`'s functions: `isC`, `g`, `f`. -/
def ordS : List Sym := [390, 389, 391]

/-- The lists the package would state: no function is named for termination or totality; `f`'s
equations and `clS` are named for agreement and match independence; no rule and no clause owes a
condition. -/
theorem named : cS.rankObligations ordS ++ cS.decObligationsL = [] ∧
    cS.totalObligationsRP ordS [] = [] ∧ cS.agreeObligationsI = [391] ∧
    cS.matchObligationsL = [(391, 0)] ∧ cS.owedRules = [] ∧ cS.owedClauses = [] := by
  decide +kernel

theorem fS_mem : fS ∈ cS.fns := List.mem_append_right _ (List.mem_singleton_self _)

theorem lookupF {fn : Fn} (h : cS.lookupFn 391 = some fn) : fn = fS :=
  Option.some.inj (h.symm.trans (lookupFn_of_core coreS fS_mem))

/-- **The variables of `f`'s clauses are held**: `clS`'s Y is of Float, which has the value `0.0`;
`clOne` has no variable. -/
theorem heldFnS : cS.HeldFn fS := by
  intro cl hcl i s hs
  simp only [fS, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · cases i with
    | zero => cases hs; exact .inr ⟨fltV, sortOf_fltV0⟩
    | succ i => simp [clS] at hs
  · simp [clOne] at hs

/-- **What is owed of `f`, by the first fact.** -/
theorem heldS : ∀ f ∈ cS.heldObligations, HeldOwed cS f := by
  intro f hf fn hfn
  rw [shape.2.2.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupF hfn
  subst e
  exact .inl heldFnS

/-- `clS` applies under no substitution: its `requires` is `false`. -/
theorem clS_not_applies (σ : Subst) (vs : List GroundTerm) : ¬ clS.AppliesAt cS σ vs := fun h => by
  have := h.2.2.1 _ rfl
  cases this

/-- `f`'s equations agree: `clS` applies nowhere. -/
theorem agreeS : ClausesAgree cS fS := by
  intro cl cl' hp _
  have hp' : (cl, cl') = (clS, clOne) := by simpa [fS, pairs] using hp
  cases hp'
  exact ⟨fun vs σ _ ha => absurd ha (clS_not_applies σ vs), fun vs _ σ' _ ha => absurd ha (clS_not_applies σ' vs)⟩

/-- **The facts the deciders leave of `FnHyp` at `cS`**: the two named ones by hand. -/
theorem oblS : FnObligations cS ordS [] := by
  obtain ⟨hterm, htot, hagr, hmat, howR, howC⟩ := named
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf fn hfn => ?_, fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩,
    openLaws_of_plain (by decide +kernel)⟩
  · rw [hagr, List.mem_singleton] at hf
    subst hf
    have e := lookupF hfn
    subst e
    exact agreeS
  · rw [hmat, List.mem_singleton] at hp
    subst hp
    have e := lookupF hfn
    subst e
    have e : cl = clS := by simpa [fS] using hcl.symm
    subst e
    exact (matchIndependent_iff_noExs rfl).mpr fun vs σ _ ha => absurd ha (clS_not_applies σ vs)

/-- **`FnHyp cS` from the held-named form**: `coreOK`, the owed fact of `f` (its variables are
held) and the deciders. -/
theorem fnHypS : FnHyp cS := fnHyp_of_fnObligationsN coreS heldS ParamsTotal.nil oblS

/-- `f` has a result at `[]`, from the rank decider run with `f`'s held variables. -/
example : ∃ r, Eval cS 391 [] r := fnHypS.1 fS fS_mem [] rfl

/-- The pinned statements at `cS`. -/
example : SoundC cS := sound_hyp cS coreS fnHypS
example : ExactC cS := exact_hyp cS coreS fnHypS
example : SoundC cS := sound_fnN cS ordS [] coreS heldS ParamsTotal.nil oblS

/-- Under an interpretation H the variables of `f` are held as well (`sortOf` of a literal reads
no parameter), so the owed fact is shown for every H. -/
theorem heldSH (H : HookParams) : ∀ f ∈ cS.heldObligations, HeldOwed (cS.withHooks H) f := by
  intro f hf fn hfn
  rw [shape.2.2.2.1, List.mem_singleton] at hf
  subst hf
  have e : fn = fS := Option.some.inj (hfn.symm.trans
    (lookupFn_of_core ((Semantics.coreOK_withHooks cS H).trans coreS) (c := cS.withHooks H) fS_mem))
  subst e
  refine .inl fun cl hcl i s hs => ?_
  simp only [fS, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · cases i with
    | zero => cases hs; exact .inr ⟨fltV, sortOf_fltV H⟩
    | succ i => simp [clS] at hs
  · simp [clOne] at hs

example (H : HookParams) (hob : FnObligations (cS.withHooks H) ordS []) : FnHyp (cS.withHooks H) :=
  fnHyp_withHooksN coreS H (heldSH H) ParamsTotal.nil hob

/--
info: 'HeldNamedTest.fnHypS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fnHypS

end HeldNamedTest
