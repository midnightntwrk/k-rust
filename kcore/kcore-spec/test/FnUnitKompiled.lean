/-
  The unit laws of a function on its kompiled text: `f2-examples/e2-fn-assoc-unit.kompile.kore`,
  the text of fixture e2-fn-assoc-unit (`syntax Int ::= "zero" [function, total]`,
  `syntax Int ::= pu(Int, Int) [function, total, assoc, unit(zero)]`, `rule zero => 0`,
  `rule pu(A, B) => A +Int B`), the text whose sha256 `test/constructs/fixtures/e2-fn-assoc-unit/kompile.txt`
  records (1e7f66ac…), with its paths restored. Every statement is on the literal `defn`, for every
  interpretation H.

  The text writes three laws of `pu` (sentences 250 to 252 of its main module): `pu(pu(K1, K2), K3) =
  pu(K1, pu(K2, K3))`, `pu(K, zero) = K` and `pu(zero, K) = K`. The reader holds them as
  `Definition.laws` (`laws_eq`), not in the semantics; the account lists `FnLaws` as owed for each.
  Each is `lawSorted` (`laws_sorted`) and `coreOK` accepts the text (`coreOK_text`).

  The function's clauses decide each law, under every interpretation:
  - `zero` is 0 by its one clause (`eval_zero`), `pu(a, b)` is `a + b` by its one clause at every
    pair of Ints (`eval_pu`); no rest is read.
  - So `pu(a, zero)` and `pu(zero, a)` are `a`: `LawAt` holds of both unit laws (`unitR_lawAt`,
    `unitL_lawAt`), and of the associativity law (`assoc_lawAt`): both sides are `a + b + d`.
  - `FnLaws` holds of the text's laws (`fnLaws`): the fact the account lists as owed is discharged
    for this text.

  Where the clauses decide otherwise the law is false: `cOne` is the semantics with `zero`'s clause
  answering 1 (not a kompiled text). There `pu(a, zero)` is `a + 1`, and `LawAt` of the right unit
  law fails at every interpretation (`cOne_not_unitR`).

  Run from the package root: `lake env lean -j1 test/FnUnitKompiled.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnUnitKompiled

open KCore ML Faithful

definition_of defn from "f2-examples/e2-fn-assoc-unit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def pu : Sym := 384
def zero : Sym := 385

theorem names : c.symName pu = "Lblpu" ∧ c.symName zero = "Lblzero" := by decide +kernel

/-- No parameter of the definition is an open generator: it has none. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK_text : c.coreOK = true := by decide +kernel

/-! ## The laws the text writes -/

/-- `pu(pu(K1, K2), K3) = pu(K1, pu(K2, K3))`. -/
def assocLaw : LawEq :=
  ⟨[Srt.int, Srt.int, Srt.int], .app pu [.app pu [.var 0, .var 1], .var 2],
    .app pu [.var 0, .app pu [.var 1, .var 2]]⟩

/-- `pu(K, zero) = K`. -/
def unitR : LawEq := ⟨[Srt.int], .app pu [.var 0, .app zero []], .var 0⟩

/-- `pu(zero, K) = K`. -/
def unitL : LawEq := ⟨[Srt.int], .app pu [.app zero [], .var 0], .var 0⟩

/-- The reader's laws of the text are its three law axioms, in text order. -/
theorem laws_eq : defn.laws = [assocLaw, unitR, unitL] := by kernel_rfl

theorem laws_sorted : lawSorted c assocLaw = true ∧ lawSorted c unitR = true ∧ lawSorted c unitL = true := by
  decide +kernel

/-! ## The functions and their clauses -/

/-- `pu(A, B) => A +Int B`. -/
def clPu : Clause :=
  ⟨[Srt.int, Srt.int], [.var 0, .var 1], none, .app intAdd [.var 0, .var 1], none, 50, false, [], .top, .top⟩

/-- `zero => n`. -/
def clZero (n : Int) : Clause := ⟨[], [], none, .dv Srt.int (.int n), none, 50, false, [], .top, .top⟩

def fnPu : Fn := ⟨pu, [Srt.int, Srt.int], Srt.int, [clPu], true⟩
def fnZero (n : Int) : Fn := ⟨zero, [], Srt.int, [clZero n], true⟩

/-- The text's two functions are `pu` and `zero` with the clauses above. -/
theorem fns_eq : c.fns = [fnPu, fnZero 0] := by kernel_rfl

theorem ctor_pu : c.isCtor pu = false := by decide +kernel
theorem ctor_zero : c.isCtor zero = false := by decide +kernel
theorem ctor_add : c.isCtor intAdd = false := by decide +kernel
theorem param_pu : c.isParam pu = false := by decide +kernel
theorem param_zero : c.isParam zero = false := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hcf : c.clausesFixed = true := by decide +kernel
private theorem hag : c.agreeObligations = [] := by decide +kernel
private theorem hsh : c.shapesOK = true := by decide +kernel

theorem coherent (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((Semantics.clausesFixed_withHooks c H).trans hcf)
    ((Semantics.agreeObligations_withHooks c H).trans hag)

theorem look_pu (H : HookParams) : (cH H).lookupFn pu = some fnPu := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl

theorem look_zero (H : HookParams) : (cH H).lookupFn zero = some (fnZero 0) := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl

/-! ## Evaluation -/

section
variable {d : Semantics}

theorem evVar {σ : Subst} {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) :
    EvalTerm d σ (.var i) (some v) :=
  h ▸ EvalTerm.var

/-- A call of the binary function `f` at two defined arguments. -/
theorem evCall2 {f : Sym} (hk : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {σ : Subst} {t u : Term} {x y : GroundTerm} {r : Option GroundTerm}
    (ht : EvalTerm d σ t (some x)) (hu : EvalTerm d σ u (some y)) (hf : Eval d f [x, y] r) :
    EvalTerm d σ (.app f [t, u]) r :=
  .call hk hh (.cons ht (.cons hu .nil)) rfl hf hp

/-- A call of the constant function `f`. -/
theorem evCall0 {f : Sym} (hk : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {σ : Subst} {r : Option GroundTerm} (hf : Eval d f [] r) : EvalTerm d σ (.app f []) r :=
  .call hk hh .nil rfl hf hp

/-- A binary interpreted Int symbol at two variables bound to Ints. -/
theorem evHook2 {op : Sym} (hk : d.isCtor op = false) (hh : isHook op = true) {σ : Subst}
    {i j : Nat} {x y : GroundTerm} {v : GroundTerm} (hi : σ.lookup i = some x) (hj : σ.lookup j = some y)
    (hv : hook op [x, y] = some (some v)) : EvalTerm d σ (.app op [.var i, .var j]) (some v) :=
  .hook hk hh (.cons (evVar hi) (.cons (evVar hj) .nil))
    (fun vs hvs => by
      obtain rfl : [x, y] = vs := Option.some.inj hvs
      exact Semantics.hookRes_of_value hv)
    (fun h => nomatch h)

/-- A variable's one result is σ's value. -/
theorem evVar_inv {σ : Subst} {i : Nat} {r : Option GroundTerm} (h : EvalTerm d σ (.var i) r) : r = σ.lookup i := by
  cases h; rfl

theorem ws2 (a b : Int) : d.WellSorted [Srt.int, Srt.int] [(0, int a), (1, int b)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 2, hi => simp at hi

theorem ws1 (a : Int) : d.WellSorted [Srt.int] [(0, int a)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 1, hi => simp at hi

theorem ws0 : d.WellSorted [] [] := by
  intro i s hi; simp at hi

/-- `zero => n`, alone among `zero`'s clauses, decides at the empty argument list: `zero` is `n`. -/
theorem eval_zeroOf {n : Int} (hl : d.lookupFn zero = some (fnZero n)) : Eval d zero [] (some (int n)) :=
  .clause (cl := clZero n) (σ := []) hl (List.mem_singleton_self _) ws0 .nil (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      change cl' ∈ [clZero n] at hcl'
      rw [List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .dv (fun _ h => nomatch h) .top

/-- `pu(A, B) => A +Int B`, alone among `pu`'s clauses, decides at every pair of Ints. -/
theorem eval_puOf (hl : d.lookupFn pu = some fnPu) (hk : d.isCtor intAdd = false) (a b : Int) :
    Eval d pu [int a, int b] (some (int (a + b))) :=
  .clause (cl := clPu) (σ := [(0, int a), (1, int b)]) hl (List.mem_singleton_self _) (ws2 a b)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      change cl' ∈ [clPu] at hcl'
      rw [List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evHook2 (i := 0) (j := 1) hk (by decide) rfl rfl rfl) (fun _ h => nomatch h) .top

/-- A variable of sort Int under a well-sorted σ is an Int literal. -/
theorem lookup_int (hs : d.shapesOK = true) (hr : ∀ k ∈ d.params, k.raw = false) (H : HookParams)
    {vars : List Srt} {σ : Subst} (hw : (d.withHooks H).WellSorted vars σ) (i : Nat)
    (hi : vars[i]? = some Srt.int) : ∃ a, σ.lookup i = some (int a) := by
  obtain ⟨v, hv, hsv⟩ := hw i _ hi
  rw [Semantics.sortOf_withHooks d H hr] at hsv
  obtain ⟨a, rfl⟩ := shape_int hs hsv
  exact ⟨a, hv⟩

end

/-- `zero` is 0, under every interpretation. -/
theorem eval_zero (H : HookParams) : Eval (cH H) zero [] (some (int 0)) := eval_zeroOf (look_zero H)

/-- `pu(a, b)` is `a + b` at every pair of Ints, under every interpretation. -/
theorem eval_pu (H : HookParams) (a b : Int) : Eval (cH H) pu [int a, int b] (some (int (a + b))) :=
  eval_puOf (look_pu H) ctor_add a b

theorem ev_zero (H : HookParams) {σ : Subst} : EvalTerm (cH H) σ (.app zero []) (some (int 0)) :=
  evCall0 (d := cH H) ctor_zero (by decide) param_zero (eval_zero H)

/-- Two results of one term that agree on a value: the law's two sides. -/
theorem iff_of (H : HookParams) {σ : Subst} {t u : Term} {v : GroundTerm}
    (ht : EvalTerm (cH H) σ t (some v)) (hu : EvalTerm (cH H) σ u (some v)) (r : Option GroundTerm) :
    EvalTerm (cH H) σ t r ↔ EvalTerm (cH H) σ u r :=
  ⟨fun h => EvalTerm.functional (coherent H) ht h ▸ hu, fun h => EvalTerm.functional (coherent H) hu h ▸ ht⟩

/-! ## The laws at values -/

/-- **The right unit law holds at values, under every interpretation**: `pu(a, zero)` is `a + 0`. -/
theorem unitR_lawAt (H : HookParams) : LawAt (cH H) unitR := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int hsh noRaw H hσ 0 rfl
  have hl : EvalTerm (cH H) σ unitR.lhs (some (int (a + 0))) :=
    evCall2 (d := cH H) ctor_pu (by decide) param_pu (evVar ha) (ev_zero H) (eval_pu H a 0)
  rw [Int.add_zero] at hl
  exact iff_of H hl (evVar ha) r

/-- **The left unit law holds at values, under every interpretation**: `pu(zero, a)` is `0 + a`. -/
theorem unitL_lawAt (H : HookParams) : LawAt (cH H) unitL := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int hsh noRaw H hσ 0 rfl
  have hl : EvalTerm (cH H) σ unitL.lhs (some (int (0 + a))) :=
    evCall2 (d := cH H) ctor_pu (by decide) param_pu (ev_zero H) (evVar ha) (eval_pu H 0 a)
  rw [Int.zero_add] at hl
  exact iff_of H hl (evVar ha) r

/-- **Associativity holds at values, under every interpretation**: both sides are `a + b + d`. -/
theorem assoc_lawAt (H : HookParams) : LawAt (cH H) assocLaw := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int hsh noRaw H hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_int hsh noRaw H hσ 1 rfl
  obtain ⟨e, he⟩ := lookup_int hsh noRaw H hσ 2 rfl
  have hl : EvalTerm (cH H) σ assocLaw.lhs (some (int (a + b + e))) :=
    evCall2 (d := cH H) ctor_pu (by decide) param_pu
      (evCall2 (d := cH H) ctor_pu (by decide) param_pu (evVar ha) (evVar hb) (eval_pu H a b)) (evVar he) (eval_pu H (a + b) e)
  have hr : EvalTerm (cH H) σ assocLaw.rhs (some (int (a + (b + e)))) :=
    evCall2 (d := cH H) ctor_pu (by decide) param_pu
      (evVar ha) (evCall2 (d := cH H) ctor_pu (by decide) param_pu (evVar hb) (evVar he) (eval_pu H b e)) (eval_pu H a (b + e))
  rw [Int.add_assoc] at hl
  exact iff_of H hl hr r

/-- **The text's laws hold at values, under every interpretation**: the `FnLaws` the account lists
as owed for sentences 250 to 252. -/
theorem fnLaws (H : HookParams) : FnLaws (cH H) defn.laws := by
  rw [laws_eq]
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact assoc_lawAt H
  · exact unitR_lawAt H
  · exact unitL_lawAt H

/-! ## Where `zero`'s clause answers 1 -/

/-- The semantics with `zero => 1` in place of `zero => 0`. -/
noncomputable def cOne : Semantics := { c with fns := [fnPu, fnZero 1] }

theorem cOne_ctor_add : cOne.isCtor intAdd = false := ctor_add
theorem cOne_look_pu (H : HookParams) : (cOne.withHooks H).lookupFn pu = some fnPu := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl
theorem cOne_look_zero (H : HookParams) : (cOne.withHooks H).lookupFn zero = some (fnZero 1) := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl

/-- **There the right unit law fails at values, under every interpretation**: at 5, `pu(5, zero)`
is 6, and the right side 5. -/
theorem cOne_not_unitR (H : HookParams) : ¬ LawAt (cOne.withHooks H) unitR := by
  intro h
  have hl : EvalTerm (cOne.withHooks H) [(0, int 5)] unitR.lhs (some (int (5 + 1))) :=
    evCall2 (d := cOne.withHooks H) ctor_pu (by decide) param_pu (evVar (σ := [(0, int 5)]) (i := 0) rfl)
      (evCall0 (d := cOne.withHooks H) ctor_zero (by decide) param_zero (eval_zeroOf (cOne_look_zero H)))
      (eval_puOf (cOne_look_pu H) cOne_ctor_add 5 1)
  have hr := evVar_inv ((h _ (ws1 5) _).mp hl)
  exact absurd hr (by decide)
end KCore.FnUnitKompiled
