/-
  The laws of functions at values on the reader's semantics of two kompiled texts of the fixtures
  e2-fn-assoc-rest and e2-fn-idem (`f2-examples/NAME.kompile.kore`, as test/FnLawFixtures.lean,
  which checks the account's entries for them), for every interpretation H.

  - e2-fn-assoc-rest (`pk(Int, Int) [function, assoc]`, no rule): the reader reads `pk` as a
    parameter no hook implements, its value at two arguments the interpretation's answer, kept where
    it is an Int (`Rest.paramVal_pk`). So the text's associativity law is true or false by the
    interpretation, the account's entry "a condition on the interpretation": true at
    `HookParams.none` (both sides undefined at every three Ints, `Rest.lawAt_none`), true where `pk`
    is Int addition (`Rest.lawAt_add`), false where it is Int subtraction (`Rest.not_lawAt_sub`, at
    (1, 2, 3): -4 against 2).
  - e2-fn-idem (`pm(A, B) => maxInt(A, B)` with `[idem]`): `pm(a, a)` is `max a a = a` by its one
    clause, so the law holds at values under every H (`Idem.fnLaws`), and the theory with the law's
    sentence has a model under every H (`Idem.consistent`, `consistent_with_laws` at the reader's
    `defn.laws`: the text's obligation lists are empty and it has no parameter).

  Run from the package root: `lake env lean -j1 test/FnLawFixturesAt.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnLawFixturesAt

open KCore ML Faithful

/-! ## The laws, shared -/

/-- `f(f(K1, K2), K3) = f(K1, f(K2, K3))`, the text's `[assoc]` axiom of `f`. -/
def assocFL (f : Sym) : LawEq :=
  ⟨[Srt.int, Srt.int, Srt.int], .app f [.app f [.var 0, .var 1], .var 2], .app f [.var 0, .app f [.var 1, .var 2]]⟩

/-- `f(K, K) = K`, the text's `[idem]` axiom of `f`. -/
def idemFL (f : Sym) : LawEq := ⟨[Srt.int], .app f [.var 0, .var 0], .var 0⟩

/-- `f(A, B) => op(A, B)`. -/
def clOpFL (op : Sym) : Clause :=
  ⟨[Srt.int, Srt.int], [.var 0, .var 1], none, .app op [.var 0, .var 1], none, 50, false, [], .top, .top⟩

/-- The function `f`, declared total, with the one clause `f(A, B) => op(A, B)`. -/
def fnOpFL (f op : Sym) : Fn := ⟨f, [Srt.int, Srt.int], Srt.int, [clOpFL op], true⟩

/-! ## Evaluation, shared -/

section
variable {d : Semantics}

theorem evVarFL {σ : Subst} {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) :
    EvalTerm d σ (.var i) (some v) :=
  h ▸ EvalTerm.var

theorem evVarFL_inv {σ : Subst} {i : Nat} {r : Option GroundTerm} (h : EvalTerm d σ (.var i) r) :
    r = σ.lookup i := by
  cases h; rfl

/-- A call of the binary function `f` at two defined arguments. -/
theorem evCall2FL {f : Sym} (hk : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {σ : Subst} {t u : Term} {x y : GroundTerm} {r : Option GroundTerm}
    (ht : EvalTerm d σ t (some x)) (hu : EvalTerm d σ u (some y)) (hf : Eval d f [x, y] r) :
    EvalTerm d σ (.app f [t, u]) r :=
  .call hk hh (.cons ht (.cons hu .nil)) rfl hf hp

/-- A binary interpreted Int symbol at two variables bound to Ints. -/
theorem evHook2FL {op : Sym} (hk : d.isCtor op = false) (hh : isHook op = true) {σ : Subst}
    {i j : Nat} {x y : GroundTerm} {v : GroundTerm} (hi : σ.lookup i = some x) (hj : σ.lookup j = some y)
    (hv : hook op [x, y] = some (some v)) : EvalTerm d σ (.app op [.var i, .var j]) (some v) :=
  .hook hk hh (.cons (evVarFL hi) (.cons (evVarFL hj) .nil))
    (fun vs hvs => by
      obtain rfl : [x, y] = vs := Option.some.inj hvs
      exact Semantics.hookRes_of_value hv)
    (fun h => nomatch h)

theorem ws2FL (a b : Int) : d.WellSorted [Srt.int, Srt.int] [(0, int a), (1, int b)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 2, hi => simp at hi

theorem ws3FL (a b e : Int) : d.WellSorted [Srt.int, Srt.int, Srt.int] [(0, int a), (1, int b), (2, int e)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 2, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 3, hi => simp at hi

/-- `f(A, B) => op(A, B)`, alone among `f`'s clauses, decides at every pair of Ints where `op` is
an interpreted Int symbol with a value there. -/
theorem eval_opFL {f op : Sym} (hl : d.lookupFn f = some (fnOpFL f op)) (hk : d.isCtor op = false)
    (hh : isHook op = true) {a b : Int} {v : GroundTerm} (hv : hook op [int a, int b] = some (some v)) :
    Eval d f [int a, int b] (some v) :=
  .clause (cl := clOpFL op) (σ := [(0, int a), (1, int b)]) hl (List.mem_singleton_self _) (ws2FL a b)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      change cl' ∈ [clOpFL op] at hcl'
      rw [List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evHook2FL (i := 0) (j := 1) hk hh rfl rfl hv) (fun _ h => nomatch h) .top

/-- A variable of sort Int under a well-sorted σ is an Int literal. -/
theorem lookup_intFL (hs : d.shapesOK = true) (hr : ∀ k ∈ d.params, k.raw = false) (H : HookParams)
    {vars : List Srt} {σ : Subst} (hw : (d.withHooks H).WellSorted vars σ) (i : Nat)
    (hi : vars[i]? = some Srt.int) : ∃ a, σ.lookup i = some (int a) := by
  obtain ⟨v, hv, hsv⟩ := hw i _ hi
  rw [Semantics.sortOf_withHooks d H hr] at hsv
  obtain ⟨a, rfl⟩ := shape_int hs hsv
  exact ⟨a, hv⟩

/-- Two terms with one common result under a coherent semantics have the same results. -/
theorem iff_ofFL (hc : CoherentAll d) {σ : Subst} {t u : Term} {v : GroundTerm}
    (ht : EvalTerm d σ t (some v)) (hu : EvalTerm d σ u (some v)) (r : Option GroundTerm) :
    EvalTerm d σ t r ↔ EvalTerm d σ u r :=
  ⟨fun h => EvalTerm.functional hc ht h ▸ hu, fun h => EvalTerm.functional hc hu h ▸ ht⟩

end

/-- The hypotheses of `consistent_with_laws` that do not read the laws, under every
interpretation, for a semantics `coreOK` accepts whose obligation lists are empty and which has no
open generator. -/
theorem model_of_nilFL {c : Semantics} (hc : c.coreOK = true) (hv : c.rightValued = true)
    (h1 : c.rankObligations [] ++ c.decObligationsL = []) (h2 : c.totalObligationsRP [] [] = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = [])
    (h5 : c.params.all (fun k => !k.raw) = true) (H : HookParams) :
    (c.withHooks H).coreOK = true ∧ FnDet (c.withHooks H) ∧ FnSolves (c.withHooks H) ∧
      ClausePreDecided (c.withHooks H) ∧ OpenLaws (c.withHooks H) := by
  have hcH : (c.withHooks H).coreOK = true := (Semantics.coreOK_withHooks _ H).trans hc
  have hob : FnFacts (c.withHooks H) [] [] :=
    FnFacts.of_nil
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact h1)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans h2)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans h3)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans h4) h5
  have hrh := Semantics.rightHeld_withHooks_of_valued hv H
  have hm := fnModel_of_fnFacts hcH hrh hob
  exact ⟨hcH, hm.1, hm.2, clausePreDecided_of_fnFactsN hcH (fun f _ => hrh.heldOwed f) hob, hob.2.2.2.2⟩

/-! ## e2-fn-assoc-rest: `pk` with `[assoc]` and no rule -/

namespace Rest

definition_of defn from "f2-examples/e2-fn-assoc-rest.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def pk : Sym := 384

theorem names : c.symName pk = "Lblpk" := by decide +kernel

theorem laws_eq : defn.laws = [assocFL pk] := by kernel_rfl

/-- `pk` is no function of the text: a parameter no hook implements. -/
theorem pk_param : c.fns = [] ∧ c.isParam pk = true ∧ (c.lookupParam pk).map (·.impl) = some none := by
  decide +kernel

/-! ### The law at values, on the reader's semantics

`pk` is a parameter no hook implements: under H its value at two arguments is H's answer, kept where
it is an Int (`paramVal`). So the law is true or false according to H: true where H gives `pk` no
value (`HookParams.none`: both sides undefined at every Ints), true where H gives it Int addition,
false where H gives it Int subtraction. -/

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem ctor_pk : c.isCtor pk = false := by decide +kernel
theorem hook_pk : isHook pk = false := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-- `pk`'s parameter: no hook implements it, it is no open generator, its result sort is Int. -/
theorem pk_sig : (c.lookupParam pk).map (fun k => (k.impl, k.raw, k.sig.result)) = some (none, false, Srt.int) := by
  decide +kernel

/-- `pk`'s value under H: H's answer, kept where it is of sort Int. -/
theorem paramVal_pk (H : HookParams) (vs : List GroundTerm) :
    (cH H).paramVal pk vs = (H.app pk vs).filter fun v => c.sortOf v == some Srt.int := by
  have hs := pk_sig
  have hl : (cH H).lookupParam pk = c.lookupParam pk := rfl
  unfold Semantics.paramVal
  rw [hl]
  cases hk : c.lookupParam pk with
  | none => rw [hk] at hs; cases hs
  | some k =>
    rw [hk] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hi, hr, hres⟩ := hs
    simp only [hi, hr, hres, Bool.false_eq_true, ite_false, Semantics.sortOf_withHooks c H noRaw]
    rfl

theorem coherent (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans (by decide +kernel))
    ((Semantics.srReady_withHooks c H).trans (by decide +kernel))
    ((Semantics.matchReady_withHooks c H).trans (by decide +kernel))
    ((Semantics.clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

/-- `pk` applied to two terms: the parameter's value at their values (`EvalTerm.param`). -/
theorem evPk {H : HookParams} {σ : Subst} {t u : Term} {x y : Option GroundTerm}
    (ht : EvalTerm (cH H) σ t x) (hu : EvalTerm (cH H) σ u y) :
    EvalTerm (cH H) σ (.app pk [t, u]) ((allSome [x, y]).bind ((cH H).paramVal pk)) :=
  .param ctor_pk hook_pk pk_param.2.1 (.cons ht (.cons hu .nil)) rfl

/-- `pk` at two defined values `a`, `b` where the parameter's value is `v`. -/
theorem evPkVal {H : HookParams} {σ : Subst} {t u : Term} {a b v : GroundTerm}
    (ht : EvalTerm (cH H) σ t (some a)) (hu : EvalTerm (cH H) σ u (some b))
    (hv : (cH H).paramVal pk [a, b] = some v) : EvalTerm (cH H) σ (.app pk [t, u]) (some v) := by
  have h := evPk ht hu
  rwa [show (allSome [some a, some b]).bind ((cH H).paramVal pk) = some v from hv] at h

/-- Where H gives `pk` no value, `pk` applied to anything is undefined. -/
theorem evPkNone {σ : Subst} {t u : Term} {x y : Option GroundTerm}
    (ht : EvalTerm (cH HookParams.none) σ t x) (hu : EvalTerm (cH HookParams.none) σ u y) :
    EvalTerm (cH HookParams.none) σ (.app pk [t, u]) none := by
  have h := evPk ht hu
  have hn : (allSome [x, y]).bind ((cH HookParams.none).paramVal pk) = none := by
    cases allSome [x, y] with
    | none => rfl
    | some ws => rw [Option.bind_some, paramVal_pk]; rfl
  rwa [hn] at h

/-- The interpretation that gives `pk` Int addition. -/
def HaddFL : HookParams := ⟨fun f vs => if f = pk then int2 vs fun x y => some (int (x + y)) else none⟩
/-- The interpretation that gives `pk` Int subtraction. -/
def HsubFL : HookParams := ⟨fun f vs => if f = pk then int2 vs fun x y => some (int (x - y)) else none⟩

theorem pv_add (a b : Int) : (cH HaddFL).paramVal pk [int a, int b] = some (int (a + b)) := by
  rw [paramVal_pk]
  show Option.filter (fun v => c.sortOf v == some Srt.int) (some (int (a + b))) = _
  simp [Option.filter, sortOf_int]

theorem pv_sub (a b : Int) : (cH HsubFL).paramVal pk [int a, int b] = some (int (a - b)) := by
  rw [paramVal_pk]
  show Option.filter (fun v => c.sortOf v == some Srt.int) (some (int (a - b))) = _
  simp [Option.filter, sortOf_int]

/-- **Under `HookParams.none` the law holds**: both sides are undefined at every three Ints. -/
theorem lawAt_none : LawAt (cH HookParams.none) (assocFL pk) := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_intFL shapes noRaw _ hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_intFL shapes noRaw _ hσ 1 rfl
  obtain ⟨e, he⟩ := lookup_intFL shapes noRaw _ hσ 2 rfl
  have hl : EvalTerm (cH HookParams.none) σ (assocFL pk).lhs none :=
    evPkNone (evPkNone (evVarFL ha) (evVarFL hb)) (evVarFL he)
  have hr : EvalTerm (cH HookParams.none) σ (assocFL pk).rhs none :=
    evPkNone (evVarFL ha) (evPkNone (evVarFL hb) (evVarFL he))
  exact ⟨fun h => EvalTerm.functional (coherent _) hl h ▸ hr,
    fun h => EvalTerm.functional (coherent _) hr h ▸ hl⟩

/-- **Under `HaddFL` the law holds**: both sides are `a + b + e`. -/
theorem lawAt_add : LawAt (cH HaddFL) (assocFL pk) := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_intFL shapes noRaw _ hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_intFL shapes noRaw _ hσ 1 rfl
  obtain ⟨e, he⟩ := lookup_intFL shapes noRaw _ hσ 2 rfl
  have hl : EvalTerm (cH HaddFL) σ (assocFL pk).lhs (some (int (a + b + e))) :=
    evPkVal (evPkVal (evVarFL ha) (evVarFL hb) (pv_add a b)) (evVarFL he) (pv_add (a + b) e)
  have hr : EvalTerm (cH HaddFL) σ (assocFL pk).rhs (some (int (a + (b + e)))) :=
    evPkVal (evVarFL ha) (evPkVal (evVarFL hb) (evVarFL he) (pv_add b e)) (pv_add a (b + e))
  rw [Int.add_assoc] at hl
  exact iff_ofFL (coherent _) hl hr r

/-- **Under `HsubFL` the law fails** at (1, 2, 3): the left side is `(1 - 2) - 3 = -4`, the right
side `1 - (2 - 3) = 2`. -/
theorem not_lawAt_sub : ¬ LawAt (cH HsubFL) (assocFL pk) := by
  intro h
  let σ : Subst := [(0, int 1), (1, int 2), (2, int 3)]
  have hl : EvalTerm (cH HsubFL) σ (assocFL pk).lhs (some (int (1 - 2 - 3))) :=
    evPkVal (evPkVal (evVarFL (i := 0) rfl) (evVarFL (i := 1) rfl) (pv_sub 1 2)) (evVarFL (i := 2) rfl)
      (pv_sub (1 - 2) 3)
  have hr : EvalTerm (cH HsubFL) σ (assocFL pk).rhs (some (int (1 - (2 - 3)))) :=
    evPkVal (evVarFL (i := 0) rfl) (evPkVal (evVarFL (i := 1) rfl) (evVarFL (i := 2) rfl) (pv_sub 2 3))
      (pv_sub 1 (2 - 3))
  have hr' := (h σ (ws3FL 1 2 3) _).mp hl
  have := EvalTerm.functional (coherent _) hr hr'
  exact absurd this (by decide)

end Rest

/-! ## e2-fn-idem: `pm(A, B) => maxInt(A, B)` with `[idem]` -/

namespace Idem

definition_of defn from "f2-examples/e2-fn-idem.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def pm : Sym := 384

theorem names : c.symName pm = "Lblpm" := by decide +kernel

theorem laws_eq : defn.laws = [idemFL pm] := by kernel_rfl

theorem sorted : lawSorted c (idemFL pm) = true := by decide +kernel

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK_text : c.coreOK = true := by decide_cheap

/-- The text's one function is `pm` with its clause. -/
theorem fns_eq : c.fns = [fnOpFL pm intMax] := by kernel_rfl

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem ctor_pm : c.isCtor pm = false := by decide +kernel
theorem ctor_max : c.isCtor intMax = false := by decide +kernel
theorem param_pm : c.isParam pm = false := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

theorem coherent (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans (by decide +kernel))
    ((Semantics.srReady_withHooks c H).trans (by decide +kernel))
    ((Semantics.matchReady_withHooks c H).trans (by decide +kernel))
    ((Semantics.clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

theorem look_pm (H : HookParams) : (cH H).lookupFn pm = some (fnOpFL pm intMax) := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl

/-- `pm(a, b)` is `max a b` at every pair of Ints, under every interpretation. -/
theorem eval_pm (H : HookParams) (a b : Int) : Eval (cH H) pm [int a, int b] (some (int (max a b))) :=
  eval_opFL (look_pm H) ctor_max (by decide) rfl

/-- **Idempotence holds at values, under every interpretation**: `pm(a, a)` is `max a a = a`. -/
theorem idem_lawAt (H : HookParams) : LawAt (cH H) (idemFL pm) := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_intFL shapes noRaw H hσ 0 rfl
  have hl : EvalTerm (cH H) σ (idemFL pm).lhs (some (int (max a a))) :=
    evCall2FL (d := cH H) ctor_pm (by decide) param_pm (evVarFL ha) (evVarFL ha) (eval_pm H a a)
  rw [Int.max_self] at hl
  exact iff_ofFL (coherent H) hl (evVarFL ha) r

/-- **The text's laws hold at values, under every interpretation**: the `FnLaws` the account lists
as owed, open, for sentence 249. -/
theorem fnLaws (H : HookParams) : FnLaws (cH H) defn.laws := by
  rw [laws_eq]
  intro l hl
  rw [List.mem_singleton] at hl; subst hl
  exact idem_lawAt H

/-- **The theory of the text with its law's sentence has a model, under every interpretation**:
`consistent_with_laws` at the reader's laws. -/
theorem consistent (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧ ∀ l ∈ defn.laws, I ⊧ᴵ lawPattern (cH H) l :=
  have hm := model_of_nilFL coreOK_text (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) H
  consistent_with_laws hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2 (fnLaws H)
    (fun l hl => by
      rw [laws_eq, List.mem_singleton] at hl; subst hl
      exact (lawSorted_withHooks _ H _).trans sorted)

end Idem

end KCore.FnLawFixturesAt

/-- info: 'KCore.FnLawFixturesAt.Rest.lawAt_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnLawFixturesAt.Rest.lawAt_none
/-- info: 'KCore.FnLawFixturesAt.Rest.lawAt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnLawFixturesAt.Rest.lawAt_add
/-- info: 'KCore.FnLawFixturesAt.Rest.not_lawAt_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnLawFixturesAt.Rest.not_lawAt_sub
/-- info: 'KCore.FnLawFixturesAt.Idem.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnLawFixturesAt.Idem.consistent
