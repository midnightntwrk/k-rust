/-
  Laws of functions at values (`LawAt`, `FnLaws`, Faithful.lean), kernel-checked on semantics built
  by hand from the fixtures' sentences. A law is the text's axiom `\equals{Int,R}(lhs, rhs)` with
  its variables `K1, K2, K3` (or `K`) numbered 0, 1, 2 (or 0); `assocLaw` is the `[assoc]` axiom of
  test/constructs/fixtures/e2-fn-assoc*, `idemLaw` the `[idem]` axiom of e2-fn-idem, each at the one
  function `F : Int × Int → Int`. Each law is `lawSorted` at its semantics (`*_lawSorted`), so no
  statement below holds by a law the context cannot sort, and `coreOK` accepts each semantics
  (`*_coreOK`).

  - `pl` (e2-fn-assoc): `pl(A, B) => A +Int B`, declared total. The clause applies at every pair
    of Ints, so no rest is read: `LawAt` holds under every interpretation (`pl_lawAt`, and
    `pl_fnLaws` for the list of the text's one law); at (1, 2, 3) both sides are 6 (`pl_at_123`).
  - `plBad` (e2-fn-assoc-bad): `pl(A, B) => A -Int B`. Under every interpretation `LawAt` fails at
    (1, 2, 3): the left side is -4, the right side 2 (`plBad_not_lawAt`).
  - `pk` (e2-fn-assoc-rest): `pk` with no equation, not total: its value everywhere is the
    interpretation's rest, so `LawAt` is a condition on the interpretation. It holds at
    `HookParams.none` (both sides undefined, `pk_lawAt_none`) and at `Hadd`, which gives `pk` Int
    addition (`pk_lawAt_add`); it fails at `Hsub`, which gives it subtraction, at (1, 2, 3)
    (`pk_not_lawAt_sub`).
  - `mx`: `mx(X, Y) => X requires X >Int Y`, with `[idem]`. At (2, 2) the clause fails and the
    value is the rest; the text's law says `mx(2, 2) = 2`. `LawAt` fails at `HookParams.none` (no
    value against 2, `mx_not_lawAt_none`) and at `H7`, which answers 7 there (`mx_not_lawAt_H7`);
    it holds at `Hfst`, which answers the first argument (`mx_lawAt_fst`): the interpretations the
    law admits are those with `mx(a, a) = a` where the clause fails.

  Where the law holds at values the theory with the law's sentence has a model
  (`consistent_with_laws`, LawConsistent.lean), at these semantics: `pl` under every interpretation
  (`pl_consistent_with_laws`), `pk` under `Hadd` (`pk_consistent_with_laws_add`), `mx` under `Hfst`
  (`mx_consistent_with_laws_fst`). The hypotheses are `coreOK` by the kernel, `FnDet`, `FnSolves`
  and `OpenLaws` from `FnFacts.of_nil` (no function is named, no parameter is open), `FnLaws` by
  the statements above and `lawSorted` by the kernel.

  A law over a sort that is none of the definition's is not sorted (`unnumbered`): `wn` has a sort
  `nRegSorts + 2` whose name is the empty string and which has two constructors, `coreOK` accepts
  it, and the sort 9999, none of its sorts, has the same name (`wn_sortName`). `badLaw` is
  `x = y` at two variables of the sort 9999: both sides have the sort 9999 in the context of right
  sides and each variable occurs (`badLaw_sides`), and its sentence is the sentence of `x = y` at
  the sort `nRegSorts + 2` (`badLaw_pattern`). `lawSorted` refuses it (`badLaw_not_lawSorted`)
  and accepts the law at the sort `nRegSorts + 2` (`realLaw_lawSorted`), which `LawAt` refutes at
  the two constructors (`realLaw_not_lawAt`). Not shown here: that `LawAt` holds of `badLaw`, and
  that the theory refutes the sentence.

  Run from the package root: `lake env lean test/FnLawAt.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnLawAtTest

open KCore ML Faithful

/-! ## The shared parts -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The one function of each semantics below. -/
def F : Sym := nRegSyms + 4

/-- The semantics whose one function is `fn`, with no rule: the two cell sorts and the symbols
(the cell sorts' predicates, the two cell constructors, `F`) named, so that `coreOK` accepts it. -/
def mkSem (fn : Fn) : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := ["KCell", "KCellOpt"]
  symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblF"]
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fn]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- No parameter of `mkSem fn` is an open generator: it has no parameter. -/
theorem mkSem_rawFree (fn : Fn) : ∀ k ∈ (mkSem fn).params, k.raw = false := by
  intro k hk; cases hk

/-- `F(F(K1, K2), K3) = F(K1, F(K2, K3))`. -/
def assocLaw : LawEq :=
  ⟨[Srt.int, Srt.int, Srt.int], .app F [.app F [.var 0, .var 1], .var 2],
    .app F [.var 0, .app F [.var 1, .var 2]]⟩

/-- `F(K, K) = K`. -/
def idemLaw : LawEq := ⟨[Srt.int], .app F [.var 0, .var 0], .var 0⟩

def σ2 (a b : Int) : Subst := [(0, int a), (1, int b)]
def σ3 (a b d : Int) : Subst := [(0, int a), (1, int b), (2, int d)]

section
variable {c : Semantics}

theorem evVar {σ : Subst} {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) :
    EvalTerm c σ (.var i) (some v) :=
  h ▸ EvalTerm.var

theorem evCall2 (hk : c.isCtor F = false) (hp : c.isParam F = false) {σ : Subst} {t u : Term}
    {x y : GroundTerm} {r : Option GroundTerm}
    (ht : EvalTerm c σ t (some x)) (hu : EvalTerm c σ u (some y)) (hf : Eval c F [x, y] r) :
    EvalTerm c σ (.app F [t, u]) r :=
  .call hk (by decide) (.cons ht (.cons hu .nil)) rfl hf hp

theorem evUndefL (hk : c.isCtor F = false) (hp : c.isParam F = false) {σ : Subst} {t u : Term}
    {ru : Option GroundTerm} (ht : EvalTerm c σ t none) (hu : EvalTerm c σ u ru) :
    EvalTerm c σ (.app F [t, u]) none :=
  .callUndef hk (by decide) (.cons ht (.cons hu .nil)) rfl hp

theorem evUndefR (hk : c.isCtor F = false) (hp : c.isParam F = false) {σ : Subst} {t u : Term}
    {x : GroundTerm} (ht : EvalTerm c σ t (some x)) (hu : EvalTerm c σ u none) :
    EvalTerm c σ (.app F [t, u]) none :=
  .callUndef hk (by decide) (.cons ht (.cons hu .nil)) rfl hp

/-- A binary interpreted Int symbol at two variables bound to Ints. -/
theorem evHook2 {op : Sym} (hk : c.isCtor op = false) (hh : isHook op = true) {σ : Subst}
    {i j : Nat} {x y : GroundTerm} {v : GroundTerm} (hi : σ.lookup i = some x) (hj : σ.lookup j = some y)
    (hv : hook op [x, y] = some (some v)) : EvalTerm c σ (.app op [.var i, .var j]) (some v) :=
  .hook hk hh (.cons (evVar hi) (.cons (evVar hj) .nil))
    (fun vs hvs => by
      obtain rfl : [x, y] = vs := Option.some.inj hvs
      exact Semantics.hookRes_of_value hv)
    (fun h => nomatch h)

/-- A variable of sort Int under a well-sorted σ is an Int literal. -/
theorem lookup_int (hs : c.shapesOK = true) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams) {vars : List Srt} {σ : Subst}
    (hw : (c.withHooks H).WellSorted vars σ) (i : Nat) (hi : vars[i]? = some Srt.int) :
    ∃ a, σ.lookup i = some (int a) := by
  obtain ⟨v, hv, hsv⟩ := hw i _ hi
  rw [Semantics.sortOf_withHooks c H hr] at hsv
  obtain ⟨a, rfl⟩ := shape_int hs hsv
  exact ⟨a, hv⟩

theorem ws2 (a b : Int) : c.WellSorted [Srt.int, Srt.int] (σ2 a b) := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 2, hi => simp at hi

theorem ws3 (a b d : Int) : c.WellSorted [Srt.int, Srt.int, Srt.int] (σ3 a b d) := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 2, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 3, hi => simp at hi

theorem ws1 (a : Int) : c.WellSorted [Srt.int] [(0, int a)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 1, hi => simp at hi

end

/-- The facts every semantics `mkSem fn` below needs, under every interpretation. -/
structure Ready (fn : Fn) : Prop where
  ok : (mkSem fn).ok = true
  sr : (mkSem fn).srReady = true
  mr : (mkSem fn).matchReady = true
  cf : (mkSem fn).clausesFixed = true
  ag : (mkSem fn).agreeObligations = []
  sh : (mkSem fn).shapesOK = true
  ctor : (mkSem fn).isCtor F = false
  param : (mkSem fn).isParam F = false
  look : (mkSem fn).lookupFn F = some fn

theorem Ready.coherent {fn : Fn} (h : Ready fn) (H : HookParams) : CoherentAll ((mkSem fn).withHooks H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks _ H).trans h.ok) ((Semantics.srReady_withHooks _ H).trans h.sr)
    ((Semantics.matchReady_withHooks _ H).trans h.mr) ((Semantics.clausesFixed_withHooks _ H).trans h.cf)
    ((Semantics.agreeObligations_withHooks _ H).trans h.ag)

theorem Ready.lookH {fn : Fn} (h : Ready fn) (H : HookParams) :
    ((mkSem fn).withHooks H).lookupFn F = some fn := by
  rw [Semantics.lookupFn_withHooks]; exact h.look

theorem Ready.ctorH {fn : Fn} (h : Ready fn) (H : HookParams) : ((mkSem fn).withHooks H).isCtor F = false :=
  h.ctor

theorem Ready.paramH {fn : Fn} (h : Ready fn) (H : HookParams) : ((mkSem fn).withHooks H).isParam F = false :=
  h.param

/-- `F(F(x0, x1), x2)` from the three calls' results. -/
theorem Ready.lhs3 {fn : Fn} (h : Ready fn) (H : HookParams) {σ : Subst} {a b d ab : GroundTerm}
    {r : Option GroundTerm} (ha : σ.lookup 0 = some a) (hb : σ.lookup 1 = some b) (hd : σ.lookup 2 = some d)
    (h1 : Eval ((mkSem fn).withHooks H) F [a, b] (some ab)) (h2 : Eval ((mkSem fn).withHooks H) F [ab, d] r) :
    EvalTerm ((mkSem fn).withHooks H) σ assocLaw.lhs r :=
  evCall2 (h.ctorH H) (h.paramH H) (evCall2 (h.ctorH H) (h.paramH H) (evVar ha) (evVar hb) h1) (evVar hd) h2

/-- `F(x0, F(x1, x2))` from the three calls' results. -/
theorem Ready.rhs3 {fn : Fn} (h : Ready fn) (H : HookParams) {σ : Subst} {a b d bd : GroundTerm}
    {r : Option GroundTerm} (ha : σ.lookup 0 = some a) (hb : σ.lookup 1 = some b) (hd : σ.lookup 2 = some d)
    (h1 : Eval ((mkSem fn).withHooks H) F [b, d] (some bd)) (h2 : Eval ((mkSem fn).withHooks H) F [a, bd] r) :
    EvalTerm ((mkSem fn).withHooks H) σ assocLaw.rhs r :=
  evCall2 (h.ctorH H) (h.paramH H) (evVar ha) (evCall2 (h.ctorH H) (h.paramH H) (evVar hb) (evVar hd) h1) h2

/-! ## `pl(A, B) => A +Int B` and `pl(A, B) => A -Int B` -/

/-- `pl(A, B) => op(A, B)`. -/
def clPl (op : Sym) : Clause :=
  ⟨[Srt.int, Srt.int], [.var 0, .var 1], none, .app op [.var 0, .var 1], none, 50, false, [], .top, .top⟩
def fnPl (op : Sym) : Fn := ⟨F, [Srt.int, Srt.int], Srt.int, [clPl op], true⟩

abbrev pl : Semantics := mkSem (fnPl intAdd)
abbrev plBad : Semantics := mkSem (fnPl intSub)

theorem ready_pl : Ready (fnPl intAdd) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
theorem ready_plBad : Ready (fnPl intSub) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

theorem pl_lawSorted : lawSorted pl assocLaw = true := by decide +kernel
theorem plBad_lawSorted : lawSorted plBad assocLaw = true := by decide +kernel

/-- The clause decides at every pair of Ints, under every interpretation: `op`'s value. -/
theorem eval_pl {op : Sym} (hr : Ready (fnPl op)) (hk : (mkSem (fnPl op)).isCtor op = false)
    (hh : isHook op = true) (H : HookParams) (a b : Int) {v : GroundTerm}
    (hv : hook op [int a, int b] = some (some v)) :
    Eval ((mkSem (fnPl op)).withHooks H) F [int a, int b] (some v) :=
  .clause (cl := clPl op) (σ := σ2 a b) (hr.lookH H) (List.mem_singleton_self _) (ws2 a b)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      change cl' ∈ [clPl op] at hcl'
      rw [List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evHook2 (c := (mkSem (fnPl op)).withHooks H) (σ := σ2 a b) (i := 0) (j := 1) hk hh rfl rfl hv)
    (fun _ h => nomatch h) .top

theorem eval_plAdd (H : HookParams) (a b : Int) : Eval (pl.withHooks H) F [int a, int b] (some (int (a + b))) :=
  eval_pl ready_pl (by decide +kernel) (by decide +kernel) H a b rfl

theorem eval_plSub (H : HookParams) (a b : Int) : Eval (plBad.withHooks H) F [int a, int b] (some (int (a - b))) :=
  eval_pl ready_plBad (by decide +kernel) (by decide +kernel) H a b rfl

/-- **Associativity of `pl` at values, under every interpretation**: at Ints a, b, d both sides are
`a + b + d`. -/
theorem pl_lawAt (H : HookParams) : LawAt (pl.withHooks H) assocLaw := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int ready_pl.sh (mkSem_rawFree _) H hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_int ready_pl.sh (mkSem_rawFree _) H hσ 1 rfl
  obtain ⟨d, hd⟩ := lookup_int ready_pl.sh (mkSem_rawFree _) H hσ 2 rfl
  have hl := ready_pl.lhs3 H ha hb hd (eval_plAdd H a b) (eval_plAdd H (a + b) d)
  have hr := ready_pl.rhs3 H ha hb hd (eval_plAdd H b d) (eval_plAdd H a (b + d))
  rw [Int.add_assoc] at hl
  exact ⟨fun h => EvalTerm.functional (ready_pl.coherent H) hl h ▸ hr,
    fun h => EvalTerm.functional (ready_pl.coherent H) hr h ▸ hl⟩

/-- The text's one law of `pl`, under every interpretation. -/
theorem pl_fnLaws (H : HookParams) : FnLaws (pl.withHooks H) [assocLaw] := fun l hl => by
  rw [List.mem_singleton] at hl; subst hl; exact pl_lawAt H

/-- At (1, 2, 3) both sides are 6. -/
theorem pl_at_123 (H : HookParams) :
    EvalTerm (pl.withHooks H) (σ3 1 2 3) assocLaw.lhs (some (int 6)) ∧
      EvalTerm (pl.withHooks H) (σ3 1 2 3) assocLaw.rhs (some (int 6)) :=
  ⟨ready_pl.lhs3 H rfl rfl rfl (eval_plAdd H 1 2) (eval_plAdd H 3 3),
    ready_pl.rhs3 H rfl rfl rfl (eval_plAdd H 2 3) (eval_plAdd H 1 5)⟩

/-- **`pl(A, B) => A -Int B` is not associative at values, under every interpretation**: at
(1, 2, 3) the left side is `(1 - 2) - 3 = -4` and the right side `1 - (2 - 3) = 2`. -/
theorem plBad_not_lawAt (H : HookParams) : ¬ LawAt (plBad.withHooks H) assocLaw := by
  intro h
  have hl := ready_plBad.lhs3 H (σ := σ3 1 2 3) rfl rfl rfl (eval_plSub H 1 2) (eval_plSub H (1 - 2) 3)
  have hr := ready_plBad.rhs3 H (σ := σ3 1 2 3) rfl rfl rfl (eval_plSub H 2 3) (eval_plSub H 1 (2 - 3))
  have he := EvalTerm.functional (ready_plBad.coherent H) hr ((h _ (ws3 1 2 3) _).mp hl)
  exact absurd he (by decide)

/-! ## `pk`, with no equation -/

def fnPk : Fn := ⟨F, [Srt.int, Srt.int], Srt.int, [], false⟩

abbrev pk : Semantics := mkSem fnPk

theorem ready_pk : Ready fnPk :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

theorem pk_lawSorted : lawSorted pk assocLaw = true := by decide +kernel

/-- The interpretation that gives `pk` Int addition. -/
def Hadd : HookParams := ⟨fun f vs => if f = F then int2 vs fun x y => some (int (x + y)) else none⟩
/-- The interpretation that gives `pk` Int subtraction. -/
def Hsub : HookParams := ⟨fun f vs => if f = F then int2 vs fun x y => some (int (x - y)) else none⟩

/-- No clause, so `pk`'s value is its rest, under every interpretation. -/
theorem eval_pk (H : HookParams) (vs : List GroundTerm) :
    Eval (pk.withHooks H) F vs ((pk.withHooks H).fnRest fnPk vs) :=
  .rest (ready_pk.lookH H) fun _ h => nomatch h

theorem eval_pk_none (a b : Int) : Eval (pk.withHooks HookParams.none) F [int a, int b] none :=
  Semantics.fnRest_withHooks_none pk fnPk _ ▸ eval_pk HookParams.none [int a, int b]

/-- The rest of `F : Int × Int → Int` at two Ints is the interpretation's value there. -/
theorem fnRest2 {fn : Fn} (hl : fn.label = F) (ha : fn.args = [Srt.int, Srt.int])
    (hres : fn.result = Srt.int) {g : Int → Int → Int} {H : HookParams}
    (hH : ∀ a b, H.app F [int a, int b] = some (int (g a b))) (a b : Int) :
    ((mkSem fn).withHooks H).fnRest fn [int a, int b] = some (int (g a b)) := by
  have hs : ((mkSem fn).withHooks H).sortsOf [int a, int b] = some [Srt.int, Srt.int] := by
    rw [Semantics.sortsOf_withHooks _ H (mkSem_rawFree fn)]; simp [Semantics.sortsOf, sortOf_int]
  show (H.app fn.label [int a, int b]).filter (fun v => ((mkSem fn).withHooks H).sortsOf [int a, int b] ==
    some fn.args && ((mkSem fn).withHooks H).sortOf v == some fn.result) = _
  rw [hl, hH, hs, ha, hres]; simp [sortOf_int]

theorem eval_pk_add (a b : Int) : Eval (pk.withHooks Hadd) F [int a, int b] (some (int (a + b))) :=
  fnRest2 (fn := fnPk) rfl rfl rfl (H := Hadd) (fun _ _ => rfl) a b ▸ eval_pk Hadd [int a, int b]

theorem eval_pk_sub (a b : Int) : Eval (pk.withHooks Hsub) F [int a, int b] (some (int (a - b))) :=
  fnRest2 (fn := fnPk) rfl rfl rfl (H := Hsub) (fun _ _ => rfl) a b ▸ eval_pk Hsub [int a, int b]

/-- **Under `HookParams.none` the law holds of `pk`**: both sides are undefined at every Ints. -/
theorem pk_lawAt_none : LawAt (pk.withHooks HookParams.none) assocLaw := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int ready_pk.sh (mkSem_rawFree _) _ hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_int ready_pk.sh (mkSem_rawFree _) _ hσ 1 rfl
  obtain ⟨d, hd⟩ := lookup_int ready_pk.sh (mkSem_rawFree _) _ hσ 2 rfl
  have k := ready_pk.ctorH HookParams.none
  have p := ready_pk.paramH HookParams.none
  have hl : EvalTerm _ σ assocLaw.lhs none :=
    evUndefL k p (evCall2 k p (evVar ha) (evVar hb) (eval_pk_none a b)) (evVar hd)
  have hr : EvalTerm _ σ assocLaw.rhs none :=
    evUndefR k p (evVar ha) (evCall2 k p (evVar hb) (evVar hd) (eval_pk_none b d))
  exact ⟨fun h => EvalTerm.functional (ready_pk.coherent _) hl h ▸ hr,
    fun h => EvalTerm.functional (ready_pk.coherent _) hr h ▸ hl⟩

/-- **Under `Hadd` the law holds of `pk`**: both sides are `a + b + d`. -/
theorem pk_lawAt_add : LawAt (pk.withHooks Hadd) assocLaw := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int ready_pk.sh (mkSem_rawFree _) _ hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_int ready_pk.sh (mkSem_rawFree _) _ hσ 1 rfl
  obtain ⟨d, hd⟩ := lookup_int ready_pk.sh (mkSem_rawFree _) _ hσ 2 rfl
  have hl := ready_pk.lhs3 Hadd ha hb hd (eval_pk_add a b) (eval_pk_add (a + b) d)
  have hr := ready_pk.rhs3 Hadd ha hb hd (eval_pk_add b d) (eval_pk_add a (b + d))
  rw [Int.add_assoc] at hl
  exact ⟨fun h => EvalTerm.functional (ready_pk.coherent _) hl h ▸ hr,
    fun h => EvalTerm.functional (ready_pk.coherent _) hr h ▸ hl⟩

/-- **Under `Hsub` the law fails for `pk`** at (1, 2, 3): -4 against 2. -/
theorem pk_not_lawAt_sub : ¬ LawAt (pk.withHooks Hsub) assocLaw := by
  intro h
  have hl := ready_pk.lhs3 Hsub (σ := σ3 1 2 3) rfl rfl rfl (eval_pk_sub 1 2) (eval_pk_sub (1 - 2) 3)
  have hr := ready_pk.rhs3 Hsub (σ := σ3 1 2 3) rfl rfl rfl (eval_pk_sub 2 3) (eval_pk_sub 1 (2 - 3))
  have he := EvalTerm.functional (ready_pk.coherent _) hr ((h _ (ws3 1 2 3) _).mp hl)
  exact absurd he (by decide)

/-! ## `mx(X, Y) => X requires X >Int Y`, with `[idem]` -/

/-- `mx(X, Y) => X requires X >Int Y`. -/
def clMx : Clause :=
  ⟨[Srt.int, Srt.int], [.var 0, .var 1], some (.app intGt [.var 0, .var 1]), .var 0, none, 50, false, [],
    .top, .top⟩
def fnMx : Fn := ⟨F, [Srt.int, Srt.int], Srt.int, [clMx], false⟩

abbrev mx : Semantics := mkSem fnMx

theorem ready_mx : Ready fnMx :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

theorem mx_lawSorted : lawSorted mx idemLaw = true := by decide +kernel

/-- At `(a, a)` the clause fails under every interpretation: `a >Int a` is `false`. -/
theorem mx_fails (H : HookParams) (a : Int) : Fails (mx.withHooks H) [int a, int a] clMx := by
  refine .intro fun σ _ hp => ?_
  cases hp with
  | cons h0 hs => cases hs with
    | cons h1 _ => cases h0 with
      | var e0 => cases h1 with
        | var e1 =>
          have hv : hook intGt [int a, int a] = some (some (bool false)) := by
            show some (int2 [int a, int a] fun x y => some (bool (decide (x > y)))) = _
            simp [int2, asInt, int]
          have hk : mx.isCtor intGt = false := by decide +kernel
          exact .intro rfl (evHook2 (c := mx.withHooks H) (i := 0) (j := 1) hk (by decide +kernel) e0 e1 hv)
            (by decide)

/-- So `mx(a, a)` is the rest, under every interpretation. -/
theorem eval_mx (H : HookParams) (a : Int) :
    Eval (mx.withHooks H) F [int a, int a] ((mx.withHooks H).fnRest fnMx [int a, int a]) :=
  .rest (ready_mx.lookH H) fun cl hcl => by
    change cl ∈ [clMx] at hcl
    rw [List.mem_singleton] at hcl; subst hcl; exact mx_fails H a

/-- The interpretation that answers 7 at `mx`. -/
def H7 : HookParams := ⟨fun f _ => if f = F then some (int 7) else none⟩
/-- The interpretation that answers the first argument at `mx`. -/
def Hfst : HookParams := ⟨fun f vs => if f = F then (match vs with | [a, _] => some a | _ => none) else none⟩

theorem eval_mx_H7 : Eval (mx.withHooks H7) F [int 2, int 2] (some (int 7)) :=
  fnRest2 (fn := fnMx) rfl rfl rfl (g := fun _ _ => 7) (H := H7) (fun _ _ => rfl) 2 2 ▸ eval_mx H7 2

/-- **Under `HookParams.none` the law fails for `mx`** at 2: the left side has no value, the right
side is 2. -/
theorem mx_not_lawAt_none : ¬ LawAt (mx.withHooks HookParams.none) idemLaw := by
  intro h
  have k := ready_mx.ctorH HookParams.none
  have p := ready_mx.paramH HookParams.none
  have hl : EvalTerm _ [(0, int 2)] idemLaw.lhs none :=
    evCall2 k p (evVar rfl) (evVar rfl) (Semantics.fnRest_withHooks_none mx fnMx _ ▸ eval_mx HookParams.none 2)
  have hr : EvalTerm (mx.withHooks HookParams.none) [(0, int 2)] idemLaw.rhs (some (int 2)) := evVar rfl
  have he := EvalTerm.functional (ready_mx.coherent _) hl ((h _ (ws1 2) _).mpr hr)
  exact absurd he (by decide)

/-- **Under `H7` the law fails for `mx`** at 2: the left side is 7, the right side 2. -/
theorem mx_not_lawAt_H7 : ¬ LawAt (mx.withHooks H7) idemLaw := by
  intro h
  have k := ready_mx.ctorH H7
  have p := ready_mx.paramH H7
  have hl : EvalTerm _ [(0, int 2)] idemLaw.lhs (some (int 7)) := evCall2 k p (evVar rfl) (evVar rfl) eval_mx_H7
  have hr : EvalTerm (mx.withHooks H7) [(0, int 2)] idemLaw.rhs (some (int 2)) := evVar rfl
  have he := EvalTerm.functional (ready_mx.coherent _) hl ((h _ (ws1 2) _).mpr hr)
  exact absurd he (by decide)

/-- **Under `Hfst` the law holds of `mx`**: at every Int a both sides are a. -/
theorem mx_lawAt_fst : LawAt (mx.withHooks Hfst) idemLaw := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_int ready_mx.sh (mkSem_rawFree _) _ hσ 0 rfl
  have hl : EvalTerm _ σ idemLaw.lhs (some (int a)) :=
    evCall2 (ready_mx.ctorH Hfst) (ready_mx.paramH Hfst) (evVar ha) (evVar ha)
      (fnRest2 (fn := fnMx) rfl rfl rfl (g := fun x _ => x) (H := Hfst) (fun _ _ => rfl) a a ▸ eval_mx Hfst a)
  have hr : EvalTerm (mx.withHooks Hfst) σ idemLaw.rhs (some (int a)) := evVar ha
  exact ⟨fun h => EvalTerm.functional (ready_mx.coherent _) hl h ▸ hr,
    fun h => EvalTerm.functional (ready_mx.coherent _) hr h ▸ hl⟩

/-! ## The theory with the law's sentence has a model -/

theorem pl_coreOK : pl.coreOK = true := by decide_cheap
theorem plBad_coreOK : plBad.coreOK = true := by decide_cheap
theorem pk_coreOK : pk.coreOK = true := by decide_cheap
theorem mx_coreOK : mx.coreOK = true := by decide_cheap

/-- The hypotheses of `consistent_with_laws` that do not read the law, for a semantics `mkSem fn`
that `coreOK` accepts and none of whose functions is named by an obligation list, under every
interpretation. -/
theorem mkSem_model {fn : Fn} (hc : (mkSem fn).coreOK = true) (hv : (mkSem fn).rightValued = true)
    (h1 : (mkSem fn).rankObligations [] ++ (mkSem fn).decObligationsL = [])
    (h2 : (mkSem fn).totalObligationsRP [] [] = []) (h3 : (mkSem fn).agreeObligationsI = [])
    (h4 : (mkSem fn).matchObligationsL = []) (H : HookParams) :
    ((mkSem fn).withHooks H).coreOK = true ∧ FnDet ((mkSem fn).withHooks H) ∧
      FnSolves ((mkSem fn).withHooks H) ∧ ClausePreDecided ((mkSem fn).withHooks H) ∧
      OpenLaws ((mkSem fn).withHooks H) := by
  have hcH : ((mkSem fn).withHooks H).coreOK = true := (Semantics.coreOK_withHooks _ H).trans hc
  have hob : FnFacts ((mkSem fn).withHooks H) [] [] :=
    FnFacts.of_nil
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact h1)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans h2)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans h3)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans h4)
      (List.all_eq_true.mpr fun k hk => by rw [mkSem_rawFree fn k hk]; rfl)
  have hm := fnModel_of_fnFacts hcH (Semantics.rightHeld_withHooks_of_valued hv H) hob
  have hrh := Semantics.rightHeld_withHooks_of_valued hv H
  exact ⟨hcH, hm.1, hm.2, clausePreDecided_of_fnFactsN hcH (fun f _ => hrh.heldOwed f) hob, hob.2.2.2.2⟩

/-- `consistent_with_laws` at one law of `mkSem fn` under H. -/
theorem mkSem_consistent_with_laws {fn : Fn} {H : HookParams} {l : LawEq}
    (hm : ((mkSem fn).withHooks H).coreOK = true ∧ FnDet ((mkSem fn).withHooks H) ∧
      FnSolves ((mkSem fn).withHooks H) ∧ ClausePreDecided ((mkSem fn).withHooks H) ∧
      OpenLaws ((mkSem fn).withHooks H))
    (hl : LawAt ((mkSem fn).withHooks H) l) (hs : lawSorted (mkSem fn) l = true) :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc ((mkSem fn).withHooks H) ∪ Γstep ((mkSem fn).withHooks H))) ∧
        ∀ l' ∈ [l], I ⊧ᴵ lawPattern ((mkSem fn).withHooks H) l' :=
  consistent_with_laws hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2
    (fun l' hl' => by rw [List.mem_singleton] at hl'; subst hl'; exact hl)
    (fun l' hl' => by rw [List.mem_singleton] at hl'; subst hl'; exact (lawSorted_withHooks _ H _).trans hs)

/-- **The theory of `pl` with its associativity sentence has a model, under every
interpretation.** -/
theorem pl_consistent_with_laws (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (pl.withHooks H) ∪ Γstep (pl.withHooks H))) ∧
        ∀ l ∈ [assocLaw], I ⊧ᴵ lawPattern (pl.withHooks H) l :=
  mkSem_consistent_with_laws
    (mkSem_model pl_coreOK (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) H)
    (pl_lawAt H) pl_lawSorted

/-- **The theory of `pk` with its associativity sentence has a model under `Hadd`**, where the
law is a condition on the interpretation. -/
theorem pk_consistent_with_laws_add :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (pk.withHooks Hadd) ∪ Γstep (pk.withHooks Hadd))) ∧
        ∀ l ∈ [assocLaw], I ⊧ᴵ lawPattern (pk.withHooks Hadd) l :=
  mkSem_consistent_with_laws
    (mkSem_model pk_coreOK (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) Hadd)
    pk_lawAt_add pk_lawSorted

/-- **The theory of `mx` with its idempotence sentence has a model under `Hfst`**, which gives
`mx(a, a)` the value the law states where the clause fails. -/
theorem mx_consistent_with_laws_fst :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (mx.withHooks Hfst) ∪ Γstep (mx.withHooks Hfst))) ∧
        ∀ l ∈ [idemLaw], I ⊧ᴵ lawPattern (mx.withHooks Hfst) l :=
  mkSem_consistent_with_laws
    (mkSem_model mx_coreOK (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) Hfst)
    mx_lawAt_fst mx_lawSorted

/-! ## A law over a sort that is none of the definition's -/

/-- The first constructor of `wn`'s sort. -/
def wnA : Sym := nRegSyms + 5
/-- The second constructor of `wn`'s sort. -/
def wnB : Sym := nRegSyms + 6

/-- The cell sorts and constructors with one more sort, `nRegSorts + 2`, named by the empty string,
and its two nullary constructors; no function, rule or parameter. -/
def wn : Semantics where
  lib := {}
  sortNames := ["KCell", "KCellOpt", ""]
  symNames := ["LblisKCell", "LblisKCellOpt", "Lblis", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx", "Lbly"]
  userSorts := cellSorts ++ [nRegSorts + 2]
  ctors :=
    [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
     ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
     ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩,
     ⟨wnA, [], nRegSorts + 2⟩, ⟨wnB, [], nRegSorts + 2⟩]
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- `x = y` at two variables of the sort 9999, which is none of `wn`'s. -/
def badLaw : LawEq := ⟨[9999, 9999], .var 0, .var 1⟩
/-- `x = y` at two variables of `wn`'s sort `nRegSorts + 2`. -/
def realLaw : LawEq := ⟨[nRegSorts + 2, nRegSorts + 2], .var 0, .var 1⟩

theorem wn_coreOK : wn.coreOK = true := by decide_cheap

/-- The sort 9999 is none of `wn`'s, and has the name of `wn`'s sort `nRegSorts + 2`. -/
theorem wn_sortName : ¬ 9999 < nRegSorts + wn.sortNames.length ∧
    wn.sortName 9999 = wn.sortName (nRegSorts + 2) := by decide +kernel

/-- Both sides of `badLaw` have the sort 9999 in the context of right sides, and each of its
variables occurs in a side. -/
theorem badLaw_sides :
    sortOfTerm (wn.rhsCtx (wn.fns.map Fn.sig)) badLaw.vars badLaw.lhs = some 9999 ∧
    sortOfTerm (wn.rhsCtx (wn.fns.map Fn.sig)) badLaw.vars badLaw.rhs = some 9999 ∧
    binds badLaw.vars.length (varOccs badLaw.lhs ++ varOccs badLaw.rhs) = true := by decide +kernel

/-- `badLaw`'s sentence is `realLaw`'s: the variables' guards and the equation's sort are written
by name. -/
theorem badLaw_pattern : lawPattern wn badLaw = lawPattern wn realLaw := by decide +kernel

/-- **`lawSorted` refuses the law over the sort that is none of the definition's.** -/
theorem badLaw_not_lawSorted : lawSorted wn badLaw = false := by decide +kernel

/-- The same equation at the definition's sort is sorted. -/
theorem realLaw_lawSorted : lawSorted wn realLaw = true := by decide +kernel

/-- **`LawAt` refutes it there**, under every interpretation: at the two constructors the left
side is the first and the right side the second. -/
theorem realLaw_not_lawAt (H : HookParams) : ¬ LawAt (wn.withHooks H) realLaw := by
  intro h
  have hw : (wn.withHooks H).WellSorted realLaw.vars [(0, .ctor wnA []), (1, .ctor wnB [])] := by
    intro i s hi
    match i, hi with
    | 0, hi =>
      cases hi
      exact ⟨_, rfl, by rw [Semantics.sortOf_withHooks wn H (fun k hk => nomatch hk)]; decide +kernel⟩
    | 1, hi =>
      cases hi
      exact ⟨_, rfl, by rw [Semantics.sortOf_withHooks wn H (fun k hk => nomatch hk)]; decide +kernel⟩
    | n + 2, hi => simp [realLaw] at hi
  have hl : EvalTerm (wn.withHooks H) [(0, .ctor wnA []), (1, .ctor wnB [])] realLaw.lhs (some (.ctor wnA [])) :=
    evVar rfl
  cases (h _ hw _).mp hl

/-! ## Axioms -/

/-- info: 'KCore.FnLawAtTest.pl_lawAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pl_lawAt
/-- info: 'KCore.FnLawAtTest.pl_fnLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pl_fnLaws
/-- info: 'KCore.FnLawAtTest.pl_at_123' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pl_at_123
/-- info: 'KCore.FnLawAtTest.plBad_not_lawAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms plBad_not_lawAt
/-- info: 'KCore.FnLawAtTest.pk_lawAt_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pk_lawAt_none
/-- info: 'KCore.FnLawAtTest.pk_lawAt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pk_lawAt_add
/-- info: 'KCore.FnLawAtTest.pk_not_lawAt_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pk_not_lawAt_sub
/-- info: 'KCore.FnLawAtTest.mx_not_lawAt_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mx_not_lawAt_none
/-- info: 'KCore.FnLawAtTest.mx_not_lawAt_H7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mx_not_lawAt_H7
/-- info: 'KCore.FnLawAtTest.mx_lawAt_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mx_lawAt_fst
/-- info: 'KCore.FnLawAtTest.pl_lawSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pl_lawSorted
/-- info: 'KCore.FnLawAtTest.plBad_lawSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms plBad_lawSorted
/-- info: 'KCore.FnLawAtTest.pk_lawSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pk_lawSorted
/-- info: 'KCore.FnLawAtTest.mx_lawSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mx_lawSorted

/-- info: 'KCore.FnLawAtTest.pl_consistent_with_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pl_consistent_with_laws
/-- info: 'KCore.FnLawAtTest.pk_consistent_with_laws_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pk_consistent_with_laws_add
/-- info: 'KCore.FnLawAtTest.mx_consistent_with_laws_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mx_consistent_with_laws_fst
/-- info: 'KCore.FnLawAtTest.wn_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wn_coreOK
/-- info: 'KCore.FnLawAtTest.badLaw_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms badLaw_pattern
/-- info: 'KCore.FnLawAtTest.badLaw_not_lawSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms badLaw_not_lawSorted
/-- info: 'KCore.FnLawAtTest.realLaw_not_lawAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms realLaw_not_lawAt
/-- info: 'KCore.consistent_with_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.consistent_with_laws

end KCore.FnLawAtTest
