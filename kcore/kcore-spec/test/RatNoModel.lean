/-
  Γ of a text holding module RAT has no model, for every interpretation H of the parameter
  symbols. The text is `f2-examples/e6-param-rat.kompile.kore`: kompile 7.1.337's text of the
  construct fixture e6-param-rat (`test/constructs/fixtures/e6-param-rat/e6-param-rat.k`), the
  fixture's directory written as `kcore-spec/test/constructs/fixtures/e6-param-rat/`; with K's
  builtin directory written `BUILTIN/` and the fixture's `FIXTURE/` its sha256 is the one the
  fixture's kompile.txt records.

  RAT's two equations of maxRat (rat.md:223-224) and of minRat (:220-221) have one priority, and
  both decide at (<1,1>Rat, 1): the `requires` `_>=Rat_` (`_<=Rat_`) is `true` both ways, and the
  two equations give the two arguments, which are distinct values of Rat. The text states that
  `<_,_>Rat` has a value at every pair of integers; the invariant excluding `<1,1>Rat`
  (rat.md:99) is a comment, in no sentence. So, for every H:
  - `maxRat_first`, `maxRat_second`, `minRat_first`, `minRat_second`: `Eval` has both results
    there (the first by the evaluator, the second by the second equation, whose `requires` the
    evaluator computes);
  - `no_model` (by maxRat), `no_model_min` (by minRat alone): Γ has no model, since each `Eval`
    result is a theorem of Γ (`TiePair.eval_some_sound`, which asks `coreOK` only) and Γ keeps
    the constructor's values apart from the injection's (`values_apart`);
  - `not_consistent`, `not_fnHyp`, `not_fnDet`, `not_coherentAll`.
  `coreOK` is true of the text (`coreOK`). `both_at_2`: the two `requires` are `true` both ways at
  (<2,2>Rat, 1) and (<3,3>Rat, 1) as well, so identifying `<1,1>Rat` with `1` would not give a
  model. Which conjunct of `FnHyp` fails is not stated here.

  Independently, makeRat/3's equations rat.md:171 (`J ==Int D`) and :173 (`J <Int 0`) have one
  priority and both decide at `J = D < 0`; at (-3, -3, -3) 171 gives `1` and 173, then 172 at
  (3, 3, -3), gives `<-1,-1>Rat` (`makeRat3_first`, `makeRat3_second`). So Γ has no model by
  makeRat/3 alone (`no_model_makeRat3`; `no_model_of` takes any argument list and any two distinct
  values of Rat). `gt_both_at_merged`: `_>Rat_` is `false` at (<-1,-1>Rat, 0) and `true` at (1, 0),
  so identifying the two values would not give a model of the `_>Rat_` equations either.
-/import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RatNoModel

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/e6-param-rat.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

def maxRat : Sym := 402
def minRat : Sym := 403
def geRat : Sym := 396
def leRat : Sym := 392
def ratCtor : Sym := 385
def gtRat : Sym := 397
def makeRat3 : Sym := 401
def rat : Srt := 32

theorem names : c.symName maxRat = "LblmaxRat" ∧ c.symName minRat = "LblminRat" ∧
    c.symName geRat = "Lbl'Unds-GT-Eqls'Rat'Unds'" ∧ c.symName leRat = "Lbl'Unds-LT-Eqls'Rat'Unds'" ∧
    c.symName ratCtor = "Lbl'-LT-UndsCommUnds-GT-'Rat'Unds'RAT-COMMON'Unds'Rat'Unds'Int'Unds'Int" ∧
    c.symName gtRat = "Lbl'Unds-GT-'Rat'Unds'" ∧
    c.symName makeRat3 = "LblmakeRat'LParUndsCommUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Int'Unds'Int'Unds'Int" ∧
    c.sortName rat = "Rat" ∧ c.isCtor ratCtor = true ∧ (Srt.int, rat) ∈ c.subsorts := by decide +kernel

/-- `<n,n>Rat`: the constructor at a pair the file's invariant excludes (rat.md:99). -/
def pair (n : Int) : GroundTerm := .ctor ratCtor [int n, int n]
/-- The Int `1` as a Rat. -/
def one : GroundTerm := .inj Srt.int rat (int 1)

theorem sort_pair (n : Int) : c.sortOf (pair n) = some rat := by
  show c.sortOf (.ctor ratCtor [.dv Srt.int (.int n), .dv Srt.int (.int n)]) = some rat
  rfl
theorem sort_one : c.sortOf one = some rat := by decide +kernel
theorem ne : pair 1 ≠ one := by decide

theorem sort_pairH (H : HookParams) (n : Int) : (cH H).sortOf (pair n) = some rat := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_pair n
theorem sort_oneH (H : HookParams) : (cH H).sortOf one = some rat := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_one

/-- The function numbered `f`, as `lookupFn` finds it. -/
noncomputable def fnOf (f : Sym) : Fn := (c.lookupFn f).getD ⟨0, [], 0, [], false⟩

theorem hfn (f : Sym) (h : (c.lookupFn f).isSome = true) : c.lookupFn f = some (fnOf f) := by
  unfold fnOf; cases hl : c.lookupFn f with
  | none => rw [hl] at h; cases h
  | some fn => rfl
theorem hfnH (H : HookParams) (f : Sym) (h : (c.lookupFn f).isSome = true) :
    (cH H).lookupFn f = some (fnOf f) := by rw [Semantics.lookupFn_withHooks]; exact hfn f h

/-- What `Cert.evalFC` computes is `Eval`'s under every H. -/
theorem eval_of {f : Sym} {vs : List GroundTerm} {k : Nat} {r : Option GroundTerm}
    (hf : (c.lookupFn f).isSome = true) (hvs : c.sortsOf vs = some (fnOf f).args)
    (h : Cert.evalFC c k f vs = some r) (H : HookParams) : Eval (cH H) f vs r :=
  TiePair.eval_withHooks hok hsr hmr noRaw H (hfn f hf) hvs h

/-- The second of two equations `f(R, S) => R requires g(R, S)`, `f(R, S) => S requires g(S, R)`
of one priority gives `S` where `g(S, R)` is `true`. -/
theorem eval_second {c' : Semantics} {f g : Sym} {fn : Fn} {cl : Clause} {a b : GroundTerm} {s : Srt}
    (hfn : c'.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hvars : cl.vars = [s, s]) (hpats : cl.pats = [.var 0, .var 1])
    (hreq : cl.req = some (.app g [.var 1, .var 0])) (hpre : cl.pre = .top) (hpost : cl.post = .top)
    (hexs : cl.exs = []) (hens : cl.ens = none) (hrhs : cl.rhs = .var 1)
    (hprio : ∀ cl' ∈ fn.clauses, ¬ cl'.prio < cl.prio)
    (hsa : c'.sortOf a = some s) (hsb : c'.sortOf b = some s)
    (hg : EvalTerm c' [(0, a), (1, b)] (.app g [.var 1, .var 0]) (some (bool true))) :
    Eval c' f [a, b] (some b) := by
  refine Eval.clause (cl := cl) (σ := [(0, a), (1, b)]) hfn hmem ?_ ?_ ?_ ?_ ?_ hexs ?_ ?_ ?_
  · intro i t hi
    rw [hvars] at hi
    match i, hi with
    | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨a, rfl, hsa⟩
    | 1, hi => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨b, rfl, hsb⟩
    | _ + 2, hi => simp at hi
  · rw [hpats]; exact .cons (.var rfl) (.cons (.var rfl) .nil)
  · intro t ht; rw [hreq] at ht; cases ht; exact hg
  · rw [hpre]; exact .top
  · intro cl' hcl' _ hlt; exact absurd hlt (hprio cl' hcl')
  · rw [hrhs]; exact EvalTerm.var (σ := [(0, a), (1, b)]) (i := 1)
  · intro t ht; rw [hens] at ht; cases ht
  · rw [hpost]; exact .top

/-- `g(S, R)` as a term over `R`, `S`, from the function's value at the two arguments. -/
theorem call_swapped {c' : Semantics} {g : Sym} {a b : GroundTerm} {r : Option GroundTerm}
    (hc : c'.isCtor g = false) (hh : isHook g = false) (hp : c'.isParam g = false)
    (hE : Eval c' g [b, a] r) : EvalTerm c' [(0, a), (1, b)] (.app g [.var 1, .var 0]) r :=
  EvalTerm.call (rs := [some b, some a]) hc hh
    (.cons (EvalTerm.var (σ := [(0, a), (1, b)]) (i := 1)) (.cons (EvalTerm.var (σ := [(0, a), (1, b)]) (i := 0)) .nil))
    rfl hE hp

/-! ## maxRat at (<1,1>Rat, 1) -/

theorem maxRat_first (H : HookParams) : Eval (cH H) maxRat [pair 1, one] (some (pair 1)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

theorem ge_swapped (H : HookParams) : Eval (cH H) geRat [one, pair 1] (some (bool true)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

theorem maxRat_second (H : HookParams) : Eval (cH H) maxRat [pair 1, one] (some one) :=
  eval_second (cl := (fnOf maxRat).clauses[1]'(by decide +kernel)) (g := geRat) (s := rat)
    (hfnH H maxRat (by decide +kernel)) (List.getElem_mem _)
    (by decide +kernel) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by decide +kernel) (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel)
    (sort_pairH H 1) (sort_oneH H)
    (call_swapped (by show c.isCtor geRat = false; decide +kernel) (by decide +kernel)
      (by show c.isParam geRat = false; decide +kernel) (ge_swapped H))

/-! ## minRat at (<1,1>Rat, 1) -/

theorem minRat_first (H : HookParams) : Eval (cH H) minRat [pair 1, one] (some (pair 1)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

theorem le_swapped (H : HookParams) : Eval (cH H) leRat [one, pair 1] (some (bool true)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

theorem minRat_second (H : HookParams) : Eval (cH H) minRat [pair 1, one] (some one) :=
  eval_second (cl := (fnOf minRat).clauses[1]'(by decide +kernel)) (g := leRat) (s := rat)
    (hfnH H minRat (by decide +kernel)) (List.getElem_mem _)
    (by decide +kernel) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by decide +kernel) (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel)
    (sort_pairH H 1) (sort_oneH H)
    (call_swapped (by show c.isCtor leRat = false; decide +kernel) (by decide +kernel)
      (by show c.isParam leRat = false; decide +kernel) (le_swapped H))

/-! ## No model -/

theorem rat_apart : apartSort c rat = true := by decide +kernel

/-- Two distinct values of Rat as values of one function at one argument list: Γ has no model. -/
theorem no_model_of {H : HookParams} {f : Sym} {vs : List GroundTerm} {a b : GroundTerm}
    (hf : (c.lookupFn f).isSome = true) (hvs : (cH H).sortsOf vs = some (fnOf f).args)
    (hsa : (cH H).sortOf a = some rat) (hsb : (cH H).sortOf b = some rat) (hab : a ≠ b)
    (h1 : Eval (cH H) f vs (some a)) (h2 : Eval (cH H) f vs (some b)) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ (cH H)) := by
  intro M _ I hI
  obtain ⟨hsok, hsr', hnn, hg, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hD := defOK hI
  have s1 : Γ (cH H) ⊧ (TiePair.app (cH H) f vs ≡ den (cH H) a) :=
    TiePair.eval_some_sound (hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok (hokH H))) (cH H)
      (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H)) h1 (hfnH H f hf) hvs
  have s2 : Γ (cH H) ⊧ (TiePair.app (cH H) f vs ≡ den (cH H) b) :=
    TiePair.eval_some_sound (hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok (hokH H))) (cH H)
      (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H)) h2 (hfnH H f hf) hvs
  have e1 := (KoreAML.interp_equal hD).mp (s1 hI KoreAML.val0 default)
  have e2 := (KoreAML.interp_equal hD).mp (s2 hI KoreAML.val0 default)
  have he : elemOf (cH H) I a = elemOf (cH H) I b := by
    have a1 := (elemOf_spec hI hsa KoreAML.val0).1
    have a2 := (elemOf_spec hI hsb KoreAML.val0).1
    exact (a2 _).mp ((e2 _).mp ((e1 _).mpr ((a1 _).mpr rfl)))
  exact hab (values_apart hI hg htr rat_apart hsa hsb he)

theorem sorts_args (H : HookParams) (f : Sym) {vs : List GroundTerm} (h : c.sortsOf vs = some (fnOf f).args) :
    (cH H).sortsOf vs = some (fnOf f).args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact h

/-- **Γ of the text has no model, for every H** (by maxRat). -/
theorem no_model (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model_of (f := maxRat) (by decide +kernel) (sorts_args H maxRat (by decide +kernel))
    (sort_pairH H 1) (sort_oneH H) ne (maxRat_first H) (maxRat_second H) M i I hI

/-- The same by minRat alone. -/
theorem no_model_min (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model_of (f := minRat) (by decide +kernel) (sorts_args H minRat (by decide +kernel))
    (sort_pairH H 1) (sort_oneH H) ne (minRat_first H) (minRat_second H) M i I hI

/-- Γ with the step's closure has no model, for every H. -/
theorem not_consistent (H : HookParams) : ¬ Consistent (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model H ⟨M, i, I, fun φ hφ => hI φ (Or.inl (Or.inl hφ))⟩

/-- `FnHyp` is false of the text, for every H. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) :=
  fun hf => not_consistent H (consistent_of_fnHyp _ (coreOKH H) hf)

/-- maxRat has two results at one argument list, for every H. -/
theorem not_fnDet (H : HookParams) : ¬ FnDet (cH H) :=
  fun h => ne (Option.some.inj (h _ _ _ _ (maxRat_first H) (maxRat_second H)))

/-- Some two competing equations of some function are not coherent, for every H. Which function
is not stated here: `Coherent` asks the `requires` to have one result (`HDet`), which for
`_>=Rat_` at these arguments is the uniqueness of every evaluation in its call chain. -/
theorem not_coherentAll (H : HookParams) : ¬ CoherentAll (cH H) :=
  fun h => not_fnDet H (fnDet_of_coherent h)

/-! ## makeRat/3 at (-3, -3, -3)

makeRat/3's three equations (rat.md:171-173) have one priority. At `J = D < 0` both 171
(`J ==Int D`) and 173 (`J <Int 0`) decide: 171 gives `inj{Int,Rat}(I /Int D)`, and 173 gives
makeRat/3 at `(0 -Int I, 0 -Int J, D)`, where 172 (`J >Int 0 andBool J =/=Int D`) gives
`<I' /Int D, J' /Int D>Rat`. At (-3, -3, -3) these are `1` and `<-1,-1>Rat`, distinct values of
Rat. The reader's clauses of makeRat/3 are in the text's order 172, 171, 173, so the evaluator
gives 171's value, and 173's is by its clause, the third, whose right side calls makeRat/3 at
(3, 3, -3), where the evaluator gives 172's. -/

/-- The argument list (-3, -3, -3). -/
def neg3 : List GroundTerm := [int (-3), int (-3), int (-3)]

/-- A clause `f(V0, V1, V2) => rhs requires q` with variable patterns, of no larger priority than
any other clause of `f`, decides at `[a, b, d]` where `q` is `true`. -/
theorem eval_clause3_rmr {c' : Semantics} {f : Sym} {fn : Fn} {cl : Clause} {a b d : GroundTerm}
    {s : Srt} {q : Term} {r : Option GroundTerm}
    (hfn : c'.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hvars : cl.vars = [s, s, s]) (hpats : cl.pats = [.var 0, .var 1, .var 2])
    (hreq : cl.req = some q) (hpre : cl.pre = .top) (hpost : cl.post = .top)
    (hexs : cl.exs = []) (hens : cl.ens = none)
    (hprio : ∀ cl' ∈ fn.clauses, ¬ cl'.prio < cl.prio)
    (hsa : c'.sortOf a = some s) (hsb : c'.sortOf b = some s) (hsd : c'.sortOf d = some s)
    (hq : EvalTerm c' [(0, a), (1, b), (2, d)] q (some (bool true)))
    (hr : EvalTerm c' [(0, a), (1, b), (2, d)] cl.rhs r) :
    Eval c' f [a, b, d] r := by
  refine Eval.clause (cl := cl) (σ := [(0, a), (1, b), (2, d)]) hfn hmem ?_ ?_ ?_ ?_ ?_ hexs hr ?_ ?_
  · intro i t hi
    rw [hvars] at hi
    match i, hi with
    | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨a, rfl, hsa⟩
    | 1, hi => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨b, rfl, hsb⟩
    | 2, hi => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨d, rfl, hsd⟩
    | _ + 3, hi => simp at hi
  · rw [hpats]; exact .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))
  · intro t ht; rw [hreq] at ht; cases ht; exact hq
  · rw [hpre]; exact .top
  · intro cl' hcl' _ hlt; exact absurd hlt (hprio cl' hcl')
  · intro t ht; rw [hens] at ht; cases ht
  · rw [hpost]; exact .top

/-- A hooked symbol at two arguments with values, where `hook` gives a value. -/
theorem hook2_rmr {c' : Semantics} {g : Sym} {σ : Subst} {t₁ t₂ : Term} {x y v : GroundTerm}
    (hc : c'.isCtor g = false) (hh : isHook g = true)
    (h₁ : EvalTerm c' σ t₁ (some x)) (h₂ : EvalTerm c' σ t₂ (some y)) (hv : hook g [x, y] = some (some v)) :
    EvalTerm c' σ (.app g [t₁, t₂]) (some v) :=
  EvalTerm.hook (rs := [some x, some y]) hc hh (.cons h₁ (.cons h₂ .nil))
    (fun vs h => by
      have hvs : vs = [x, y] := by simpa [allSome] using h.symm
      subst hvs; exact Semantics.hookRes_of_value hv)
    (fun h => by simp [allSome] at h)

theorem sorts_neg3 : c.sortsOf neg3 = some (fnOf makeRat3).args := by decide +kernel

theorem sort_intH (H : HookParams) (n : Int) : (cH H).sortOf (int n) = some Srt.int := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; rfl

/-- 171: the evaluator's value. -/
theorem makeRat3_first (H : HookParams) : Eval (cH H) makeRat3 neg3 (some one) :=
  eval_of (k := 60) (by decide +kernel) sorts_neg3 (by decide +kernel) H

/-- 172 at (3, 3, -3): `<3 /Int -3, 3 /Int -3>Rat`, by the evaluator. -/
theorem makeRat3_at_pos (H : HookParams) :
    Eval (cH H) makeRat3 [int 3, int 3, int (-3)] (some (pair (-1))) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- The clause of rat.md:173, `makeRat(I, J, D) => makeRat(0 -Int I, 0 -Int J, D) requires J <Int 0`. -/
noncomputable def cl173 : Clause := (fnOf makeRat3).clauses[2]'(by decide +kernel)

theorem cl173_mem : cl173 ∈ (fnOf makeRat3).clauses := List.getElem_mem _

theorem cl173_req : cl173.req = some (.app KCore.intLt [.var 1, .dv Srt.int (.int 0)]) := by
  with_unfolding_all rfl

theorem cl173_rhs : cl173.rhs = .app makeRat3
    [.app KCore.intSub [.dv Srt.int (.int 0), .var 0], .app KCore.intSub [.dv Srt.int (.int 0), .var 1], .var 2] := by
  with_unfolding_all rfl

/-- 173 at (-3, -3, -3): `(-3) <Int 0` is `true`, and the right side is makeRat/3 at (3, 3, -3). -/
theorem makeRat3_second (H : HookParams) : Eval (cH H) makeRat3 neg3 (some (pair (-1))) := by
  have hsub : ∀ i : Nat, i < 3 → EvalTerm (cH H) [(0, int (-3)), (1, int (-3)), (2, int (-3))]
      (.app KCore.intSub [.dv Srt.int (.int 0), .var i]) (some (int 3)) := by
    intro i hi
    have hl : List.lookup i [(0, int (-3)), (1, int (-3)), (2, int (-3))] = some (int (-3)) := by
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    exact hook2_rmr (by show c.isCtor KCore.intSub = false; decide +kernel) (by decide +kernel)
      EvalTerm.dv (by rw [← hl]; exact .var) (by decide +kernel)
  have hr : EvalTerm (cH H) [(0, int (-3)), (1, int (-3)), (2, int (-3))] cl173.rhs (some (pair (-1))) := by
    rw [cl173_rhs]
    exact EvalTerm.call (rs := [some (int 3), some (int 3), some (int (-3))])
      (by show c.isCtor makeRat3 = false; decide +kernel) (by decide +kernel)
      (.cons (hsub 0 (by decide)) (.cons (hsub 1 (by decide)) (.cons EvalTerm.var .nil))) rfl
      (makeRat3_at_pos H) (by show c.isParam makeRat3 = false; decide +kernel)
  exact eval_clause3_rmr (q := .app KCore.intLt [.var 1, .dv Srt.int (.int 0)]) (s := Srt.int)
    (hfnH H makeRat3 (by decide +kernel)) cl173_mem
    (by decide +kernel) (by with_unfolding_all rfl) cl173_req (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by decide +kernel)
    (sort_intH H (-3)) (sort_intH H (-3)) (sort_intH H (-3))
    (hook2_rmr (by show c.isCtor KCore.intLt = false; decide +kernel) (by decide +kernel)
      EvalTerm.var EvalTerm.dv (by decide +kernel))
    hr

theorem ne_neg1 : pair (-1) ≠ one := by decide

/-- **Γ of the text has no model, for every H**, by makeRat/3 alone. -/
theorem no_model_makeRat3 (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model_of (f := makeRat3) (by decide +kernel) (sorts_args H makeRat3 sorts_neg3)
    (sort_oneH H) (sort_pairH H (-1)) ne_neg1.symm (makeRat3_first H) (makeRat3_second H) M i I hI

/-- `_>Rat_` at the two values against `0`: `false` at `<-1,-1>Rat` (rat.md:209) and `true` at `1`
(rat.md:210), so the two values are not one element of any model of the text's `_>Rat_` equations
either. -/
theorem gt_both_at_merged :
    Cert.evalFC c 60 gtRat [pair (-1), .inj Srt.int rat (int 0)] = some (some (bool false)) ∧
    Cert.evalFC c 60 gtRat [one, .inj Srt.int rat (int 0)] = some (some (bool true)) := by decide +kernel

/-! ## Identifying `<1,1>Rat` with `1` does not help: the same holds at `<2,2>Rat`, `<3,3>Rat` -/

theorem both_at_2 : Cert.evalFC c 60 geRat [pair 2, one] = some (some (bool true)) ∧
    Cert.evalFC c 60 geRat [one, pair 2] = some (some (bool true)) ∧
    Cert.evalFC c 60 geRat [pair 3, one] = some (some (bool true)) ∧
    Cert.evalFC c 60 geRat [one, pair 3] = some (some (bool true)) := by decide +kernel

#check @coreOK
#check @names
#check @sort_pair
#check @rat_apart
#check @maxRat_first
#check @maxRat_second
#check @minRat_first
#check @minRat_second
#check @ge_swapped
#check @le_swapped
#check @no_model
#check @no_model_min
#check @not_consistent
#check @not_fnHyp
#check @not_fnDet
#check @not_coherentAll
#check @both_at_2
#check @makeRat3_first
#check @makeRat3_second
#check @no_model_makeRat3
#check @gt_both_at_merged
#check @eval_clause3_rmr
#check @hook2_rmr
#check @makeRat3_at_pos
#check @cl173_req
#check @cl173_rhs

#print axioms maxRat_first
#print axioms maxRat_second
#print axioms minRat_first
#print axioms minRat_second
#print axioms no_model
#print axioms no_model_min
#print axioms not_consistent
#print axioms not_fnHyp
#print axioms not_fnDet
#print axioms not_coherentAll
#print axioms both_at_2
#print axioms makeRat3_first
#print axioms makeRat3_second
#print axioms no_model_makeRat3
#print axioms gt_both_at_merged
#print axioms eval_clause3_rmr
#print axioms hook2_rmr
#print axioms makeRat3_at_pos

end KCore.RatNoModel
