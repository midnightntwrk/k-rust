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
def rat : Srt := 32

theorem names : c.symName maxRat = "LblmaxRat" ∧ c.symName minRat = "LblminRat" ∧
    c.symName geRat = "Lbl'Unds-GT-Eqls'Rat'Unds'" ∧ c.symName leRat = "Lbl'Unds-LT-Eqls'Rat'Unds'" ∧
    c.symName ratCtor = "Lbl'-LT-UndsCommUnds-GT-'Rat'Unds'RAT-COMMON'Unds'Rat'Unds'Int'Unds'Int" ∧
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

/-- Two values of one function at one argument list, distinct values of Rat: Γ has no model. -/
theorem no_model_of {H : HookParams} {f : Sym} (hf : (c.lookupFn f).isSome = true)
    (hvs : (cH H).sortsOf [pair 1, one] = some (fnOf f).args)
    (h1 : Eval (cH H) f [pair 1, one] (some (pair 1))) (h2 : Eval (cH H) f [pair 1, one] (some one)) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ (cH H)) := by
  intro M _ I hI
  obtain ⟨hsok, hsr', hnn, hg, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hD := defOK hI
  have s1 : Γ (cH H) ⊧ (TiePair.app (cH H) f [pair 1, one] ≡ den (cH H) (pair 1)) :=
    TiePair.eval_some_sound (hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok (hokH H))) (cH H)
      (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H)) h1 (hfnH H f hf) hvs
  have s2 : Γ (cH H) ⊧ (TiePair.app (cH H) f [pair 1, one] ≡ den (cH H) one) :=
    TiePair.eval_some_sound (hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok (hokH H))) (cH H)
      (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H)) h2 (hfnH H f hf) hvs
  have e1 := (KoreAML.interp_equal hD).mp (s1 hI KoreAML.val0 default)
  have e2 := (KoreAML.interp_equal hD).mp (s2 hI KoreAML.val0 default)
  have he : elemOf (cH H) I (pair 1) = elemOf (cH H) I one := by
    have a1 := (elemOf_spec hI (sort_pairH H 1) KoreAML.val0).1
    have a2 := (elemOf_spec hI (sort_oneH H) KoreAML.val0).1
    exact (a2 _).mp ((e2 _).mp ((e1 _).mpr ((a1 _).mpr rfl)))
  exact ne (values_apart hI hg htr rat_apart (sort_pairH H 1) (sort_oneH H) he)

theorem sorts_args (H : HookParams) (f : Sym) (h : c.sortsOf [pair 1, one] = some (fnOf f).args) :
    (cH H).sortsOf [pair 1, one] = some (fnOf f).args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact h

/-- **Γ of the text has no model, for every H** (by maxRat). -/
theorem no_model (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model_of (f := maxRat) (by decide +kernel) (sorts_args H maxRat (by decide +kernel))
    (maxRat_first H) (maxRat_second H) M i I hI

/-- The same by minRat alone. -/
theorem no_model_min (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model_of (f := minRat) (by decide +kernel) (sorts_args H minRat (by decide +kernel))
    (minRat_first H) (minRat_second H) M i I hI

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

end KCore.RatNoModel
