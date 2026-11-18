import KcoreSpec

/-!
`Coherent` asks, of a first clause with existential variables, that each of its instances is
decided by terms with one result (`InstDet`), and grants the premises on its right-hand side and
`ensures` at the match only to a clause without them. This file holds why, and that the
proposition does what it is for.

`CoherentPrem` is `Coherent` with the two premises on the right-hand side and the `ensures` granted
at the match for every first clause, and no premise on instances. Two definitions have every two
competing clauses `CoherentPrem` and a function with two results:
- `Fx.cS`: `f` and `g` call each other, each by a clause with an existential variable whose
  predicate `post` is false. A derivation by `Eval.exNone` evaluates neither the right-hand side nor
  the `ensures`, so the premise "the right-hand side's terms have one result" is false of a clause
  whose right-hand side has two results, and holds no derivation to refute it.
- `Fx2.cT`: every instance fails by its right-hand side (`u()`, a function without an equation), its
  `ensures` never evaluated; the `ensures` is the term with two results.
`FnTerminates` holds of both, so no termination hypothesis excludes them.

Of `Coherent`:
- `refuses`: `CoherentAll` fails at `Fx.cS b` and at `Fx2.cT` (`fnDet_of_coherent`).
- `coherent_iff_prem`: for a first clause without existential variables it is `CoherentPrem`.
- `clB_coherent`: `f() => ?B ensures ?B` is coherent with itself in every semantics, so the
  proposition is not vacuous on clauses with existential variables.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore
namespace CoherentExsTest

open GroundTerm

/-- `Coherent` with the premises on the first clause's right-hand side and `ensures` granted at
the match whether or not it has existential variables, and no premise on its instances. -/
def CoherentPrem (c : Semantics) (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
    (∀ t, cl.req = some t → HDet c σ t) →
    ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs) →
    (∀ t, cl.ens = some t → HDet c σ t) →
    (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
      cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
    (cl.exs = [] ∧ cl'.exs = [] ∧
      cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
      ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∨
    ∀ r r', cl.Res c σ r → cl'.Res c σ' r' → r = r'

def CoherentAllPrem (c : Semantics) : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, ∀ cl' ∈ fn.clauses,
    (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio)) →
    CoherentPrem c cl cl'

/-- For a first clause without existential variables `Coherent` is `CoherentPrem`. -/
theorem coherent_iff_prem {c : Semantics} {cl cl' : Clause} (h : cl.exs = []) :
    Coherent c cl cl' ↔ CoherentPrem c cl cl' :=
  ⟨fun hc vs σ σ' ha ha' hq hr he hd => hc vs σ σ' ha ha' hq (fun _ => hr) (fun _ => he) (fun hne => absurd h hne) hd,
   fun hc vs σ σ' ha ha' hq hr he _ hd => hc vs σ σ' ha ha' hq (hr h) (he h) hd⟩

/-- A clause without an `ensures` whose right side has two results under every σ is coherent with
every clause: the premise "the right side's terms have one result" is false. -/
theorem coherent_of_two {c : Semantics} {cl cl' : Clause} (hn : cl.ens = none)
    {r r' : Option GroundTerm} (hne : r ≠ r') (h1 : ∀ σ, EvalTerm c σ cl.rhs r)
    (h2 : ∀ σ, EvalTerm c σ cl.rhs r') : CoherentPrem c cl cl' := by
  intro vs σ σ' _ _ _ hr _ _
  exact absurd (hr (fun t ht => by rw [hn] at ht; cases ht) _ (self_mem_subterms _) _ _ (h1 σ) (h2 σ)) hne

/-- A clause without `exs` and without an `ensures` whose right side holds no variable is
coherent with itself: the same instance. -/
theorem coherent_self_closed {c : Semantics} {cl : Clause} (hx : cl.exs = [])
    (hn : cl.ens = none) (hv : varOccs cl.rhs = []) : CoherentPrem c cl cl := by
  intro vs σ σ' _ _ _ _ _ _
  exact .inl ⟨hx, hx, rfl, rfl, (fun i hi => by rw [hv] at hi; cases hi), (fun t ht => by rw [hn] at ht; cases ht)⟩

/-- The generated sort predicates' clauses that compete are coherent, in every semantics. -/
theorem sortPreds_coherent {c : Semantics} {fn : Fn} (hfn : fn ∈ c.sortPreds) {cl cl' : Clause}
    (hm : cl ∈ fn.clauses) (hm' : cl' ∈ fn.clauses)
    (hc : cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨ (cl'.aside = true ∧ cl'.prio < cl.prio)) :
    CoherentPrem c cl cl' := by
  simp only [Semantics.sortPreds, List.mem_append, List.mem_cons, List.mem_filterMap, List.not_mem_nil,
    or_false, Option.map_eq_some_iff] at hfn
  rcases hfn with (rfl | rfl) | ⟨X, -, p, -, rfl⟩
  · simp only [List.mem_singleton] at hm hm'
    subst hm hm'
    exact coherent_self_closed rfl rfl rfl
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hm'
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
    · exact coherent_self_closed rfl rfl rfl
    · rcases hc with h | ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
    · rcases hc with h | ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
    · exact coherent_self_closed rfl rfl rfl

/-! ## The fixture

```k
syntax Bool ::= f() [function] | g() [function]
rule f() => #Exists Z:Bool. (g() #And (#Bottom #And Z #Equals Z))        // X
rule f() => g()                                        // Y
rule g() => #Exists Z:Bool. (f() #And (#Bottom #And Z #Equals Z)) requires f()   [priority(40)]   // Xg (b = true)
rule g() => true                                                             // W
```
With `b = false`, Xg has the predicate `#Ceil(f())` in place of the `requires`. -/

namespace Fx

open GroundTerm

def fl : Sym := nRegSyms
def gl : Sym := nRegSyms + 1
def fcall : Term := .app fl []
def gcall : Term := .app gl []

/-- A predicate that is false under every σ and holds the variable 0: `\bot ∧ (Z = Z)`. -/
def postF : Cond := .and .bot (.equals Srt.bool (.var 0) (.var 0))

theorem holds_postF {c : Semantics} {n : Nat} {σ : Subst} : Holds c n σ postF false :=
  Holds.and .bot (.equals .var .var)

def clX : Clause := { vars := [Srt.bool], pats := [], req := none, rhs := gcall, ens := none, exs := [0], post := postF }
def clY : Clause := { vars := [], pats := [], req := none, rhs := gcall, ens := none }
def clXg (b : Bool) : Clause :=
  { vars := [Srt.bool], pats := [], req := cond b (some fcall) none, rhs := fcall, ens := none, prio := 40,
    exs := [0], pre := cond b .top (.ceil Srt.bool fcall), post := postF }
def clW : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.bool (.bool true), ens := none }

def fnF : Fn := { label := fl, args := [], result := Srt.bool, clauses := [clX, clY] }
def fnG (b : Bool) : Fn := { label := gl, args := [], result := Srt.bool, clauses := [clXg b, clW] }

def cS (b : Bool) : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := []
    symNames := ["Lblfl", "Lblgl"]
    userSorts := []
    ctors := []
    fns := [fnF, fnG b]
    userSubsorts := []
    pgmSort := Srt.k
    rules := [] }

theorem lookup_fl (b : Bool) : (cS b).lookupFn fl = some fnF := by
  rw [Semantics.lookupFn_eq]; rfl
theorem lookup_gl (b : Bool) : (cS b).lookupFn gl = some (fnG b) := by
  rw [Semantics.lookupFn_eq]; rfl

theorem fl_notCtor (b : Bool) : (cS b).isCtor fl = false := by cases b <;> decide +kernel
theorem gl_notCtor (b : Bool) : (cS b).isCtor gl = false := by cases b <;> decide +kernel
theorem fl_notHook : isHook fl = false := by decide +kernel
theorem gl_notHook : isHook gl = false := by decide +kernel
theorem fl_notParam (b : Bool) : (cS b).isParam fl = false := by cases b <;> decide +kernel
theorem gl_notParam (b : Bool) : (cS b).isParam gl = false := by cases b <;> decide +kernel

/-- `f()` as a term has the results `f` has, under every σ. -/
theorem evF {b : Bool} {r : Option GroundTerm} (h : Eval (cS b) fl [] r) (σ : Subst) :
    EvalTerm (cS b) σ fcall r :=
  .call (fl_notCtor b) fl_notHook .nil rfl h (fl_notParam b)
theorem evG {b : Bool} {r : Option GroundTerm} (h : Eval (cS b) gl [] r) (σ : Subst) :
    EvalTerm (cS b) σ gcall r :=
  .call (gl_notCtor b) gl_notHook .nil rfl h (gl_notParam b)

theorem lookup_cons_self (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lookup_cons_ne {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

/-- The extension of σ that gives the variable 0 the Bool `true`. -/
def ext (σ : Subst) : Subst := (0, bool true) :: σ

theorem ext_sorted (c : Semantics) (σ : Subst) : c.WellSorted [Srt.bool] (ext σ) := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, lookup_cons_self _ _ _, sortOf_bool true⟩

theorem ext_agree (σ : Subst) : AgreeOff [0] σ (ext σ) := by
  intro i hi
  exact lookup_cons_ne _ _ (fun h => hi (by simp [h]))

theorem nil_sorted (c : Semantics) (σ : Subst) : c.WellSorted [] σ := by
  intro i s h; simp at h

theorem clX_free : clX.exsFree = [0] := by decide
theorem clXg_free (b : Bool) : (clXg b).exsFree = [0] := by cases b <;> decide

/-- An instance of a clause whose `post` is `postF` is decided and gives nothing. -/
theorem inst_bot {c : Semantics} {cl : Clause} (hp : cl.post = postF) (σ : Subst) (r : Option GroundTerm) :
    InstIs c σ cl r :=
  .fails (b := false) (by rw [hp]; exact holds_postF) (.post (by rw [hp]; exact holds_postF))

/-! ### The four derivations -/

/-- 1. `f()` has the result none, by X: every instance fails by `post`. Nothing else is evaluated. -/
theorem f_none (b : Bool) : Eval (cS b) fl [] none :=
  .exNone (cl := clX) (σ := []) (lookup_fl b) (by simp [fnF]) (by decide) (fun i hi => by cases hi) .nil
    (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by
      simp [fnF] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide))
    ⟨ext [], clX_free ▸ ext_agree [], ext_sorted _ _⟩
    (fun σ' _ _ => inst_bot rfl σ' none)

/-- Xg fails at `[]`: its `requires` (or its predicate) reads `f()`, which has the result none. -/
theorem xg_fails (b : Bool) : Fails (cS b) [] (clXg b) :=
  .intro fun σ _ _ => by
    cases b
    · exact .pre (Holds.ceil (evF (f_none false) σ))
    · exact .intro (t := fcall) rfl (evF (f_none true) σ) (by simp)

/-- 2. `g()` has the result `true`, by W: Xg, of the smaller priority, fails by 1. -/
theorem g_true (b : Bool) : Eval (cS b) gl [] (some (bool true)) :=
  .clause (cl := clW) (σ := []) (lookup_gl b) (by simp [fnG]) (nil_sorted _ _) .nil (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by
      simp [fnG] at hm
      rcases hm with rfl | rfl
      · exact xg_fails b
      · exact absurd hlt (by decide))
    rfl .dv (fun t ht => by cases ht) .top

/-- 3. `f()` has the result `true`, by Y and 2. -/
theorem f_true (b : Bool) : Eval (cS b) fl [] (some (bool true)) :=
  .clause (cl := clY) (σ := []) (lookup_fl b) (by simp [fnF]) (nil_sorted _ _) .nil (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by
      simp [fnF] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide))
    rfl (evG (g_true b) []) (fun t ht => by cases ht) .top

/-- 4. `g()` has the result none, by Xg: it applies by 3, and every instance fails by `post`. -/
theorem g_none (b : Bool) : Eval (cS b) gl [] none :=
  .exNone (cl := clXg b) (σ := []) (lookup_gl b) (by simp [fnG]) (by cases b <;> decide)
    (fun i hi => by cases b <;> cases hi) .nil
    (fun t ht => by
      cases b
      · cases ht
      · cases ht; exact evF (f_true true) [])
    (by
      cases b
      · exact Holds.ceil (evF (f_true false) [])
      · exact .top)
    (fun cl' hm _ hlt => by
      simp [fnG] at hm
      rcases hm with rfl | rfl
      · exact absurd hlt (by cases b <;> decide)
      · exact absurd hlt (by cases b <;> decide))
    ⟨ext [], clXg_free b ▸ ext_agree [], ext_sorted _ _⟩
    (fun σ' _ _ => inst_bot (by cases b <;> rfl) σ' none)

/-! ### The statement -/

/-- **`FnDet` is false**: `f()` has the results none and `true`. -/
theorem not_fnDet (b : Bool) : ¬ FnDet (cS b) := fun h => by
  have := h fl [] _ _ (f_none b) (f_true b)
  cases this

/-- Every two competing clauses of every function are `CoherentPrem`, for both forms of Xg. -/
theorem coherentAll (b : Bool) : CoherentAllPrem (cS b) := by
  intro f fn hfn cl hm cl' hm' hc
  rw [Semantics.lookupFn_eq] at hfn
  have hmem : fn ∈ [fnF, fnG b] ++ (cS b).sortPreds := List.mem_of_find?_eq_some hfn
  rcases List.mem_append.mp hmem with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · -- f: both clauses have the right side g(), which has two results
      have hr : cl.rhs = gcall ∧ cl.ens = none := by
        simp [fnF] at hm
        rcases hm with rfl | rfl <;> exact ⟨rfl, rfl⟩
      exact coherent_of_two hr.2 (r := some (bool true)) (r' := none) (by simp)
        (fun σ => hr.1 ▸ evG (g_true b) σ) (fun σ => hr.1 ▸ evG (g_none b) σ)
    · simp [fnG] at hm hm'
      rcases hm with rfl | rfl
      · -- Xg: its right side f() has two results
        exact coherent_of_two (by cases b <;> rfl) (r := some (bool true)) (r' := none) (by simp)
          (fun σ => by cases b <;> exact evF (f_true _) σ) (fun σ => by cases b <;> exact evF (f_none _) σ)
      · rcases hm' with rfl | rfl
        · -- W beside Xg: the priorities differ and neither is aside
          exact absurd hc (by cases b <;> decide)
        · exact coherent_self_closed rfl rfl rfl
  · exact sortPreds_coherent h hm hm' hc

/-- `CoherentAllPrem` and not `FnDet`. -/
theorem coherentAll_not_fnDet (b : Bool) : CoherentAllPrem (cS b) ∧ ¬ FnDet (cS b) :=
  ⟨coherentAll b, not_fnDet b⟩

/-- **Results exist** at `f()` and at `g()`. -/
theorem results_exist (b : Bool) : (∃ r, Eval (cS b) fl [] r) ∧ ∃ r, Eval (cS b) gl [] r :=
  ⟨⟨_, f_none b⟩, ⟨_, g_none b⟩⟩

end Fx

/-! ## The second route: every instance fails by its right side; no `ensures` is evaluated

```k
syntax Bool ::= f() [function] | g() [function] | u() [function]      // u has no equation
rule f() => #Exists Z:Bool. (u() #And Z #Equals Z) ensures g()                      // X
rule f() => g()                                                                   // Y
rule g() => #Exists Z:Bool. (u() #And Z #Equals Z) requires f() ensures f() [priority(40)]   // Xg
rule g() => true                                                                  // W
``` -/

namespace Fx2

open GroundTerm Fx

def ul : Sym := nRegSyms + 2
def ucall : Term := .app ul []

/-- A predicate with a truth value under every σ that holds the variable 0: `Z = Z`. -/
def postT : Cond := .equals Srt.bool (.var 0) (.var 0)

def clX : Clause := { vars := [Srt.bool], pats := [], req := none, rhs := ucall, ens := some gcall, exs := [0], post := postT }
def clY : Clause := { vars := [], pats := [], req := none, rhs := gcall, ens := none }
def clXg : Clause :=
  { vars := [Srt.bool], pats := [], req := some fcall, rhs := ucall, ens := some fcall, prio := 40, exs := [0], post := postT }

def fnF : Fn := { label := fl, args := [], result := Srt.bool, clauses := [clX, clY] }
def fnG : Fn := { label := gl, args := [], result := Srt.bool, clauses := [clXg, clW] }
def fnU : Fn := { label := ul, args := [], result := Srt.bool, clauses := [] }

def cT : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := []
    symNames := ["Lblfl", "Lblgl", "Lblul"]
    userSorts := []
    ctors := []
    fns := [fnF, fnG, fnU]
    userSubsorts := []
    pgmSort := Srt.k
    rules := [] }

theorem lookup_fl : cT.lookupFn fl = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_gl : cT.lookupFn gl = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_ul : cT.lookupFn ul = some fnU := by rw [Semantics.lookupFn_eq]; rfl

theorem flags (f : Sym) (h : f = fl ∨ f = gl ∨ f = ul) :
    cT.isCtor f = false ∧ isHook f = false ∧ cT.isParam f = false := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem ev {f : Sym} (h : f = fl ∨ f = gl ∨ f = ul) {r : Option GroundTerm} (he : Eval cT f [] r) (σ : Subst) :
    EvalTerm cT σ (.app f []) r :=
  .call (flags f h).1 (flags f h).2.1 .nil rfl he (flags f h).2.2

/-- `u()` has the result none: it has no equation, and its rest is undefined. -/
theorem u_none : Eval cT ul [] none := Eval.rest (fn := fnU) lookup_ul (fun _ h => nomatch h)

theorem clX_free : clX.exsFree = [0] := by decide
theorem clXg_free : clXg.exsFree = [0] := by decide

/-- An instance of a clause whose right side is `u()` and whose `post` is `postT` is decided and
gives nothing, by its right side: its `ensures` is not evaluated. -/
theorem inst_rhs {cl : Clause} (hr : cl.rhs = ucall) (hp : cl.post = postT) (σ : Subst) (r : Option GroundTerm) :
    InstIs cT σ cl r :=
  .fails (by rw [hp]; exact .equals .var .var) (.rhs (by rw [hr]; exact ev (.inr (.inr rfl)) u_none σ))

theorem f_none : Eval cT fl [] none :=
  .exNone (cl := clX) (σ := []) lookup_fl (by simp [fnF]) (by decide) (fun i hi => by cases hi) .nil
    (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by
      simp [fnF] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide))
    ⟨ext [], clX_free ▸ ext_agree [], ext_sorted _ _⟩
    (fun σ' _ _ => inst_rhs rfl rfl σ' none)

theorem xg_fails : Fails cT [] clXg :=
  .intro fun σ _ _ => .intro (t := fcall) rfl (ev (.inl rfl) f_none σ) (by simp)

theorem g_true : Eval cT gl [] (some (bool true)) :=
  .clause (cl := clW) (σ := []) lookup_gl (by simp [fnG]) (nil_sorted _ _) .nil (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by
      simp [fnG] at hm
      rcases hm with rfl | rfl
      · exact xg_fails
      · exact absurd hlt (by decide))
    rfl .dv (fun t ht => by cases ht) .top

theorem f_true : Eval cT fl [] (some (bool true)) :=
  .clause (cl := clY) (σ := []) lookup_fl (by simp [fnF]) (nil_sorted _ _) .nil (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by
      simp [fnF] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide))
    rfl (ev (.inr (.inl rfl)) g_true []) (fun t ht => by cases ht) .top

theorem g_none : Eval cT gl [] none :=
  .exNone (cl := clXg) (σ := []) lookup_gl (by simp [fnG]) (by decide) (fun i hi => by cases hi) .nil
    (fun t ht => by cases ht; exact ev (.inl rfl) f_true []) .top
    (fun cl' hm _ hlt => by
      simp [fnG] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide))
    ⟨ext [], clXg_free ▸ ext_agree [], ext_sorted _ _⟩
    (fun σ' _ _ => inst_rhs rfl rfl σ' none)

theorem not_fnDet : ¬ FnDet cT := fun h => by
  have := h fl [] _ _ f_none f_true
  cases this

/-- A clause whose `ensures` has two results under every σ is coherent with every clause: the
premise "the terms of the `ensures` have one result" is false. -/
theorem coherent_of_ens2 {c : Semantics} {cl cl' : Clause} {t : Term} (he : cl.ens = some t)
    {r r' : Option GroundTerm} (hne : r ≠ r') (h1 : ∀ σ, EvalTerm c σ t r) (h2 : ∀ σ, EvalTerm c σ t r') :
    CoherentPrem c cl cl' := by
  intro vs σ σ' _ _ _ _ hd _
  exact absurd (hd t he _ (self_mem_subterms _) _ _ (h1 σ) (h2 σ)) hne

theorem coherentAll : CoherentAllPrem cT := by
  intro f fn hfn cl hm cl' hm' hc
  rw [Semantics.lookupFn_eq] at hfn
  have hmem : fn ∈ [fnF, fnG, fnU] ++ cT.sortPreds := List.mem_of_find?_eq_some hfn
  rcases List.mem_append.mp hmem with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · simp [fnF] at hm
      rcases hm with rfl | rfl
      · exact coherent_of_ens2 rfl (r := some (bool true)) (r' := none) (by simp)
          (fun σ => ev (.inr (.inl rfl)) g_true σ) (fun σ => ev (.inr (.inl rfl)) g_none σ)
      · exact coherent_of_two rfl (r := some (bool true)) (r' := none) (by simp)
          (fun σ => ev (.inr (.inl rfl)) g_true σ) (fun σ => ev (.inr (.inl rfl)) g_none σ)
    · simp [fnG] at hm hm'
      rcases hm with rfl | rfl
      · exact coherent_of_ens2 rfl (r := some (bool true)) (r' := none) (by simp)
          (fun σ => ev (.inl rfl) f_true σ) (fun σ => ev (.inl rfl) f_none σ)
      · rcases hm' with rfl | rfl
        · exact absurd hc (by decide)
        · exact coherent_self_closed rfl rfl rfl
    · exact nomatch hm
  · exact sortPreds_coherent h hm hm' hc

/-- **The second route**: `CoherentAllPrem` and not `FnDet`, no `ensures` of an instance evaluated. -/
theorem coherentAll_not_fnDet : CoherentAllPrem cT ∧ ¬ FnDet cT := ⟨coherentAll, not_fnDet⟩

/-- Results exist at every function of `cT`: `FnTerminates`. -/
theorem fnTerminates : FnTerminates cT := by
  intro fn hfn vs hvs
  simp [cT] at hfn
  rcases hfn with rfl | rfl | rfl <;>
    (have : vs = [] := Faithful.sortsOf_nil_eq hvs
     subst this)
  · exact ⟨_, f_none⟩
  · exact ⟨_, g_none⟩
  · exact ⟨_, u_none⟩

end Fx2

/-- **`FnTerminates` holds of the first fixture too.** -/
theorem Fx.fnTerminates (b : Bool) : FnTerminates (Fx.cS b) := by
  intro fn hfn vs hvs
  simp [Fx.cS] at hfn
  rcases hfn with rfl | rfl <;>
    (have : vs = [] := Faithful.sortsOf_nil_eq hvs
     subst this)
  · exact ⟨_, Fx.f_none b⟩
  · exact ⟨_, Fx.g_none b⟩

/-- **`CoherentAll` refuses both definitions.** -/
theorem refuses (b : Bool) : ¬ CoherentAll (Fx.cS b) ∧ ¬ CoherentAll Fx2.cT :=
  ⟨fun h => Fx.not_fnDet b (fnDet_of_coherent h), fun h => Fx2.not_fnDet (fnDet_of_coherent h)⟩

/-- The clause of `f() => ?B ensures ?B`. -/
def clB : Clause := { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := some (.var 0), exs := [0] }

/-- Every result of `clB` at every match is `true`. -/
theorem clB_res (c : Semantics) (σ : Subst) (r : Option GroundTerm) (h : clB.Res c σ r) : r = some (KCore.bool true) := by
  have hf : clB.exsFree = [0] := by decide
  rcases h with ⟨hex, -⟩ | ⟨-, ⟨σ₁, v, -, -, ⟨grhs, gens, -⟩, -, rfl⟩ | ⟨rfl, -, hall⟩⟩
  · exact absurd hex (by decide)
  · have h1 := EvalTerm.var_inv grhs
    have h2 := EvalTerm.var_inv (gens _ rfl)
    exact h1.trans h2.symm
  · have hi := hall (Fx.ext σ) (hf ▸ Fx.ext_agree σ) (Fx.ext_sorted _ _)
    have hl : (Fx.ext σ).lookup 0 = some (KCore.bool true) := Fx.lookup_cons_self _ _ _
    generalize hn : (none : Option GroundTerm) = r₀ at hi
    cases hi with
    | fails hp hfl =>
      cases hfl with
      | ens ht he hw => cases ht; exact absurd ((EvalTerm.var_inv he).trans hl) hw
      | post hpf => exact absurd hpf.top_eq (by simp)
      | rhs hr => have := (EvalTerm.var_inv hr).trans hl; cases this
    | gives => cases hn

/-- `clB` is coherent with itself in every semantics: every result of it at every match is `true`. -/
theorem clB_coherent (c : Semantics) : Coherent c clB clB := by
  intro vs σ σ' _ _ _ _ _ _ _
  exact .inr fun r r' h1 h2 => (clB_res c σ r h1).trans (clB_res c σ' r' h2).symm


/-- info: 'KCore.CoherentExsTest.Fx.coherentAll_not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fx.coherentAll_not_fnDet
/-- info: 'KCore.CoherentExsTest.Fx2.coherentAll_not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fx2.coherentAll_not_fnDet
/-- info: 'KCore.CoherentExsTest.Fx2.fnTerminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fx2.fnTerminates
/-- info: 'KCore.CoherentExsTest.Fx.fnTerminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fx.fnTerminates
/-- info: 'KCore.CoherentExsTest.refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refuses
/-- info: 'KCore.CoherentExsTest.clB_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clB_coherent
/-- info: 'KCore.CoherentExsTest.coherent_iff_prem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coherent_iff_prem
/-- info: 'KCore.fnDet_of_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnDet_of_coherent
/-- info: 'KCore.Eval.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Eval.functional

example : ∀ {c : Semantics}, CoherentAll c → FnDet c := @fnDet_of_coherent

end CoherentExsTest
end KCore
