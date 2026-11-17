/-
  Clauses that are `aside` (a `non-executable` equation: an axiom of the text that no `[owise]`
  premise negates, so it blocks no clause). Run from the package root:
  `lake env lean test/AsideClauses.lean`.

  - `E5`: `f2-examples/owisene.kompile.kore` (`owisene.k`, a text neighbouring fixture
    e5-owise-nonexec's and not that text: sort `Exp`, a `<k>` cell and one rule
    `go(X, Y) => done(choose(X, Y))`, where the fixture has sort `Foo` and no rule; the three
    equations of `choose` are the fixture's up to the sort's name, so no fact below is about the
    fixture's own sentences):
    `choose(a, Y) = Y`, `choose(b, Y) = Y` [non-executable], `choose(X, _) = X` [owise]. The
    `[owise]` premise negates the first equation only. Read with the second clause `aside`
    (`aside_b`); the `[owise]` clause's smaller clauses are the first alone (`lower_owise`). At
    (b, a) the text states `= a` (the `non-executable` equation) and `= b` (the `[owise]` one), and
    `Eval` gives both (`eval_ba_a`, `eval_ba_b`): not `FnDet`, not `ClausesAgree` (`not_fnDet`,
    `not_agree`). At (b, b) one value b (`eval_bb`), at (a, y) one value y (`eval_ay`).
  - `G`: `g()` with C `false` (`aside`, 50), D `false requires g()` (50), E `true` (200). `Eval`
    gives `false` by C and `true` by E (D fails by C's result): not `FnDet`, and (C, E), a pair
    `ClausesAgree` reads since C is `aside` and of the smaller priority, is not coherent: both
    decide as `Eval.clause` reads deciding (`Clause.Decides`), with different results.
  - `U`: `g()` with C `false` (`aside`, 50), U `false` with one variable of a sort without a value
    that stands nowhere (50), E `true` (200). `Eval` gives `false` only (`only_false`): U does not
    fail (its patterns and conditions hold no variable) and gives no result. E does not decide
    (`E_not_decides`): U, of a smaller priority, has an instance that matches over the substitutions
    `Fails` ranges over. `FnSolves` holds (`fnSolves_c`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.AsideClausesTest

open KCore

/-! ## E5: `owisene.kompile.kore` -/

namespace E5

definition_of defn from "f2-examples/owisene.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def choose : Sym := 390
def a : Sym := 386
def b : Sym := 387
def exp : Srt := 33
def va : GroundTerm := .ctor a []
def vb : GroundTerm := .ctor b []

theorem names : c.symName choose = "Lblchoose" ∧ c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧
    c.sortName exp = "Exp" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev clA : Clause := fn.clauses[0]'(by decide +kernel)
noncomputable abbrev clB : Clause := fn.clauses[1]'(by decide +kernel)
noncomputable abbrev clO : Clause := fn.clauses[2]'(by decide +kernel)

theorem fn_label : fn.label = choose := by decide +kernel
theorem hfn : c.lookupFn choose = some fn := rfl
theorem fn_clauses : fn.clauses = [clA, clB, clO] := rfl

/-- The core is accepted. -/
theorem coreOK : c.coreOK = true := by decide_cheap

/-- The `non-executable` equation is read as an `aside` clause; the others are not. -/
theorem aside_b : clB.aside = true ∧ clA.aside = false ∧ clO.aside = false := by decide +kernel

theorem pA : clA.prio = 50 := rfl
theorem pB : clB.prio = 50 := rfl
theorem pO : clO.prio = 200 := rfl
theorem vA : clA.vars = [exp] := rfl
theorem ptA : clA.pats = [.app a [], .var 0] := rfl
theorem qA : clA.req = none := rfl
theorem rA : clA.rhs = .var 0 := rfl
theorem eA : clA.ens = none := rfl
theorem vB : clB.vars = [exp] := rfl
theorem ptB : clB.pats = [.app b [], .var 0] := rfl
theorem qB : clB.req = none := rfl
theorem rB : clB.rhs = .var 0 := rfl
theorem eB : clB.ens = none := rfl
theorem vO : clO.vars = [exp, exp] := rfl
theorem ptO : clO.pats = [.var 0, .var 1] := rfl
theorem qO : clO.req = none := rfl
theorem rO : clO.rhs = .var 0 := rfl
theorem eO : clO.ens = none := rfl
theorem preA : clA.pre = .top := rfl
theorem preB : clB.pre = .top := rfl
theorem preO : clO.pre = .top := rfl

/-- No clause of `choose` has an existential variable. -/
theorem exs_fn {cl : Clause} (h : cl ∈ fn.clauses) : cl.exs = [] := by
  rw [fn_clauses] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

/-- The `[owise]` clause's smaller clauses are the first alone, as sentence 206 writes. -/
theorem lower_owise : Faithful.lowerClauses fn clO = [clA] := rfl

theorem isCtor_a : c.isCtor a = true := by decide +kernel
theorem isCtor_b : c.isCtor b = true := by decide +kernel
theorem sort_a : c.sortOf va = some exp := by decide +kernel
theorem sort_b : c.sortOf vb = some exp := by decide +kernel

theorem ws1 {v : GroundTerm} (hv : c.sortOf v = some exp) : c.WellSorted [exp] [(0, v)] := fun i s h => by
  cases i with
  | zero => cases h; exact ⟨v, rfl, hv⟩
  | succ i => simp at h

theorem ws2 {v w : GroundTerm} (hv : c.sortOf v = some exp) (hw : c.sortOf w = some exp) :
    c.WellSorted [exp, exp] [(0, v), (1, w)] := fun i s h => by
  match i, h with
  | 0, h => cases h; exact ⟨v, rfl, hv⟩
  | 1, h => cases h; exact ⟨w, rfl, hw⟩

/-- The pattern of a constructor without arguments denotes that constructor only. -/
theorem patVal_ctor0 {σ : Subst} {f : Sym} {v : GroundTerm} (hf : c.isCtor f = true)
    (hk : patternHooks.contains f = false) (h : PatVal c σ (.app f []) v) : v = .ctor f [] := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => rw [hk] at hp; cases hp
  | coll hc _ _ _ => rw [hf] at hc; cases hc
  | ovl hc _ _ _ => rw [hf] at hc; cases hc

theorem hook_a : patternHooks.contains a = false := by decide
theorem hook_b : patternHooks.contains b = false := by decide

/-- The first clause fails at `(b, w)`: its pattern `a` does not denote `b`. -/
theorem clA_fails_b (w : GroundTerm) : Fails c [vb, w] clA := .intro fun σ _ hp => by
  rw [ptA] at hp
  cases hp with
  | cons h _ => exact absurd (patVal_ctor0 isCtor_a hook_a h) (by simp [vb, a, b])

/-- At (b, a): `a`, by the `aside` clause (no clause of a smaller priority is not `aside`). -/
theorem eval_ba_a : Eval c choose [vb, va] (some va) :=
  .clause (cl := clB) (σ := [(0, va)]) hfn (by rw [fn_clauses]; simp)
    (by rw [vB]; exact ws1 sort_a)
    (by rw [ptB]; exact .cons (.ctor isCtor_b .nil) (.cons (.var rfl) .nil))
    (fun t ht => by rw [qB] at ht; cases ht)
    (Clause.holds_preTop preB _)
    (fun cl' h ha hlt => by
      rw [fn_clauses] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · rw [pA, pB] at hlt; exact absurd hlt (by decide)
      · rw [aside_b.1] at ha; cases ha
      · rw [pO, pB] at hlt; exact absurd hlt (by decide))
    rfl (by rw [rB]; exact .var)
    (fun t ht => by rw [eB] at ht; cases ht) (Clause.holds_postTop rfl _)

/-- At (b, a): `b`, by the `[owise]` clause (its one smaller clause that is not `aside`, the first,
fails). -/
theorem eval_ba_b : Eval c choose [vb, va] (some vb) :=
  .clause (cl := clO) (σ := [(0, vb), (1, va)]) hfn (by rw [fn_clauses]; simp)
    (by rw [vO]; exact ws2 sort_b sort_a)
    (by rw [ptO]; exact .cons (.var rfl) (.cons (.var rfl) .nil))
    (fun t ht => by rw [qO] at ht; cases ht)
    (Clause.holds_preTop preO _)
    (fun cl' h ha hlt => by
      rw [fn_clauses] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact clA_fails_b va
      · rw [aside_b.1] at ha; cases ha
      · exact absurd hlt (Nat.lt_irrefl _))
    rfl (by rw [rO]; exact .var)
    (fun t ht => by rw [eO] at ht; cases ht) (Clause.holds_postTop rfl _)

theorem va_ne_vb : va ≠ vb := by simp [va, vb, a, b]

/-- **Not `FnDet`**: the text states two values at (b, a). -/
theorem not_fnDet : ¬ FnDet c := fun h => va_ne_vb (Option.some.inj (h _ _ _ _ eval_ba_a eval_ba_b))

/-- **Not `ClausesAgree`**: the `aside` clause and the `[owise]` clause compete (the `aside` one has the
smaller priority) and both decide at (b, a), with the results `a` and `b`. -/
theorem not_agree : ¬ ClausesAgree c fn := fun h => by
  have hp : (clB, clO) ∈ pairs fn.clauses := by rw [fn_clauses]; simp [pairs]
  have hcomp : clB.prio = clO.prio ∨ (clB.aside = true ∧ clB.prio < clO.prio) ∨
      (clO.aside = true ∧ clO.prio < clB.prio) :=
    .inr (.inl ⟨aside_b.1, by rw [pB, pO]; decide⟩)
  have hco := (h clB clO hp hcomp).1
  have hapB : clB.AppliesAt c [(0, va)] [vb, va] :=
    ⟨by rw [vB]; exact ws1 sort_a,
     by rw [ptB]; exact .cons (.ctor isCtor_b .nil) (.cons (.var rfl) .nil),
     (fun t ht => by rw [qB] at ht; cases ht), Clause.holds_preTop preB _⟩
  have hapO : clO.AppliesAt c [(0, vb), (1, va)] [vb, va] :=
    ⟨by rw [vO]; exact ws2 sort_b sort_a,
     by rw [ptO]; exact .cons (.var rfl) (.cons (.var rfl) .nil),
     (fun t ht => by rw [qO] at ht; cases ht), Clause.holds_preTop preO _⟩
  have hdecB : clB.Decides c fn [(0, va)] [vb, va] := ⟨hapB, fun cl' h ha hlt => by
    rw [fn_clauses] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · rw [pA, pB] at hlt; exact absurd hlt (by decide)
    · rw [aside_b.1] at ha; cases ha
    · rw [pO, pB] at hlt; exact absurd hlt (by decide)⟩
  have hdecO : clO.Decides c fn [(0, vb), (1, va)] [vb, va] := ⟨hapO, fun cl' h ha hlt => by
    rw [fn_clauses] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact clA_fails_b va
    · rw [aside_b.1] at ha; cases ha
    · exact absurd hlt (Nat.lt_irrefl _)⟩
  have hdet : HDet c [(0, va)] clB.rhs := by
    rw [rB]
    intro u hu r r' h1 h2
    simp only [subterms, List.mem_singleton] at hu
    subst hu
    cases h1; cases h2; rfl
  rcases hco [vb, va] [(0, va)] [(0, vb), (1, va)] hapB hapO
      (fun t ht => by rw [qB] at ht; cases ht) (fun _ _ => hdet)
      (fun _ t ht => by rw [eB] at ht; cases ht) (fun hne => absurd rfl hne)
      ⟨choose, fn, hfn, by rw [fn_clauses]; simp, by rw [fn_clauses]; simp, hdecB, hdecO⟩ with
    ⟨-, -, -, -, hv, -⟩ | hr
  · have := hv 0 (by rw [rB]; simp [varOccs])
    exact va_ne_vb (by simpa using this)
  · have := hr (some va) (some vb)
      ((Clause.res_noExs rfl).mpr (.inl ⟨(fun t ht => by rw [eB] at ht; cases ht),
        Clause.holds_postTop rfl _, (by rw [rB]; exact .var)⟩))
      ((Clause.res_noExs rfl).mpr (.inl ⟨(fun t ht => by rw [eO] at ht; cases ht),
        Clause.holds_postTop rfl _, (by rw [rO]; exact .var)⟩))
    exact va_ne_vb (Option.some.inj this)

/-- A clause without a `requires` and without a `pre` whose patterns match does not fail. -/
theorem not_fails_noReq {vs : List GroundTerm} {cl : Clause} {σ : Subst} (hq : cl.req = none)
    (hpre : cl.pre = .top)
    (hw : c.WellSortedAt cl.vars cl.leftVars σ) (hp : PatVals c σ cl.pats vs) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ hw hp with
    | intro ht _ _ => rw [hq] at ht; cases ht
    | pre h => rw [hpre] at h; exact absurd (Holds.top_eq h) (by simp)

/-- **At (b, b), one value**: `b`. -/
theorem eval_bb (r : Option GroundTerm) (h : Eval c choose [vb, vb] r) : r = some vb := by
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [ptA] at hmatch
      cases hmatch with
      | cons h1 _ => exact absurd (patVal_ctor0 isCtor_a hook_a h1) (by simp [vb, a, b])
    · rw [ptB] at hmatch; rw [rB] at hrhs
      cases hmatch with
      | cons _ h2 => cases h2 with
        | cons h2 _ => cases h2 with
          | var hl => cases hrhs; exact hl
    · rw [ptO] at hmatch; rw [rO] at hrhs
      cases hmatch with
      | cons h1 _ => cases h1 with
        | var hl => cases hrhs; exact hl
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails_noReq qB preB (by rw [vB]; exact (ws1 sort_b).at _)
      (by rw [ptB]; exact .cons (.ctor isCtor_b .nil) (.cons (.var rfl) .nil))
      (hnone clB (by rw [fn_clauses]; simp))).elim
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (exs_fn hmem) hne
  | exNone hfn' hmem hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (exs_fn hmem) hne
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [eA] at ht; cases ht
    · rw [eB] at ht; cases ht
    · rw [eO] at ht; cases ht

/-- **At (a, y), one value**: `y`, for every value y of Exp. -/
theorem eval_ay {y : GroundTerm} (hy : c.sortOf y = some exp) (r : Option GroundTerm)
    (h : Eval c choose [va, y] r) : r = some y := by
  have hAap : c.WellSortedAt clA.vars clA.leftVars [(0, y)] ∧ PatVals c [(0, y)] clA.pats [va, y] :=
    ⟨by rw [vA]; exact (ws1 hy).at _, by rw [ptA]; exact .cons (.ctor isCtor_a .nil) (.cons (.var rfl) .nil)⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ hprio _ hrhs _ _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [ptA] at hmatch; rw [rA] at hrhs
      cases hmatch with
      | cons _ h2 => cases h2 with
        | cons h2 _ => cases h2 with
          | var hl => cases hrhs; exact hl
    · rw [ptB] at hmatch
      cases hmatch with
      | cons h1 _ => exact absurd (patVal_ctor0 isCtor_b hook_b h1) (by simp [va, a, b])
    · exact (not_fails_noReq qA preA hAap.1 hAap.2
        (hprio clA (by rw [fn_clauses]; simp) aside_b.2.1 (by rw [pA, pO]; decide))).elim
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails_noReq qA preA hAap.1 hAap.2 (hnone clA (by rw [fn_clauses]; simp))).elim
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (exs_fn hmem) hne
  | exNone hfn' hmem hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (exs_fn hmem) hne
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [eA] at ht; cases ht
    · rw [eB] at ht; cases ht
    · rw [eO] at ht; cases ht

end E5

/-! ## G: an `aside` clause beside a clause that a larger one's priority reads -/

namespace G

def gl : Sym := nRegSyms + 4
def ff : Term := .dv Srt.bool (.bool false)
def tt : Term := .dv Srt.bool (.bool true)
def C : Clause := { vars := [], pats := [], req := none, rhs := ff, ens := none, prio := 50, aside := true }
def D : Clause := { vars := [], pats := [], req := some (.app gl []), rhs := ff, ens := none, prio := 50 }
def E : Clause := { vars := [], pats := [], req := none, rhs := tt, ens := none, prio := 200 }
def gfn : Fn := { label := gl, args := [], result := Srt.bool, clauses := [C, D, E] }
def c : Semantics := { Faithful.JunkWitness.c with fns := [gfn] }

theorem hfn : c.lookupFn gl = some gfn := rfl
theorem ws_nil : c.WellSorted [] [] := fun i s h => by simp at h

theorem g_false : Eval c gl [] (some (bool false)) :=
  .clause (cl := C) (σ := []) hfn (by simp [gfn]) ws_nil .nil (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [C, D, E] at hlt)
    rfl .dv (fun t h => by cases h) .top

theorem D_fails : Fails c [] D := .intro fun σ _ _ =>
  .intro (t := .app gl []) rfl (.call (vs := []) (by decide +kernel) (by decide +kernel) .nil rfl g_false
    (by decide +kernel)) (by simp [bool])

theorem E_lower : ∀ cl' ∈ gfn.clauses, cl'.aside = false → cl'.prio < E.prio → Fails c [] cl' := fun cl' h ha hlt => by
  simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · simp [C] at ha
  · exact D_fails
  · simp [E] at hlt

theorem g_true : Eval c gl [] (some (bool true)) :=
  .clause (cl := E) (σ := []) hfn (by simp [gfn]) ws_nil .nil (fun t h => by cases h) .top E_lower rfl .dv
    (fun t h => by cases h) .top

/-- Not `FnDet`: `false` by C, `true` by E. -/
theorem not_fnDet : ¬ FnDet c := fun h => by
  have := h _ _ _ _ g_false g_true
  simp [bool] at this

/-- Not `ClausesAgree`: (C, E) compete (C is `aside`, of the smaller priority) and both decide as
`Eval.clause` reads deciding, with different results. -/
theorem not_agree : ¬ ClausesAgree c gfn := fun h => by
  have hco := (h C E (by simp [gfn, pairs]) (.inr (.inl ⟨rfl, by decide⟩))).1
  have hapC : C.AppliesAt c [] [] := ⟨ws_nil, .nil, (fun t h => by cases h), .top⟩
  have hapE : E.AppliesAt c [] [] := ⟨ws_nil, .nil, (fun t h => by cases h), .top⟩
  have hdecC : C.Decides c gfn [] [] := ⟨hapC, fun cl' h _ hlt => by
    simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [C, D, E] at hlt⟩
  rcases hco [] [] [] hapC hapE (fun t h => by cases h)
      (fun _ _ u hu r r' h1 h2 => by simp [C, ff, subterms] at hu; subst hu; cases h1; cases h2; rfl)
      (fun _ t h => by cases h) (fun hne => absurd rfl hne)
      ⟨gl, gfn, hfn, by simp [gfn], by simp [gfn], hdecC, ⟨hapE, E_lower⟩⟩ with ⟨-, -, he, -⟩ | hr
  · simp [C, E, ff, tt] at he
  · have := hr (some (bool false)) (some (bool true))
      ((Clause.res_noExs rfl).mpr (.inl ⟨(fun t h => by cases h), .top, .dv⟩))
      ((Clause.res_noExs rfl).mpr (.inl ⟨(fun t h => by cases h), .top, .dv⟩))
    simp [bool] at this

end G

/-! ## U: `DecidesAt` ranges as `Fails` does (F1-DECISION 2.6) -/

namespace U

def gl : Sym := nRegSyms + 4
def ff : Term := .dv Srt.bool (.bool false)
def tt : Term := .dv Srt.bool (.bool true)
def C : Clause := { vars := [], pats := [], req := none, rhs := ff, ens := none, prio := 50, aside := true }
/-- One variable of IOError (no value) that stands nowhere. -/
def U : Clause := { vars := [Srt.ioError], pats := [], req := none, rhs := ff, ens := none, prio := 50 }
def E : Clause := { vars := [], pats := [], req := none, rhs := tt, ens := none, prio := 200 }
def gfn : Fn := { label := gl, args := [], result := Srt.bool, clauses := [C, U, E] }
def c' : Semantics := { Faithful.JunkWitness.c with fns := [gfn] }

theorem ctors_not_err' : c'.ctorSigs.all (fun k => k.result != Srt.ioError) = true := by decide +kernel
theorem subs_not_err' : c'.subsorts.all (fun p => p.2 != Srt.ioError) = true := by decide +kernel
theorem coll_err' : c'.collOf Srt.ioError = none := by decide +kernel

/-- **No value has sort IOError**: no constructor and no subsort pair ends there, no literal is an
IOError (`dvOK`), and IOError is no collection sort. -/
theorem no_err' (v : GroundTerm) : c'.sortOf v ≠ some Srt.ioError := by
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf]
    cases hk : lookupSig c'.ctorSigs f with
    | none => have : c'.lookupOvl f = none := rfl
              have ho : c'.lookupOpen f = none := c'.lookupOpen_of_noRaw (by intro k hk; cases hk) f
              simp [this, ho]
    | some k =>
      simp only
      have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
      have := List.all_eq_true.mp ctors_not_err' k hm
      split <;> simp_all
  | inj a b t =>
    rw [Semantics.sortOf]
    split
    · rename_i h
      intro hb
      cases hb
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      have := List.all_eq_true.mp subs_not_err' _ h.1.1
      simp at this
    · simp
  | dv s lit =>
    rw [Semantics.sortOf]
    split
    · rename_i h
      intro hs
      cases hs
      cases lit with
      | int _ => simp only [dvOK, beq_iff_eq] at h; exact absurd h (by decide)
      | bool _ => simp only [dvOK, beq_iff_eq] at h; exact absurd h (by decide)
      | float _ _ _ => simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at h; exact absurd h.1 (by decide)
      | tok t =>
        simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ((h | h) | h) | ⟨h | h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide +kernel)
        · exact absurd h (by decide)
        · exact absurd h (by decide +kernel)
    · simp
  | map s es =>
    intro h
    obtain ⟨_, _, _, _, _, _, hs⟩ := Semantics.sortOf_map_inv _ h
    subst hs
    rw [Semantics.sortOf, coll_err'] at h
    cases h
  | set s es | list s es =>
    intro h
    have hs : s = Srt.ioError := by
      rw [Semantics.sortOf] at h
      split at h
      · split at h
        · first
            | exact Option.some.inj h
            | (split at h <;> first | exact Option.some.inj h | cases h)
        · cases h
      · cases h
    subst hs
    rw [Semantics.sortOf, coll_err'] at h
    cases h


theorem hfn : c'.lookupFn gl = some gfn := rfl
theorem ws_nil : c'.WellSorted [] [] := fun i s h => by simp at h

theorem no_U_σ {σ : Subst} (h : c'.WellSorted U.vars σ) : False := by
  obtain ⟨v, -, hv⟩ := h 0 Srt.ioError rfl
  exact no_err' v hv

theorem leftVars_U : U.leftVars = [] := by simp [Clause.leftVars, Clause.condVars, U, varOccsList, varOccsCond]

/-- U does not fail: no variable of its patterns and conditions, no `requires`, the predicate `\top`. -/
theorem U_not_fails : ¬ Fails c' [] U := fun h => by
  cases h with
  | intro h =>
    cases h [] (fun i hi => by rw [leftVars_U] at hi; cases hi) .nil with
    | intro ht _ _ => cases ht
    | pre h => exact absurd (Holds.top_eq h) (by simp)

theorem g_false : Eval c' gl [] (some (bool false)) :=
  .clause (cl := C) (σ := []) hfn (by simp [gfn]) ws_nil .nil (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [C, U, E] at hlt)
    rfl .dv (fun t h => by cases h) .top

/-- `g()` is `false` only: C gives it; U gives nothing (no σ is well sorted on its variables); E
needs U to fail, and the rest needs C to. -/
theorem only_false (r : Option GroundTerm) (h : Eval c' gl [] r) : r = some (bool false) := by
  cases h with
  | clause hfn' hmem hσ _ _ _ hprio _ hrhs _ _ =>
    rw [hfn] at hfn'; cases hfn'
    simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · cases hrhs; rfl
    · exact (no_U_σ hσ).elim
    · exact (U_not_fails (hprio U (by simp [gfn]) rfl (by decide))).elim
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone C (by simp [gfn]) with
    | intro h => cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, C, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre h => exact absurd (Holds.top_eq h) (by simp)
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfn] at hfn'; cases hfn'
    simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact absurd rfl hne
  | exNone hfn' hmem hne =>
    rw [hfn] at hfn'; cases hfn'
    simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact absurd rfl hne
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
    rw [hfn] at hfn'; cases hfn'
    simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> cases ht

/-- E decides nowhere in the form the model reads: U, not `aside` and of a smaller priority, has a
matching instance (σ' := []) over the substitutions `Fails` ranges over. -/
theorem E_not_decides (σ : Subst) : ¬ E.DecidesAt c' gfn σ [] := fun h =>
  h.2 U (by simp [gfn]) rfl (by decide) [] (fun i hi => by rw [leftVars_U] at hi; cases hi) .nil
    ⟨(fun t ht => by cases ht), .top⟩

/-- **`FnSolves` holds**: C decides and gives `false`, the one result; U never applies; E never decides. -/
theorem fnSolves_c : FnSolves c' := by
  intro fn hfn' vs hvs cl hcl σ hdec v
  have hf : fn = gfn := List.mem_singleton.mp hfn'
  subst hf
  have hv : vs = [] := by
    cases vs with
    | nil => rfl
    | cons w ws => obtain ⟨_, _, _, _, h⟩ := sortsOf_cons.mp hvs; cases h
  subst hv
  simp only [gfn, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl
  · refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := C) rfl rfl hdec.1.1 v).symm
    constructor
    · intro h
      cases only_false _ h
      exact ⟨.dv, fun t ht => by cases ht⟩
    · rintro ⟨h, -⟩
      cases h
      exact g_false
  · exact (no_U_σ hdec.1.1).elim
  · exact (E_not_decides σ hdec).elim

end U

/-- info: 'KCore.AsideClausesTest.E5.not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.not_fnDet
/-- info: 'KCore.AsideClausesTest.E5.not_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.not_agree
/-- info: 'KCore.AsideClausesTest.E5.eval_bb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.eval_bb
/-- info: 'KCore.AsideClausesTest.E5.eval_ay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.eval_ay
/-- info: 'KCore.AsideClausesTest.G.not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G.not_fnDet
/-- info: 'KCore.AsideClausesTest.G.not_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G.not_agree
/-- info: 'KCore.AsideClausesTest.U.only_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms U.only_false
/-- info: 'KCore.AsideClausesTest.U.E_not_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms U.E_not_decides
/-- info: 'KCore.AsideClausesTest.U.fnSolves_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms U.fnSolves_c

end KCore.AsideClausesTest
