/-
  The function lemmas at a clause with a predicate in its premise (`Clause.pre`), on the semantics
  of CN-4 §4.9's expectation, built by hand. Run from the package root:
  `lake env lean -j1 test/ClausePreFn.lean`. Kernel-checked.

  The semantics `c`, two functions over Int:
  - `u(X:Int) => X ensures X >Int 0` (`uCl`): `u(0)` has no value (`Eval.ensFails`), `u(2)` is 2;
  - `g(X:Int)` with `gCl1`, `pre := ⌈u(X)⌉`, `rhs := 1`, of priority 50, and `gCl2`, `rhs := 0`, of
    priority 200.

  What is shown, none of it through a hypothesis that says a predicate is `\top`:
  - `coherent`, `fnDet`: the clauses that compete are coherent, so every function of `c` has at
    most one result (`fnDet_of_coherent`).
  - `gAt0`, `gAt2`: `g(0)` is 0 and nothing else (`gCl1` fails by `ReqFails.pre`, `⌈u(0)⌉` being
    false), `g(2)` is 1 and nothing else (`gCl1` meets `hpre` and blocks `gCl2`).
  - `decides0`, `decides2`: `gCl2` decides at `[0]` and `gCl1` at `[2]` (`Clause.DecidesAt`).
  - `solves0`, `solves2`: where a clause of `g` decides at `[0]` or at `[2]`, the values of `g` are
    that clause's right-hand side's (`solves_of_parts`: `FnSolves`' statement for `g` at these
    arguments), its `PrioDecided` premise from the truth value of `⌈u(X)⌉` there.

  `c` is outside `coreOK` while `clausesPlain` asks `cl.pre.isTop`, so `HypSoundCore c` is false
  and `prioDecided_of_total_pre`, `fnSolves_of_total_pre` have no instance at `c`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ClausePreFn

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- An integer literal, as a term and as a value. -/
def iT (i : Int) : Term := .dv Srt.int (.int i)
def iv (i : Int) : GroundTerm := .dv Srt.int (.int i)

/-- The symbols after the four cell symbols: u, g. -/
def U : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5

/-- `u(X)`, X the variable 0. -/
def uX : Term := .app U [.var 0]

/-- `u(X) => X ensures X >Int 0`. -/
def uCl : Clause := ⟨[Srt.int], [.var 0], none, .var 0, some (.app intGt [.var 0, iT 0]), 50, false, [], .top, .top⟩
def uFn : Fn := ⟨U, [Srt.int], Srt.int, [uCl], false⟩

/-- `⌈u(X)⌉`. -/
def pre1 : Cond := .ceil Srt.int uX

/-- `g(X) => 1` where `⌈u(X)⌉`, of priority 50. -/
def gCl1 : Clause := ⟨[Srt.int], [.var 0], none, iT 1, none, 50, false, [], pre1, .top⟩
/-- `g(X) => 0`, of priority 200. -/
def gCl2 : Clause := ⟨[Srt.int], [.var 0], none, iT 0, none, 200, false, [], .top, .top⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int, [gCl1, gCl2], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblu", "Lblg"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [uFn, gFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem lookups : c.lookupFn U = some uFn ∧ c.lookupFn G = some gFn := ⟨rfl, rfl⟩

theorem kinds : isHook intGt = true ∧ c.isCtor intGt = false ∧
    c.isCtor U = false ∧ isHook U = false ∧ c.isParam U = false ∧ c.isOvl U = false ∧
    c.isCtor G = false ∧ isHook G = false ∧ c.isParam G = false ∧ c.isOvl G = false := by decide +kernel

theorem gt_at : c.hookRes intGt [iv 0, iv 0] = some (some (bool false)) ∧
    c.hookRes intGt [iv 2, iv 0] = some (some (bool true)) := by decide +kernel

/-- `gCl1`'s predicate is well sorted over its variables and is not `\top`. -/
theorem pre_ok : c.condOK gCl1.vars gCl1.pre = true ∧ gCl1.pre.isTop = false := by decide +kernel

/-! ## Matches -/

/-- A match of the one pattern `X` at `vs`: `vs` is one value, σ's at X. -/
theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals c σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

theorem match_at {σ : Subst} {x : GroundTerm} (h : PatVals c σ [.var 0] [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, hv, hl⟩ := match0 h
  cases hv; exact hl

/-- The substitution of X by an integer. -/
def sg (x : Int) : Subst := [(0, iv x)]

theorem sg_sorted (x : Int) : c.WellSorted [Srt.int] (sg x) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨iv x, rfl, sortOf_int (c := c) x⟩
  | succ i => simp at hs

theorem sg_match (x : Int) : PatVals c (sg x) [.var 0] [iv x] := .cons (.var rfl) .nil

/-! ## Coherence, and one result -/

theorem mem_fns {fn : Fn} (h : fn ∈ c.fns) : fn = uFn ∨ fn = gFn := by
  simpa [c] using h

theorem coherent_lit {cl : Clause} (hr : varOccs cl.rhs = []) (he : cl.ens = none) (hx : cl.exs = []) :
    MatchIndependent c cl := by
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => ?_
  exact .inl ⟨hx, hx, rfl, rfl, (fun i hi => by rw [hr] at hi; cases hi), (fun t ht => by rw [he] at ht; cases ht)⟩

theorem coherent_u : Coherent c uCl uCl := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨v, rfl, hl⟩ := match0 ha.2.1
  have hl' := match_at ha'.2.1
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht i hi => ?_⟩
  · have : i = 0 := by simpa [uCl, varOccs] using hi
    subst this; rw [hl, hl']
  · have ht' : t = .app intGt [.var 0, iT 0] := by simpa [uCl] using ht.symm
    subst ht'
    have : i = 0 := by simpa [varOccs, varOccsList, iT] using hi
    subst this; rw [hl, hl']

/-- The clauses that compete are coherent: `u`'s one clause and each clause of `g` with itself
(the two clauses of `g` are of different priorities and not `aside`, so they do not compete). -/
theorem coherent : CoherentAll c :=
  Faithful.coherentAll_ofCl
    (fun fn hfn cl cl' hp hprio => by
      rcases mem_fns hfn with rfl | rfl
      · simp [uFn, pairs] at hp
      · have : cl = gCl1 ∧ cl' = gCl2 := by simpa [gFn, pairs] using hp
        obtain ⟨rfl, rfl⟩ := this
        exact absurd hprio (not_compete (by decide)))
    (fun fn hfn cl hcl => by
      rcases mem_fns hfn with rfl | rfl
      · have : cl = uCl := by simpa [uFn] using hcl
        subst this; exact (matchIndependent_iff_noExs rfl).mpr coherent_u
      · have : cl = gCl1 ∨ cl = gCl2 := by simpa [gFn] using hcl
        rcases this with rfl | rfl
        · exact coherent_lit rfl rfl rfl
        · exact coherent_lit rfl rfl rfl)

/-- **Every function of `c` has at most one result**, `gCl1`'s predicate being `⌈u(X)⌉`. -/
theorem fnDet : FnDet c := fnDet_of_coherent coherent

/-! ## `u` at 0 and at 2 -/

theorem gt_eval {σ : Subst} {x : Int} {b : Bool} (hl : σ.lookup 0 = some (iv x))
    (hh : c.hookRes intGt [iv x, iv 0] = some (some (bool b))) :
    EvalTerm c σ (.app intGt [.var 0, iT 0]) (some (bool b)) := by
  refine .hook (rs := [some (iv x), some (iv 0)]) kinds.2.1 kinds.1 (.cons (hl ▸ .var) (.cons .dv .nil))
    (fun vs hvs => ?_) (fun h => by simp [allSome] at h)
  have : vs = [iv x, iv 0] := by simpa [allSome] using hvs.symm
  subst this; exact hh

/-- `u(0)` has no value: its `ensures` is `false`. -/
theorem uAt0 : Eval c U [iv 0] none :=
  .ensFails (cl := uCl) (σ := sg 0) lookups.1 (List.mem_singleton_self _) (sg_sorted 0) (sg_match 0)
    (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      have : cl' = uCl := by simpa [uFn] using hcl'
      subst this; exact absurd hlt (Nat.lt_irrefl _))
    rfl rfl (gt_eval rfl gt_at.1) (by decide)

/-- `u(2)` is 2. -/
theorem uAt2 : Eval c U [iv 2] (some (iv 2)) :=
  .clause (cl := uCl) (σ := sg 2) lookups.1 (List.mem_singleton_self _) (sg_sorted 2) (sg_match 2)
    (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      have : cl' = uCl := by simpa [uFn] using hcl'
      subst this; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => by
      have ht' : t = .app intGt [.var 0, iT 0] := by simpa [uCl] using ht.symm
      subst ht'; exact gt_eval rfl gt_at.2) .top

/-! ## The predicate `⌈u(X)⌉` at 0 and at 2 -/

theorem uX_eval {σ : Subst} {x : Int} {r : Option GroundTerm} (hl : σ.lookup 0 = some (iv x))
    (h : Eval c U [iv x] r) : EvalTerm c σ uX r :=
  .call (rs := [some (iv x)]) kinds.2.2.1 kinds.2.2.2.1 (.cons (hl ▸ .var) .nil) rfl h kinds.2.2.2.2.1

/-- `⌈u(X)⌉` is false at X := 0. -/
theorem preAt0 {σ : Subst} (hl : σ.lookup 0 = some (iv 0)) : Holds c 1 σ pre1 false :=
  .ceil (r := none) (uX_eval hl uAt0)

/-- `⌈u(X)⌉` is true at X := 2. -/
theorem preAt2 {σ : Subst} (hl : σ.lookup 0 = some (iv 2)) : Holds c 1 σ pre1 true :=
  .ceil (r := some (iv 2)) (uX_eval hl uAt2)

/-! ## `g` at 0 and at 2 -/

theorem mem_g {cl : Clause} (h : cl ∈ gFn.clauses) : cl = gCl1 ∨ cl = gCl2 := by
  simpa [gFn] using h

/-- `gCl1` fails at `[0]`: at each match its predicate is false (`ReqFails.pre`). -/
theorem fails1_at0 : Fails c [iv 0] gCl1 :=
  .intro fun _ _ hp => .pre (preAt0 (match_at hp))

/-- `f`'s result at `[iv x]` is `r` and only `r`. -/
def OnlyResult (f : Sym) (x : Int) (r : Option GroundTerm) : Prop :=
  Eval c f [iv x] r ∧ ∀ r', Eval c f [iv x] r' → r' = r

/-- **`g(0)` is 0 and nothing else**: the first clause fails, its predicate being false, and the
second decides. -/
theorem gAt0 : OnlyResult G 0 (some (iv 0)) := by
  have h : Eval c G [iv 0] (some (iv 0)) :=
    .clause (cl := gCl2) (σ := sg 0) lookups.2 (by simp [gFn]) (sg_sorted 0) (sg_match 0)
      (fun _ h => nomatch h) .top
      (fun cl' hcl' _ hlt => by
        rcases mem_g hcl' with rfl | rfl
        · exact fails1_at0
        · exact absurd hlt (Nat.lt_irrefl _))
      rfl .dv (fun _ h => nomatch h) .top
  exact ⟨h, fun r' h' => fnDet _ _ _ _ h' h⟩

/-- **`g(2)` is 1 and nothing else**: the first clause's predicate is true, so it decides. -/
theorem gAt2 : OnlyResult G 2 (some (iv 1)) := by
  have h : Eval c G [iv 2] (some (iv 1)) :=
    .clause (cl := gCl1) (σ := sg 2) lookups.2 (by simp [gFn]) (sg_sorted 2) (sg_match 2)
      (fun _ h => nomatch h) (preAt2 (σ := sg 2) rfl)
      (fun cl' hcl' _ hlt => by
        rcases mem_g hcl' with rfl | rfl
        · exact absurd hlt (Nat.lt_irrefl _)
        · exact absurd hlt (by decide))
      rfl .dv (fun _ h => nomatch h) .top
  exact ⟨h, fun r' h' => fnDet _ _ _ _ h' h⟩

/-! ## Where a clause of `g` decides -/

/-- `gCl2` decides at `[0]`: `gCl1`, the one clause of a smaller priority, does not apply there. -/
theorem decides0 : gCl2.DecidesAt c gFn (sg 0) [iv 0] := by
  refine ⟨⟨sg_sorted 0, sg_match 0, (fun _ h => nomatch h), .top⟩, fun cl' hcl' _ hlt σ' _ hp' h => ?_⟩
  rcases mem_g hcl' with rfl | rfl
  · exact absurd (Holds.functional_of_fnDet fnDet h.2 (preAt0 (match_at hp'))) (by simp)
  · exact absurd hlt (Nat.lt_irrefl _)

/-- `gCl1` decides at `[2]`: its predicate is true there, and no clause is of a smaller priority. -/
theorem decides2 : gCl1.DecidesAt c gFn (sg 2) [iv 2] := by
  refine ⟨⟨sg_sorted 2, sg_match 2, (fun _ h => nomatch h), preAt2 (σ := sg 2) rfl⟩, fun cl' hcl' _ hlt => ?_⟩
  rcases mem_g hcl' with rfl | rfl
  · exact absurd hlt (Nat.lt_irrefl _)
  · exact absurd hlt (by decide)

/-- Each clause of `g` has an instance result at each σ: no `ensures`, a literal right-hand side. -/
theorem instRes {cl : Clause} (hcl : cl ∈ gFn.clauses) (σ : Subst) : ∃ r, cl.InstRes c σ r := by
  rcases mem_g hcl with rfl | rfl
  · exact ⟨_, .inl ⟨(fun _ h => nomatch h), .dv⟩⟩
  · exact ⟨_, .inl ⟨(fun _ h => nomatch h), .dv⟩⟩

/-- **Evaluation solves `g`'s equations at `[x]`** where `⌈u(X)⌉` has a truth value at X := x: where
a clause of `g` decides, the values of `g` are that clause's right-hand side's (`solves_of_parts`). -/
theorem solves_at {x : Int} {b : Bool} (hb : ∀ σ, σ.lookup 0 = some (iv x) → Holds c 1 σ pre1 b)
    {cl : Clause} (hcl : cl ∈ gFn.clauses) {σ : Subst} (hdec : cl.DecidesAt c gFn σ [iv x]) (v : GroundTerm) :
    Eval c G [iv x] (some v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) :=
  solves_of_parts (fn := gFn) lookups.2 fnDet
    (fun cl hcl => by rcases mem_g hcl with rfl | rfl <;> exact ⟨rfl, rfl⟩)
    (fun _ _ _ _ cl' hcl' _ _ σ' _ hp' => by
      rcases mem_g hcl' with rfl | rfl
      · exact ⟨(fun _ h => nomatch h), b, hb σ' (match_at hp')⟩
      · exact ⟨(fun _ h => nomatch h), true, .top⟩)
    (fun _ _ cl' σ' _ hcl' _ _ _ => instRes hcl' σ')
    hcl hdec v

/-- At `[0]`, where `⌈u(X)⌉` is false. -/
theorem solves0 {cl : Clause} (hcl : cl ∈ gFn.clauses) {σ : Subst} (hdec : cl.DecidesAt c gFn σ [iv 0])
    (v : GroundTerm) : Eval c G [iv 0] (some v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) :=
  solves_at (fun _ hl => preAt0 hl) hcl hdec v

/-- At `[2]`, where `⌈u(X)⌉` is true. -/
theorem solves2 {cl : Clause} (hcl : cl ∈ gFn.clauses) {σ : Subst} (hdec : cl.DecidesAt c gFn σ [iv 2])
    (v : GroundTerm) : Eval c G [iv 2] (some v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) :=
  solves_at (fun _ hl => preAt2 hl) hcl hdec v

/-- The two instances, read: `g(0)`'s values are `gCl2`'s right-hand side's, `g(2)`'s are `gCl1`'s. -/
theorem solved : (∀ v, Eval c G [iv 0] (some v) ↔ v = iv 0) ∧ (∀ v, Eval c G [iv 2] (some v) ↔ v = iv 1) := by
  refine ⟨fun v => (solves0 (by simp [gFn]) decides0 v).trans ⟨fun h => ?_, fun h => ?_⟩,
    fun v => (solves2 (by simp [gFn]) decides2 v).trans ⟨fun h => ?_, fun h => ?_⟩⟩
  · cases h.1; rfl
  · subst h; exact ⟨.dv, (fun _ h => nomatch h)⟩
  · cases h.1; rfl
  · subst h; exact ⟨.dv, (fun _ h => nomatch h)⟩

/-! ## The semantics that shows `FnSolves` cannot be dropped meets `ClausePreDecided` -/

/-- `FnSolvesWitness.c` has `coreOK`, `FnDet` and `OpenLaws` and no model of its theory; it meets
`ClausePreDecided` too, its clauses' predicates being `⊤`, so of `consistent_of`'s hypotheses it
lacks `FnSolves` alone. -/
example : ClausePreDecided FnSolvesWitness.c := clausePreDecided_of_isTop (by decide +kernel)

/-! ## Axioms -/

/-- info: 'KCore.ClausePreFn.fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnDet
/-- info: 'KCore.ClausePreFn.solved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms solved

end ClausePreFn

end KCore
