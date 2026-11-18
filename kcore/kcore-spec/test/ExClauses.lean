/-
  Clauses with existential variables on the evaluation block, kernel-checked: hand-built semantics
  of one function `fl()` (or `h(K)`) over a small definition, and what `Eval`, `Clause.Res`,
  `Coherent`, `MatchIndependent` and `FnSolves` say of them.

  - F1 `fl() => ?B ensures ?B`: the result `true` by `clauseEx`, no result `none`, one result at
    `fl()`; `MatchIndependent` holds; `FnSolves` holds.
  - F2 `fl() => ?B`: no result (the instances differ).
  - F3 `fl() => ?B ensures false`: the result `none` by `exNone`.
  - C `f() => g(?Z:Int)` with `post := Z ∈ lp()`, `lp() => lp()`: no result at all (`lp()` has
    none, so `post` has no truth value at any instance).
  - K2 `fl() => true` beside `fl() => ?B`: the one result `true`, every two clauses coherent,
    the second clause not match independent (it has no `Res`), and `FnSolves` false.
  - Q `fl() => true` beside `fl() => false` with `post := ⊥`: both clauses match independent,
    `FnSolves` false.
  - P `fl() => Y` with `post := ⊥`, no `exs`: no result, and the clause coherent with itself.
  - c, s, vac: a variable fixed by a term over a confined variable (`c_some`, `c_res`), by a binder
    (`s_some`, `s_res`), and a binder over a sort without a value (`vac_ex`, `vac_some`).
  - h `h(K) => ?Z` with `post := inj{Int,KItem}(Z) = K`: the result 3 at `inj(3)` by `clauseEx`, and
    `none` at `inj{Bool,KItem}(true)` by `exNone`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.ExClausesTest

open KCore
open GroundTerm
/-- The configuration `<k> K </k>` with the generated counter. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def fl : Sym := nRegSyms + 4
def fnOf (cls : List Clause) : Fn := { label := fl, args := [], result := Srt.bool, clauses := cls }
def cF (cls : List Clause) : Semantics :=
  { base with symNames := base.symNames ++ ["Lblfl"], fns := [fnOf cls] }

theorem lookup_fl (cls : List Clause) : (cF cls).lookupFn fl = some (fnOf cls) := by
  rw [Semantics.lookupFn_eq]; rfl

theorem lookup_cons_self (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lookup_cons_ne {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

/-- The extension of σ that gives the variable 0 the Bool b. -/
def ext (b : Bool) (σ : Subst) : Subst := (0, bool b) :: σ

theorem ext_sorted (c : Semantics) (b : Bool) (σ : Subst) : c.WellSorted [Srt.bool] (ext b σ) := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, lookup_cons_self _ _ _, sortOf_bool b⟩

theorem ext_agree (b : Bool) (σ : Subst) : AgreeOff [0] σ (ext b σ) := by
  intro i hi
  exact lookup_cons_ne _ _ (fun h => hi (by simp [h]))

theorem nil_sorted (c : Semantics) (σ : Subst) : c.WellSorted [] σ := by
  intro i s h; simp at h

theorem sortsOf_nil {c : Semantics} {vs : List GroundTerm} (h : c.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    rw [Semantics.sortsOf] at h
    split at h <;> cases h

theorem holds_cast {c : Semantics} {n : Nat} {σ : Subst} {p : Cond} {b b' : Bool}
    (h : Holds c n σ p b) (e : b = b') : Holds c n σ p b' := e ▸ h

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]
theorem sameResult_self (v : GroundTerm) : sameResult (some v) (some v) = true := sameResult_some.mpr rfl
theorem sameResult_ne {v w : GroundTerm} (h : v ≠ w) : sameResult (some v) (some w) = false := by
  cases hs : sameResult (some v) (some w) with
  | false => rfl
  | true => exact absurd (sameResult_some.mp hs) h

/-! ## F1: `fl() => ?B ensures ?B` -/

def clB : Clause := { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := some (.var 0), exs := [0] }
abbrev c1 : Semantics := cF [clB]

theorem clB_free : Clause.exsFree clB = [0] := by decide

/-- Every instance of `clB` at a Bool value is decided and gives `true` or nothing. -/
theorem f1_hall (c : Semantics) (σ' : Subst) (hσ' : c.WellSorted clB.vars σ') : InstIs c σ' clB (some (bool true)) := by
  obtain ⟨v, hv, -⟩ := hσ' 0 Srt.bool rfl
  by_cases hvt : v = bool true
  · subst hvt
    have e : EvalTerm c σ' (.var 0) (some (bool true)) := hv ▸ .var (i := 0)
    exact .gives e (fun t ht => by cases ht; exact e) .top
  · exact .fails .top (.ens (t := .var 0) rfl (.var (i := 0)) (by rw [hv]; intro h; exact hvt (Option.some.inj h)))

/-- **`fl()` is `true`**, by `clauseEx`: the instance at B ↦ true gives `true`, the others give
nothing (their `ensures` is not `true`). -/
theorem f1_some : Eval c1 fl [] (some (bool true)) := by
  refine .clauseEx (cl := clB) (σ := ext true []) (lookup_fl _) (by simp [fnOf]) (ext_sorted _ _ _) .nil
    (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) (by decide) ?_ ?_ .top ?_
  · simp [fnOf] at hm; subst hm; exact absurd hlt (by decide)
  · exact .var (i := 0)
  · intro t ht; cases ht; exact .var (i := 0)
  · exact fun σ' _ hσ' => f1_hall _ σ' hσ'

/-- At every match, `true` is a result of `clB` (`Clause.Res`, the giving case). -/
theorem f1_res (c : Semantics) (σ : Subst) : Clause.Res c clB σ (some (bool true)) :=
  Or.inr (And.intro (by decide) (Or.inl ⟨ext true σ, bool true, clB_free ▸ ext_agree true σ, ext_sorted _ _ _,
    ⟨.var (i := 0), (fun t ht => by cases ht; exact .var (i := 0)), .top⟩,
    fun σ'' _ h => f1_hall _ σ'' h, rfl⟩))

theorem clB_not_fails (c : Semantics) (σ : Subst) : ¬ InstFails c (ext true σ) clB := by
  intro h
  cases h with
  | ens ht he hw => cases ht; exact hw (EvalTerm.var_inv he)
  | post h => cases h
  | rhs h => have := EvalTerm.var_inv h; simp [ext, lookup_cons_self] at this

theorem clB_not_reqFails (c : Semantics) (σ : Subst) : ¬ ReqFails c σ clB := by
  intro h
  cases h with
  | intro ht _ _ => cases ht
  | pre h => cases h

/-- Every result of `clB` at a match is `true`. -/
theorem clB_res_true (c : Semantics) (σ : Subst) {r : Option GroundTerm} (h : Clause.Res c clB σ r) :
    r = some (bool true) := by
  rcases h with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, ⟨hr, he, -⟩, -, rfl⟩ | ⟨-, -, hall⟩⟩
  · cases hex
  · rw [EvalTerm.var_inv hr, ← EvalTerm.var_inv (he _ rfl)]
  · have hi := hall (ext true σ) (clB_free ▸ ext_agree true σ) (ext_sorted _ _ _)
    generalize hn : (none : Option GroundTerm) = r0 at hi
    cases hi with
    | fails _ h => exact absurd h (clB_not_fails _ _)
    | gives _ _ _ => cases hn

/-- `fl()` has the one result `true`. -/
theorem f1_only {r : Option GroundTerm} (h : Eval c1 fl [] r) : r = some (bool true) := by
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; cases hex
  | @rest _ fn _ hfn hnone =>
    rw [lookup_fl] at hfn; cases hfn
    cases hnone clB (by simp [fnOf]) with
    | intro h => exact absurd (h [] (fun i hi => by cases hi) .nil) (clB_not_reqFails _ _)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex ht he hw =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; cases hex
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem
    rw [EvalTerm.var_inv hrhs, ← EvalTerm.var_inv (hens _ rfl)]
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem
    have hi := hall (ext true σ) (clB_free ▸ ext_agree true σ) (ext_sorted _ _ _)
    generalize hn : (none : Option GroundTerm) = r0 at hi
    cases hi with
    | fails _ h => exact absurd h (clB_not_fails _ _)
    | gives _ _ _ => cases hn

/-- **No result `none`** at `fl()`. -/
theorem f1_not_none : ¬ Eval c1 fl [] none := fun h => by cases f1_only h

/-- **`FnDet` at `fl()`**: two results there are one. -/
theorem f1_fnDet {r r' : Option GroundTerm} (h : Eval c1 fl [] r) (h' : Eval c1 fl [] r') : r = r' :=
  (f1_only h).trans (f1_only h').symm

/-- **`clB` is match independent**: coherent with itself (its results at two matches are `true`),
and with a result at each match. -/
theorem f1_matchIndependent : MatchIndependent c1 clB := by
  refine ⟨fun vs σ σ' _ _ _ _ _ _ _ => .inr fun r r' h h' => ?_, fun _ _ _ _ σ _ _ _ => ⟨_, f1_res _ σ⟩⟩
  rw [clB_res_true _ _ h, clB_res_true _ _ h']

/-- **`FnSolves` holds in `c1`**: the values of `fl()` are the values the extensions give. -/
theorem f1_solves : FnSolves c1 := by
  intro fn hfn vs hvs cl hcl σ _ v
  simp [cF] at hfn; subst hfn
  cases sortsOf_nil hvs
  simp [fnOf] at hcl; subst hcl
  constructor
  · intro h
    cases Option.some.inj (f1_only h)
    exact ⟨ext true σ, clB_free ▸ ext_agree true σ, ext_sorted _ _ _,
      .var (i := 0), (fun t ht => by cases ht; exact .var (i := 0)), .top⟩
  · rintro ⟨σ', -, -, h1, h2, -⟩
    have e1 := EvalTerm.var_inv h1
    have e2 := EvalTerm.var_inv (h2 _ rfl)
    rw [← e2] at e1
    cases e1
    exact f1_some

/-! ## F2: `fl() => ?B`, no `ensures`: no result (the instances differ) -/

def clN : Clause := { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := none, exs := [0] }
abbrev c2 : Semantics := cF [clN]

theorem clN_free : Clause.exsFree clN = [0] := by decide

theorem clN_not_fails (c : Semantics) (b : Bool) (σ : Subst) : ¬ InstFails c (ext b σ) clN := by
  intro h
  cases h with
  | ens ht _ _ => cases ht
  | post h => cases h
  | rhs h => have := EvalTerm.var_inv h; simp [ext, lookup_cons_self] at this

/-- The instance at B ↦ b is `b` and nothing else. -/
theorem clN_is (c : Semantics) (b : Bool) (σ : Subst) {r : Option GroundTerm}
    (h : InstIs c (ext b σ) clN r) : r = some (bool b) := by
  cases h with
  | fails _ h => exact absurd h (clN_not_fails _ _ _)
  | gives hrhs _ _ => rw [EvalTerm.var_inv hrhs]; exact lookup_cons_self _ _ _

/-- The instances of `clN` at one match do not agree on a result. -/
theorem clN_differ (c : Semantics) (σ : Subst) (r : Option GroundTerm)
    (hall : ∀ σ', AgreeOff (Clause.exsFree clN) σ σ' → c.WellSorted clN.vars σ' → InstIs c σ' clN r) : False := by
  have h1 := clN_is c true σ (hall _ (clN_free ▸ ext_agree true σ) (ext_sorted _ _ _))
  have h2 := clN_is c false σ (hall _ (clN_free ▸ ext_agree false σ) (ext_sorted _ _ _))
  rw [h1] at h2
  simp [bool] at h2

theorem clN_not_reqFails (c : Semantics) (σ : Subst) : ¬ ReqFails c σ clN := by
  intro h
  cases h with
  | intro ht _ _ => cases ht
  | pre h => cases h

/-- **`fl()` has no result.** -/
theorem f2_none {r : Option GroundTerm} : ¬ Eval c2 fl [] r := by
  intro h
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; cases hex
  | @rest _ fn _ hfn hnone =>
    rw [lookup_fl] at hfn; cases hfn
    cases hnone clN (by simp [fnOf]) with
    | intro h => exact absurd (h [] (fun i hi => by cases hi) .nil) (clN_not_reqFails _ _)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex ht he hw =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; cases hex
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem
    exact clN_differ _ σ _ hall
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem
    exact clN_differ _ σ _ hall

/-- `clN` has no `Res` at any match, in any semantics. -/
theorem clN_noRes (c : Semantics) (σ : Subst) (r : Option GroundTerm) : ¬ Clause.Res c clN σ r := by
  rintro (⟨hex, -⟩ | ⟨-, (⟨_, v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩)⟩)
  · cases hex
  · exact clN_differ c σ _ hall
  · exact clN_differ c σ _ hall

/-! ## F3: `fl() => ?B ensures false`: the result `none`, by `exNone` -/

def clZ : Clause :=
  { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := some (.dv Srt.bool (.bool false)), exs := [0] }
abbrev c3 : Semantics := cF [clZ]

theorem clZ_free : Clause.exsFree clZ = [0] := by decide

theorem f3_none : Eval c3 fl [] none := by
  refine .exNone (cl := clZ) (σ := []) (lookup_fl _) (by simp [fnOf]) (by decide) (fun i hi => by cases hi) .nil
    (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) ⟨ext true [], clZ_free ▸ ext_agree true [], ext_sorted _ _ _⟩ ?_
  · simp [fnOf] at hm; subst hm; exact absurd hlt (by decide)
  · intro σ' _ _
    exact .fails .top (.ens (t := .dv Srt.bool (.bool false)) rfl .dv (by simp [bool]))

/-- `Res` at the match of `fl()` is `none`. -/
theorem f3_res : Clause.Res c3 clZ [] none :=
  .inr ⟨by decide, .inr ⟨rfl, ⟨ext true [], clZ_free ▸ ext_agree true [], ext_sorted _ _ _⟩, fun σ' _ _ =>
    .fails .top (.ens (t := .dv Srt.bool (.bool false)) rfl .dv (by simp [bool]))⟩⟩

/-! ## K2: `fl() => true` beside `fl() => ?B`, of one priority

`fl()` has the one result `true`, every two clauses are coherent (the second has no `Res` at its
match, so coherence with it asks nothing), the second clause is not match independent (the owed
fact, a `Res` at each match where it decides, is false), and `FnSolves` is false: the instance
B ↦ false gives `false`, which is no result. -/

def clT : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
abbrev cK : Semantics := cF [clT, clN]

theorem clT_not_reqFails (c : Semantics) (σ : Subst) : ¬ ReqFails c σ clT := by
  intro h
  cases h with
  | intro ht _ _ => cases ht
  | pre h => cases h

theorem noPrioK {vs : List GroundTerm} {cl : Clause} (hc : cl.prio = 50) :
    ∀ cl' ∈ (fnOf [clT, clN]).clauses, cl'.aside = false → cl'.prio < cl.prio → Fails cK vs cl' := by
  intro cl' hm _ hlt
  simp [fnOf] at hm
  rcases hm with rfl | rfl <;> exact absurd hlt (by rw [hc]; decide)

theorem k2_true : Eval cK fl [] (some (bool true)) :=
  .clause (cl := clT) (σ := []) (lookup_fl _) (by simp [fnOf]) (nil_sorted _ _) .nil (fun t ht => by cases ht) .top
    (noPrioK rfl) rfl .dv (fun t ht => by cases ht) .top

theorem k2_only {r : Option GroundTerm} (h : Eval cK fl [] r) : r = some (bool true) := by
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem
    rcases hmem with rfl | rfl
    · exact EvalTerm.dv_inv hrhs
    · cases hex
  | @rest _ fn _ hfn hnone =>
    rw [lookup_fl] at hfn; cases hfn
    cases hnone clT (by simp [fnOf]) with
    | intro h => exact absurd (h [] (fun i hi => by cases hi) .nil) (clT_not_reqFails _ _)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex ht he hw =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem
    rcases hmem with rfl | rfl
    · cases ht
    · cases hex
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem
    rcases hmem with rfl | rfl
    · exact absurd rfl hne
    · exact absurd hall (fun h => clN_differ _ σ _ h)
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem
    rcases hmem with rfl | rfl
    · exact absurd rfl hne
    · exact absurd hall (fun h => clN_differ _ σ _ h)

theorem clT_res (c : Semantics) (σ : Subst) (r : Option GroundTerm) (h : Clause.Res c clT σ r) :
    r = some (bool true) := by
  rcases h with ⟨-, (⟨-, -, hr⟩ | ⟨t, w, ht, -⟩)⟩ | ⟨hne, -⟩
  · exact EvalTerm.dv_inv hr
  · cases ht
  · exact absurd rfl hne

/-- **Every two clauses of `fl` are coherent in `cK`.** -/
theorem k2_coherent : ∀ cl ∈ [clT, clN], ∀ cl' ∈ [clT, clN], Coherent cK cl cl' := by
  intro cl hm cl' hm'
  simp at hm hm'
  intro vs σ σ' _ _ _ _ _ _ _
  refine .inr fun r r' h1 h2 => ?_
  rcases hm with rfl | rfl
  · rcases hm' with rfl | rfl
    · rw [clT_res _ _ _ h1, clT_res _ _ _ h2]
    · exact absurd h2 (clN_noRes _ _ _)
  · exact absurd h1 (clN_noRes _ _ _)

theorem appliesN (c : Semantics) (b : Bool) : clN.AppliesAt c (ext b []) [] :=
  ⟨ext_sorted _ _ _, .nil, (fun t ht => by cases ht), .top⟩

theorem k2_decidesN (b : Bool) : Clause.Decides cK (fnOf [clT, clN]) clN (ext b []) [] :=
  ⟨appliesN _ b, noPrioK rfl⟩

/-- **The owed fact is false at `clN`**: it decides at `fl()`'s match and has no `Res` there, so it is
not match independent (though coherent with itself, `k2_coherent`). -/
theorem k2_not_matchIndependent : ¬ MatchIndependent cK clN := fun h => by
  obtain ⟨r, hr⟩ := h.2 (by decide) fl _ [] (ext true []) (lookup_fl _) (by simp [fnOf]) (k2_decidesN true)
  exact clN_noRes _ _ _ hr

theorem k2_terminates : FnTerminates cK := by
  intro fn hfn vs hvs
  simp [cF] at hfn; subst hfn
  cases sortsOf_nil hvs
  exact ⟨_, k2_true⟩

/-- **`FnSolves` is false in `cK`**, without the owed fact. -/
theorem k2_not_solves : ¬ FnSolves cK := by
  intro h
  have hdec : Clause.DecidesAt cK (fnOf [clT, clN]) clN (ext true []) [] :=
    ⟨appliesN _ true, fun cl' hm _ hlt => by
      simp [fnOf] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide)⟩
  have := (h (fnOf [clT, clN]) (by simp [cF]) [] rfl clN (by simp [fnOf]) _ hdec (bool false)).mpr
    ⟨ext false (ext true []), clN_free ▸ ext_agree false _, ext_sorted _ _ _,
      .var (i := 0), (fun t ht => by cases ht), .top⟩
  have := k2_only this
  simp [bool] at this

/-! ## Q: `fl() => true` beside `fl() => false` with `post := ⊥`, of one priority

Both clauses are match independent; `FnSolves` is false: where the second decides, `fl()` has the
value `true`, which no instance of it gives (its `post` is false). -/

def clQ : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.bool (.bool false), ens := none, post := .bot }
abbrev cQ : Semantics := cF [clT, clQ]

theorem q_true : Eval cQ fl [] (some (bool true)) :=
  .clause (cl := clT) (σ := []) (lookup_fl _) (by simp [fnOf]) (nil_sorted _ _) .nil (fun t ht => by cases ht) .top
    (fun cl' hm _ hlt => by simp [fnOf] at hm; rcases hm with rfl | rfl <;> exact absurd hlt (by decide))
    rfl .dv (fun t ht => by cases ht) .top

/-- **Both clauses of `fl` are match independent in `cQ`.** -/
theorem q_matchIndependent : ∀ cl ∈ (fnOf [clT, clQ]).clauses, MatchIndependent cQ cl := by
  intro cl hm
  simp [fnOf] at hm
  rcases hm with rfl | rfl
  · exact (matchIndependent_iff_noExs rfl).mpr fun _ _ _ _ _ _ _ _ _ _ =>
      .inl ⟨rfl, rfl, rfl, rfl, fun i hi => by simp [clT, varOccs] at hi, fun t ht => by cases ht⟩
  · exact (matchIndependent_iff_noExs rfl).mpr fun _ _ _ _ _ _ _ _ _ _ =>
      .inl ⟨rfl, rfl, rfl, rfl, fun i hi => by simp [clQ, varOccs] at hi, fun t ht => by cases ht⟩

/-- **`FnSolves` is false in `cQ`**: its clauses' predicates are not all `\top`. -/
theorem q_not_solves : ¬ FnSolves cQ := by
  intro h
  have hap : clQ.AppliesAt cQ [] [] := ⟨nil_sorted _ _, .nil, (fun t ht => by cases ht), .top⟩
  have hdec : Clause.DecidesAt cQ (fnOf [clT, clQ]) clQ [] [] :=
    ⟨hap, fun cl' hm _ hlt => by
      simp [fnOf] at hm
      rcases hm with rfl | rfl <;> exact absurd hlt (by decide)⟩
  obtain ⟨σ', -, -, -, -, hp⟩ := (h (fnOf [clT, clQ]) (by simp [cF]) [] rfl clQ (by simp [fnOf]) [] hdec (bool true)).mp q_true
  cases hp

/-! ## P: `fl() => Y` with `post := ⊥`, without existential variables

`fl()` has no result, and the clause is coherent with itself: a result of it (`Clause.Res`) needs
its `post` true. -/

def clP : Clause := { vars := [Srt.int], pats := [], req := none, rhs := .var 0, ens := none, post := .bot }
abbrev cP : Semantics := cF [clP]

theorem clP_not_reqFails (c : Semantics) (σ : Subst) : ¬ ReqFails c σ clP := by
  intro h
  cases h with
  | intro ht _ _ => cases ht
  | pre h => cases h

theorem p_none {r : Option GroundTerm} : ¬ Eval cP fl [] r := by
  intro h
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; cases hpost
  | @rest _ fn _ hfn hnone =>
    rw [lookup_fl] at hfn; cases hfn
    cases hnone clP (by simp [fnOf]) with
    | intro h => exact absurd (h [] (fun i hi => by cases hi) .nil) (clP_not_reqFails _ _)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex ht he hw =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; cases ht
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; exact absurd rfl hne
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [lookup_fl] at hfn; cases hfn; simp [fnOf] at hmem; subst hmem; exact absurd rfl hne

theorem clP_noRes (c : Semantics) (σ : Subst) (r : Option GroundTerm) : ¬ Clause.Res c clP σ r := by
  rintro (⟨-, (⟨-, hp, -⟩ | ⟨t, w, ht, -⟩)⟩ | ⟨hne, -⟩)
  · cases hp
  · cases ht
  · exact absurd rfl hne

/-- **`clP` is coherent with itself**: no instance of it has a result. -/
theorem p_coherent : Coherent cP clP clP :=
  fun _ _ _ _ _ _ _ _ _ _ => .inr fun r _ h1 _ => absurd h1 (clP_noRes _ _ r)

/-! ## C: `f() => g(?Z:Int)` with `post := Z ∈ lp()`, beside `lp() => lp()`

`lp()` has no result (each derivation of it holds a shorter one), so `post` has no truth value at
any instance of `f`'s clause, no instance is decided, and `f()` has no result at all: neither
`clauseEx` nor `exNone` applies (each asks every instance decided), `clause` and `ensFails` ask no
existential variable, and the rest asks the clause to fail, which it does not (it applies under
the empty match). -/

def fC : Sym := nRegSyms + 4
def lpS : Sym := nRegSyms + 5
def gS : Sym := nRegSyms + 6
def clCf : Clause :=
  { vars := [Srt.int], pats := [], req := none, rhs := .app gS [.var 0], ens := none, exs := [0],
    post := .mem Srt.int (.var 0) (.app lpS []) }
def clLp : Clause := { vars := [], pats := [], req := none, rhs := .app lpS [], ens := none }
def fnCf : Fn := { label := fC, args := [], result := Srt.int, clauses := [clCf] }
def fnLp : Fn := { label := lpS, args := [], result := Srt.int, clauses := [clLp] }
def cCe : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnCf, fnLp] }

theorem lookup_lp : cCe.lookupFn lpS = some fnLp := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_fC : cCe.lookupFn fC = some fnCf := by rw [Semantics.lookupFn_eq]; rfl

theorem lp_flags : cCe.isCtor lpS = false ∧ isHook lpS = false ∧ cCe.isParam lpS = false ∧
    cCe.isOvl lpS = false := by decide +kernel

/-- **`lp()` has no result.** -/
theorem lp_none {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm cCe σ (.app lpS []) r := by
  obtain ⟨hk, hh, hp, ho⟩ := lp_flags
  intro hv
  exact EvalTerm.rec (c := cCe)
    (motive_1 := fun f vs _ _ => f = lpS → vs = [] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ t _ _ => t = .app lpS [] → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True) (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact ihrhs rfl)
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      cases hnone clLp (by simp [fnLp]) with
      | intro h =>
        cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clLp, varOccsList, varOccsCond] at hi) .nil with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd (Holds.top_eq hp) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases ht)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun {_ _ _ _ _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun h => by cases h) (fun h => by cases h) (fun _ _ h => by cases h)
    (fun hk' _ _ h => by cases h; rw [hk] at hk'; cases hk')
    (fun _ hhk _ _ _ _ h => by cases h; rw [hh] at hhk; cases hhk)
    (fun _ _ hp' _ _ _ h => by cases h; rw [hp] at hp'; cases hp')
    (fun _ _ hts hvs _ _ _ ihf h => by
      cases h
      cases hts
      simp only [allSome, Option.some.injEq] at hvs
      exact ihf rfl hvs.symm)
    (fun _ _ hts hvs _ _ h => by
      cases h
      cases hts
      simp [allSome] at hvs)
    (fun _ ho' _ _ _ h => by cases h; rw [ho] at ho'; cases ho')
    (fun _ ho' _ _ _ _ _ _ _ h => by cases h; rw [ho] at ho'; cases ho')
    trivial (fun _ _ _ _ => trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    hv rfl

/-- At no σ has `clCf`'s `post` a truth value. -/
theorem clCf_post_undecided (σ : Subst) (b : Bool) : ¬ Holds cCe 1 σ clCf.post b := by
  intro h
  cases h with
  | mem _ h' => exact lp_none h'

theorem clCf_not_inst (σ : Subst) (r : Option GroundTerm) : ¬ InstIs cCe σ clCf r := by
  intro h
  cases h with
  | fails hp _ => exact clCf_post_undecided _ _ hp
  | gives _ _ hp => exact clCf_post_undecided _ _ hp

theorem σ0_sorted : cCe.WellSorted [Srt.int] [(0, int 0)] := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, sortOf_int 0⟩

theorem clCf_free : Clause.exsFree clCf = [0] := by decide

/-- **`f()` has no result at all.** -/
theorem fC_none {r : Option GroundTerm} : ¬ Eval cCe fC [] r := by
  intro h
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem; cases hex
  | @rest _ fn _ hfn hnone =>
    rw [lookup_fC] at hfn; cases hfn
    cases hnone clCf (by simp [fnCf]) with
    | intro h =>
      cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clCf, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem; cases hex
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem
    exact clCf_post_undecided _ _ hpost
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem
    obtain ⟨σ', ha, hw⟩ := hsome
    exact clCf_not_inst _ _ (hall σ' ha hw)

/-! ## s: `fl() => 3 #Or #Exists B:Int. (B #And {B #Equals 3})`, a variable fixed under a binder

`exs = [Z]`, `rhs := Z`, `post := Z ∈ 3 ∨ ∃B:Int. (Z ∈ B ∧ B = 3)`. -/

abbrev v3 : GroundTerm := .dv Srt.int (.int 3)
def bodyS : Cond := .and (.mem Srt.int (.var 0) (.var 1)) (.equals Srt.int (.var 1) (.dv Srt.int (.int 3)))
def clS : Clause :=
  { vars := [Srt.int], pats := [], req := none, rhs := .var 0, ens := none, exs := [0],
    post := .or (.mem Srt.int (.var 0) (.dv Srt.int (.int 3))) (.ex Srt.int bodyS) }
abbrev cS : Semantics := cF [clS]

def gS' (σ : Subst) : Bool :=
  ((σ.lookup 0).isSome && sameResult (σ.lookup 0) (σ.lookup 1)) &&
    sameResult (σ.lookup 1) (some (GroundTerm.dv Srt.int (.int 3)))

theorem bodyS_holds (c : Semantics) (σ : Subst) : Holds c (1 + 1) σ bodyS (gS' σ) :=
  .and (.mem (.var (i := 0)) (.var (i := 1))) (.equals (.var (i := 1)) .dv)

theorem clS_post_true (c : Semantics) (σ' : Subst) (hz : σ'.lookup 0 = some v3) :
    Holds c 1 σ' clS.post true := by
  have hm : Holds c 1 σ' (.mem Srt.int (.var 0) (.dv Srt.int (.int 3))) true :=
    holds_cast (Holds.mem (s := Srt.int) (.var (i := 0)) .dv) (by rw [hz]; exact sameResult_self _)
  have hex : Holds c 1 σ' (.ex Srt.int bodyS) true := by
    refine .ex gS' (fun σ'' _ => bodyS_holds c σ'') ⟨fun _ => ?_, fun _ => rfl⟩
    have h0 : (((1, v3) :: σ' : Subst)).lookup 0 = some v3 := (lookup_cons_ne _ _ (by omega)).trans hz
    have h1 : (((1, v3) :: σ' : Subst)).lookup 1 = some v3 := lookup_cons_self _ _ _
    refine ⟨(1, v3) :: σ', ⟨fun i hi => lookup_cons_ne _ _ (by omega), fun j s hj => ?_⟩, ?_⟩
    · match j, hj with
      | 0, hj => cases hj; exact ⟨v3, h1, sortOf_int 3⟩
    · show ((((1, v3) :: σ' : Subst).lookup 0).isSome && sameResult (((1, v3) :: σ' : Subst).lookup 0)
        (((1, v3) :: σ' : Subst).lookup 1) && sameResult (((1, v3) :: σ' : Subst).lookup 1) (some v3)) = true
      rw [h0, h1, sameResult_self]; rfl
  exact Holds.or hm hex

theorem clS_post_false (c : Semantics) (σ' : Subst) (z : GroundTerm) (hz : σ'.lookup 0 = some z)
    (hne : z ≠ v3) : Holds c 1 σ' clS.post false := by
  have hm : Holds c 1 σ' (.mem Srt.int (.var 0) (.dv Srt.int (.int 3))) false :=
    holds_cast (Holds.mem (s := Srt.int) (.var (i := 0)) .dv) (by rw [hz, sameResult_ne hne]; rfl)
  have hex : Holds c 1 σ' (.ex Srt.int bodyS) false := by
    refine .ex gS' (fun σ'' _ => bodyS_holds c σ'') ⟨fun h => (by cases h), ?_⟩
    rintro ⟨σ'', ⟨hag, _⟩, hg⟩
    exfalso
    have h0 : σ''.lookup 0 = some z := (hag 0 (by omega)).trans hz
    simp only [gS', h0, Bool.and_eq_true] at hg
    cases h1 : σ''.lookup 1 with
    | none => rw [h1] at hg; simp [sameResult] at hg
    | some w =>
      rw [h1] at hg
      exact hne ((sameResult_some.mp hg.1.2).trans (sameResult_some.mp hg.2))
  exact Holds.or hm hex

/-- Every instance of `clS` at an Int value is decided and gives 3 or nothing. -/
theorem s_hall (c : Semantics) (σ' : Subst) (hσ' : c.WellSorted clS.vars σ') : InstIs c σ' clS (some v3) := by
  obtain ⟨z, hz, -⟩ := hσ' 0 Srt.int rfl
  by_cases h3 : z = v3
  · subst h3
    exact .gives (hz ▸ .var (i := 0)) (fun t ht => by cases ht) (clS_post_true c σ' hz)
  · exact .fails (clS_post_false c σ' z hz h3) (.post (clS_post_false c σ' z hz h3))

theorem σ3_sorted (c : Semantics) : c.WellSorted [Srt.int] [(0, v3)] := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, lookup_cons_self _ _ _, sortOf_int 3⟩

/-- **`fl()` is 3**, by `clauseEx`: every Int instance is decided (`Holds.ex` over every Int value of B). -/
theorem s_some : Eval cS fl [] (some v3) := by
  refine .clauseEx (cl := clS) (σ := [(0, v3)]) (lookup_fl _) (by simp [fnOf]) (σ3_sorted _) .nil
    (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) (by decide) ?_ ?_ ?_ ?_
  · simp [fnOf] at hm; subst hm; exact absurd hlt (by decide)
  · exact .var (i := 0)
  · intro t ht; cases ht
  · exact clS_post_true _ _ rfl
  · exact fun σ' _ hσ' => s_hall _ σ' hσ'

theorem clS_free : Clause.exsFree clS = [0] := by decide

/-- The fact `MatchIndependent`'s body asks: a result of the clause at its match. -/
theorem s_res : Clause.Res cS clS [] (some v3) :=
  Or.inr (And.intro (by decide) (Or.inl ⟨[(0, v3)], v3,
    clS_free ▸ (fun i hi => lookup_cons_ne _ _ (fun h => hi (by simp [h]))), σ3_sorted _,
    ⟨.var (i := 0), (fun t ht => by cases ht), clS_post_true _ _ rfl⟩,
    fun σ'' _ h => s_hall _ σ'' h, rfl⟩))

/-! ## c: `exs = [B:Bool, Z:KItem]`, `rhs := Z`, `ens := B`, `post := Z ∈ inj(B)`: Z fixed by a
term over the confined B, which nothing but the `ensures` pins -/

def base2 : Semantics := { base with lib := { sortsBelowKItem := [Srt.int, Srt.bool] } }
def cF2 (cls : List Clause) : Semantics :=
  { base2 with symNames := base2.symNames ++ ["Lblfl"], fns := [fnOf cls] }
theorem lookup_fl2 (cls : List Clause) : (cF2 cls).lookupFn fl = some (fnOf cls) := by
  rw [Semantics.lookupFn_eq]; rfl

abbrev vT : GroundTerm := .dv Srt.bool (.bool true)
abbrev wT : GroundTerm := .inj Srt.bool Srt.kitem (.dv Srt.bool (.bool true))
def clC : Clause :=
  { vars := [Srt.bool, Srt.kitem], pats := [], req := none, rhs := .var 1, ens := some (.var 0), exs := [0, 1],
    post := .mem Srt.kitem (.var 1) (.inj Srt.bool Srt.kitem (.var 0)) }
abbrev cC : Semantics := cF2 [clC]

theorem wT_sorted : cC.sortOf wT = some Srt.kitem := by decide +kernel

theorem clC_post (c : Semantics) (σ' : Subst) : Holds c 2 σ' clC.post
    ((σ'.lookup 1).isSome && sameResult (σ'.lookup 1) ((σ'.lookup 0).map (injNormal Srt.bool Srt.kitem))) :=
  .mem (.var (i := 1)) (.inj (.var (i := 0)))

/-- Every instance of `clC` at values is decided and gives `inj(true)` or nothing. -/
theorem c_hall (c : Semantics) (σ' : Subst) (hσ' : c.WellSorted clC.vars σ') : InstIs c σ' clC (some wT) := by
  obtain ⟨v, hv, -⟩ := hσ' 0 Srt.bool rfl
  obtain ⟨z, hz, -⟩ := hσ' 1 Srt.kitem rfl
  by_cases hvt : v = vT
  · subst hvt
    by_cases hzw : z = wT
    · subst hzw
      exact .gives (hz ▸ .var (i := 1)) (fun t ht => by cases ht; exact hv ▸ .var (i := 0))
        (holds_cast (clC_post c σ') (by rw [hz, hv]; exact sameResult_self _))
    · have hf : Holds c 2 σ' clC.post false :=
        holds_cast (clC_post c σ') (by
          rw [hz, hv]
          show ((some z).isSome && sameResult (some z) (some wT)) = false
          rw [sameResult_ne hzw]; rfl)
      exact .fails hf (.post hf)
  · exact .fails (clC_post c σ') (.ens (t := .var 0) rfl (.var (i := 0))
      (by rw [hv]; intro h; exact hvt (Option.some.inj h)))

theorem σC_sorted : cC.WellSorted [Srt.bool, Srt.kitem] [(0, vT), (1, wT)] := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, sortOf_bool true⟩
  | 1, h => cases h; exact ⟨_, rfl, wT_sorted⟩

/-- **`fl()` is `inj(true)`**, by `clauseEx`. -/
theorem c_some : Eval cC fl [] (some wT) := by
  refine .clauseEx (cl := clC) (σ := [(0, vT), (1, wT)]) (lookup_fl2 _) (by simp [fnOf]) σC_sorted .nil
    (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) (by decide) ?_ ?_ ?_ ?_
  · simp [fnOf] at hm; subst hm; exact absurd hlt (by decide)
  · exact .var (i := 1)
  · intro t ht; cases ht; exact .var (i := 0)
  · exact holds_cast (clC_post _ _) (sameResult_self _)
  · exact fun σ' _ hσ' => c_hall _ σ' hσ'

theorem clC_free : Clause.exsFree clC = [0, 1] := by decide

theorem c_res : Clause.Res cC clC [] (some wT) :=
  Or.inr (And.intro (by decide) (Or.inl ⟨[(0, vT), (1, wT)], wT,
    clC_free ▸ (fun i hi => by
      have h0 : i ≠ 0 := fun h => hi (by simp [h])
      have h1 : i ≠ 1 := fun h => hi (by simp [h])
      exact (lookup_cons_ne _ _ h0).trans (lookup_cons_ne _ _ h1)), σC_sorted,
    ⟨.var (i := 1), (fun t ht => by cases ht; exact .var (i := 0)),
      holds_cast (clC_post _ _) (sameResult_self _)⟩,
    fun σ'' _ h => c_hall _ σ'' h, rfl⟩))

/-! ## vac: a binder over a sort without a value

`post := Z ∈ true ∨ ∃B:S. (Z ∈ k(B) ∧ B = lp())`: where no value has the sort S the binder is
false whatever its body, so `fl()` is `true` whatever `k` and `lp` are. -/

def clV (S : Srt) : Clause :=
  { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := none, exs := [0],
    post := .or (.mem Srt.bool (.var 0) (.dv Srt.bool (.bool true)))
      (.ex S (.and (.mem Srt.bool (.var 0) (.app 900 [.var 1])) (.equals S (.var 1) (.app 901 [])))) }

/-- **At a sort without a value, `Holds` of `.ex` is false for every body.** -/
theorem vac_ex (c : Semantics) (S : Srt) (hno : ∀ v, c.sortOf v ≠ some S) (σ' : Subst) (body : Cond) :
    Holds c 1 σ' (.ex S body) false :=
  .ex (fun _ => false)
    (fun σ'' h => by obtain ⟨v, -, hv⟩ := h.2 0 S rfl; exact absurd hv (hno v))
    ⟨fun h => (by cases h), fun ⟨_, _, h⟩ => (by simp at h)⟩

theorem v_mem (c : Semantics) (σ' : Subst) (z : GroundTerm) (hz : σ'.lookup 0 = some z) :
    (z = vT → Holds c 1 σ' (.mem Srt.bool (.var 0) (.dv Srt.bool (.bool true))) true) ∧
    (z ≠ vT → Holds c 1 σ' (.mem Srt.bool (.var 0) (.dv Srt.bool (.bool true))) false) :=
  ⟨fun h => holds_cast (Holds.mem (s := Srt.bool) (.var (i := 0)) .dv) (by rw [hz, h]; exact sameResult_self _),
   fun h => holds_cast (Holds.mem (s := Srt.bool) (.var (i := 0)) .dv) (by rw [hz, sameResult_ne h]; rfl)⟩

theorem v_post (c : Semantics) (S : Srt) (hno : ∀ v, c.sortOf v ≠ some S) (σ' : Subst) (b : Bool)
    (hm : Holds c 1 σ' (.mem Srt.bool (.var 0) (.dv Srt.bool (.bool true))) b) :
    Holds c 1 σ' (clV S).post b :=
  holds_cast (Holds.or hm (vac_ex c S hno σ' _)) (Bool.or_false b)

theorem v_hall (c : Semantics) (S : Srt) (hno : ∀ v, c.sortOf v ≠ some S) (σ' : Subst)
    (hσ' : c.WellSorted (clV S).vars σ') : InstIs c σ' (clV S) (some vT) := by
  obtain ⟨z, hz, -⟩ := hσ' 0 Srt.bool rfl
  by_cases hzt : z = vT
  · exact .gives (hzt ▸ hz ▸ .var (i := 0)) (fun t ht => by cases ht)
      (v_post c S hno σ' true ((v_mem c σ' z hz).1 hzt))
  · have hf := v_post c S hno σ' false ((v_mem c σ' z hz).2 hzt)
    exact .fails hf (.post hf)

/-- **Where S has no value, `fl()` is `true`, whatever `k` and `lp` are.** -/
theorem vac_some (S : Srt) (hno : ∀ v, (cF [clV S]).sortOf v ≠ some S) :
    Eval (cF [clV S]) fl [] (some vT) := by
  refine .clauseEx (cl := clV S) (σ := [(0, vT)]) (lookup_fl _) (by simp [fnOf]) ?_ .nil
    (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) (by simp [clV]) ?_ ?_ ?_ ?_
  · intro i s h
    match i, h with
    | 0, h => cases h; exact ⟨_, rfl, sortOf_bool true⟩
  · simp [fnOf] at hm; subst hm; exact absurd hlt (Nat.lt_irrefl _)
  · exact .var (i := 0)
  · intro t ht; cases ht
  · exact v_post _ S hno _ true ((v_mem _ _ vT rfl).1 rfl)
  · exact fun σ' _ hσ' => v_hall _ S hno σ' hσ'

/-- What the landed texts say of `clS`: its existential variable is in scope and its `post` sorted
(`clauseExOK`), but Int is not confined and Z is fixed only under the binder, which `fixedExs`
does not read (no binder's sort is admitted), so `clausePlainEx` refuses it. -/
theorem s_ok : base.clauseExOK clS = true ∧ base.clausePlainEx clS = false ∧
    clS.fixedExs base.confined (fun _ => false) = [] ∧ base.confined Srt.int = false := by decide +kernel

/-- What the landed texts say of `clC`: Bool is confined and KItem is not, and Z is fixed by
`Z ∈ inj(B)` over the confined B, so `clausePlainEx` admits it. -/
theorem c_ok : base2.clauseExOK clC = true ∧ base2.clausePlainEx clC = true ∧
    clC.fixedExs base2.confined (fun _ => false) = [1] ∧
    base2.confined Srt.kitem = false ∧ base2.confined Srt.bool = true := by decide +kernel

/-! ## h: `h(K) => #Exists Z:Int. (Z #And {inj{Int,KItem}(Z) #Equals K})`

`vars = [K:KItem, Z:Int]`, `exs = [Z]`, `rhs := Z`, `post := inj{Int,KItem}(Z) = K`. -/

def hS : Sym := nRegSyms + 4
def clH : Clause :=
  { vars := [Srt.kitem, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.kitem (.inj Srt.int Srt.kitem (.var 1)) (.var 0) }
def fnH : Fn := { label := hS, args := [Srt.kitem], result := Srt.int, clauses := [clH] }
def cH : Semantics := { base2 with symNames := base2.symNames ++ ["Lblh"], fns := [fnH] }

theorem lookup_h : cH.lookupFn hS = some fnH := by
  rw [Semantics.lookupFn_eq]; rfl

/-- The clause has CE's conjuncts (`clauseExOK`, `clausePlainEx`), Z (of Int, not confined) being
fixed by `inj(Z) = K`; the pair is a subsort pair, and the values are generated (`genWf`). -/
theorem h_ok : cH.clauseExOK clH = true ∧ cH.clausePlainEx clH = true ∧
    clH.fixedExs cH.confined (fun _ => false) = [1] ∧
    cH.confined Srt.int = false ∧ cH.subsorts.contains (Srt.int, Srt.kitem) = true ∧
    Faithful.genWf cH = true := by decide +kernel

instance : OvlOK cH := .of_nil rfl (by decide +kernel)

abbrev k3 : GroundTerm := .inj Srt.int Srt.kitem v3
abbrev kT : GroundTerm := .inj Srt.bool Srt.kitem vT

theorem k3_sorted : cH.sortOf k3 = some Srt.kitem := by decide +kernel
theorem kT_sorted : cH.sortOf kT = some Srt.kitem := by decide +kernel
theorem v3_sorted : cH.sortOf v3 = some Srt.int := sortOf_int 3

/-- `post` at an extension: decided, true exactly where Z's injection is K's value. -/
theorem clH_post (c : Semantics) (σ' : Subst) : Holds c 2 σ' clH.post
    (sameResult ((σ'.lookup 1).map (injNormal Srt.int Srt.kitem)) (σ'.lookup 0)) :=
  .equals (.inj (.var (i := 1))) (.var (i := 0))

/-- No value of Int injects to `inj{Bool,KItem}(true)`, where Bool is not below Int. -/
theorem int_not_kT {c : Semantics} (hns : (Srt.bool, Srt.int) ∉ c.subsorts) {z : GroundTerm}
    (hz : c.sortOf z = some Srt.int) : injNormal Srt.int Srt.kitem z ≠ kT := by
  intro he
  cases z with
  | inj a' b' w =>
    obtain ⟨hsub, -, -, hb⟩ := sortOf_inj.mp hz
    simp only [injNormal] at he
    injection he with ha _ _
    subst ha; subst hb
    exact hns hsub
  | ctor f ts => simp [injNormal] at he
  | dv s l => simp [injNormal] at he
  | map s es => simp [injNormal] at he
  | set s es => simp [injNormal] at he
  | list s es => simp [injNormal] at he

theorem cH_nsub : (Srt.bool, Srt.int) ∉ cH.subsorts := by decide +kernel

/-- Every instance of `clH` at `K := inj(3)` is decided and gives 3 or nothing. -/
theorem h_hall (σ' : Subst) (hk : σ'.lookup 0 = some k3) (hσ' : cH.WellSorted clH.vars σ') :
    InstIs cH σ' clH (some v3) := by
  obtain ⟨z, hz, hzs⟩ := hσ' 1 Srt.int rfl
  by_cases h3 : z = v3
  · subst h3
    exact .gives (hz ▸ .var (i := 1)) (fun t ht => by cases ht)
      (holds_cast (clH_post cH σ') (by rw [hz, hk]; exact sameResult_self _))
  · have hne : injNormal Srt.int Srt.kitem z ≠ k3 := fun he =>
      h3 (Faithful.injNormal_inj h_ok.2.2.2.2.2 hzs v3_sorted he)
    have hf : Holds cH 2 σ' clH.post false :=
      holds_cast (clH_post cH σ') (by rw [hz, hk]; exact sameResult_ne hne)
    exact .fails hf (.post hf)

theorem σH_sorted : cH.WellSorted [Srt.kitem, Srt.int] [(0, k3), (1, v3)] := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, k3_sorted⟩
  | 1, h => cases h; exact ⟨_, rfl, v3_sorted⟩

theorem clH_free : Clause.exsFree clH = [1] := by decide

theorem agree_k {k : GroundTerm} {σ' : Subst} (h : AgreeOff (Clause.exsFree clH) [(0, k)] σ') :
    σ'.lookup 0 = some k := by
  rw [clH_free] at h
  exact h 0 (by decide)

theorem agree_k' {k z : GroundTerm} {σ' : Subst} (h : AgreeOff (Clause.exsFree clH) [(0, k), (1, z)] σ') :
    σ'.lookup 0 = some k := by
  rw [clH_free] at h
  exact h 0 (by decide)

/-- **`h(inj{Int,KItem}(3))` is 3**, by `clauseEx`. -/
theorem h_some : Eval cH hS [k3] (some v3) := by
  refine .clauseEx (cl := clH) (σ := [(0, k3), (1, v3)]) lookup_h (by simp [fnH]) σH_sorted
    (.cons (.var rfl) .nil) (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) (by decide) ?_ ?_ ?_ ?_
  · simp [fnH] at hm; subst hm; exact absurd hlt (by decide)
  · exact .var (i := 1)
  · intro t ht; cases ht
  · exact holds_cast (clH_post _ _) (sameResult_self _)
  · exact fun σ' ha hσ' => h_hall σ' (agree_k' ha) hσ'

/-- A result of the clause at the match `K := inj(3)`, the fact `MatchIndependent`'s body asks. -/
theorem h_res : Clause.Res cH clH [(0, k3)] (some v3) :=
  Or.inr (And.intro (by decide) (Or.inl ⟨[(0, k3), (1, v3)], v3,
    clH_free ▸ (fun i hi => by
      have h1 : i ≠ 1 := fun h => hi (by simp [h])
      match i, h1 with
      | 0, _ => rfl
      | (n + 2), _ => rfl), σH_sorted,
    ⟨.var (i := 1), (fun t ht => by cases ht), holds_cast (clH_post _ _) (sameResult_self _)⟩,
    fun σ'' ha h => h_hall σ'' (agree_k ha) h, rfl⟩))

/-- **`h(inj{Bool,KItem}(true))` is `none`**, by `exNone`: an instance exists (Z := 3) and every
instance is decided and gives nothing. -/
theorem h_none : Eval cH hS [kT] none := by
  refine .exNone (cl := clH) (σ := [(0, kT)]) lookup_h (by simp [fnH]) (by decide) ?_
    (.cons (.var rfl) .nil) (fun t ht => by cases ht) .top (fun cl' hm _ hlt => ?_) ?_ ?_
  · intro i hi s h
    match i, h with
    | 0, h => cases h; exact ⟨_, rfl, kT_sorted⟩
    | 1, h => cases h; exact absurd hi (by decide)
  · simp [fnH] at hm; subst hm; exact absurd hlt (by decide)
  · refine ⟨[(0, kT), (1, v3)], clH_free ▸ (fun i hi => ?_), ?_⟩
    · have h1 : i ≠ 1 := fun h => hi (by simp [h])
      match i, h1 with
      | 0, _ => rfl
      | (n + 2), _ => rfl
    · intro i s h
      match i, h with
      | 0, h => cases h; exact ⟨_, rfl, kT_sorted⟩
      | 1, h => cases h; exact ⟨_, rfl, v3_sorted⟩
  · intro σ' ha hσ'
    obtain ⟨z, hz, hzs⟩ := hσ' 1 Srt.int rfl
    have hf : Holds cH 2 σ' clH.post false :=
      holds_cast (clH_post cH σ') (by rw [hz, agree_k ha]; exact sameResult_ne (int_not_kT cH_nsub hzs))
    exact .fails hf (.post hf)

end KCore.ExClausesTest

/-! ## Axioms -/

#print axioms KCore.ExClausesTest.f1_some
#print axioms KCore.ExClausesTest.f1_not_none
#print axioms KCore.ExClausesTest.f1_fnDet
#print axioms KCore.ExClausesTest.f1_matchIndependent
#print axioms KCore.ExClausesTest.f1_solves
#print axioms KCore.ExClausesTest.f2_none
#print axioms KCore.ExClausesTest.f3_none
#print axioms KCore.ExClausesTest.fC_none
#print axioms KCore.ExClausesTest.k2_coherent
#print axioms KCore.ExClausesTest.k2_not_matchIndependent
#print axioms KCore.ExClausesTest.k2_not_solves
#print axioms KCore.ExClausesTest.q_matchIndependent
#print axioms KCore.ExClausesTest.q_not_solves
#print axioms KCore.ExClausesTest.p_none
#print axioms KCore.ExClausesTest.p_coherent
#print axioms KCore.ExClausesTest.s_some
#print axioms KCore.ExClausesTest.s_res
#print axioms KCore.ExClausesTest.c_some
#print axioms KCore.ExClausesTest.c_res
#print axioms KCore.ExClausesTest.vac_some
#print axioms KCore.ExClausesTest.h_ok
#print axioms KCore.ExClausesTest.h_some
#print axioms KCore.ExClausesTest.h_res
#print axioms KCore.ExClausesTest.h_none
