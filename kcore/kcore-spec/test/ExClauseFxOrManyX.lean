/-
  The fixture e3-ml-eq-rhs-or-many-x (e3-ml-eq-rhs-or-many with every alternative X:
  `rule k(X) => X #Or X #Or … #Or X`, nine alternatives, k `[function, total]` over Int): the clause
  the reader gives for its text and the results of `k`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxOrManyX.lean`.

  The text is `f2-examples/e3-ml-eq-rhs-or-many-x.kompile.kore`; sentence 235 (`AxiomDecl.index`) is
  k's equation `k(X0) = (((X ∨ X) ∨ X) ∨ … ∨ X) ∧ \top` (with `X0 ∈ X`), 95 k's functional sentence.

  From the sentences: k(x) is {x}, one element, as the functional sentence states.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clause read is `clX` (`read`): `[X:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`, `post` the
    disjunction of nine memberships `#Or0 ∈ X`, nested as the text nests them; k is `total`.
  - `k_value`, `k_alone`: `k(x)` is x, by `Eval.clauseEx` at #Or0 := x (every other instance has
    `post` false), and has no other result; `k_2`, `k_2_alone` at 2.
  - `fnHyp`: `FnHyp` holds: k has a value at every argument of Int, its clause has one result at
    each match where it decides, no rule, no open condition, no open generator.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.OrManyXFx

open GroundTerm

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem sameResult_self (v : GroundTerm) : sameResult (some v) (some v) = true := sameResult_some.mpr rfl

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

/-- The instances of a clause whose one existential variable is the variable 1: σ with it set. -/
theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

/-- A substitution giving the variables 0 and 1 values of the two sorts is well sorted. -/
theorem sorted2 {a b : Srt} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) : d.WellSorted [a, b] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp at hs

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-- The predicate p has the truth value b under σ, and no other. -/
def Dec (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {n : Nat} {p q : Cond} {b b' : Bool} (hp : Dec d n σ p b) (hq : Dec d n σ q b') :
    Dec d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

end ExClauseFixtures.OrManyXFx

namespace ExClauseFixtures.OrManyX

open GroundTerm ExClauseFixtures.OrManyXFx

definition_of defn from "f2-examples/e3-ml-eq-rhs-or-many-x.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fK : Sym := 384

/-- The membership `#Or0 ∈ X` (the variable 1 in the variable 0). -/
def memX : Cond := .mem Srt.int (.var 1) (.var 0)

/-- `((#Or0 ∈ X ∨ #Or0 ∈ X) ∨ #Or0 ∈ X) ∨ … ∨ #Or0 ∈ X`, nine memberships nested as the text
nests the disjunctions. -/
def postX : Cond := [0, 0, 0, 0, 0, 0, 0, 0].foldl (fun p (_ : Nat) => .or p memX) memX

/-- `k(X) => #Or0` with `exs = [#Or0]` and `post := postX`, both variables of Int. -/
def clX : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postX }

def fnK : Fn := { label := fK, args := [Srt.int], result := Srt.int, clauses := [clX], total := true }

/-- **The reading**: the text's one function is `k`, `total`, with the one clause `clX`. -/
theorem read : c.fns = [fnK] := by kernel_rfl

theorem names : c.symName fK = "Lblk" ∧ c.sortName Srt.int = "Int" := by decide +kernel

/-- #Or0 is of the unconfined Int and fixed by X in every alternative: `clausePlainEx` admits the
clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx clX = true := by decide +kernel

theorem lookupK : c.lookupFn fK = some fnK := by rw [Semantics.lookupFn_eq]; rfl
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noRules : c.rules = [] := by decide +kernel

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics} {σ : Subst}

theorem dec_mem {n : Nat} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d n σ memX (sameResult (some w) (some x)) := by
  refine ⟨holds_cast (Holds.mem .var .var) (by rw [h0, h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := EvalTerm.var_inv h'
    rw [h0, h1]; rfl

theorem dec_fold {n : Nat} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    ∀ (ks : List Nat) (p : Cond), Dec d n σ p (sameResult (some w) (some x)) →
      Dec d n σ (ks.foldl (fun p (_ : Nat) => .or p memX) p) (sameResult (some w) (some x))
  | [], _, h => h
  | _ :: ks, _, h => dec_fold h0 h1 ks _ (by
      have := dec_or h (dec_mem (d := d) (n := n) h0 h1)
      rwa [Bool.or_self] at this)

/-- **The clause's `post`** at a match giving X the value x: whether #Or0 is x. -/
theorem dec_post {n : Nat} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d n σ postX (sameResult (some w) (some x)) :=
  dec_fold h0 h1 _ _ (dec_mem h0 h1)

/-- **Every instance is decided and gives x or nothing.** -/
theorem inst_all {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hw : d.WellSorted clX.vars σ) :
    InstIs d σ clX (some x) := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.int rfl
  cases hb : sameResult (some w) (some x) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (dec_post h0 hw1).1 hb)
  | false => exact .fails (dec_post h0 hw1).1 (.post (holds_cast (dec_post h0 hw1).1 hb))

/-- The instance at #Or0 := x does not give nothing. -/
theorem inst_not_none {x : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some x) :
    ¬ InstIs d σ clX none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := (dec_post (d := d) h0 h1).2 _ hp
      rw [sameResult_self] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e

theorem ext_sorted {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int) :
    d.WellSorted clX.vars ((1, x) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) hx

theorem agree_x {σ' : Subst} (h : AgreeOff clX.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

/-- **The clause has the one result x at a match giving X the value x.** -/
theorem res_eq {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Clause.Res d clX σ r) : r = some x := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, ha, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · have h0' := (agree_x ha).trans h0
    have h1 : σ'.lookup 1 = some v := (EvalTerm.var_inv hrhs).symm
    have e := (dec_post h0' h1).2 _ hpost
    rw [sameResult_some.mp e.symm]
  · exact absurd (hall _ (agree_set1 σ _) (ext_sorted h0 hx))
      (inst_not_none ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

theorem res_some {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int) :
    Clause.Res d clX σ (some x) :=
  have h0' : ((1, x) :: σ : Subst).lookup 0 = some x := (lkNe _ _ (by decide)).trans h0
  .inr ⟨by decide, .inl ⟨(1, x) :: σ, x, agree_set1 σ _, ext_sorted h0 hx,
    ⟨(lkSelf 1 x σ) ▸ .var, (fun t ht => nomatch ht),
      holds_cast (dec_post h0' (lkSelf _ _ _)).1 (sameResult_self _)⟩,
    fun σ'' ha hw => inst_all ((agree_x ha).trans h0) hw, rfl⟩⟩

/-- **`k(x)` is x**, by `Eval.clauseEx` at #Or0 := x. -/
theorem value (hfn : d.lookupFn fK = some fnK) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) :
    Eval d fK [x] (some x) :=
  have h0 : ([(1, x), (0, x)] : Subst).lookup 0 = some x := rfl
  .clauseEx (fn := fnK) (cl := clX) (σ := [(1, x), (0, x)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl hx rfl hx) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnK, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (dec_post h0 rfl).1 (sameResult_self _))
    (fun σ' ha hw => inst_all ((agree_x ha).trans h0) hw)

/-- **`k(x)` has no other result.** -/
theorem alone (hfn : d.lookupFn fK = some fnK) {x : GroundTerm} (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Eval d fK [x] r) : r = some x := by
  have hcl : ∀ {cl fn'}, d.lookupFn fK = some fn' → cl ∈ fn'.clauses → cl = clX := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnK] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clX.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clX (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clX.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have h1 := (EvalTerm.var_inv hrhs).symm
    have e := (dec_post (hx0 hmatch) h1).2 _ hpost
    rw [sameResult_some.mp e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx0 hmatch
    exact absurd (hall _ (agree_set1 σ _) (ext_sorted h0 hx))
      (inst_not_none ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-- The value a match of the clause gives X is a value of Int. -/
theorem applies_x {vs : List GroundTerm} (h : clX.AppliesAt d σ vs) :
    ∃ x, σ.lookup 0 = some x ∧ d.sortOf x = some Srt.int :=
  h.1 0 (by decide) Srt.int rfl

/-- **`FnHyp`** of a semantics whose one function is `k` with the clause `clX`, without rules and
open generators. -/
theorem fnHyp_of (hfns : d.fns = [fnK]) (hfn : d.lookupFn fK = some fnK)
    (hrules : d.rules = []) (hraw : ∀ k ∈ d.params, k.raw = false) : FnHyp d := by
  have hmem : ∀ {fn}, fn ∈ d.fns → fn = fnK := fun h => by rw [hfns] at h; simpa using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf _ vs hvs => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecided_of_plain (fun r hr => by rw [hrules] at hr; cases hr) (fun fn hf cl hcl => ?_),
    openLaws_of_plain hraw⟩
  · obtain rfl := hmem hf
    obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
    exact ⟨_, value hfn hw⟩
  · obtain rfl := hmem hf
    obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
    exact ⟨_, value hfn hw⟩
  · obtain rfl := hmem hf; exact agree_one rfl
  · obtain rfl := hmem hf
    obtain rfl : cl = clX := by simpa [fnK] using hcl
    refine ⟨fun vs σ σ' ha ha' _ _ _ _ _ => .inr fun r r' hr hr' => ?_, fun _ _ _ _ σ _ _ hdec => ?_⟩
    · obtain ⟨x, hx0, hx⟩ := applies_x ha
      obtain ⟨x', hx0', hx'⟩ := applies_x ha'
      obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv ha.2.1
      obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv ha'.2.1
      cases hvs
      have e : x = x' := Option.some.inj
        (hx0.symm.trans ((PatVal.var_inv hv).trans ((PatVal.var_inv hv').symm.trans hx0')))
      subst e
      rw [res_eq hx0 hx hr, res_eq hx0' hx' hr']
    · obtain ⟨x, hx0, hx⟩ := applies_x hdec.1
      exact ⟨_, res_some hx0 hx⟩
  · obtain rfl := hmem hf
    obtain rfl : cl = clX := by simpa [fnK] using hcl
    rfl

end Clause

/-! ### The expectations, for every H -/

theorem lookupKH (H : HookParams) : (cH H).lookupFn fK = some fnK := by
  rw [Semantics.lookupFn_withHooks]; exact lookupK

/-- **`k(n) = n`, for every H.** -/
theorem k_value (H : HookParams) (n : Int) : Eval (cH H) fK [int n] (some (int n)) :=
  value (lookupKH H) (rmS_sortOf_int _ n)

/-- **`k(n)` has no other result, for every H.** -/
theorem k_alone (H : HookParams) {n : Int} {r : Option GroundTerm} (h : Eval (cH H) fK [int n] r) :
    r = some (int n) :=
  alone (lookupKH H) (rmS_sortOf_int _ n) h

/-- **`k(2) = 2`, for every H.** -/
theorem k_2 (H : HookParams) : Eval (cH H) fK [int 2] (some (int 2)) := k_value H 2

/-- **`k(2)` has no result but 2, for every H.** -/
theorem k_2_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fK [int 2] r) :
    r = some (int 2) := k_alone H h

/-- **`FnHyp` holds, for every H.** -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of ((show (cH H).fns = c.fns from rfl).trans read) (lookupKH H)
    ((show (cH H).rules = c.rules from rfl).trans noRules)
    (fun k hk => noRaw k ((show (cH H).params = c.params from rfl) ▸ hk))

end ExClauseFixtures.OrManyX

/-- info: 'ExClauseFixtures.OrManyX.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.OrManyX.read
#print axioms ExClauseFixtures.OrManyX.k_value
#print axioms ExClauseFixtures.OrManyX.k_alone
#print axioms ExClauseFixtures.OrManyX.k_2
#print axioms ExClauseFixtures.OrManyX.k_2_alone
#print axioms ExClauseFixtures.OrManyX.fnHyp
