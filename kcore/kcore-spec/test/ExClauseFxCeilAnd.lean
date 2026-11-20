/-
  The fixture e3-ml-eq-rhs-ceil-and (a conjunction of two terms in the operand of a `#Ceil` that is a
  conjunct of an equation's right side): the clauses the reader gives for its text and the results of
  `h`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxCeilAnd.lean`.

  `syntax Int ::= f(Int) [function] | g(Int) [function] | h(Int) [function]`,
  `rule f(X) => X requires X >Int 0` (axiom 200), `rule g(X) => 0 -Int X requires X <Int 5` (axiom 202)
  and `rule h(X) => X #And #Ceil(f(X) #And g(X))` (axiom 204).

  From the sentences: `h(x)` is x where `f(x) ∧ g(x)` has an element, and empty elsewhere. At x with
  0 < x < 5 the first two sentences give `f(x) = x` and `g(x) = 0 - x`, two different integers, so the
  conjunction is empty and `h(x)` is empty: h has no value at 1, 2, 3 and 4. At x ≤ 0 the text has
  no sentence on `f(x)`, and at x ≥ 5 none on `g(x)`: there the value of `h(x)` is not the text's but
  the interpretation's of f and g (`Semantics.fnRest`), so the text has no argument at which h has a
  value under every interpretation.

  The statements are on `defn`, the definition the reader gives for the text
  (`f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore`), each for every hook interpretation H:
  - The clauses read are `clFf`, `clGg` and `clH` (`read`): for h `[X:Int, #Cut0:Int]`, `exs [1]`,
    `rhs X`, `post ⌈#Cut0⌉ ∧ #Cut0 ∈ f(X) ∧ #Cut0 ∈ g(X)`: the conjunction of the two terms is a fresh
    existential variable that is a member of both. No function is `total` or has another clause.
  - `clausePlainEx` admits h's clause (`plainEx`): #Cut0 is of Int, which is not confined, and `post`
    fixes it, by its membership in a term over X.
  - `f_value`, `f_alone`, `g_value`, `g_alone`: at 0 < n, `f(n)` has the one result n; at n < 5,
    `g(n)` has the one result `0 - n`.
  - `h_none`: at 0 < n < 5, `h(n)` has the result none, by `Eval.exNone`: every instance, at
    #Cut0 := z, is decided and gives nothing, its `post` being false (z is not both n and `0 - n`).
    `h_alone`: it has no other result. `h_1`, `h_1_alone`: the two at 1.

  `ExClauseFixtures.CeFx` holds the facts the proofs share with the other fixtures of an equation
  read as one clause with existential variables (test/ExClauseFxBool.lean and the files beside it; a
  test file imports no test file, so each repeats them).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.CeFx

open GroundTerm

/-- What a semantics reads of its symbols and sorts does not depend on the hook interpretation. -/
theorem isCtor_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isCtor f = d.isCtor f := rfl
theorem shapesOK_wh (d : Semantics) (H : HookParams) : (d.withHooks H).shapesOK = d.shapesOK := rfl
theorem fns_wh (d : Semantics) (H : HookParams) : (d.withHooks H).fns = d.fns := rfl
theorem params_wh (d : Semantics) (H : HookParams) : (d.withHooks H).params = d.params := rfl
theorem rules_wh (d : Semantics) (H : HookParams) : (d.withHooks H).rules = d.rules := rfl

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

theorem sameResult_eq_some {r : Option GroundTerm} {v : GroundTerm} (h : sameResult r (some v) = true) :
    r = some v := by
  cases r with
  | none => cases h
  | some w => rw [sameResult_some.mp h]

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

/-- An application of an interpreted hooked symbol has the value `hookRes` gives at its arguments'
results, and none where an argument has none. -/
theorem hook_inv {f : Sym} {ts : List Term} {r : Option GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = true) (h : EvalTerm d σ (.app f ts) r) :
    ∃ rs, EvalTerms d σ ts rs ∧ (∀ vs, allSome rs = some vs → d.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | hook _ _ hts hh hund => cases ht; exact ⟨_, hts, hh, hund⟩
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | param _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hk] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | ovl _ ho _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | _ => cases ht

/-- The results of two terms. -/
theorem terms2_inv {t u : Term} {rs : List (Option GroundTerm)} (h : EvalTerms d σ [t, u] rs) :
    ∃ r r', rs = [r, r'] ∧ EvalTerm d σ t r ∧ EvalTerm d σ u r' := by
  obtain ⟨r, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv h
  obtain ⟨r', rs'', rfl, h2, hs'⟩ := EvalTerms.cons_inv hs
  obtain rfl := EvalTerms.nil_inv hs'
  exact ⟨r, r', rfl, h1, h2⟩


/-- The instances of a clause whose existential variables are the variables 1 and 2: σ with both set. -/
theorem agree_set12 (σ : Subst) (w z : GroundTerm) : AgreeOff [1, 2] σ ((2, z) :: (1, w) :: σ) := fun i hi => by
  have h1 : i ≠ 1 := fun h => hi (by rw [h]; simp)
  have h2 : i ≠ 2 := fun h => hi (by rw [h]; simp)
  rw [lkNe z _ h2, lkNe w σ h1]

/-- A substitution giving the variable 0 a value of the sort is well sorted. -/
theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

/-- A substitution giving the variables 0, 1 and 2 values of the three sorts is well sorted. -/
theorem sorted3 {a b e : Srt} {x w z : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) (h2 : σ.lookup 2 = some z)
    (hz : d.sortOf z = some e) : d.WellSorted [a, b, e] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | 2, hs => cases hs; exact ⟨z, h2, hz⟩
  | i + 3, hs => simp at hs

theorem isParam_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isParam f = d.isParam f := rfl
theorem isOvl_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isOvl f = d.isOvl f := rfl

/-- A call of a function of the definition at the value of a variable has the function's result there. -/
theorem call_var {f : Sym} (hc : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {i : Nat} {w : GroundTerm} (hl : σ.lookup i = some w) {r : Option GroundTerm} (h : Eval d f [w] r) :
    EvalTerm d σ (.app f [.var i]) r :=
  .call (vs := [w]) hc hh (.cons .var .nil) (by rw [hl]; rfl) h hp

/-- A result of such a call is a result of the function at the variable's value. -/
theorem call_var_inv {f : Sym} (hc : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    (ho : d.isOvl f = false) {i : Nat} {w : GroundTerm} (hl : σ.lookup i = some w) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app f [.var i]) r) : Eval d f [w] r := by
  obtain ⟨rs, hts, hcase⟩ := EvalTerm.call_inv hc hh hp ho h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  rw [hl] at hcase
  rcases hcase with ⟨vs, hvs, hf⟩ | ⟨hn, -⟩
  · obtain rfl : [w] = vs := Option.some.inj hvs
    exact hf
  · cases hn

/-- The value a match of a clause whose one pattern is the variable 0 gives it. -/
theorem pat0 {v : GroundTerm} (hm : PatVals d σ [.var 0] [v]) : σ.lookup 0 = some v := by
  obtain ⟨v', vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

end ExClauseFixtures.CeFx

namespace ExClauseFixtures.ExCeilAnd

open GroundTerm ExClauseFixtures.CeFx

definition_of defn from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def gS : Sym := 385
def hS : Sym := 386

/-- `f(X) => X requires X >Int 0`. -/
def clFf : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := some (.app intGt [.var 0, .dv Srt.int (.int 0)]),
    rhs := .var 0, ens := none }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clFf] }

/-- `g(X) => 0 -Int X requires X <Int 5`. -/
def clGg : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := some (.app intLt [.var 0, .dv Srt.int (.int 5)]),
    rhs := .app intSub [.dv Srt.int (.int 0), .var 0], ens := none }

def fnG : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clGg] }

/-- `h(X) => X` with `exs = [#Cut0]` and `post := ⌈#Cut0⌉ ∧ #Cut0 ∈ f(X) ∧ #Cut0 ∈ g(X)`, X and #Cut0
of Int. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none, exs := [1],
    post := .and (.ceil Srt.int (.var 1))
      (.and (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app gS [.var 0]))) }

def fnH : Fn := { label := hS, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, each with its one clause. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.symName hS = "Lblh" ∧
    c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" ∧ c.symName intLt = "Lbl'Unds-LT-'Int'Unds'" ∧
    c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ c.sortName Srt.int = "Int" := by decide +kernel

/-- **h's clause is not refused**: #Cut0 is of Int, which is not confined, and is fixed by `post`. -/
theorem plainEx : c.clausePlainEx clH = true ∧ c.confined Srt.int = false ∧
    clH.fixedExs c.confined c.hasValue = [1] := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn hS = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem ctors : c.isCtor intGt = false ∧ c.isCtor intLt = false ∧ c.isCtor intSub = false ∧
    c.isCtor fF = false ∧ c.isCtor gS = false := by decide +kernel
theorem fnsPlain : c.isParam fF = false ∧ c.isOvl fF = false ∧ c.isParam gS = false ∧ c.isOvl gS = false := by
  decide +kernel

/-- What a semantics must give for the three clauses to be read in it: `>Int`, `<Int` and `-Int`
the hooks, and `f`, `g` and `h` the functions with the clauses `clFf`, `clGg` and `clH`. -/
structure Reads (d : Semantics) : Prop where
  gt : d.isCtor intGt = false
  lt : d.isCtor intLt = false
  sub : d.isCtor intSub = false
  fC : d.isCtor fF = false
  fP : d.isParam fF = false
  fO : d.isOvl fF = false
  gC : d.isCtor gS = false
  gP : d.isParam gS = false
  gO : d.isOvl gS = false
  lookF : d.lookupFn fF = some fnF
  lookG : d.lookupFn gS = some fnG
  lookH : d.lookupFn hS = some fnH

section Clauses

variable {d : Semantics} {σ : Subst}

theorem hooks : isHook intGt = true ∧ isHook intLt = true ∧ isHook intSub = true ∧ isHook fF = false ∧
    isHook gS = false := by decide +kernel

/-- `>Int`, `<Int` and `-Int` at two values of Int, under every interpretation (domains.md,
`hook(INT.gt)`, `hook(INT.lt)`, `hook(INT.sub)`: the comparisons and the difference of the two
integers). -/
theorem hookGt (n : Int) : d.hookRes intGt [int n, int 0] = some (some (bool (decide (n > 0)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl)

theorem hookLt (n : Int) : d.hookRes intLt [int n, int 5] = some (some (bool (decide (n < 5)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intLt]; rfl)

theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value (by rw [hook_intSub]; rfl)

theorem evalGt (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool (decide (n > 0)))) :=
  .hook hd.gt hooks.1 (rs := [σ.lookup 0, some (int 0)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookGt n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalGt_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) r) : r = some (bool (decide (n > 0))) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.gt hooks.1 h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [int n, int 0] (by rw [h0]; rfl)
  rw [hookGt] at this
  exact (Option.some.inj this).symm

theorem evalLt (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intLt [.var 0, .dv Srt.int (.int 5)]) (some (bool (decide (n < 5)))) :=
  .hook hd.lt hooks.2.1 (rs := [σ.lookup 0, some (int 5)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookLt n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalLt_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intLt [.var 0, .dv Srt.int (.int 5)]) r) : r = some (bool (decide (n < 5))) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.lt hooks.2.1 h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [int n, int 5] (by rw [h0]; rfl)
  rw [hookLt] at this
  exact (Option.some.inj this).symm

theorem evalSub (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intSub [.dv Srt.int (.int 0), .var 0]) (some (int (0 - n))) :=
  .hook hd.sub hooks.2.2.1 (rs := [some (int 0), σ.lookup 0]) (.cons .dv (.cons .var .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookSub n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalSub_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intSub [.dv Srt.int (.int 0), .var 0]) r) : r = some (int (0 - n)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.sub hooks.2.2.1 h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.dv_inv h1
  obtain rfl := EvalTerm.var_inv h2
  have := hh [int 0, int n] (by rw [h0]; rfl)
  rw [hookSub] at this
  exact (Option.some.inj this).symm

/-! ### f and g -/

/-- **`f(n)` is n where 0 < n**, by its one clause. -/
theorem valueF (hd : Reads d) {n : Int} (hn : 0 < n) : Eval d fF [int n] (some (int n)) :=
  .clause (fn := fnF) (cl := clFf) (σ := [(0, int n)]) hd.lookF (List.mem_singleton_self _)
    (sorted1 rfl (sortOf_int n)) (.cons (.var rfl) .nil)
    (fun t ht => by
      cases ht
      have h := evalGt hd (σ := [(0, int n)]) (n := n) rfl
      rw [decide_eq_true (show n > 0 from hn)] at h
      exact h)
    .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top

/-- **`f(n)` has no other result where 0 < n.** -/
theorem aloneF (hd : Reads d) {n : Int} (hn : 0 < n) {r : Option GroundTerm} (h : Eval d fF [int n] r) :
    r = some (int n) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clFf := fun h1 h2 => by
    rw [hd.lookF] at h1; cases h1; simpa [fnF] using h2
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    exact (EvalTerm.var_inv hrhs).trans (pat0 hmatch)
  | rest hfn' hnone =>
    rw [hd.lookF] at hfn'; cases hfn'
    cases hnone clFf (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clFf.vars [(0, int n)] := sorted1 rfl (sortOf_int n)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht he hr =>
        cases ht
        exact absurd (by rw [evalGt_inv hd rfl he, decide_eq_true (show n > 0 from hn)]) hr
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

/-- **`g(n)` is `0 - n` where n < 5**, by its one clause. -/
theorem valueG (hd : Reads d) {n : Int} (hn : n < 5) : Eval d gS [int n] (some (int (0 - n))) :=
  .clause (fn := fnG) (cl := clGg) (σ := [(0, int n)]) hd.lookG (List.mem_singleton_self _)
    (sorted1 rfl (sortOf_int n)) (.cons (.var rfl) .nil)
    (fun t ht => by
      cases ht
      have h := evalLt hd (σ := [(0, int n)]) (n := n) rfl
      rw [decide_eq_true hn] at h
      exact h)
    .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evalSub hd rfl) (fun t ht => nomatch ht) .top

/-- **`g(n)` has no other result where n < 5.** -/
theorem aloneG (hd : Reads d) {n : Int} (hn : n < 5) {r : Option GroundTerm} (h : Eval d gS [int n] r) :
    r = some (int (0 - n)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn gS = some fn' → cl ∈ fn'.clauses → cl = clGg := fun h1 h2 => by
    rw [hd.lookG] at h1; cases h1; simpa [fnG] using h2
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    exact evalSub_inv hd (pat0 hmatch) hrhs
  | rest hfn' hnone =>
    rw [hd.lookG] at hfn'; cases hfn'
    cases hnone clGg (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clGg.vars [(0, int n)] := sorted1 rfl (sortOf_int n)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht he hr =>
        cases ht
        exact absurd (by rw [evalLt_inv hd rfl he, decide_eq_true hn]) hr
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

/-! ### h -/

/-- The truth value of h's `post` where X has the value n, 0 < n < 5: #Cut0 has a value, which is
`f(n) = n` and `g(n) = 0 - n`. -/
def postVal (σ : Subst) (n : Int) : Bool :=
  (σ.lookup 1).isSome && (((σ.lookup 1).isSome && sameResult (σ.lookup 1) (some (int n))) &&
    ((σ.lookup 1).isSome && sameResult (σ.lookup 1) (some (int (0 - n)))))

theorem post_holds (hd : Reads d) {n : Int} (h0n : 0 < n) (hn5 : n < 5) (h0 : σ.lookup 0 = some (int n)) :
    Holds d 2 σ clH.post (postVal σ n) :=
  .and (.ceil .var)
    (.and (.mem .var (call_var hd.fC hooks.2.2.2.1 hd.fP h0 (valueF hd h0n)))
      (.mem .var (call_var hd.gC hooks.2.2.2.2 hd.gP h0 (valueG hd hn5))))

theorem post_inv (hd : Reads d) {n : Int} (h0n : 0 < n) (hn5 : n < 5) (h0 : σ.lookup 0 = some (int n))
    {t : Bool} (h : Holds d 2 σ clH.post t) : t = postVal σ n := by
  cases h with
  | and hc hm =>
    cases hc with
    | ceil hz =>
      cases hm with
      | and hf hg =>
        cases hf with
        | mem hf1 hf2 =>
          cases hg with
          | mem hg1 hg2 =>
            obtain rfl := EvalTerm.var_inv hz
            obtain rfl := EvalTerm.var_inv hf1
            obtain rfl := EvalTerm.var_inv hg1
            obtain rfl := aloneF hd h0n (call_var_inv hd.fC hooks.2.2.2.1 hd.fP hd.fO h0 hf2)
            obtain rfl := aloneG hd hn5 (call_var_inv hd.gC hooks.2.2.2.2 hd.gP hd.gO h0 hg2)
            rfl

/-- **`post` is false at every value of #Cut0**: no value is both n and `0 - n` where 0 < n. -/
theorem post_false (σ : Subst) {n : Int} (h0n : 0 < n) : postVal σ n = false :=
  Bool.eq_false_iff.mpr fun h => by
    simp only [postVal, Bool.and_eq_true] at h
    have e1 := sameResult_eq_some h.2.1.2
    have e2 := sameResult_eq_some h.2.2.2
    rw [e1] at e2
    have e : n = 0 - n := by simpa [KCore.int] using Option.some.inj e2
    omega

/-- **Every instance of h's clause is decided and gives nothing**, at X := n with 0 < n < 5. -/
theorem inst_none (hd : Reads d) {n : Int} (h0n : 0 < n) (hn5 : n < 5) (h0 : σ.lookup 0 = some (int n)) :
    InstIs d σ clH none :=
  .fails (post_holds hd h0n hn5 h0)
    (.post (holds_cast (post_holds hd h0n hn5 h0) (post_false σ h0n)))

theorem agree_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

/-- **`h(n)` has no value where 0 < n < 5**, by `Eval.exNone`: every instance gives nothing. -/
theorem noneH (hd : Reads d) {n : Int} (h0n : 0 < n) (hn5 : n < 5) : Eval d hS [int n] none :=
  have hs : d.WellSorted clH.vars [(1, int 0), (0, int n)] := sorted2 rfl (sortOf_int n) rfl (sortOf_int 0)
  .exNone (fn := fnH) (cl := clH) (σ := [(1, int 0), (0, int n)]) hd.lookH (List.mem_singleton_self _)
    (by decide) (hs.at _) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    ⟨_, fun _ _ => rfl, hs⟩
    (fun σ' ha _ => inst_none hd h0n hn5 ((agree_x ha).trans rfl))

/-- **`h(n)` has no other result where 0 < n < 5.** -/
theorem aloneH (hd : Reads d) {n : Int} (h0n : 0 < n) (hn5 : n < 5) {r : Option GroundTerm}
    (h : Eval d hS [int n] r) : r = none := by
  have hcl : ∀ {cl fn'}, d.lookupFn hS = some fn' → cl ∈ fn'.clauses → cl = clH := fun h1 h2 => by
    rw [hd.lookH] at h1; cases h1; simpa [fnH] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hd.lookH] at hfn'; cases hfn'
    cases hnone clH (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clH.vars [(1, int 0), (0, int n)] :=
        sorted2 rfl (sortOf_int n) rfl (sortOf_int 0)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails => rfl
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have e := post_inv hd h0n hn5 (pat0 hmatch) hpost
    rw [post_false _ h0n] at e
    cases e
  | exNone => rfl

end Clauses

/-! ### The expectations, for every H -/

theorem reads (H : HookParams) : Reads (cH H) where
  gt := (isCtor_wh c H _).trans ctors.1
  lt := (isCtor_wh c H _).trans ctors.2.1
  sub := (isCtor_wh c H _).trans ctors.2.2.1
  fC := (isCtor_wh c H _).trans ctors.2.2.2.1
  fP := (isParam_wh c H _).trans fnsPlain.1
  fO := (isOvl_wh c H _).trans fnsPlain.2.1
  gC := (isCtor_wh c H _).trans ctors.2.2.2.2
  gP := (isParam_wh c H _).trans fnsPlain.2.2.1
  gO := (isOvl_wh c H _).trans fnsPlain.2.2.2
  lookF := by rw [Semantics.lookupFn_withHooks]; exact lookupF
  lookG := by rw [Semantics.lookupFn_withHooks]; exact lookupG
  lookH := by rw [Semantics.lookupFn_withHooks]; exact lookupH

/-- **`f(n) = n` where 0 < n, for every H.** -/
theorem f_value (H : HookParams) {n : Int} (hn : 0 < n) : Eval (cH H) fF [int n] (some (int n)) :=
  valueF (reads H) hn

/-- **`f(n)` has no other result where 0 < n, for every H.** -/
theorem f_alone (H : HookParams) {n : Int} (hn : 0 < n) {r : Option GroundTerm}
    (h : Eval (cH H) fF [int n] r) : r = some (int n) := aloneF (reads H) hn h

/-- **`g(n) = 0 - n` where n < 5, for every H.** -/
theorem g_value (H : HookParams) {n : Int} (hn : n < 5) : Eval (cH H) gS [int n] (some (int (0 - n))) :=
  valueG (reads H) hn

/-- **`g(n)` has no other result where n < 5, for every H.** -/
theorem g_alone (H : HookParams) {n : Int} (hn : n < 5) {r : Option GroundTerm}
    (h : Eval (cH H) gS [int n] r) : r = some (int (0 - n)) := aloneG (reads H) hn h

/-- **`h(n)` has no value where 0 < n < 5, for every H.** -/
theorem h_none (H : HookParams) {n : Int} (h0n : 0 < n) (hn5 : n < 5) : Eval (cH H) hS [int n] none :=
  noneH (reads H) h0n hn5

/-- **`h(n)` has no other result where 0 < n < 5, for every H.** -/
theorem h_alone (H : HookParams) {n : Int} (h0n : 0 < n) (hn5 : n < 5) {r : Option GroundTerm}
    (h : Eval (cH H) hS [int n] r) : r = none := aloneH (reads H) h0n hn5 h

/-- **`h(1)` has no value, for every H**: `f(1) = 1` and `g(1) = -1`. -/
theorem h_1 (H : HookParams) : Eval (cH H) hS [int 1] none := h_none H (by decide) (by decide)

/-- **`h(1)` has no result but none, for every H.** -/
theorem h_1_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) hS [int 1] r) : r = none :=
  h_alone H (by decide) (by decide) h

end ExClauseFixtures.ExCeilAnd

/-- info: 'ExClauseFixtures.ExCeilAnd.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.read
/-- info: 'ExClauseFixtures.ExCeilAnd.f_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.f_value
/-- info: 'ExClauseFixtures.ExCeilAnd.f_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.f_alone
/-- info: 'ExClauseFixtures.ExCeilAnd.g_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.g_value
/-- info: 'ExClauseFixtures.ExCeilAnd.g_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.g_alone
/-- info: 'ExClauseFixtures.ExCeilAnd.h_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.h_none
/-- info: 'ExClauseFixtures.ExCeilAnd.h_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.h_alone
/-- info: 'ExClauseFixtures.ExCeilAnd.h_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.h_1
/-- info: 'ExClauseFixtures.ExCeilAnd.h_1_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCeilAnd.h_1_alone
