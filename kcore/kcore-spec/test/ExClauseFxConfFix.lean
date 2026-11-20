/-
  The fixture e3-eq-exists-ml-confined-fix (an equation's right side whose binder of an unconfined
  sort is fixed by terms over a binder of a confined sort): the clauses the reader gives for its text
  and the results of `f`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxConfFix.lean`.

  `syntax Int ::= f(Bool) [function] | g(Bool) [function, total] | h(Bool) [function, total]`,
  `rule f(X) => #Exists B:Bool. #Exists Z:Int. (Z #And g(B) #And h(B) #And {B #Equals X})` (axiom
  202), `rule g(B) => 1 requires B` (axiom 204), `rule g(B) => 1 requires notBool B` (axiom 205) and
  `rule h(_) => 1` (axiom 207).

  From the sentences: `f(x)` is the set of the integers z that are, for an element b of Bool with
  b = x, elements of both `g(b)` and `h(b)`. `g(b) = 1` at both values of Bool (the first equation at
  `true`, the second at `false`) and `h(b) = 1`, so `f(x) = 1` at both: f has a value at every
  argument, and the text has no argument at which f is without one.

  The statements are on `defn`, the definition the reader gives for the text
  (`f2-examples/e3-eq-exists-ml-confined-fix.kompile.kore`), each for every hook interpretation H:
  - The clauses read are `clF`, `clG0`, `clG1` and `clH` (`read`): for f `[X:Bool, B:Bool, Z:Int]`,
    `exs [1, 2]`, `rhs Z`, `post B = X ∧ Z ∈ g(B) ∧ Z ∈ h(B)`. f is not `total` and has no other
    clause.
  - `clausePlainEx` admits f's clause (`plainEx`): B is of the confined sort Bool; Z is of Int, which
    is not confined, and `post` fixes it, by its membership in a term over the confined B (`fixedExs`
    is `[1, 2]`).
  - `g_value`, `g_alone`, `h_value`, `h_alone`: `g(b)` and `h(b)` have the one result 1.
  - `f_value`: `f(b)` has the result 1, by `Eval.clauseEx` at B := b and Z := 1. Every other
    instance, at B the other value of Bool or Z another integer, has `post` false: an instance that
    gives nothing, not a result none (`inst_all`).
  - `f_alone`: `f(b)` has no other result, and not none. `f_true`, `f_true_alone`: the two at `true`.

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

namespace ExClauseFixtures.ExConfFix

open GroundTerm ExClauseFixtures.CeFx

definition_of defn from "f2-examples/e3-eq-exists-ml-confined-fix.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def gS : Sym := 385
def hS : Sym := 386

/-- `f(X) => Z` with `exs = [B, Z]` and `post := B = X ∧ Z ∈ g(B) ∧ Z ∈ h(B)`, X and B of Bool, Z of
Int. -/
def clF : Clause :=
  { vars := [Srt.bool, Srt.bool, Srt.int], pats := [.var 0], req := none, rhs := .var 2, ens := none,
    exs := [1, 2],
    post := .and (.equals Srt.bool (.var 1) (.var 0))
      (.and (.mem Srt.int (.var 2) (.app gS [.var 1])) (.mem Srt.int (.var 2) (.app hS [.var 1]))) }

def fnF : Fn := { label := fF, args := [Srt.bool], result := Srt.int, clauses := [clF] }

/-- `g(B) => 1 requires B`. -/
def clG0 : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := some (.var 0), rhs := .dv Srt.int (.int 1), ens := none }

/-- `g(B) => 1 requires notBool B`. -/
def clG1 : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := some (.app boolNot [.var 0]), rhs := .dv Srt.int (.int 1),
    ens := none }

def fnG : Fn :=
  { label := gS, args := [Srt.bool], result := Srt.int, clauses := [clG0, clG1], total := true }

/-- `h(_) => 1`. -/
def clH : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs := .dv Srt.int (.int 1), ens := none }

def fnH : Fn := { label := hS, args := [Srt.bool], result := Srt.int, clauses := [clH], total := true }

/-- **The reading**: the text's functions are `f`, with the one clause `clF`, `g` and `h`. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.symName hS = "Lblh" ∧
    c.symName boolNot = "LblnotBool'Unds'" ∧ c.sortName Srt.bool = "Bool" ∧ c.sortName Srt.int = "Int" := by
  decide +kernel

/-- **f's clause is not refused**: B is of the confined sort Bool; Z is of Int, which is not
confined, and is fixed by `post`, by its membership in a term over B. -/
theorem plainEx : c.clausePlainEx clF = true ∧ c.confined Srt.bool = true ∧ c.confined Srt.int = false ∧
    clF.fixedExs c.confined c.hasValue = [1, 2] := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn hS = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem ctors : c.isCtor boolNot = false ∧ c.isCtor gS = false ∧ c.isCtor hS = false := by decide +kernel
theorem fnsPlain : c.isParam gS = false ∧ c.isOvl gS = false ∧ c.isParam hS = false ∧ c.isOvl hS = false := by
  decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-- What a semantics must give for the clauses to be read in it: `notBool` the hook, the values of
Bool its literals, and `f`, `g` and `h` the functions with these clauses. -/
structure Reads (d : Semantics) : Prop where
  notC : d.isCtor boolNot = false
  gC : d.isCtor gS = false
  gP : d.isParam gS = false
  gO : d.isOvl gS = false
  hC : d.isCtor hS = false
  hP : d.isParam hS = false
  hO : d.isOvl hS = false
  shapes : d.shapesOK = true
  lookF : d.lookupFn fF = some fnF
  lookG : d.lookupFn gS = some fnG
  lookH : d.lookupFn hS = some fnH

section Clauses

variable {d : Semantics} {σ : Subst}

theorem hooks : isHook boolNot = true ∧ isHook gS = false ∧ isHook hS = false := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation (domains.md 1138, 1139). -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

theorem evalNot (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    EvalTerm d σ (.app boolNot [.var 0]) (some (bool (!b))) :=
  .hook hc hooks.1 (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalNot_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : EvalTerm d σ (.app boolNot [.var 0]) r) : r = some (bool (!b)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc hooks.1 h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  have := hh [bool b] (by rw [h0]; rfl)
  rw [hookNot] at this
  exact (Option.some.inj this).symm

/-! ### g and h -/

theorem prioG {cl cl' : Clause} (hcl : cl ∈ fnG.clauses) (hcl' : cl' ∈ fnG.clauses) : ¬ cl'.prio < cl.prio := by
  simp only [fnG, List.mem_cons, List.not_mem_nil, or_false] at hcl hcl'
  rcases hcl with rfl | rfl <;> rcases hcl' with rfl | rfl <;> exact Nat.lt_irrefl _

/-- **`g(b)` is 1**: by its first clause at `true`, by its second at `false`. -/
theorem valueG (hd : Reads d) (b : Bool) : Eval d gS [bool b] (some (int 1)) := by
  cases b with
  | true =>
    exact .clause (fn := fnG) (cl := clG0) (σ := [(0, bool true)]) hd.lookG (List.mem_cons_self ..)
      (sorted1 rfl (rmS_sortOf_bool d true)) (.cons (.var rfl) .nil)
      (fun t ht => by cases ht; exact (.var : EvalTerm d [(0, bool true)] (.var 0) _)) .top
      (fun cl' hcl' _ hlt => absurd hlt (prioG (List.mem_cons_self ..) hcl'))
      rfl .dv (fun t ht => nomatch ht) .top
  | false =>
    exact .clause (fn := fnG) (cl := clG1) (σ := [(0, bool false)]) hd.lookG
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      (sorted1 rfl (rmS_sortOf_bool d false)) (.cons (.var rfl) .nil)
      (fun t ht => by cases ht; exact evalNot hd.notC (σ := [(0, bool false)]) (b := false) rfl) .top
      (fun cl' hcl' _ hlt => absurd hlt (prioG (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hcl'))
      rfl .dv (fun t ht => nomatch ht) .top

/-- **`g(b)` has no other result.** -/
theorem aloneG (hd : Reads d) {b : Bool} {r : Option GroundTerm} (h : Eval d gS [bool b] r) :
    r = some (int 1) := by
  have hcl : ∀ {cl fn'}, d.lookupFn gS = some fn' → cl ∈ fn'.clauses → cl = clG0 ∨ cl = clG1 :=
    fun h1 h2 => by rw [hd.lookG] at h1; cases h1; simpa [fnG] using h2
  have hs : d.WellSorted [Srt.bool] [(0, bool b)] := sorted1 rfl (rmS_sortOf_bool d b)
  cases h with
  | clause hfn' hmem _ _ _ _ _ _ hrhs _ _ =>
    rcases hcl hfn' hmem with rfl | rfl <;> exact EvalTerm.dv_inv hrhs
  | rest hfn' hnone =>
    rw [hd.lookG] at hfn'; cases hfn'
    cases b with
    | true =>
      cases hnone clG0 (List.mem_cons_self ..) with
      | intro hF =>
        cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
        | intro ht he hr => cases ht; exact absurd (EvalTerm.var_inv he) hr
        | pre hp => cases hp
    | false =>
      cases hnone clG1 (List.mem_cons_of_mem _ (List.mem_singleton_self _)) with
      | intro hF =>
        cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
        | intro ht he hr => cases ht; exact absurd (evalNot_inv hd.notC (b := false) rfl he) hr
        | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => rcases hcl hfn' hmem with rfl | rfl <;> cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => rcases hcl hfn' hmem with rfl | rfl <;> exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => rcases hcl hfn' hmem with rfl | rfl <;> exact absurd rfl hne

/-- **`h(b)` is 1**, by its one clause. -/
theorem valueH (hd : Reads d) (b : Bool) : Eval d hS [bool b] (some (int 1)) :=
  .clause (fn := fnH) (cl := clH) (σ := [(0, bool b)]) hd.lookH (List.mem_singleton_self _)
    (sorted1 rfl (rmS_sortOf_bool d b)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .dv (fun t ht => nomatch ht) .top

/-- **`h(b)` has no other result.** -/
theorem aloneH (hd : Reads d) {b : Bool} {r : Option GroundTerm} (h : Eval d hS [bool b] r) :
    r = some (int 1) := by
  have hcl : ∀ {cl fn'}, d.lookupFn hS = some fn' → cl ∈ fn'.clauses → cl = clH := fun h1 h2 => by
    rw [hd.lookH] at h1; cases h1; simpa [fnH] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ _ hrhs _ _ => obtain rfl := hcl hfn' hmem; exact EvalTerm.dv_inv hrhs
  | rest hfn' hnone =>
    rw [hd.lookH] at hfn'; cases hfn'
    cases hnone clH (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clH.vars [(0, bool b)] := sorted1 rfl (rmS_sortOf_bool d b)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

/-! ### f -/

/-- The truth value of f's `post` where B has a value of Bool: B's value is X's, and Z has a value,
which is `g(B) = 1` and `h(B) = 1`. -/
def postVal (σ : Subst) : Bool :=
  sameResult (σ.lookup 1) (σ.lookup 0) && (((σ.lookup 2).isSome && sameResult (σ.lookup 2) (some (int 1))) &&
    ((σ.lookup 2).isSome && sameResult (σ.lookup 2) (some (int 1))))

theorem post_holds (hd : Reads d) {w : Bool} (h1 : σ.lookup 1 = some (bool w)) :
    Holds d 3 σ clF.post (postVal σ) :=
  .and (.equals .var .var)
    (.and (.mem .var (call_var hd.gC hooks.2.1 hd.gP h1 (valueG hd w)))
      (.mem .var (call_var hd.hC hooks.2.2 hd.hP h1 (valueH hd w))))

theorem post_inv (hd : Reads d) {w : Bool} (h1 : σ.lookup 1 = some (bool w)) {t : Bool}
    (h : Holds d 3 σ clF.post t) : t = postVal σ := by
  cases h with
  | and he hm =>
    cases he with
    | equals he1 he2 =>
      cases hm with
      | and hg hh =>
        cases hg with
        | mem hg1 hg2 =>
          cases hh with
          | mem hh1 hh2 =>
            obtain rfl := EvalTerm.var_inv he1
            obtain rfl := EvalTerm.var_inv he2
            obtain rfl := EvalTerm.var_inv hg1
            obtain rfl := EvalTerm.var_inv hh1
            obtain rfl := aloneG hd (call_var_inv hd.gC hooks.2.1 hd.gP hd.gO h1 hg2)
            obtain rfl := aloneH hd (call_var_inv hd.hC hooks.2.2 hd.hP hd.hO h1 hh2)
            rfl

/-- Where `post` is true, Z has the value 1. -/
theorem postVal_z (h : postVal σ = true) : σ.lookup 2 = some (int 1) := by
  simp only [postVal, Bool.and_eq_true] at h
  exact sameResult_eq_some h.2.1.2

/-- `post` is true at B := X's value and Z := 1. -/
theorem postVal_at {x : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some x)
    (h2 : σ.lookup 2 = some (int 1)) : postVal σ = true := by
  simp [postVal, h0, h1, h2, sameResult_self]

/-- B's value in a well-sorted instance is a literal of Bool. -/
theorem bF (hd : Reads d) (hw : d.WellSorted clF.vars σ) : ∃ w, σ.lookup 1 = some (bool w) := by
  obtain ⟨w, hw1, hws⟩ := hw 1 Srt.bool rfl
  obtain ⟨w', rfl⟩ := shape_bool hd.shapes hws
  exact ⟨w', hw1⟩

/-- **Every instance is decided and gives 1 or nothing**: where its `post` is true Z is 1, the
right-hand side. -/
theorem inst_all (hd : Reads d) (hw : d.WellSorted clF.vars σ) : InstIs d σ clF (some (int 1)) := by
  obtain ⟨w, hw1⟩ := bF hd hw
  cases hv : postVal σ with
  | true =>
    have hr : EvalTerm d σ clF.rhs (σ.lookup 2) := .var
    rw [postVal_z hv] at hr
    exact .gives hr (fun t ht => nomatch ht) (holds_cast (post_holds hd hw1) hv)
  | false => exact .fails (post_holds hd hw1) (.post (holds_cast (post_holds hd hw1) hv))

/-- The instance at B := b and Z := 1 does not give nothing. -/
theorem inst_not_none (hd : Reads d) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (h1 : σ.lookup 1 = some (bool b)) (h2 : σ.lookup 2 = some (int 1)) : ¬ InstIs d σ clF none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := post_inv hd h1 hp
      rw [postVal_at h0 h1 h2] at e
      cases e
    | rhs h => have := EvalTerm.var_inv h; rw [h2] at this; cases this

/-- σ with B := b and Z := 1 is an instance of the clause at σ, well sorted where σ gives X the
value b. -/
theorem ext_sorted {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    d.WellSorted clF.vars ((2, int 1) :: (1, bool b) :: σ) :=
  sorted3 ((lkNe _ _ (by decide)).trans ((lkNe _ _ (by decide)).trans h0)) (rmS_sortOf_bool d b)
    ((lkNe _ _ (by decide)).trans (lkSelf _ _ _)) (rmS_sortOf_bool d b) (lkSelf _ _ _) (sortOf_int 1)

theorem ext_agree (σ : Subst) (w z : GroundTerm) : AgreeOff clF.exsFree σ ((2, z) :: (1, w) :: σ) :=
  agree_set12 σ w z

/-- **`f(b)` is 1**, by `Eval.clauseEx` at B := b and Z := 1. -/
theorem value (hd : Reads d) (b : Bool) : Eval d fF [bool b] (some (int 1)) :=
  .clauseEx (fn := fnF) (cl := clF) (σ := [(2, int 1), (1, bool b), (0, bool b)]) hd.lookF
    (List.mem_singleton_self _)
    (sorted3 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d b) rfl (sortOf_int 1)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (post_holds hd (w := b) rfl) (postVal_at (x := bool b) rfl rfl rfl))
    (fun σ' _ hw => inst_all hd hw)

/-- **`f(b)` has no other result.** -/
theorem alone (hd : Reads d) {b : Bool} {r : Option GroundTerm} (h : Eval d fF [bool b] r) :
    r = some (int 1) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hd.lookF] at h1; cases h1; simpa [fnF] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hd.lookF] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clF.vars [(2, int 1), (1, bool b), (0, bool b)] :=
        sorted3 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d b) rfl (sortOf_int 1)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem hσ _ _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨w, hw1⟩ := bF hd hσ
    have e := post_inv hd hw1 hpost
    exact (EvalTerm.var_inv hrhs).trans (postVal_z e.symm)
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := pat0 hmatch
    exact absurd (hall _ (ext_agree σ _ _) (ext_sorted h0))
      (inst_not_none hd ((lkNe _ _ (by decide)).trans ((lkNe _ _ (by decide)).trans h0))
        ((lkNe _ _ (by decide)).trans (lkSelf _ _ _)) (lkSelf _ _ _))

end Clauses

/-! ### The expectations, for every H -/

theorem reads (H : HookParams) : Reads (cH H) where
  notC := (isCtor_wh c H _).trans ctors.1
  gC := (isCtor_wh c H _).trans ctors.2.1
  gP := (isParam_wh c H _).trans fnsPlain.1
  gO := (isOvl_wh c H _).trans fnsPlain.2.1
  hC := (isCtor_wh c H _).trans ctors.2.2
  hP := (isParam_wh c H _).trans fnsPlain.2.2.1
  hO := (isOvl_wh c H _).trans fnsPlain.2.2.2
  shapes := (shapesOK_wh c H).trans shapes
  lookF := by rw [Semantics.lookupFn_withHooks]; exact lookupF
  lookG := by rw [Semantics.lookupFn_withHooks]; exact lookupG
  lookH := by rw [Semantics.lookupFn_withHooks]; exact lookupH

/-- **`g(b) = 1`, for every H.** -/
theorem g_value (H : HookParams) (b : Bool) : Eval (cH H) gS [bool b] (some (int 1)) := valueG (reads H) b

/-- **`g(b)` has no other result, for every H.** -/
theorem g_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) gS [bool b] r) :
    r = some (int 1) := aloneG (reads H) h

/-- **`h(b) = 1`, for every H.** -/
theorem h_value (H : HookParams) (b : Bool) : Eval (cH H) hS [bool b] (some (int 1)) := valueH (reads H) b

/-- **`h(b)` has no other result, for every H.** -/
theorem h_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) hS [bool b] r) :
    r = some (int 1) := aloneH (reads H) h

/-- **`f(b) = 1`, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) fF [bool b] (some (int 1)) := value (reads H) b

/-- **`f(b)` has no other result, for every H.** -/
theorem f_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fF [bool b] r) :
    r = some (int 1) := alone (reads H) h

/-- **`f(true) = 1`, for every H.** -/
theorem f_true (H : HookParams) : Eval (cH H) fF [bool true] (some (int 1)) := f_value H true

/-- **`f(true)` has no result but 1, for every H**: no other integer, and not none. -/
theorem f_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fF [bool true] r) :
    r = some (int 1) := f_alone H h

end ExClauseFixtures.ExConfFix

/-- info: 'ExClauseFixtures.ExConfFix.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.read
/-- info: 'ExClauseFixtures.ExConfFix.g_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.g_value
/-- info: 'ExClauseFixtures.ExConfFix.g_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.g_alone
/-- info: 'ExClauseFixtures.ExConfFix.h_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.h_value
/-- info: 'ExClauseFixtures.ExConfFix.h_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.h_alone
/-- info: 'ExClauseFixtures.ExConfFix.f_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.f_value
/-- info: 'ExClauseFixtures.ExConfFix.f_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.f_alone
/-- info: 'ExClauseFixtures.ExConfFix.f_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.f_true
/-- info: 'ExClauseFixtures.ExConfFix.f_true_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExConfFix.f_true_alone
