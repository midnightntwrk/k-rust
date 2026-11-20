/-
  The fixture e3-eq-exists-under-app-partial-ml (a binder under an application on an equation's right
  side, of a function that is not `total`): the clauses the reader gives for its text and the results
  of `f`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxUnderApp.lean`.

  `syntax Bool ::= f(Bool) [function] | g(Bool) [function, total]`,
  `rule f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))` (axiom 132) and `rule g(B) => notBool B`.

  From the sentences: `g(∃B. (B ∧ B = X))` is the union over the elements b of Bool of g applied to
  `b ∧ (b = x)`, which is `g(b)` where b = x and empty elsewhere (an application at an empty argument
  is empty). So `f(x) = g(x) = notBool x`: `f(true) = false`, `f(false) = true`, and nothing else.
  f has a value at every argument: the text has no argument at which f is without one.

  The statements are on `defn`, the definition the reader gives for the text
  (`f2-examples/e3-eq-exists-under-app-partial-ml.kompile.kore`), each for every hook interpretation H:
  - The clauses read are `clF` and `clG` (`read`): for f `[X:Bool, B:Bool]`, `exs [1]`, `rhs g(B)`,
    `post B = X` (the binder at the top of the right side, the application over its variable); for g
    `[B:Bool]`, `rhs notBool B`. f is not `total` and has no other clause.
  - `f_value`: `f(b)` has the result `notBool b`, by `Eval.clauseEx` at B := b. The instance at the
    other value of Bool has `post` false: an instance that gives nothing, not a result none
    (`inst_all`).
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

namespace ExClauseFixtures.ExUnderApp

open GroundTerm ExClauseFixtures.CeFx

definition_of defn from "f2-examples/e3-eq-exists-under-app-partial-ml.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def gS : Sym := 385

/-- `f(X) => g(B)` with `exs = [B]` and `post := B = X`, X and B of Bool. -/
def clF : Clause :=
  { vars := [Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .app gS [.var 1], ens := none,
    exs := [1], post := .equals Srt.bool (.var 1) (.var 0) }

def fnF : Fn := { label := fF, args := [Srt.bool], result := Srt.bool, clauses := [clF] }

/-- `g(B) => notBool B`. -/
def clG : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs := .app boolNot [.var 0], ens := none }

def fnG : Fn := { label := gS, args := [Srt.bool], result := Srt.bool, clauses := [clG], total := true }

/-- **The reading**: the text's functions are `f`, with the one clause `clF`, and `g`. -/
theorem read : c.fns = [fnF, fnG] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.symName boolNot = "LblnotBool'Unds'" ∧
    c.sortName Srt.bool = "Bool" := by decide +kernel

/-- B is of the confined sort Bool: the clause is one `clausePlainEx` admits. -/
theorem plainEx : c.confined Srt.bool = true ∧ c.clausePlainEx clF = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel
theorem gCtor : c.isCtor gS = false := by decide +kernel
theorem gParam : c.isParam gS = false := by decide +kernel
theorem gOvl : c.isOvl gS = false := by decide +kernel

/-- What a semantics must give for the two clauses to be read in it: `notBool` the hook, and `g`
the function with the clause `clG`, `f` the one with `clF`. -/
structure Reads (d : Semantics) : Prop where
  notC : d.isCtor boolNot = false
  gC : d.isCtor gS = false
  gP : d.isParam gS = false
  gO : d.isOvl gS = false
  lookF : d.lookupFn fF = some fnF
  lookG : d.lookupFn gS = some fnG

section Clauses

variable {d : Semantics} {σ : Subst}

theorem notHook : isHook boolNot = true := by decide +kernel
theorem gHook : isHook gS = false := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation (domains.md 1138, 1139). -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

theorem evalNot (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    EvalTerm d σ (.app boolNot [.var 0]) (some (bool (!b))) :=
  .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalNot_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : EvalTerm d σ (.app boolNot [.var 0]) r) : r = some (bool (!b)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  have := hh [bool b] (by rw [h0]; rfl)
  rw [hookNot] at this
  exact (Option.some.inj this).symm

/-! ### g -/

/-- **`g(b)` is `notBool b`**, by its one clause. -/
theorem valueG (hd : Reads d) (b : Bool) : Eval d gS [bool b] (some (bool (!b))) :=
  .clause (fn := fnG) (cl := clG) (σ := [(0, bool b)]) hd.lookG (List.mem_singleton_self _)
    (sorted1 rfl (rmS_sortOf_bool d b)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evalNot hd.notC rfl) (fun t ht => nomatch ht) .top

/-- **`g(b)` has no other result.** -/
theorem aloneG (hd : Reads d) {b : Bool} {r : Option GroundTerm} (h : Eval d gS [bool b] r) :
    r = some (bool (!b)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn gS = some fn' → cl ∈ fn'.clauses → cl = clG := fun h1 h2 => by
    rw [hd.lookG] at h1; cases h1; simpa [fnG] using h2
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    exact evalNot_inv hd.notC (pat0 hmatch) hrhs
  | rest hfn' hnone =>
    rw [hd.lookG] at hfn'; cases hfn'
    cases hnone clG (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clG.vars [(0, bool b)] := sorted1 rfl (rmS_sortOf_bool d b)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

/-- The clause's right-hand side `g(B)` where B has the value w. -/
theorem rhsF (hd : Reads d) {w : Bool} (h1 : σ.lookup 1 = some (bool w)) :
    EvalTerm d σ clF.rhs (some (bool (!w))) :=
  call_var hd.gC gHook hd.gP h1 (valueG hd w)

theorem rhsF_inv (hd : Reads d) {w : Bool} (h1 : σ.lookup 1 = some (bool w)) {r : Option GroundTerm}
    (h : EvalTerm d σ clF.rhs r) : r = some (bool (!w)) :=
  aloneG hd (call_var_inv hd.gC gHook hd.gP hd.gO h1 h)

/-! ### f -/

/-- The clause's `post`: whether B's value is X's. -/
theorem post_holds : Holds d 2 σ clF.post (sameResult (σ.lookup 1) (σ.lookup 0)) := Holds.equals .var .var

theorem post_inv {t : Bool} (h : Holds d 2 σ clF.post t) : t = sameResult (σ.lookup 1) (σ.lookup 0) := by
  cases h with
  | equals h1 h2 =>
    obtain rfl := EvalTerm.var_inv h1
    obtain rfl := EvalTerm.var_inv h2
    rfl

/-- **Every instance is decided and gives `notBool b` or nothing**: at B := b it gives `g(b)`, at
another value its `post` is false. -/
theorem inst_all (hd : Reads d) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (hw : d.WellSorted clF.vars σ) : InstIs d σ clF (some (bool (!b))) := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.bool rfl
  cases hb : sameResult (some w) (some (bool b)) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (rhsF hd hw1) (fun t ht => nomatch ht) (holds_cast post_holds (by rw [hw1, h0, hb]))
  | false => exact .fails post_holds (.post (holds_cast post_holds (by rw [hw1, h0, hb])))

/-- The instance at B := b does not give nothing. -/
theorem inst_not_none (hd : Reads d) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (h1 : σ.lookup 1 = some (bool b)) : ¬ InstIs d σ clF none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := post_inv hp
      rw [h1, h0, sameResult_self] at e
      cases e
    | rhs h => cases rhsF_inv hd h1 h

/-- σ with B := b is an instance of the clause at σ, well sorted where σ gives X the value b. -/
theorem ext_sorted {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    d.WellSorted clF.vars ((1, bool b) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (rmS_sortOf_bool d b) (lkSelf _ _ _) (rmS_sortOf_bool d b)

theorem ext_agree (σ : Subst) (w : GroundTerm) : AgreeOff clF.exsFree σ ((1, w) :: σ) := agree_set1 σ w

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff clF.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- **`f(b)` is `notBool b`**, by `Eval.clauseEx` at B := b. -/
theorem value (hd : Reads d) (b : Bool) : Eval d fF [bool b] (some (bool (!b))) :=
  have h0 : ([(1, bool b), (0, bool b)] : Subst).lookup 0 = some (bool b) := rfl
  .clauseEx (fn := fnF) (cl := clF) (σ := [(1, bool b), (0, bool b)]) hd.lookF (List.mem_singleton_self _)
    (sorted2 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d b)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) (rhsF hd rfl) (fun t ht => nomatch ht)
    (holds_cast post_holds (sameResult_self (bool b)))
    (fun σ' ha hw => inst_all hd ((agree_x ha).trans h0) hw)

/-- **`f(b)` has no other result.** -/
theorem alone (hd : Reads d) {b : Bool} {r : Option GroundTerm} (h : Eval d fF [bool b] r) :
    r = some (bool (!b)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hd.lookF] at h1; cases h1; simpa [fnF] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hd.lookF] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clF.vars [(1, bool b), (0, bool b)] :=
        sorted2 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d b)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have e := post_inv hpost
    rw [pat0 hmatch] at e
    exact rhsF_inv hd (sameResult_eq_some e.symm) hrhs
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := pat0 hmatch
    exact absurd (hall _ (ext_agree σ _) (ext_sorted h0))
      (inst_not_none hd ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

end Clauses

/-! ### The expectations, for every H -/

theorem reads (H : HookParams) : Reads (cH H) where
  notC := (isCtor_wh c H _).trans notCtor
  gC := (isCtor_wh c H _).trans gCtor
  gP := (isParam_wh c H _).trans gParam
  gO := (isOvl_wh c H _).trans gOvl
  lookF := by rw [Semantics.lookupFn_withHooks]; exact lookupF
  lookG := by rw [Semantics.lookupFn_withHooks]; exact lookupG

/-- **`f(b) = notBool b`, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) fF [bool b] (some (bool (!b))) :=
  value (reads H) b

/-- **`f(b)` has no other result, for every H.** -/
theorem f_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fF [bool b] r) :
    r = some (bool (!b)) :=
  alone (reads H) h

/-- **`f(true) = false`, for every H.** -/
theorem f_true (H : HookParams) : Eval (cH H) fF [bool true] (some (bool false)) := f_value H true

/-- **`f(true)` has no result but `false`, for every H**: not `true`, and not none. -/
theorem f_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fF [bool true] r) :
    r = some (bool false) := f_alone H h

end ExClauseFixtures.ExUnderApp

/-- info: 'ExClauseFixtures.ExUnderApp.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.ExUnderApp.read
/-- info: 'ExClauseFixtures.ExUnderApp.f_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExUnderApp.f_value
/-- info: 'ExClauseFixtures.ExUnderApp.f_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExUnderApp.f_alone
/-- info: 'ExClauseFixtures.ExUnderApp.f_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExUnderApp.f_true
/-- info: 'ExClauseFixtures.ExUnderApp.f_true_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExUnderApp.f_true_alone
