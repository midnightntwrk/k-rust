/-
  The fixture e3-eq-exists-ml-in-or-float
  (`rule f(X) => X #Or (#Exists B:Float. (B #And {B #Equals X +Float 1.0}))`, f `[function]` over
  Float, not `total`): the clause the reader gives for its text and that `f(1.0)` has no result, for
  every hook interpretation. Run from the package root:
  `lake env lean -j1 test/ExClauseFxInOrFloat.lean`.

  The text is `f2-examples/e3-eq-exists-ml-in-or-float.kompile.kore`; sentence 151
  (`AxiomDecl.index`) is f's equation
  `f(X0) = (X ∨ ∃B:Float. (B ∧ {B = X +Float 1.0})) ∧ \top` (with `X0 ∈ X`). The text holds no
  functional sentence of f.

  From the sentence: f(x) is the elements of x and of x +Float 1.0. At the double 1.0 the sum is
  the double 2.0 (both exactly represented, so the sum is exact), another element: f(1.0) is two
  elements.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clause read is `clO Srt.float tAdd` (`read`): `[X:Float, #Or0:Float]`, `exs [1]`,
    `rhs #Or0`, `post (#Or0 ∈ X) ∨ ∃B:Float. ((#Or0 ∈ B) ∧ (B = X +Float 1.0))`. The binder is kept in
    its alternative (`Cond.ex`, its variable the index 2): Float is not confined, and the binder's
    body equates it with a term over X. f is not `total` and has no other clause.
  - `plainEx`: `clausePlainEx` admits the clause (each alternative fixes #Or0).
  - `no_result_one`: `f(1.0)` has no result at all, neither a value nor none. The instance at
    #Or0 := 1.0 gives 1.0 (the first alternative), the instance at #Or0 := 2.0 gives 2.0 (the
    second, the binder's witness 2.0), and the two differ. So no `Eval.clauseEx` derivation exists,
    no `Eval.exNone`, and the clause applies at every argument, so no `Eval.rest`.
    `1.0 +Float 1.0` is a value of the registry (`hookOneOne`), so the same under every H.
    The statement is at the argument 1.0, not at every Float: where `x +Float 1.0` is x (the sum
    rounds back to x) the two instances agree, and where the registry gives the sum no value the
    interpretation H may.
  - `not_matchIndependent`: the owed fact the package names for the clause (`MatchIndependent`) is
    false: the clause decides at `[1.0]` and has no result there (`Clause.Res`).
  - `not_fnHyp`: `FnHyp` is false (f has no result at 1.0).
  The facts on the clause's shape (`clO s t`, a binder of sort s kept in the second alternative and
  equated there with the term t over X) are stated once, from what t evaluates to (`TermAt`), as in
  test/ExClauseFxInOrInt.lean (a test file imports no test file, so each repeats them).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.InOrFloatFx

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

/-- `f(X) => Z` with `exs = [Z]` and `post := (Z ∈ X) ∨ ∃B:s. ((Z ∈ B) ∧ (B = t))`, X and Z of the
sort s; the binder B is the index 2, bound in its alternative. -/
def clO (s : Srt) (t : Term) : Clause :=
  { vars := [s, s], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .or (.mem s (.var 1) (.var 0))
      (.ex s (.and (.mem s (.var 1) (.var 2)) (.equals s (.var 2) t))) }

def fnO (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clO s t] }

/-- Under every σ giving X the value x, the term t has no result but the value y. -/
def TermAt (d : Semantics) (t : Term) (x y : GroundTerm) : Prop :=
  ∀ (σ : Subst) (r : Option GroundTerm), σ.lookup 0 = some x → EvalTerm d σ t r → r = some y

section Shape

variable {s : Srt} {t : Term} {x y : GroundTerm} {f : Sym}

/-- Where Z is X's value, `post` has no truth value but true: its first alternative holds. -/
theorem post_at_x (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some x) {b : Bool}
    (h : Holds d 2 σ (clO s t).post b) : b = true := by
  cases h with
  | or h h' =>
    cases h with
    | mem a1 a0 =>
      obtain rfl := EvalTerm.var_inv a1
      obtain rfl := EvalTerm.var_inv a0
      rw [h0, h1]; simp [sameResult_self]

/-- σ with the binder's index given the value y of the sort s. -/
theorem extends_y (σ : Subst) (hy : d.sortOf y = some s) : Extends d 2 [s] σ ((2, y) :: σ) :=
  ⟨fun _ hi => lkNe y σ (Nat.ne_of_lt hi), fun j s' hj => by
    match j, hj with
    | 0, hj => cases hj; exact ⟨y, lkSelf _ _ _, hy⟩
    | j + 1, hj => simp at hj⟩

/-- Where Z is t's value y, `post` has no truth value but true: the second alternative holds, at
the binder's value y. -/
theorem post_at_y (ht : TermAt d t x y) (hy : d.sortOf y = some s) (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some y) {b : Bool} (h : Holds d 2 σ (clO s t).post b) : b = true := by
  cases h with
  | @or _ _ _ _ b1 b2 h h' =>
    cases h' with
    | ex g hb hr =>
      have l1 : ((2, y) :: σ : Subst).lookup 1 = some y := (lkNe y σ (by decide)).trans h1
      have l2 : ((2, y) :: σ : Subst).lookup 2 = some y := lkSelf _ _ _
      have hg : g ((2, y) :: σ) = true := by
        have hb' := hb _ (extends_y σ hy)
        generalize g ((2, y) :: σ) = gb at hb'
        cases hb' with
        | and hm he =>
          cases hm with
          | mem a1 a2 =>
            cases he with
            | equals e1 e2 =>
              obtain rfl := EvalTerm.var_inv a1
              obtain rfl := EvalTerm.var_inv a2
              obtain rfl := EvalTerm.var_inv e1
              obtain rfl := ht _ _ ((lkNe y σ (by decide)).trans h0) e2
              rw [l1, l2]; simp [sameResult_self]
      have e2 : b2 = true := hr.mpr ⟨_, extends_y σ hy, hg⟩
      rw [e2]; simp

theorem exsFree_clO : (clO s t).exsFree = [1] := rfl
theorem exs_clO : (clO s t).exs ≠ [] := List.cons_ne_nil 1 []

/-- An instance at which Z has the value w and `post` has no truth value but true gives w. -/
theorem inst_eq {σ' : Subst} {w : GroundTerm} {r : Option GroundTerm} (h1 : σ'.lookup 1 = some w)
    (hp : ∀ b, Holds d 2 σ' (clO s t).post b → b = true) (h : InstIs d σ' (clO s t) r) : r = some w := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp' => cases hp _ hp'
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- **The instances at Z := x and Z := y do not agree on one result**, where y is not x: no r is
the result of every instance of the clause at a match giving X the value x. -/
theorem two_insts (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (h0 : σ.lookup 0 = some x) {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff (clO s t).exsFree σ σ' → d.WellSorted (clO s t).vars σ' → InstIs d σ' (clO s t) r) :
    False := by
  have h0' : ∀ w, ((1, w) :: σ : Subst).lookup 0 = some x := fun w => (lkNe _ _ (by decide)).trans h0
  have hw : ∀ w, d.sortOf w = some s → d.WellSorted (clO s t).vars ((1, w) :: σ) := fun w hw =>
    sorted2 (h0' w) hx (lkSelf _ _ _) hw
  have e1 := inst_eq (lkSelf 1 x σ) (fun _ hb => post_at_x (h0' x) (lkSelf _ _ _) hb)
    (hall _ (agree_set1 σ _) (hw x hx))
  have e2 := inst_eq (lkSelf 1 y σ) (fun _ hb => post_at_y ht hy (h0' y) (lkSelf _ _ _) hb)
    (hall _ (agree_set1 σ _) (hw y hy))
  rw [e1] at e2
  exact hne (Option.some.inj e2).symm

theorem pat_x {σ : Subst} (hm : PatVals d σ (clO s t).pats [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

/-- **`f(x)` has no result**, where t's value y at x is not x. -/
theorem no_res (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnO f s t)) {r : Option GroundTerm} (h : Eval d f [x] r) : False := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clO s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnO] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clO
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone (clO s t) (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted (clO s t).vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clO
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall
  | exNone hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall

/-- **The clause is not match independent**: it decides at `[x]` and has no result there. -/
theorem not_mi (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnO f s t)) : ¬ MatchIndependent d (clO s t) := by
  intro hm
  have hs : d.WellSorted (clO s t).vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
  have hdec : (clO s t).Decides d (fnO f s t) [(1, x), (0, x)] [x] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnO, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 exs_clO f (fnO f s t) [x] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex exs_clO
  · exact two_insts (σ := [(1, x), (0, x)]) ht hne hx hy rfl hall
  · exact two_insts (σ := [(1, x), (0, x)]) ht hne hx hy rfl hall

end Shape

end ExClauseFixtures.InOrFloatFx

namespace ExClauseFixtures.InOrFloat

open GroundTerm ExClauseFixtures.InOrFloatFx

definition_of defn from "f2-examples/e3-eq-exists-ml-in-or-float.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384

/-- The doubles 1.0 (`0x3FF0000000000000`) and 2.0 (`0x4000000000000000`). -/
def one : GroundTerm := .dv Srt.float (.float 53 11 4607182418800017408)
def two : GroundTerm := .dv Srt.float (.float 53 11 4611686018427387904)

/-- The term the binder is equated with, `X +Float 1.0`. -/
def tAdd : Term := .app floatAdd [.var 0, .dv Srt.float (.float 53 11 4607182418800017408)]

/-- **The reading**: the text's one function is f, not `total`, with the one clause
`[X:Float, #Or0:Float]`, `exs [1]`, `rhs #Or0`,
`post (#Or0 ∈ X) ∨ ∃B:Float. ((#Or0 ∈ B) ∧ (B = X +Float 1.0))`: the binder kept in its alternative. -/
theorem read : c.fns = [fnO fF Srt.float tAdd] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧
    c.symName floatAdd = "Lbl'UndsPlus'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float" ∧
    c.sortName Srt.float = "Float" := by decide +kernel

/-- Float is not confined; each alternative fixes #Or0 (the second by the binder, which its body
equates with a term over X): `clausePlainEx` admits the clause. -/
theorem plainEx : c.confined Srt.float = false ∧ c.clausePlainEx (clO Srt.float tAdd) = true := by
  decide +kernel

theorem lookupF : c.lookupFn fF = some (fnO fF Srt.float tAdd) := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor floatAdd = false := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem sort_one : c.sortOf one = some Srt.float := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩
theorem sort_two : c.sortOf two = some Srt.float := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩

section Terms

variable {d : Semantics}

theorem addHook : isHook floatAdd = true := by decide +kernel

/-- `1.0 +Float 1.0` is 2.0 in the registry, so under every interpretation. -/
theorem hookOneOne : d.hookRes floatAdd [one, one] = some (some two) :=
  Semantics.hookRes_of_value (by decide +kernel)

/-- `X +Float 1.0` where X is 1.0: 2.0, and no other result. -/
theorem tAdd_at (hc : d.isCtor floatAdd = false) : TermAt d tAdd one two := by
  intro σ r h0 h
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc addHook h
  obtain ⟨r1, rs1, rfl, h1, hs1⟩ := EvalTerms.cons_inv hts
  obtain ⟨r2, rs2, rfl, h2, hs2⟩ := EvalTerms.cons_inv hs1
  obtain rfl := EvalTerms.nil_inv hs2
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [one, one] (by rw [h0]; rfl)
  rw [hookOneOne] at this
  exact (Option.some.inj this).symm

theorem two_ne : two ≠ one := by decide

end Terms

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some (fnO fF Srt.float tAdd) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

theorem tAdd_atH (H : HookParams) : TermAt (cH H) tAdd one two := tAdd_at (d := cH H) notCtor

theorem sort_oneH (H : HookParams) : (cH H).sortOf one = some Srt.float := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_one
theorem sort_twoH (H : HookParams) : (cH H).sortOf two = some Srt.float := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_two

/-- **`f(1.0)` has no result, for every H**: neither a value nor none. Its instances at
#Or0 := 1.0 and at #Or0 := 2.0 give 1.0 and 2.0. -/
theorem no_result_one (H : HookParams) (r : Option GroundTerm) : ¬ Eval (cH H) fF [one] r :=
  fun h => no_res (tAdd_atH H) two_ne (sort_oneH H) (sort_twoH H) (lookupFH H) h

/-- **The owed fact the package names for f's clause, `MatchIndependent`, is false, for every H.** -/
theorem not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) (clO Srt.float tAdd) :=
  not_mi (tAdd_atH H) two_ne (sort_oneH H) (sort_twoH H) (lookupFH H)

/-- **`FnHyp` is false, for every H**: f has no result at 1.0. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [one] = some (fnO fF Srt.float tAdd).args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
  obtain ⟨r, hr⟩ := hf.1 (fnO fF Srt.float tAdd)
    (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_singleton_self _) [one] hso
  exact no_result_one H r hr

end ExClauseFixtures.InOrFloat

/-- info: 'ExClauseFixtures.InOrFloat.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.InOrFloat.read
/-- info: 'ExClauseFixtures.InOrFloat.no_result_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOrFloat.no_result_one
/-- info: 'ExClauseFixtures.InOrFloat.not_matchIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOrFloat.not_matchIndependent
/-- info: 'ExClauseFixtures.InOrFloat.not_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOrFloat.not_fnHyp
