/-
  The fixture e3-eq-exists-ml-in-or
  (`rule f(X) => X #Or (#Exists B:Bool. (B #And {B #Equals notBool X}))` and
  `rule fx(X) => X #Or (#Exists B:Bool. (B #And {B #Equals X}))`, f and fx `[function]` over Bool,
  neither `total`): the clauses the reader gives for its text, that `fx(x)` is x alone and that `f`
  has no result, for every hook interpretation. Run from the package root:
  `lake env lean -j1 test/ExClauseFxInOr.lean`.

  The text is `f2-examples/e3-eq-exists-ml-in-or.kompile.kore`; sentence numbers are
  `AxiomDecl.index`: 131 is f's equation
  `f(X0) = (X ∨ ∃B:Bool. (B ∧ {B = notBool X})) ∧ \top` (with `X0 ∈ X`), 132 fx's, the same with
  `{B = X}`. The text holds no functional sentence of f or of fx.

  From the sentences: f(x) is the set {x, notBool x}, two elements at every x; fx(x) is {x}.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clauses read (`read`): the binder, of the confined Bool, is moved over the `\or`
    (`(∃B:s. φ) ∨ ψ = ∃B:s. (φ ∨ ψ)`, s having an element) and the disjunction is a fresh variable:
    `[X:Bool, B:Bool, #Or0:Bool]`, `exs [1, 2]`, `rhs #Or0`,
    `post (#Or0 ∈ X) ∨ ((#Or0 ∈ B) ∧ (B = notBool X))` for f, and with `B = X` for fx.
  - `plainEx`: `clausePlainEx` admits both clauses.
  - `fx_value`, `fx_alone`: `fx(b)` is b, by `Eval.clauseEx` at B := b and #Or0 := b, and has no
    other result, and not none: an instance gives #Or0's value where `post` is true, which is where
    #Or0 is b (by either alternative); every other instance has `post` false (it gives nothing, not
    a result none). `fx_true`, `fx_true_alone`: the two at `true`.
  - `f_no_result`: `f(b)` has no result at all, neither a value nor none. The instance at B := b,
    #Or0 := b gives b (the first alternative), the instance at B := notBool b, #Or0 := notBool b
    gives notBool b (the second), and the two differ. So no `Eval.clauseEx` derivation exists (it
    asks every instance to give the one value or nothing), no `Eval.exNone` (it asks every instance
    to give nothing), and the clause applies at every argument, so no `Eval.rest`.
  - `f_not_matchIndependent`: the owed fact the package names for f's clause (`MatchIndependent`)
    is false: the clause decides at every argument and has no result there (`Clause.Res`).
  - `not_fnHyp`: `FnHyp` is false (f has no result at `true`).
  The two clauses have one shape, `clB s t` (the term t over X the binder is equated with); the
  facts on that shape are stated once, from what t evaluates to (`TermIs`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.InOrFx

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

/-- The instances of a clause whose existential variables are the variables 1 and 2: σ with them
set. -/
theorem agree_set12 (σ : Subst) (w1 w2 : GroundTerm) : AgreeOff [1, 2] σ ((2, w2) :: (1, w1) :: σ) := fun i hi => by
  have h1 : i ≠ 1 := fun h => hi (by rw [h]; decide)
  have h2 : i ≠ 2 := fun h => hi (by rw [h]; decide)
  rw [lkNe _ _ h2, lkNe _ _ h1]

/-- A substitution giving the variables 0, 1 and 2 values of the three sorts is well sorted. -/
theorem sorted3 {a b e : Srt} {x w1 w2 : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w1) (hw1 : d.sortOf w1 = some b) (h2 : σ.lookup 2 = some w2)
    (hw2 : d.sortOf w2 = some e) : d.WellSorted [a, b, e] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w1, h1, hw1⟩
  | 2, hs => cases hs; exact ⟨w2, h2, hw2⟩
  | i + 3, hs => simp at hs

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

/-- `f(X) => Z` with `exs = [B, Z]` and `post := (Z ∈ X) ∨ ((Z ∈ B) ∧ (B = t))`, the three
variables of the sort s. -/
def clB (s : Srt) (t : Term) : Clause :=
  { vars := [s, s, s], pats := [.var 0], req := none, rhs := .var 2, ens := none, exs := [1, 2],
    post := .or (.mem s (.var 2) (.var 0)) (.and (.mem s (.var 2) (.var 1)) (.equals s (.var 1) t)) }

def fnB (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clB s t] }

/-- Under every σ giving X the value x, the term t has the value y and no other result. -/
structure TermIs (d : Semantics) (t : Term) (x y : GroundTerm) : Prop where
  ev : ∀ (σ : Subst), σ.lookup 0 = some x → EvalTerm d σ t (some y)
  inv : ∀ (σ : Subst) (r : Option GroundTerm), σ.lookup 0 = some x → EvalTerm d σ t r → r = some y

section Shape

variable {s : Srt} {t : Term} {x y : GroundTerm} {f : Sym}

/-- The truth value of `post` where B has the value w1 and Z the value w2. -/
def postVal (x y w1 w2 : GroundTerm) : Bool :=
  sameResult (some w2) (some x) || (sameResult (some w2) (some w1) && sameResult (some w1) (some y))

theorem post_holds (ht : TermIs d t x y) {w1 w2 : GroundTerm} (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some w1) (h2 : σ.lookup 2 = some w2) : Holds d 3 σ (clB s t).post (postVal x y w1 w2) :=
  holds_cast (Holds.or (Holds.mem .var .var) (Holds.and (Holds.mem .var .var) (Holds.equals .var (ht.ev σ h0))))
    (by rw [h0, h1, h2]; rfl)

theorem post_inv (ht : TermIs d t x y) {w1 w2 : GroundTerm} (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some w1) (h2 : σ.lookup 2 = some w2) {b : Bool} (h : Holds d 3 σ (clB s t).post b) :
    b = postVal x y w1 w2 := by
  cases h with
  | or h h' =>
    cases h with
    | mem a2 a0 =>
      cases h' with
      | and hm he =>
        cases hm with
        | mem c2 c1 =>
          cases he with
          | equals e1 e2 =>
            obtain rfl := EvalTerm.var_inv a2
            obtain rfl := EvalTerm.var_inv a0
            obtain rfl := EvalTerm.var_inv c2
            obtain rfl := EvalTerm.var_inv c1
            obtain rfl := EvalTerm.var_inv e1
            obtain rfl := ht.inv σ _ h0 e2
            rw [h0, h1, h2]; rfl

theorem postVal_x (x y w1 : GroundTerm) : postVal x y w1 x = true := by
  simp [postVal, sameResult_self]
theorem postVal_y (x y : GroundTerm) : postVal x y y y = true := by
  simp [postVal, sameResult_self]
/-- Where t's value at x is x, `post` is true exactly where Z is x. -/
theorem postVal_same {x w1 w2 : GroundTerm} (h : postVal x x w1 w2 = true) : w2 = x := by
  simp only [postVal, Bool.or_eq_true, Bool.and_eq_true, sameResult_some] at h
  rcases h with h | ⟨h, h'⟩
  · exact h
  · exact h.trans h'

theorem exsFree_clB : (clB s t).exsFree = [1, 2] := rfl
theorem exs_clB : (clB s t).exs ≠ [] := List.cons_ne_nil 1 [2]

theorem agree_x {σ' : Subst} (h : AgreeOff (clB s t).exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by rw [exsFree_clB]; decide)

theorem pat_x {σ : Subst} (hm : PatVals d σ (clB s t).pats [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

/-- An instance at which Z has the value w2 and `post` is true gives w2. -/
theorem inst_eq (ht : TermIs d t x y) {σ' : Subst} {w1 w2 : GroundTerm} {r : Option GroundTerm}
    (h0 : σ'.lookup 0 = some x) (h1 : σ'.lookup 1 = some w1) (h2 : σ'.lookup 2 = some w2)
    (hv : postVal x y w1 w2 = true) (h : InstIs d σ' (clB s t) r) : r = some w2 := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht' _ _ => cases ht'
    | post hp =>
      have e := post_inv ht h0 h1 h2 hp
      rw [hv] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h2] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h2] at e; exact e

/-- σ with B and Z given the value w. -/
def set12 (σ : Subst) (w : GroundTerm) : Subst := (2, w) :: (1, w) :: σ

theorem set12_0 (h0 : σ.lookup 0 = some x) (w : GroundTerm) : (set12 σ w).lookup 0 = some x :=
  (lkNe _ _ (by decide)).trans ((lkNe _ _ (by decide)).trans h0)
theorem set12_1 (σ : Subst) (w : GroundTerm) : (set12 σ w).lookup 1 = some w :=
  (lkNe _ _ (by decide)).trans (lkSelf _ _ _)
theorem set12_2 (σ : Subst) (w : GroundTerm) : (set12 σ w).lookup 2 = some w := lkSelf _ _ _
theorem set12_sorted (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some s) {w : GroundTerm}
    (hw : d.sortOf w = some s) : d.WellSorted (clB s t).vars (set12 σ w) :=
  sorted3 (set12_0 h0 w) hx (set12_1 σ w) hw (set12_2 σ w) hw

/-- **The instances at B, Z := x and at B, Z := y do not agree on one result**, where y is not x:
no r is the result of every instance of the clause at a match giving X the value x. -/
theorem two_insts (ht : TermIs d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (h0 : σ.lookup 0 = some x) {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff (clB s t).exsFree σ σ' → d.WellSorted (clB s t).vars σ' → InstIs d σ' (clB s t) r) :
    False := by
  have e1 := inst_eq ht (set12_0 h0 x) (set12_1 σ x) (set12_2 σ x) (postVal_x x y x)
    (hall _ (agree_set12 σ _ _) (set12_sorted h0 hx hx))
  have e2 := inst_eq ht (set12_0 h0 y) (set12_1 σ y) (set12_2 σ y) (postVal_y x y)
    (hall _ (agree_set12 σ _ _) (set12_sorted h0 hx hy))
  rw [e1] at e2
  exact hne (Option.some.inj e2).symm

theorem sorted_x (hx : d.sortOf x = some s) : d.WellSorted (clB s t).vars [(2, x), (1, x), (0, x)] :=
  sorted3 rfl hx rfl hx rfl hx

/-- The clause does not fail at `[x]`: it has no `requires` and its `pre` is `⊤`. -/
theorem not_fails (hx : d.sortOf x = some s) : ¬ Fails d [x] (clB s t) := fun h => by
  cases h with
  | intro hF =>
    cases hF _ ((sorted_x hx).at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **`f(x)` has no result**, where t's value y at x is not x. -/
theorem no_res (ht : TermIs d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnB f s t)) {r : Option GroundTerm} (h : Eval d f [x] r) : False := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clB s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnB] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact not_fails hx (hnone (clB s t) (List.mem_singleton_self _))
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall
  | exNone hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall

/-- **The clause is not match independent**, where t's value y at x is not x: it decides at `[x]`
and has no result there. -/
theorem not_mi (ht : TermIs d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnB f s t)) : ¬ MatchIndependent d (clB s t) := by
  intro hm
  have hdec : (clB s t).Decides d (fnB f s t) [(2, x), (1, x), (0, x)] [x] :=
    ⟨⟨(sorted_x hx).at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnB, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 exs_clB f (fnB f s t) [x] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex exs_clB
  · exact two_insts (σ := [(2, x), (1, x), (0, x)]) ht hne hx hy rfl hall
  · exact two_insts (σ := [(2, x), (1, x), (0, x)]) ht hne hx hy rfl hall

/-- **Every instance is decided and gives x or nothing**, where t's value at x is x. -/
theorem inst_all (ht : TermIs d t x x) (h0 : σ.lookup 0 = some x) (hw : d.WellSorted (clB s t).vars σ) :
    InstIs d σ (clB s t) (some x) := by
  obtain ⟨w1, h1, -⟩ := hw 1 s rfl
  obtain ⟨w2, h2, -⟩ := hw 2 s rfl
  cases hb : postVal x x w1 w2 with
  | true =>
    obtain rfl := postVal_same hb
    exact .gives (h2 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds ht h0 h1 h2) hb)
  | false => exact .fails (post_holds ht h0 h1 h2) (.post (holds_cast (post_holds ht h0 h1 h2) hb))

/-- **`f(x)` is x**, where t's value at x is x, by `Eval.clauseEx` at B := x and Z := x. -/
theorem value (ht : TermIs d t x x) (hfn : d.lookupFn f = some (fnB f s t)) (hx : d.sortOf x = some s) :
    Eval d f [x] (some x) :=
  have h0 : ([(2, x), (1, x), (0, x)] : Subst).lookup 0 = some x := rfl
  .clauseEx (fn := fnB f s t) (cl := clB s t) (σ := [(2, x), (1, x), (0, x)]) hfn (List.mem_singleton_self _)
    (sorted_x hx) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnB, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    exs_clB .var (fun t ht => nomatch ht)
    (holds_cast (post_holds ht h0 rfl rfl) (postVal_x x x x))
    (fun σ' ha hw => inst_all ht ((agree_x ha).trans h0) hw)

/-- **`f(x)` has no other result**, where t's value at x is x. -/
theorem alone (ht : TermIs d t x x) (hfn : d.lookupFn f = some (fnB f s t)) (hx : d.sortOf x = some s)
    {r : Option GroundTerm} (h : Eval d f [x] r) : r = some x := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clB s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnB] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hnone (clB s t) (List.mem_singleton_self _)) (not_fails hx)
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | clauseEx hfn' hmem hσ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨w1, h1, -⟩ := hσ 1 s rfl
    have h2 := (EvalTerm.var_inv hrhs).symm
    have e := post_inv ht (pat_x hmatch) h1 h2 hpost
    rw [postVal_same e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := pat_x hmatch
    have hi := hall _ (agree_set12 σ x x) (set12_sorted h0 hx hx)
    have e := inst_eq ht (set12_0 h0 x) (set12_1 σ x) (set12_2 σ x) (postVal_x x x x) hi
    cases e

end Shape

end ExClauseFixtures.InOrFx

namespace ExClauseFixtures.InOr

open GroundTerm ExClauseFixtures.InOrFx

definition_of defn from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def fX : Sym := 385

/-- The term f's binder is equated with, `notBool X`. -/
def tNot : Term := .app boolNot [.var 0]
/-- The term fx's binder is equated with, X. -/
def tX : Term := .var 0

/-- **The reading**: the text's functions are f and fx, neither `total`, each with the one clause
`[X:Bool, B:Bool, #Or0:Bool]`, `exs [1, 2]`, `rhs #Or0`, `post (#Or0 ∈ X) ∨ ((#Or0 ∈ B) ∧ (B = t))`,
t being `notBool X` for f and X for fx: the binder moved over the `\or`. -/
theorem read : c.fns = [fnB fF Srt.bool tNot, fnB fX Srt.bool tX] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName fX = "Lblfx" ∧ c.symName boolNot = "LblnotBool'Unds'" ∧
    c.sortName Srt.bool = "Bool" := by decide +kernel

/-- Bool is confined: `clausePlainEx` admits both clauses. -/
theorem plainEx : c.confined Srt.bool = true ∧ c.clausePlainEx (clB Srt.bool tNot) = true ∧
    c.clausePlainEx (clB Srt.bool tX) = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some (fnB fF Srt.bool tNot) := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupX : c.lookupFn fX = some (fnB fX Srt.bool tX) := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

section Terms

variable {d : Semantics}

theorem notHook : isHook boolNot = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation. -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

/-- `notBool X` where X is b: `!b`, and no other result. -/
theorem tNot_is (hc : d.isCtor boolNot = false) (b : Bool) : TermIs d tNot (bool b) (bool (!b)) where
  ev σ h0 := .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)
  inv σ r h0 h := by
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    have := hh [bool b] (by rw [h0]; rfl)
    rw [hookNot] at this
    exact (Option.some.inj this).symm

/-- X where X is x: x, and no other result. -/
theorem tX_is (x : GroundTerm) : TermIs d tX x x where
  ev _ h0 := h0 ▸ .var
  inv _ _ h0 h := (EvalTerm.var_inv h).trans h0

theorem not_ne (b : Bool) : bool (!b) ≠ bool b := by cases b <;> decide

end Terms

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some (fnB fF Srt.bool tNot) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupXH (H : HookParams) : (cH H).lookupFn fX = some (fnB fX Srt.bool tX) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupX
theorem tNot_isH (H : HookParams) (b : Bool) : TermIs (cH H) tNot (bool b) (bool (!b)) :=
  tNot_is (d := cH H) notCtor b

/-- **`fx(b) = b`, for every H.** -/
theorem fx_value (H : HookParams) (b : Bool) : Eval (cH H) fX [bool b] (some (bool b)) :=
  value (tX_is _) (lookupXH H) (rmS_sortOf_bool _ b)

/-- **`fx(b)` has no other result, for every H**: not the other value of Bool, and not none. -/
theorem fx_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fX [bool b] r) :
    r = some (bool b) :=
  alone (tX_is _) (lookupXH H) (rmS_sortOf_bool _ b) h

/-- **`fx(true) = true`, for every H.** -/
theorem fx_true (H : HookParams) : Eval (cH H) fX [bool true] (some (bool true)) := fx_value H true

/-- **`fx(true)` has no result but `true`, for every H.** -/
theorem fx_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fX [bool true] r) :
    r = some (bool true) := fx_alone H h

/-- **`f(b)` has no result, for every H and both values of Bool**: neither a value nor none. Its
instances at B, #Or0 := b and at B, #Or0 := notBool b give b and notBool b. -/
theorem f_no_result (H : HookParams) (b : Bool) (r : Option GroundTerm) : ¬ Eval (cH H) fF [bool b] r :=
  fun h => no_res (tNot_isH H b) (not_ne b) (rmS_sortOf_bool _ b) (rmS_sortOf_bool _ (!b)) (lookupFH H) h

/-- **The owed fact the package names for f's clause, `MatchIndependent`, is false, for every H.** -/
theorem f_not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) (clB Srt.bool tNot) :=
  not_mi (tNot_isH H true) (not_ne true) (rmS_sortOf_bool _ true) (rmS_sortOf_bool _ (!true)) (lookupFH H)

/-- **`FnHyp` is false, for every H**: f has no result at `true`. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [bool true] = some (fnB fF Srt.bool tNot).args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl
  obtain ⟨r, hr⟩ := hf.1 (fnB fF Srt.bool tNot)
    (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_cons_self ..) [bool true] hso
  exact f_no_result H true r hr

end ExClauseFixtures.InOr

/-- info: 'ExClauseFixtures.InOr.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.InOr.read
/-- info: 'ExClauseFixtures.InOr.fx_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOr.fx_value
/-- info: 'ExClauseFixtures.InOr.fx_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOr.fx_alone
/-- info: 'ExClauseFixtures.InOr.f_no_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOr.f_no_result
/-- info: 'ExClauseFixtures.InOr.f_not_matchIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOr.f_not_matchIndependent
/-- info: 'ExClauseFixtures.InOr.not_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.InOr.not_fnHyp
