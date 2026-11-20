/-
  The fixture e3-ml-eq-rhs-or (`rule h(X) => f(X) #Or g(X)` with `rule f(X) => X` and
  `rule g(X) => 0 -Int X`, none `total`, over Int): the clause the reader gives for h's equation and
  the results of `h`, for every hook interpretation. Run from the package root:
  `lake env lean -j1 test/ExClauseFxOr.lean`.

  The text is `f2-examples/e3-ml-eq-rhs-or.kompile.kore`; sentence numbers are `AxiomDecl.index`:
  204 is h's equation `h(X0) = (f(X) ∨ g(X)) ∧ \top` (with `X0 ∈ X`), 200 f's `f(X0) = X ∧ \top` and
  202 g's `g(X0) = (0 -Int X) ∧ \top` (`s204`, `s200`, `s202`).

  From the sentences: `h(x)` is the union of `f(x)` and `g(x)`. Where the two are the same element,
  or one is empty, the union is the element of the other; where both are empty it is empty; where
  they are two elements it is the two, and no one result is stated.

  The clause read for 204 is `clH` (`read`): `[X:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`,
  `post := #Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`.

  Two layers of statements.

  Over every semantics `d` that reads `h` with the one clause `clH` and `f`, `g` as functions
  (`Fun`: no constructor, hook, parameter or overloading symbol), at an argument x of Int where `f`
  has the one result rf and `g` the one result rg (`Only`):
  - `value_of`: rf and rg are each the value v (of Int) or none, and one of them is v: `h(x)` has
    the result v, by `Eval.clauseEx` at #Or0 := v, and no other result.
  - `none_of`: rf and rg are none: `h(x)` has the result none, by `Eval.exNone` (every instance has
    `post` false), and no other result; the clause applies at x (`not_fails`), so no rest is read.
  - `differ_of`: rf and rg are two values of Int: `h(x)` has no result, neither a value nor none
    (the instances at #Or0 := v and #Or0 := w give v and w).

  On `defn`, the definition the reader gives for the text, each for every H:
  - `f_res`, `g_res`: `f(n)` has the one result n and `g(n)` the one result `0 - n`. So the text has
    no argument of Int where `f` or `g` is undefined, and the two agree at 0 alone: `value_of` is
    used here at rf = rg only, and `none_of` at no argument of this text.
  - `h_zero`, `h_zero_alone`: `h(0)` has the result 0 and no other.
  - `h_differ`: at n ≠ 0, `h(n)` has no result.
  - `not_fnHyp`: `FnHyp` is false (h has no result at 1).

  `ExClauseFixtures.OrFx` holds the facts the proofs share with the other fixtures of an equation
  read as one clause with existential variables (a test file imports no test file, so each repeats
  them).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.OrFx

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

/-- A substitution giving the variable 0 a value of the sort is well sorted. -/
theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

/-- The predicate p has the truth value b under σ, and no other. -/
def Dec (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {n : Nat} {p q : Cond} {b b' : Bool} (hp : Dec d n σ p b) (hq : Dec d n σ q b') :
    Dec d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

/-- `f` is a function of d: no constructor, hook, parameter or overloading symbol, so an
application of it on defined arguments has `Eval`'s results. -/
def Fun (d : Semantics) (f : Sym) : Prop :=
  d.isCtor f = false ∧ isHook f = false ∧ d.isParam f = false ∧ d.isOvl f = false

/-- `f` has at `[x]` the result r and no other. -/
def Only (d : Semantics) (f : Sym) (x : GroundTerm) (r : Option GroundTerm) : Prop :=
  Eval d f [x] r ∧ ∀ r', Eval d f [x] r' → r' = r

/-- The application `f(X)` of a function has `f`'s results at the value σ gives X. -/
theorem call_of {f : Sym} (hf : Fun d f) {x : GroundTerm} (h0 : σ.lookup 0 = some x)
    {r : Option GroundTerm} (h : Eval d f [x] r) : EvalTerm d σ (.app f [.var 0]) r :=
  .call hf.1 hf.2.1 (rs := [σ.lookup 0]) (.cons .var .nil) (by rw [h0]; rfl) h hf.2.2.1

theorem call_inv {f : Sym} (hf : Fun d f) {x : GroundTerm} (h0 : σ.lookup 0 = some x)
    {r : Option GroundTerm} (h : EvalTerm d σ (.app f [.var 0]) r) : Eval d f [x] r := by
  have hrs : ∀ {rs}, EvalTerms d σ [.var 0] rs → rs = [some x] := fun hts => by
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    rw [h0]
  generalize ht : Term.app f [.var 0] = t at h
  cases h with
  | hook _ hk _ _ _ => cases ht; rw [hf.2.1] at hk; cases hk
  | ctor hc _ => cases ht; rw [hf.1] at hc; cases hc
  | param _ _ hp _ _ => cases ht; rw [hf.2.2.1] at hp; cases hp
  | call _ _ hts hvs he _ =>
    cases ht
    rw [hrs hts] at hvs
    cases hvs
    exact he
  | callUndef _ _ hts hvs _ => cases ht; rw [hrs hts] at hvs; cases hvs
  | ovl _ ho _ _ => cases ht; rw [hf.2.2.2] at ho; cases ho
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [hf.2.2.2] at ho; cases ho
  | _ => cases ht

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

end ExClauseFixtures.OrFx

namespace ExClauseFixtures.Or

open GroundTerm ExClauseFixtures.OrFx

definition_of defn from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or.kompile.kore" module "E3-ML-EQ-RHS-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def fG : Sym := 385
def fH : Sym := 386

/-- `f(X) => X`. -/
def clF : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }

/-- `g(X) => 0 -Int X`. -/
def clG : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intSub [.dv Srt.int (.int 0), .var 0],
    ens := none }

/-- `#Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`: the disjunction's variable (the variable 1) is an element of one
of the two alternatives. -/
def postH : Cond :=
  .or (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app fG [.var 0]))

/-- `h(X) => #Or0` with `exs = [#Or0]` and `post := postH`, both variables of Int. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postH }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clF] }
def fnG : Fn := { label := fG, args := [Srt.int], result := Srt.int, clauses := [clG] }
def fnH : Fn := { label := fH, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, none `total`, `h` with the one
clause `clH`. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName fG = "Lblg" ∧ c.symName fH = "Lblh" ∧
    c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ c.sortName Srt.int = "Int" := by decide +kernel

/-! ### The sentences the clauses are read from -/

section Sentences

open KoreAML

def sI : Kore.KSort := srt "Int"
def vX0 : Kore.Pattern := ev "X0" sI
def vX : Kore.Pattern := ev "VarX" sI

/-- The premise `\top ∧ (X0 ∈ X ∧ \top)` of each of the three equations. -/
def premP : Kore.Pattern :=
  .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in sI KoreAML.R vX0 vX, .top KoreAML.R]]

/-- The equation `l(X0) = rhs ∧ \top` under the premise. -/
def eqnP (l : String) (rhs : Kore.Pattern) : Kore.Pattern :=
  .implies KoreAML.R premP (.equals sI KoreAML.R (ap l [vX0]) (.and sI [rhs, .top sI]))

theorem s200 : U.ax200.ax.pattern = eqnP "Lblf" vX := by decide +kernel
theorem s202 : U.ax202.ax.pattern = eqnP "Lblg" (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vX]) := by
  decide +kernel
theorem s204 : U.ax204.ax.pattern = eqnP "Lblh" (.or sI [ap "Lblf" [vX], ap "Lblg" [vX]]) := by
  decide +kernel

end Sentences

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn fG = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn fH = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem kinds : (c.isCtor fF = false ∧ isHook fF = false ∧ c.isParam fF = false ∧ c.isOvl fF = false) ∧
    (c.isCtor fG = false ∧ isHook fG = false ∧ c.isParam fG = false ∧ c.isOvl fG = false) ∧
    c.isCtor intSub = false := by decide +kernel

/-- #Or0 is not of a confined sort; each alternative fixes it (`Cond.fixes`): `clausePlainEx`
admits the clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx clH = true := by decide +kernel

/-! ### The clauses in a semantics that reads them -/

section Clause

variable {d : Semantics} {σ : Subst}

/-- The truth value of `postH` where #Or0 has the value w, `f` the result rf and `g` the result rg
at X's value. -/
def postVal (w : GroundTerm) (rf rg : Option GroundTerm) : Bool :=
  sameResult (some w) rf || sameResult (some w) rg

theorem dec_mem {f : Sym} (hf : Fun d f) {n : Nat} {x w : GroundTerm} {r : Option GroundTerm}
    (ho : Only d f x r) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d n σ (.mem Srt.int (.var 1) (.app f [.var 0])) (sameResult (some w) r) := by
  refine ⟨holds_cast (Holds.mem .var (call_of hf h0 ho.1)) (by rw [h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := ho.2 _ (call_inv hf h0 h')
    rw [h1]; rfl

/-- **`post` is decided** where `f` and `g` each have one result at X's value. -/
theorem dec_post (hF : Fun d fF) (hG : Fun d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d 2 σ postH (postVal w rf rg) :=
  dec_or (dec_mem hF hf h0 h1) (dec_mem hG hg h0 h1)

/-- An instance whose `post` is true gives #Or0's value, and agrees with no other result. -/
theorem inst_true (hF : Fun d fF) (hG : Fun d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w)
    (hp : postVal w rf rg = true) : InstIs d σ clH (some w) ∧ ∀ r, InstIs d σ clH r → r = some w := by
  have hd := dec_post hF hG hf hg h0 h1
  refine ⟨.gives (h1 ▸ .var) (fun t ht => nomatch ht) (holds_cast hd.1 hp), fun r h => ?_⟩
  cases h with
  | fails _ hfl =>
    cases hfl with
    | ens ht _ _ => cases ht
    | post hq => have e := hd.2 _ hq; rw [hp] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- An instance whose `post` is false gives nothing: it agrees with every result. -/
theorem inst_false (hF : Fun d fF) (hG : Fun d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w)
    (hp : postVal w rf rg = false) (r : Option GroundTerm) : InstIs d σ clH r :=
  have hd := dec_post hF hG hf hg h0 h1
  .fails hd.1 (.post (holds_cast hd.1 hp))

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- σ with #Or0 := w is an instance of the clause at σ, well sorted where σ gives X a value of Int
and w is of Int. -/
theorem ext_sorted {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    (hw : d.sortOf w = some Srt.int) : d.WellSorted clH.vars ((1, w) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) hw

theorem ext_x {x : GroundTerm} (h0 : σ.lookup 0 = some x) (w : GroundTerm) :
    ((1, w) :: σ : Subst).lookup 0 = some x := (lkNe _ _ (by decide)).trans h0

/-- The value a match of the clause at `[x]` gives X is x. -/
theorem match_x {x : GroundTerm} (hm : PatVals d σ clH.pats [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

theorem only_clH (hfn : d.lookupFn fH = some fnH) {cl : Clause} {fn' : Fn}
    (h1 : d.lookupFn fH = some fn') (h2 : cl ∈ fn'.clauses) : cl = clH := by
  rw [hfn] at h1; cases h1; simpa [fnH] using h2

/-- **The clause applies at every argument of Int**: `h` has no rest there. -/
theorem not_fails_at {x : GroundTerm} (hx : d.sortOf x = some Srt.int) : ¬ Fails d [x] clH := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : d.WellSorted clH.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- A result of `h` at x agrees with every instance of the clause at X := x: it is not the rest,
and each of `Eval.clauseEx` and `Eval.exNone` asks it of every instance. -/
theorem res_insts (hfn : d.lookupFn fH = some fnH) {x : GroundTerm} (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Eval d fH [x] r) :
    ∀ w, d.sortOf w = some Srt.int → ∃ σ' : Subst, σ'.lookup 0 = some x ∧ σ'.lookup 1 = some w ∧
      InstIs d σ' clH r := by
  intro w hw
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ =>
    obtain rfl := only_clH hfn hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hnone clH (List.mem_singleton_self _)) (not_fails_at hx)
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ =>
    obtain rfl := only_clH hfn hfn' hmem; exact absurd hex (by decide)
  | @clauseEx _ _ _ _ σ _ hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := only_clH hfn hfn' hmem
    have h0 := match_x hmatch
    exact ⟨_, ext_x h0 w, lkSelf _ _ _, hall _ (agree_set1 σ w) (ext_sorted h0 hx hw)⟩
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := only_clH hfn hfn' hmem
    have h0 := match_x hmatch
    exact ⟨_, ext_x h0 w, lkSelf _ _ _, hall _ (agree_set1 σ w) (ext_sorted h0 hx hw)⟩

/-- **`h(x)` is v** where v, of Int, is the one value of #Or0 at which `post` is true. -/
theorem value_at (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH) {x v : GroundTerm}
    (hx : d.sortOf x = some Srt.int) (hv : d.sortOf v = some Srt.int) {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (hp : postVal v rf rg = true)
    (huniq : ∀ w, postVal w rf rg = true → w = v) : Eval d fH [x] (some v) :=
  have h0 : ([(1, v), (0, x)] : Subst).lookup 0 = some x := rfl
  have h1 : ([(1, v), (0, x)] : Subst).lookup 1 = some v := rfl
  .clauseEx (fn := fnH) (cl := clH) (σ := [(1, v), (0, x)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl hx rfl hv) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (dec_post hF hG hf hg h0 h1).1 hp)
    (fun σ' ha hw => by
      have h0' := (agree_x ha).trans h0
      obtain ⟨w, hw1, -⟩ := hw 1 Srt.int rfl
      cases hpw : postVal w rf rg with
      | true => obtain rfl := huniq w hpw; exact (inst_true hF hG hf hg h0' hw1 hpw).1
      | false => exact inst_false hF hG hf hg h0' hw1 hpw _)

/-- A result of `h` at x is v where `post` is true at #Or0 := v, of Int. -/
theorem res_eq (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH) {x v : GroundTerm}
    (hx : d.sortOf x = some Srt.int) (hv : d.sortOf v = some Srt.int) {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (hp : postVal v rf rg = true)
    {r : Option GroundTerm} (h : Eval d fH [x] r) : r = some v := by
  obtain ⟨σ', h0, h1, hi⟩ := res_insts hfn hx h v hv
  exact (inst_true hF hG hf hg h0 h1 hp).2 _ hi

/-- A value of `h` at x is a value of #Or0 at which `post` is true: `Eval.clauseEx` alone gives a
value. -/
theorem res_post (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH) {x v : GroundTerm}
    (hx : d.sortOf x = some Srt.int) {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h : Eval d fH [x] (some v)) : postVal v rf rg = true := by
  generalize hr : some v = r at h
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ =>
    obtain rfl := only_clH hfn hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hnone clH (List.mem_singleton_self _)) (not_fails_at hx)
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ =>
    obtain rfl := only_clH hfn hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := only_clH hfn hfn' hmem
    cases hr
    exact ((dec_post hF hG hf hg (match_x hmatch) (EvalTerm.var_inv hrhs).symm).2 _ hpost).symm
  | exNone _ _ _ _ _ _ _ _ _ _ => cases hr

/-- **`h(x)` is none** where `post` is true at no value of #Or0, by `Eval.exNone`. -/
theorem none_at (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH) {x : GroundTerm}
    (hx : d.sortOf x = some Srt.int) {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (hnone : ∀ w, postVal w rf rg = false) :
    Eval d fH [x] none :=
  have h0 : ([(0, x)] : Subst).lookup 0 = some x := rfl
  .exNone (fn := fnH) (cl := clH) (σ := [(0, x)]) hfn (List.mem_singleton_self _) (by decide)
    (fun i hi s hs => by
      have : i = 0 := by simp [Clause.univ, clH] at hi; omega
      subst this; cases hs; exact ⟨x, rfl, hx⟩)
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    ⟨(1, x) :: [(0, x)], agree_set1 _ _, ext_sorted h0 hx hx⟩
    (fun σ' ha hw => by
      have h0' := (agree_x ha).trans h0
      obtain ⟨w, hw1, -⟩ := hw 1 Srt.int rfl
      exact inst_false hF hG hf hg h0' hw1 (hnone w) _)

end Clause

/-! ### The results of `h` from those of `f` and `g`, over every semantics reading the clause -/

theorem postVal_left {v : GroundTerm} {rg : Option GroundTerm} : postVal v (some v) rg = true := by
  simp [postVal, sameResult_self]

theorem postVal_right {v : GroundTerm} {rf : Option GroundTerm} : postVal v rf (some v) = true := by
  simp [postVal, sameResult_self]

theorem sameResult_none (w : GroundTerm) : sameResult (some w) none = false := rfl

/-- **Where `f` and `g` agree or one is undefined, `h` has the value and no other result.** In a
semantics d reading `h` with the clause `clH`, at an argument x of Int where `f` has the one result
rf and `g` the one result rg, each the value v of Int or none and one of them v: `h(x)` is v. -/
theorem value_of (d : Semantics) (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH)
    {x v : GroundTerm} (hx : d.sortOf x = some Srt.int) (hv : d.sortOf v = some Srt.int)
    {rf rg : Option GroundTerm} (hf : Only d fF x rf) (hg : Only d fG x rg)
    (hrf : rf = some v ∨ rf = none) (hrg : rg = some v ∨ rg = none) (hone : rf = some v ∨ rg = some v) :
    Eval d fH [x] (some v) ∧ ∀ r, Eval d fH [x] r → r = some v := by
  have hp : postVal v rf rg = true := by
    rcases hone with rfl | rfl
    · exact postVal_left
    · exact postVal_right
  have huniq : ∀ w, postVal w rf rg = true → w = v := fun w hw => by
    simp only [postVal, Bool.or_eq_true] at hw
    rcases hw with hw | hw
    · rcases hrf with rfl | rfl
      · exact sameResult_some.mp hw
      · cases hw
    · rcases hrg with rfl | rfl
      · exact sameResult_some.mp hw
      · cases hw
  exact ⟨value_at hF hG hfn hx hv hf hg hp huniq, fun r h => res_eq hF hG hfn hx hv hf hg hp h⟩

/-- **Where neither `f` nor `g` is defined, `h` has the result none and no other**, by
`Eval.exNone`: every instance of the clause has `post` false. -/
theorem none_of (d : Semantics) (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH)
    {x : GroundTerm} (hx : d.sortOf x = some Srt.int) (hf : Only d fF x none) (hg : Only d fG x none) :
    Eval d fH [x] none ∧ ∀ r, Eval d fH [x] r → r = none := by
  have hnone : ∀ w, postVal w none none = false := fun _ => rfl
  refine ⟨none_at hF hG hfn hx hf hg hnone, fun r h => ?_⟩
  cases r with
  | none => rfl
  | some v => have e := res_post hF hG hfn hx hf hg h; rw [hnone] at e; cases e

/-- **The clause applies at every argument of Int of a semantics reading it**: a result of `h`
there is the clause's, never the rest (`Eval.rest` asks that every clause fail). -/
theorem not_fails (d : Semantics) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) : ¬ Fails d [x] clH :=
  not_fails_at hx

/-- **Where `f` and `g` differ, `h` has no result**, neither a value nor none: the instances at
#Or0 := v and #Or0 := w give v and w. -/
theorem differ_of (d : Semantics) (hF : Fun d fF) (hG : Fun d fG) (hfn : d.lookupFn fH = some fnH)
    {x v w : GroundTerm} (hx : d.sortOf x = some Srt.int) (hv : d.sortOf v = some Srt.int)
    (hw : d.sortOf w = some Srt.int) (hf : Only d fF x (some v)) (hg : Only d fG x (some w)) (hne : v ≠ w)
    (r : Option GroundTerm) : ¬ Eval d fH [x] r := by
  intro h
  have e1 := res_eq hF hG hfn hx hv hf hg postVal_left h
  have e2 := res_eq hF hG hfn hx hw hf hg postVal_right h
  rw [e1] at e2
  exact hne (Option.some.inj e2)

/-! ### `f` and `g` in a semantics that reads their clauses -/

section FG

variable {d : Semantics}

/-- **`f(x)` is x and nothing else**, at an argument of Int. -/
theorem f_only (hfn : d.lookupFn fF = some fnF) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) :
    Only d fF x (some x) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnF] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clF.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  have hs : d.WellSorted clF.vars [(0, x)] := sorted1 rfl hx
  refine ⟨.clause (fn := fnF) (cl := clF) (σ := [(0, x)]) hfn (List.mem_singleton_self _) hs
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    rw [EvalTerm.var_inv hrhs, hx0 hmatch]
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

theorem subHook : isHook intSub = true := by decide +kernel

/-- `0 -Int n`, under every interpretation: the hook's value on Int values. -/
theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value rfl

theorem evalSub (hc : d.isCtor intSub = false) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ clG.rhs (some (int (0 - n))) :=
  .hook hc subHook (rs := [some (int 0), σ.lookup 0]) (.cons .dv (.cons .var .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookSub n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalSub_inv (hc : d.isCtor intSub = false) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n))
    {r : Option GroundTerm} (h : EvalTerm d σ clG.rhs r) : r = some (int (0 - n)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc subHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain ⟨r1, rs'', rfl, h2, hs'⟩ := EvalTerms.cons_inv hs
  obtain rfl := EvalTerms.nil_inv hs'
  obtain rfl := EvalTerm.dv_inv h1
  obtain rfl := EvalTerm.var_inv h2
  have := hh [int 0, int n] (by rw [h0]; rfl)
  rw [hookSub] at this
  exact (Option.some.inj this).symm

/-- **`g(n)` is `0 - n` and nothing else.** -/
theorem g_only (hc : d.isCtor intSub = false) (hfn : d.lookupFn fG = some fnG) (n : Int) :
    Only d fG (int n) (some (int (0 - n))) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fG = some fn' → cl ∈ fn'.clauses → cl = clG := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnG] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clG.pats [int n] → σ.lookup 0 = some (int n) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  have hs : d.WellSorted clG.vars [(0, int n)] := sorted1 rfl (rmS_sortOf_int d n)
  refine ⟨.clause (fn := fnG) (cl := clG) (σ := [(0, int n)]) hfn (List.mem_singleton_self _) hs
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evalSub hc rfl) (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    exact evalSub_inv hc (hx0 hmatch) hrhs
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clG (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

end FG

/-! ### The expectations on the text, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some fnF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupGH (H : HookParams) : (cH H).lookupFn fG = some fnG := by
  rw [Semantics.lookupFn_withHooks]; exact lookupG
theorem lookupHH (H : HookParams) : (cH H).lookupFn fH = some fnH := by
  rw [Semantics.lookupFn_withHooks]; exact lookupH
theorem funF (H : HookParams) : Fun (cH H) fF := kinds.1
theorem funG (H : HookParams) : Fun (cH H) fG := kinds.2.1
theorem subNotCtor (H : HookParams) : (cH H).isCtor intSub = false := kinds.2.2

/-- **`f(n)` is n and nothing else, for every H.** -/
theorem f_res (H : HookParams) (n : Int) :
    Eval (cH H) fF [int n] (some (int n)) ∧ ∀ r, Eval (cH H) fF [int n] r → r = some (int n) :=
  f_only (lookupFH H) (rmS_sortOf_int _ n)

/-- **`g(n)` is `0 - n` and nothing else, for every H.** -/
theorem g_res (H : HookParams) (n : Int) :
    Eval (cH H) fG [int n] (some (int (0 - n))) ∧ ∀ r, Eval (cH H) fG [int n] r → r = some (int (0 - n)) :=
  g_only (subNotCtor H) (lookupGH H) n

/-- **`h(0)` is 0, for every H**: `f(0)` and `g(0)` are both 0. -/
theorem h_zero (H : HookParams) : Eval (cH H) fH [int 0] (some (int 0)) :=
  (value_of (cH H) (funF H) (funG H) (lookupHH H) (rmS_sortOf_int _ 0) (rmS_sortOf_int _ 0)
    (f_res H 0) (g_res H 0) (.inl rfl) (.inl rfl) (.inl rfl)).1

/-- **`h(0)` has no result but 0, for every H.** -/
theorem h_zero_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fH [int 0] r) :
    r = some (int 0) :=
  (value_of (cH H) (funF H) (funG H) (lookupHH H) (rmS_sortOf_int _ 0) (rmS_sortOf_int _ 0)
    (f_res H 0) (g_res H 0) (.inl rfl) (.inl rfl) (.inl rfl)).2 r h

/-- **At n ≠ 0, `h(n)` has no result, for every H**: `f(n)` is n and `g(n)` is `0 - n`. -/
theorem h_differ (H : HookParams) {n : Int} (hn : n ≠ 0) (r : Option GroundTerm) :
    ¬ Eval (cH H) fH [int n] r :=
  differ_of (cH H) (funF H) (funG H) (lookupHH H) (rmS_sortOf_int _ n) (rmS_sortOf_int _ n)
    (rmS_sortOf_int _ (0 - n)) (f_res H n) (g_res H n)
    (fun e => hn (by have e' : n = 0 - n := by simpa [KCore.int] using e
                     omega)) r

/-- **`FnHyp` is false, for every H**: h has no result at 1. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [int 1] = some fnH.args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl
  obtain ⟨r, hr⟩ := hf.1 fnH (by rw [show (cH H).fns = c.fns from rfl, read]; simp) [int 1] hso
  exact h_differ H (by decide) r hr

end ExClauseFixtures.Or

/-- info: 'ExClauseFixtures.Or.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.Or.read
/-- info: 'ExClauseFixtures.Or.s204' depends on axioms: [propext] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.s204
/-- info: 'ExClauseFixtures.Or.value_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.value_of
/-- info: 'ExClauseFixtures.Or.none_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.none_of
/-- info: 'ExClauseFixtures.Or.not_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.not_fails
/-- info: 'ExClauseFixtures.Or.differ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.differ_of
/-- info: 'ExClauseFixtures.Or.f_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.f_res
/-- info: 'ExClauseFixtures.Or.g_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.g_res
/-- info: 'ExClauseFixtures.Or.h_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.h_zero
/-- info: 'ExClauseFixtures.Or.h_zero_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.h_zero_alone
/-- info: 'ExClauseFixtures.Or.h_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.h_differ
/-- info: 'ExClauseFixtures.Or.not_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Or.not_fnHyp
