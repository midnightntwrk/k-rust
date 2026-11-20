/-
  The fixture e3-eq-exists-ml-supersort (a binder below the equation's sort, and a binder equated with a
  term of a larger sort): the clauses the reader gives for its text and the results of `f` and `h`, for
  every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxSuper.lean`.

  `syntax KItem ::= f(Int) [function]`, `rule f(X) => #Exists B:Bool. (B #And {B #Equals (X >Int 0)})`
  (axiom 200): the binder's sort Bool is below the equation's sort KItem. And
  `syntax Int ::= h(KItem) [function]`, `rule h(K) => #Exists Z:Int. (Z #And {Z #Equals K})` (axiom
  203): the binder is equated with a term of a larger sort, which kompile writes as
  `inj{Int,KItem}(Z) = K`.

  From the sentences: `f(x)` is the set of `inj{Bool,KItem}(b)` for the elements b of Bool with
  `b = (x >Int 0)`, so `f(x) = inj{Bool,KItem}(x >Int 0)`. `h(k)` is the set of the elements z of
  Int with `inj{Int,KItem}(z) = k`: `{v}` where k is `inj{Int,KItem}(v)` (the injection is
  injective), and empty where k is no injection of an element of Int.

  The statements are on `defn`, the definition the reader gives for the text
  (`f2-examples/e3-eq-exists-ml-supersort.kompile.kore`), each for every hook interpretation H:
  - The clauses read are `clF` and `clH` (`read`): for f `[X:Int, B:Bool]`, `exs [1]`,
    `rhs inj{Bool,KItem}(B)`, `post B = (X >Int 0)`; for h `[K:KItem, Z:Int]`, `exs [1]`, `rhs Z`,
    `post inj{Int,KItem}(Z) = K`. Neither function has another clause or is `total`.
  - `clausePlainEx` admits both (`plainEx`): B is of the confined sort Bool; Z is of Int, which is
    not confined, and `post` fixes it, by the equation of its injection with K (`fixedExs` is `[1]`).
  - `f_value`, `f_alone`: `f(n)` has the one result `inj{Bool,KItem}(n >Int 0)`; `f_1`, `f_1_alone`
    at 1.
  - `h_int`, `h_int_alone`: `h(inj{Int,KItem}(n))` has the one result n; `h_3`, `h_3_alone` at 3.
  - `h_bool`, `h_bool_alone`: `h(inj{Bool,KItem}(b))` has the result none, by `Eval.exNone` (every
    instance has `post` false), and no other; `h_true`, `h_true_alone` at `true`.

  `ExClauseFixtures.CeFx` holds the facts the proofs share with the other fixtures of an equation
  read as one clause with existential variables (test/ExClauseFxBool.lean, test/ExClauseFxCtor.lean,
  test/ExClauseFxSuper.lean; a test file imports no test file, so each repeats them).
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

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

end ExClauseFixtures.CeFx

namespace ExClauseFixtures.ExSuper

open GroundTerm ExClauseFixtures.CeFx

definition_of defn from "f2-examples/e3-eq-exists-ml-supersort.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def hS : Sym := 385

/-- `f(X) => inj{Bool,KItem}(B)` with `exs = [B]` and `post := B = (X >Int 0)`, X of Int, B of Bool. -/
def clF : Clause :=
  { vars := [Srt.int, Srt.bool], pats := [.var 0], req := none, rhs := .inj Srt.bool Srt.kitem (.var 1),
    ens := none, exs := [1],
    post := .equals Srt.bool (.var 1) (.app intGt [.var 0, .dv Srt.int (.int 0)]) }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.kitem, clauses := [clF] }

/-- `h(K) => Z` with `exs = [Z]` and `post := inj{Int,KItem}(Z) = K`, K of KItem, Z of Int. -/
def clH : Clause :=
  { vars := [Srt.kitem, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.kitem (.inj Srt.int Srt.kitem (.var 1)) (.var 0) }

def fnH : Fn := { label := hS, args := [Srt.kitem], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f` and `h`, each with its one clause. -/
theorem read : c.fns = [fnF, fnH] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName hS = "Lblh" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" ∧
    c.sortName Srt.int = "Int" ∧ c.sortName Srt.bool = "Bool" ∧ c.sortName Srt.kitem = "KItem" := by
  decide +kernel

/-- **Neither clause is refused**: B is of the confined sort Bool; Z is of Int, which is not
confined, and is fixed by `post`, the equation of its injection with K. -/
theorem plainEx : c.clausePlainEx clF = true ∧ c.confined Srt.bool = true ∧
    c.clausePlainEx clH = true ∧ c.confined Srt.int = false ∧ clH.fixedExs c.confined c.hasValue = [1] := by
  decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn hS = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem gtCtor : c.isCtor intGt = false := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel
theorem subs : c.subsorts.contains (Srt.int, Srt.kitem) = true ∧ c.subsorts.contains (Srt.bool, Srt.kitem) = true := by
  decide +kernel

/-- What a semantics must give for the two clauses to be read in it: `>Int` the hook, the values of
Int and Bool their literals, and Int and Bool below KItem. -/
structure Reads (d : Semantics) : Prop where
  gt : d.isCtor intGt = false
  shapes : d.shapesOK = true
  subInt : d.subsorts.contains (Srt.int, Srt.kitem) = true
  subBool : d.subsorts.contains (Srt.bool, Srt.kitem) = true

theorem subsorts_wh (d : Semantics) (H : HookParams) : (d.withHooks H).subsorts = d.subsorts := rfl

/-- `inj{Int,KItem}(n)`. -/
def injI (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (int n)
/-- `inj{Bool,KItem}(b)`. -/
def injB (b : Bool) : GroundTerm := .inj Srt.bool Srt.kitem (bool b)

section Clauses

variable {d : Semantics} {σ : Subst}

theorem injI_sort (hd : Reads d) (n : Int) : d.sortOf (injI n) = some Srt.kitem :=
  sortOf_inj_of hd.subInt rfl (sortOf_int n)

theorem injB_sort (hd : Reads d) (b : Bool) : d.sortOf (injB b) = some Srt.kitem :=
  sortOf_inj_of hd.subBool rfl (rmS_sortOf_bool d b)

/-! ### f -/

theorem gtHook : isHook intGt = true := by decide +kernel

/-- `>Int` at two values of Int, under every interpretation (domains.md 1331, `hook(INT.gt)`: the comparison of the two integers). -/
theorem hookGt (n : Int) : d.hookRes intGt [int n, int 0] = some (some (bool (decide (n > 0)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl)

theorem evalGt (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool (decide (n > 0)))) :=
  .hook hd.gt gtHook (rs := [σ.lookup 0, some (int 0)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookGt n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalGt_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) r) : r = some (bool (decide (n > 0))) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.gt gtHook h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [int n, int 0] (by rw [h0]; rfl)
  rw [hookGt] at this
  exact (Option.some.inj this).symm

/-- The clause's `post` at a match giving X the value n: whether B's value is `n >Int 0`. -/
theorem postF_holds (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    Holds d 2 σ clF.post (sameResult (σ.lookup 1) (some (bool (decide (n > 0))))) :=
  Holds.equals .var (evalGt hd h0)

theorem postF_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {t : Bool}
    (h : Holds d 2 σ clF.post t) : t = sameResult (σ.lookup 1) (some (bool (decide (n > 0)))) := by
  cases h with
  | equals h1 h2 =>
    obtain rfl := EvalTerm.var_inv h1
    obtain rfl := evalGt_inv hd h0 h2
    rfl

/-- The clause's right-hand side where B has the value b. -/
theorem rhsF {b : Bool} (h1 : σ.lookup 1 = some (bool b)) : EvalTerm d σ clF.rhs (some (injB b)) := by
  have h : EvalTerm d σ clF.rhs _ := .inj (a := Srt.bool) (b := Srt.kitem) (.var (i := 1))
  rw [h1] at h
  exact h

theorem rhsF_inv {b : Bool} (h1 : σ.lookup 1 = some (bool b)) {r : Option GroundTerm}
    (h : EvalTerm d σ clF.rhs r) : r = some (injB b) := by
  obtain ⟨r', h', rfl⟩ := EvalTerm.inj_inv h
  obtain rfl := EvalTerm.var_inv h'
  rw [h1]; rfl

/-- **Every instance of f's clause is decided and gives `inj{Bool,KItem}(n >Int 0)` or nothing.** -/
theorem instF_all (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n))
    (hw : d.WellSorted clF.vars σ) : InstIs d σ clF (some (injB (decide (n > 0)))) := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.bool rfl
  cases hb : sameResult (some w) (some (bool (decide (n > 0)))) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (rhsF hw1) (fun t ht => nomatch ht) (holds_cast (postF_holds hd h0) (by rw [hw1, hb]))
  | false => exact .fails (postF_holds hd h0) (.post (holds_cast (postF_holds hd h0) (by rw [hw1, hb])))

theorem instF_not_none (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n))
    (h1 : σ.lookup 1 = some (bool (decide (n > 0)))) : ¬ InstIs d σ clF none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := postF_inv hd h0 hp
      rw [h1, sameResult_self] at e
      cases e
    | rhs h => cases rhsF_inv h1 h

theorem agreeF_x {σ' : Subst} (h : AgreeOff clF.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

/-- **`f(n)` is `inj{Bool,KItem}(n >Int 0)`**, by `Eval.clauseEx` at B := `n >Int 0`. -/
theorem valueF (hd : Reads d) (hfn : d.lookupFn fF = some fnF) (n : Int) :
    Eval d fF [int n] (some (injB (decide (n > 0)))) :=
  have h0 : ([(1, bool (decide (n > 0))), (0, int n)] : Subst).lookup 0 = some (int n) := rfl
  .clauseEx (fn := fnF) (cl := clF) (σ := [(1, bool (decide (n > 0))), (0, int n)]) hfn
    (List.mem_singleton_self _)
    (sorted2 rfl (sortOf_int n) rfl (rmS_sortOf_bool d _)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) (rhsF rfl) (fun t ht => nomatch ht)
    (holds_cast (postF_holds hd h0) (sameResult_self _))
    (fun σ' ha hw => instF_all hd ((agreeF_x ha).trans h0) hw)

/-- **`f(n)` has no other result.** -/
theorem aloneF (hd : Reads d) (hfn : d.lookupFn fF = some fnF) {n : Int}
    {r : Option GroundTerm} (h : Eval d fF [int n] r) : r = some (injB (decide (n > 0))) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnF] using h2
  have hx : ∀ {σ : Subst}, PatVals d σ clF.pats [int n] → σ.lookup 0 = some (int n) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clF.vars [(1, bool true), (0, int n)] :=
        sorted2 rfl (sortOf_int n) rfl (rmS_sortOf_bool d true)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have e := postF_inv hd (hx hmatch) hpost
    exact rhsF_inv (sameResult_eq_some e.symm) hrhs
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx hmatch
    exact absurd (hall _ (agree_set1 σ _)
        (sorted2 ((lkNe _ _ (by decide)).trans h0) (sortOf_int n) (lkSelf _ _ _) (rmS_sortOf_bool d _)))
      (instF_not_none hd ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-! ### h -/

/-- The clause's `post`: whether the injection of Z's value is K's value. -/
theorem postH_holds {i : Int} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some (int i)) :
    Holds d 2 σ clH.post (sameResult (some (injI i)) (some x)) := by
  have h : Holds d 2 σ clH.post _ :=
    Holds.equals (.inj (a := Srt.int) (b := Srt.kitem) (.var (i := 1))) (.var (i := 0))
  rw [h0, h1] at h
  exact h

theorem postH_inv {i : Int} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some (int i))
    {t : Bool} (h : Holds d 2 σ clH.post t) : t = sameResult (some (injI i)) (some x) := by
  cases h with
  | equals hl hr =>
    obtain ⟨r', h', rfl⟩ := EvalTerm.inj_inv hl
    obtain rfl := EvalTerm.var_inv h'
    obtain rfl := EvalTerm.var_inv hr
    rw [h0, h1]; rfl

theorem injI_inj {i n : Int} : sameResult (some (injI i)) (some (injI n)) = decide (i = n) := by
  by_cases h : i = n
  · subst h; simp [sameResult_self]
  · have : sameResult (some (injI i)) (some (injI n)) = false :=
      Bool.eq_false_iff.mpr fun e => h (by simpa [injI, KCore.int] using sameResult_some.mp e)
    simp [this, h]

theorem injI_ne_injB (i : Int) (b : Bool) : sameResult (some (injI i)) (some (injB b)) = false :=
  Bool.eq_false_iff.mpr fun e => by
    have := sameResult_some.mp e
    simp [injI, injB] at this

/-- Z's value in a well-sorted instance is a literal of Int. -/
theorem zH (hd : Reads d) (hw : d.WellSorted clH.vars σ) : ∃ i, σ.lookup 1 = some (int i) := by
  obtain ⟨w, hw1, hws⟩ := hw 1 Srt.int rfl
  obtain ⟨i, rfl⟩ := shape_int hd.shapes hws
  exact ⟨i, hw1⟩

theorem agreeH_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

/-- σ with Z := i is an instance of the clause at σ, well sorted where σ gives K a value of KItem. -/
theorem extH_sorted {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.kitem) (i : Int) :
    d.WellSorted clH.vars ((1, int i) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) (sortOf_int i)

/-- **Every instance of h's clause at K := `inj{Int,KItem}(n)` is decided and gives n or
nothing.** -/
theorem instH_all (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (injI n))
    (hw : d.WellSorted clH.vars σ) : InstIs d σ clH (some (int n)) := by
  obtain ⟨i, h1⟩ := zH hd hw
  by_cases hin : i = n
  · subst hin
    exact .gives (h1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (postH_holds h0 h1) (sameResult_self _))
  · exact .fails (postH_holds h0 h1)
      (.post (holds_cast (postH_holds h0 h1) (by rw [injI_inj]; simpa using hin)))

theorem instH_not_none {n : Int} (h0 : σ.lookup 0 = some (injI n))
    (h1 : σ.lookup 1 = some (int n)) : ¬ InstIs d σ clH none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := postH_inv h0 h1 hp
      rw [sameResult_self] at e
      cases e
    | rhs h => have := EvalTerm.var_inv h; rw [h1] at this; cases this

/-- **`h(inj{Int,KItem}(n))` is n**, by `Eval.clauseEx` at Z := n. -/
theorem valueH (hd : Reads d) (hfn : d.lookupFn hS = some fnH) (n : Int) :
    Eval d hS [injI n] (some (int n)) :=
  have h0 : ([(1, int n), (0, injI n)] : Subst).lookup 0 = some (injI n) := rfl
  .clauseEx (fn := fnH) (cl := clH) (σ := [(1, int n), (0, injI n)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl (injI_sort hd n) rfl (sortOf_int n)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (postH_holds h0 rfl) (sameResult_self _))
    (fun σ' ha hw => instH_all hd ((agreeH_x ha).trans h0) hw)

/-- The results of `h` at a value x of KItem, by the constructor of `Eval`: `Eval.clauseEx` at a
well-sorted match whose `post` is true, or `Eval.exNone` with every instance giving nothing. -/
theorem casesH (hd : Reads d) (hfn : d.lookupFn hS = some fnH) {x : GroundTerm}
    (hxs : d.sortOf x = some Srt.kitem) {r : Option GroundTerm} (h : Eval d hS [x] r) :
    (∃ i, sameResult (some (injI i)) (some x) = true ∧ r = some (int i)) ∨
    (r = none ∧ ∃ σ : Subst, σ.lookup 0 = some x ∧
      ∀ σ', AgreeOff clH.exsFree σ σ' → d.WellSorted clH.vars σ' → InstIs d σ' clH none) := by
  have hcl : ∀ {cl fn'}, d.lookupFn hS = some fn' → cl ∈ fn'.clauses → cl = clH := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnH] using h2
  have hx : ∀ {σ : Subst}, PatVals d σ clH.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clH (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clH.vars [(1, int 0), (0, x)] := sorted2 rfl hxs rfl (sortOf_int 0)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem hσ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨i, h1⟩ := zH hd hσ
    have e := postH_inv (hx hmatch) h1 hpost
    have hv := EvalTerm.var_inv hrhs
    rw [h1] at hv
    exact .inl ⟨i, e.symm, hv⟩
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact .inr ⟨rfl, σ, hx hmatch, hall⟩

/-- **`h(inj{Int,KItem}(n))` has no other result.** -/
theorem aloneH (hd : Reads d) (hfn : d.lookupFn hS = some fnH) {n : Int}
    {r : Option GroundTerm} (h : Eval d hS [injI n] r) : r = some (int n) := by
  rcases casesH hd hfn (injI_sort hd n) h with ⟨i, e, rfl⟩ | ⟨-, σ, h0, hall⟩
  · rw [injI_inj] at e
    rw [of_decide_eq_true e]
  · exact absurd (hall _ (agree_set1 σ _) (extH_sorted h0 (injI_sort hd n) n))
      (instH_not_none ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-- **`h(inj{Bool,KItem}(b))` has the result none**, by `Eval.exNone`: every instance, at a value
of Int for Z, has `post` false, the injection of a value of Int being no injection of a value of
Bool. -/
theorem noneH (hd : Reads d) (hfn : d.lookupFn hS = some fnH) (b : Bool) : Eval d hS [injB b] none :=
  have h0 : ([(0, injB b)] : Subst).lookup 0 = some (injB b) := rfl
  .exNone (fn := fnH) (cl := clH) (σ := [(0, injB b)]) hfn (List.mem_singleton_self _) (by decide)
    (fun i hi s hs => by
      have : i = 0 := by simp [Clause.univ, clH] at hi; omega
      subst this; cases hs; exact ⟨_, rfl, injB_sort hd b⟩)
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    ⟨_, agree_set1 _ (int 0), extH_sorted h0 (injB_sort hd b) 0⟩
    (fun σ' ha hw => by
      obtain ⟨i, h1⟩ := zH hd hw
      have h0' := (agreeH_x ha).trans h0
      exact .fails (postH_holds h0' h1) (.post (holds_cast (postH_holds h0' h1) (injI_ne_injB i b))))

/-- **`h(inj{Bool,KItem}(b))` has no other result.** -/
theorem noneH_alone (hd : Reads d) (hfn : d.lookupFn hS = some fnH) {b : Bool}
    {r : Option GroundTerm} (h : Eval d hS [injB b] r) : r = none := by
  rcases casesH hd hfn (injB_sort hd b) h with ⟨i, e, -⟩ | ⟨rfl, -⟩
  · rw [injI_ne_injB] at e; cases e
  · rfl

end Clauses

/-! ### The expectations, for every H -/

/-- The text's semantics reads the two clauses, under every H. -/
theorem readsH (H : HookParams) : Reads (cH H) where
  gt := (isCtor_wh c H _).trans gtCtor
  shapes := (shapesOK_wh c H).trans shapes
  subInt := (congrArg (·.contains (Srt.int, Srt.kitem)) (subsorts_wh c H)).trans subs.1
  subBool := (congrArg (·.contains (Srt.bool, Srt.kitem)) (subsorts_wh c H)).trans subs.2

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some fnF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupHH (H : HookParams) : (cH H).lookupFn hS = some fnH := by
  rw [Semantics.lookupFn_withHooks]; exact lookupH

/-- **`f(n) = inj{Bool,KItem}(n >Int 0)`, for every H.** -/
theorem f_value (H : HookParams) (n : Int) : Eval (cH H) fF [int n] (some (injB (decide (n > 0)))) :=
  valueF (readsH H) (lookupFH H) n

/-- **`f(n)` has no other result, for every H.** -/
theorem f_alone (H : HookParams) {n : Int} {r : Option GroundTerm} (h : Eval (cH H) fF [int n] r) :
    r = some (injB (decide (n > 0))) := aloneF (readsH H) (lookupFH H) h

/-- **`f(1) = inj{Bool,KItem}(true)`, for every H.** -/
theorem f_1 (H : HookParams) : Eval (cH H) fF [int 1] (some (.inj Srt.bool Srt.kitem (bool true))) := f_value H 1

/-- **`f(1)` has no result but `inj{Bool,KItem}(true)`, for every H.** -/
theorem f_1_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fF [int 1] r) :
    r = some (.inj Srt.bool Srt.kitem (bool true)) := f_alone H h

/-- **`h(inj{Int,KItem}(n)) = n`, for every H.** -/
theorem h_int (H : HookParams) (n : Int) : Eval (cH H) hS [injI n] (some (int n)) :=
  valueH (readsH H) (lookupHH H) n

/-- **`h(inj{Int,KItem}(n))` has no other result, for every H.** -/
theorem h_int_alone (H : HookParams) {n : Int} {r : Option GroundTerm} (h : Eval (cH H) hS [injI n] r) :
    r = some (int n) := aloneH (readsH H) (lookupHH H) h

/-- **`h(inj{Int,KItem}(3)) = 3`, for every H.** -/
theorem h_3 (H : HookParams) : Eval (cH H) hS [.inj Srt.int Srt.kitem (int 3)] (some (int 3)) := h_int H 3

/-- **`h(inj{Int,KItem}(3))` has no result but 3, for every H.** -/
theorem h_3_alone (H : HookParams) {r : Option GroundTerm}
    (h : Eval (cH H) hS [.inj Srt.int Srt.kitem (int 3)] r) : r = some (int 3) := h_int_alone H (n := 3) h

/-- **`h(inj{Bool,KItem}(b))` has the result none, for every H.** -/
theorem h_bool (H : HookParams) (b : Bool) : Eval (cH H) hS [injB b] none := noneH (readsH H) (lookupHH H) b

/-- **`h(inj{Bool,KItem}(b))` has no other result, for every H.** -/
theorem h_bool_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) hS [injB b] r) :
    r = none := noneH_alone (readsH H) (lookupHH H) h

/-- **`h(inj{Bool,KItem}(true))` has the result none, for every H.** -/
theorem h_true (H : HookParams) : Eval (cH H) hS [.inj Srt.bool Srt.kitem (bool true)] none := h_bool H true

/-- **`h(inj{Bool,KItem}(true))` has no result but none, for every H.** -/
theorem h_true_alone (H : HookParams) {r : Option GroundTerm}
    (h : Eval (cH H) hS [.inj Srt.bool Srt.kitem (bool true)] r) : r = none := h_bool_alone H (b := true) h

end ExClauseFixtures.ExSuper

/-- info: 'ExClauseFixtures.ExSuper.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.read
/-- info: 'ExClauseFixtures.ExSuper.plainEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.plainEx
/-- info: 'ExClauseFixtures.ExSuper.f_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.f_1
/-- info: 'ExClauseFixtures.ExSuper.f_1_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.f_1_alone
/-- info: 'ExClauseFixtures.ExSuper.h_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.h_3
/-- info: 'ExClauseFixtures.ExSuper.h_3_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.h_3_alone
/-- info: 'ExClauseFixtures.ExSuper.h_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.h_true
/-- info: 'ExClauseFixtures.ExSuper.h_true_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExSuper.h_true_alone
