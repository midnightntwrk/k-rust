/-
  The conjunct of `confinedAt` on a generator that overloads a function ("each of whose generators
  … is no overloading symbol that overloads a function"): no witness found in the no-model form.
  Run from the package root: `lake env lean -j1 test/WitStage4.lean`.

  The conjunct is no leaf of `coreOK`: `confinedAt` is read by `rulesPlain` and `clausesPlain`
  (through `confined`, at an open variable of a rule or a clause, and in `clausePlainEx` and
  `needsWitness`), so dropping it admits more rules and clauses. `confinedAtV` below is
  `confinedAt` without it, and `rulesPlainV` is `rulesPlain` reading `confinedAtV`.

  `c fs`: sorts A, B, S, B < A, the constructor `b : → B`, the function `fB : B → S` without a
  clause (not total), the overloading symbol `fS : A → S` overloading `fs`, and the rule
  `<k> x </k> => <k> y </k>` whose right side binds `?H : S` by `\exists` and has the predicate
  `⌈?H⌉`. `?H` is held by nothing (it is in no term of the rule), so `rulesPlain` asks S confined.
  Kernel-checked:
  - `meets_others`: `c [fB]` meets every leaf of `coreOK` but `rulesPlain` (each a decision of
    its own), and `FnHyp` (`fB` has no clause: its value is its rest, ⊥, everywhere);
  - `not_rulesPlain`, `not_coreOK`: `rulesPlain` fails, so `coreOK` does;
  - `confined_S`: S is not confined, by this conjunct alone: its one generator `fS` overloads
    `fB`, while S is confined for `confinedAtV`, and with `fS` overloading nothing (`c []`);
  - `rulesPlainV_true`: `rulesPlain` holds of `c [fB]` once the conjunct is dropped, so `c [fB]`
    is the semantics a `coreOK` without the conjunct would admit;
  - `c0_coreOK`: `c []` meets `coreOK`.
  Argued, not kernel-checked: `Γ (c [fB])` has a model. B's elements are b's (no-junk of B), A's
  the injection of b's (no-junk of A), and S's elements are those of `fS` applied to A's
  (no-junk of S). The overload equation gives `fS(inj b) = inj(fB(b))` and `ΓFallback` gives
  `fB(b) = ⊥` (`fB` has no clause), so S is empty in every model, and S has no value: `fS(inj b)`
  is covered by `fB` and so no value (`sortOf` reads a covered application as none). The rule's
  axiom then makes no step from `x` (no element for `?H`), and `Step` makes none (no value for
  `?H`). The value model of `c [fB]` without the rule, read with S empty, is one.

  Why no witness was found. The conjunct is read where `confinedAt_valueCl` (Confined.lean) shows
  that every element of a confined sort is a value's element, and `confined_has_value` that a
  confined sort has a value. Dropped, a covered application of the generator denotes what the
  function it overloads denotes there (the overload equation). Under `FnHyp`'s first conjunct
  that function has an `Eval` result at every argument list of values, and the result is what
  `Γ` states the application to be (its clauses' items, or its rest through `ΓFallback`): ⊥ or a
  value's element. So at a semantics `coreOK` without the conjunct admits, with `FnHyp`, every
  element of a sort `confinedAtV` confines is still a value's element, and no model is lost and no
  step is added. Where `FnHyp` fails it is not so: in test/OvlFun.lean's `Conf` (REVIEW-CN4
  finding A) `fB(X) = fB(X)` gives `fB(b)` no `Eval` result and leaves its element free in `Γ`, so
  `fS(inj b)` can be an element of S that is no value's. `confined_has_value` does fail without the
  conjunct: S of `c [fB]` is confined for `confinedAtV` and has no value (argued above; no library
  theorem reads `confined_has_value`). The conjunct is asked because `confinedAt_valueCl` and
  `confined_has_value` are stated without `FnHyp`, which their readers' headline statements carry.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace KCore.WitStage4Gen

/-- `confinedAt` without its conjunct on a generator that overloads a function. -/
def confinedAtV (c : Semantics) : Nat → Srt → Bool
  | 0, s => s == Srt.bool && c.litSort s
  | k + 1, s => confinedAtV c 0 s ||
      ((Faithful.consSorts c).contains s && !(c.gens s).isEmpty &&
        (c.gens s).all fun g => g.argSorts.all (confinedAtV c k))

/-- `confined` reading `confinedAtV`. -/
def confinedV (c : Semantics) (s : Srt) : Bool := confinedAtV c (Faithful.kernelSorts c).length s

/-- `rulesPlain` reading `confinedV`. -/
def rulesPlainV (c : Semantics) : Bool := c.rules.all fun r =>
  let conf := fun i => (r.vars[i]?.map (confinedV c)).getD false || memHeld c (varOccs r.lhs) r.pre i
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (heldOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- `rulesPlainV` is `rulesPlain` with `confinedV` for `confined`: the text, by `rfl`. -/
theorem rulesPlain_eq (c : Semantics) : c.rulesPlain = c.rules.all fun r =>
    let conf := fun i => (r.vars[i]?.map c.confined).getD false || memHeld c (varOccs r.lhs) r.pre i
    let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
    let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
    r.opens.all (fun i => (heldOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
    (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed) := rfl

def aS : Srt := nRegSorts
def bS : Srt := nRegSorts + 1
def sS : Srt := nRegSorts + 2
def pgmS : Srt := nRegSorts + 3
def kl : Sym := nRegSyms + 6
def b : Sym := nRegSyms + 8
def x : Sym := nRegSyms + 9
def y : Sym := nRegSyms + 10
def fB : Sym := nRegSyms + 11
def fS : Sym := nRegSyms + 12

def cellCtors (kc : Srt) (kl : Sym) : List CtorSig :=
  [⟨topLabel, [kc, Srt.counter], Srt.top⟩, ⟨topFragLabel, [kc + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kl, [Srt.k], kc⟩, ⟨kl + 1, [], kc + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts (kc : Srt) : List (Srt × Srt) := [(kc, kc + 1), (Srt.counter, Srt.counterOpt)]

/-- The library: Int and Bool below KItem, `#KConfigValue`. -/
def lib0 : Lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }

/-- `<generatedTop>(<k>(kseq(inj{s,KItem}(t), dotk)), C)`, C the variable `cnt`. -/
def cfg (s : Srt) (t : Term) (cnt : Nat) : Term :=
  .app topLabel [.app kl [.app kseq [.inj s Srt.kitem t, .app dotk []]], .var cnt]

/-- `fB : B → S`, not total, without a clause. -/
def fBFn : Fn := ⟨fB, [bS], sS, [], false⟩

/-- `<k> x </k> => ∃ ?H : S. <k> y </k> ∧ ⌈?H⌉`. -/
def rY : Rule :=
  { vars := [Srt.counter, sS], lhs := cfg pgmS (.app x []) 0, req := none,
    rhs := cfg pgmS (.app y []) 0, ens := none, prio := 50, exs := [1], post := .ceil sS (.var 1) }

/-- `fS` overloads `over`. -/
def c (over : List Sym) : Semantics :=
  { lib := lib0
    sortNames := ["A", "B", "S", "Pgm", "KCell", "KCellOpt"]
    symNames := ["LblisA", "LblisB", "LblisS", "LblisPgm", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'",
      "LblnoKCell", "Lblb", "Lblx", "Lbly", "LblfB", "LblfS"]
    userSorts := [Srt.top, Srt.topFrag, aS, bS, sS, pgmS, pgmS + 1, pgmS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (pgmS + 1) kl ++ [⟨b, [], bS⟩, ⟨x, [], pgmS⟩, ⟨y, [], pgmS⟩]
    fns := [fBFn]
    userSubsorts := (bS, aS) :: cellSubsorts (pgmS + 1)
    pgmSort := pgmS
    rules := [rY]
    ovls := [⟨⟨fS, [aS], sS⟩, over⟩] }

/-! ## Every leaf of `coreOK` but `rulesPlain`, and `FnHyp` -/

theorem subsortsOK_of (o : List Sym) (h : o = [fB] ∨ o = []) : (c o).subsortsOK = true := by
  rcases h with rfl | rfl <;> decide_cheap
theorem clauses_of (o : List Sym) :
    ((c o).fns.all fun f => f.clauses.all ((c o).clauseSorted f (List.map Fn.sig (c o).fns))) = true := rfl
theorem rules_of (o : List Sym) (h : o = [fB] ∨ o = []) : ((c o).rules.all (c o).ruleSorted) = true := by
  rcases h with rfl | rfl <;> decide_cheap
theorem clausesPlain_of (o : List Sym) : (c o).clausesPlain = true := rfl
theorem paramsPlain_of (o : List Sym) (h : o = [fB] ∨ o = []) : (c o).paramsPlain = true := by
  rcases h with rfl | rfl <;> decide_cheap
theorem predsApart_of (o : List Sym) (h : o = [fB] ∨ o = []) : (c o).predsApart = true := by
  rcases h with rfl | rfl <;> decide_cheap
theorem idsOK_of (o : List Sym) (h : o = [fB] ∨ o = []) : (c o).idsOK = true := by
  rcases h with rfl | rfl <;> decide_cheap
theorem overloadsOK_of (o : List Sym) (h : o = [fB] ∨ o = []) : (c o).overloadsOK = true := by
  rcases h with rfl | rfl <;> decide +kernel

open Faithful.Model in
theorem names_fast_of (o : List Sym) (h : o = [fB] ∨ o = []) : namesApartFast (c o) = true := by
  rcases h with rfl | rfl <;> decide +kernel

open Faithful.Model in
theorem ites_of (o : List Sym) (h : o = [fB] ∨ o = []) : itesApart (c o) = true := by
  rcases h with rfl | rfl <;> decide_itesApart

set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
theorem faith_light_of (o : List Sym) (h : o = [fB] ∨ o = []) : (namesNumbered (c o) && genWf (c o) &&
    collSortsOK (c o) && collsOK (c o) && patHeadsOK (c o) && LitsApart (c o) && sortsNumbered (c o) &&
    kindsApart (c o) && ctorsOnce (c o) && fnsApart (c o)) = true := by
  rcases h with rfl | rfl <;> decide_cheap

open Faithful Faithful.Model in
theorem faithCoreOK_of (o : List Sym) (h : o = [fB] ∨ o = []) : (c o).faithCoreOK = true := by
  have hl := faith_light_of o h
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hl
  unfold Semantics.faithCoreOK
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, namesApartK_of_fast (names_fast_of o h), ites_of o h,
    Bool.and_self]

theorem lookup_fB : (c [fB]).lookupFn fB = some fBFn := rfl

/-- `fB` has no clause: its value is its rest everywhere and it is not total; the rule needs no
witness and there is no parameter. -/
theorem fnHyp : FnHyp (c [fB]) := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, fun k hk => absurd hk List.not_mem_nil⟩
  · intro fn hfn vs _
    rw [show (c [fB]).fns = [fBFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact ⟨_, Eval.rest lookup_fB fun _ h => absurd h List.not_mem_nil⟩
  · intro fn hfn ht
    rw [show (c [fB]).fns = [fBFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd ht Bool.false_ne_true
  · intro fn hfn cl cl' h
    rw [show (c [fB]).fns = [fBFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd h List.not_mem_nil
  · intro fn hfn cl hcl
    rw [show (c [fB]).fns = [fBFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd hcl List.not_mem_nil
  · intro r hr hw
    rw [show (c [fB]).rules = [rY] from rfl, List.mem_singleton] at hr
    subst hr
    exact absurd hw (by decide +kernel)
  · intro fn hfn cl hcl _
    rw [show (c [fB]).fns = [fBFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd hcl List.not_mem_nil

theorem meets_others : (c [fB]).subsortsOK = true ∧
    ((c [fB]).fns.all fun f => f.clauses.all ((c [fB]).clauseSorted f (List.map Fn.sig (c [fB]).fns))) = true ∧
    ((c [fB]).rules.all (c [fB]).ruleSorted) = true ∧ (c [fB]).clausesPlain = true ∧
    (c [fB]).paramsPlain = true ∧ (c [fB]).faithCoreOK = true ∧
    (c [fB]).predsApart = true ∧ (c [fB]).idsOK = true ∧ (c [fB]).overloadsOK = true ∧ FnHyp (c [fB]) :=
  ⟨subsortsOK_of _ (.inl rfl), clauses_of _, rules_of _ (.inl rfl), clausesPlain_of _, paramsPlain_of _ (.inl rfl),
    faithCoreOK_of _ (.inl rfl), predsApart_of _ (.inl rfl), idsOK_of _ (.inl rfl),
    overloadsOK_of _ (.inl rfl), fnHyp⟩

/-! ## The conjunct alone refuses `c [fB]` -/

/-- S is not confined, by the conjunct alone: confined for `confinedAtV`, and with `fS`
overloading nothing. -/
theorem confined_S : (c [fB]).confined sS = false ∧ confinedV (c [fB]) sS = true ∧ (c []).confined sS = true := by
  decide +kernel

theorem fnOvl_facts : (c [fB]).fnOvlSyms = [fS] ∧ (c []).fnOvlSyms = [] := by decide +kernel

theorem not_rulesPlain : (c [fB]).rulesPlain = false := by decide +kernel
theorem not_coreOK : (c [fB]).coreOK = false := by decide +kernel

/-- With the conjunct dropped, `rulesPlain` holds of `c [fB]`. -/
theorem rulesPlainV_true : rulesPlainV (c [fB]) = true := by decide +kernel

theorem c0_rulesPlain : (c []).rulesPlain = true := by decide +kernel

/-- With `fS` overloading nothing, `coreOK` holds. -/
theorem c0_coreOK : (c []).coreOK = true := by
  have hs : (c []).sortedOK = true := by
    unfold Semantics.sortedOK
    rw [subsortsOK_of _ (.inr rfl), clauses_of, rules_of _ (.inr rfl), c0_rulesPlain, clausesPlain_of,
      paramsPlain_of _ (.inr rfl)]; rfl
  unfold Semantics.coreOK
  rw [hs, faithCoreOK_of _ (.inr rfl), predsApart_of _ (.inr rfl),
    idsOK_of _ (.inr rfl), overloadsOK_of _ (.inr rfl)]; rfl

end KCore.WitStage4Gen

/-- info: 'KCore.WitStage4Gen.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitStage4Gen.meets_others
/-- info: 'KCore.WitStage4Gen.confined_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitStage4Gen.confined_S
/-- info: 'KCore.WitStage4Gen.not_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitStage4Gen.not_coreOK
/-- info: 'KCore.WitStage4Gen.rulesPlainV_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitStage4Gen.rulesPlainV_true
/-- info: 'KCore.WitStage4Gen.c0_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitStage4Gen.c0_coreOK
