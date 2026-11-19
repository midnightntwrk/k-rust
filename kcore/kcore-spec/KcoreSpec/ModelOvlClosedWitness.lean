/-
  KCore. A semantics that meets every condition of `coreOK` but the part of `overloadsOK` that asks
  an overloading symbol to list every function it reaches along the overloads (`ovlClosure`), and
  `FnHyp`, whose `Γ` has no model: so `SoundC` fails of it (`not_sound`), and that part cannot be
  left out of `coreOK`.

  The chain `plusBig : Big Big → Big` over `plusExp : Exp Exp → Exp` over the function
  `plusInt : Int Int → Int`, Int < Exp < Big, with `plusBig` listing `plusExp` only and `plusInt`
  without a clause (test/OvlFun.lean's `Chain.c false` with its function's clause taken away).
  `plusExp` lists a function, so it is function-overloaded; `plusBig` lists none, so it is not
  (`fnOvlSyms`), and `consItemsK` states its Cons-Fun at every argument: `plusBig(y, y)` is one
  element of Big for every y of Big. The overload equations state `plusBig(inj x, inj x) =
  inj(plusExp(x, x))` for x of Exp and `plusExp(inj z, inj z) = inj(plusInt(z, z))` for z of Int.
  `plusInt` has no clause and no rest, so `ΓFallback` states `plusInt(0, 0) = ⊥`. At z the element
  of `0`, `plusBig(inj inj z, inj inj z)` is then empty and one element at once. With `plusBig`
  listing `plusInt` as well (`c0`), `overloadsOK` holds (`c0_overloadsOK`): `plusBig` is then
  function-overloaded and its Cons-Fun is stated at uncovered arguments only. The decidable facts
  are kernel decisions, each part of `coreOK` on its own.
-/
import KcoreSpec.Sound
import KcoreSpec.CoreDecide
import KcoreSpec.ModelOvlLibCtorWitness

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore

namespace Faithful

namespace OvlClosedWitness

open ML
open Faithful.OvlLibCtorWitness (ov1 ov2 ov3 ov4 ov5 ov6 ov7 ov8 ov9)

/-- The library: Int and Bool below KItem, `#KConfigValue`. -/
def lib0 : Lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }

def expS : Srt := nRegSorts
def bigS : Srt := nRegSorts + 1
/-- The `k` cell's sort (its optional sort `kcS + 1`). -/
def kcS : Srt := nRegSorts + 2
def kl : Sym := nRegSyms + 4
def plusInt : Sym := nRegSyms + 6
def plusExp : Sym := nRegSyms + 7
def plusBig : Sym := nRegSyms + 8

/-- `<generatedTop>`, `<k>`, the counter and their optional sorts. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, kcS, kcS + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [kcS, Srt.counter], Srt.top⟩, ⟨topFragLabel, [kcS + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kl, [Srt.k], kcS⟩, ⟨kl + 1, [], kcS + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(kcS, kcS + 1), (Srt.counter, Srt.counterOpt)]

/-- `plusInt : Int Int → Int`, not total, without a clause. -/
def plusIntFn : Fn := ⟨plusInt, [Srt.int, Srt.int], Srt.int, [], false⟩

def intSig : CtorSig := ⟨plusInt, [Srt.int, Srt.int], Srt.int⟩
def expSig : CtorSig := ⟨plusExp, [expS, expS], expS⟩
def bigSig : CtorSig := ⟨plusBig, [bigS, bigS], bigS⟩
def oExp : OvlSig := ⟨expSig, [plusInt]⟩

/-- `plusBig` overloads `plusExp`, and `plusInt` where `b`. -/
def cOf (b : Bool) : Semantics :=
  { lib := lib0
    sortNames := ["Exp", "Big", "KCell", "KCellOpt"]
    symNames := ["LblisExp", "LblisBig", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell",
      "LblplusInt", "LblplusExp", "LblplusBig"]
    userSorts := [Srt.top, Srt.topFrag, expS, bigS, kcS, kcS + 1, Srt.counter, Srt.counterOpt]
    ctors := cellCtors
    fns := [plusIntFn]
    userSubsorts := [(Srt.int, expS), (expS, bigS)] ++ cellSubsorts
    pgmSort := Srt.k
    rules := []
    ovls := [oExp, ⟨bigSig, if b then [plusExp, plusInt] else [plusExp]⟩] }

def oBig : OvlSig := ⟨bigSig, [plusExp]⟩

/-- The witness: `plusBig` does not list `plusInt`. -/
def c : Semantics := cOf false

/-- With `plusBig` listing `plusInt` as well. -/
def c0 : Semantics := cOf true

/-! ## Every condition of `coreOK` but `overloadsOK`'s ninth part, and `FnHyp` -/

theorem sortedOK_of (b : Bool) : (cOf b).sortedOK = true := by cases b <;> decide_cheap
theorem hooksApart_of (b : Bool) : (cOf b).hooksApart = true := by cases b <;> decide_cheap
theorem predsApart_of (b : Bool) : (cOf b).predsApart = true := by cases b <;> decide_cheap
theorem idsOK_of (b : Bool) : (cOf b).idsOK = true := by cases b <;> decide_cheap

open Faithful.Model in
theorem names_fast_of (b : Bool) : namesApartFast (cOf b) = true := by cases b <;> decide +kernel

open Faithful.Model in
theorem ites_of (b : Bool) : itesApart (cOf b) = true := by cases b <;> decide_itesApart

set_option maxHeartbeats 1000000 in
open Faithful.Model in
theorem faith_light_of (b : Bool) : (namesNumbered (cOf b) && genWf (cOf b) && collSortsOK (cOf b) &&
    collsOK (cOf b) && patHeadsOK (cOf b) && LitsApart (cOf b) && sortsNumbered (cOf b) &&
    kindsApart (cOf b) && ctorsOnce (cOf b) && fnsApart (cOf b)) = true := by cases b <;> decide_cheap

open Faithful.Model in
theorem faithCoreOK_of (b : Bool) : (cOf b).faithCoreOK = true := by
  have h := faith_light_of b
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  unfold Semantics.faithCoreOK
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, namesApartK_of_fast (names_fast_of b), ites_of b,
    Bool.and_self]

theorem sortedOK : c.sortedOK = true := sortedOK_of false
theorem faithCoreOK : c.faithCoreOK = true := faithCoreOK_of false
theorem hooksApart : c.hooksApart = true := hooksApart_of false
theorem predsApart : c.predsApart = true := predsApart_of false
theorem idsOK : c.idsOK = true := idsOK_of false

theorem c0_overloadsOK : c0.overloadsOK = true := by decide +kernel

/-- With `plusBig` listing `plusInt` as well, `coreOK` holds. -/
theorem c0_coreOK : c0.coreOK = true := by
  show ((cOf true).sortedOK && (cOf true).faithCoreOK && (cOf true).hooksApart && (cOf true).predsApart &&
    (cOf true).idsOK && c0.overloadsOK) = true
  rw [sortedOK_of, faithCoreOK_of, hooksApart_of, predsApart_of, idsOK_of, c0_overloadsOK]; rfl

theorem lookup_plusInt : c.lookupFn plusInt = some plusIntFn := rfl

/-- `plusInt` has no clause: its value is its rest everywhere, it is not total, and no two of its
clauses meet. -/
theorem fnHyp : FnHyp c := by
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩
  · intro fn hfn vs _
    rw [show c.fns = [plusIntFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact ⟨_, Eval.rest lookup_plusInt fun _ h => absurd h List.not_mem_nil⟩
  · intro fn hfn ht
    rw [show c.fns = [plusIntFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd ht Bool.false_ne_true
  · intro fn hfn cl cl' h
    rw [show c.fns = [plusIntFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd h List.not_mem_nil
  · intro fn hfn cl hcl
    rw [show c.fns = [plusIntFn] from rfl, List.mem_singleton] at hfn
    subst hfn
    exact absurd hcl List.not_mem_nil

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `overloadsOK`'s ninth part holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ ov1 c = true ∧ ov2 c = true ∧ ov3 c = true ∧ ov4 c = true ∧
    ov5 c = true ∧ ov6 c = true ∧ ov7 c = true ∧ ov8 c = true ∧ c.ovlPatsOK = true ∧ FnHyp c :=
  ⟨sortedOK, faithCoreOK, hooksApart, predsApart, idsOK, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fnHyp⟩

/-- `plusBig` reaches `plusInt` through `plusExp` and does not list it. -/
theorem not_ov9 : ov9 c = false := by decide +kernel
theorem not_overloadsOK : c.overloadsOK = false := by decide +kernel

/-! ## `Γ c` has no model -/

theorem fnOvlSyms_eq : c.fnOvlSyms = [plusExp] := by decide +kernel
theorem exp_cons : expS ∈ consSorts c := by decide +kernel
theorem big_cons : bigS ∈ consSorts c := by decide +kernel
theorem int_exp : (Srt.int, expS) ∈ c.subsorts := by decide +kernel
theorem exp_big : (expS, bigS) ∈ c.subsorts := by decide +kernel
theorem genWf_c : genWf c = true := by decide_cheap
theorem oExp_mem : oExp ∈ c.ovls := List.mem_cons_self ..
theorem oBig_mem : oBig ∈ c.ovls := List.mem_cons_of_mem _ (List.mem_singleton_self _)
theorem big_not_fnOvl : c.fnOvl (.ctor bigSig) = false := by decide +kernel
theorem exp_over : expSig ∈ c.ovlOver oBig := by decide +kernel
theorem int_over : intSig ∈ c.ovlOver oExp := by decide +kernel
theorem int_ne_exp : (c.sortName Srt.int == c.sortName expS) = false := by decide +kernel
theorem exp_ne_big : (c.sortName expS == c.sortName bigS) = false := by decide +kernel
theorem plusInt_allFns : plusIntFn ∈ c.allFns := List.mem_append_left _ (List.mem_singleton_self _)
theorem sorts00 : c.sortsOf [int 0, int 0] = some plusIntFn.args := by decide +kernel
theorem rest00 : c.fnRest plusIntFn [int 0, int 0] = none := by decide +kernel

/-- Two elements of one sort. -/
theorem pair_sorts {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {x : M} {s : String}
    (hx : InS I s x) : ∀ (i : Nat) (y : M) (s' : String), [x, x][i]? = some y → [s, s][i]? = some s' → InS I s' y
  | 0, _, _, hy, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy hs; subst hy hs; exact hx
  | 1, _, _, hy, hs => by
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hy hs; subst hy hs; exact hx
  | _ + 2, _, _, hy, _ => by simp at hy

/-- The lifts of an overload equation at two equal arguments, the sorts named apart. -/
theorem pair_lift {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {A B : String} {z y : M}
    (hAB : (A == B) = false) (h : ∀ m, GS I B (.inj A) [z] m ↔ m = y) :
    ∀ (i : Nat) (A' B' : String) (z' y' : M), [A, A][i]? = some A' → [B, B][i]? = some B' →
      [z, z][i]? = some z' → [y, y][i]? = some y' →
      ∀ m, (if (A' == B') = true then m = z' else GS I B' (.inj A') [z'] m) ↔ m = y'
  | 0, _, _, _, _, hA, hB, hz, hy, m => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB hz hy
    subst hA hB hz hy
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hAB]; exact Bool.false_ne_true))]; exact h m
  | 1, _, _, _, _, hA, hB, hz, hy, m => by
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hA hB hz hy
    subst hA hB hz hy
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hAB]; exact Bool.false_ne_true))]; exact h m
  | _ + 2, _, _, _, _, hA, _, _, _, _ => by simp at hA

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem koreList_trW : ∀ ws : List GroundTerm, (GroundTerm.koreList c ws).map (KoreAML.tr ⟨[], []⟩) = ws.map (den c)
  | [] => by rw [GroundTerm.koreList]; rfl
  | w :: ws => by rw [GroundTerm.koreList, List.map_cons, List.map_cons, koreList_trW ws]; rfl

theorem elems_all2W (hI : I ⊧ᴵP Γ c) (e : Valuation M) : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
    All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) (ws.map (den c)) (ws.map (elemOf c I))
  | [], _, _ => .nil
  | w :: ws, ss, h => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOf_cons.mp h
    exact .cons (elemOf_spec hI h1 e).1 (elems_all2W hI e h2)

/-- The element of an application of a symbol with the signature `k` is the one `k`'s generator
builds from its arguments' elements. -/
theorem den_sig_gsW (hI : I ⊧ᴵP Γ c) {f : Sym} {ws : List GroundTerm} {k : CtorSig} (hn : k.name = f)
    (hws : c.sortsOf ws = some k.args) (e : Valuation M) (m : M) :
    (den c (.ctor f ws)).interpret I e m ↔ GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m := by
  rw [den_ctor, trArgs_appList, koreList_trW, interp_appList_sing _ _ _ (elems_all2W hI e hws)]
  unfold GS
  simp only [Gen.toK, toK, genHead, hn]
  rfl

end

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  let x := elemOf c I (int 0)
  have hx : InS I (c.sortName Srt.int) x := (inS_iff _).mp (elemOf_spec hI (sortOf_int 0) KoreAML.val0).2
  -- `inj{Int,Exp}(x)` and `inj{Exp,Big}` of it, by the injections' Cons-Fun
  obtain ⟨y1, hy1, hy1e⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem exp_cons (gensF_inj int_exp) rfl, rfl⟩))
    (xs := [x]) rfl (single_sorts hx)
  obtain ⟨y2, hy2, hy2e⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem big_cons (gensF_inj exp_big) rfl, rfl⟩))
    (xs := [y1]) rfl (single_sorts hy1)
  -- `plusBig(y2, y2)` is one element, by its Cons-Fun
  obtain ⟨y, -, hye⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem (N := bigSig.result) big_cons
    (gensF_of_ovl genWf_c oBig_mem) big_not_fnOvl, rfl⟩)) (xs := [y2, y2]) rfl (pair_sorts hy2)
  have hy : GS I (c.sortName bigS) (.ctor (toK c bigSig)) [y2, y2] y := (hye y).mpr rfl
  -- the overload equation of `plusBig` over `plusExp`
  have e1 := ovlEq_at hD (N := c.sortName bigS) (N' := c.sortName expS)
    (sat_cons hI (Or.inl ⟨_, ovlEqItem_mem oBig_mem exp_over, rfl⟩))
    (zs := [y1, y1]) (ys := [y2, y2]) rfl rfl rfl (pair_sorts hy1) (pair_lift exp_ne_big hy2e) y
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [show (toK c expSig).result = c.sortName expS from rfl,
    show (toK c oBig.sig).result = c.sortName bigS from rfl, exp_ne_big]; exact Bool.false_ne_true))] at e1
  obtain ⟨x1, hx1, -⟩ := e1.mp hy
  -- the overload equation of `plusExp` over `plusInt`
  have e2 := ovlEq_at hD (N := c.sortName expS) (N' := c.sortName Srt.int)
    (sat_cons hI (Or.inl ⟨_, ovlEqItem_mem oExp_mem int_over, rfl⟩))
    (zs := [x, x]) (ys := [y1, y1]) rfl rfl rfl (pair_sorts hx) (pair_lift int_ne_exp hy1e) x1
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [show (toK c intSig).result = c.sortName Srt.int from rfl,
    show (toK c oExp.sig).result = c.sortName expS from rfl, int_ne_exp]; exact Bool.false_ne_true))] at e2
  obtain ⟨w, hw, -⟩ := e2.mp hx1
  -- `plusInt(0, 0)` is nothing, by `ΓFallback`
  have hfb := sat_rest hI plusInt_allFns sorts00 (fun _ h => absurd h List.not_mem_nil)
  rw [rest00] at hfb
  have h1 := hfb KoreAML.val0 default
  rw [KoreAML.interp_equal hD] at h1
  have hden : (den c (.ctor plusInt [int 0, int 0])).interpret I KoreAML.val0 w :=
    (den_sig_gsW hI (k := intSig) rfl sorts00 KoreAML.val0 w).mpr hw
  exact absurd ((h1 w).mp hden) (by simp)

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `overloadsOK`'s ninth
part, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end OvlClosedWitness

end Faithful

end KCore
