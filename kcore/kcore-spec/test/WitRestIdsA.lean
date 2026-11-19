/-
  The rows idsOK.1, idsOK.3 and idsOK.5 of test/witnesses.toml (the own sorts' numbering, the sort
  names within the symbol names, the registry sorts once). Run from the package root:
  `lake env lean -j1 test/WitRestIdsA.lean`.

  Kernel-checked here:
  - idsOK.1, `Perm.c`: the cells with the two own sorts listed in the other order in `userSorts`
    meet every other leaf condition of `coreOK` (`sortedOK`, `faithCoreOK`,
    `predsApart`, the other seven leaves of `idsOK`, `overloadsOK`) and `FnHyp`, with idsOK.1 false;
    `Perm.c0`, the same sorts in order, meets `coreOK`. (An own sort listed twice repeats its
    predicate among `allFns`, so `predsApart` refuses it as well: `Perm.dup_preds`.)
  - idsOK.3, `Short.c`: one own sort and no symbol names: every other leaf and `FnHyp` hold, with
    idsOK.3 false (idsOK.2 holds by the truncated subtraction: no own symbol, and none expected);
    `Short.c0`, the same with the predicate's name `LblisS`, meets `coreOK`.
  - idsOK.5: implied by `predsApart`, idsOK.4 and idsOK.6, for every semantics
    (`ids5_of_predsApart`): every registry sort of `userSorts` is a generated configuration sort
    (idsOK.6), each of which has a predicate (`regPred`) below `nRegSyms`, which labels no function
    of `c.fns` (idsOK.4), so `sortPreds` builds it and it is among the labels of `allFns`, which
    `predsApart` makes distinct; so a registry sort listed twice repeats a label (`Twice.c`, the
    counter's `Opt` sort listed twice: `predsApart` false). Since `predsApart` is itself implied by
    `idsOK` where the functions of `c.fns` are labelled apart (test/WitRestApart.lean,
    `predsApart_of_idsOK`), at most one of predsApart.1 and idsOK.5 can be dropped from `coreOK`
    for such a semantics, not both.

  Argued, not kernel-checked: `Γ` of `Perm.c` and of `Short.c` has a model.
  - `Perm.c`: `Γ` reads `userSorts` as a set of sorts (the sorts below KItem, the constructor sorts,
    `sortsOf`, the predicates' equations are stated per sort; their order orders the items only),
    so `Γ c` and `Γ c0` have the same premises, and `c0` meets `coreOK` and `FnHyp`, whose theory
    has a model.
  - `Short.c`: `Γ` names a symbol by `symName` only, and `c` differs from `c0` by the name of one
    symbol, the predicate of `S` (`""` for `LblisS`), which names no other symbol of either
    (`namesApartK` holds of both); renaming that symbol maps the premises of `Γ c0` onto those of
    `Γ c`, and a model of the one onto a model of the other. The conjunct is asked for the
    numbering of the own symbols after the sort predicates (`symBase`), not for a model.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestIdsA

open ML Faithful.Model
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- The leaves of `idsOK`, as test/witnesses.toml lists them. -/
def ids1 (c : Semantics) : Bool := c.ownSorts == List.range' nRegSorts c.sortNames.length
def ids2 (c : Semantics) : Bool := c.ownSyms == List.range' c.symBase (c.symNames.length - c.sortNames.length)
def ids3 (c : Semantics) : Bool := decide (c.sortNames.length ≤ c.symNames.length)
def ids4 (c : Semantics) : Bool := c.fns.all fun f => decide (nRegSyms ≤ f.label)
def ids5 (c : Semantics) : Bool := nodup (c.userSorts.filter fun s => decide (s < nRegSorts))
def ids6 (c : Semantics) : Bool := (c.userSorts.filter fun s => decide (s < nRegSorts)).all genSorts.contains
def ids7 (c : Semantics) : Bool := c.ctors.all fun k => decide (nRegSyms ≤ k.name) || genSyms.contains k.name
def ids8 (c : Semantics) : Bool := c.lib.ok

/-- The eight are `idsOK`'s leaves. -/
theorem idsOK_eq (c : Semantics) :
    c.idsOK = (ids1 c && ids2 c && (ids3 c && ids4 c) && (ids5 c && ids6 c && ids7 c && ids8 c)) := rfl

/-- Every leaf condition of `coreOK` outside `idsOK`. -/
def outside (c : Semantics) : Prop :=
  c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.predsApart = true ∧ c.overloadsOK = true

theorem fnHyp_of_nil {c : Semantics} (hf : c.fns = []) (hp : ∀ k ∈ c.params, k.raw = false) (hr : c.readsConfined = false) :
    FnHyp c :=
  ⟨fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    openDecided_of_readsConfined hr, openLaws_of_plain hp⟩

/-! ## idsOK.1: the own sorts out of order -/

namespace Perm

def c0 : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- `KCellOpt` listed before `KCell`. -/
def c : Semantics := { c0 with userSorts := [Srt.top, Srt.topFrag, nRegSorts + 1, nRegSorts, Srt.counter, Srt.counterOpt] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide_cheap

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧ ids2 c = true ∧ ids3 c = true ∧ ids4 c = true ∧
    ids5 c = true ∧ ids6 c = true ∧ ids7 c = true ∧ ids8 c = true ∧ FnHyp c :=
  ⟨⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_ids1 : ids1 c = false := by decide +kernel

/-- `KCell` listed twice: its predicate is repeated, `predsApart` fails as well. -/
theorem dup_preds : ({ c0 with userSorts := cellSorts ++ [nRegSorts] } : Semantics).predsApart = false := by
  decide +kernel

end Perm

/-! ## idsOK.3: more sort names than symbol names -/

namespace Short

def S : Srt := nRegSorts

/-- One own sort, no symbol names. -/
def c : Semantics :=
  { lib := {}
    sortNames := ["S"]
    symNames := []
    userSorts := [S]
    ctors := []
    fns := []
    userSubsorts := []
    pgmSort := Srt.k
    rules := [] }

/-- The same, the predicate of `S` named `LblisS`. -/
def c0 : Semantics := { c with symNames := ["LblisS"] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide_cheap

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧ ids1 c = true ∧ ids2 c = true ∧ ids4 c = true ∧
    ids5 c = true ∧ ids6 c = true ∧ ids7 c = true ∧ ids8 c = true ∧ FnHyp c :=
  ⟨⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_ids3 : ids3 c = false := by decide +kernel

/-- The predicate of `S` is named `""` in `c`, `LblisS` in `c0`; no other symbol is named either. -/
theorem pred_names : c.symName nRegSyms = "" ∧ c0.symName nRegSyms = "LblisS" ∧ predOf S = some nRegSyms ∧
    namesApartK c = true ∧ namesApartK c0 = true :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap⟩

end Short

/-! ## idsOK.5: implied by `predsApart`, idsOK.4 and idsOK.6 -/

/-- The predicate `sortPreds` builds for the sort `X`: `predOf X` where it labels no function of
`c.fns`. -/
def predIn (c : Semantics) (X : Srt) : Option Sym := (predOf X).filter fun p => !c.fns.any (·.label == p)

theorem sortPreds_labels (c : Semantics) :
    c.sortPreds.map (·.label) = isK :: isKItem :: c.sortsBelowKItem.filterMap (predIn c) := by
  simp only [Semantics.sortPreds, List.map_cons, List.map_filterMap, List.cons_append, List.nil_append]
  congr 2
  congr 1
  funext X
  unfold predIn
  cases (predOf X).filter fun p => !c.fns.any (·.label == p) <;> rfl

/-- A predicate below `nRegSyms` is built where no function bears a registry symbol (idsOK.4). -/
theorem predIn_of_lt {c : Semantics} (h4 : ids4 c = true) {X : Srt} {p : Sym} (hX : predOf X = some p)
    (hp : p < nRegSyms) : predIn c X = some p := by
  have hq : (!c.fns.any (·.label == p)) = true := by
    rw [Bool.not_eq_true', List.any_eq_false]
    intro f hf heq
    have h1 := of_decide_eq_true (List.all_eq_true.mp h4 f hf)
    rw [beq_iff_eq] at heq
    subst heq
    exact absurd hp (Nat.not_lt.mpr h1)
  unfold predIn
  rw [hX]
  simp only [Option.filter, hq, ite_true]

/-- A list is without repetition where its images under a map defined on each of its members are. -/
theorem nodup_of_filterMap {f : Nat → Option Nat} : ∀ {l : List Nat}, (l.filterMap f).Nodup →
    (∀ x ∈ l, (f x).isSome = true) → l.Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hs => by
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hs a List.mem_cons_self)
    rw [List.filterMap_cons_some hp, List.nodup_cons] at h
    refine List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_filterMap.mpr ⟨a, ha, hp⟩), ?_⟩
    exact nodup_of_filterMap h.2 fun x hx => hs x (List.mem_cons_of_mem _ hx)

/-- Every generated configuration sort has a predicate, below `nRegSyms`. -/
theorem genSorts_pred : ∀ X ∈ genSorts, (predOf X).isSome = true ∧ (predOf X).all (decide <| · < nRegSyms) = true := by
  decide

/-- **idsOK.5 is implied by `predsApart`, idsOK.4 and idsOK.6**, for every semantics. -/
theorem ids5_of_predsApart (c : Semantics) (hp : c.predsApart = true) (h4 : ids4 c = true) (h6 : ids6 c = true) :
    ids5 c = true := by
  unfold Semantics.predsApart Semantics.allFns at hp
  rw [NamesApart.nodupB_iff, List.map_append, sortPreds_labels] at hp
  have hP : (c.sortsBelowKItem.filterMap (predIn c)).Nodup := ((List.nodup_append.mp hp).2.1).of_cons.of_cons
  have hsub : ((c.userSorts.filter fun s => decide (s < nRegSorts)).filterMap (predIn c)).Sublist
      (c.sortsBelowKItem.filterMap (predIn c)) :=
    ((List.filter_sublist).trans (List.sublist_append_right c.lib.sortsBelowKItem c.userSorts)).filterMap _
  unfold ids5
  rw [NamesApart.nodupB_iff]
  refine nodup_of_filterMap (hP.sublist hsub) fun x hx => ?_
  unfold ids6 at h6
  have hg := genSorts_pred x (List.contains_iff_mem.mp (List.all_eq_true.mp h6 x hx))
  obtain ⟨p, hpx⟩ := Option.isSome_iff_exists.mp hg.1
  rw [hpx, Option.all_some, decide_eq_true_eq] at hg
  rw [predIn_of_lt h4 hpx hg.2]
  rfl

namespace Twice

/-- The counter's `Opt` sort listed twice. -/
def c : Semantics := { Perm.c0 with userSorts := cellSorts ++ [Srt.counterOpt] }

theorem not_ids5 : ids5 c = false := by decide +kernel
theorem not_predsApart : c.predsApart = false := by decide +kernel

end Twice

/-- info: 'KCore.Faithful.WitRestIdsA.Perm.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Perm.meets_others

/-- info: 'KCore.Faithful.WitRestIdsA.Short.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Short.meets_others

/-- info: 'KCore.Faithful.WitRestIdsA.ids5_of_predsApart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ids5_of_predsApart

end KCore.Faithful.WitRestIdsA
