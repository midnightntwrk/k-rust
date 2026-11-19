/-
  The rows overloadsOK.5 to overloadsOK.7 of test/witnesses.toml (the symbols an overloading
  symbol overloads are constructors, overloading symbols listed before it or functions, each pair
  is well formed, the overloads agree), and the condition `ov6` that `overloadsOK` does not ask
  (`ovlOver` finds them all). Run from the package root: `lake env lean -j1 test/WitRestOvlB.lean`.

  overloadsOK.7 has a witness module, KcoreSpec/ModelOvlIncohWitness.lean (two constructors
  overloaded by one symbol, meeting at Int: `Γ` has no model). The conditions `ov1` to `ov9` are
  those of KcoreSpec/ModelOvlLibCtorWitness.lean (`ov7` to `ov9` the rows overloadsOK.6 to .8).

  Kernel-checked here:
  - `ov6`: implied by overloadsOK.5 at the same overloading symbol, for every semantics
    (`ov6_of_ov5`): a symbol found among the constructors, among the overloading symbols listed
    before or among the functions is found by `ovlOver`'s lookup in the constructors, every
    overloading symbol and the functions, so no overloaded symbol is dropped. So `overloadsOK`
    does not ask it.
  - overloadsOK.5, `Self.c`: the overloading symbol `f : Int → K` overloading itself meets every
    other leaf condition of `coreOK` (`sortedOK`, `faithCoreOK`, `predsApart`,
    `idsOK`, the other leaves of `overloadsOK`) and `FnHyp`, with overloadsOK.5 false.
  - overloadsOK.6, `Pair.c`: `f : Int → KCellOpt` overloading the counter cell's constructor
    `<generatedCounter> : Int → GeneratedCounterCell`, whose result sort is not below KCellOpt,
    meets every other leaf and `FnHyp`, with overloadsOK.6 false.
  `Self.c0` and `Pair.c0`, the same symbols overloading nothing, meet `coreOK`.

  Argued, not kernel-checked: `Γ` of `Self.c` and of `Pair.c` has a model.
  - `Self.c`: against `Self.c0`, `Γ` adds the overload equation `f(x) = f(x)`, valid; f's
    applications to Int are covered by f's own overload, so they are no values (`Self.f_covered`) and
    `ΓDomains` states less of them; the distinctness of f from K's other generators is stated at
    uncovered arguments only, none at Int; every other item is `c0`'s. So a model of `Γ c0` (it meets
    `coreOK` and `FnHyp`) is one of `Γ c`.
  - `Pair.c`: against `Pair.c0`, `Γ` adds the overload equation, `f(x)` is the injection from
    GeneratedCounterCell to KCellOpt of `<generatedCounter>(x)` (`ovlEq_at`, the result sorts
    differing); that injection is of no declared subsort, so no other item names it (`Pair.inj_free`);
    f's applications are covered, so no values; its distinctness from KCellOpt's other generators is
    `c0`'s or stated at uncovered arguments only. A model of `Γ c0`, the injection read as the map
    taking the element of `<generatedCounter>(n)` to that of `f(n)`, is one of `Γ c`. The conjunct
    is asked for the overloads' sorts as `norm` and the theorems on overloads read them.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestOvlB

open ML Faithful.Model
open Faithful.OvlLibCtorWitness (ov1 ov2 ov3 ov4 ov5 ov6 ov7 ov8 ov9)
open Faithful.OvlTwiceWitness (cellSorts cellCtors cellSubsorts fSig)

/-! ## `ov6`: implied by overloadsOK.5 -/

theorem length_filterMap {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    rw [List.filterMap_cons_some hb, List.length_cons, List.length_cons,
      length_filterMap f l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **`ov6` is implied by overloadsOK.5** at each overloading symbol `o` (at any place `i`),
for every semantics. -/
theorem ov6_of_ov5 (c : Semantics) (o : OvlSig) (i : Nat)
    (h : o.over.all (fun g => (lookupSig c.ctorSigs g).isSome || (c.ovls.take i).any (·.sig.name == g) ||
      c.fns.any (·.label == g)) = true) :
    ((c.ovlOver o).length == o.over.length) = true := by
  unfold Semantics.ovlOver
  rw [beq_iff_eq]
  refine length_filterMap _ _ fun g hg => ?_
  have hg' := List.all_eq_true.mp h g hg
  rw [lookupSig_eq, List.find?_append, List.find?_append]
  rcases Bool.or_eq_true_iff.mp hg' with h12 | h3
  · rcases Bool.or_eq_true_iff.mp h12 with h1 | h2
    · rw [lookupSig_eq] at h1
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h1
      rw [hk]; rfl
    · obtain ⟨x, hx, hxg⟩ := List.any_eq_true.mp h2
      have hs : (c.ovlSigs.find? (·.name == g)).isSome = true :=
        List.find?_isSome.mpr ⟨x.sig, List.mem_map_of_mem (List.mem_of_mem_take hx), hxg⟩
      cases h' : c.ctorSigs.find? (·.name == g) with
      | none =>
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
        rw [hy]; rfl
      | some k => rfl
  · obtain ⟨fn, hfn, hl⟩ := List.any_eq_true.mp h3
    have hs : ((c.fns.map fun fn => (⟨fn.label, fn.args, fn.result⟩ : CtorSig)).find? (·.name == g)).isSome = true :=
      List.find?_isSome.mpr ⟨_, List.mem_map_of_mem hfn, hl⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    rw [hy]
    cases c.ctorSigs.find? (·.name == g) <;> cases c.ovlSigs.find? (·.name == g) <;> rfl

/-! ## overloadsOK.5: an overloading symbol overloading itself -/

def base : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem fnHyp_of {c : Semantics} (hf : c.fns = []) (hp : ∀ k ∈ c.params, k.raw = false) (hr : c.readsConfined = false) :
    FnHyp c :=
  ⟨fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    openDecided_of_readsConfined hr, openLaws_of_plain hp⟩

namespace Self

def c0 : Semantics := { base with ovls := [⟨fSig, []⟩] }
def c : Semantics := { base with ovls := [⟨fSig, [fSig.name]⟩] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap
theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem fnHyp : FnHyp c := fnHyp_of rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ ov1 c = true ∧ ov2 c = true ∧ ov3 c = true ∧ ov4 c = true ∧
    ov7 c = true ∧ ov8 c = true ∧ c.ovlPatsOK = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

/-- It lists every function it reaches along the overloads: it reaches itself only. -/
theorem meets_ov9 : ov9 c = true := by decide +kernel

theorem not_ov5 : ov5 c = false := by decide +kernel

/-- `f(0)` is a value of `c0`, none of `c`. -/
theorem f_covered : c0.sortOf (.ctor fSig.name [int 0]) = some Srt.k ∧ c.sortOf (.ctor fSig.name [int 0]) = none := by
  decide +kernel

end Self

/-! ## overloadsOK.6: an overload whose result sort is not below the overloading symbol's -/

namespace Pair

def KCellOpt : Srt := nRegSorts + 1
def fOpt : CtorSig := ⟨nRegSyms + 4, [Srt.int], KCellOpt⟩

def c0 : Semantics := { base with ovls := [⟨fOpt, []⟩] }
def c : Semantics := { base with ovls := [⟨fOpt, [counterLabel]⟩] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap
theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem fnHyp : FnHyp c := fnHyp_of rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ ov1 c = true ∧ ov2 c = true ∧ ov3 c = true ∧ ov4 c = true ∧
    ov5 c = true ∧ ov8 c = true ∧ c.ovlPatsOK = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

/-- It lists every function it reaches along the overloads: it reaches a constructor only. -/
theorem meets_ov9 : ov9 c = true := by decide +kernel

theorem not_ov7 : ov7 c = false := by decide +kernel

/-- GeneratedCounterCell lies below no sort, KCellOpt in particular. -/
theorem inj_free : c.subsorts.all (fun p => p.1 != Srt.counter || p.2 != KCellOpt) = true ∧
    c.le Srt.counter KCellOpt = false := by decide +kernel

end Pair

/-- info: 'KCore.Faithful.WitRestOvlB.ov6_of_ov5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ov6_of_ov5

/-- info: 'KCore.Faithful.WitRestOvlB.Self.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Self.meets_others

/-- info: 'KCore.Faithful.WitRestOvlB.Pair.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pair.meets_others

end KCore.Faithful.WitRestOvlB
