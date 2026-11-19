/-
  The rows idsOK.6, idsOK.7 and idsOK.8 of test/witnesses.toml (the registry sorts of `userSorts`
  generated ones, the registry constructors of `ctors` generated ones, the library's facts). Run
  from the package root: `lake env lean -j1 test/WitRestIdsB.lean`.

  Kernel-checked here, each a semantics meeting every other leaf condition of `coreOK`
  (`sortedOK`, `faithCoreOK`, `predsApart`, the other seven leaves of `idsOK`,
  `overloadsOK`) and `FnHyp`, with the leaf false, beside a semantics `c0` meeting `coreOK`:
  - idsOK.6, `Reg.c`: the registry sort Id (no generated one) listed among `userSorts`; `Reg.c0`
    lists it among the library's sorts below KItem instead. The constructor items of the two have,
    in order, the same patterns (`Reg.cons_align`).
  - idsOK.7, `Ctor.c`: the registry constructor `#KConfigValue : K → KItem` listed among the
    definition's constructors; `Ctor.c0` lists it among the library's. The constructor items of the two have,
    in order, the same patterns (`Ctor.cons_align`).
  - idsOK.8, `Dup.c`: the library's sorts below KItem list MInt twice (`Lib.ok`'s second part);
    `Dup.c0` lists it once.
  Of `Lib.ok`'s other parts (kernel decisions, `Other`): a library sort KItem, or a library subsort
  outside the library's sorts, fails `genWf` too; a library sort numbered as an own sort fails
  `namesApartK`; a library sort that is a generated configuration sort of the cells fails
  `predsApart`. Not examined: a library constructor named like a map-pattern symbol, a generated
  configuration sort in the library of a semantics without that cell, a library sort numbered beyond
  the own sorts.

  Argued, not kernel-checked: `Γ` of each witness has a model.
  - `Reg.c`: `Γ` reads the sorts below KItem as `lib.sortsBelowKItem ++ userSorts`, the same
    sorts in another order, and its kernel sorts as a range independent of either; Id becomes a
    constructor sort in `c` (`consSorts` reads `userSorts`) but has no generator, so it adds no
    constructor item (`cons_align`). So `Γ c` and `Γ c0` have the same premises up to order, and `c0`
    meets `coreOK` and `FnHyp`, whose theory has a model.
  - `Ctor.c`: `ctorSigs` lists the library's constructors, then the definition's: the two have the
    same constructors in another order, the same generators per sort (`cons_align`) and the same
    signature items up to order. The conjunct is asked for the numbering of the definition's own
    symbols, not for a model.
  - `Dup.c`: Γ is `Dup.c0`'s up to repeated items: MInt's subsort into KItem is listed twice, the
    injection from MInt is a generator of KItem twice, and a pair of comparable injections has no
    distinctness item; MInt has no sort predicate (`regPred`), so the sort predicates are the same.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestIdsB

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

/-- The configuration `<k> K </k>` with the generated counter. -/
def base : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-! ## idsOK.6: a registry sort that is no generated one among `userSorts` -/

namespace Reg

/-- The registry sort Id. -/
def Id : Srt := 9

def c0 : Semantics := { base with lib := { sortsBelowKItem := [Id] } }
def c : Semantics := { base with userSorts := cellSorts ++ [Id] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap
theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧ ids1 c = true ∧ ids2 c = true ∧ ids3 c = true ∧ ids4 c = true ∧
    ids5 c = true ∧ ids7 c = true ∧ ids8 c = true ∧ FnHyp c :=
  ⟨⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fnHyp⟩

theorem not_ids6 : ids6 c = false := by decide +kernel

/-- Id is the registry's, a sort below KItem of both, without generator in `c`. -/
theorem id_facts : Id < nRegSorts ∧ !genSorts.contains Id ∧ c.sortsBelowKItem.contains Id ∧
    c0.sortsBelowKItem.contains Id ∧ (consSorts c).contains Id ∧ c.gens Id = [] := by decide +kernel

theorem cons_align : (consItemsK c).map (·.pat) = (consItemsK c0).map (·.pat) := by decide +kernel

end Reg

/-! ## idsOK.7: a registry constructor that is no generated one among `ctors` -/

namespace Ctor

def kv : CtorSig := ⟨kconfigValue, [Srt.k], Srt.kitem⟩

def c0 : Semantics := { base with lib := { ctors := [kv] } }
def c : Semantics := { base with ctors := cellCtors ++ [kv] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap
theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧ ids1 c = true ∧ ids2 c = true ∧ ids3 c = true ∧ ids4 c = true ∧
    ids5 c = true ∧ ids6 c = true ∧ ids8 c = true ∧ FnHyp c :=
  ⟨⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fnHyp⟩

theorem not_ids7 : ids7 c = false := by decide +kernel

/-- The two have the same constructors, in another order. -/
theorem ctors_perm : c.ctorSigs.Perm c0.ctorSigs := by
  show (fixedCtors ++ [] ++ (cellCtors ++ [kv])).Perm (fixedCtors ++ [kv] ++ cellCtors)
  simp only [List.append_nil, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

theorem cons_align : (consItemsK c).map (·.pat) = (consItemsK c0).map (·.pat) := by decide +kernel

end Ctor

/-! ## idsOK.8: the library's facts -/

namespace Dup

/-- The registry sort MInt, without sort predicate. -/
def MInt : Srt := 8

def c0 : Semantics := { base with lib := { sortsBelowKItem := [MInt] } }
def c : Semantics := { base with lib := { sortsBelowKItem := [MInt, MInt] } }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap
theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧ ids1 c = true ∧ ids2 c = true ∧ ids3 c = true ∧ ids4 c = true ∧
    ids5 c = true ∧ ids6 c = true ∧ ids7 c = true ∧ FnHyp c :=
  ⟨⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fnHyp⟩

theorem not_ids8 : ids8 c = false := by decide +kernel

theorem no_pred : regPred MInt = none := by decide

end Dup

namespace Other

theorem kitem : genWf { base with lib := { sortsBelowKItem := [Srt.kitem] } } = false := by decide +kernel
theorem sub : genWf { base with lib := { sortsBelowKItem := [9], subsorts := [(9, 12)] } } = false := by
  decide +kernel
theorem own : namesApartK { base with lib := { sortsBelowKItem := [nRegSorts + 2] } } = false := by decide +kernel
theorem gen : ({ base with lib := { sortsBelowKItem := [Srt.counter] } } : Semantics).predsApart = false := by
  decide +kernel

end Other

/-- info: 'KCore.Faithful.WitRestIdsB.Reg.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Reg.meets_others

/-- info: 'KCore.Faithful.WitRestIdsB.Ctor.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ctor.meets_others

/-- info: 'KCore.Faithful.WitRestIdsB.Dup.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dup.meets_others

end KCore.Faithful.WitRestIdsB
