/-
  The row faithCoreOK.5 (`patHeadsOK`) of test/witnesses.toml: no witness found in the no-model
  form (a semantics meeting every other leaf condition of `coreOK` and `FnHyp`, failing the
  conjunct, whose `Γ` has no model). The rows faithCoreOK.4 (`collsOK`) and faithCoreOK.7
  (`LitsApart`) have witness modules: KcoreSpec/ModelCollUnitWitness.lean and
  KcoreSpec/ModelLitsWitness.lean. Run from the package root: `lake env lean -j1 test/WitRestFaithB.lean`.

  Kernel-checked here: `DupParam.c` meets every other leaf condition of `coreOK` (`sortedOK`, the
  other eleven conjuncts of `faithCoreOK`, `predsApart`, `idsOK`, `overloadsOK`) and
  `FnHyp`, with `patHeadsOK` false; so it is not implied by the others. `DupParam.c0`, `c` without
  the repeated declaration, meets `coreOK`.

  `DupParam.c`: the cells and one range-map collection `S` of the definition's own, of Int keys and
  values, whose unit parameter is numbered `r`, a registry symbol (`#EOF`) that is no hook, no
  constructor and no function of `c`, and declared twice with one signature: first implemented by
  the library range map's unit, then by the library list's unit. The second declaration is
  implemented by a collection pattern symbol, so its signature is a pattern head (`collPatSigs`);
  `isCollPat r` reads the first (`lookupParam`), implemented by no pattern symbol, so the head is
  neither a constructor nor one the downward reading covers.

  How narrow the failure is (argued, not kernel-checked): a head of `patCtxAll` is a constructor
  (passes by `isCtor`), a map pattern hook (`downHead`), a set or list hook (`isCollPat`, those
  hooks being apart from the map's), an overloading symbol (`isOvl`, by `overloadsOK`'s first
  part) or a parameter implemented by a pattern symbol. Such a parameter is named like no hook
  (`kindsApart`); `collsOK` makes it a unit, element or concatenation of a collection whose first
  declaration is implemented by the library's symbol of the collection's kind, a pattern symbol for
  a map, a set or a list, so it passes unless the collection is a range map and the name is
  declared twice. Two declarations of an own symbol are refused by `idsOK`'s numbering, so the name
  is a registry symbol's, and `namesApartK` asks the two signatures to be one.

  Argued, not kernel-checked: `Γ` of `c` has a model. `ΓDomains` states each parameter's graph by
  `paramVal`, which reads the first declaration (`lookupParam`), so both declarations give one item;
  the arity item (`sigItems`, over `kernelSyms`) is repeated; no other part of `Γ` reads `params`
  but through `lookupParam` or the signatures. So `Γ c` is `Γ c0`'s premises up to a repeated item,
  and `c0` meets `coreOK` and `FnHyp`, whose theory has a model. The conjunct is asked for the
  downward reading of left-hand sides (a pattern head it does not read), not for a model.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestFaithB

open ML Faithful.Model
open CollUnitWitness (cellSorts cellSubsorts ownCtors S)

namespace DupParam

/-- `#EOF`: a registry symbol, no hook. -/
def r : Sym := 75

def eS : Sym := nRegSyms + 5
def cS : Sym := nRegSyms + 6

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
    sortNames := ["KCell", "KCellOpt", "S"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblSItem", "Lbl'Unds'S'Unds'"]
    userSorts := cellSorts ++ [S]
    ctors := ownCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [{ sig := ⟨r, [], S⟩, impl := some (builtinColl .rangeMap).unit },
      { sig := ⟨r, [], S⟩, impl := some listUnit },
      { sig := ⟨eS, [Srt.int, Srt.int], S⟩, impl := some (builtinColl .rangeMap).elem },
      { sig := ⟨cS, [S, S], S⟩, impl := some (builtinColl .rangeMap).concat }]
    colls := [⟨S, .rangeMap, Srt.int, some Srt.int, r, eS, cS⟩] }

/-- `c` without the second declaration of `r`. -/
def c0 : Semantics := { c with params := c.params.eraseIdx 1 }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide_cheap

theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧
    collsOK c = true ∧ namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧
    itesApart c = true ∧ kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, fnHyp⟩

theorem not_patHeadsOK : patHeadsOK c = false := by decide +kernel

/-- `r` is no hook, the first declaration is implemented by no pattern symbol, the second by one. -/
theorem r_facts : isHook r = false ∧ c.isCollPat r = false ∧ collPatternHooks.contains listUnit = true ∧
    c.lookupParam r = some { sig := ⟨r, [], S⟩, impl := some (builtinColl .rangeMap).unit } := by
  decide +kernel

end DupParam

/-- info: 'KCore.Faithful.WitRestFaithB.DupParam.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DupParam.meets_others

/-- info: 'KCore.Faithful.WitRestFaithB.DupParam.c0_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DupParam.c0_coreOK

end KCore.Faithful.WitRestFaithB
