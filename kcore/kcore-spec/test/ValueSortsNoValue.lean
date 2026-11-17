/-
  `Semantics.valueSorts` against the values of a sort (`Semantics.sortOf`), on definitions with
  `coreOK`. Run from the package root: `lake env lean -j1 test/ValueSortsNoValue.lean`.
  Kernel-checked (`decide +kernel`).

  `valueSorts` starts from K, KItem, Int, the library's sorts below KItem, its token sorts, the
  sorts with a carrier and the collection sorts, and closes under generators. Membership does not
  give a value on `coreOK` alone: `coreOK` does not ask that a library sort below KItem has a
  literal, a collection or a constructor.

  - `cIO`: Int and IOError below KItem, the cells of a `<k>` configuration, and no constructor of
    the library (`lib.ctors = []`). `cIO_core`: `coreOK` holds. `cIO_valueSorts`: IOError is in
    `valueSorts`. `cIO_no_value`: no value has the sort IOError (no constructor, overloading
    symbol or open generator has it as result, no sort is below it, no literal is one of its, and
    it is no collection sort).
  - `cLoop`: the same configuration with Int below KItem and a sort S of the one constructor
    `s : S → S` (`syntax S ::= s(S)`). `cLoop_core`: `coreOK` holds. `cLoop_valueSorts`: S is not
    in `valueSorts`, and Int, KItem, K and the cell sorts are.
  - `Semantics.hasValue`, the decided test that gives a value on `coreOK` (`hasValue_value`):
    IOError of `cIO` and S of `cLoop` are outside; String, KItem, K, the cell sorts, a token sort,
    a sort hooked to a carrier, a cell map sort, and IOError with a constructor are inside.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.ValueSortsNoValue

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

abbrev ioError : Srt := 12

example : regSortNames[ioError]? = some "IOError" := by decide +kernel

def cIO : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, ioError] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem cIO_core : cIO.coreOK = true := by decide_cheap

theorem cIO_valueSorts : cIO.valueSorts.contains ioError = true := by decide +kernel

theorem cIO_notColl : cIO.collOf ioError = none := by decide +kernel

/-- No value of `cIO` has the sort IOError. -/
theorem cIO_no_value (v : GroundTerm) : cIO.sortOf v ≠ some ioError := by
  intro h
  cases v with
  | ctor f ts =>
    obtain ⟨k, hk, -, hr⟩ := (Semantics.sortOf_ctor_of_none (c := cIO) rfl (by decide +kernel)).mp h
    rw [lookupSig_eq] at hk
    have hm : k ∈ cIO.ctorSigs := List.mem_of_find?_eq_some hk
    have hall : cIO.ctorSigs.all (fun k => k.result != ioError) = true := by decide +kernel
    have := List.all_eq_true.mp hall k hm
    simp [← hr] at this
  | inj a b w =>
    obtain ⟨hsub, -, -, hb⟩ := sortOf_inj.mp h
    have hall : cIO.subsorts.all (fun p => p.2 != ioError) = true := by decide +kernel
    have := List.all_eq_true.mp hall _ hsub
    simp [← hb] at this
  | dv s l =>
    obtain ⟨hd, hs⟩ := sortOf_dv.mp h
    subst hs
    have h1 : (cIO.lib.carrier ioError == Srt.int) = false := by decide +kernel
    have h2 : (cIO.lib.carrier ioError == Srt.bool) = false := by decide +kernel
    have k1 : cIO.lib.carrier ioError ≠ Srt.kconfigVar := by decide +kernel
    have k2 : cIO.lib.carrier ioError ≠ Srt.string := by decide +kernel
    have k3 : cIO.lib.carrier ioError ∉ cIO.lib.tokenSorts := by decide +kernel
    have k4 : cIO.lib.carrier ioError ≠ Srt.bytes := by decide +kernel
    have k5 : cIO.lib.carrier ioError ∉ cIO.lib.byteSorts := by decide +kernel
    have h5 : (cIO.lib.carrier ioError == Srt.float) = false := by decide +kernel
    cases l <;> simp [dvOK, h1, h2, h5, k1, k2, k3, k4, k5] at hd
  | map s es =>
    obtain ⟨k, vs, hk, -, -, -, hs⟩ := sortOf_mapS_iff.mp h
    subst hs
    rw [cIO_notColl] at hk; cases hk
  | set s es =>
    obtain ⟨k, hk, -, -, -, hs⟩ := sortOf_setS.mp h
    subst hs
    rw [cIO_notColl] at hk; cases hk
  | list s es =>
    obtain ⟨k, hk, -, -, hs⟩ := sortOf_listS.mp h
    subst hs
    rw [cIO_notColl] at hk; cases hk

/-- `coreOK`, a sort in `valueSorts`, and no value of it. -/
theorem valueSorts_no_value :
    ∃ (c : Semantics) (s : Srt), c.coreOK = true ∧ c.valueSorts.contains s = true ∧
      ∀ v, c.sortOf v ≠ some s :=
  ⟨cIO, ioError, cIO_core, cIO_valueSorts, cIO_no_value⟩

/-! ## A sort without a value outside `valueSorts` -/

abbrev sS : Srt := nRegSorts + 2

def cLoop : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt", "S"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbls"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt, sS]
    ctors :=
      [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
       ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
       ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩,
       ⟨nRegSyms + 5, [sS], sS⟩]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem cLoop_core : cLoop.coreOK = true := by decide_cheap

theorem cLoop_valueSorts : cLoop.valueSorts.contains sS = false ∧ cLoop.valueless = [sS] ∧
    [Srt.int, Srt.kitem, Srt.k, Srt.top, nRegSorts].all cLoop.valueSorts.contains = true := by decide +kernel

/-! ## `Semantics.hasValue` on the same definitions

`hasValue` counts no seed sort as having a value: a sort is accepted for a probe literal, an empty
collection, or a constructor or injection over accepted sorts. -/

/-- IOError of `cIO`, which has no value (`cIO_no_value`), is outside; Int, String, KItem (the
injection of an Int), K, the cell sorts and the builtin collection sorts are inside. -/
theorem cIO_hasValue : cIO.hasValue ioError = false ∧
    [Srt.int, Srt.bool, Srt.string, Srt.kitem, Srt.k, Srt.top, nRegSorts, nRegSorts + 1, Srt.map, Srt.set,
      Srt.list].all cIO.hasValue = true := by decide +kernel

/-- S of `syntax S ::= s(S)` is outside. -/
theorem cLoop_hasValue : cLoop.hasValue sS = false ∧
    [Srt.int, Srt.kitem, Srt.k, Srt.top, nRegSorts].all cLoop.hasValue = true := by decide +kernel

/-- `cIO` with a constructor without arguments of IOError (K-IO's `#EOF` is one): IOError is inside,
and so has a value (`hasValue_value`). -/
def cIOk : Semantics := { cIO with lib := { cIO.lib with ctors := [⟨regSymNames.idxOf "Lbl'Hash'EOF", [], ioError⟩] } }

theorem cIOk_hasValue : cIOk.hasValue ioError = true := by decide +kernel

/-- A token sort (the literal `""`), a sort hooked to the carrier Int (the literal `0`), and a cell
map sort with a value sort (its empty map) are inside; a map sort without a value sort is outside,
as `sortOf` gives it no map. -/
def cLit : Semantics :=
  { cIO with
    lib := { cIO.lib with tokenSorts := [nRegSorts + 2], carriers := [(nRegSorts + 3, Srt.int)] }
    colls := [⟨nRegSorts + 4, .map, Srt.int, some Srt.int, nRegSyms + 4, nRegSyms + 5, nRegSyms + 6⟩,
              ⟨nRegSorts + 5, .map, Srt.int, none, nRegSyms + 7, nRegSyms + 8, nRegSyms + 9⟩] }

theorem cLit_hasValue : [nRegSorts + 2, nRegSorts + 3, nRegSorts + 4].all cLit.hasValue = true ∧
    cLit.hasValue (nRegSorts + 5) = false ∧ cLit.hasLit (nRegSorts + 2) = true ∧
    cLit.hasLit (nRegSorts + 3) = true ∧ cLit.hasEmpty (nRegSorts + 4) = true := by decide +kernel

/-- On `cIO`, a definition with `coreOK`, the accepted sorts have values. -/
theorem cIO_values : ∀ s ∈ [Srt.string, Srt.kitem, Srt.k, Srt.top], ∃ v, cIO.sortOf v = some s := by
  intro s hs
  refine hasValue_value cIO_core ?_
  revert s
  decide +kernel

end KCore.ValueSortsNoValue

#print axioms KCore.hasValue_value
#print axioms KCore.ValueSortsNoValue.cIO_hasValue
#print axioms KCore.ValueSortsNoValue.cIO_values

#print axioms KCore.ValueSortsNoValue.valueSorts_no_value
#print axioms KCore.ValueSortsNoValue.cLoop_core
#print axioms KCore.ValueSortsNoValue.cLoop_valueSorts
