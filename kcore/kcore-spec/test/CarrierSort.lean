/-
  A sort hooked under its own name to a library carrier (`syntax MyInt [hook(INT.Int)]`, fixture
  test/constructs/fixtures/e5-hooked-int: `+My` hooked to INT.add, `sum(X, Y) => X +My Y`). Run from
  the package root: `lake env lean test/CarrierSort.lean`. Kernel-checked (`decide +kernel`).

  What the text states: the sort's values are the integers (INT.Int's prose), `+My` is addition
  (INT.add's), and no sentence relates MyInt to Int, so the two are apart. Its no-junk sentence is
  `\or{SortMyInt{}}(\top, \bottom)`, which states nothing: the sort is no constructor sort
  (`consSorts`) and not confined.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The own sort of the fixture: the first own sort. -/
def myInt : Srt := nRegSorts
/-- `+My`, the first own symbol after the sort predicate. -/
def plusMy : Sym := nRegSyms + 1

/-- A semantics with one own sort hooked to Int and `+My` implemented by INT.add. -/
def carrierSem : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool], carriers := [(myInt, Srt.int)] }
  sortNames := ["MyInt"]
  symNames := ["LblisMyInt", "LblplusMy"]
  userSorts := [myInt]
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨plusMy, [myInt, myInt], myInt⟩, impl := some intAdd }]

def lit (s : Srt) (i : Int) : GroundTerm := .dv s (.int i)

/-- The carrier sort is no constructor sort, not confined, a distinct sort, and admitted by
`paramsPlain` and `carriersOK`; its literals are Int's, at its own sort. -/
example : (Faithful.consSorts carrierSem).contains myInt = false ∧ carrierSem.confined myInt = false ∧
    (Faithful.distinctSorts carrierSem).contains myInt = true ∧ carrierSem.paramsPlain = true ∧
    carrierSem.carriersOK = true ∧
    carrierSem.sortOf (lit myInt 5) = some myInt ∧ carrierSem.sortOf (.dv myInt (.bool true)) = none := by
  decide +kernel

/-- `2 +My 3` is `\dv{SortMyInt{}}("5")` (INT.add's prose; the result sort from the declaration). -/
example : (match carrierSem.paramVal plusMy [lit myInt 2, lit myInt 3] with
    | some v => GroundTerm.cmp v (lit myInt 5) == .eq
    | none => false) = true := by decide +kernel

/-- `\dv{SortMyInt{}}("5")` and `\dv{SortInt{}}("5")` are distinct values, injected into KItem as
two distinct values of KItem (no sentence equates them). -/
example : GroundTerm.cmp (.inj myInt Srt.kitem (lit myInt 5)) (.inj Srt.int Srt.kitem (lit Srt.int 5)) != .eq := by
  decide +kernel
