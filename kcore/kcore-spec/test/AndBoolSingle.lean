/-
  An equation's condition `\and{SortBool{}}(B₁, B₂)`, read from K 7.1.337 kompile's KORE of
  `f2-examples/ens.k` (`half(N) => N /Int 2 ensures N >=Int 0`, half's only equation) with its
  `ensures` edited. Run from the package root: `lake env lean test/AndBoolSingle.lean`.
  `\and{SortBool{}}` is an intersection, `B₁ ∩ B₂ = {true}`, which is `⌈B₁ = true⌉ ∧ ⌈B₂ = true⌉`
  where each Bᵢ has at most one element and not where one has `true` and another element.
  - `ensures (N >=Int 0) #And (N >=Int 0)`: `_>=Int_` has a `functional` axiom in the text, so each
    conjunct has one element: read (`andAtBool`).
  - `ensures (N >=Int 0) #And (half(N) >=Int 0)`: `half` has no `functional` axiom (it is not
    declared total), so `half(N) >=Int 0` may have two elements: refused `patternConnective`
    (`\and`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path`, edited by `edit`: read, or the refusal. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).length}"
    | .error r => s!"{r.reason.name} {r.detail}"

/-- The `ensures` of `half`'s equation, as kompile writes its first conjunct's line. -/
def ensLine : String := "        Lbl'Unds-GT-Eqls'Int'Unds'{}(VarN:SortInt{},\\dv{SortInt{}}(\"0\")),\n"

/-- That `ensures` conjoined with `b`. -/
def withConj (b : String) (s : String) : String :=
  s.replace ensLine
    s!"        \\and\{SortBool\{}}(Lbl'Unds-GT-Eqls'Int'Unds'\{}(VarN:SortInt\{},\\dv\{SortInt\{}}(\"0\")), {b}),\n"

/--
info: read; unaccounted 0
read; unaccounted 0
patternConnective \and
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ens.kompile.kore")
  IO.println (← verdict "f2-examples/ens.kompile.kore"
    (withConj "Lbl'Unds-GT-Eqls'Int'Unds'{}(VarN:SortInt{},\\dv{SortInt{}}(\"0\"))"))
  IO.println (← verdict "f2-examples/ens.kompile.kore"
    (withConj "Lbl'Unds-GT-Eqls'Int'Unds'{}(Lblhalf{}(VarN:SortInt{}),\\dv{SortInt{}}(\"0\"))"))
