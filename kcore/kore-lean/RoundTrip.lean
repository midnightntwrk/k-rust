/-
  Round-trip driver (new in the k-rust port).
  Released under MIT license as described in the file LICENSE.

  `lake exe roundtrip FILE…` (and `lake test`, with the files of `testDriverArgs`):
  first a few unit checks of the reader, then for each file
  parse → print → parse, requiring equal ASTs,
  and requiring the token streams of the file and of the printed text to be equal.
-/

import KoreParser

open Kore

def ms (t₀ t₁ : Nat) : String :=
  let d := (t₁ - t₀) / 100000
  s!"{d / 10}.{d % 10} ms"

/-- The first index where two token arrays differ, if any. -/
def firstDifference (a b : Array Token) : Option Nat := Id.run do
  for i in [0:max a.size b.size] do
    if a[i]? != b[i]? then return some i
  return none

def context (a : Array Token) (i : Nat) : String :=
  " ".intercalate ((a.extract (i - 5) (i + 6)).toList.map toString)

/-- Unit checks of the reader on constructs the round-trip inputs may lack. -/
def parsesTo (input : String) (p : Pattern) : Bool :=
  match parsePattern input with
  | .ok q => q == p
  | .error _ => false

def unitChecks : List (String × Bool) :=
  let R : KSort := .var ⟨⟨⟨"R"⟩⟩⟩
  let S : KSort := .ctor ⟨⟨"SortString"⟩⟩ []
  let X : SVar := ⟨⟨⟨"X"⟩⟩, R⟩
  [ ("escapes decode to code points",
      parsesTo "\\dv{SortString{}}(\"a\\n\\t\\f\\r\\\"\\\\\\x41\\u00e9\\U0001F600 ~\")"
        (.dv S "a\n\t\x0c\r\"\\Aé😀 ~"))
  , ("escapes print canonically",
      Printer.strLit "a\n\x01éā😀" == "\"a\\n\\x01\\xe9\\u0101\\U0001f600\"")
  , ("raw non-ASCII in a literal is rejected", (parsePattern "\"é\"").toOption.isNone)
  , ("surrogate escape is rejected", (parsePattern "\"\\ud800\"").toOption.isNone)
  , ("unknown escape is rejected", (parsePattern "\"\\q\"").toOption.isNone)
  , ("\\nu is not \\mu",
      parsesTo "\\nu{}(@X:R, @X:R)" (.nu X (.var (.svar X))))
  , ("\\forall is not \\exists",
      parsesTo "\\forall{R}(x:R, x:R)"
        (.forall R ⟨⟨⟨"x"⟩⟩, R⟩ (.var (.evar ⟨⟨⟨"x"⟩⟩, R⟩))))
  , ("R is a sort variable, R{} a sort constructor",
      parsesTo "\\top{R}()" (.top R)
        && parsesTo "\\top{R{}}()" (.top (.ctor ⟨⟨"R"⟩⟩ [])))
  , ("n-ary \\and", parsesTo "\\and{R}(\\top{R}(), \\top{R}(), \\top{R}())"
        (.and R [.top R, .top R, .top R]))
  , ("nullary \\or", parsesTo "\\or{R}()" (.or R []))
  , ("identifiers carry ' and -", parsesTo "Lbl'Unds'-x1{}()"
        (.app ⟨⟨"Lbl'Unds'-x1"⟩⟩ [] []))
  , ("\\-prefixed symbol", parsesTo "\\foo{}()" (.app ⟨⟨"\\foo"⟩⟩ [] []))
  , ("comments are whitespace", parsesTo "/* a */ \\top{R}( // b\n)" (.top R))
  , ("keywords are not identifiers", (parsePattern "axiom{}()").toOption.isNone)
  , ("trailing input is rejected", (parseDefinition "[] module M endmodule [] x").toOption.isNone)
  ]

def roundTrip (path : String) : IO Bool := do
  let input ← IO.FS.readFile path
  let t₀ ← IO.monoNanosNow
  let some d ← (match parseDefinition input with
      | .ok d => pure (some d)
      | .error e => do IO.eprintln s!"FAIL {path}: parse: {e}"; pure none)
    | return false
  let t₁ ← IO.monoNanosNow
  let printed := Printer.definition d
  let t₂ ← IO.monoNanosNow
  let some d' ← (match parseDefinition printed with
      | .ok d => pure (some d)
      | .error e => do IO.eprintln s!"FAIL {path}: reparse of printed text: {e}"; pure none)
    | return false
  if d ≠ d' then
    IO.eprintln s!"FAIL {path}: parse (print (parse f)) ≠ parse f"
    return false
  let .ok tf := tokenize input | IO.eprintln s!"FAIL {path}: tokenize input"; return false
  let .ok tp := tokenize printed | IO.eprintln s!"FAIL {path}: tokenize printed"; return false
  if let some i := firstDifference tf tp then
    IO.eprintln s!"FAIL {path}: token {i} differs:\n  file:    {context tf i}\n  printed: {context tp i}"
    return false
  let byTop := ", ".intercalate (d.axiomsByTopConnective.map fun (c, n) => s!"{c} {n}")
  IO.println s!"ok   {path}
     {input.utf8ByteSize} bytes, {tf.size} tokens, {d.modules.length} modules, {d.sentenceCount} sentences, {d.axioms.length} axioms ({d.axiomNodes} pattern nodes), {d.claims.length} claims
     axioms by top connective: {byTop}
     parse {ms t₀ t₁}, print {ms t₁ t₂}"
  return true

def main (args : List String) : IO UInt32 := do
  let mut failures := 0
  for (name, ok) in unitChecks do
    if !ok then
      IO.eprintln s!"FAIL unit check: {name}"
      failures := failures + 1
  IO.println s!"unit checks: {unitChecks.length - failures}/{unitChecks.length} passed"
  for path in args do
    if !(← roundTrip path) then failures := failures + 1
  IO.println (if failures == 0 then "all passed" else s!"{failures} failure(s)")
  return if failures == 0 then 0 else 1
