/-
  The two notes of a rule that the class reads from the names (`Parse.classify`, `Parse.namesOf`),
  each against the rule the reader reads. Run from the package root:
  `lake env lean -j1 test/ClassNamesNotes.lean`.
  - `andTermsCut`, on `f2-examples/mlandt`, `mlandc`, `mlandv` and `mlorand` (the texts of
    e3-ml-rule-rhs-and-term, -and-ctor, -and-var and e3-ml-rule-lhs-or-rhs-and): for each rewrite
    axiom of the user's source, its class, its notes (`connNotes`, the account's connective
    readings) and, for each rule it gives (`scanRewrites`), whether the rule read (`ruleOf`) is not
    the rule read without the cut (`ruleBodyUncut`). The notes hold `andTermsCut` exactly where some
    rule took the cut, and the class is `read andTermsCut` where that note is the first; on
    `mlorand` the first note is `orSplit` and both rules took the cut.
  - `keyFunctionAsMember`, on `f2-examples/keyfn`, that text with `B` renamed in the `<base>` cell
    (the key's argument then bound only inside the key), `keyfn-both` and `keyfn-partial`: for each
    rewrite axiom of the user's source, its class and, for each rule it gives, whether the rule read
    holds more variables than the rule read with names that list no function (`keyFns := []`), the
    fresh variable `keyCut` adds. The class is `read keyFunctionAsMember` exactly where a rule took
    the key, and the account's line lists those axioms (`keysAsMember`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The rewrite axioms of the user's source in the last module of `k`, by position in it. -/
def userRewrites (k : Kore.Definition) : List (Nat × Kore.Axiom) :=
  match k.modules.getLast? with
  | none => []
  | some m => m.sentences.zipIdx.filterMap fun (s, i) => match s with
    | .axiom a => if (Parse.scanRewrite s).isSome && Parse.isUserSource a.attributes then some (i, a) else none
    | _ => none

/-- The rule a rewrite axiom gives, read by `rd`, printed; `none` where it is refused. -/
def ruleStr (rd : Kore.Axiom → Parse.Rd (Rule × RulePres)) (b : Kore.Axiom) : Option String :=
  (rd b).toOption.map fun (r, _) => reprStr r

/-- Per rewrite axiom of the user's source: its class, its notes, whether each rule it gives took the
cut, and whether the notes hold `andTermsCut` exactly where one did. -/
def cutVerdict (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  let N := Parse.namesOf k
  let lines := (userRewrites k).map fun (i, a) =>
    let cuts := (Parse.scanRewrites (.axiom a)).map fun b =>
      ruleStr (Parse.ruleOf N "") b != ruleStr (Parse.ruleBodyUncut N "") b
    let notes := Parse.connNotes N a
    s!"{i}: {(Parse.classify N (.axiom a)).name}; notes {notes.map (·.name)}; cut {cuts}; agree {notes.contains .andTermsCut == cuts.any id}"
  return "\n".intercalate lines

/--
info: 298: read andTermsCut; notes [andTermsCut]; cut [true]; agree true
200: read andTermsCut; notes [andTermsCut]; cut [true]; agree true
194: read andTermsCut; notes [andTermsCut]; cut [true]; agree true
200: read orSplit; notes [orSplit, andTermsCut]; cut [true, true]; agree true
-/
#guard_msgs in
#eval show IO Unit from do
  for f in ["mlandt", "mlandc", "mlandv", "mlorand"] do
    IO.println (← cutVerdict s!"f2-examples/{f}.kompile.kore")

/-- Per rewrite axiom of the user's source: its class, whether each rule it gives took a map key
(the rule read holds more variables than with no function listed), and whether the class is
`read keyFunctionAsMember` exactly where one did; then the account's line. -/
def keyVerdict (path : String) (edit : String → String := id) : IO String := do
  let .ok k := Kore.parseDefinition (edit (← IO.FS.readFile path)) | return "KORE read error"
  let N := Parse.namesOf k
  let N₀ : Parse.Names := { N with keyFns := [] }
  let lines := (userRewrites k).map fun (i, a) =>
    let took := (Parse.scanRewrites (.axiom a)).map fun b =>
      match Parse.ruleOf N "" b, Parse.ruleOf N₀ "" b with
      | .ok (r, _), .ok (r₀, _) => r.vars.length != r₀.vars.length
      | _, _ => false
    let cl := Parse.classify N (.axiom a)
    s!"{i}: {cl.name}; key {took}; agree {(cl == .readAs .keyFunctionAsMember) == took.any id}"
  return "\n".intercalate (lines ++ [s!"keys {(Parse.keysAsMember k).map (·.2)}"])

/--
info: 315: read keyFunctionAsMember; key [true]; agree true
keys [[Lblidx]]
315: read; key [false]; agree true
keys []
319: read keyFunctionAsMember; key [true]; agree true
keys [[Lblidx]]
358: read keyFunctionAsMember; key [true]; agree true
359: read; key [false]; agree true
360: read keyFunctionAsMember; key [true]; agree true
361: read keyFunctionAsMember; key [true]; agree true
keys [[Lblpidx], [Lblkf], [Lblpidx]]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← keyVerdict "f2-examples/keyfn.kompile.kore")
  IO.println (← keyVerdict "f2-examples/keyfn.kompile.kore" fun s =>
    s.replace "Lbl'-LT-'base'-GT-'{}(VarB:SortInt{})" "Lbl'-LT-'base'-GT-'{}(VarB2:SortInt{})")
  IO.println (← keyVerdict "f2-examples/keyfn-both.kompile.kore")
  IO.println (← keyVerdict "f2-examples/keyfn-partial.kompile.kore")
