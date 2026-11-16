/-
  A symbol with laws and a law of no collection, read from K 7.1.337 kompile's own KORE: each is
  refused by name. Run from the package root: `lake env lean test/OpenGenerator.lean`.
  - `f2-examples/commctor.kompile.kore` (`commctor.k`): `Exp "&" Exp [comm]` and `Exp "|" Exp
    [assoc]`, which kompile declares `functional` alone, neither `function` nor `constructor`, and
    states `|`'s associativity as an axiom (no axiom for `&`'s commutativity). Each symbol is
    refused (`openGenerator`), the law axioms the text states of it named; it is not read as a
    function.
  - `f2-examples/lawfn.kompile.kore` (`lawfn.k`): `Exp "+" Exp [function, assoc]`, whose
    associativity kompile states as an axiom. The text is read; the account refuses the axiom
    (`lawAxiom`), `+` being no collection's concatenation. The laws of `_Map_`, `_Set_` and
    `_List_` the text states, and `_Set_`'s idempotence, are not refused.
  - `f2-examples/projuser.kompile.kore`: no law refused.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The refusals of the text at `path` with the reason `r`. -/
def refusalsOf (path : String) (r : Parse.RefusalReason) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => return ((Parse.refusals k).filter (·.reason == r)).map Parse.Refusal.toText

/-- The account's law refusals of the text at `path` (`Parse.lawUnmatched`), or its first refusal. -/
def lawRefusals (path : String) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => return match Parse.parse k with
    | .ok d => (Parse.lawUnmatched k d).map Parse.Refusal.toText
    | .error r => [s!"refused: {r.toText}"]

/--
info: [sentence 62 (Lbland): openGenerator (Lbland: neither function nor constructor; law axioms: none), sentence 89 (Lblor): openGenerator (Lblor: neither function nor constructor; law axioms: assoc)]
[sentence 267 (Lblplus): lawAxiom (Lblplus: assoc)]
[]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← refusalsOf "f2-examples/commctor.kompile.kore" .openGenerator)
  IO.println (← lawRefusals "f2-examples/lawfn.kompile.kore")
  IO.println (← lawRefusals "f2-examples/projuser.kompile.kore")
