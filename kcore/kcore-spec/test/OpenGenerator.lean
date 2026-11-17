/-
  Open generators and the laws of functions, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/OpenGenerator.lean`.
  - `f2-examples/commctor.kompile.kore` (`commctor.k`): `Exp "&" Exp [comm]` and `Exp "|" Exp
    [assoc]`, which kompile declares `functional` alone, neither `function` nor `constructor`,
    lists among Exp's generators in its no-junk axiom, and states `|`'s associativity as an axiom
    (no axiom for `&`'s commutativity). Exp's one constructor `x` is nullary, so each is read as an
    open generator (`ParamSig.raw`, `Parse.openGenFault` none), not as a function; nothing is
    refused `openGenerator`, and Exp's no-junk axiom is the one `Γ` states with them among its
    generators (`Parse.uninduced` empty). The account refuses `|`'s associativity axiom
    (`lawAxiom`): no law of an open generator is read.
  - `f2-examples/lawfn.kompile.kore` (`lawfn.k`): `Exp "+" Exp [function, assoc]`, whose
    associativity kompile states as an axiom. The text is read, the axiom read as the law
    `plus(plus(K1, K2), K3) = plus(K1, plus(K2, K3))` of `Presentation.laws` (`Parse.fnLawOf`,
    stated at values under `FnLaws`; its sides of one sort, `Parse.fnLawSorted`), and nothing
    refused by `lawUnmatched`, nor the laws of
    `_Map_`, `_Set_` and `_List_` the text states, nor `_Set_`'s idempotence.
  - `f2-examples/projuser.kompile.kore`: no law read, none refused.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's sort check of a law is `lawSorted`. -/
example : Parse.fnLawSorted = lawSorted := rfl

/-- The refusals of the text at `path` with the reason `r`. -/
def refusalsOf (path : String) (r : Parse.RefusalReason) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => return ((Parse.refusals k).filter (·.reason == r)).map Parse.Refusal.toText

/-- What `readOf` prints of the definition `d` read from `k`. -/
def readLines (k : Kore.Definition) (d : Definition) : List String :=
  let c := d.sem
  let og := (c.params.filter (·.raw)).map (fun p =>
    c.symName p.sig.name ++ " : " ++ toString (p.sig.args.map c.sortName) ++ " → " ++
      c.sortName p.sig.result ++ s!" assoc {p.assoc} idem {p.idem}")
  let ls := d.laws.map (fun l => l.vars.map c.sortName)
  let lsAt := (Parse.fnLawSentences k d).map (fun (i, h, ks) => s!"{i} {h} {ks}")
  let lu := (Parse.lawUnmatched k d).map Parse.Refusal.toText
  let ui := (Parse.uninduced k d).map Parse.Refusal.toText
  s!"open generators: {og}" :: s!"laws: {ls} at {lsAt}" :: s!"lawUnmatched: {lu}" :: s!"uninduced: {ui}" :: []

/-- The text at `path` read: its open generators (name, argument and result sorts, the laws
read), its laws of functions (the law's variables' sorts; the symbol and laws of each sentence),
the account's law refusals (`Parse.lawUnmatched`) and the inert constructor axioms it does not
induce (`Parse.uninduced`); or its first refusal. -/
def readOf (path : String) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => return match Parse.parse k with
    | .ok d => readLines k d
    | .error r => [s!"refused: {r.toText}"]

/--
info: []
[open generators: [Lbland : [Exp, Exp] → Exp assoc false idem false, Lblor : [Exp, Exp] → Exp assoc false idem false], laws: [] at [], lawUnmatched: [sentence 186 (Lblor): lawAxiom (Lblor: assoc)], uninduced: []]
[open generators: [], laws: [[Exp, Exp, Exp]] at [267 Lblplus [assoc]], lawUnmatched: [], uninduced: []]
[open generators: [], laws: [] at [], lawUnmatched: [], uninduced: []]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← refusalsOf "f2-examples/commctor.kompile.kore" .openGenerator)
  IO.println (← readOf "f2-examples/commctor.kompile.kore")
  IO.println (← readOf "f2-examples/lawfn.kompile.kore")
  IO.println (← readOf "f2-examples/projuser.kompile.kore")
