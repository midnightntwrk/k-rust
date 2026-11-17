/-
  Open generators and the laws of functions, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/OpenGenerator.lean`.
  - `f2-examples/commctor.kompile.kore` (`commctor.k`): `Exp "&" Exp [comm]` and `Exp "|" Exp
    [assoc]`, which kompile declares `functional` alone, neither `function` nor `constructor`,
    lists among Exp's generators in its no-junk axiom, and states `|`'s associativity as an axiom
    (no axiom for `&`'s commutativity). Exp's one constructor `x` is nullary, so each is read as an
    open generator (`ParamSig.raw`, `Parse.openGenFault` none), not as a function; nothing is
    refused `openGenerator`, and Exp's no-junk axiom is the one `Γ` states with them among its
    generators (`Parse.uninduced` empty). `|`'s associativity axiom is the sentence `Γ` holds for
    an open generator with `assoc` (`Parse.openAssocAx`, `Faithful.assocAxK`): it is read
    (`ParamSig.assoc`, `Parse.openLawSentences`) and nothing is refused by `lawUnmatched`.
  - `f2-examples/lawfn.kompile.kore` (`lawfn.k`): `Exp "+" Exp [function, assoc]`, whose
    associativity kompile states as an axiom. The text is read, the axiom read as the law
    `plus(plus(K1, K2), K3) = plus(K1, plus(K2, K3))` of `Presentation.laws` (`Parse.fnLawOf`,
    stated at values under `FnLaws`; its sides of one sort, `Parse.fnLawSorted`), and nothing
    refused by `lawUnmatched`, nor the laws of
    `_Map_`, `_Set_` and `_List_` the text states, nor `_Set_`'s idempotence.
  - `f2-examples/projuser.kompile.kore`: no law read, none refused.
  - `f2-examples/openmixedunheld.kompile.kore`: a sort whose only values apply an open generator,
    where a rule needs a value of it: refused `unheldVariable` (the last section).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's sort check of a law is `lawSorted`. -/
example : Parse.fnLawSorted = lawSorted := rfl

/-- The law sentences the reader recognises for an open generator are those `Γ` holds for it. -/
example (c : Semantics) (k : ParamSig) :
    Faithful.assocAxK c k = Parse.openAssocAx (c.symName k.sig.name) (KoreAML.srt (c.sortName k.sig.result)) := rfl
example (c : Semantics) (k : ParamSig) :
    Faithful.idemAxK c k = Parse.openIdemAx (c.symName k.sig.name) (KoreAML.srt (c.sortName k.sig.result)) := rfl

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
  let ol := (Parse.openLawSentences k d).map (fun (i, h, ks) => s!"{i} {h} {ks}")
  let ui := (Parse.uninduced k d).map Parse.Refusal.toText
  s!"open generators: {og}" :: s!"laws: {ls} at {lsAt}" :: s!"open laws at: {ol}" ::
    s!"lawUnmatched: {lu}" :: s!"uninduced: {ui}" :: []

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
[open generators: [Lbland : [Exp, Exp] → Exp assoc false idem false, Lblor : [Exp, Exp] → Exp assoc true idem false], laws: [] at [], open laws at: [186 Lblor [assoc]], lawUnmatched: [], uninduced: []]
[open generators: [], laws: [[Exp, Exp, Exp]] at [267 Lblplus [assoc]], open laws at: [], lawUnmatched: [], uninduced: []]
[open generators: [], laws: [] at [], open laws at: [], lawUnmatched: [], uninduced: []]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← refusalsOf "f2-examples/commctor.kompile.kore" .openGenerator)
  IO.println (← readOf "f2-examples/commctor.kompile.kore")
  IO.println (← readOf "f2-examples/lawfn.kompile.kore")
  IO.println (← readOf "f2-examples/projuser.kompile.kore")

/-! ## A sort whose only values apply an open generator

`f2-examples/openmixedunheld.kompile.kore` (fixture e2-open-mixed-unheld): e2-open-mixed's sorts,
`A ::= x | y` and `B ::= A "&" A` with `&` an open generator, and two rules that need a value of B
where they are read without a variable of the axiom: `c(_:B) #Or e() => d(x)` (the rule of the
disjunct `e()` does not hold the variable) and `g(#Exists Z:B. x) => d(y)`. Every value of B
applies `&`, and at an interpretation that answers `&` outside B, B has no value; the reader
exhibits a value only where it applies no open generator (`Parse.rawFree_of_exhibit`), exhibits
none of B, and refuses both axioms `unheldVariable`. Where it exhibits a value, `Γ` entails an
element of the sort at every interpretation (`Faithful.inhabited_of_exhibit_withHooks`). -/

example := @Faithful.inhabited_of_exhibit_withHooks

/--
info: sentence 229 (Lbl'-LT-'generatedTop'-GT-'): unheldVariable (Var'Unds'Gen0:B: a variable of the axiom that a rule read from it does not hold, of a sort of which the reader exhibits no value: the axiom holds for every element of the sort, so where the sort has none it states nothing while the rule would step, and Γ entails neither an element of the sort nor its emptiness (the text's sorted theory gives every sort an element, which Γ does not state))
sentence 230 (Lbl'-LT-'generatedTop'-GT-'): unheldVariable (VarZ':B: a variable of the axiom that a rule read from it does not hold, of a sort of which the reader exhibits no value: the axiom holds for every element of the sort, so where the sort has none it states nothing while the rule would step, and Γ entails neither an element of the sort nor its emptiness (the text's sorted theory gives every sort an element, which Γ does not state))
-/
#guard_msgs in
#eval show IO Unit from do
  for r in ← refusalsOf "f2-examples/openmixedunheld.kompile.kore" .unheldVariable do
    IO.println r

/-! ## An open generator in a left side

`f2-examples/openrec.kompile.kore` (fixture e2-open-rec: `B ::= "e" | B "&" B [comm]`,
`<k> c(X & Y) => d(X) </k>`) and `f2-examples/openmixed.kompile.kore` (fixture e2-open-mixed:
`A ::= "x" | "y"`, `B ::= A "&" A [comm]`, the same rule). In each, `&` is read as an open generator
without a law (kompile writes no sentence for `comm`), and the rule's left side applies it to
variables: the account refuses the rule `openGeneratorPattern`, not `functionInPattern`, the detail
naming `&`, its sort B and the reason that applies at B. In e2-open-rec B is recursive through `&`
itself, so not confined: the arguments that match depend on elements of B the text does not name
(R-a). In e2-open-mixed B is confined (its one generator `&` takes two arguments of A, whose
generators are the nullary `x` and `y`): the arguments that match are values, the value's preimage
under the interpretation's graph, which the semantics does not build (R-c). -/

/-- The text at `path` read: its open generators, whether each of its sorts is confined, and the
left sides the account refuses for applying a function symbol or an open generator. -/
def patternsOf (path : String) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => return match Parse.parse k with
    | .ok d =>
      let c := d.sem
      let og := (c.params.filter (·.raw)).map (fun p =>
        c.symName p.sig.name ++ " : " ++ toString (p.sig.args.map c.sortName) ++ " → " ++
          c.sortName p.sig.result ++ s!" assoc {p.assoc} idem {p.idem} confined {c.confined p.sig.result}")
      let fp := (Parse.functionInPattern k d).map Parse.Refusal.toText
      let gp := (Parse.openGeneratorInPattern k d).map Parse.Refusal.toText
      s!"open generators: {og}" :: s!"functionInPattern: {fp}" :: s!"openGeneratorInPattern: {gp}" :: []
    | .error r => [s!"refused: {r.toText}"]

/--
info: open generators: [Lbland : [B, B] → B assoc false idem false confined false]
functionInPattern: []
openGeneratorInPattern: [sentence 210 (Lbl'-LT-'generatedTop'-GT-'): openGeneratorPattern (Lbland: its sort B is recursive or reaches an unconfined sort: the arguments it matches depend on elements of B the text does not name)]
-/
#guard_msgs in
#eval show IO Unit from do
  for l in ← patternsOf "f2-examples/openrec.kompile.kore" do IO.println l

/-! e2-open-mixed: `&` across sorts (`A A → B`), read as a raw parameter without a law (`comm` has
no sentence); B is confined, and the rule's left side is refused with the second reason. -/

/--
info: open generators: [Lbland : [A, A] → B assoc false idem false confined true]
functionInPattern: []
openGeneratorInPattern: [sentence 219 (Lbl'-LT-'generatedTop'-GT-'): openGeneratorPattern (Lbland: its sort B is confined: the arguments it matches at a value are the value's preimage under the interpretation's graph, which the semantics does not build)]
-/
#guard_msgs in
#eval show IO Unit from do
  for l in ← patternsOf "f2-examples/openmixed.kompile.kore" do IO.println l
