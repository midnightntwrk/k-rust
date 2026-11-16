/-
  Sorts without a value, read from K 7.1.337 kompile's KORE. Run from the package root:
  `lake env lean test/EmptySort.lean`.
  - `f2-examples/emptysort.kompile.kore` (`emptysort.k`): `syntax Empty` (no production) and
    `syntax Loop ::= loop(Loop)` (no production with a base case): no finite term has either sort.
    `f(Empty) : Bool` is a function with no equation; `g(KItem) : Int` has `g(_:Empty) => 1` and
    `g(_) => 0 [owise]`; the rule `<k> go(I) => done(g(I)) </k>`.
  - Read with nothing unaccounted or refused by the account; `wf` holds (no sort is required to have
    a value) and the account's note names `Loop` and `Empty` as the sorts without a value. `emit`
    does not give the text back up to sentence order (`Reordered` false, decided natively), as for
    every text kompile 7.1.337 writes (`test/roundtrip.expected`: all of them `differs` or
    `cannot`; `emit` writes the shape of the corpus's texts, other attributes and prelude sentences),
    so the text is not `Tied`; the tie is not what this case is about.
  - No value has sort Empty, so `g`'s first equation applies to none: the compiled step function
    takes `<k> go(i) </k>` to `<k> done(0) </k>` at each i tried (natively).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict, `wf`, the sorts without a value and the tie's `Reordered`, natively. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let unacc := (Parse.unconsumed k d).length + (Parse.uninduced k d).length
        s!"read; unaccounted or uninduced {unacc}; refused by the account {(Parse.accountRefusals k d).length}; wf {wf d}; failing {(d.report.filter (!·.2)).map (·.1)}; without a value {d.sem.valueless.map d.sem.sortName}; inhabited {d.sem.inhabited}; reordered {decide (KoreAML.Reordered d.emit k)}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; unaccounted or uninduced 0; refused by the account 0; wf true; failing []; without a value [Loop, Empty]; inhabited false; reordered false
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/emptysort.kompile.kore")

/-- The successors of `<k> go(i) </k>` by the compiled step function, for each i of `is`. -/
def steps (is : List Int) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/emptysort.kompile.kore") | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  let c := d.sem
  let sym := fun (n : String) => ((List.range (nRegSyms + c.symNames.length)).find? (c.symName · == n)).getD 0
  let srt := fun (n : String) => ((List.range (nRegSorts + c.sortNames.length)).find? (c.sortName · == n)).getD 0
  let cfg := fun (t : GroundTerm) => GroundTerm.ctor topLabel
    [.ctor (sym "Lbl'-LT-'k'-GT-'") [.ctor kseq [.inj (srt "Pgm") Srt.kitem t, .ctor dotk []]],
     .ctor counterLabel [.dv Srt.int (.int 0)]]
  let show1 : GroundTerm → String
    | .ctor _ [.ctor _ [.ctor _ [.inj _ _ (.ctor f [.dv _ (.int i)]), _]], _] => s!"{c.symName f}({i})"
    | _ => "?"
  return ", ".intercalate (is.map fun i =>
    s!"go({i}) ⟶ {(Exec.successorsN c 100 (cfg (.ctor (sym "Lblgo") [.dv Srt.int (.int i)]))).map show1}")

/--
info: go(-2) ⟶ [Lbldone(0)], go(0) ⟶ [Lbldone(0)], go(1) ⟶ [Lbldone(0)], go(7) ⟶ [Lbldone(0)]
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← steps [-2, 0, 1, 7])

/-- Neither sort is confined: Empty has no generator, so the text holds no sentence about which
elements it has; Loop's one generator takes a Loop, confined at no smaller depth. -/
def confinedSorts : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/emptysort.kompile.kore") | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  let c := d.sem
  let srt := fun (n : String) => ((List.range (nRegSorts + c.sortNames.length)).find? (c.sortName · == n)).getD 0
  return s!"confined: Empty {c.confined (srt "Empty")}, Loop {c.confined (srt "Loop")}"

/--
info: confined: Empty false, Loop false
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← confinedSorts)

/-- The no-junk items of `Γ`: none for Empty, which has no generator (the text writes no no-junk
sentence for it); Loop's is the translation (T-axiom) of the text's sentence for Loop,
`\or{SortLoop{}}(\exists{SortLoop{}}(X0, Lblloop{}(X0)), \bottom{SortLoop{}}())`: the text's
axioms whose translation is the item, by their index among the text's sentences. -/
def noJunkItems : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/emptysort.kompile.kore") | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  let c := d.sem
  let items := Faithful.consItemsK c
  let loop := items.find? (·.label == "cons-nojunk SortLoop")
  let tr := k.axiomDecls.filter fun ad => loop.any fun it => (KoreAML.trAxiom [] [] ad).pat == it.pat
  return s!"cons-nojunk SortEmpty: {items.any (·.label == "cons-nojunk SortEmpty")}; cons-nojunk SortLoop: {loop.isSome}, the translation of sentence {tr.map (·.index)}"

/--
info: cons-nojunk SortEmpty: false; cons-nojunk SortLoop: true, the translation of sentence [131]
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← noJunkItems)
