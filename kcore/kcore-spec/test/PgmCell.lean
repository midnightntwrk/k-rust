/-
  The program variable `$PGM` in a cell other than `<k>`, read from K 7.1.337 kompile's KORE. Run
  from the package root: `lake env lean test/PgmCell.lean`.
  - `f2-examples/pgmt.kompile.kore` (`pgmt.k`, `configuration <T> $PGM:Pgm </T>`, no `<k>`): the
    text's initializer `initTCell(Init) = <T>(project:Pgm(kseq(Map:lookup(Init, $PGM), dotk)))`
    states that `<T>` holds `$PGM`, of sort Pgm. Read: `$PGM` of sort Pgm, the configuration's place
    that of `<T>`'s declaration, nothing unaccounted or refused by the account, `coreOK` (compiled,
    not in the kernel); the rule steps `<T> go(1) </T>` to `<T> done(2) </T>` (compiled step
    function).
  - `f2-examples/pgmtk.kompile.kore` (`pgmtk.k`, `<T> <k> .K </k> <p> $PGM:Pgm </p> </T>`): `initKCell`
    projects nothing, `initPCell` projects `$PGM` to Pgm. Read likewise; the configuration's place is
    `<k>`'s declaration's, as for every text with a `<k>` cell.
  - `pgmtk` with `$PGM` renamed `$X` in its initializer: no initializer holds `$PGM`, so no cell
    holds it (`Presentation.pgmCell` is `none`) and `$X` is a configuration variable as `$ENV` is:
    read, with nothing unaccounted (the sort of `$PGM` K, which no sentence `emit` writes reads).
  - `pgmt` with the projection around `$PGM` removed from `initTCell`'s right side
    (`<T>(kseq(Map:lookup(Init, $PGM), dotk))`): an initializer holds `$PGM` and none states its
    sort, refused (`pgmSort`).
  - The tie, natively: both are `wf` (no cell named `k` is asked for: the leaf the text's
    initializer gives `$PGM`, `Presentation.pgmCell`, is `<T>` and `<p>`), and `emit` writes the
    cells' initializer declarations and equations as the text states them: `$PGM`'s projection in
    the cell holding it, `<k>`'s `.K` as its value like any leaf's (`initCells`: no initializer
    sentence of one side missing from the other). `Reordered d.emit k` is false for both, as for
    every text kompile 7.1.337 writes (`test/roundtrip.expected`), for sentences other than the
    cells'.
  - A presentation whose `$PGM` leaf has content Int (`pgmt` with `<T>`'s content and constructor
    argument Int) has `cellsOK` false: `emit` writes `$PGM`'s projection into a K or into its sort.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's and the account's verdict on the text at `path` (edited by `edit`). -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let unacc := (Parse.unconsumed k d).length + (Parse.uninduced k d).length
        s!"read; pgm {d.sem.sortName d.sem.pgmSort}; configLoc {d.pres.configLoc.l1}:{d.pres.configLoc.c1}; unaccounted or uninduced {unacc}; functionInPattern {(Parse.functionInPattern k d).length}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; pgm Pgm; configLoc 11:17; unaccounted or uninduced 0; functionInPattern 0; coreOK true
read; pgm Pgm; configLoc 11:21; unaccounted or uninduced 0; functionInPattern 0; coreOK true
read; pgm K; configLoc 11:21; unaccounted or uninduced 0; functionInPattern 0; coreOK true
pgmSort no cell initializer projects $PGM
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/pgmt.kompile.kore")
  IO.println (← verdict "f2-examples/pgmtk.kompile.kore")
  IO.println (← verdict "f2-examples/pgmtk.kompile.kore" fun s => s.replace "(\"$PGM\")" "(\"$X\")")
  IO.println (← verdict "f2-examples/pgmt.kompile.kore" fun s => s.replace
    "Lbl'-LT-'T'-GT-'{}(Lblproject'Coln'Pgm{}(kseq{}(LblMap'Coln'lookup{}(VarInit:SortMap{},inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}(\"$PGM\"))),dotk{}())))"
    "Lbl'-LT-'T'-GT-'{}(kseq{}(LblMap'Coln'lookup{}(VarInit:SortMap{},inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}(\"$PGM\"))),dotk{}()))")

/-- `pgmt`'s rule by the compiled step function: the successors of `<T> go(1) </T>`. -/
def steps : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/pgmt.kompile.kore") | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  let c := d.sem
  let sym := fun (n : String) => ((List.range (nRegSyms + c.symNames.length)).find? (c.symName · == n)).getD 0
  let cfg := fun (t : GroundTerm) => GroundTerm.ctor topLabel
    [.ctor (sym "Lbl'-LT-'T'-GT-'") [t], .ctor counterLabel [.dv Srt.int (.int 0)]]
  let show1 : GroundTerm → String
    | .ctor _ [.ctor _ [.ctor f [.dv _ (.int i)]], _] => s!"{c.symName f}({i})"
    | _ => "?"
  return s!"{(Exec.successorsN c 100 (cfg (.ctor (sym "Lblgo") [.dv Srt.int (.int 1)]))).map show1}"

/--
info: [Lbldone(2)]
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← steps)

/-- The initializer sentences (those naming `Lblinit`) `emit` writes and the text does not, and the
text's that `emit` does not write. -/
def initCells (k : Kore.Definition) (d : Definition) : Nat × Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for (me, mk) in d.emit.modules.zip k.modules do
    let isInit := fun (t : String) => (t.splitOn "Lblinit").length > 1
    let pe := (me.sentences.map Kore.Printer.sentence).filter isInit
    let pk := (mk.sentences.map Kore.Printer.sentence).filter isInit
    a := a + (pe.filter (!pk.contains ·)).length
    b := b + (pk.filter (!pe.contains ·)).length
  return (a, b)

/-- `wf`, the cell holding `$PGM`, `cellsOK`, the initializer sentences apart, `Reordered`. -/
def tie (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  return s!"wf {wf d}; pgmCell {d.pres.pgmCell.getD "none"}; cellsOK {d.pres.cellsOK d.sem}; initializer sentences emitted only, in the text only {initCells k d}; reordered {decide (KoreAML.Reordered d.emit k)}"

/--
info: wf true; pgmCell T; cellsOK true; initializer sentences emitted only, in the text only (0, 0); reordered false
wf true; pgmCell p; cellsOK true; initializer sentences emitted only, in the text only (0, 0); reordered false
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← tie "f2-examples/pgmt.kompile.kore")
  IO.println (← tie "f2-examples/pgmtk.kompile.kore")

/-- `pgmt`'s cell tree with the `$PGM` leaf's content `s`, and its constructor's argument `s`. -/
def withContent (d : Definition) (s : Srt) : Definition :=
  let rec go : Cell → Cell
    | .leaf n t i => if d.pres.pgmCell == some n then .leaf n s i else .leaf n t i
    | .node n cs i => .node n (cs.attach.map fun ⟨x, _⟩ => go x) i
    | .coll s => .coll s
  let lbl := ((Cell.all (Cell.top d.pres.config)).find? (some ·.name == d.pres.pgmCell)).map Cell.label
  { d with pres := { d.pres with config := d.pres.config.map go }
           sem := { d.sem with ctors := d.sem.ctors.map fun k => if some k.name == lbl then { k with args := [s] } else k } }

/--
info: cellsOK at content Pgm true, at content Int false
-/
#guard_msgs in
#eval show IO Unit from do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/pgmt.kompile.kore") | IO.println "kore"
  let .ok d := Parse.parse k | IO.println "refused"
  let d1 := withContent d d.sem.pgmSort
  let d2 := withContent d Srt.int
  IO.println s!"cellsOK at content Pgm {d1.pres.cellsOK d1.sem}, at content Int {d2.pres.cellsOK d2.sem}"
