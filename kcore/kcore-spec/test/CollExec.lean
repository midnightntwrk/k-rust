/-
  The executable step with collection patterns (`CExec.successorsN`, KcoreSpec/CollExec.lean) on
  the kompiled texts of f2-examples that apply them, from the configurations in `test/collexec/`
  (KORE patterns, read by `CExec.configOfText`). Run from the package root:
  `lake env lean test/CollExec.lean`. Each successor list is printed back as KORE, each successor
  once; the readiness check (`CExec.execReady`) is printed for each text.
  - setcat: `drop` (`SetItem(_X) REST`) from `{1, 2}` steps to `{2}` and to `{1}` and nothing else
    (test/SetCat.lean's `step_a`, `step_b`, `drop_only`); `add` (`S SetItem(1)`) has no successor
    where 1 is in S (`add_stuck`) and one where it is not; `bump` (a cell set's element and the
    other tasks) from the tasks of ids 1 and 2 steps to the tasks 2 and 11 (`step_bump`) and,
    matching the other task, to 1 and 12.
  - setitem: `take` from `{5}` to `got(5)` (test/SetItem.lean's `step_take`), none from `{5, 6}`
    (`SetItem(X)` denotes one-member sets only); `clear` (`SetItem(1)`); `finish` from the task of
    id 7 to `got(7)` (`step_finish`).
  - colls-list and colls: `ListItem(X) L` takes the first element, `L ListItem(_)` drops the last;
    a cell map's element `<acct> <id> I </id> … </acct>` updates the account of id I, none where
    no account has it; a run of `pop ; drop ; pop` over `[1, 2, 3, 4]` ends at `[3]` with sum 3.
  - kimp: a variable's lookup `X |-> V` in `<env>` (the map pattern symbols); the executable step
    of Exec.lean, whose matcher reads map patterns, lists the same successors.
-/
import KcoreSpec

open KCore

/-- The core of a KORE text. -/
def coreOf (path : String) : IO Semantics := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => throw (IO.userError s!"{path}: KORE read error {e}")
  | .ok k => match Parse.parse k with
    | .ok d => pure d.sem
    | .error r => throw (IO.userError s!"{path}: refused {r.toText}")

/-- A configuration of `test/collexec/`. -/
def cfgOf (c : Semantics) (name : String) : IO GroundTerm := do
  match CExec.configOfText c (← IO.FS.readFile s!"test/collexec/{name}.kore") with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{name}: {e}")

/-- Print the successors of each configuration. -/
def showSuccs (path : String) (names : List String) : IO Unit := do
  let c ← coreOf path
  IO.println s!"{path}: readiness {CExec.execReady c}"
  for n in names do
    let x ← cfgOf c n
    let ys := CExec.successors c x
    IO.println s!"{n}: {ys.length}"
    for y in ys do IO.println ("  " ++ CExec.showValue c y)

/--
info: f2-examples/setcat.kompile.kore: readiness true
setcat-go: 2
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}()), dotk{}())), Lbl'-LT-'s'-GT-'{}(LblSetItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2")))), Lbl'-LT-'tasks'-GT-'{}(Lbl'Stop'TaskCellSet{}()), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}()), dotk{}())), Lbl'-LT-'s'-GT-'{}(LblSetItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))), Lbl'-LT-'tasks'-GT-'{}(Lbl'Stop'TaskCellSet{}()), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
setcat-add: 0
setcat-add3: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}()), dotk{}())), Lbl'-LT-'s'-GT-'{}(Lbl'Unds'Set'Unds'{}(LblSetItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))), Lbl'Unds'Set'Unds'{}(LblSetItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2"))), LblSetItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("3")))))), Lbl'-LT-'tasks'-GT-'{}(Lbl'Stop'TaskCellSet{}()), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
setcat-bump: 2
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}()), dotk{}())), Lbl'-LT-'s'-GT-'{}(Lbl'Stop'Set{}()), Lbl'-LT-'tasks'-GT-'{}(Lbl'Unds'TaskCellSet'Unds'{}(LblTaskCellSetItem{}(Lbl'-LT-'task'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("2")))), LblTaskCellSetItem{}(Lbl'-LT-'task'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("11")))))), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}()), dotk{}())), Lbl'-LT-'s'-GT-'{}(Lbl'Stop'Set{}()), Lbl'-LT-'tasks'-GT-'{}(Lbl'Unds'TaskCellSet'Unds'{}(LblTaskCellSetItem{}(Lbl'-LT-'task'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("1")))), LblTaskCellSetItem{}(Lbl'-LT-'task'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("12")))))), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
-/
#guard_msgs in
#eval showSuccs "f2-examples/setcat.kompile.kore" ["setcat-go", "setcat-add", "setcat-add3", "setcat-bump"]

/--
info: f2-examples/setitem.kompile.kore: readiness true
setitem-go: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lblgot{}(\dv{SortInt{}}("5"))), dotk{}())), Lbl'-LT-'s'-GT-'{}(Lbl'Stop'Set{}()), Lbl'-LT-'tasks'-GT-'{}(Lbl'Stop'TaskCellSet{}()), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
setitem-go2: 0
setitem-clear: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}()), dotk{}())), Lbl'-LT-'s'-GT-'{}(Lbl'Stop'Set{}()), Lbl'-LT-'tasks'-GT-'{}(Lbl'Stop'TaskCellSet{}()), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
setitem-finish: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lblgot{}(\dv{SortInt{}}("7"))), dotk{}())), Lbl'-LT-'s'-GT-'{}(Lbl'Stop'Set{}()), Lbl'-LT-'tasks'-GT-'{}(Lbl'Stop'TaskCellSet{}()), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
-/
#guard_msgs in
#eval showSuccs "f2-examples/setitem.kompile.kore" ["setitem-go", "setitem-go2", "setitem-clear", "setitem-finish"]

/--
info: f2-examples/colls-list.kore: readiness true
colls-list-pop: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'stack'-GT-'{}(LblListItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2")))), Lbl'-LT-'sum'-GT-'{}(\dv{SortInt{}}("1")), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
colls-list-drop: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'stack'-GT-'{}(LblListItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))), Lbl'-LT-'sum'-GT-'{}(\dv{SortInt{}}("0")), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
-/
#guard_msgs in
#eval showSuccs "f2-examples/colls-list.kore" ["colls-list-pop", "colls-list-drop"]

/-- info: steps 5, stuck true, branched false: Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'stack'-GT-'{}(LblListItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("3")))), Lbl'-LT-'sum'-GT-'{}(\dv{SortInt{}}("3")), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))) -/
#guard_msgs in
#eval show IO Unit from do
  let c ← coreOf "f2-examples/colls-list.kore"
  let x ← cfgOf c "colls-list-seq"
  let (path, br) := CExec.runFrom c Exec.fuel 20 x
  let last := path.getLast?.getD x
  IO.println s!"steps {path.length}, stuck {(CExec.successorsN c Exec.fuel last).isEmpty}, branched {br}: {CExec.showValue c last}"

/--
info: f2-examples/colls.kore: readiness true
colls-pop: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'stack'-GT-'{}(LblListItem{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2")))), Lbl'-LT-'sum'-GT-'{}(\dv{SortInt{}}("1")), Lbl'-LT-'accts'-GT-'{}(LblAcctCellMapItem{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("0")), Lbl'-LT-'acct'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("0")), Lbl'-LT-'bal'-GT-'{}(\dv{SortInt{}}("0"))))), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
colls-bump: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()), Lbl'-LT-'stack'-GT-'{}(Lbl'Stop'List{}()), Lbl'-LT-'sum'-GT-'{}(\dv{SortInt{}}("0")), Lbl'-LT-'accts'-GT-'{}(Lbl'Unds'AcctCellMap'Unds'{}(LblAcctCellMapItem{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("0")), Lbl'-LT-'acct'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("0")), Lbl'-LT-'bal'-GT-'{}(\dv{SortInt{}}("0")))), Lbl'Unds'AcctCellMap'Unds'{}(LblAcctCellMapItem{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("1")), Lbl'-LT-'acct'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("1")), Lbl'-LT-'bal'-GT-'{}(\dv{SortInt{}}("6")))), LblAcctCellMapItem{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("2")), Lbl'-LT-'acct'-GT-'{}(Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("2")), Lbl'-LT-'bal'-GT-'{}(\dv{SortInt{}}("9"))))))), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
colls-bump-none: 0
-/
#guard_msgs in
#eval showSuccs "f2-examples/colls.kore" ["colls-pop", "colls-bump", "colls-bump-none"]

/--
info: f2-examples/kimp.kore: readiness true
kimp-lookup: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7")), dotk{}())), Lbl'-LT-'env'-GT-'{}(Lbl'Unds'Map'Unds'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortId{}, SortKItem{}}(\dv{SortId{}}("x")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("5"))), Lbl'Unds'Map'Unds'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortId{}, SortKItem{}}(\dv{SortId{}}("y")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7"))), Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortId{}, SortKItem{}}(\dv{SortId{}}("z")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("9")))))), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
kimp-lookup-none: 0
-/
#guard_msgs in
#eval showSuccs "f2-examples/kimp.kore" ["kimp-lookup", "kimp-lookup-none"]

/-- Exec.lean's executable step (whose matcher reads constructors and map patterns, `Semantics.ok`)
lists the same successors on kimp. -/
def agreesWithExec (path : String) (names : List String) : IO Unit := do
  let c ← coreOf path
  IO.println s!"ok {c.ok}"
  for n in names do
    let x ← cfgOf c n
    let a := CExec.successors c x
    let b := Exec.successorsN c Exec.fuel x
    IO.println s!"{n}: {a.all (fun y => b.any (Exec.same · y)) && b.all (fun y => a.any (Exec.same · y))}"

/--
info: ok true
kimp-lookup: true
kimp-lookup-none: true
-/
#guard_msgs in
#eval agreesWithExec "f2-examples/kimp.kore" ["kimp-lookup", "kimp-lookup-none"]
