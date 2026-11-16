/-
  K's stream cells, read from K 7.1.337 kompile's KORE. Run from the package root:
  `lake env lean test/StreamIO.lean`.
  - `f2-examples/iot.kompile.kore` (`iot.k`): cells `<in stream="stdin">` and `<out stream="stdout">`
    and a rule writing to `<out>`. The text holds K-IO (a library module), K-REFLECTION's nine
    sentences and the eight rules of the stream modules, instantiated on `<in>` and `<out>`, all with
    the installation's `domains.md` as `Source`. K-REFLECTION's sentences are recognised by content
    and read as the definition's own (`reflectionAsOwn`, `#configuration` among them as a parameter
    symbol), but `#unparseKORE{S}`'s declaration (`unread parametricUnused`); the rules
    are read as the definition's (`streamRule`); `#noParse` is a constructor of `IOError` beside the
    library's, and the text's distinctness axioms between them are induced. Nothing is refused or
    unaccounted, and `coreOK` holds (decided by the compiled `coreOK`, not in the kernel).
  - with `#argv`'s declaration dropped: K-REFLECTION incomplete (`builtinIncomplete`); with `#fresh`'s
    `impure` dropped: no sentence of K-REFLECTION, refused (`builtinText`); with the label of
    `stdoutWrite` renamed: no stream rule, refused (`builtinText`).
  - `f2-examples/iot-cfg.kompile.kore` (`iot-cfg.k`): a rule applying `#configuration`, a parameter
    symbol: read, nothing unaccounted (test/Configuration.lean: no step at `HookParams.none`).
  - `f2-examples/iot-in.kompile.kore` (`iot-in.k`): a rule reading `<in>`, for which kompile writes
    an instance of STDIN-STREAM's unblocking rule into the user's file: read, nothing unaccounted.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The text with the user module's sentences edited by `f`. -/
def editUser (f : Kore.Sentence → Option Kore.Sentence) (k : Kore.Definition) : Kore.Definition :=
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.filterMap f }]).getD [] }

/-- Without the hooked symbol `n`'s declaration. -/
def dropHooked (n : String) : Kore.Sentence → Option Kore.Sentence
  | .hookedSymbol x => if x.symbol.ident.ident.name == n then none else some (.hookedSymbol x)
  | s => some s

/-- The hooked symbol `n` without its attribute `a`. -/
def dropAttr (n a : String) : Kore.Sentence → Option Kore.Sentence
  | .hookedSymbol x => if x.symbol.ident.ident.name == n then
      some (.hookedSymbol { x with attributes := x.attributes.filter (·.head.ident.name != a) })
    else some (.hookedSymbol x)
  | s => some s

/-- The rewrite axiom labelled `l` relabelled `l'`. -/
def relabel (l l' : String) : Kore.Sentence → Option Kore.Sentence
  | .axiom a => some (.axiom { a with attributes := a.attributes.map fun ap =>
      if ap.head.ident.name == "label" && ap.args.any (fun p => match p with
          | .string v => v == l
          | _ => false) then { ap with args := [.string l'] } else ap })
  | s => some s

/-- The reader's verdict on the text at `path` (edited by `edit`): its sentences by class (those of
the readings this test is about), and the refusal or what the account finds. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    let cls := (Parse.classCounts k).filter fun (n, _) =>
      ["read reflectionAsOwn", "read streamRule", "unread parametricUnused"].contains n
    let cls := cls.mergeSort fun a b => decide (a.1 ≤ b.1)
    return s!"{cls}; " ++ match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; uninduced {(Parse.uninduced k d).length}; missing {(Parse.missingBuiltin k d).map (·.head)}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/--
info: [(read reflectionAsOwn, 8), (read streamRule, 8), (unread parametricUnused, 1)]; read; unaccounted []; uninduced 0; missing []; coreOK true
[(read reflectionAsOwn, 7), (read streamRule, 8), (unread parametricUnused, 1)]; read; unaccounted []; uninduced 0; missing [K-REFLECTION]; coreOK true
[(read reflectionAsOwn, 7), (read streamRule, 8), (unread parametricUnused, 1)]; builtinText
[(read reflectionAsOwn, 8), (read streamRule, 7), (unread parametricUnused, 1)]; builtinText
[(read reflectionAsOwn, 8), (read streamRule, 8), (unread parametricUnused, 1)]; read; unaccounted []; uninduced 0; missing []; coreOK true
[(read reflectionAsOwn, 8), (read streamRule, 8), (unread parametricUnused, 1)]; read; unaccounted []; uninduced 0; missing []; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  let f := "f2-examples/iot.kompile.kore"
  IO.println (← verdict f)
  IO.println (← verdict f (editUser (dropHooked "Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List")))
  IO.println (← verdict f (editUser (dropAttr "Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String" "impure")))
  IO.println (← verdict f (editUser (relabel "STDOUT-STREAM.stdoutWrite" "STDOUT.stdoutWrite")))
  IO.println (← verdict "f2-examples/iot-cfg.kompile.kore")
  IO.println (← verdict "f2-examples/iot-in.kompile.kore")
