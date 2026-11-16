/-
  A cell collection's injection `inj{XCell, XCellMap}` is not read: a text whose rule applies it is
  refused (`cellCollectionInjection`). Run from the package root:
  `lake env lean test/CellCollection.lean`.
  - `f2-examples/colls.kore`: read (its rules build the account map from `AcctCellMapItem`);
  - the same text with `bump`'s `AcctCellMapItem(<id>(I), <acct>(…))` replaced by
    `inj{SortAcctCell{}, SortAcctCellMap{}}(<acct>(…))` (an edit of the parsed text in the test):
    refused, `cellCollectionInjection`.
-/
import KcoreSpec.Account

open KCore

mutual
  /-- `AcctCellMapItem(k, c)` made `inj{AcctCell, AcctCellMap}(c)`. -/
  partial def injectCells : Kore.Pattern → Kore.Pattern
    | .app h ss ps =>
      if h.ident.name == "LblAcctCellMapItem" then match ps with
        | [_, c] => .app ⟨⟨"inj"⟩⟩ [KoreAML.srt "AcctCell", KoreAML.srt "AcctCellMap"] [injectCells c]
        | _ => .app h ss (injectCellsList ps)
      else .app h ss (injectCellsList ps)
    | .and s ps => .and s (injectCellsList ps)
    | .rewrites s p q => .rewrites s (injectCells p) (injectCells q)
    | p => p
  partial def injectCellsList : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => injectCells p :: injectCellsList ps
end

/-- The user module's rewrite axioms with their cells injected. -/
def injectRules (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => match a.pattern with
      | .rewrites .. => .axiom { a with pattern := injectCells a.pattern }
      | _ => s
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read", or its refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (edit k) with
    | .ok _ => "read"
    | .error r => r.reason.name

/--
info: read
cellCollectionInjection
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/colls.kore")
  IO.println (← verdict "f2-examples/colls.kore" injectRules)
