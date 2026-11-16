/-
  `kore_definition name from "file.kore"`: reads a KORE file with kore-lean's reader at
  elaboration time and adds `def name : Kore.Definition := <the AST as a Lean term>`, with the
  command's source range as the declaration's range.
  The AST is a closed term of constructors, so later proofs can unfold it.
  The path is relative to the directory Lake runs Lean in (this package's root).
-/
import Lean
import KoreParser

set_option autoImplicit false

open Lean Elab Command

-- One type per command, in dependency order: a multi-type `deriving instance` does not
-- make the earlier instances available to the later ones.
deriving instance ToExpr for Kore.Identifier
deriving instance ToExpr for Kore.SymbolIdent
deriving instance ToExpr for Kore.EVarIdent
deriving instance ToExpr for Kore.SVarIdent
deriving instance ToExpr for Kore.SortIdent
deriving instance ToExpr for Kore.ModuleName
deriving instance ToExpr for Kore.SortVar
deriving instance ToExpr for Kore.KSort
deriving instance ToExpr for Kore.EVar
deriving instance ToExpr for Kore.SVar
deriving instance ToExpr for Kore.VarPattern
deriving instance ToExpr for Kore.Pattern
deriving instance ToExpr for Kore.AppPattern
deriving instance ToExpr for Kore.SymbolOrAlias
deriving instance ToExpr for Kore.Symbol
deriving instance ToExpr for Kore.Alias
deriving instance ToExpr for Kore.Import
deriving instance ToExpr for Kore.SentenceSort
deriving instance ToExpr for Kore.HookedSort
deriving instance ToExpr for Kore.SentenceSymbol
deriving instance ToExpr for Kore.HookedSymbol
deriving instance ToExpr for Kore.SentenceAlias
deriving instance ToExpr for Kore.Axiom
deriving instance ToExpr for Kore.Claim
deriving instance ToExpr for Kore.Sentence
deriving instance ToExpr for Kore.Module
deriving instance ToExpr for Kore.Definition

namespace KoreAML

syntax (name := koreDefinitionCmd) "kore_definition " ident " from " str : command

@[command_elab koreDefinitionCmd]
def elabKoreDefinition : CommandElab
  | stx@`(kore_definition $id:ident from $path:str) => do
    let input ← IO.FS.readFile path.getString
    match Kore.parseDefinition input with
    | .error e => throwError "kore_definition: {path.getString}: {e}"
    | .ok d =>
      let name := (← getCurrNamespace) ++ id.getId
      liftCoreM <| addAndCompile <| .defnDecl {
        name, levelParams := [], type := mkConst ``Kore.Definition, value := toExpr d,
        hints := .regular 0, safety := .safe }
      addDeclarationRangesFromSyntax name stx id
  | _ => throwUnsupportedSyntax

end KoreAML
