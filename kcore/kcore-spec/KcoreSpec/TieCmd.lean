/-
  `user_axioms`: the axioms of one module of a KORE text as constants, for a per-sentence tie.
-/
import KcoreSpec.ParseCmd

set_option autoImplicit false

open Lean Elab Command in
/-- `user_axioms NAME from "file" module "M"`: a constant `NAME.axN` for each axiom of the module M
(N its `AxiomDecl.index` among the text's axioms), and `NAME.all`, their list in text order. The
constants are literals; a tie checks them against the text's literal
(`kore.axiomDecls.filter (·.module == "M") = NAME.all`). -/
syntax (name := userAxiomsCmd) "user_axioms " ident " from " str " module " str : command

open Lean Elab Command in
@[command_elab userAxiomsCmd] def elabUserAxioms : CommandElab
  | `(user_axioms $id:ident from $path:str module $m:str) => do
    let input ← IO.FS.readFile path.getString
    let k ← match Kore.parseDefinition input with
      | .error e => throwError "user_axioms: {e}"
      | .ok k => pure k
    let ns := (← getCurrNamespace) ++ id.getId
    let ty := mkConst ``KoreAML.AxiomDecl
    let mut consts : List Expr := []
    for ad in k.axiomDecls do
      if ad.module == m.getString then
        let n := ns ++ Name.mkSimple s!"ax{ad.index}"
        let v := mkApp3 (mkConst ``KoreAML.AxiomDecl.mk) (toExpr ad.index) (toExpr ad.module) (toExpr ad.ax)
        let d : DefinitionVal := { name := n, levelParams := [], type := ty, value := v, hints := .regular 0, safety := .safe }
        liftCoreM <| addDecl <| .defnDecl d
        consts := consts ++ [mkConst n]
    let l ← liftTermElabM <| Meta.mkListLit ty consts
    let d : DefinitionVal := { name := ns ++ `all, levelParams := [], type := mkApp (mkConst ``List [0]) ty, value := l, hints := .regular 0, safety := .safe }
    liftCoreM <| addDecl <| .defnDecl d
  | _ => throwUnsupportedSyntax
