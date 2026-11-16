/-
  A KORE file as a Lean term, for the tie. `kore_term name from "file.kore"` reads the file with
  the KORE reader and adds `def name : Kore.Definition := <the AST>` with `addDecl`: the kernel
  checks the term, and nothing compiles it (the tie's theorems only unfold it; compiling the AST of
  a large definition is the slowest part of reading it).

  `kore_term name from "file.kore" cut [n₁, n₂, …]` stores the last module's sentences in
  segments: `name.seg0` holds the sentences before position `n₁`, `name.seg1` those from `n₁` to
  `n₂`, and so on; `name.segs` is the list of the segments, and the module's sentences are
  `name.segs.flatten`. The term denotes the same definition (`flatten` of the segments is the
  sentence list); the segments let a tie compare the module a segment at a time, each segment a
  constant it names instead of a position it walks to (`KoreAML.Blocks`).
-/
import KcoreSpec.Kore.Import

open Lean Elab Command

syntax (name := koreTermCmd) "kore_term " ident " from " str (" cut " "[" num,* "]")? : command

/-- The list `l` cut before each position of `cuts` (ascending, within the list). -/
def cutAt {α : Type} (l : List α) (cuts : List Nat) : List (List α) :=
  let rec go (l : List α) (pos : Nat) : List Nat → List (List α)
    | [] => [l]
    | c :: cs => (l.take (c - pos)) :: go (l.drop (c - pos)) c cs
  go l 0 cuts

@[command_elab koreTermCmd] def elabKoreTerm : CommandElab
  | stx@`(kore_term $id:ident from $path:str $[cut [$cs,*]]?) => do
    let input ← IO.FS.readFile path.getString
    match Kore.parseDefinition input with
    | .error e => throwError "kore_term: {path.getString}: {e}"
    | .ok d =>
      let name := (← getCurrNamespace) ++ id.getId
      let addDef (n : Name) (ty v : Expr) : CommandElabM Unit :=
        liftCoreM <| addDecl <| .defnDecl {
          name := n, levelParams := [], type := ty, value := v, hints := .regular 0, safety := .safe }
      match cs with
      | none => addDef name (mkConst ``Kore.Definition) (toExpr d)
      | some cs =>
        let cuts := cs.getElems.toList.map (·.getNat)
        let some m := d.modules.getLast? | throwError "kore_term: {path.getString}: no module"
        unless cuts.zip (cuts.drop 1) |>.all (fun (a, b) => a < b) do throwError "kore_term: cuts not ascending"
        unless cuts.all (· < m.sentences.length) do throwError "kore_term: a cut is past the module's end"
        let sentTy := mkApp (mkConst ``List [0]) (mkConst ``Kore.Sentence)
        let segs := cutAt m.sentences cuts
        let mut segConsts : List Expr := []
        for (s, i) in segs.zipIdx do
          let n := name ++ Name.mkSimple s!"seg{i}"
          addDef n sentTy (toExpr s)
          segConsts := segConsts ++ [mkConst n]
        let segsTy := mkApp (mkConst ``List [0]) sentTy
        let segsName := name ++ `segs
        addDef segsName segsTy (← liftTermElabM <| Meta.mkListLit sentTy segConsts)
        let sents := mkApp2 (mkConst ``List.flatten [0]) (mkConst ``Kore.Sentence) (mkConst segsName)
        let mU := mkApp3 (mkConst ``Kore.Module.mk) (toExpr m.name) sents (toExpr m.attributes)
        let modTy := mkConst ``Kore.Module
        let mods ← liftTermElabM <| Meta.mkListLit modTy (d.modules.dropLast.map toExpr ++ [mU])
        addDef name (mkConst ``Kore.Definition)
          (mkApp2 (mkConst ``Kore.Definition.mk) (toExpr d.attributes) mods)
      addDeclarationRangesFromSyntax name stx id
  | _ => throwUnsupportedSyntax
