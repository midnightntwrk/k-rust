/-
  KCore, tooling. `semantics_of NAME from "file.kore"`: reads
  the KORE file at elaboration time, runs KCore's `parse` on it (compiled), and adds
  `def NAME : Semantics := <the result>` as a term with `addDecl`: not printed as Lean source and
  elaborated, and not compiled (findings/R1-scale.md §3). The path is relative to the directory Lean
  runs in.

  What NAME denotes is `(parse k).sem` for the file's KORE k, by construction: the command runs the
  same `parse` the kernel unfolds (a kernel tie `parse k = .ok d` is a generated package's
  `Tie/Parse`).
  The command refuses a definition with parameter symbols: such a semantics is stated for every
  interpretation (`withHooks`), and the data carries only the default one.

  `det_index_of NAME from "file.kore"`: `det_index NAME := Det.autoIndex c` for the `c` that
  `semantics_of` gives the same file. `det_index` evaluates its term by compiled code, and a
  constant added by `semantics_of` is not compiled; this computes the index from the parse instead.
  Nothing is trusted: the index is a hint, which the kernel checks in `Det.detOK c NAME`.

  `tables_of NAME from "file.kore"`: the definition's tables (A5), likewise from the parse.
-/
import Lean
import KcoreSpec.DataCmd
import KcoreSpec.Account
import KcoreSpec.Kore.KoreTerm

open Lean Elab Command

namespace KCore

-- One type per command, in dependency order.
deriving instance ToExpr for Lib
deriving instance ToExpr for Term
deriving instance ToExpr for Cond
deriving instance ToExpr for Clause
deriving instance ToExpr for Fn
deriving instance ToExpr for Rule
deriving instance ToExpr for CellIds
deriving instance ToExpr for Cell
deriving instance ToExpr for ParamSig
deriving instance ToExpr for OvlSig
deriving instance ToExpr for KoreAML.Loc
deriving instance ToExpr for KoreAML.Meta
deriving instance ToExpr for KoreAML.SortUids
deriving instance ToExpr for ProdKind
deriving instance ToExpr for ClausePres
deriving instance ToExpr for FnPres
deriving instance ToExpr for CtorPres
deriving instance ToExpr for RulePres
deriving instance ToExpr for ParamPres
deriving instance ToExpr for LawEq
deriving instance ToExpr for Presentation
deriving instance ToExpr for Certificates
instance {α β : Type} [ToExpr α] [ToExpr β] : ToExpr (α ⊕ β) where
  toExpr
    | .inl a => mkApp3 (mkConst ``Sum.inl [.zero, .zero]) (toTypeExpr α) (toTypeExpr β) (toExpr a)
    | .inr b => mkApp3 (mkConst ``Sum.inr [.zero, .zero]) (toTypeExpr α) (toTypeExpr β) (toExpr b)
  toTypeExpr := mkApp2 (mkConst ``Sum [.zero, .zero]) (toTypeExpr α) (toTypeExpr β)
deriving instance ToExpr for Parse.RefusalReason
deriving instance ToExpr for Parse.RawEqn
deriving instance ToExpr for Parse.Scan
deriving instance ToExpr for Parse.CellParts

/-- The term of a `Semantics` without parameter symbols (its interpretation is the default). -/
def semanticsExpr (c : Semantics) : Expr :=
  mkAppN (mkConst ``Semantics.mk)
    #[toExpr c.lib, toExpr c.sortNames, toExpr c.symNames, toExpr c.userSorts, toExpr c.ctors,
      toExpr c.fns, toExpr c.userSubsorts, toExpr c.pgmSort, toExpr c.rules,
      toExpr c.params, toExpr c.colls, toExpr c.ovls, mkConst ``HookParams.none]

/-- The term of a `Definition` (its semantics' interpretation of the parameters is the default). -/
def definitionExpr (d : Definition) : Expr :=
  mkApp3 (mkConst ``Definition.mk) (semanticsExpr d.sem) (toExpr d.pres) (toExpr d.cert)

syntax (name := semanticsOfCmd) "semantics_of " ident " from " str : command

@[command_elab semanticsOfCmd] def elabSemanticsOf : CommandElab
  | stx@`(semantics_of $id:ident from $path:str) => do
    let input ← IO.FS.readFile path.getString
    let k ← match Kore.parseDefinition input with
      | .error e => throwError "semantics_of: {path.getString}: KORE read error {e}"
      | .ok k => pure k
    let d ← match Parse.parse k with
      | .ok d => pure d
      | .error r => throwError "semantics_of: {path.getString}: KCore's parse refuses it: {r.toText}"
    unless d.sem.params.isEmpty do
      throwError "semantics_of: {path.getString}: the definition has parameter symbols"
    let name := (← getCurrNamespace) ++ id.getId
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type := mkConst ``Semantics, value := semanticsExpr d.sem,
      hints := .regular 0, safety := .safe }
    addDeclarationRangesFromSyntax name stx id
  | _ => throwUnsupportedSyntax

/-- The semantics KCore's parse gives a KORE file, read at elaboration time. -/
def semanticsOfFile (path : String) : CommandElabM Semantics := do
  let input ← IO.FS.readFile path
  let k ← match Kore.parseDefinition input with
    | .error e => throwError "{path}: KORE read error {e}"
    | .ok k => pure k
  match Parse.parse k with
  | .ok d => return d.sem
  | .error r => throwError "{path}: KCore's parse refuses it: {r.toText}"

syntax (name := detIndexOfCmd) "det_index_of " ident " from " str (" at " term)? : command

/-- `det_index_of NAME from "file.kore" [at PATHS]`: the determinism index at the default paths, or
at the paths PATHS (a `List (List Nat)`, which the generator chooses per definition). -/
@[command_elab detIndexOfCmd] def elabDetIndexOf : CommandElab
  | stx@`(det_index_of $id:ident from $path:str $[at $ps]?) => do
    let c ← semanticsOfFile path.getString
    let paths ← match ps with
      | none => pure (Det.autoPaths c)
      | some ps => liftTermElabM do
        let ty := mkApp (mkConst ``List [.zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
        let e ← Term.elabTerm ps (some ty)
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        unsafe Meta.evalExpr (List (List Nat)) ty e
    let name := (← getCurrNamespace) ++ id.getId
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type := mkConst ``Det.DetIndex, value := toExpr (Det.DetIndex.build c (tables c) paths),
      hints := .regular 0, safety := .safe }
    addDeclarationRangesFromSyntax name stx id
  | _ => throwUnsupportedSyntax

syntax (name := definitionOfCmd) "definition_of " ident " from " str : command

/-- `definition_of NAME from "file.kore"`: `def NAME : Definition := <KCore's parse of the file>`, added
as a term (not printed, not compiled). A definition with parameter symbols carries the default
interpretation; its theorems are stated for every one (`withHooks`). The package's tie proves that
NAME is the kernel's `parse` of the KORE term (`D/Tie`). -/
@[command_elab definitionOfCmd] def elabDefinitionOf : CommandElab
  | stx@`(definition_of $id:ident from $path:str) => do
    let input ← IO.FS.readFile path.getString
    let k ← match Kore.parseDefinition input with
      | .error e => throwError "definition_of: {path.getString}: KORE read error {e}"
      | .ok k => pure k
    let d ← match Parse.parse k with
      | .ok d => pure d
      | .error r => throwError "definition_of: {path.getString}: KCore's parse refuses it: {r.toText}"
    let name := (← getCurrNamespace) ++ id.getId
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type := mkConst ``Definition, value := definitionExpr d,
      hints := .regular 0, safety := .safe }
    addDeclarationRangesFromSyntax name stx id
  | _ => throwUnsupportedSyntax

syntax (name := tablesOfCmd) "tables_of " ident " from " str (" with " term)? : command

/-- `tables_of NAME from "file.kore" [with F]`: `tables c` (A5, Tables.lean) for the `c` that
`semantics_of` gives the same file (or `F c`, F a `Semantics → Semantics`: a probe's variant of a
definition), computed from the parse and added as a term. The kernel checks it once, in the fact
`NAME = tables c`. -/
@[command_elab tablesOfCmd] def elabTablesOf : CommandElab
  | stx@`(tables_of $id:ident from $path:str $[with $f]?) => do
    let c ← semanticsOfFile path.getString
    let c ← match f with
      | none => pure c
      | some f => do
        let F ← liftTermElabM do
          let ty := Expr.forallE `c (mkConst ``Semantics) (mkConst ``Semantics) .default
          let e ← Term.elabTerm f (some ty)
          Term.synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          unsafe Lean.Meta.evalExpr (Semantics → Semantics) ty e
        pure (F c)
    let name := (← getCurrNamespace) ++ id.getId
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type := mkConst ``Tables, value := toExpr (tables c),
      hints := .regular 0, safety := .safe }
    addDeclarationRangesFromSyntax name stx id
  | _ => throwUnsupportedSyntax

deriving instance ToExpr for Parse.Names
deriving instance ToExpr for Parse.RCell
deriving instance ToExpr for Prod
deriving instance ToExpr for Parse.Env

syntax (name := parseStagesCmd) "parse_stages " ident " from " str " cut " "[" num,* "]"
  " scan_blocks " "[" num,* "]" " prod_blocks " "[" num,* "]" " rule_blocks " "[" num,* "]"
  " event_blocks " "[" num,* "]" " clause_blocks " "[" num,* "]" : command

/-- `parse_stages NAME from "file.kore" cut [CUTS] scan_blocks [..] prod_blocks [..] rule_blocks [..]
event_blocks [..] clause_blocks [..]`:
the stages of `parse` on the file, as data, for the tie to check one at a time (`Parse.ScanIs`,
`Parse.envOf`, `Parse.MapIs`, `Parse.assemble_of_parts`). The user module's sentences are cut into segments
as `kore_term … cut [CUTS]` cuts them; for each block of consecutive segments, `NAME.scanI` is its
scan; `NAME.env` the names; for each block of the user symbols and of the rewrite axioms,
`NAME.prodsI` and `NAME.rulesI` their productions and rules; `NAME.prodsM` the productions with
the subsorts merged in, `NAME.eventsI` the declaration events of each block, and `NAME.cells`
the presentation's cell parts. `clause_blocks` lists, for each function whose clauses are checked
in blocks, its user symbol's index, the number of blocks, then each block's length;
`NAME.clsS_J` is block J of symbol S's clauses (`Parse.fnClauses`). Computed by compiled code from the
file and added as terms; nothing is trusted (a wrong one makes its check fail). -/
@[command_elab parseStagesCmd] def elabParseStages : CommandElab
  | `(parse_stages $id:ident from $path:str cut [$cs,*] scan_blocks [$bs,*] prod_blocks [$ps,*] rule_blocks [$rs,*]
      event_blocks [$es,*] clause_blocks [$cbs,*]) => do
    let input ← IO.FS.readFile path.getString
    let k ← match Kore.parseDefinition input with
      | .error e => throwError "parse_stages: {path.getString}: KORE read error {e}"
      | .ok k => pure k
    let some m := k.modules.getLast? | throwError "parse_stages: no module"
    let segs := cutAt m.sentences (cs.getElems.toList.map (·.getNat))
    let base := (← getCurrNamespace) ++ id.getId
    let add (n : Name) (ty v : Expr) : CommandElabM Unit :=
      liftCoreM <| addDecl <| .defnDecl
        { name := base ++ n, levelParams := [], type := ty, value := v, hints := .regular 0, safety := .safe }
    let nums := fun (xs : Syntax.TSepArray `num ",") => xs.getElems.toList.map (·.getNat)
    -- each block is scanned at the cell-collection pairs of the whole module (`Parse.ScanIs`)
    let P := Parse.cellCollPairs m.sentences
    let mut a := 0
    for (n, i) in (nums bs).zipIdx do
      add (Name.mkSimple s!"scan{i}") (mkConst ``Parse.Scan) (toExpr (Parse.scanWith P ((segs.drop a).take n).flatten))
      a := a + n
    let S := Parse.scan m.sentences
    let .ok E := Parse.envOf m S | throwError "parse_stages: the names fail"
    add `env (mkConst ``Parse.Env) (toExpr E)
    a := 0
    for (n, i) in (nums ps).zipIdx do
      let .ok r := (((Parse.prodSyms S E).drop a).take n).mapM (Parse.symProd E S.eqs) | throwError "parse_stages: productions {i} fail"
      add (Name.mkSimple s!"prods{i}") (toTypeExpr (List Prod)) (toExpr r)
      a := a + n
    let mut cb := nums cbs
    while !cb.isEmpty do
      let sym := cb.head!
      let k := cb.getD 1 0
      let lens := (cb.drop 2).take k
      cb := cb.drop (2 + k)
      let some s := (Parse.prodSyms S E)[sym]? | throwError "parse_stages: no user symbol {sym}"
      let pairs := Parse.fnPairs S.eqs s.symbol.ident.ident.name
      a := 0
      for (n, j) in lens.zipIdx do
        let .ok r := ((pairs.drop a).take n).mapM (Parse.clauseOf E.N E.src) | throwError "parse_stages: clauses {sym} {j} fail"
        add (Name.mkSimple s!"cls{sym}_{j}") (toTypeExpr (List (Clause × ClausePres))) (toExpr r)
        a := a + n
    a := 0
    for (n, i) in (nums rs).zipIdx do
      let .ok r := ((S.rewrites.drop a).take n).mapM (Parse.ruleOf E.N E.src) | throwError "parse_stages: rules {i} fail"
      add (Name.mkSimple s!"rules{i}") (toTypeExpr (List (Rule × RulePres))) (toExpr r)
      a := a + n
    -- the assembly's intermediate parts: the merged productions and the cell parts
    let .ok sp := (Parse.prodSyms S E).mapM (Parse.symProd E S.eqs) | throwError "parse_stages: productions fail"
    let .ok rs := S.rewrites.mapM (Parse.ruleOf E.N E.src) | throwError "parse_stages: rules fail"
    a := 0
    for (n, i) in (nums es).zipIdx do
      let r := ((S.events.drop a).take n).filterMap (Parse.eventOf E sp)
      add (Name.mkSimple s!"events{i}") (toTypeExpr (List (Sum Sym (Srt × Srt)))) (toExpr r)
      a := a + n
    let ps := Parse.prodsOf S E sp
    add `prodsM (toTypeExpr (List Prod)) (toExpr ps)
    let .ok core := Parse.coreOf S E ps rs | throwError "parse_stages: the core fails"
    let .ok cp := Parse.cellPartsOf S E core | throwError "parse_stages: the cell parts fail"
    add `cells (mkConst ``Parse.CellParts) (toExpr cp)
  | _ => throwUnsupportedSyntax

end KCore
