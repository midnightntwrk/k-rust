/-
  KCore, tooling (checked layer): `det_index NAME := TERM` evaluates TERM,
  a `Det.DetIndex` (by compiled code), and adds NAME with that value as a term: not printed as Lean
  source and elaborated, and not compiled (findings/R1-scale.md §3: a literal built this way costs the
  kernel its size; printed as source, the elaborator's work is about 10 M heartbeats for kimp's index
  alone). Nothing is trusted from the evaluation: the kernel checks the index (`Det.idxOK`) in its own
  decision, and the theorems hold for any index that passes it.
-/
import Lean
import KcoreSpec.Determinism

open Lean Elab Command Meta

namespace KCore

instance : ToExpr Lit where
  toExpr
    | .int i => mkApp (mkConst ``Lit.int) (toExpr i)
    | .bool b => mkApp (mkConst ``Lit.bool) (toExpr b)
    | .tok s => mkApp (mkConst ``Lit.tok) (toExpr s)
    | .float p e b => mkApp3 (mkConst ``Lit.float) (toExpr p) (toExpr e) (toExpr b)
  toTypeExpr := mkConst ``Lit

namespace Det

instance : ToExpr Key where
  toExpr
    | .sym f => mkApp (mkConst ``Key.sym) (toExpr f)
    | .lit s l => mkApp2 (mkConst ``Key.lit) (toExpr s) (toExpr l)
    | .src s => mkApp (mkConst ``Key.src) (toExpr s)
  toTypeExpr := mkConst ``Key

instance : ToExpr DetIndex where
  toExpr ix := mkAppN (mkConst ``DetIndex.mk)
    #[toExpr ix.paths, toExpr ix.keys, toExpr ix.buckets, toExpr ix.wild, toExpr ix.probes]
  toTypeExpr := mkConst ``DetIndex

end Det

instance {α : Type} [ToExpr α] : ToExpr (NatMap α) where
  toExpr := go
  toTypeExpr := mkApp (mkConst ``NatMap) (toTypeExpr α)
where
  go : NatMap α → Expr
    | .leaf => mkApp (mkConst ``NatMap.leaf) (toTypeExpr α)
    | .node v l r => mkApp4 (mkConst ``NatMap.node) (toTypeExpr α) (toExpr v) (go l) (go r)

instance : ToExpr CtorSig where
  toExpr k := mkApp3 (mkConst ``CtorSig.mk) (toExpr k.name) (toExpr k.args) (toExpr k.result)
  toTypeExpr := mkConst ``CtorSig

deriving instance ToExpr for CollKind
deriving instance ToExpr for CollSig
deriving instance ToExpr for OvlSig

instance : ToExpr Tables where
  toExpr T := mkApp7 (mkConst ``Tables.mk) (toExpr T.subs) (toExpr T.sup) (toExpr T.inf) (toExpr T.sigs)
    (toExpr T.colls) (toExpr T.ovls) (toExpr T.fnSigs)
  toTypeExpr := mkConst ``Tables

/-- `tables_of NAME := TERM`: NAME is `tables` of TERM (a `Semantics`), computed by compiled code and
added as a term (A5, Tables.lean). The kernel checks it once, in the fact `NAME = tables TERM`. -/
elab "tables_of " id:ident " := " t:term : command => do
  let declName := (← getCurrNamespace) ++ id.getId
  let T ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``Semantics))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unsafe evalExpr Tables (mkConst ``Tables) (mkApp (mkConst ``tables) e)
  liftCoreM <| addDecl <| .defnDecl
    { name := declName, levelParams := [], type := mkConst ``Tables, value := toExpr T,
      hints := .regular 0, safety := .safe }

/-- `det_index NAME := TERM`: NAME is the value of TERM (a `Det.DetIndex`), added as a term. -/
elab "det_index " id:ident " := " t:term : command => do
  let declName := (← getCurrNamespace) ++ id.getId
  let ix ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``Det.DetIndex))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unsafe evalExpr Det.DetIndex (mkConst ``Det.DetIndex) e
  liftCoreM <| addDecl <| .defnDecl
    { name := declName, levelParams := [], type := mkConst ``Det.DetIndex, value := toExpr ix,
      hints := .regular 0, safety := .safe }

/-- `kernel_rfl NAME : ∀ xs, l = r` (P1.3): the theorem NAME with proof `fun xs => Eq.refl l`, added
without the elaborator's definitional-equality check, so only the kernel checks that l and r are
definitionally equal. Used where the two sides are equal by unfolding but the elaborator's
heuristics give up (a structurally recursive function of a structure literal against the same
function of the variable it updates: Params.lean). Nothing is trusted: a false equation is
rejected by the kernel. -/
elab "kernel_rfl " id:ident " : " t:term : command => do
  let declName := (← getCurrNamespace) ++ id.getId
  let ty ← liftTermElabM do
    let ty ← Term.elabTerm t (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars ty
  let v ← liftTermElabM <| forallTelescope ty fun xs b => do
    let some (_, l, _) := b.eq? | throwError "kernel_rfl: not an equation"
    mkLambdaFVars xs (← mkEqRefl l)
  liftCoreM <| addDecl <| .thmDecl { name := declName, levelParams := [], type := ty, value := v }

end KCore
