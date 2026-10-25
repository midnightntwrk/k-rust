import Lean

/-! Printing terms of the arity-indexed universe as K terms.

A library generated on the arity-indexed universe (`design.md`, §2.1) has one family `NS.Term : NS.Tag → Type` whose constructors are shared by every sort: `Term.c2 (s := t) c a0 a1` for a constructor of arity 2 of sort `t`, where `c : NS.T.C2` names it, and `Term.inj hs l h a` for the leaf injection of `a : Term l` into sort `t`; each sort's type is an abbreviation `NS.SortX := Term .«SortX»`.
Each K constructor is a reducible definition `NS.T.«c» a0 a1 := Term.c2 (s := .«T») NS.T.C2.«c» a0 a1`, and each leaf injection a definition `NS.T.inj_L a := Term.inj rfl .«SortL» rfl a` (with `Term.b_SortL a` for a builtin `L`, which also wraps a constructor's argument of a builtin sort), which `whnf`, `cases` and `simp` unfold.
This delaborator prints such a term, and a sort's type, by the name of its definition when the environment has one, so that goals read as K.
The proofs `hs` and `h` are propositions, so the printed term denotes the same term up to proof irrelevance.
`set_option pp.explicit true` turns it off. -/

namespace KPrelude.Delab

open Lean PrettyPrinter Delaborator SubExpr

/-- `NS` and the constructor's name, when `f` is a constructor of a family `NS.Term`. -/
def familyCtor? (env : Environment) (f : Name) : Option (Name × String) :=
  match f with
  | .str p@(.str ns "Term") c =>
    match env.find? p with
    | some (.inductInfo _) => some (ns, c)
    | _ => none
  | _ => none

/-- The name of the tag constant `NS.Tag.«SortX.Own»`'s sort, as a string (`SortX.Own`). -/
def tagName? (ns : Name) (e : Expr) : Option String :=
  match e with
  | .const (.str (.str ns' "Tag") s) _ => if ns' == ns then some s else none
  | _ => none

/-- The Lean name of the type of sort `s` (`SortX.Own` is `NS.SortX.Own`). -/
def sortType (ns : Name) (s : String) : Name :=
  (s.splitOn ".").foldl Name.str ns

/-- `target a0 … a(k-1)`, the definition that the family application being printed unfolds from,
its arguments from index `first` on. -/
def app (target : Name) (first k : Nat) : Delab := do
  let head := mkIdent (← unresolveNameGlobal target)
  if k == 0 then return head
  -- an argument of a builtin sort is wrapped in its carrier's constructor `Term.b_SortL v`
  let e ← getExpr
  let args ← (List.range k).toArray.mapM fun i => do
    let a := e.getArg! (first + i)
    let builtin := a.getAppNumArgs == 1 && (match a.getAppFn.constName? with
      | some (.str (.str _ "Term") b) => b.startsWith "b_" | _ => false)
    withNaryArg (first + i) (if builtin then withNaryArg 0 delab else delab)
  `($head $args*)

@[delab app]
def delabTerm : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  let .const f _ := e.getAppFn | failure
  let env ← getEnv
  -- the type `NS.Term NS.Tag.«SortX»`: its abbreviation `NS.SortX`
  if let .str ns "Term" := f then
    if e.getAppNumArgs == 1 && (env.find? f).any (·.isInductive) then
      let some s := tagName? ns (e.getArg! 0) | failure
      let target := sortType ns s
      unless env.contains target do failure
      return mkIdent (← unresolveNameGlobal target)
  let some (ns, c) := familyCtor? env f | failure
  if c == "inj" then
    -- `Term.inj {s} hs l h a`
    unless e.getAppNumArgs == 5 do failure
    let some s := tagName? ns (e.getArg! 0) | failure
    let some l := tagName? ns (e.getArg! 2) | failure
    let leaf := ((l.dropPrefix? "Sort").map (·.toString)).getD l
    let leaf := ((leaf.dropSuffix? ".Own").map (·.toString)).getD leaf
    let target := (sortType ns s).str ("inj_" ++ leaf)
    unless env.contains target do failure
    app target 4 1
  else
    -- `Term.ck {s} c a0 … a(k-1)`, with `c` a constructor of `NS.T.Ck`
    let some k := (c.dropPrefix? "c").bind (·.toString.toNat?) | failure
    unless e.getAppNumArgs == k + 2 do failure
    let .const (.str (.str sortNs ck) n) _ := (e.getArg! 1).getAppFn | failure
    unless ck == s!"C{k}" do failure
    let target := sortNs.str n
    unless env.contains target do failure
    app target 2 k

open Lean Elab Command Meta in
/-- `#k2l_check_delab NS`: for every K constructor and leaf injection of library `NS` (a
definition whose body is a constructor of `NS.Term`), check that the term it unfolds to, applied
to variables, prints as the definition applied to them; fail on the first that does not. -/
elab "#k2l_check_delab " id:ident : command => liftTermElabM do
  let ns := id.getId
  let env ← getEnv
  let fam := ns.str "Term"
  let mut checked : Nat := 0
  for (nm, ci) in env.constants.toList do
    let .defnInfo d := ci | continue
    unless ns.isPrefixOf nm do continue
    let ok ← forallTelescope d.type fun xs _ => do
      let body := (mkAppN d.value xs).headBeta
      let some (ns', _) := familyCtor? env (body.getAppFn.constName?.getD .anonymous) | return none
      unless ns' == ns && body.getAppFn.constName? != some (fam.str "coll") do return none
      -- only definitions named after their constructor: `T.«c»` for `Term.ck … T.Ck.«c» …`,
      -- `T.inj_L` for `Term.inj`
      let isCtor := match body.getAppFn.constName? with
        | some (.str _ "inj") => (match nm with | .str _ s => s.startsWith "inj_" | _ => false)
        | some (.str _ c) => c.startsWith "c" && body.getAppNumArgs ≥ 2 &&
            (match (body.getArg! 1).getAppFn.constName? with
              | some (.str (.str p _) n) => p.str n == nm | _ => false)
        | _ => false
      unless isCtor do return none
      let folded := mkAppN (.const nm (d.levelParams.map .param)) xs
      -- without generalized field notation, which prints `T.«c» a0` as `a0.«c»` when `a0 : T`
      let pp (e : Expr) : MetaM String := withTheReader Core.Context
        (fun c => { c with options := c.options.setBool `pp.fieldNotation.generalized false })
        (return toString (← Meta.ppExpr e))
      let a ← pp body
      let b ← pp folded
      return some (a == b, a, b)
    match ok with
    | none => pure ()
    | some (true, _, _) => checked := checked + 1
    | some (false, a, b) => throwError m!"#k2l_check_delab: {nm} unfolds to a term printed as{indentD a}\nnot as{indentD b}"
  if checked == 0 then throwError m!"#k2l_check_delab: no constructor of {fam} found"
  logInfo m!"#k2l_check_delab: {checked} constructors of {fam} print as K"

end KPrelude.Delab
