import Lean

/-! The proved equations of the generated functions, by function: `@[k2l_equation]`, which the
generator writes on each theorem of `Equations` that states a K equation (`Eqn.*`) and is proved.
A claim's proof rewrites a function's value with them where its arguments are symbolic and an
equation's premises follow from the facts (`KClaims`), as K evaluates a function: by the equation
whose `requires` holds. An open obligation is no theorem and has no attribute. -/

namespace KPrelude

open Lean Meta

/-- The function a proved equation is about: the head of its left-hand side (`f args = …`, or
`some (f args) = …` for a total function whose right-hand side has partial calls). -/
def equationHead (type : Expr) : MetaM Name :=
  forallTelescopeReducing type fun _ body => do
    let some (_, lhs, _) := body.eq? | throwError "k2l_equation: not an equation{indentExpr body}"
    let lhs := if lhs.isAppOfArity ``Option.some 2 then lhs.appArg! else lhs
    let .const f _ := lhs.getAppFn | throwError "k2l_equation: no function at the head{indentExpr lhs}"
    return f

initialize k2lEquationExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (f, thm) => m.insert f (((m.get? f).getD #[]).push thm)
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `k2l_equation
  descr := "a proved K equation of a generated function, by which a claim's proof may rewrite its value"
  add := fun decl _ kind => do
    let f ← (equationHead (← getConstInfo decl).type).run'
    k2lEquationExt.add (f, decl) kind
}

/-- The proved equations of `f`, in the order the library states them. -/
def equationsOf (env : Environment) (f : Name) : Array Name :=
  ((k2lEquationExt.getState env).get? f).getD #[]

end KPrelude
