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

/-! The proved lemmas of an author about the value of a generated function's call, by function:
`@[k2l_value]`, which the generator writes on each theorem of `Equations` that states an author's
simplification or lemma about a call's value (`g(X) >=Int 0 => true`, stated `Option.bind (K.g X) f =
some true`) and is proved. A later proof that cases on a call of `g` reads, from the lemma, that the
call is defined and what its value satisfies (`k2l_value_facts`, EQ-23). -/

/-- The function a lemma about a call's value is about: the body of its type, after its binders, is
`Option.bind (g xs) f = some c` with `g` a constant; none for a theorem of another form. -/
def valueHead? (type : Expr) : MetaM (Option Name) :=
  forallTelescopeReducing type fun _ body => do
    let some (_, lhs, rhs) := body.eq? | return none
    unless lhs.isAppOfArity ``Option.bind 4 && rhs.isAppOfArity ``Option.some 2 do return none
    let .const g _ := (lhs.getArg! 2).getAppFn | return none
    return some g

initialize k2lValueExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (g, thm) => m.insert g (((m.get? g).getD #[]).push thm)
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `k2l_value
  descr := "a proved lemma of an author about the value of a call, which a later proof that cases on the call reads"
  add := fun decl _ kind => do
    if let some g ← (valueHead? (← getConstInfo decl).type).run' then
      k2lValueExt.add (g, decl) kind
}

/-- The proved lemmas about the value of a call of `g`, in the order the library states them. -/
def valueLemmasOf (env : Environment) (g : Name) : Array Name :=
  ((k2lValueExt.getState env).get? g).getD #[]

end KPrelude
