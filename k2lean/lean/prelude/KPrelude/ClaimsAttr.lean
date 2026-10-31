import Lean

/-! The generated theorems that two bindings of a map claiming one thing are one binding:
`@[k2l_claims_apart]`, which `gen --invariant` writes on each `Invariant.F_apart` (a fold of claims
`F` whose `noDup` is a whole part of the invariant). `k2l_one_binding` (`KPrelude.OneBinding`)
applies them. -/

namespace KPrelude

open Lean

initialize k2lClaimsApartExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun a n => a.push n
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `k2l_claims_apart
  descr := "two bindings of a map that claim one thing are one binding, under an invariant (gen --invariant)"
  add := fun decl _ kind => k2lClaimsApartExt.add decl kind
}

/-- The `@[k2l_claims_apart]` theorems, in the order they were declared. -/
def claimsApartTheorems (env : Environment) : Array Name := k2lClaimsApartExt.getState env

end KPrelude
