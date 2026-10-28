import KClaims

/-! Importing `KClaims` reserves no common identifier: the option words of `kc_auto` (`circ`,
`inv`, `close`, `fuel`) are non-reserved atoms, so an importer can still use them as names (a
structure's fields, a binder), as Mathlib's `Inv` class does with `inv`. -/

namespace KClaimsTest

structure Names where
  circ : Nat
  inv : Nat
  close : Nat
  fuel : Nat

def total (n : Names) : Nat := n.circ + n.inv + n.close + n.fuel

def countdown (fuel : Nat) : Nat := fuel

end KClaimsTest
