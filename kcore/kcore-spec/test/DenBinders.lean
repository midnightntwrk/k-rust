/-
  Two facts the statements over conditions rest on, each checked by `rfl`.
  `KoreAML.den` reads a pattern with the empty variable table, so every element variable is read at
  one index: `x = y` and `x = x` have one pattern. It is for patterns without variables; a pattern
  that binds variables is read by `KoreAML.denB`.
  A Bool literal is a value of Bool in every semantics, so Bool has a value, and a predicate written
  at Bool (`Clause.condK`) is at a sort that is not empty in a model of `Γ`.
  Run from kcore-spec, after the library: `lake env lean test/DenBinders.lean`.
-/
import KcoreSpec

set_option autoImplicit false

open KoreAML in
example (S : Kore.KSort) (x y : Kore.EVar) :
    den (.equals S S (.var (.evar x)) (.var (.evar y))) =
    den (.equals S S (.var (.evar x)) (.var (.evar x))) := rfl

section
open KCore

example (c : Semantics) : c.sortOf (bool true) = some Srt.bool := rfl

end
