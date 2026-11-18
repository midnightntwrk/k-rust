/-
  KCore. A variable that a rule's left side leaves open and a cut holds, as definitions over the
  data.

  - `Cond.conjuncts`: the top-level conjuncts of a condition.
  - `memHeld`: a variable held by a cut, a conjunct `V ∈ t` of `pre` with V among the bound
    variables and t holding the variable (`heldOccs`).
-/
import KcoreSpec.FaithOK

set_option autoImplicit false

namespace KCore

/-- The top-level conjuncts of a condition. -/
def Cond.conjuncts : Cond → List Cond
  | .and p q => p.conjuncts ++ q.conjuncts
  | p => [p]

/-- The variable i is held by a cut: a conjunct `V ∈ t`, V among `bound`, t holding i (`heldOccs`). -/
def memHeld (c : Semantics) (bound : List Nat) (pre : Cond) (i : Nat) : Bool :=
  pre.conjuncts.any fun
    | .mem _ (.var v) t => bound.contains v && (heldOccs c t).contains i
    | _ => false

end KCore
