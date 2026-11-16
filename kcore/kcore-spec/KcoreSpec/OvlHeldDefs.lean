/-
  KCore. Two ways a variable that a rule's left side leaves open is decided by values, as
  definitions over the data; no lemma reads them yet.

  - `Semantics.ovlHeld`: an overloading symbol each function in whose overload closure
    (`Semantics.fnOverloads`: the functions of `c.fns` labelled by a symbol of `ovlClosure`) takes
    arguments of confined sorts. An ordinary overloading symbol, whose closure holds no function,
    passes by the empty `all`.
  - `Cond.conjuncts`: the top-level conjuncts of a condition.
  - `memHeld`: a variable held by a cut, a conjunct `V ∈ t` of `pre` with V among the bound
    variables and t holding the variable (`heldOccs`).
-/
import KcoreSpec.FaithOK

set_option autoImplicit false

namespace KCore

/-- The functions in the overload closure of f: those of `c.fns` labelled by a symbol of
`ovlClosure f`. -/
def Semantics.fnOverloads (c : Semantics) (f : Sym) : List Fn :=
  (c.ovlClosure f).flatMap fun g => c.fns.filter (·.label == g)

/-- An overloading symbol each function in whose overload closure takes arguments of confined sorts. -/
def Semantics.ovlHeld (c : Semantics) (f : Sym) : Bool :=
  c.isOvl f && (c.fnOverloads f).all fun fn => fn.args.all c.confined

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
