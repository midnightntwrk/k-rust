/-
  What is asked of one clause's existential variables (`Clause.exs`) and right-side predicate
  (`Clause.post`) for the function's values to be values the clause's instances give.

  A function's value is not a given value, so an existential variable of a clause is decided by
  values in two ways only: its sort is confined (`Semantics.confined`: its elements in a model are
  the values'), or the predicate equates it with a term over variables that are decided
  (`Clause.fixedExs`: `Z ∈ t` or `Z = t` at values of t's variables holds at the value of t, or
  nowhere; a variable of t bound by a binder of the predicate is decided where its sort is confined,
  or has a value, `Semantics.valued`, and the binder's body fixes it). `f() => c(?Z:Int)` has neither: its value at an element of Int that is no value's is
  no value's.
-/
import KcoreSpec.FaithOK

set_option autoImplicit false

namespace KCore

/-- A clause without existential variables has the right-side predicate `\top`, and each
existential variable is of a confined sort or fixed by the predicate (`Clause.fixedExs`, over the
other existential variables of a confined sort; a binder's variable is admitted where its sort has
a value, `Semantics.valued`, and the body fixes it). -/
def Semantics.clausePlainEx (c : Semantics) (cl : Clause) : Bool :=
  let conf := fun i => (cl.vars[i]?.map c.confined).getD false
  (!cl.exs.isEmpty || cl.post.isTop) &&
  cl.exs.all (fun i => conf i || (cl.fixedExs c.confined c.valued).contains i)

/-- A clause with no existential variable and the predicate `\top` has it. -/
theorem Semantics.clausePlainEx_of_nil {c : Semantics} {cl : Clause} (hex : cl.exs = [])
    (hpost : cl.post.isTop = true) : c.clausePlainEx cl = true := by
  simp [Semantics.clausePlainEx, hex, hpost]

/-- A clause with no existential variable has it exactly where its predicate is `\top`. -/
theorem Semantics.clausePlainEx_nil_iff {c : Semantics} {cl : Clause} (hex : cl.exs = []) :
    c.clausePlainEx cl = true ↔ cl.post.isTop = true := by
  simp [Semantics.clausePlainEx, hex]

end KCore
