/-
  KCore. A decided test of "the sort has a value at every interpretation of the parameters", wider
  than `Semantics.valued`.

  `Semantics.hasValue c s` accepts a sort that `valued` accepts, a sort with one of four probe
  literals (`hasLit`), a collection sort whose empty collection is a value (`hasEmpty`), and a sort
  reached from those by constructors and injections (`witnessed`). An overloading symbol and a raw
  parameter are no generators here: an application of the first is a value only at arguments no
  overload covers, of the second only where the interpretation of the parameters leaves it raw.
  None of the four reads `c.hooks`.

  The lemma that an accepted sort has a value on a definition with `coreOK` is
  `hasValue_value` (HasValueValue.lean).
-/
import KcoreSpec.RightHeld

set_option autoImplicit false

namespace KCore

/-- One of four literals is a literal of the sort (`dvOK`): that literal is a value of it. -/
def Semantics.hasLit (c : Semantics) (s : Srt) : Bool :=
  [Lit.int 0, .bool true, .tok "", .float 1 1 0].any (dvOK c.lib s)

/-- The sort is a collection sort whose empty collection is a value. -/
def Semantics.hasEmpty (c : Semantics) (s : Srt) : Bool :=
  match c.collOf s with
  | some k => (match k.kind with | .map | .rangeMap => k.val.isSome | _ => true)
  | none => false

/-- Sorts with a value at every interpretation of the parameters: closed under constructors and
injections from the sorts with one of four literals or an empty collection. -/
def Semantics.witnessed (c : Semantics) : List Srt :=
  let univ := [Srt.k, Srt.kitem] ++ c.lib.sortsBelowKItem ++ c.userSorts
  let step := fun (inh : List Srt) =>
    let ok := fun a => inh.contains a || c.hasLit a || c.hasEmpty a
    inh ++ univ.filter fun N => !inh.contains N &&
      ((c.ctorSigs.any fun k => k.result == N && k.args.all ok) ||
       (c.subsorts.any fun p => p.2 == N && ok p.1))
  Nat.repeat step univ.length (univ.filter fun s => c.hasLit s || c.hasEmpty s)

/-- A sort with a value at every interpretation of the parameters, decided: `valued`, a probe
literal, an empty collection, or reached by constructors and injections. -/
def Semantics.hasValue (c : Semantics) (s : Srt) : Bool :=
  c.valued s || c.hasLit s || c.hasEmpty s || c.witnessed.contains s

/-- `hasValue` does not read the interpretation of the parameters. -/
theorem Semantics.hasValue_withHooks (c : Semantics) (H : HookParams) (s : Srt) :
    (c.withHooks H).hasValue s = c.hasValue s := by
  unfold Semantics.hasValue
  rw [Semantics.valued_withHooks]
  rfl

/-- A sort `valued` accepts, `hasValue` accepts. -/
theorem Semantics.hasValue_of_valued {c : Semantics} {s : Srt} (h : c.valued s = true) : c.hasValue s = true := by
  simp [Semantics.hasValue, h]

end KCore
