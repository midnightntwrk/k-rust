/-
  KCore. A clause variable that neither the patterns nor the conditions hold (one of the right side
  or the `ensures` only), read where its sort has a value.

  `Eval.clause` asks a substitution well sorted on every variable of the clause, `Fails` one well
  sorted on the variables of its patterns and conditions (`leftVars`). Where each other variable is
  of a sort with a value, a substitution of the second kind extends to one of the first.
  `Semantics.RightHeld` states that of every clause of the definition's
  functions; `Semantics.rightValued` decides it, over `Semantics.valued`, a test of "the sort has a
  value" that exhibits the value (`Semantics.valued_value`): Int (`0`), Bool (`true`), or the result
  sort of a constructor without arguments. A sort with a value that `valued` does not exhibit
  (KItem, String, a token sort, a sort whose constructors all take arguments) is not decided by it;
  `RightHeld` is the Prop, and holds there too.

  None of these is read by `coreOK`. Where every clause's patterns bind every variable `RightHeld`
  holds (`rightHeld_of_binds`). Neither reads the interpretation of the parameters
  (`rightValued_withHooks`; `rightHeld_withHooks`, RightHeldHooks.lean).
-/
import KcoreSpec.Evaluation

set_option autoImplicit false

namespace KCore

/-- A sort with an exhibited value: Int (`0`), Bool (`true`), or the result sort of a constructor
without arguments (the constructor). -/
def Semantics.valued (c : Semantics) (s : Srt) : Bool :=
  s == Srt.int || s == Srt.bool ||
  c.ctorSigs.any fun k => (lookupSig c.ctorSigs k.name).any fun k' => k'.args.isEmpty && k'.result == s

/-- **A sort `valued` accepts has a value.** -/
theorem Semantics.valued_value {c : Semantics} {s : Srt} (h : c.valued s = true) : ∃ v, c.sortOf v = some s := by
  simp only [Semantics.valued, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Option.any_eq_true,
    Bool.and_eq_true, List.isEmpty_iff] at h
  rcases h with (rfl | rfl) | ⟨k, -, k', hk', ha, rfl⟩
  · exact ⟨.dv Srt.int (.int 0), by simp [Semantics.sortOf, show dvOK c.lib Srt.int (.int 0) = true from rfl]⟩
  · exact ⟨.dv Srt.bool (.bool true), by simp [Semantics.sortOf, show dvOK c.lib Srt.bool (.bool true) = true from rfl]⟩
  · exact ⟨.ctor k.name [], by simp [Semantics.sortOf, Semantics.sortsOf, hk', ha]⟩

/-- Each variable of each clause is held by the clause's patterns or conditions, or is of a sort
with a value. -/
def Semantics.RightHeld (c : Semantics) : Prop :=
  ∀ f ∈ c.fns, ∀ cl ∈ f.clauses, ∀ i s, cl.vars[i]? = some s →
    i ∈ cl.leftVars ∨ ∃ v, c.sortOf v = some s

/-- The decided form of `RightHeld`. -/
def Semantics.rightValued (c : Semantics) : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  (List.range cl.vars.length).all fun i =>
    cl.leftVars.contains i || (cl.vars[i]?.map c.valued).getD false

/-- **`rightValued` decides `RightHeld`**: a variable outside `leftVars` is of a sort `valued`
accepts, which has a value (`valued_value`). -/
theorem Semantics.rightHeld_of_valued {c : Semantics} (h : c.rightValued = true) : c.RightHeld := by
  intro f hf cl hcl i s hs
  have hi : i < cl.vars.length := (List.getElem?_eq_some_iff.mp hs).1
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h f hf) cl hcl) i
    (List.mem_range.mpr hi)
  rw [hs, Bool.or_eq_true, List.contains_iff_mem] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Semantics.valued_value h1)

/-- **Where every clause's patterns bind every variable, `RightHeld` holds**: each variable is in
`leftVars`. -/
theorem Semantics.rightHeld_of_binds {c : Semantics}
    (h : ∀ f ∈ c.fns, ∀ cl ∈ f.clauses, binds cl.vars.length (varOccsList cl.pats) = true) : c.RightHeld := by
  intro f hf cl hcl i s hs
  have hi : i < cl.vars.length := (List.getElem?_eq_some_iff.mp hs).1
  have h1 := List.all_eq_true.mp (h f hf cl hcl) i (List.mem_range.mpr hi)
  exact Or.inl (List.mem_append_left _ (List.contains_iff_mem.mp h1))

/-- `rightValued` does not read the interpretation of the parameters. -/
theorem Semantics.rightValued_withHooks (c : Semantics) (H : HookParams) :
    (c.withHooks H).rightValued = c.rightValued := rfl

/-! ## The functions the test does not accept, by name

`rightValued` is one Bool for the definition. `heldObligations` lists the functions with a clause
the test does not accept (the held-named functions): the theorems that derive `FnHyp` ask the held
variables of these alone, and of each either that (`HeldFn`, RightHeldExtend.lean) or that the
function has a result at every argument list (`HeldOwed`, Terminates.lean). -/

/-- `rightValued`'s test of one clause: each variable is in `leftVars` or of a sort `valued`
accepts. -/
def Semantics.clauseValued (c : Semantics) (cl : Clause) : Bool :=
  (List.range cl.vars.length).all fun i =>
    cl.leftVars.contains i || (cl.vars[i]?.map c.valued).getD false

/-- `rightValued` is `clauseValued` of every clause of every function. -/
theorem Semantics.rightValued_eq (c : Semantics) :
    c.rightValued = c.fns.all fun f => f.clauses.all c.clauseValued := rfl

/-- **The held-named functions**: those with a clause holding a variable outside `leftVars` whose
sort `valued` does not accept. -/
def Semantics.heldObligations (c : Semantics) : List Sym :=
  (c.fns.filter fun f => !f.clauses.all c.clauseValued).map (·.label)

/-- `heldObligations` does not read the interpretation of the parameters. -/
theorem Semantics.heldObligations_withHooks (c : Semantics) (H : HookParams) :
    (c.withHooks H).heldObligations = c.heldObligations := rfl

/-- **No function is held-named exactly where `rightValued` holds.** -/
theorem Semantics.heldObligations_eq_nil {c : Semantics} : c.heldObligations = [] ↔ c.rightValued = true := by
  rw [Semantics.rightValued_eq]
  simp [Semantics.heldObligations, List.filter_eq_nil_iff]

end KCore
