/-
  Opaque constants reachable from what the kernel checks evaluate (run from the package root:
  `lake env lean test/OpaqueAudit.lean`, seconds). The kernel cannot unfold an opaque constant,
  while compiled code runs its implementation: a `parse`, `wf`, `emit` or `Reordered` that reaches
  one evaluates in compiled code (`diagnose`, the differentials) but gets stuck in the kernel.
  M2.3 met one: Lean v4.34.0 derives `BEq` for kore-lean's nested `KSort` as an opaque function,
  and a `==` on sorts in F1's `parse` blocked its kernel check. This test walks the values of the
  definitions reachable from each root (not proofs, which reduction never needs) and pins the
  opaque constants found. The only one is `String.Internal.append`, reached through panic
  messages, which no successful evaluation reaches (the kernel ties pass with it).
-/
import KcoreSpec

open Lean

/-- Opaque constants reachable through the values of definitions from `roots`, each with the
definition it was reached from. -/
def opaqueReach (roots : List Name) : MetaM (List Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := roots
  let mut out : List Name := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.opaqueInfo _) => out := n :: out
    | some (.defnInfo d) =>
      for c in d.value.getUsedConstants ++ d.type.getUsedConstants do
        unless seen.contains c do todo := c :: todo
    | _ => pure ()
  return out.mergeSort (·.toString < ·.toString)

/--
info: KCore.Parse.parse: [String.Internal.append]
KCore.wf: [String.Internal.append]
KCore.Definition.emit: [String.Internal.append]
KCore.Exec.successors: [String.Internal.append]
KoreAML.Reordered: []
-/
#guard_msgs in
#eval show MetaM Unit from do
  for root in [``KCore.Parse.parse, ``KCore.wf, ``KCore.Definition.emit, ``KCore.Exec.successors,
      ``KoreAML.Reordered] do
    IO.println s!"{root}: {← opaqueReach [root]}"

/-! Positive control: a comparison of KORE sorts with `==` reaches the derived opaque `BEq`. -/

def usesSortBEq (s : Kore.KSort) : Bool := s == s

/-- info: [Kore.instBEqKSort.beq] -/
#guard_msgs in
#eval show MetaM Unit from do IO.println s!"{← opaqueReach [``usesSortBEq]}"
