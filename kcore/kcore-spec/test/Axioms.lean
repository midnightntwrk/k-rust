/-
  The axioms of the whole library: every declaration of a `KcoreSpec.*` module (theorems,
  definitions, instances) depends on no axiom but `propext`, `Classical.choice` and `Quot.sound`.
  So no declaration uses `sorryAx` (a `sorry`), an `axiom` of its own, or `Lean.ofReduceBool`
  (`native_decide`). Fails, naming the declarations and the axioms, otherwise. Run from the package
  root: `lake env lean test/Axioms.lean`.
-/
import KcoreSpec

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless (`KcoreSpec).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    n := n + 1
    let other := (← collectAxioms c).filter (!std.contains ·)
    unless other.isEmpty do bad := bad.push (c, other)
  if n == 0 then throwError "no declaration of a KcoreSpec module found"
  unless bad.isEmpty do
    let shown := bad.toList.take 20 |>.map fun (c, a) => m!"{c}: {a.toList}"
    throwError m!"{bad.size} of {n} declarations depend on other axioms:{indentD (MessageData.joinSep shown Format.line)}"
  logInfo m!"axioms: {n} declarations of the KcoreSpec modules, each within propext, Classical.choice, Quot.sound"
