/-
  The witness modules (`KcoreSpec/Model*Witness.lean`): semantics built to show that a condition of
  `coreOK` or of the hypotheses cannot be dropped (each module's header says which). For each
  module: its theorems, each depending on no axiom but `propext`, `Classical.choice` and
  `Quot.sound`, and the names of the negative ones among them (`no_model`, `not_*`).
  Fails when a module has no theorem or a theorem depends on another axiom. Run from the package
  root: `lake env lean test/Witnesses.lean`.
-/
import KcoreSpec

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.header.moduleNames.filter fun m =>
    (`KcoreSpec).isPrefixOf m && m.toString.startsWith "KcoreSpec.Model" && m.toString.endsWith "Witness"
  if mods.isEmpty then throwError "no witness module found"
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    if mods.contains m && ci matches .thmInfo _ && !c.isInternal then
      byMod := byMod.insert m ((byMod.getD m #[]).push c)
  let mut lines : Array MessageData := #[]
  let mut bad : Array MessageData := #[]
  for m in mods.qsort (·.toString < ·.toString) do
    let thms := byMod.getD m #[]
    if thms.isEmpty then bad := bad.push m!"{m}: no theorem"
    for c in thms do
      let other := (← collectAxioms c).filter (!std.contains ·)
      unless other.isEmpty do bad := bad.push m!"{c}: {other.toList}"
    let neg := thms.filter fun c => match c with
      | .str _ s => s == "no_model" || s.startsWith "not_"
      | _ => false
    let negs := (neg.qsort (·.toString < ·.toString)).toList.map fun c => c.componentsRev.head!.toString
    lines := lines.push m!"{m}: {thms.size} theorems, negative: {negs}"
  unless bad.isEmpty do
    throwError m!"witnesses:{indentD (MessageData.joinSep bad.toList Format.line)}"
  logInfo m!"{MessageData.joinSep lines.toList Format.line}\nwitnesses: {mods.size} modules, every theorem within propext, Classical.choice, Quot.sound"
