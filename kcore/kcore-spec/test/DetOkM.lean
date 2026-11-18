/-
  Determinism and coherence over `okM`, at a core whose rule has a predicate. Run from the package
  root: `lake env lean -j1 test/DetOkM.lean`. Kernel-checked.

  The core is e3-ml-rule-rhs-and-ctor's (`f2-examples/mlandc.kompile.kore`, `c(X) => X #And a()`)
  with its rule read by `Parse.andRuleOf`: `c(X) => X` with `post := mem X a` (test/PredFixtures.lean,
  `MlAndC`). Its `post` is not `\top`, so `ok` is false (`not_ok`) and `okM` holds (`okM`).
  - `coherent`: `CoherentAll` by `Det.coherentAll_of_nil_okM`.
  - `joins_00`: `Det.detCond_sound_okM` at the pair (0, 0): two steps by the rule from one
    configuration reach one configuration. The rule steps (`c(a)` to `a`, PredFixtures `step_ca`),
    so the statement is not vacuous.
-/
import KcoreSpec.ParseCmd
import KcoreSpec.ReadRuleConn
import KcoreSpec.FnExclusive

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace DetOkMTest

open Lean Elab Command in
/-- `definition_read_and NAME from "file.kore"`: `def NAME : Definition`, the definition
`Parse.parseWith Parse.andRuleOf` builds from the file, added as a term (not compiled). -/
elab "definition_read_and " id:ident " from " path:str : command => do
  let input ← IO.FS.readFile path.getString
  let k ← match Kore.parseDefinition input with
    | .error e => throwError "definition_read_and: {path.getString}: KORE read error {e}"
    | .ok k => pure k
  let d ← match Parse.parseWith Parse.andRuleOf k with
    | .ok d => pure d
    | .error r => throwError "definition_read_and: {path.getString}: refused: {r.toText}"
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``Definition, value := definitionExpr d,
    hints := .regular 0, safety := .safe }

definition_of defL from "f2-examples/mlandc.kompile.kore"
definition_read_and defA from "f2-examples/mlandc.kompile.kore"

/-- The landed reader's definition with its rules replaced by those `Parse.andRuleOf` reads. -/
noncomputable abbrev c : Semantics := { defL.sem with rules := defA.sem.rules }

/-- The one rule has a predicate: `post` is `mem X a`, not `\top`. -/
theorem post_not_top : c.rules.length = 1 ∧ c.rules.all (fun r => !r.post.isTop) = true := by
  decide +kernel

theorem not_ok : c.ok = false := by decide +kernel
theorem okM : c.okM = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel

/-- **Coherence over `okM`.** -/
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil_okM okM srReady matchReady (by decide +kernel) (by decide +kernel)

/-- **The decider is sound over `okM`** at the rule's diagonal pair. -/
theorem joins_00 {Inv : Config c → Prop} : Det.JoinsOn c Inv 0 0 :=
  Det.detCond_sound_okM okM srReady matchReady coherent rfl (0, 0) (by decide +kernel)

end DetOkMTest

/-- info: 'DetOkMTest.joins_00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DetOkMTest.joins_00
