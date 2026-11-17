/-
  kore.k's text as kompile wrote it (`examples/ref-kk/RefKk/definition.kore`) has no open generator:
  no parameter of its semantics is `raw` (`koreSem_rawFree`, by the kernel on the parse). So the
  sort of every value, and with it the type of configurations, is the same at every interpretation
  `H` as at the parsed data's (`koreSem_sortOf_withHooks`, `koreSem_config_withHooks`), and the
  statements of the KORE in K row made at `HookParams.none` (`examples/ref-kk/User`,
  `KcoreSpec/KKStatements.lean`, `Config.toNone`) read the values and configurations of `defn.sem`
  itself. The obligation `OpenTotal` holds at every `H` (`koreSem_openTotal`), since it speaks of
  the raw parameters only. Run from the package root: `lake env lean test/KkRawFree.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KkRawFree

open KCore

definition_of defn from "examples/ref-kk/RefKk/definition.kore"

/-- kore.k's semantics, as the package `RefKk` states it (`RefKk.c`). -/
noncomputable abbrev koreSem : Semantics := defn.sem

/-- No parameter of kore.k's semantics is an open generator. -/
theorem koreSem_rawFree : ∀ k ∈ koreSem.params, k.raw = false := by decide +kernel

/-- A value's sort is the same at every interpretation. -/
theorem koreSem_sortOf_withHooks (H : HookParams) : (koreSem.withHooks H).sortOf = koreSem.sortOf :=
  Semantics.sortOf_withHooks koreSem H koreSem_rawFree

/-- The configurations at every interpretation are those of the parsed data. -/
theorem koreSem_config_withHooks (H : HookParams) : Config (koreSem.withHooks H) = Config koreSem :=
  KK.config_withHooks koreSem H koreSem_rawFree

/-- `OpenTotal` is no obligation of kore.k's statements: it holds at every interpretation. -/
theorem koreSem_openTotal (H : HookParams) : OpenTotal (koreSem.withHooks H) :=
  openTotal_of_plain fun k hk => koreSem_rawFree k hk

/-- The KORE in K row's interpretation `HookParams.none` is one of them. -/
example : Config (koreSem.withHooks HookParams.none) = Config koreSem :=
  koreSem_config_withHooks HookParams.none

end KCore.KkRawFree
