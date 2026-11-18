/-
  The C2 evidence of four inert entries whose construct leaves a mark in the kompiled text but no
  sentence the reading states: for each, the fixture's text and its companion's (a text kompile
  writes without the construct, or with the construct's effect written by hand) have one semantics,
  the literal `defn.sem` of the one equal to the other's (`rfl`). At every H the two are then one
  semantics (`withHooks_eq`), with one Γ and one `Step`: the construct changes neither the theory nor
  the steps.
  The texts are the fixtures' kompiled texts that their `kompile.txt` records, with their paths
  restored (`f2-examples/NAME.kompile.kore`). Run from the package root:
  `lake env lean -j1 test/InertSemPairs.lean`. Nothing reads `Parse.parse` or `emit`.

  - `E8`: `--disable-ceil-simplification-rules` (fixture e8-disable-ceil-simplification-rules
    against e8-ref, the same K text kompiled without the option). The option removes six `#Ceil`
    simplification axioms of the library's text and adds none.
  - `CtorUnit`: `unit` on a constructor's production (fixture c3-ctor-unit against
    c3-ctor-law-base). The texts differ in the declaration of `plus` alone, which carries
    `unit{}(Lbl'Stop'E{}())` in the first; neither text has a unit axiom.
  - `StrictAlias`: `strict(c)` through a context alias (fixture c3-strict-alias against
    c3-strict-base, `strict` alone). The texts differ in the `UNIQUE'Unds'ID` of the heating and the
    cooling rule of `twice` alone, their patterns equal.
  - `MacroUse`: a use of a macro (fixture c3-macro-rule, `rule f(X) => m(X)` with `m` a macro of
    `rule m(X) => g(X)`, against c3-macro-rule-expanded, `rule f(X) => g(X)` written by hand). The
    texts differ in the `UNIQUE'Unds'ID` of `f`'s equation alone; the macro's rule has no sentence in
    either.

  With `StrictAlias` and `MacroUse`, the reading of a rewrite axiom and of an equation does not
  depend on the value of its `UNIQUE'Unds'ID`. `trS_attrs` states that the translation of a sentence
  does not read its attributes at all.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.InertSemPairs

open KCore ML Faithful KoreAML

/-- **The translation of an axiom does not read its attributes**: the item's pattern is the same
for every attribute list. -/
theorem trS_attrs (decls : List SymbolDecl) (aliases : List String) (i : Nat) (m : String)
    (a : Kore.Axiom) (as : List Kore.AppPattern) :
    (trAxiom decls aliases ⟨i, m, { a with attributes := as }⟩).pat = (trAxiom decls aliases ⟨i, m, a⟩).pat := rfl

namespace E8
namespace Opt
definition_of defn from "f2-examples/e8-disable-ceil-simplification-rules.kompile.kore"
end Opt
namespace Ref
definition_of defn from "f2-examples/e8-ref.kompile.kore"
end Ref

/-- **The option leaves the semantics as it is.** -/
theorem sem_eq : Opt.defn.sem = Ref.defn.sem := rfl
theorem withHooks_eq (H : HookParams) : Opt.defn.sem.withHooks H = Ref.defn.sem.withHooks H :=
  congrArg (Semantics.withHooks · H) sem_eq
theorem gamma_eq (H : HookParams) : Γ (Opt.defn.sem.withHooks H) = Γ (Ref.defn.sem.withHooks H) := by
  rw [withHooks_eq]
end E8

namespace CtorUnit
namespace Unit
definition_of defn from "f2-examples/c3-ctor-unit.kompile.kore"
end Unit
namespace Base
definition_of defn from "f2-examples/c3-ctor-law-base.kompile.kore"
end Base

/-- **`unit` on the constructor leaves the semantics as it is.** -/
theorem sem_eq : Unit.defn.sem = Base.defn.sem := rfl
theorem withHooks_eq (H : HookParams) : Unit.defn.sem.withHooks H = Base.defn.sem.withHooks H :=
  congrArg (Semantics.withHooks · H) sem_eq
theorem gamma_eq (H : HookParams) : Γ (Unit.defn.sem.withHooks H) = Γ (Base.defn.sem.withHooks H) := by
  rw [withHooks_eq]
end CtorUnit

namespace StrictAlias
namespace Alias
definition_of defn from "f2-examples/c3-strict-alias.kompile.kore"
end Alias
namespace Base
definition_of defn from "f2-examples/c3-strict-base.kompile.kore"
end Base

/-- **`strict` through the context alias leaves the semantics as `strict` does.** -/
theorem sem_eq : Alias.defn.sem = Base.defn.sem := rfl
theorem withHooks_eq (H : HookParams) : Alias.defn.sem.withHooks H = Base.defn.sem.withHooks H :=
  congrArg (Semantics.withHooks · H) sem_eq
theorem gamma_eq (H : HookParams) : Γ (Alias.defn.sem.withHooks H) = Γ (Base.defn.sem.withHooks H) := by
  rw [withHooks_eq]
end StrictAlias

namespace MacroUse
namespace Macro
definition_of defn from "f2-examples/c3-macro-rule.kompile.kore"
end Macro
namespace Expanded
definition_of defn from "f2-examples/c3-macro-rule-expanded.kompile.kore"
end Expanded

/-- **A use of the macro is read as its expansion written by hand.** -/
theorem sem_eq : Macro.defn.sem = Expanded.defn.sem := rfl
theorem withHooks_eq (H : HookParams) : Macro.defn.sem.withHooks H = Expanded.defn.sem.withHooks H :=
  congrArg (Semantics.withHooks · H) sem_eq
theorem gamma_eq (H : HookParams) : Γ (Macro.defn.sem.withHooks H) = Γ (Expanded.defn.sem.withHooks H) := by
  rw [withHooks_eq]
end MacroUse

end KCore.InertSemPairs

#check @KCore.InertSemPairs.trS_attrs
#check @KCore.InertSemPairs.E8.sem_eq
#check @KCore.InertSemPairs.CtorUnit.sem_eq
#check @KCore.InertSemPairs.StrictAlias.sem_eq
#check @KCore.InertSemPairs.MacroUse.sem_eq
#print axioms KCore.InertSemPairs.trS_attrs
#print axioms KCore.InertSemPairs.E8.withHooks_eq
#print axioms KCore.InertSemPairs.E8.gamma_eq
#print axioms KCore.InertSemPairs.CtorUnit.withHooks_eq
#print axioms KCore.InertSemPairs.CtorUnit.gamma_eq
#print axioms KCore.InertSemPairs.StrictAlias.withHooks_eq
#print axioms KCore.InertSemPairs.StrictAlias.gamma_eq
#print axioms KCore.InertSemPairs.MacroUse.withHooks_eq
#print axioms KCore.InertSemPairs.MacroUse.gamma_eq
