/-
  The milestone-1 subject (`milestone-1/peano.k` compiled by krust at b51b1f0e8 into
  `milestone-1/kore/definition.kore`, sha256 b1ca7917…9a8b) and its theory Γ_D.
-/
import KcoreSpec.Kore.Import
import KcoreSpec.Kore.Translate

set_option autoImplicit false

namespace KoreAML.Peano

/- `kore`: the KORE AST of `milestone-1/kore/definition.kore`, read at elaboration time. -/
kore_definition kore from "../milestone-1/kore/definition.kore"

/-- Γ_D for the subject: Γ^AML (the encoding's axioms) and AML(Γ) (its 202 axioms, translated). -/
def ΓD : Theory := Theory.ofDefinition kore

end KoreAML.Peano
