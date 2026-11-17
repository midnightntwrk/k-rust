/-
  The milestone-1 subject (`milestone-1/peano.k` compiled by krust at b51b1f0e8 into
  `milestone-1/kore/definition.kore`, sha256 b1ca7917…9a8b) and its theory Γ_D, read from the
  package's copy `examples/peano/Peano/definition.kore` (sha256 0f0fcc9d…98fd): the same text with
  each `Source` attribute's absolute path written `milestone-1/peano.k`.
-/
import KcoreSpec.Kore.Import
import KcoreSpec.Kore.Translate

set_option autoImplicit false

namespace KoreAML.Peano

/- `kore`: the KORE AST of `examples/peano/Peano/definition.kore`, read at elaboration time. -/
kore_definition kore from "examples/peano/Peano/definition.kore"

/-- Γ_D for the subject: Γ^AML (the encoding's axioms) and AML(Γ) (its 202 axioms, translated). -/
def ΓD : Theory := Theory.ofDefinition kore

end KoreAML.Peano
