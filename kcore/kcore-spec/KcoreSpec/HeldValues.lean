/-
  KCore. The variables a term holds, at a value: over `heldOccs`, and over a cut.

  - `heldOccs_witnessed`: in a model of `Γ`, if the element of a value of a well-sorted right
    side's sort lies in its translation, at a valuation of its variables in their sorts, the
    valuation gives each variable of `heldOccs` the element of a value of its sort. It is
    `occsUnder_witnessed` at the `collHeld` symbols, the symbols `Semantics.holds` names.
-/
import KcoreSpec.OccsUnder
import KcoreSpec.OvlHeldDefs
import KcoreSpec.OpenSuccessor

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section HeldOccs
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
  [OvlOK c] (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) (hph : patHooksApart c = true) (hcs : collsOK c = true) (hcso : collSortsOK c = true)
  {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
  {L : List CtorSig} (hL : HeadsOK c L)
include hI hg htr hnm hph hcs hcso hvs hin hL

/-- **A right-hand side's held variables, at a value.** If the element of a value of a well-sorted
right-hand side's sort lies in its translation, at a valuation of its variables in their sorts,
the valuation gives each variable the term holds under constructors, injections and the unit,
element and concatenation symbols of the collections the element of a value of its sort. -/
theorem heldOccs_witnessed {t : Term} {s : Srt} {w : GroundTerm}
    (ht : sortOfTerm (c.rhsCtx L) vars t = some s) (hw : c.sortOf w = some s)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e (elemOf c I w)) :
    ∀ i ∈ heldOccs c t, Witnessed c I tbl vs vars e i := by
  intro i hi
  rw [heldOccs_eq] at hi
  exact occsUnder_witnessed hI hg htr hnm hvs hin hL
    (fun f k hc hh hk => collHeld_back hI hg htr hph hcs hcso hc hh hk) ht hw hm i hi

end HeldOccs

end KCore
