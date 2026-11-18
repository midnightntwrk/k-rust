/-
  `kore.k`'s matching against `PatVal`, collection patterns included
  (`KcoreSpec/KKDenPatVal.lean`): the statements, read at a clause and at a rule of `d₀ d` whose
  left sides may hold `Map`, `Set` and `List` patterns. Run from the package root:
  `lake env lean test/KKDenPatVal.lean`.
-/
import KcoreSpec.KKDenPatVal

set_option autoImplicit false

namespace KCore.KK.TestDenPatVal

open KCore KCore.KK

#check @den_patVal
#check @dens_patVals
#check @matchF_col_sound
#check @matchTsF_col_sound
#check @matchF_col_wellSorted
#check @matchTsF_col_wellSorted
#check @collSig_cdp
#check @collVal_concat_cdp
#check @parts_ground_cdp

/-- **Soundness at a clause, collection patterns included.** A substitution `matchTs` gives at
arguments of the function's argument sorts is read by a well-sorted `σ` under which the patterns
denote the arguments; no `noCbL`. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true)
    (hcs : Faithful.collsOK d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {qs : List T}
    (hq : encTermsWith d encLit cl.pats = some qs)
    (hb : binds cl.vars.length (varOccsList cl.pats) = true) {vs : List GroundTerm}
    (hv : (d₀ d).sortsOf vs = some fn.args) (lv : litsVL vs = true) {M : Ms} {B' : Bind}
    (hm : matchTsF (subsF d) qs (encTs vs) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep (d₀ d) cl.vars B' σ ∧ (d₀ d).WellSorted cl.vars σ ∧ PatVals (d₀ d) σ cl.pats vs := by
  obtain ⟨hmc, hov⟩ := matchCtx_d₀ hx he
  exact matchTsF_col_wellSorted hmc hov ((collsOK_d₀ d).trans hcs) ((encTermsWith_d₀ d _).trans hq)
    (clausePats_d₀ hx he hfn hcl) hv lv hb hm hB

/-- **Soundness at a rule, collection patterns included.** A substitution `match` gives at a
configuration is read by a well-sorted `σ` under which the rule's left side denotes it. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true)
    (hcs : Faithful.collsOK d = true) {r : Rule} (hr : r ∈ (d₀ d).rules) {q : T}
    (hq : encTerm d r.lhs = some q) (hb : binds r.vars.length (varOccs r.lhs) = true)
    {v : GroundTerm} (hv : (d₀ d).sortOf v = some topCellSort) (lv : litsV v = true) {M : Ms}
    {B' : Bind} (hm : matchF (subsF d) q (enc v) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep (d₀ d) r.vars B' σ ∧ (d₀ d).WellSorted r.vars σ ∧ PatVal (d₀ d) σ r.lhs v := by
  obtain ⟨hmc, hov⟩ := matchCtx_d₀ hx he
  exact matchF_col_wellSorted hmc hov ((collsOK_d₀ d).trans hcs) ((encTerm_d₀ d _).trans hq)
    (rulePat_d₀ hx he hr) hv lv hb hm hB

#print axioms den_patVal
#print axioms dens_patVals
#print axioms matchF_col_sound
#print axioms matchTsF_col_sound
#print axioms matchF_col_wellSorted
#print axioms matchTsF_col_wellSorted

end KCore.KK.TestDenPatVal
