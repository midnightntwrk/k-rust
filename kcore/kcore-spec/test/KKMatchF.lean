/-
  `kore.k`'s matching of a pattern without a collection (`KcoreSpec/KKMatchF.lean`) and its two
  statements against `PatVal` (`KcoreSpec/KKMatchFSpec.lean`): the mirrors at small arguments, and
  the statements read at a clause of `d₀ d` from what `Fails` hands over. Run from the package root:
  `lake env lean test/KKMatchF.lean`.
-/
import KcoreSpec.KKMatchFSpec

set_option autoImplicit false

namespace KCore.KK.TestMatchF

open KCore KCore.KK

#check @matchF
#check @matchTsF
#check @matchKF
#check @bindAfterF
#check @lookF
#check @bindVarF
#check @leqF
#check @leqF_eq
#check @leqF_subsF
#check @encDef_subs
#check @matchF_sound
#check @matchTsF_sound
#check @matchF_complete
#check @matchTsF_complete
#check @matchF_wellSorted
#check @matchTsF_wellSorted
#check @matchCtx_d₀
#check @clausePats_d₀
#check @rulePat_d₀
#check @matchF.induct

/-- `leq` has a result on a cyclic table, by `above`'s fuel. -/
example : leqF 1 2 [(1, 3), (3, 1)] = false := by simp [leqF, aboveF]

/-- Two steps of a table that is not transitive: `leq` is the closure, not the table. -/
example : leqF 1 3 [(1, 2), (2, 3)] = true := by simp [leqF, aboveF]

/-- `matchTs` has no equation at lists of two lengths, so `match` has no value there. -/
example : matchF [] (.ap 7 [.vr 0]) (.ap 7 []) [] = none := by
  rw [matchF_ap_ap]; simp [matchTsF]

/-- An application of another symbol does not match (`m-fail`). -/
example : matchF [] (.ap 7 [.vr 0]) (.ap 8 [.iv 1]) [] = some [] := by
  rw [matchF_ap_ap]; simp

/-- A variable seen twice is bound to one term. -/
example : matchF [] (.ap 7 [.vr 0, .vr 0]) (.ap 7 [.iv 1, .iv 1]) [] = some [[(0, .iv 1)]] := by
  simp [matchF_ap_ap, matchTsF_cons, matchTsF_nil, matchKF_cons, matchKF_nil, matchF_vr, bindVarF,
    lookF]

example : matchF [] (.ap 7 [.vr 0, .vr 0]) (.ap 7 [.iv 1, .iv 2]) [] = some [] := by
  simp [matchF_ap_ap, matchTsF_cons, matchKF_cons, matchKF_nil, matchF_vr, bindVarF, lookF]

/-- `m-inj-sub`: an injection from a subsort of the pattern's source matches the pattern's
argument against the value injected into that source. -/
example : matchF [(4, 5)] (.ij 5 9 (.vr 0)) (.ij 4 9 (.iv 1)) [] = some [[(0, .ij 4 5 (.iv 1))]] := by
  simp [matchF_ij_ij, matchF_vr, bindVarF, lookF, leqF, aboveF]

/-- The targets of the two injections are not compared: the statements take the value at the
pattern's sort. -/
example : matchF [] (.ij 5 9 (.vr 0)) (.ij 5 8 (.iv 1)) [] = some [[(0, .iv 1)]] := by
  simp [matchF_ij_ij, matchF_vr, bindVarF, lookF]

/-- An alias binds its variable after its pattern. -/
example : matchF [] (.as (.iv 1) 3) (.iv 1) [] = some [[(3, .iv 1)]] := by
  simp [matchF_as, matchF_iv, bindAfterF, bindVarF, lookF]

/-- **Completeness at a clause, from what `Fails` hands over.** Under `execReady d` and
`encodable d`, for a clause whose encoded patterns hold no `cb` and bind every variable: a `σ`
that is well sorted at the clause's left variables and under which the patterns denote `vs` is
found by `matchTs` on the encodings, as its one substitution. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {qs : List T}
    (hq : encTermsWith d encLit cl.pats = some qs) (hcb : noCbL qs = true)
    (hb : binds cl.vars.length (varOccsList cl.pats) = true) {σ : Subst} {vs : List GroundTerm}
    (hσ : (d₀ d).WellSortedAt cl.vars cl.leftVars σ) (hm : PatVals (d₀ d) σ cl.pats vs) :
    ∃ B', matchTsF (subsF d) qs (encTs vs) [] = some [B'] ∧ BindAgree B' σ ∧
      ∀ i ∈ varOccsList cl.pats, (lookF (i : Int) B').isSome = true := by
  obtain ⟨hmc, hov⟩ := matchCtx_d₀ hx he
  obtain ⟨B', h1, h2, -, h4⟩ := matchTsF_complete hmc hov (vars := cl.vars)
    ((encTermsWith_d₀ d _).trans hq) hcb (clausePats_d₀ hx he hfn hcl)
    (wellSorted_of_at_kmf hσ hb fun i hi => List.mem_append_left _ hi) hm (bindAgree_nil σ)
  exact ⟨B', h1, h2, h4⟩

/-- **Soundness at a clause.** A substitution `matchTs` gives at arguments of the function's
argument sorts is read by a well-sorted `σ` under which the patterns denote the arguments. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {qs : List T}
    (hq : encTermsWith d encLit cl.pats = some qs) (hcb : noCbL qs = true)
    (hb : binds cl.vars.length (varOccsList cl.pats) = true) {vs : List GroundTerm}
    (hv : (d₀ d).sortsOf vs = some fn.args) (lv : litsVL vs = true) {M : Ms} {B' : Bind}
    (hm : matchTsF (subsF d) qs (encTs vs) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep (d₀ d) cl.vars B' σ ∧ (d₀ d).WellSorted cl.vars σ ∧ PatVals (d₀ d) σ cl.pats vs := by
  obtain ⟨hmc, hov⟩ := matchCtx_d₀ hx he
  exact matchTsF_wellSorted hmc hov ((encTermsWith_d₀ d _).trans hq) hcb
    (clausePats_d₀ hx he hfn hcl) hv lv hb hm hB

#print axioms matchF
#print axioms leqF_subsF
#print axioms matchF_sound
#print axioms matchTsF_sound
#print axioms matchF_complete
#print axioms matchTsF_complete
#print axioms matchF_wellSorted
#print axioms matchTsF_wellSorted

end KCore.KK.TestMatchF
