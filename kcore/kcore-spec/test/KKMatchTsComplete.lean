/-
  `matchTs` is complete at argument lists, collection patterns included
  (`KcoreSpec/KKMatchTsComplete.lean`): the statements, read from the empty substitution.
  Run from the package root: `lake env lean test/KKMatchTsComplete.lean`.
-/
import KcoreSpec.KKMatchTsComplete

set_option autoImplicit false

namespace KCore.KK.TestMatchTsComplete

open KCore KCore.KK

#check @matchTsF_of_den
#check @matchTsF_complete_of_den
#check @matchTsF_col_complete

/-- **Completeness at argument lists, collection patterns included.** Where the patterns denote
the values under a well-sorted `σ`, `matchTs` from the empty substitution has a value that holds a
substitution agreeing with `σ` and binding every variable of the patterns; no `noCbL`. -/
example {c : Semantics} (hmc : Exec.MatchCtxO c) (hov : c.ovls = [])
    (hcs : Faithful.collsOK c = true) {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ)
    {ps : List Term} {qs : List T} {ss : List Srt} {vs : List GroundTerm}
    (hq : encTermsWith c encLit ps = some qs) (hcp : colPatsOKL qs = true)
    (hp : sortsOfTerms c.patCtxNF vars ps = some ss) (lv : litsVL vs = true)
    (h : PatVals c σ ps vs) :
    ∃ M, matchTsF (subsF c) qs (encTs vs) [] = some M ∧ ∃ B' ∈ M, BindAgree B' σ ∧
      ∀ i ∈ varOccsList ps, (lookF (i : Int) B').isSome = true := by
  obtain ⟨M, hM, B', hB', h1, -, h2⟩ :=
    matchTsF_col_complete hmc hov hcs hσ hq hcp hp lv h (bindAgree_nil σ)
  exact ⟨M, hM, B', hB', h1, h2⟩

/-- The one-pattern form is the list form at a singleton: `matchTs` at `[q]` and `[a]` finds
what `match` at `q` and `a` finds. -/
example {S : List (Int × Int)} {Bρ B : Bind} {M : Ms} {q a : T} (hd : DenF S Bρ q a)
    (hB : BindExt B Bρ) (h : matchTsF S [q] [a] B = some M) :
    ∃ B' ∈ M, BindExt B' Bρ ∧ ∀ x ∈ tvarsF q, (lookF x B').isSome = true := by
  obtain ⟨B', hB', -, h1, -, h2⟩ := matchTsF_of_den S (.cons hd .nil) hB h
  exact ⟨B', hB', h1, fun x hx => h2 x (by simpa [tvarsLF] using hx)⟩

#print axioms matchTsF_of_den
#print axioms matchTsF_complete_of_den
#print axioms matchTsF_col_complete

end KCore.KK.TestMatchTsComplete
