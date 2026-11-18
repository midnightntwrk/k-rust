import KcoreSpec.KKPatValDen

/-!
# `matchTs` finds every substitution a denotation of argument lists gives

The forms of `KKMatchTotal` and `KKPatValDen` for a list of patterns and a list of values, as a
function's clause matches its arguments.

`matchTsF_of_den`: the converse of `matchTsF_den`. Where under `Bρ` each pattern form is the term
at its position (`DensF`) and the given substitution's entries are `Bρ`'s, every value `matchTs`
gives holds a substitution whose entries are `Bρ`'s, which states the match and binds every
variable of the forms. `matchTsF_complete_of_den` puts it together with `matchTsF_total` at
encodings, and `matchTsF_col_complete` with `patVals_densF`: where the patterns denote the values
under a well-sorted `σ` and a `Map` or `Set` pattern among them has at most one part that is no
element, `matchTs` at the encodings has a value that holds a substitution agreeing with `σ` and
binding every variable of the patterns. The conclusion is membership, as for one pattern.
-/

set_option autoImplicit false

namespace KCore.KK

open KCore.Exec (MatchCtxO)
open KCore.Faithful (collsOK)

/-- **`matchTs` finds what a denotation gives.** Where under `Bρ` each pattern form is the term at
its position and `B`'s entries are `Bρ`'s, every value `matchTs` gives from `B` holds a
substitution that extends `B`, whose entries are `Bρ`'s, which states the match and binds every
variable of the forms. -/
theorem matchTsF_of_den (S : List (Int × Int)) {ps ts : List T} {Bρ B : Bind} {M : Ms}
    (hd : DensF S Bρ ps ts) (hB : BindExt B Bρ) (h : matchTsF S ps ts B = some M) :
    ∃ B' ∈ M, BindExt B B' ∧ BindExt B' Bρ ∧ DensF S B' ps ts ∧
      ∀ x ∈ tvarsLF ps, (lookF x B').isSome = true := by
  obtain ⟨B', h1, h2⟩ := matchTsF_of_den_kct S hd hB h
  obtain ⟨g1, g2, -⟩ := matchTsF_den S ps ts h h1
  exact ⟨B', h1, g1, h2, g2, DensF.bound g2⟩

/-- **Completeness from a denotation, at the encodings of argument lists.** Where under `σ`
encoded the encodings of patterns sorted in a left side's context are the encodings of values of
their sorts, and `B` agrees with `σ`: `matchTs` has a value, and it holds a substitution that
extends `B`, agrees with `σ` and binds every variable of the patterns. -/
theorem matchTsF_complete_of_den {c : Semantics} (hov : c.ovls = []) {vars : List Srt}
    {ps : List Term} {qs : List T} {ss : List Srt} {vs : List GroundTerm} {σ : Subst} {B : Bind}
    (hq : encTermsWith c encLit ps = some qs) (hp : sortsOfTerms c.patCtxNF vars ps = some ss)
    (hv : c.sortsOf vs = some ss) (hd : DensF (subsF c) (bindOfSubst σ) qs (encTs vs))
    (hB : BindAgree B σ) :
    ∃ M, matchTsF (subsF c) qs (encTs vs) B = some M ∧ ∃ B' ∈ M, BindAgree B' σ ∧
      BindExt B B' ∧ ∀ i ∈ varOccsList ps, (lookF (i : Int) B').isSome = true := by
  obtain ⟨M, hM⟩ := Option.isSome_iff_exists.mp (matchTsF_total hov hq hp hv (subsF c) B)
  obtain ⟨B', h1, h2, h3, -, h5⟩ := matchTsF_of_den _ hd (bindAgree_iff_ext.mp hB) hM
  exact ⟨M, hM, B', h1, bindAgree_iff_ext.mpr h3, h2,
    fun i hi => h5 _ (encTermsWith_vars_kct (fun t _ => varsIn_kct t) hq i hi)⟩

section
variable {c : Semantics} (hmc : MatchCtxO c) (hov : c.ovls = []) (hcs : collsOK c = true)
  {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ)
include hmc hov hcs hσ

/-- **`matchTsF` is complete, collection patterns included.** `matchF_col_complete` of argument
lists: where the patterns `ps` denote the values `vs` under a well-sorted `σ`, a `Map` or `Set`
pattern among them has at most one part that is no element, and `B` agrees with `σ`, `matchTs`
at the encodings has a value, and the value holds a substitution that extends `B`, agrees with
`σ` and binds every variable of `ps`. The value may hold other substitutions. -/
theorem matchTsF_col_complete {ps : List Term} {qs : List T} {ss : List Srt}
    {vs : List GroundTerm} {B : Bind} (hq : encTermsWith c encLit ps = some qs)
    (hcp : colPatsOKL qs = true) (hp : sortsOfTerms c.patCtxNF vars ps = some ss)
    (lv : litsVL vs = true) (h : PatVals c σ ps vs) (hB : BindAgree B σ) :
    ∃ M, matchTsF (subsF c) qs (encTs vs) B = some M ∧ ∃ B' ∈ M, BindAgree B' σ ∧
      BindExt B B' ∧ ∀ i ∈ varOccsList ps, (lookF (i : Int) B').isSome = true :=
  matchTsF_complete_of_den hov hq hp (Det.patVals_sortedAll hmc hσ h hp)
    (patVals_densF hmc hov hcs hσ ps hq hcp hp lv h) hB

end

end KCore.KK
