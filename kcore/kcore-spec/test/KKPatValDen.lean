/-
  `PatVal` as a substitution of `kore.k`'s `match`, collection patterns included
  (`KcoreSpec/KKPatValDen.lean`): the statements, read at a rule of `d₀ d` whose left side may
  hold `Map`, `Set` and `List` patterns. Run from the package root:
  `lake env lean test/KKPatValDen.lean`.
-/
import KcoreSpec.KKPatValDen

set_option autoImplicit false

namespace KCore.KK.TestPatValDen

open KCore KCore.KK

#check @patVal_denF
#check @patVals_densF
#check @matchF_col_complete
#check @collParts_cpv
#check @denCol_of_chunks_cpv
#check @builds_concat_cpv

/-- **Completeness at a rule, collection patterns included.** Where a rule's left side denotes a
configuration under a well-sorted `σ`, `match` from the empty substitution has a value that holds
a substitution agreeing with `σ` and binding every variable of the left side; no `noCb`. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true)
    (hcs : Faithful.collsOK d = true) {r : Rule} (hr : r ∈ (d₀ d).rules) {q : T}
    (hq : encTerm d r.lhs = some q) (hcp : colPatOK q = true) {σ : Subst}
    (hσ : (d₀ d).WellSorted r.vars σ) {v : GroundTerm} (lv : litsV v = true)
    (h : PatVal (d₀ d) σ r.lhs v) :
    ∃ M, matchF (subsF d) q (enc v) [] = some M ∧ ∃ B' ∈ M, BindAgree B' σ ∧
      ∀ i ∈ varOccs r.lhs, (lookF (i : Int) B').isSome = true := by
  obtain ⟨hmc, hov⟩ := matchCtx_d₀ hx he
  obtain ⟨M, hM, B', hB', h1, -, h2⟩ := matchF_col_complete hmc hov ((collsOK_d₀ d).trans hcs) hσ
    ((encTerm_d₀ d _).trans hq) hcp (rulePat_d₀ hx he hr) lv h (bindAgree_nil σ)
  exact ⟨M, hM, B', hB', h1, h2⟩

/-- A frame need not be a variable: a `List` pattern whose rest is an alias over a variable, and
a `Map` pattern whose rest is one, are within `colPatOK`. -/
example : colPatOK (.cb .list 0 [.el (.vr 0), .as (.vr 1) 2]) = true := by decide
example : colPatOK (.cb .map 0 [.kv (.vr 0) (.vr 1), .as (.vr 2) 3]) = true := by decide
/-- Two parts that are no elements are outside it for a `Map`, inside it for a `List`. -/
example : colPatOK (.cb .map 0 [.vr 0, .vr 1]) = false := by decide
example : colPatOK (.cb .list 0 [.vr 0, .vr 1]) = true := by decide

/-- Why a `Map` or `Set` pattern has at most one part that is no element: no substitution states
a match of two. -/
example {S : List (Int × Int)} {B : Bind} {c : Int} {es : List T} :
    ¬ DenColF S B .map c [.vr 0, .vr 1] es := by
  intro h
  cases h <;> simp_all [isElemT]

#print axioms patVal_denF
#print axioms patVals_densF
#print axioms matchF_col_complete

end KCore.KK.TestPatValDen
