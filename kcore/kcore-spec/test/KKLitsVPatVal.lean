/-
  What a match of `d₀ d` binds has a `kore.k` form (`KcoreSpec/KKLitsVPatVal.lean`): under
  `execReady d` and `encodable d`, a substitution that gives a variable of a clause's patterns or of
  a rule's left side a value of its sort gives it a `litsV` value. The reason is the variable's sort,
  never `Float`. Run from the package root: `lake env lean test/KKLitsVPatVal.lean`.
-/
import KcoreSpec.KKLitsVPatVal

set_option autoImplicit false

namespace KCore.KK.TestLitsVPatVal

open KCore KCore.KK

#check @litsV_patVar_clause
#check @litsV_patVar_clause_ws
#check @litsV_patVar_rule
#check @litsV_patVar_rule_ws
#check @clause_patVar_sort_kpv
#check @rule_patVar_sort_kpv
#check @varOccs_sort_kpv
#check @varOccsList_sort_kpv
#check @patCtxAll_heads_kpv

/-- `Fails` states well-sortedness at `leftVars`, which holds the patterns' variables. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst}
    (hσ : (d₀ d).WellSortedAt cl.vars cl.leftVars σ) {i : Nat} (hi : i ∈ varOccsList cl.pats)
    {v : GroundTerm} (hv : σ.lookup i = some v) : litsV v = true :=
  litsV_patVar_clause hx he hfn hcl hσ hi (List.mem_append_left _ hi) hv

/-- A rule's match states well-sortedness at `leftVars`, which holds its left side's variables. -/
example {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true) {r : Rule}
    (hr : r ∈ (d₀ d).rules) {σ : Subst} (hσ : (d₀ d).WellSortedAt r.vars r.leftVars σ) {i : Nat}
    (hi : i ∈ varOccs r.lhs) {v : GroundTerm} (hv : σ.lookup i = some v) : litsV v = true :=
  litsV_patVar_rule hx he hr hσ hi (List.mem_append_left _ hi) hv

/-- The sort is what matters: a `Float` variable's value need not be `litsV`, and a `Float`-sorted
pattern variable is ruled out because no argument sort a left side's context reads is `Float`. -/
example : litsV (.dv Srt.float (.float 53 11 0)) = false := rfl

#print axioms litsV_patVar_clause
#print axioms litsV_patVar_clause_ws
#print axioms litsV_patVar_rule
#print axioms litsV_patVar_rule_ws

end KCore.KK.TestLitsVPatVal
