/-
  `ruleSorted` sorts a rule's left side, and `clauseSorted` a clause's patterns, over `patCtxNF`,
  the context of the patterns that apply no function-overloaded symbol. Stated here against the
  texts they replace:

  - `ruleSorted_iff_all`: `ruleSorted r` holds exactly when `ruleSortedAll r` does (the same
    conjuncts with the left side sorted over `patCtxAll`) and the left side applies no
    function-overloaded symbol (`NoFnOvlIn`).
  - `lhs_noFnOvl_of_sortedOK`: so `sortedOK` gives, of every rule, the part of `ovlPatsOK` on its
    left side.
  - `ruleSorted_of_all_ovlPats`: and a rule of a semantics with `ovlPatsOK` has `ruleSorted` as soon
    as it has `ruleSortedAll`: on the rules of a semantics `overloadsOK` accepts the two texts agree.
  - `clauseSorted_iff_all`, `pats_noFnOvl_of_sortedOK`, `clauseSorted_of_all_ovlPats`: the same of
    `clauseSorted`, `clauseSortedAll` (the patterns sorted over `patCtxAll`) and `NoFnOvlInL` of the
    clause's patterns.

  Run from the package root: `lake env lean -j1 test/SortedNF.lean`.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.SortedNF

/-- `ruleSorted` with the left side sorted over `patCtxAll`. -/
def ruleSortedAll (c : Semantics) (r : Rule) : Bool :=
  sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort &&
  binds r.vars.length (varOccs r.lhs ++ r.condVars ++ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
    varOccsCond r.vars.length r.post) &&
  nodup r.exs && r.exs.all (fun i => r.opens.contains i && !r.condVars.contains i) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req && c.condOK r.vars r.pre &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens && c.condOK r.vars r.post &&
  Cond.bound c r.vars.length r.pre && Cond.bound c r.vars.length r.post &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort

theorem ruleSorted_iff_all (c : Semantics) (r : Rule) :
    c.ruleSorted r = true ↔ ruleSortedAll c r = true ∧ c.NoFnOvlIn r.lhs := by
  simp only [Semantics.ruleSorted, ruleSortedAll, Bool.and_eq_true, beq_iff_eq, sortOfTerm_nf_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hn⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, hn⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, hn⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hn⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩

theorem lhs_noFnOvl_of_sortedOK {c : Semantics} (h : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) :
    c.NoFnOvlIn r.lhs := by
  have hs := Semantics.sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  exact ((ruleSorted_iff_all c r).mp (hs.2 r hr)).2

theorem ruleSorted_of_all_ovlPats {c : Semantics} (hov : c.ovlPatsOK = true) {r : Rule} (hr : r ∈ c.rules)
    (h : ruleSortedAll c r = true) : c.ruleSorted r = true :=
  (ruleSorted_iff_all c r).mpr ⟨h, Semantics.ovlPats_lhs hov hr⟩

/-- `clauseSorted` with the patterns sorted over `patCtxAll`. -/
def clauseSortedAll (c : Semantics) (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats == some f.args &&
  binds cl.vars.length (varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
    (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtx rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.ens &&
  (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post) &&
  c.condOK cl.vars cl.pre

theorem sortsOfTerms_nf_iff' (c : Semantics) {vars : List Srt} {ts : List Term} {ss : List Srt} :
    sortsOfTerms c.patCtxNF vars ts = some ss ↔ sortsOfTerms c.patCtxAll vars ts = some ss ∧ c.NoFnOvlInL ts :=
  ⟨sortsOfTerms_of_nf ts, fun h => sortsOfTerms_to_nf ts h.1 h.2⟩

theorem clauseSorted_iff_all (c : Semantics) (f : Fn) (H : List CtorSig) (cl : Clause) :
    c.clauseSorted f H cl = true ↔ clauseSortedAll c f H cl = true ∧ c.NoFnOvlInL cl.pats := by
  simp only [Semantics.clauseSorted, clauseSortedAll, Bool.and_eq_true, beq_iff_eq, sortsOfTerms_nf_iff']
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, hn⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hn⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hn⟩
    exact ⟨⟨⟨⟨⟨⟨⟨h1, hn⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

theorem pats_noFnOvl_of_sortedOK {c : Semantics} (h : c.sortedOK = true) {f : Fn} (hf : f ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ f.clauses) : c.NoFnOvlInL cl.pats := by
  have hs := Semantics.sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  exact ((clauseSorted_iff_all c f _ cl).mp (hs.1.2 f hf cl hcl)).2

theorem clauseSorted_of_all_ovlPats {c : Semantics} (hov : c.ovlPatsOK = true) {f : Fn} (hf : f ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ f.clauses) {H : List CtorSig} (h : clauseSortedAll c f H cl = true) :
    c.clauseSorted f H cl = true :=
  (clauseSorted_iff_all c f H cl).mpr ⟨h, Semantics.ovlPats_pats hov hf hcl⟩

/-- info: 'KCore.SortedNF.ruleSorted_iff_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleSorted_iff_all
/-- info: 'KCore.SortedNF.lhs_noFnOvl_of_sortedOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lhs_noFnOvl_of_sortedOK
/-- info: 'KCore.SortedNF.ruleSorted_of_all_ovlPats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleSorted_of_all_ovlPats
/-- info: 'KCore.SortedNF.clauseSorted_iff_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clauseSorted_iff_all
/-- info: 'KCore.SortedNF.pats_noFnOvl_of_sortedOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pats_noFnOvl_of_sortedOK
/-- info: 'KCore.SortedNF.clauseSorted_of_all_ovlPats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clauseSorted_of_all_ovlPats

end KCore.SortedNF
