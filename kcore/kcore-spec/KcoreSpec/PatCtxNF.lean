/-
  KCore. The context of the patterns that apply no function-overloaded symbol.

  `overloadsOK` asks that no rule's left side, clause pattern or `exMatch` pattern applies a
  function-overloaded symbol (`ovlPatsOK`): an application of one denotes a function's value where
  a function overload covers its arguments, and a pattern denotes values. `patCtxNF` is `patCtxAll`
  without those symbols. A pattern is well sorted over it exactly when it is well sorted over
  `patCtxAll` and applies none of them (`sortOfTerm_nf_iff`), so a theorem about patterns that
  reads a pattern's sort over `patCtxNF` holds of the patterns of a definition `overloadsOK`
  accepts (`Semantics.lhs_nf`, `Semantics.pats_nf`) and
  reads that the head of an application is not function-overloaded off its signature
  (`patCtxNF_lookup`).
-/
import KcoreSpec.MatchComplete
import KcoreSpec.OvlLawsFn

set_option autoImplicit false

namespace KCore

variable {c : Semantics}

mutual
  /-- A term well sorted over a context none of whose symbols is function-overloaded applies no
  function-overloaded symbol. -/
  theorem noFnOvlIn_of_sorted {x : TermCtx} (hx : ∀ f k, lookupSig x.heads f = some k → f ∉ c.fnOvlSyms)
      {vars : List Srt} : ∀ (t : Term) {s : Srt}, sortOfTerm x vars t = some s → c.NoFnOvlIn t
    | .var _, _, _ => by simp [Semantics.NoFnOvlIn, symOccs]
    | .dv _ _, _, _ => by simp [Semantics.NoFnOvlIn, symOccs]
    | .app f ts, _, h => by
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp h
      exact NoFnOvlIn.mk_app (hx f k hk) (noFnOvlInL_of_sorted hx ts hargs)
    | .inj a b t, _, h => by
      obtain ⟨-, ht, -⟩ := sortOfTerm_inj.mp h
      have := noFnOvlIn_of_sorted hx t ht
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact this
    | .as t i, _, h => by
      have := noFnOvlIn_of_sorted hx t (Exec.sortOfTerm_as h).2
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact this
  theorem noFnOvlInL_of_sorted {x : TermCtx} (hx : ∀ f k, lookupSig x.heads f = some k → f ∉ c.fnOvlSyms)
      {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt}, sortsOfTerms x vars ts = some ss → c.NoFnOvlInL ts
    | [], _, _ => NoFnOvlIn.nil
    | t :: ts, _, h => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp h
      exact NoFnOvlIn.mk_cons (noFnOvlIn_of_sorted hx t h1) (noFnOvlInL_of_sorted hx ts h2)
end

/-- Without overloading symbols none is function-overloaded. -/
theorem Semantics.fnOvlSyms_of_noOvl (h : c.ovls = []) : c.fnOvlSyms = [] := by
  simp [Semantics.fnOvlSyms, h]

/-- Where no overloading symbol overloads a function the two contexts sort the same terms. -/
theorem sortOfTerm_nf_of_nil (h : c.fnOvlSyms = []) {vars : List Srt} {t : Term} {s : Srt}
    (ht : sortOfTerm c.patCtxAll vars t = some s) : sortOfTerm c.patCtxNF vars t = some s :=
  sortOfTerm_to_nf t ht (NoFnOvlIn.of_nil h t)

theorem sortsOfTerms_nf_of_nil (h : c.fnOvlSyms = []) {vars : List Srt} {ts : List Term} {ss : List Srt}
    (ht : sortsOfTerms c.patCtxAll vars ts = some ss) : sortsOfTerms c.patCtxNF vars ts = some ss :=
  sortsOfTerms_to_nf ts ht (NoFnOvlIn.ofL_nil h ts)

/-- The matcher's context (`patCtx`: the constructors and the map pattern symbols) holds no
function-overloaded symbol: such a symbol is an overloading symbol, which is neither. -/
theorem patCtx_not_fnOvl (H : OvlLaws.OvlFnFacts c) {f : Sym} {k : CtorSig}
    (hk : lookupSig c.patCtx.heads f = some k) : f ∉ c.fnOvlSyms := by
  intro hf
  unfold Semantics.fnOvlSyms at hf
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hf
  obtain ⟨hc, hh, -, -, -⟩ := c.isOvl_parts (H.isOvl o (List.mem_filter.mp ho).1)
  have hnc : lookupSig c.ctorSigs o.sig.name = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  have hnh := lookupSig_hookSigs_of_not_isHook hh
  simp only [Semantics.patCtx] at hk
  rw [lookupSig_append_of_none hnc, lookupSig_filterKeepNF (fun g => patternHooks.contains g)] at hk
  split at hk
  · rw [hnh] at hk; cases hk
  · cases hk

namespace Semantics

/-- **The patterns of every clause evaluation reads apply no function-overloaded symbol**: a
function's by `ovlPatsOK`, a sort predicate's because they are sorted over the matcher's context. -/
theorem pats_noFnOvl (H : OvlLaws.OvlHyp c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : c.NoFnOvlInL cl.pats := by
  rcases List.mem_append.mp hfn with hfn' | hfn'
  · exact ovlPats_pats (overloadsOK_pats H.ok) hfn' hcl
  · exact noFnOvlInL_of_sorted (fun _ _ => patCtx_not_fnOvl H.fnFacts) _ (sortPreds_ctx hfn' cl hcl).1

/-- The patterns of a clause evaluation reads are sorted over `patCtxNF` as they are over
`patCtxAll`, under any variable sorts. -/
theorem pats_nf (H : OvlLaws.OvlHyp c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) {vars : List Srt} {ss : List Srt}
    (h : sortsOfTerms c.patCtxAll vars cl.pats = some ss) : sortsOfTerms c.patCtxNF vars cl.pats = some ss :=
  sortsOfTerms_to_nf _ h (pats_noFnOvl H hfn hcl)

/-- A rule's left side is sorted over `patCtxNF` as it is over `patCtxAll` (`ovlPatsOK`). -/
theorem lhs_nf (hok : c.overloadsOK = true) {r : Rule} (hr : r ∈ c.rules) {vars : List Srt} {s : Srt}
    (h : sortOfTerm c.patCtxAll vars r.lhs = some s) : sortOfTerm c.patCtxNF vars r.lhs = some s :=
  sortOfTerm_to_nf _ h (ovlPats_lhs (overloadsOK_pats hok) hr)

end Semantics

/-- A term sorted over `patCtxAll` is sorted over `patCtxNF` where no overloading symbol overloads
a function (`OvlOK.noFn`). Read where the term is not at hand as a clause's pattern of the
definition: the pattern of an `exMatch` in the Holds lemmas, and the clauses of the statements that
take a sorted clause that need not be the definition's. A rule's left side is sorted over
`patCtxNF` by `ruleSorted` itself (`Semantics.ruleSorted_lhs_nf`). -/
theorem OvlOK.nf_bridge (h : OvlOK c) {vars : List Srt} {t : Term} {s : Srt}
    (ht : sortOfTerm c.patCtxAll vars t = some s) : sortOfTerm c.patCtxNF vars t = some s :=
  sortOfTerm_nf_of_nil h.noFn ht

theorem OvlOK.nfs_bridge (h : OvlOK c) {vars : List Srt} {ts : List Term} {ss : List Srt}
    (ht : sortsOfTerms c.patCtxAll vars ts = some ss) : sortsOfTerms c.patCtxNF vars ts = some ss :=
  sortsOfTerms_nf_of_nil h.noFn ht

end KCore
