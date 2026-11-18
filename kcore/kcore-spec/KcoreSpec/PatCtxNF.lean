/-
  KCore. The context of the patterns that apply no function-overloaded symbol.

  `overloadsOK` asks that no rule's left side, clause pattern or `exMatch` pattern applies a
  function-overloaded symbol (`ovlPatsOK`): an application of one denotes a function's value where
  a function overload covers its arguments, and a pattern denotes values. `patCtxNF` is `patCtxAll`
  without those symbols. A pattern is well sorted over it exactly when it is well sorted over
  `patCtxAll` and applies none of them (`sortOfTerm_nf_iff`), so a theorem about patterns that
  reads a pattern's sort over `patCtxNF` holds of the patterns of a definition `overloadsOK`
  accepts (`Semantics.lhs_nf`, `Semantics.pats_nf`, `Semantics.ruleCond_nf`, `Semantics.clauseCond_nf`) and
  reads that the head of an application is not function-overloaded off its signature
  (`patCtxNF_lookup`).
-/
import KcoreSpec.MatchComplete
import KcoreSpec.OvlLawsFn

set_option autoImplicit false

namespace KCore

/-- `patCtxAll` without the function-overloaded symbols: the context of a pattern that applies
none. -/
def Semantics.patCtxNF (c : Semantics) : TermCtx :=
  { c.patCtxAll with heads := c.patCtxAll.heads.filter fun k => !c.fnOvlSyms.contains k.name }

variable {c : Semantics}

/-- A lookup among the signatures whose names `q` keeps: the lookup of a name `q` keeps. -/
theorem lookupSig_filterKeepNF (q : Sym → Bool) (f : Sym) (l : List CtorSig) :
    lookupSig (l.filter fun k => q k.name) f = if q f = true then lookupSig l f else none := by
  rw [lookupSig_eq, lookupSig_eq]
  induction l with
  | nil => simp
  | cons k l ih =>
    by_cases hk : k.name = f
    · subst hk
      cases hq : q k.name <;> simp [List.filter, hq, ih]
    · have hne : (k.name == f) = false := by simpa using hk
      cases hq : q k.name <;> simp [List.filter, hq, ih, hne]

/-- `as` is well sorted where the context admits it, the variable has the sort and the term has. -/
theorem sortOfTerm_as_introNF {x : TermCtx} {vars : List Srt} {t : Term} {i : Nat} {s : Srt}
    (hx : x.asOK = true) (hi : vars[i]? = some s) (ht : sortOfTerm x vars t = some s) :
    sortOfTerm x vars (.as t i) = some s := by
  simp only [sortOfTerm]; rw [hx, hi, ht]; simp

theorem patCtxAll_asOK : c.patCtxAll.asOK = true := rfl

theorem patCtxNF_asOK : c.patCtxNF.asOK = true := rfl

/-- A signature of `patCtxNF` is `patCtxAll`'s, of a symbol that is not function-overloaded. -/
theorem patCtxNF_lookup {f : Sym} {k : CtorSig} :
    lookupSig c.patCtxNF.heads f = some k ↔ lookupSig c.patCtxAll.heads f = some k ∧ f ∉ c.fnOvlSyms := by
  rw [show lookupSig c.patCtxNF.heads f = _ from
    lookupSig_filterKeepNF (fun g => !c.fnOvlSyms.contains g) f c.patCtxAll.heads]
  cases hq : c.fnOvlSyms.contains f with
  | true => simp [List.contains_iff_mem.mp hq]
  | false =>
    have : f ∉ c.fnOvlSyms := fun hm => by rw [List.contains_iff_mem.mpr hm] at hq; cases hq
    simp [this]

mutual
  /-- A term well sorted over `patCtxNF` is well sorted over `patCtxAll` and applies no
  function-overloaded symbol. -/
  theorem sortOfTerm_of_nf {vars : List Srt} : ∀ (t : Term) {s : Srt},
      sortOfTerm c.patCtxNF vars t = some s → sortOfTerm c.patCtxAll vars t = some s ∧ c.NoFnOvlIn t
    | .var _, _, h => ⟨by simpa [sortOfTerm] using h, by simp [Semantics.NoFnOvlIn, symOccs]⟩
    | .dv _ _, _, h => ⟨(sortOfTerm_dv (x := c.patCtxAll)).mpr ((sortOfTerm_dv (x := c.patCtxNF)).mp h),
      by simp [Semantics.NoFnOvlIn, symOccs]⟩
    | .app f ts, _, h => by
      obtain ⟨k, hk, hargs, rfl⟩ := sortOfTerm_app.mp h
      obtain ⟨hk', hf⟩ := patCtxNF_lookup.mp hk
      obtain ⟨h1, h2⟩ := sortsOfTerms_of_nf ts hargs
      exact ⟨sortOfTerm_app.mpr ⟨k, hk', h1, rfl⟩, NoFnOvlIn.mk_app hf h2⟩
    | .inj a b t, _, h => by
      obtain ⟨hab, ht, rfl⟩ := sortOfTerm_inj.mp h
      obtain ⟨h1, h2⟩ := sortOfTerm_of_nf t ht
      refine ⟨sortOfTerm_inj.mpr ⟨hab, h1, rfl⟩, ?_⟩
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact h2
    | .as t i, s, h => by
      obtain ⟨hi, ht⟩ := Exec.sortOfTerm_as h
      obtain ⟨h1, h2⟩ := sortOfTerm_of_nf t ht
      refine ⟨sortOfTerm_as_introNF patCtxAll_asOK hi h1, ?_⟩
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact h2
  theorem sortsOfTerms_of_nf {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms c.patCtxNF vars ts = some ss → sortsOfTerms c.patCtxAll vars ts = some ss ∧ c.NoFnOvlInL ts
    | [], _, h => ⟨sortsOfTerms_nil.mpr (sortsOfTerms_nil.mp h), NoFnOvlIn.nil⟩
    | t :: ts, _, h => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
      obtain ⟨a1, a2⟩ := sortOfTerm_of_nf t h1
      obtain ⟨b1, b2⟩ := sortsOfTerms_of_nf ts h2
      exact ⟨sortsOfTerms_cons.mpr ⟨s, ss', a1, b1, rfl⟩, NoFnOvlIn.mk_cons a2 b2⟩
end

mutual
  /-- A term well sorted over `patCtxAll` that applies no function-overloaded symbol is well sorted
  over `patCtxNF`. -/
  theorem sortOfTerm_to_nf {vars : List Srt} : ∀ (t : Term) {s : Srt},
      sortOfTerm c.patCtxAll vars t = some s → c.NoFnOvlIn t → sortOfTerm c.patCtxNF vars t = some s
    | .var _, _, h, _ => by simpa [sortOfTerm] using h
    | .dv _ _, _, h, _ => (sortOfTerm_dv (x := c.patCtxNF)).mpr ((sortOfTerm_dv (x := c.patCtxAll)).mp h)
    | .app f ts, _, h, hn => by
      obtain ⟨k, hk, hargs, rfl⟩ := sortOfTerm_app.mp h
      exact sortOfTerm_app.mpr ⟨k, patCtxNF_lookup.mpr ⟨hk, (NoFnOvlIn.app hn).1⟩, sortsOfTerms_to_nf ts hargs (NoFnOvlIn.app hn).2, rfl⟩
    | .inj a b t, _, h, hn => by
      obtain ⟨hab, ht, rfl⟩ := sortOfTerm_inj.mp h
      exact sortOfTerm_inj.mpr ⟨hab, sortOfTerm_to_nf t ht (NoFnOvlIn.inj hn), rfl⟩
    | .as t i, s, h, hn => by
      obtain ⟨hi, ht⟩ := Exec.sortOfTerm_as h
      exact sortOfTerm_as_introNF patCtxNF_asOK hi (sortOfTerm_to_nf t ht (NoFnOvlIn.as hn))
  theorem sortsOfTerms_to_nf {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms c.patCtxAll vars ts = some ss → c.NoFnOvlInL ts → sortsOfTerms c.patCtxNF vars ts = some ss
    | [], _, h, _ => sortsOfTerms_nil.mpr (sortsOfTerms_nil.mp h)
    | t :: ts, _, h, hn => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
      exact sortsOfTerms_cons.mpr ⟨s, ss', sortOfTerm_to_nf t h1 (NoFnOvlIn.cons hn).1,
        sortsOfTerms_to_nf ts h2 (NoFnOvlIn.cons hn).2, rfl⟩
end

/-- A term is well sorted over `patCtxNF` exactly when it is over `patCtxAll` and applies no
function-overloaded symbol. -/
theorem sortOfTerm_nf_iff {vars : List Srt} {t : Term} {s : Srt} :
    sortOfTerm c.patCtxNF vars t = some s ↔ sortOfTerm c.patCtxAll vars t = some s ∧ c.NoFnOvlIn t :=
  ⟨sortOfTerm_of_nf t, fun h => sortOfTerm_to_nf t h.1 h.2⟩

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
a function (`OvlOK.noFn`). Read where the term is not at hand as a rule's left side or a clause's
pattern: the pattern of an `exMatch` in the Holds lemmas, and the rules and clauses of the
statements that take a sorted rule or clause that need not be the definition's. -/
theorem OvlOK.nf_bridge (h : OvlOK c) {vars : List Srt} {t : Term} {s : Srt}
    (ht : sortOfTerm c.patCtxAll vars t = some s) : sortOfTerm c.patCtxNF vars t = some s :=
  sortOfTerm_nf_of_nil h.noFn ht

theorem OvlOK.nfs_bridge (h : OvlOK c) {vars : List Srt} {ts : List Term} {ss : List Srt}
    (ht : sortsOfTerms c.patCtxAll vars ts = some ss) : sortsOfTerms c.patCtxNF vars ts = some ss :=
  sortsOfTerms_nf_of_nil h.noFn ht

end KCore
