/-
  Two instances of kore.k's equations that decide at one argument list have results together at
  `HookParams.none` (`KK.coDefined : CoDefined c₀`).

  Two clauses that decide at one point are of one priority: the one of the smaller priority would
  apply where the other decides. Two of one priority are one clause, whose two matches agree on
  every variable (`clauseFixedL`, which every clause of kore.k passes), or a pair the coherence
  deciders accept or one of the nine pairs no argument list satisfies both of (`Apart`,
  User/Coherent.lean). A pair the deciders accept is apart or one instance (`pairOK_of_dec`): in
  each case of `pairAgreeL` and `instAgree` the clauses never both apply (patterns apart, `requires`
  exclusive, list patterns apart, a guard, a negated conjunction, literals apart), or their
  right-hand sides are one closed term (`clausesAgree`), or the second's right-hand side is the
  instance of the first's at the second's patterns, which has under the second match exactly the
  results the first has under the first (`substT_eval`). `Coherent` does not say which; the cases
  are read again here with that conclusion. The terms of the `requires` the exclusive cases
  compare have one result each, every function having at most one (`KK.fnDet`). No clause of
  kore.k has an `ensures`, so a clause instance's result is its right-hand side's.
-/
import User.FnSolves

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

/-! ## Apart or one instance -/

/-- Where both clauses apply at one argument list, each result of the first's right-hand side
under its match is one of the second's under its match. -/
def OneInst (c : Semantics) (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs → ∀ r,
    EvalTerm c σ cl.rhs r → EvalTerm c σ' cl'.rhs r

/-- The two clauses never both apply at one argument list, or they are one instance in both
orders. -/
def PairOK (c : Semantics) (cl cl' : Clause) : Prop :=
  Apart c cl cl' ∨ (OneInst c cl cl' ∧ OneInst c cl' cl)

theorem PairOK.symm {c : Semantics} {cl cl' : Clause} (h : PairOK c cl cl') : PairOK c cl' cl :=
  h.elim (fun h => .inl fun vs σ σ' ha ha' => h vs σ' σ ha' ha) (fun h => .inr ⟨h.2, h.1⟩)

namespace CoDef

/-- Where every function has at most one result, every term has one result. -/
theorem hdet_of_fnDet {c : Semantics} (hd : FnDet c) (σ : Subst) (t : Term) : HDet c σ t :=
  fun _ _ _ _ h h' => EvalTerm.functional_of_fnDet hd h h'

end CoDef

open CoDef

variable {c : Semantics}

/-- **A pair `pairAgreeL` accepts, of one priority, is apart or one instance**, where every
function has at most one result. -/
theorem pairOK_of_pairAgreeL (hmc : Exec.MatchCtxO c) (hd : FnDet c) {heads : List CtorSig} {f : Fn}
    {cl cl' : Clause} (hf : c.ovlFreeList cl.pats = true) (hf' : c.ovlFreeList cl'.pats = true)
    (hc1 : c.clauseSorted f heads cl = true) (hc2 : c.clauseSorted f heads cl' = true)
    (hx : cl.exs = []) (hx' : cl'.exs = [])
    (h : c.pairAgreeL heads cl cl' = true) (hprio : cl.prio = cl'.prio) : PairOK c cl cl' := by
  have hw1 : ∀ {σ : Subst}, c.WellSortedAt cl.vars cl.univ σ → c.WellSorted cl.vars σ :=
    (wellSortedAt_univ hx).mp
  have hw2 : ∀ {σ : Subst}, c.WellSortedAt cl'.vars cl'.univ σ → c.WellSorted cl'.vars σ :=
    (wellSortedAt_univ hx').mp
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1 hc2
  replace hc1 := hc1.1
  replace hc2 := hc2.1
  have hne : notCompeting cl cl' = false := by
    cases hn : notCompeting cl cl'
    · rfl
    · exact (notCompeting_iff.mp hn (.inl hprio)).elim
  simp only [Semantics.pairAgreeL, hne, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with (((((((⟨⟨hne', -⟩, -⟩ | ho) | ⟨hfx, hx1 | hx1⟩) | ha) | hl) | hg) | hg) | ⟨hfx, hn⟩)
  · exact (hne' hprio).elim
  · exact .inl fun vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ =>
      overlap_soundF hmc (hw1 hσ) (hw2 hσ') cl.pats hf hf' hc1.1.1.1.1.1 hc2.1.1.1.1.1 ho hm hm'
  · exact .inl fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ =>
      clausesExclusive_sound hmc hc1.1.1.1.1.1 hfx hc2.1.1.1.2 hx1 (hw1 hσ) hm hq (hw2 hσ') hm' hq'
        (.inl fun t _ => hdet_of_fnDet hd σ t)
  · simp only [Semantics.clausesExclusive, Bool.and_eq_true, beq_iff_eq] at hx1
    obtain ⟨⟨hv, hpb⟩, hx''⟩ := hx1
    have hpp := Term.beqList_sound hpb
    have hfx' : c.clauseFixed cl' = true := by
      unfold Semantics.clauseFixed at hfx ⊢; rw [hpp, hv]; exact hfx
    have hx2 : c.clausesExclusive heads cl' cl = true := by
      simp only [Semantics.clausesExclusive, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨hv, ?_⟩, hx''⟩
      have hpb' := hpb
      rw [← hpp] at hpb' ⊢
      exact hpb'
    exact .inl fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ =>
      clausesExclusive_sound hmc hc2.1.1.1.1.1 hfx' hc1.1.1.1.2 hx2 (hw2 hσ') hm' hq' (hw1 hσ) hm hq
        (.inl fun t _ => hdet_of_fnDet hd σ' t)
  · refine .inr ⟨fun vs σ σ' _ _ r h => ?_, fun vs σ σ' _ _ r h => ?_⟩
    · obtain ⟨⟨hr, -, hv, -⟩, -⟩ := clausesAgree_sound ha σ σ'
      rw [← hr]; exact Exec.EvalTerm.congr h hv
    · obtain ⟨-, ⟨hr, -, hv, -⟩⟩ := clausesAgree_sound ha σ' σ
      rw [← hr]; exact Exec.EvalTerm.congr h hv
  · exact .inl fun vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ =>
      clausesListApart_sound hmc hf hf' hc1.1.1.1.1.1 hc2.1.1.1.1.1 hl (hw1 hσ) (hw2 hσ') hm hm'
  · exact .inl fun vs σ σ' ⟨_, hm, _⟩ ⟨_, hm', hq', _⟩ => guardApart_sound hg hm hm' hq'
  · exact .inl fun vs σ σ' ⟨_, hm, hq, _⟩ ⟨_, hm', _⟩ => guardApart_sound hg hm' hm hq
  · exact .inl fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ =>
      negConjApart_sound hmc hc1.1.1.1.1.1 hfx hc2.1.1.1.2 hn (hw1 hσ) hm hq (hw2 hσ') hm' hq'
        (.inl fun t _ => hdet_of_fnDet hd σ t)

/-- **A pair `instAgree` accepts is apart or one instance**, where every function has at most one
result: the second's right-hand side is the instance of the first's, or the instance of the
first's `requires` excludes the second's. -/
theorem pairOK_of_instAgree (hmc : Exec.MatchCtxO c) (hd : FnDet c) {heads : List CtorSig} {cl cl' : Clause}
    {ss ss' : List Srt} (hpt : sortsOfTerms c.patCtxNF cl.vars cl.pats = some ss)
    (hpt' : sortsOfTerms c.patCtxNF cl'.vars cl'.pats = some ss')
    (hx : cl.exs = []) (hx' : cl'.exs = [])
    (h : c.instAgree heads cl cl' = true) : PairOK c cl cl' := by
  unfold Semantics.instAgree at h
  split at h
  · cases h
  rename_i θ hθi
  have inst : ∀ {vs σ σ'}, cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs → InstOK c σ σ' θ :=
    fun ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ =>
      instOfList_sound hmc ((wellSortedAt_univ hx).mp hσ) ((wellSortedAt_univ hx').mp hσ') cl.pats hθi hm hm'
        hpt hpt' (fun _ h => by cases h)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hb, he⟩, -⟩, -⟩ | h
  · have he := Term.beq_sound he
    refine .inr ⟨fun vs σ σ' ha ha' r h1 => ?_, fun vs σ' σ ha' ha r h2 => ?_⟩
    · rw [← he]; exact (substT_eval (inst ha ha') cl.rhs hb r).mp h1
    · rw [← he] at h2; exact (substT_eval (inst ha ha') cl.rhs hb r).mpr h2
  · split at h
    · rename_i q hq
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hb, hx⟩ := h
      refine .inl fun vs σ σ' ha ha' => ?_
      have hθ := inst ha ha'
      obtain ⟨_, _, hreq, _⟩ := ha
      obtain ⟨_, _, hreq', _⟩ := ha'
      have hqt : EvalTerm c σ' (substT θ q) (some (bool true)) :=
        (substT_eval hθ q hb _).mp (hreq q hq)
      have hF : HDet c σ' (substT θ q) := hdet_of_fnDet hd σ' _
      rcases hx with (hx | hx) | hx
      · exact reqsExclusive_sound hx (.inl fun t ht => by cases ht; exact hF)
          (fun t ht => by cases ht; exact hqt) hreq'
      · exact reqsExclusive_sound hx (.inr fun t ht => by cases ht; exact hF)
          hreq' (fun t ht => by cases ht; exact hqt)
      · exact litsApartI_sound hx (.inl fun l hl X hX => hF X (subterms_trans (mem_subterms_of_lits hl) hX))
          (fun l hl => lits_sound hqt hl) (fun l hl => lits_reqLits hreq' hl)
    · cases h

/-- **A pair the coherence deciders accept, of one priority, is apart or one instance.** -/
theorem pairOK_of_dec (hmc : Exec.MatchCtxO c) (hd : FnDet c) {heads : List CtorSig} {f : Fn}
    {cl cl' : Clause} (hf : c.ovlFreeList cl.pats = true) (hf' : c.ovlFreeList cl'.pats = true)
    (hc1 : c.clauseSorted f heads cl = true) (hc2 : c.clauseSorted f heads cl' = true)
    (hx : cl.exs = []) (hx' : cl'.exs = [])
    (h : (c.pairAgreeL heads cl cl' ||
      (cl.prio == cl'.prio && (c.instAgree heads cl cl' || c.instAgree heads cl' cl))) = true)
    (hprio : cl.prio = cl'.prio) : PairOK c cl cl' := by
  have hc1' := hc1; have hc2' := hc2
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1' hc2'
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hl | ⟨-, hi | hi⟩
  · exact pairOK_of_pairAgreeL hmc hd hf hf' hc1 hc2 hx hx' hl hprio
  · exact pairOK_of_instAgree hmc hd hc1'.1.1.1.1.1.1 hc2'.1.1.1.1.1.1 hx hx' hi
  · exact (pairOK_of_instAgree hmc hd hc2'.1.1.1.1.1.1 hc1'.1.1.1.1.1.1 hx' hx hi).symm

/-- **One clause that `clauseFixedL` accepts is one instance against itself**: its two matches
at one argument list agree on every variable. -/
theorem oneInst_self (hmc : Exec.MatchCtxO c) {cl : Clause} {ss : List Srt} {x : TermCtx} {s : Srt}
    (hpt : sortsOfTerms c.patCtxNF cl.vars cl.pats = some ss)
    (hrt : sortOfTerm x cl.vars cl.rhs = some s) (hfx : c.clauseFixedL cl = true) (hx : cl.exs = []) :
    OneInst c cl cl := by
  intro vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ r h
  unfold Semantics.clauseFixedL at hfx
  split at hfx
  · rename_i D hD
    simp only [List.all_eq_true, List.contains_iff_mem, List.mem_range] at hfx
    have hag : ∀ i, i < cl.vars.length → σ.lookup i = σ'.lookup i := fun i hi =>
      uniqArgs_sound hmc ((wellSortedAt_univ hx).mp hσ) ((wellSortedAt_univ hx).mp hσ') _ cl.pats hD
        (fun p hp => ⟨patVals_pairs hm hm' p hp, sortsOfTerms_each hpt p hp⟩) (fun _ h => by cases h) i (hfx i hi)
    exact Exec.EvalTerm.congr h fun i hi => hag i (Exec.sortOfTerm_vars hrt i hi)
  · cases hfx

/-! ## kore.k's pairs -/

namespace CoDef

/-- No clause of kore.k is `aside` or has an `ensures`. -/
theorem plain_clauses : (c₀.fns.all fun fn => fn.clauses.all fun cl => !cl.aside && cl.ens.isNone) = true := by
  decide +kernel

theorem aside_ens {fn : Fn} (hfn : fn ∈ c₀.fns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    cl.aside = false ∧ cl.ens = none := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp plain_clauses fn hfn) cl hcl
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  exact h

theorem nodup_labels : (c₀.allFns.map (·.label)).Nodup := by decide +kernel

theorem lookup_self {fn : Fn} (hfn : fn ∈ c₀.fns) : c₀.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label nodup_labels (List.mem_append_left _ hfn)

/-- Every clause of kore.k is fixed by its patterns (`match_named = []`). -/
theorem fixed_all {fn : Fn} (hfn : fn ∈ c₀.fns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    c₀.clauseFixedL cl = true := by
  cases hfx : c₀.clauseFixedL cl
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
    have h : (fn.label, i) ∈ c₀.matchObligationsL := by
      simp only [Semantics.matchObligationsL, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, Prod.mk.injEq]
      exact ⟨fn, hfn, i, ⟨hi, by simp [List.getElem?_eq_getElem hi, hfx]⟩, rfl, rfl⟩
    rw [Semantics.matchObligationsL_withHooks, match_named] at h
    cases h
  · rfl

/-- The functions the deciders confirm are all but `cmpI`, `join` and `matchCol`. -/
theorem excl_of_not_named {fn : Fn} (hfn : fn ∈ c₀.fns)
    (hn : fn.label ≠ 457 ∧ fn.label ≠ 479 ∧ fn.label ≠ 487) :
    c₀.fnExclusiveI (c₀.fns.map Fn.sig) fn = true := by
  cases hx : c₀.fnExclusiveI (c₀.fns.map Fn.sig) fn
  · have h : fn.label ∈ c₀.agreeObligationsI := by
      simp only [Semantics.agreeObligationsI, List.mem_map, List.mem_filter]
      exact ⟨fn, ⟨hfn, by simp [hovls, hx]⟩, rfl⟩
    rw [Semantics.agreeObligationsI_withHooks, agree_named] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact (hn.1 h).elim
    · exact (hn.2.1 h).elim
    · exact (hn.2.2 h).elim
  · rfl

/-- The coherence deciders accept the pair (`fnExclusiveI`'s test of one pair). -/
noncomputable abbrev Dec (p : Clause × Clause) : Bool :=
  c₀.pairAgreeL (c₀.fns.map Fn.sig) p.1 p.2 ||
    (p.1.prio == p.2.prio && (c₀.instAgree (c₀.fns.map Fn.sig) p.1 p.2 || c₀.instAgree (c₀.fns.map Fn.sig) p.2 p.1))

/-- The pairs of a function of kore.k that the deciders accept or no argument list satisfies
both of are apart or one instance. -/
theorem pairOK_of_parts {fn : Fn} (hfn : fn ∈ c₀.fns)
    (h : ∀ p ∈ pairs fn.clauses, Dec p = true ∨ Apart c₀ p.1 p.2) :
    ∀ p ∈ pairs fn.clauses, p.1.prio = p.2.prio → PairOK c₀ p.1 p.2 := by
  intro p hp hprio
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have hx := fnsNoExs₀ _ hfn
  rcases h p hp with hdc | ha
  · exact pairOK_of_dec hmc fnDet (hfr _ _ h1) (hfr _ _ h2) (hcls hfn _ h1) (hcls hfn _ h2)
      (hx _ h1) (hx _ h2) hdc hprio
  · exact .inl ha

theorem pairs_cmpI : ∀ p ∈ pairs fnCmpI.clauses, Dec p = true ∨ Apart c₀ p.1 p.2 := by
  intro p hp
  simp only [fnCmpI, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .inr apart_lt_eq
  · exact .inr apart_lt_gt
  · exact .inr apart_eq_gt

theorem pairs_join : ∀ p ∈ pairs fnJoin.clauses, Dec p = true ∨ Apart c₀ p.1 p.2 := by
  intro p hp
  simp only [fnJoin, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inr apart_col_list
  · exact .inr apart_col_elem
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inr apart_list_elem

theorem pairs_matchCol : ∀ p ∈ pairs fnMatchCol.clauses, Dec p = true ∨ Apart c₀ p.1 p.2 := by
  intro p hp
  simp only [fnMatchCol, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr apart_head_frame
  · exact .inr apart_head_choose
  · exact .inl (by decide +kernel)
  · exact .inr apart_head_split
  all_goals exact .inl (by decide +kernel)

/-- **Every two clauses of one priority of a function of kore.k are apart or one instance.** -/
theorem pairOK_all {fn : Fn} (hfn : fn ∈ c₀.fns) :
    ∀ p ∈ pairs fn.clauses, p.1.prio = p.2.prio → PairOK c₀ p.1 p.2 := by
  refine pairOK_of_parts hfn ?_
  by_cases hn : fn.label ≠ 457 ∧ fn.label ≠ 479 ∧ fn.label ≠ 487
  · exact fun p hp => .inl (List.all_eq_true.mp (excl_of_not_named hfn hn) p hp)
  · have hl := lookup_self hfn
    have h3 : fn.label = 457 ∨ fn.label = 479 ∨ fn.label = 487 := Classical.byContradiction fun hc =>
      hn ⟨fun h => hc (.inl h), fun h => hc (.inr (.inl h)), fun h => hc (.inr (.inr h))⟩
    rcases h3 with h | h | h <;> rw [h] at hl
    · rw [lookup_cmpI, Option.some.injEq] at hl; subst hl; exact pairs_cmpI
    · rw [lookup_join, Option.some.injEq] at hl; subst hl; exact pairs_join
    · rw [lookup_matchCol, Option.some.injEq] at hl; subst hl; exact pairs_matchCol

end CoDef

/-! ## `CoDefined` -/

/-- **Two instances of kore.k's equations that decide at one argument list have results together
at `HookParams.none`** (`CoDefined`): of two clause instances of one function that decide at one
point, if one has a value, the other has a result. -/
theorem coDefined : CoDefined c₀ := by
  intro fn hfn vs cl σ cl' σ' hcl hcl' hd hd' ⟨v, hv⟩
  have hx := fnsNoExs₀ _ hfn
  obtain ⟨ha1, he1⟩ := aside_ens hfn hcl
  obtain ⟨ha2, he2⟩ := aside_ens hfn hcl'
  have hprio : cl.prio = cl'.prio := by
    rcases Nat.lt_trichotomy cl.prio cl'.prio with h | h | h
    · exact (hd'.2 cl hcl ha1 h σ (((wellSortedAt_univ (hx cl hcl)).mp hd.1.1).at _) hd.1.2.1
        ⟨hd.1.2.2.1, hd.1.2.2.2⟩).elim
    · exact h
    · exact (hd.2 cl' hcl' ha2 h σ' (((wellSortedAt_univ (hx cl' hcl')).mp hd'.1.1).at _) hd'.1.2.1
        ⟨hd'.1.2.2.1, hd'.1.2.2.2⟩).elim
  have hrhs : EvalTerm c₀ σ cl.rhs (some v) := by
    rcases hv with ⟨-, h⟩ | ⟨t, -, ht, -⟩
    · exact h
    · rw [he1] at ht; cases ht
  suffices h : OneInst c₀ cl cl' from
    ⟨some v, .inl ⟨fun t ht => (by rw [he2] at ht; cases ht), h vs σ σ' hd.1 hd'.1 _ hrhs⟩⟩
  by_cases he : cl = cl'
  · subst he
    obtain ⟨-, -, L, -, -, hrt, -⟩ := Faithful.clause_ctxOccE hsorted (List.mem_append_left _ hfn) hcl
    have hpt : sortsOfTerms c₀.patCtxNF cl.vars cl.pats = some fn.args := by
      have hs := Semantics.sortedOK_sorted hsorted
      simp only [Bool.and_eq_true, List.all_eq_true] at hs
      have hcs := hs.1.2 fn hfn cl hcl
      simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hcs
      exact hcs.1.1.1.1.1.1
    exact oneInst_self hmc hpt hrt (fixed_all hfn hcl) (hx cl hcl)
  · rcases mem_pairs_of_ne hcl hcl' he with hp | hp
    · rcases pairOK_all hfn _ hp hprio with ha | ⟨h, -⟩
      · exact (ha vs σ σ' hd.1 hd'.1).elim
      · exact h
    · rcases pairOK_all hfn _ hp hprio.symm with ha | ⟨-, h⟩
      · exact (ha vs σ' σ hd'.1 hd.1).elim
      · exact h

end KK
