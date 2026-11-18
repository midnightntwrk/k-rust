/-
  KCore, checked layer: the executable matcher is complete on well-sorted patterns (toward
  `Exec.step_iff`, Exec.lean).

  `MatchCtx`: three facts about a core's subsorts and constructors that matching reads: the
  subsort pairs are closed under composition and irreflexive, and no constructor is named like a
  map pattern symbol. They are decidable on the data (`matchReady`); `wf` gives them
  (`NamesApart.matchReady_of_wf`).

  - `patVal_sorted`: under a well-sorted σ, a well-sorted pattern denotes a value of its sort;
  - `matchP_complete_mf`: for a pattern without map symbols (function clauses), with enough fuel,
    the matcher finds, from any σ below a well-sorted τ under which the pattern denotes the value,
    a substitution below τ binding every variable of the pattern. The injection case is where
    sorts are needed: the value an injection pattern's argument denotes has the argument's sort,
    so it is not an injection into that sort (irreflexivity), and the matcher's one choice is it;
  - `matchP_sub_mf`: on such a pattern the matcher returns at most one substitution.
-/
import KcoreSpec.MatchSound
import KcoreSpec.SubjectReduction
import KcoreSpec.EvalLemmas

set_option autoImplicit false

namespace KCore.Exec

open KCore GroundTerm

/-- What matching reads of a core's sorts and constructors. -/
structure MatchCtx (c : Semantics) : Prop where
  trans : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts
  irrefl : ∀ a, (a, a) ∉ c.subsorts
  patHooks : ∀ f ∈ patternHooks, c.isCtor f = false
  /-- for now, no overloading symbol -/
  noOvl : c.ovls = []

/-- `MatchCtx`, decided. -/
def _root_.KCore.Semantics.matchReady (c : Semantics) : Bool :=
  (c.subsorts.all fun (a, b) => c.subsorts.all fun (b', d) => b != b' || c.subsorts.contains (a, d)) &&
  (c.subsorts.all fun (a, b) => a != b) &&
  (patternHooks.all fun f => !c.isCtor f) && c.ovls.isEmpty

theorem matchCtx_of {c : Semantics} (h : c.matchReady = true) : MatchCtx c := by
  simp only [Semantics.matchReady, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨htr, hir⟩, hph⟩, hno⟩ := h
  refine ⟨fun a b d hab hbd => ?_, fun a ha => ?_, fun f hf => ?_, List.isEmpty_iff.mp hno⟩
  · have := htr (a, b) hab (b, d) hbd
    simpa using this
  · have := hir (a, a) ha
    simp at this
  · have := hph f hf
    simpa using this

/-- The executable matcher's condition holds of a semantics without overloading symbols, which
subject reduction reads (`OvlCase`). -/
theorem ovlCase_of {c : Semantics} (h : c.matchReady = true) : c.OvlCase := .inl (matchCtx_of h).noOvl

/-- What matching reads of a core whose patterns may apply overloading symbols: `MatchCtx`'s
subsort and map-symbol facts, and well-formed overloads (`overloadsOK`) in place of none, which
the laws of `norm` (OvlLaws.lean) read. -/
structure MatchCtxO (c : Semantics) : Prop where
  trans : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts
  irrefl : ∀ a, (a, a) ∉ c.subsorts
  patHooks : ∀ f ∈ patternHooks, c.isCtor f = false
  ovlOK : c.overloadsOK = true

/-- `MatchCtxO`, decided: `matchReady` with `overloadsOK` in place of `ovls.isEmpty`. -/
def _root_.KCore.Semantics.matchReadyO (c : Semantics) : Bool :=
  (c.subsorts.all fun (a, b) => c.subsorts.all fun (b', d) => b != b' || c.subsorts.contains (a, d)) &&
  (c.subsorts.all fun (a, b) => a != b) &&
  (patternHooks.all fun f => !c.isCtor f) && c.overloadsOK

theorem matchCtxO_of {c : Semantics} (h : c.matchReadyO = true) : MatchCtxO c := by
  simp only [Semantics.matchReadyO, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨htr, hir⟩, hph⟩, hov⟩ := h
  refine ⟨fun a b d hab hbd => ?_, fun a ha => ?_, fun f hf => ?_, hov⟩
  · have := htr (a, b) hab (b, d) hbd
    simpa using this
  · have := hir (a, a) ha
    simp at this
  · have := hph f hf
    simpa using this

/-- Without overloading symbols, `MatchCtx` gives `MatchCtxO`. -/
theorem MatchCtx.o {c : Semantics} (h : MatchCtx c) : MatchCtxO c :=
  ⟨h.trans, h.irrefl, h.patHooks, by simp [Semantics.overloadsOK, Semantics.ovlPatsOK, Semantics.fnOvlSyms, h.noOvl]⟩

/-- A lemma over `MatchCtxO` applies where `MatchCtx` holds. -/
instance {c : Semantics} : Coe (MatchCtx c) (MatchCtxO c) := ⟨MatchCtx.o⟩

theorem MatchCtxO.ovlHyp {c : Semantics} (h : MatchCtxO c) : OvlLaws.OvlHyp c := ⟨h.ovlOK, h.trans, h.irrefl⟩

theorem MatchCtxO.ovlCase {c : Semantics} (h : MatchCtxO c) : c.OvlCase := .inr ⟨h.ovlOK, h.irrefl⟩

variable {c : Semantics}

/-! ## Binding a variable below τ -/

theorem bindVar_complete {σ τ : Subst} {i : Nat} {v : GroundTerm} (hx : Ext σ τ)
    (hi : τ.lookup i = some v) : ∃ σ', bindVar σ i v = some σ' ∧ Ext σ' τ ∧ Ext σ σ' ∧
      σ'.lookup i = some v := by
  unfold bindVar
  cases hl : σ.lookup i with
  | some w =>
    have := hx i w hl
    rw [hi] at this
    cases this
    refine ⟨σ, ?_, hx, Ext.refl _, hl⟩
    simp [same_iff.mpr rfl]
  | none =>
    refine ⟨(i, v) :: σ, rfl, fun j w hw => ?_, fun j w hw => ?_, by simp [List.lookup]⟩
    · simp only [List.lookup] at hw
      cases hj : (j == i) with
      | true =>
        rw [hj] at hw; cases hw
        rw [beq_iff_eq] at hj; subst hj; exact hi
      | false => rw [hj] at hw; exact hx j w hw
    · simp only [List.lookup]
      cases hj : (j == i) with
      | true => rw [beq_iff_eq] at hj; subst hj; rw [hl] at hw; cases hw
      | false => exact hw

/-! ## Sorts of what patterns denote -/

theorem patternHooks_lookup : ∀ f ∈ patternHooks,
    lookupSig (hookSigs.filter (patternHooks.contains ·.name)) f = lookupSig hookSigs f := by decide +kernel

theorem patCtx_hook_lookup (hc : MatchCtx c) {f : Sym} (hf : patternHooks.contains f = true)
    {k : CtorSig} (hk : lookupSig c.patCtx.heads f = some k) : lookupSig hookSigs f = some k := by
  have hfm : f ∈ patternHooks := List.contains_iff_mem.mp hf
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc.patHooks f hfm)
  simp only [Semantics.patCtx] at hk
  rw [lookupSig_append_of_none hnc, patternHooks_lookup f hfm] at hk
  exact hk

/-- No collection pattern symbol heads a pattern of the matcher's context: its heads are the
constructors and the map pattern symbols. -/
theorem collPat_not_patCtx {vars : List Srt} {f : Sym} {ps : List Term} {s : Srt}
    (ht : sortOfTerm c.patCtx vars (.app f ps) = some s) (hc : c.isCtor f = false)
    (hp : c.isCollPat f = true) : False := by
  obtain ⟨k, hk', -, -⟩ := sortOfTerm_app.mp ht
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  simp only [Semantics.patCtx] at hk'
  rw [lookupSig_append_of_none hnc, lookupSig_eq] at hk'
  obtain ⟨hmem, hname⟩ := List.find?_eq_some_iff_append.mp hk' |>.1 |> fun h => (⟨List.mem_of_find?_eq_some hk', h⟩ : _ ∧ _)
  have hf : patternHooks.contains f = true := by
    have := (List.mem_filter.mp hmem).2
    rw [beq_iff_eq.mp hname] at this; exact this
  rw [Semantics.isCollPat_of_hook c hf] at hp; cases hp

/-- No overloading symbol heads a pattern of the matcher's context. -/
theorem ovl_not_patCtx {vars : List Srt} {f : Sym} {ps : List Term} {s : Srt}
    (ht : sortOfTerm c.patCtx vars (.app f ps) = some s) (hc : c.isCtor f = false)
    (ho : c.isOvl f = true) : False := by
  obtain ⟨k, hk', -, -⟩ := sortOfTerm_app.mp ht
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  simp only [Semantics.patCtx] at hk'
  rw [lookupSig_append_of_none hnc, lookupSig_eq] at hk'
  have hmem := List.mem_of_find?_eq_some hk'
  have hname := List.find?_some hk'
  have hf : patternHooks.contains f = true := by
    have := (List.mem_filter.mp hmem).2
    rw [beq_iff_eq.mp hname] at this; exact this
  rw [c.isOvl_of_patternHook hf] at ho; cases ho

/-- A head of the matcher's context that is not a map pattern symbol is a constructor. -/
theorem ctor_of_patCtx {vars : List Srt} {f : Sym} {ps : List Term} {s : Srt}
    (ht : sortOfTerm c.patCtx vars (.app f ps) = some s) (hph : patternHooks.contains f = false) :
    c.isCtor f = true := by
  cases hc : c.isCtor f with
  | true => rfl
  | false =>
    obtain ⟨k, hk', -, -⟩ := sortOfTerm_app.mp ht
    have hnc : lookupSig c.ctorSigs f = none :=
      Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
    simp only [Semantics.patCtx] at hk'
    rw [lookupSig_append_of_none hnc, lookupSig_eq] at hk'
    have hmem := List.mem_of_find?_eq_some hk'
    have hname := List.find?_some hk'
    have := (List.mem_filter.mp hmem).2
    rw [beq_iff_eq.mp hname, hph] at this; cases this

mutual
  theorem patVal_sorted (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ {p : Term} {v : GroundTerm} {s : Srt},
      PatVal c τ p v → sortOfTerm c.patCtx vars p = some s → c.sortOf v = some s
    | _, _, s, .var h, ht => by
      obtain ⟨w, hw, hs⟩ := hτ _ s (sortOfTerm_var.mp ht)
      rw [h] at hw; cases hw; exact hs
    | _, _, s, .dv, ht => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      exact sortOf_dv.mpr ⟨hok, rfl⟩
    | _, _, s, .ctor (f := f) hk hs, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hk
      simp only [Semantics.patCtx] at hk'
      rw [lookupSig_append_of_some hk₀] at hk'
      cases hk'
      exact sortOf_ctor_intro ⟨k, hk₀, patVals_sorted hc hτ hs hargs, rfl⟩
    | _, _, s, .hook hp hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      exact hook_sorted (fun he => patternHooks_ne_rmKeys _ hp he |>.elim) (patCtx_hook_lookup hc hp hk')
        (patVals_sorted hc hτ hs hargs) hv
    | _, _, s, .coll hct hp _ _, ht => (collPat_not_patCtx ht hct hp).elim
    | _, _, s, .inj h, ht => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      exact sortOf_injNormal hc.trans hab (patVal_sorted hc hτ h ht')
    | _, _, s, .as h _, ht => patVal_sorted hc hτ h (sortOfTerm_as ht).2
    | _, _, s, .ovl hct ho _ _, ht => (ovl_not_patCtx ht hct ho).elim
  theorem patVals_sorted (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ {ps : List Term} {vs : List GroundTerm} {ss : List Srt},
      PatVals c τ ps vs → sortsOfTerms c.patCtx vars ps = some ss → c.sortsOf vs = some ss
    | _, _, _, .nil, ht => by rw [sortsOfTerms_nil.mp ht]; exact sortsOf_nil
    | _, _, _, .cons h hs, ht => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      exact sortsOf_cons.mpr ⟨s, ss', patVal_sorted hc hτ h h1, patVals_sorted hc hτ hs h2, rfl⟩
end

/-! ## Completeness on patterns without map symbols -/

/-- Every variable of the list is bound. -/
def Binds (σ : Subst) (is : List Nat) : Prop := ∀ i ∈ is, ∃ w, σ.lookup i = some w

theorem Binds.mono {σ σ' : Subst} {is : List Nat} (hx : Ext σ σ') (h : Binds σ is) : Binds σ' is :=
  fun i hi => by obtain ⟨w, hw⟩ := h i hi; exact ⟨w, hx i w hw⟩

theorem termSize_pos : ∀ (p : Term), 1 ≤ termSize p := by
  intro p; cases p <;> simp [termSize]

mutual
  theorem matchP_complete_mf (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {p : Term} {v : GroundTerm} {s : Srt},
      2 * termSize p ≤ n → mapFree p = true → PatVal c τ p v →
      sortOfTerm c.patCtx vars p = some s → Ext σ τ →
      ∃ σ' ∈ matchP c n σ p v, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccs p)
    | 0, _, p, _, _, hn, _, _, _, _ => by have := termSize_pos p; omega
    | n + 1, σ, .var i, v, _, _, _, hp, _, hx => by
      obtain ⟨σ', hb, hx', hx'', hl⟩ := bindVar_complete hx (PatVal.var_inv hp)
      refine ⟨σ', by simp [matchP, hb], hx', hx'', fun j hj => ?_⟩
      simp only [varOccs, List.mem_singleton] at hj
      exact ⟨v, hj ▸ hl⟩
    | n + 1, σ, .dv s l, v, _, _, _, hp, _, hx => by
      cases hp
      exact ⟨σ, by simp [matchP], hx, Ext.refl _, fun j hj => by simp [varOccs] at hj⟩
    | n + 1, σ, .app f ps, v, s, hn, hmf, hp, ht, hx => by
      simp only [mapFree, Bool.and_eq_true, Bool.not_eq_true'] at hmf
      cases hp with
      | hook hp' => rw [hmf.1] at hp'; cases hp'
      | coll hct hp' => exact (collPat_not_patCtx ht hct hp').elim
      | ovl hct ho => exact (ovl_not_patCtx ht hct ho).elim
      | ctor hk hs =>
        rename_i vs
        obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
        have hn' : 2 * termSizeList ps + 1 ≤ n := by simp [termSize] at hn; omega
        obtain ⟨σ', hm, hx', hx'', hb⟩ := matchL_complete_mf hc hτ n hn' hmf.2 hs hargs hx
        refine ⟨σ', ?_, hx', hx'', by simpa [varOccs] using hb⟩
        simp [matchP, hk, hm]
    | n + 1, σ, .inj a b p, v, s, hn, hmf, hp, ht, hx => by
      simp only [mapFree] at hmf
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      have hn' : 2 * termSize p ≤ n := by simp [termSize] at hn; omega
      cases hp with
      | inj hw =>
        rename_i w
        have hsw := patVal_sorted hc hτ hw ht'
        cases w with
        | inj a' y u =>
          obtain ⟨h1, h2, h3, rfl⟩ := sortOf_inj.mp hsw
          have hne : (a' == a) = false := by
            rw [beq_eq_false_iff_ne]; rintro rfl; exact hc.irrefl _ h1
          obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete_mf hc hτ n hn' hmf hw ht' hx
          refine ⟨σ', ?_, hx', hx'', by simpa [varOccs] using hb⟩
          simp [matchP, injNormal, hne, hm]
        | ctor f ts =>
          obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete_mf hc hτ n hn' hmf hw ht' hx
          exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | dv s l =>
          obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete_mf hc hτ n hn' hmf hw ht' hx
          exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | map _ es =>
          obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete_mf hc hτ n hn' hmf hw ht' hx
          exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | set _ es =>
          obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete_mf hc hτ n hn' hmf hw ht' hx
          exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | list _ es =>
          obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete_mf hc hτ n hn' hmf hw ht' hx
          exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
    | n + 1, σ, .as p i, v, s, hn, hmf, hp, ht, hx => by
      simp only [mapFree] at hmf
      obtain ⟨hp', hi⟩ := PatVal.as_inv hp
      have hn' : 2 * termSize p ≤ n := by simp [termSize] at hn; omega
      obtain ⟨σ1, hm, hx1, hx1', hb1⟩ :=
        matchP_complete_mf hc hτ n hn' hmf hp' (sortOfTerm_as ht).2 hx
      obtain ⟨σ', hbv, hx', hx'', hl⟩ := bindVar_complete hx1 hi
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
      · simp only [matchP, List.mem_filterMap]
        exact ⟨σ1, hm, hbv⟩
      · simp only [varOccs, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact Binds.mono hx'' hb1 j hj
        · exact ⟨v, hl⟩
  theorem matchL_complete_mf (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {ps : List Term} {vs : List GroundTerm}
      {ss : List Srt}, 2 * termSizeList ps + 1 ≤ n → mapFreeList ps = true → PatVals c τ ps vs →
      sortsOfTerms c.patCtx vars ps = some ss → Ext σ τ →
      ∃ σ' ∈ matchL c n σ ps vs, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccsList ps)
    | 0, _, _, _, _, hn, _, _, _, _ => by omega
    | n + 1, σ, [], vs, _, _, _, hp, _, hx => by
      rw [PatVals.nil_inv hp]
      exact ⟨σ, by simp [matchL], hx, Ext.refl _, fun j hj => by simp [varOccsList] at hj⟩
    | n + 1, σ, p :: ps, vs, ss, hn, hmf, hp, ht, hx => by
      simp only [mapFreeList, Bool.and_eq_true] at hmf
      obtain ⟨v, vs', rfl, hp1, hps⟩ := PatVals.cons_inv hp
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      have hsz := termSize_pos p
      have hn1 : 2 * termSize p ≤ n := by simp [termSizeList] at hn; omega
      have hn2 : 2 * termSizeList ps + 1 ≤ n := by simp [termSizeList] at hn; omega
      obtain ⟨σ1, hm1, hx1, hx1', hb1⟩ := matchP_complete_mf hc hτ n hn1 hmf.1 hp1 h1 hx
      obtain ⟨σ', hm2, hx', hx'', hb2⟩ := matchL_complete_mf hc hτ n hn2 hmf.2 hps h2 hx1
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
      · simp only [matchL, List.mem_flatMap]
        exact ⟨σ1, hm1, hm2⟩
      · simp only [varOccsList, List.mem_append] at hj
        rcases hj with hj | hj
        · exact Binds.mono hx'' hb1 j hj
        · exact hb2 j hj
end

/-! ## At most one match on patterns without map symbols -/

mutual
  theorem matchP_sub_mf : ∀ (n : Nat) {σ : Subst} {p : Term} {v : GroundTerm} {σ1 σ2 : Subst},
      mapFree p = true → σ1 ∈ matchP c n σ p v → σ2 ∈ matchP c n σ p v → σ1 = σ2
    | 0, _, _, _, _, _, _, h, _ => by simp [matchP] at h
    | n + 1, σ, .var i, v, σ1, σ2, _, h1, h2 => by
      simp only [matchP, Option.mem_toList] at h1 h2
      rw [h1] at h2; cases h2; rfl
    | n + 1, σ, .dv s l, v, σ1, σ2, _, h1, h2 => by
      cases v <;> simp only [matchP] at h1 h2 <;> (try split at h1) <;> simp_all
    | n + 1, σ, .app f ps, v, σ1, σ2, hmf, h1, h2 => by
      simp only [mapFree, Bool.and_eq_true, Bool.not_eq_true'] at hmf
      simp only [matchP, hmf.1] at h1 h2
      split at h1
      · cases v with
        | ctor g vs =>
          simp only at h1 h2
          split at h1
          · simp only [*, ↓reduceIte] at h2
            exact matchL_sub_mf n hmf.2 h1 h2
          · simp at h1
        | _ => simp at h1
      · simp at h1
    | n + 1, σ, .inj a b p, v, σ1, σ2, hmf, h1, h2 => by
      simp only [mapFree] at hmf
      cases v with
      | inj x b' u =>
        simp only [matchP] at h1 h2
        split at h1
        · simp only [*, ↓reduceIte] at h2
          split at h1
          · simp only [*, ↓reduceIte] at h2
            exact matchP_sub_mf n hmf h1 h2
          · simp only [*, ↓reduceIte] at h2
            exact matchP_sub_mf n hmf h1 h2
        · simp at h1
      | _ => simp [matchP] at h1
    | n + 1, σ, .as p i, v, σ1, σ2, hmf, h1, h2 => by
      simp only [mapFree] at hmf
      simp only [matchP, List.mem_filterMap] at h1 h2
      obtain ⟨τ1, hτ1, hb1⟩ := h1
      obtain ⟨τ2, hτ2, hb2⟩ := h2
      rw [matchP_sub_mf n hmf hτ1 hτ2, hb2] at hb1
      cases hb1; rfl
  theorem matchL_sub_mf : ∀ (n : Nat) {σ : Subst} {ps : List Term} {vs : List GroundTerm}
      {σ1 σ2 : Subst}, mapFreeList ps = true → σ1 ∈ matchL c n σ ps vs →
      σ2 ∈ matchL c n σ ps vs → σ1 = σ2
    | 0, _, _, _, _, _, _, h, _ => by simp [matchL] at h
    | n + 1, σ, [], [], σ1, σ2, _, h1, h2 => by
      simp only [matchL, List.mem_singleton] at h1 h2; rw [h1, h2]
    | n + 1, σ, p :: ps, v :: vs, σ1, σ2, hmf, h1, h2 => by
      simp only [mapFreeList, Bool.and_eq_true] at hmf
      simp only [matchL, List.mem_flatMap] at h1 h2
      obtain ⟨τ1, hτ1, h1⟩ := h1
      obtain ⟨τ2, hτ2, h2⟩ := h2
      rw [matchP_sub_mf n hmf.1 hτ1 hτ2] at h1
      exact matchL_sub_mf n hmf.2 h1 h2
    | n + 1, _, [], _ :: _, _, _, _, h, _ => by simp [matchL] at h
    | n + 1, _, _ :: _, [], _, _, _, h, _ => by simp [matchL] at h
end

end KCore.Exec
