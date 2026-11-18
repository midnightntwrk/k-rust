/-
  KCore, checked layer: what `uniq` (DefinitionWf.lean) means. Two well-sorted substitutions under
  which a pattern denotes one value, and that agree on D, agree on the variables `uniq c D p`
  lists (`uniq_sound`, `uniqList_sound`): constructors and injections are injective on values
  (`injNormal_inj`), and a map pattern `K |-> V M` with K's variables fixed has one decomposition,
  since a map's keys are unique (`union_single_unique`). The patterns are those well sorted in a
  left-hand side's context (`patCtxAll`), which denote values of their sorts (`patVal_sortedAll`).

  Moved from DetSound.lean (2026-11-09), where determinism reads it for a rule's left-hand side,
  so that the executable evaluation's completeness reads it for a function's clauses
  (`Semantics.clauseFixed`, EvalComplete.lean).
-/
import KcoreSpec.MatchMap
import KcoreSpec.HooksApart
import KcoreSpec.PatCtxNF

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec GroundTerm

variable {c : Semantics}

/-! ## Injections -/

theorem injNormal_shape (a b : Srt) (w : GroundTerm) : ∃ s u, injNormal a b w = .inj s b u := by
  cases w <;> exact ⟨_, _, rfl⟩

theorem injNormal_isInj (a b : Srt) (w : GroundTerm) : (injNormal a b w).isInj = true := by
  obtain ⟨s, u, h⟩ := injNormal_shape a b w
  rw [h]; rfl

/-- Injecting two values of sort a into b gives one value only if they are one value. -/
theorem injNormal_inj (hmc : MatchCtxO c) {a b : Srt} {w w' : GroundTerm}
    (hw : c.sortOf w = some a) (hw' : c.sortOf w' = some a) (h : injNormal a b w = injNormal a b w') :
    w = w' := by
  cases w with
  | inj a₁ b₁ u₁ =>
    obtain ⟨_, _, _, rfl⟩ := sortOf_inj.mp hw
    cases w' with
    | inj a₂ b₂ u₂ =>
      obtain ⟨_, _, _, rfl⟩ := sortOf_inj.mp hw'
      simp only [injNormal, GroundTerm.inj.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      rfl
    | _ =>
      simp only [injNormal, GroundTerm.inj.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      exact absurd (sortOf_inj.mp hw).1 (hmc.irrefl _)
  | _ =>
    cases w' with
    | inj a₂ b₂ u₂ =>
      obtain ⟨_, _, _, rfl⟩ := sortOf_inj.mp hw'
      simp only [injNormal, GroundTerm.inj.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      exact absurd (sortOf_inj.mp hw').1 (hmc.irrefl _)
    | _ =>
      simp only [injNormal, GroundTerm.inj.injEq, true_and] at h
      exact h

/-! ## Values a pattern denotes -/

theorem patternHooks_isHook {f : Sym} (h : patternHooks.contains f = true) : isHook f = true := by
  rcases patternHooks_cases h with rfl | rfl | rfl <;> rfl

/-- f is no overloading symbol, or one that overloads no symbol: its normal forms are its raw
applications (`norm_plain`). -/
def _root_.KCore.Semantics.ovlPlain (c : Semantics) (f : Sym) : Bool :=
  (c.lookupOvl f).all (·.over.isEmpty)

theorem norm_plain {f : Sym} (hf : c.ovlPlain f = true) (vs : List GroundTerm) : c.norm f vs = .ctor f vs := by
  unfold Semantics.norm Semantics.normN
  cases ho : c.lookupOvl f with
  | none => rfl
  | some o =>
    simp only [Semantics.ovlPlain, ho, Option.all_some, List.isEmpty_iff] at hf
    simp [Semantics.ovlOver, hf]

theorem ovlPlain_of_nil (hno : c.ovls = []) (f : Sym) : c.ovlPlain f = true := by
  simp [Semantics.ovlPlain, Semantics.lookupOvl, hno]

/-- A pattern `f(…)` whose head overloads no symbol denotes a constructor term, or (a map or
collection pattern symbol) a map, a list or a set. -/
theorem PatVal.app_shapeO {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : c.ovlPlain f = true) (h : PatVal c σ (.app f ps) v) :
    (∃ vs, v = .ctor f vs) ∨ (∃ s es, v = .map s es) ∨ (∃ s es, v = .list s es) ∨
      (∃ s es, v = .set s es) := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor _ _ => cases ht; exact .inl ⟨_, rfl⟩
  | hook hp _ hv => cases ht; obtain ⟨es, rfl⟩ := patternHook_map hp hv; exact .inr (.inl ⟨_, _, rfl⟩)
  | coll _ hp _ hv => cases ht; exact .inr (collVal_shape hp hv)
  | ovl _ _ _ hv => cases ht; rw [← hv, norm_plain hf]; exact .inl ⟨_, rfl⟩
  | _ => cases ht

theorem PatVal.app_shape (hno : c.ovls = []) {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (h : PatVal c σ (.app f ps) v) :
    (∃ vs, v = .ctor f vs) ∨ (∃ s es, v = .map s es) ∨ (∃ s es, v = .list s es) ∨
      (∃ s es, v = .set s es) :=
  PatVal.app_shapeO (ovlPlain_of_nil hno f) h

/-! ## Patterns that apply no overloading symbol -/

mutual
  /-- No application in the pattern is headed by an overloading symbol that overloads a symbol
  (`ovlPlain`), so the inversions of `PatVal` at an application (`PatVal.app_shapeO`) apply at
  each of them. -/
  def _root_.KCore.Semantics.ovlFree (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .app f ps => c.ovlPlain f && c.ovlFreeList ps
    | .inj _ _ p => c.ovlFree p
    | .as p _ => c.ovlFree p
    termination_by structural p => p
  def _root_.KCore.Semantics.ovlFreeList (c : Semantics) : List Term → Bool
    | [] => true
    | p :: ps => c.ovlFree p && c.ovlFreeList ps
    termination_by structural ps => ps
end

theorem ovlFree_app {f : Sym} {ps : List Term} (h : c.ovlFree (.app f ps) = true) :
    c.ovlPlain f = true ∧ c.ovlFreeList ps = true := by
  simpa only [Semantics.ovlFree, Bool.and_eq_true] using h

theorem ovlFreeList_cons {p : Term} {ps : List Term} (h : c.ovlFreeList (p :: ps) = true) :
    c.ovlFree p = true ∧ c.ovlFreeList ps = true := by
  simpa [Semantics.ovlFreeList] using h

theorem ovlFreeList_iff : ∀ {ps : List Term}, c.ovlFreeList ps = true ↔ ∀ p ∈ ps, c.ovlFree p = true
  | [] => by simp [Semantics.ovlFreeList]
  | p :: ps => by simp [Semantics.ovlFreeList, ovlFreeList_iff (ps := ps)]

mutual
  theorem ovlFree_of_nil (hno : c.ovls = []) : ∀ p : Term, c.ovlFree p = true
    | .var _ => rfl
    | .dv _ _ => rfl
    | .app f ps => by
      simp only [Semantics.ovlFree, ovlPlain_of_nil hno f, Bool.true_and]
      exact ovlFreeList_of_nil hno ps
    | .inj _ _ p => by simp only [Semantics.ovlFree]; exact ovlFree_of_nil hno p
    | .as p _ => by simp only [Semantics.ovlFree]; exact ovlFree_of_nil hno p
  theorem ovlFreeList_of_nil (hno : c.ovls = []) : ∀ ps : List Term, c.ovlFreeList ps = true
    | [] => rfl
    | p :: ps => by
      simp only [Semantics.ovlFreeList, Bool.and_eq_true]
      exact ⟨ovlFree_of_nil hno p, ovlFreeList_of_nil hno ps⟩
end

theorem PatVal.ctor_shape (hmc : MatchCtxO c) {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : c.isCtor f = true) (h : PatVal c σ (.app f ps) v) : ∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs := by
  have hph : patternHooks.contains f = false := by
    cases hc : patternHooks.contains f with
    | false => rfl
    | true => exact absurd hf (by rw [hmc.patHooks f (List.contains_iff_mem.mp hc)]; simp)
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hph h hf
  exact ⟨vs, rfl, hs⟩

theorem PatVal.inj_shape {σ : Subst} {a b : Srt} {p : Term} {v : GroundTerm}
    (h : PatVal c σ (.inj a b p) v) : v.isInj = true := by
  obtain ⟨w, -, rfl⟩ := PatVal.inj_inv h
  exact injNormal_isInj a b w

theorem PatVal.dv_shape {σ : Subst} {s : Srt} {l : Lit} {v : GroundTerm}
    (h : PatVal c σ (.dv s l) v) : v = .dv s l := by
  cases h; rfl

theorem injNormal_of_not_inj {a b : Srt} {w : GroundTerm} (h : w.isInj = false) :
    injNormal a b w = .inj a b w := by
  cases w <;> first | rfl | cases h

theorem PatVals.cons_inv' {σ : Subst} {p : Term} {ps : List Term} {vs : List GroundTerm}
    (h : PatVals c σ (p :: ps) vs) : ∃ v vs', vs = v :: vs' ∧ PatVal c σ p v ∧ PatVals c σ ps vs' := by
  cases h with
  | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

/-! ## One rule: its match fixes the right-hand side -/

theorem PatVal.hook_inv {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : c.isCtor f = false) (hph : patternHooks.contains f = true) (h : PatVal c σ (.app f ps) v) :
    ∃ vs, PatVals c σ ps vs ∧ hook f vs = some (some v) := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hc _ => cases ht; rw [hf] at hc; cases hc
  | hook _ hs hv => cases ht; exact ⟨_, hs, hv⟩
  | coll _ hp _ _ => cases ht; rw [Semantics.isCollPat_of_hook c hph] at hp; cases hp
  | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_patternHook hph] at ho; cases ho
  | _ => cases ht

theorem PatVal.coll_inv {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : c.isCtor f = false) (hp : c.isCollPat f = true) (h : PatVal c σ (.app f ps) v) :
    ∃ vs, PatVals c σ ps vs ∧ c.collVal f vs = some v := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hc _ => cases ht; rw [hf] at hc; cases hc
  | hook hph _ _ => cases ht; rw [Semantics.isCollPat_of_hook c hph] at hp; cases hp
  | coll _ _ hs hv => cases ht; exact ⟨_, hs, hv⟩
  | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_collPat hp] at ho; cases ho
  | _ => cases ht

/-- An overloading symbol's pattern denotes the normal form of its arguments' values. -/
theorem PatVal.ovl_inv {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (ho : c.isOvl f = true) (h : PatVal c σ (.app f ps) v) :
    ∃ vs, PatVals c σ ps vs ∧ c.norm f vs = v := by
  have hp := c.isOvl_parts ho
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hc _ => cases ht; rw [hp.1] at hc; cases hc
  | hook hph _ _ => cases ht; rw [c.isOvl_of_patternHook hph] at ho; cases ho
  | coll _ hcp _ _ => cases ht; rw [c.isOvl_of_collPat hcp] at ho; cases ho
  | ovl _ _ hs hv => cases ht; exact ⟨_, hs, hv⟩
  | _ => cases ht

mutual
  /-- The value a pattern denotes depends only on its variables' values. -/
  theorem PatVal.functional (hmc : MatchCtxO c) {σ σ' : Subst} : ∀ {p : Term} {v v' : GroundTerm},
      PatVal c σ p v → PatVal c σ' p v' → (∀ i ∈ varOccs p, σ.lookup i = σ'.lookup i) → v = v'
    | .var i, v, v', .var h, h', ha => by
      have := PatVal.var_inv h'
      rw [ha i (by simp [varOccs]), this] at h
      exact (Option.some.inj h).symm
    | .dv _ _, _, _, .dv, h', _ => (PatVal.dv_shape h').symm
    | .app f ps, _, v', .ctor hc hs, h', ha => by
      obtain ⟨vs', rfl, hs'⟩ := PatVal.ctor_shape hmc hc h'
      rw [PatVals.functional hmc hs hs' (fun i hi => ha i (by simpa [varOccs] using hi))]
    | .app f ps, v, v', .hook hp hs hv, h', ha => by
      have hf := hmc.patHooks f (List.contains_iff_mem.mp hp)
      obtain ⟨vs', hs', hv'⟩ := PatVal.hook_inv hf hp h'
      rw [PatVals.functional hmc hs hs' (fun i hi => ha i (by simpa [varOccs] using hi)), hv'] at hv
      exact (Option.some.inj (Option.some.inj hv)).symm
    | .app f ps, v, v', .coll hc hp hs hv, h', ha => by
      obtain ⟨vs', hs', hv'⟩ := PatVal.coll_inv hc hp h'
      rw [PatVals.functional hmc hs hs' (fun i hi => ha i (by simpa [varOccs] using hi)), hv'] at hv
      exact (Option.some.inj hv).symm
    | .inj a b p, _, v', .inj h, h', ha => by
      obtain ⟨w', hw', rfl⟩ := PatVal.inj_inv h'
      rw [PatVal.functional hmc h hw' (fun i hi => ha i (by simpa [varOccs] using hi))]
    | .as p i, v, v', .as h _, h', ha => by
      obtain ⟨h'', _⟩ := PatVal.as_inv h'
      exact PatVal.functional hmc h h'' (fun j hj => ha j (by simp [varOccs, hj]))
    | .app f ps, v, v', .ovl _ ho hs hv, h', ha => by
      obtain ⟨vs', hs', hv'⟩ := PatVal.ovl_inv ho h'
      rw [← hv, ← hv', PatVals.functional hmc hs hs' (fun i hi => ha i (by simpa [varOccs] using hi))]
  theorem PatVals.functional (hmc : MatchCtxO c) {σ σ' : Subst} : ∀ {ps : List Term} {vs vs' : List GroundTerm},
      PatVals c σ ps vs → PatVals c σ' ps vs' → (∀ i ∈ varOccsList ps, σ.lookup i = σ'.lookup i) → vs = vs'
    | [], _, _, .nil, h', _ => by cases h'; rfl
    | p :: ps, _, vs', .cons h hs, h', ha => by
      obtain ⟨v', vs'', rfl, h1, h2⟩ := PatVals.cons_inv' h'
      rw [PatVal.functional hmc h h1 (fun i hi => ha i (by simp [varOccsList, hi])),
        PatVals.functional hmc hs h2 (fun i hi => ha i (by simp [varOccsList, hi]))]
end

/-- `K |-> V M` and `K |-> V' M'` with one key denote one map only with V = V' and M = M'. -/
theorem union_single_unique {k v v' : GroundTerm} {b b' m : Entries}
    (h : union [(k, v)] b = some m) (h' : union [(k, v')] b' = some m)
    (hb : keysSorted b = true) (hb' : keysSorted b' = true) : v = v' ∧ b = b' := by
  obtain ⟨hm, -, -, hd⟩ := union_spec h
  obtain ⟨hm', -, -, hd'⟩ := union_spec h'
  have hk : ∀ e ∈ b, e.1 ≠ k := fun e he hek =>
    hd (k, v) (List.mem_singleton_self _) e he (by rw [hek]; exact cmp_refl k)
  have hk' : ∀ e ∈ b', e.1 ≠ k := fun e he hek =>
    hd' (k, v') (List.mem_singleton_self _) e he (by rw [hek]; exact cmp_refl k)
  have hv : v = v' := by
    rcases (hm' (k, v)).mp ((hm (k, v)).mpr (.inl (List.mem_singleton_self _))) with h1 | h1
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1; exact h1.2
    · exact absurd rfl (hk' _ h1)
  subst hv
  refine ⟨rfl, entries_canon hb hb' fun e => ⟨fun he => ?_, fun he => ?_⟩⟩
  · rcases (hm' e).mp ((hm e).mpr (.inr he)) with h1 | h1
    · simp only [List.mem_singleton] at h1; subst h1; exact absurd rfl (hk _ he)
    · exact h1
  · rcases (hm e).mp ((hm' e).mpr (.inr he)) with h1 | h1
    · simp only [List.mem_singleton] at h1; subst h1; exact absurd rfl (hk' _ he)
    · exact h1

/-! ## The sorts of the values of patterns over the collection pattern symbols

A left-hand side's context (`patCtxAll`) gives a signature to the matcher's heads (`patCtx`: the
constructors and the map pattern symbols) and to the collection pattern symbols. A collection
pattern symbol denotes its operation's value (`collVal`): an interpreted hook's, whose value has
the hook's result sort, or a parameter's, whose value has its declared result sort. So a pattern
well sorted in that context denotes values of its sort (`patVal_sortedAll`). -/

theorem lookupSig_filterName (q : Sym → Bool) (f : Sym) (l : List CtorSig) :
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

theorem find?_filter_keep {α : Type} {p q : α → Bool} : ∀ {l : List α} {x : α}, l.find? p = some x →
    q x = true → (l.filter q).find? p = some x
  | [], _, h, _ => by simp at h
  | a :: l, x, h, hq => by
    by_cases hp : p a = true
    · rw [List.find?_cons_of_pos hp] at h
      cases h
      rw [List.filter_cons_of_pos hq, List.find?_cons_of_pos hp]
    · rw [List.find?_cons_of_neg hp] at h
      by_cases hqa : q a = true
      · rw [List.filter_cons_of_pos hqa, List.find?_cons_of_neg hp]
        exact find?_filter_keep h hq
      · rw [List.filter_cons_of_neg hqa]
        exact find?_filter_keep h hq

/-- A map pattern symbol's signature in a left-hand side's context is its hook's (no constructor
being named like one). -/
theorem patCtxAll_hook_lookup' (hph : ∀ f ∈ patternHooks, c.isCtor f = false) {f : Sym}
    (hf : patternHooks.contains f = true)
    {k : CtorSig} (hk : lookupSig c.patCtxAll.heads f = some k) : lookupSig hookSigs f = some k := by
  have hfm : f ∈ patternHooks := List.contains_iff_mem.mp hf
  have hs : ∀ g ∈ patternHooks, (lookupSig hookSigs g).isSome = true := by decide
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp (hs f hfm)
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hph f hfm)
  have hp : lookupSig c.patCtx.heads f = some k' := by
    simp only [Semantics.patCtx]
    rw [lookupSig_append_of_none hnc, patternHooks_lookup f hfm]
    exact hk'
  have hall : lookupSig c.patCtxAll.heads f = some k' := by
    simp only [Semantics.patCtxAll]
    exact lookupSig_append_of_some hp
  rw [hall] at hk
  cases hk
  exact hk'

/-- A map pattern symbol's signature in a left-hand side's context is its hook's. -/
theorem patCtxAll_hook_lookup (hc : MatchCtxO c) {f : Sym} (hf : patternHooks.contains f = true)
    {k : CtorSig} (hk : lookupSig c.patCtxAll.heads f = some k) : lookupSig hookSigs f = some k :=
  patCtxAll_hook_lookup' hc.patHooks hf hk

/-- An overloading symbol's signature in a left-hand side's context is its declaration's. -/
theorem patCtxAll_ovl_lookup {f : Sym} (ho : c.isOvl f = true) {k : CtorSig}
    (hk : lookupSig c.patCtxAll.heads f = some k) : ∃ o, c.lookupOvl f = some o ∧ k = o.sig := by
  obtain ⟨hc, hh, hp, -, -⟩ := c.isOvl_parts ho
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  have hnh := lookupSig_hookSigs_of_not_isHook hh
  have hnf : ∀ q : Sym → Bool, lookupSig (hookSigs.filter (fun k => q k.name)) f = none := fun q => by
    rw [lookupSig_filterName]
    split
    · exact hnh
    · rfl
  have hnp : ∀ P : ParamSig → Bool, lookupSig ((c.params.filter P).map (·.sig)) f = none := fun P => by
    rw [lookupSig_eq, List.find?_eq_none]
    intro k hk hkn
    obtain ⟨kp, hkp, rfl⟩ := List.mem_map.mp hk
    have hpn := c.lookupSig_params_of_not hp
    rw [lookupSig_eq, List.find?_eq_none] at hpn
    exact hpn _ (List.mem_map_of_mem (List.mem_filter.mp hkp).1) hkn
  simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs] at hk
  rw [lookupSig_append_of_none ((lookupSig_append_of_none hnc).trans (hnf _)), List.append_assoc,
    lookupSig_append_of_none (hnf _), lookupSig_append_of_none (hnp _), lookupSig_eq, OvlLaws.find_ovlSigs] at hk
  obtain ⟨o, ho', rfl⟩ := Option.map_eq_some_iff.mp hk
  exact ⟨o, ho', rfl⟩

theorem patCtxAll_sig (hc : MatchCtxO c) {vars : List Srt} {f : Sym} {ps : List Term} {s : Srt}
    (hf : patternHooks.contains f = true) (ht : sortOfTerm c.patCtxAll vars (.app f ps) = some s) :
    ∃ k, lookupSig hookSigs f = some k ∧ sortsOfTerms c.patCtxAll vars ps = some k.args ∧ s = k.result := by
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  exact ⟨k, patCtxAll_hook_lookup hc hf hk', hargs, rfl⟩

/-- A collection pattern symbol's signature in a left-hand side's context: an interpreted hook's,
or a parameter's declaration. -/
theorem patCtxAll_collPat_lookup {f : Sym} {k : CtorSig} (hct : c.isCtor f = false)
    (hp : c.isCollPat f = true) (hk : lookupSig c.patCtxAll.heads f = some k) :
    (isHook f = true ∧ lookupSig hookSigs f = some k) ∨
      (isHook f = false ∧ ∃ kp, c.lookupParam f = some kp ∧ kp.sig = k) := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
  have hnph : patternHooks.contains f = false := by
    cases h : patternHooks.contains f
    · rfl
    · rw [Semantics.isCollPat_of_hook c h] at hp; cases hp
  have h0 : lookupSig c.patCtx.heads f = none := by
    simp only [Semantics.patCtx]
    rw [lookupSig_append_of_none hnc, lookupSig_filterName, hnph]
    rfl
  simp only [Semantics.patCtxAll, Semantics.collPatSigs] at hk
  rw [lookupSig_append_of_none h0] at hk
  have hp' := hp
  unfold Semantics.isCollPat at hp'
  rw [hnph] at hp'
  cases hh : isHook f with
  | true =>
    left
    refine ⟨rfl, ?_⟩
    rw [hh] at hp'
    have hcp : collPatternHooks.contains f = true := by simpa using hp'
    have hs : (lookupSig hookSigs f).isSome = true := by
      rw [lookupSig_eq, List.find?_isSome]
      obtain ⟨k', hk', he⟩ := List.any_eq_true.mp ((isHook_iff f).mp hh)
      exact ⟨k', hk', he⟩
    obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hs
    have h1 : lookupSig (hookSigs.filter fun k => collPatternHooks.contains k.name) f = some k' := by
      rw [lookupSig_filterName, if_pos hcp]; exact hk'
    rw [lookupSig_append_of_some (lookupSig_append_of_some h1)] at hk
    cases hk
    exact hk'
  | false =>
    right
    refine ⟨rfl, ?_⟩
    rw [hh] at hp'
    have h1 : lookupSig (hookSigs.filter fun k => collPatternHooks.contains k.name) f = none := by
      rw [lookupSig_filterName]
      split
      · rw [lookupSig_eq, List.find?_eq_none]
        intro k' hk' he
        have : hookSigs.any (·.name == f) = true := List.any_eq_true.mpr ⟨k', hk', he⟩
        rw [← isHook_iff, hh] at this
        cases this
      · rfl
    rw [List.append_assoc, lookupSig_append_of_none h1] at hk
    cases hl : c.lookupParam f with
    | none => rw [hl] at hp'; simp at hp'
    | some kp =>
      rw [hl] at hp'
      refine ⟨kp, rfl, ?_⟩
      have hfind : c.params.find? (·.sig.name == f) = some kp := (c.lookupParam_eq f).symm.trans hl
      have hq : (match kp.impl with
          | some g => patternHooks.contains g || collPatternHooks.contains g
          | none => false) = true := hp'
      rw [lookupSig_eq, List.find?_append, List.find?_map] at hk
      have hf2 := find?_filter_keep (q := fun k => match k.impl with
          | some g => patternHooks.contains g || collPatternHooks.contains g
          | none => false) hfind hq
      simp only [Function.comp_def] at hk
      erw [hf2] at hk
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at hk
      exact hk

/-! ### Signatures in the context without function-overloaded symbols -/

theorem patCtxNF_hook_lookup' (hph : ∀ f ∈ patternHooks, c.isCtor f = false) {f : Sym}
    (hf : patternHooks.contains f = true)
    {k : CtorSig} (hk : lookupSig c.patCtxNF.heads f = some k) : lookupSig hookSigs f = some k :=
  patCtxAll_hook_lookup' hph hf (patCtxNF_lookup.mp hk).1

theorem patCtxNF_hook_lookup (hc : MatchCtxO c) {f : Sym} (hf : patternHooks.contains f = true)
    {k : CtorSig} (hk : lookupSig c.patCtxNF.heads f = some k) : lookupSig hookSigs f = some k :=
  patCtxAll_hook_lookup hc hf (patCtxNF_lookup.mp hk).1

theorem patCtxNF_ovl_lookup {f : Sym} (ho : c.isOvl f = true) {k : CtorSig}
    (hk : lookupSig c.patCtxNF.heads f = some k) : ∃ o, c.lookupOvl f = some o ∧ k = o.sig :=
  patCtxAll_ovl_lookup ho (patCtxNF_lookup.mp hk).1

theorem patCtxNF_sig (hc : MatchCtxO c) {vars : List Srt} {f : Sym} {ps : List Term} {s : Srt}
    (hf : patternHooks.contains f = true) (ht : sortOfTerm c.patCtxNF vars (.app f ps) = some s) :
    ∃ k, lookupSig hookSigs f = some k ∧ sortsOfTerms c.patCtxNF vars ps = some k.args ∧ s = k.result := by
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  exact ⟨k, patCtxNF_hook_lookup hc hf hk', hargs, rfl⟩

theorem patCtxNF_collPat_lookup {f : Sym} {k : CtorSig} (hct : c.isCtor f = false)
    (hp : c.isCollPat f = true) (hk : lookupSig c.patCtxNF.heads f = some k) :
    (isHook f = true ∧ lookupSig hookSigs f = some k) ∨
      (isHook f = false ∧ ∃ kp, c.lookupParam f = some kp ∧ kp.sig = k) :=
  patCtxAll_collPat_lookup hct hp (patCtxNF_lookup.mp hk).1

/-- An overloading symbol that overloads no symbol is not function-overloaded. -/
theorem not_fnOvl_of_plain (hmc : MatchCtxO c) {f : Sym} (hf : c.ovlPlain f = true) : f ∉ c.fnOvlSyms := by
  intro hm
  unfold Semantics.fnOvlSyms at hm
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hom, hany⟩ := List.mem_filter.mp ho
  have hlo := OvlLaws.lookupOvl_of_mem hmc.ovlHyp hom
  simp only [Semantics.ovlPlain, hlo, Option.all_some, List.isEmpty_iff] at hf
  rw [hf] at hany
  simp at hany

mutual
  /-- A pattern none of whose applications is headed by an overloading symbol that overloads a
  symbol applies no function-overloaded symbol. -/
  theorem noFnOvlIn_of_ovlFree (hmc : MatchCtxO c) : ∀ (p : Term), c.ovlFree p = true → c.NoFnOvlIn p
    | .var _, _ => by simp [Semantics.NoFnOvlIn, symOccs]
    | .dv _ _, _ => by simp [Semantics.NoFnOvlIn, symOccs]
    | .app f ps, h =>
      NoFnOvlIn.mk_app (not_fnOvl_of_plain hmc (ovlFree_app h).1) (noFnOvlInL_of_ovlFree hmc ps (ovlFree_app h).2)
    | .inj _ _ p, h => by
      have := noFnOvlIn_of_ovlFree hmc p (by simpa only [Semantics.ovlFree] using h)
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact this
    | .as p _, h => by
      have := noFnOvlIn_of_ovlFree hmc p (by simpa only [Semantics.ovlFree] using h)
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact this
  theorem noFnOvlInL_of_ovlFree (hmc : MatchCtxO c) : ∀ (ps : List Term), c.ovlFreeList ps = true → c.NoFnOvlInL ps
    | [], _ => NoFnOvlIn.nil
    | p :: ps, h => NoFnOvlIn.mk_cons (noFnOvlIn_of_ovlFree hmc p (ovlFreeList_cons h).1)
        (noFnOvlInL_of_ovlFree hmc ps (ovlFreeList_cons h).2)
end

mutual
  /-- A pattern well sorted in a left-hand side's context denotes values of its sort. -/
  theorem patVal_sortedAllO (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ {p : Term} {v : GroundTerm} {s : Srt},
      PatVal c τ p v → sortOfTerm c.patCtxNF vars p = some s → c.sortOf v = some s
    | _, _, s, .var h, ht => by
      obtain ⟨w, hw, hs⟩ := hτ _ s (sortOfTerm_var.mp ht)
      rw [h] at hw; cases hw; exact hs
    | _, _, s, .dv, ht => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      exact sortOf_dv.mpr ⟨hok, rfl⟩
    | _, _, s, .ctor (f := f) hk hs, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hk
      have h0 : lookupSig c.patCtxAll.heads f = some k₀ := by
        simp only [Semantics.patCtxAll, Semantics.patCtx]
        exact lookupSig_append_of_some (lookupSig_append_of_some hk₀)
      have hkk : k = k₀ := Option.some.inj ((patCtxNF_lookup.mp hk').1.symm.trans h0)
      subst hkk
      exact sortOf_ctor_intro ⟨k, hk₀, patVals_sortedAllO hc hτ hs hargs, rfl⟩
    | _, _, s, .hook hp hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      exact hook_sorted (fun he => patternHooks_ne_rmKeys _ hp he |>.elim) (patCtxNF_hook_lookup' hc.patHooks hp hk')
        (patVals_sortedAllO hc hτ hs hargs) hv
    | _, _, s, .coll hct hp hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      unfold Semantics.collVal at hv
      rcases patCtxNF_collPat_lookup hct hp hk' with ⟨hh, hl⟩ | ⟨hh, kp, hkp, rfl⟩
      · rw [if_pos hh] at hv
        exact hook_sorted (fun he => isCollPat_hook_ne_rmKeys hp hh he |>.elim) hl (patVals_sortedAllO hc hτ hs hargs)
          (Option.join_eq_some_iff.mp hv)
      · rw [if_neg (by rw [hh]; decide)] at hv
        obtain ⟨k', hk'', hsv⟩ := c.paramVal_sorted hv
        rw [hkp] at hk''
        cases hk''
        exact hsv
    | _, _, s, .inj h, ht => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      exact sortOf_injNormal hc.trans hab (patVal_sortedAllO hc hτ h ht')
    | _, _, s, .as h _, ht => patVal_sortedAllO hc hτ h (sortOfTerm_as ht).2
    | _, _, s, .ovl (f := f) _ ho hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := patCtxNF_ovl_lookup ho hk'
      rw [← hv]
      exact OvlLaws.sortOf_norm_ovlF hc.ovlHyp hc.ovlHyp.fnFacts hlo (patVals_sortedAllO hc hτ hs hargs)
        (OvlLaws.fnCover_none_of_not_fnOvl (patCtxNF_lookup.mp hk').2 _)
  theorem patVals_sortedAllO (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ {ps : List Term} {vs : List GroundTerm} {ss : List Srt},
      PatVals c τ ps vs → sortsOfTerms c.patCtxNF vars ps = some ss → c.sortsOf vs = some ss
    | _, _, _, .nil, ht => by rw [sortsOfTerms_nil.mp ht]; exact sortsOf_nil
    | _, _, _, .cons h hs, ht => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      exact sortsOf_cons.mpr ⟨s, ss', patVal_sortedAllO hc hτ h h1, patVals_sortedAllO hc hτ hs h2, rfl⟩
end

/-- A pattern well sorted in a left-hand side's context denotes values of its sort
(`patVal_sortedAllO`). -/
theorem patVal_sortedAll (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
    (hτ : c.WellSorted vars τ) {p : Term} {v : GroundTerm} {s : Srt}
    (h : PatVal c τ p v) (ht : sortOfTerm c.patCtxNF vars p = some s) : c.sortOf v = some s :=
  patVal_sortedAllO hc hτ h ht

theorem patVals_sortedAll (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
    (hτ : c.WellSorted vars τ) {ps : List Term} {vs : List GroundTerm} {ss : List Srt}
    (h : PatVals c τ ps vs) (ht : sortsOfTerms c.patCtxNF vars ps = some ss) : c.sortsOf vs = some ss :=
  patVals_sortedAllO hc hτ h ht

theorem sortsOfTerms_two {x : TermCtx} {vars : List Srt} {p q : Term} {a b : Srt}
    (h : sortsOfTerms x vars [p, q] = some [a, b]) :
    sortOfTerm x vars p = some a ∧ sortOfTerm x vars q = some b := by
  obtain ⟨s₁, ss₁, h1, h2, he⟩ := sortsOfTerms_cons.mp h
  obtain ⟨s₂, ss₂, h3, h4, he'⟩ := sortsOfTerms_cons.mp h2
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [List.cons.injEq] at he'
  obtain ⟨rfl, -⟩ := he'
  exact ⟨h1, h3⟩

theorem uniqConcat_inv {D D' : List Nat} {ps : List Term} (h : uniqConcat c D ps = some D') :
    ∃ e k vp rest, ps = [.app e [k, vp], rest] ∧ uniqConcat c D [.app e [k, vp], rest] = some D' := by
  unfold uniqConcat at h
  split at h
  · rename_i e k vp rest
    refine ⟨e, k, vp, rest, rfl, ?_⟩
    unfold uniqConcat
    exact h
  · cases h

mutual
  theorem uniq_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (p : Term) {D D' : List Nat} {v : GroundTerm} {s : Srt}, uniq c D p = some D' →
        PatVal c σ p v → PatVal c σ' p v → sortOfTerm c.patCtxNF vars p = some s →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | .var j, D, D', v, s, hu, h, h', _, hD => by
      simp only [uniq, Option.some.injEq] at hu
      subst hu
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [PatVal.var_inv h, PatVal.var_inv h']
      · exact hD i hi
    | .dv _ _, D, D', v, s, hu, _, _, _, hD => by
      simp only [uniq, Option.some.injEq] at hu
      subst hu; exact hD
    | .inj a b p, D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniq] at hu
      obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv h
      obtain ⟨w', hw', he⟩ := PatVal.inj_inv h'
      obtain ⟨-, hps, -⟩ := sortOfTerm_inj.mp hs
      have := injNormal_inj hmc (patVal_sortedAll hmc hσ hw hps) (patVal_sortedAll hmc hσ' hw' hps) he
      subst this
      exact uniq_sound hmc hσ hσ' p hu hw hw' hps hD
    | .as p j, D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniq, Option.map_eq_some_iff] at hu
      obtain ⟨D'', hu, rfl⟩ := hu
      obtain ⟨hp, hj⟩ := PatVal.as_inv h
      obtain ⟨hp', hj'⟩ := PatVal.as_inv h'
      have ih := uniq_sound hmc hσ hσ' p hu hp hp' (sortOfTerm_as hs).2 hD
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hj, hj']
      · exact ih i hi
    | .app f ps, D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniq] at hu
      split at hu
      · rename_i hf
        obtain ⟨vs, rfl, hvs⟩ := PatVal.ctor_shape hmc hf h
        obtain ⟨vs', he, hvs'⟩ := PatVal.ctor_shape hmc hf h'
        cases he
        obtain ⟨k, -, hk, -⟩ := sortOfTerm_app.mp hs
        exact uniqList_sound hmc hσ hσ' ps hu hvs hvs' hk hD
      · split at hu
        · split at hu
          · simp only [Option.some.injEq] at hu; subst hu; exact hD
          · cases hu
        · split at hu
          · rename_i hcat
            have hcat := beq_iff_eq.mp hcat
            subst hcat
            exact uniqConcat_sound hmc hσ hσ' ps hu h h' hs hD
          · cases hu
  theorem uniqList_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (ps : List Term) {D D' : List Nat} {vs : List GroundTerm} {ss : List Srt},
        uniqList c D ps = some D' → PatVals c σ ps vs → PatVals c σ' ps vs →
        sortsOfTerms c.patCtxNF vars ps = some ss →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | [], D, D', vs, ss, hu, _, _, _, hD => by
      simp only [uniqList, Option.some.injEq] at hu
      subst hu; exact hD
    | p :: ps, D, D', vs, ss, hu, h, h', hs, hD => by
      simp only [uniqList, Option.bind_eq_some_iff] at hu
      obtain ⟨D'', hu₁, hu₂⟩ := hu
      obtain ⟨v, vs₁, rfl, h1, h2⟩ := PatVals.cons_inv' h
      obtain ⟨v', vs₁', he, h1', h2'⟩ := PatVals.cons_inv' h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨s₁, ss₁, hs₁, hs₂, -⟩ := sortsOfTerms_cons.mp hs
      exact uniqList_sound hmc hσ hσ' ps hu₂ h2 h2' hs₂ (uniq_sound hmc hσ hσ' p hu₁ h1 h1' hs₁ hD)
  theorem uniqConcat_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (ps : List Term) {D D' : List Nat} {v : GroundTerm} {s : Srt}, uniqConcat c D ps = some D' →
        PatVal c σ (.app mapConcat ps) v → PatVal c σ' (.app mapConcat ps) v →
        sortOfTerm c.patCtxNF vars (.app mapConcat ps) = some s →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | [.app e [k, vp], rest], D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniqConcat] at hu
      split at hu
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hc
        obtain ⟨rfl, hk⟩ := hc
        simp only [Option.bind_eq_some_iff] at hu
        obtain ⟨D'', hu₁, hu₂⟩ := hu
        have hcat : c.isCtor mapConcat = false := hmc.patHooks _ (by decide)
        have hel : c.isCtor mapElem = false := hmc.patHooks _ (by decide)
        obtain ⟨ms, hms, hv⟩ := PatVal.hook_inv hcat rfl h
        obtain ⟨ms', hms', hv'⟩ := PatVal.hook_inv hcat rfl h'
        obtain ⟨_, _, a, b, m, rfl, hab, rfl⟩ := hook_concat_inv hv
        obtain ⟨_, _, a', b', m', rfl, hab', hm'⟩ := hook_concat_inv hv'
        cases hm'
        obtain ⟨_, _, he1, hE, hRa⟩ := PatVals.cons_inv' hms
        obtain ⟨_, _, he2, hRb, -⟩ := PatVals.cons_inv' hRa
        cases he1; cases he2
        obtain ⟨_, _, he3, hE', hRc⟩ := PatVals.cons_inv' hms'
        obtain ⟨_, _, he4, hRd, -⟩ := PatVals.cons_inv' hRc
        cases he3; cases he4
        obtain ⟨kv, hkv, hkvv⟩ := PatVal.hook_inv hel rfl hE
        obtain ⟨kv', hkv', hkvv'⟩ := PatVal.hook_inv hel rfl hE'
        obtain ⟨wk, wv, rfl, hav⟩ := hook_elem_inv hkvv
        obtain ⟨wk', wv', rfl, hav'⟩ := hook_elem_inv hkvv'
        simp only [GroundTerm.map.injEq] at hav hav'
        obtain ⟨rfl, rfl⟩ := hav
        obtain ⟨rfl, rfl⟩ := hav'
        obtain ⟨_, _, he5, hK, hVa⟩ := PatVals.cons_inv' hkv
        obtain ⟨_, _, he6, hV, -⟩ := PatVals.cons_inv' hVa
        cases he5; cases he6
        obtain ⟨_, _, he7, hK', hVb⟩ := PatVals.cons_inv' hkv'
        obtain ⟨_, _, he8, hV', -⟩ := PatVals.cons_inv' hVb
        cases he7; cases he8
        have hkk := PatVal.functional hmc hK hK' (fun i hi => hD i (hk i hi))
        subst hkk
        obtain ⟨kc, hkc, hargs, -⟩ := patCtxNF_sig hmc (by decide) hs
        rw [sig_concat] at hkc
        cases hkc
        obtain ⟨hsE, hsR⟩ := sortsOfTerms_two hargs
        obtain ⟨ke, hke, hargsE, -⟩ := patCtxNF_sig hmc (by decide) hsE
        rw [sig_elem] at hke
        cases hke
        obtain ⟨-, hsV⟩ := sortsOfTerms_two hargsE
        have hsb := patVal_sortedAll hmc hσ hRb hsR
        have hsb' := patVal_sortedAll hmc hσ' hRd hsR
        obtain rfl := sortOf_map hsb
        obtain rfl := sortOf_map hsb'
        have hb := (sortOf_Map.mp hsb).1
        have hb' := (sortOf_Map.mp hsb').1
        obtain ⟨rfl, rfl⟩ := union_single_unique hab hab' hb hb'
        exact uniq_sound hmc hσ hσ' rest hu₂ hRb hRd hsR (uniq_sound hmc hσ hσ' vp hu₁ hV hV' hsV hD)
      · cases hu
    | [], _, _, _, _, hu, _, _, _, _ | [_], _, _, _, _, hu, _, _, _, _
    | _ :: _ :: _ :: _, _, _, _, _, hu, _, _, _, _
    | [.var _, _], _, _, _, _, hu, _, _, _, _ | [.dv _ _, _], _, _, _, _, hu, _, _, _, _
    | [.inj _ _ _, _], _, _, _, _, hu, _, _, _, _ | [.as _ _, _], _, _, _, _, hu, _, _, _, _
    | [.app _ [], _], _, _, _, _, hu, _, _, _, _ | [.app _ [_], _], _, _, _, _, hu, _, _, _, _
    | [.app _ (_ :: _ :: _ :: _), _], _, _, _, _, hu, _, _, _, _ => by
      obtain ⟨_, _, _, _, he, -⟩ := uniqConcat_inv hu
      simp at he
end

end KCore.Det
