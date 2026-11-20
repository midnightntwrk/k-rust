/-
  KCore. The three law sentences the text states of `_RangeMap_` (domains.md 508: `assoc`,
  `unit(.RangeMap)`; kompiled as equalities of patterns) hold at range-map values under
  `rangeMapHooks`' concatenation:
  - `rmConcat_unit`: `.RangeMap` is the value `rmV []`, and `_RangeMap_` of it and a value, either
    way round, is that value;
  - `rmConcat_assoc`: `(m n) p` and `m (n p)` are one result of `rmHook`, both without a value together, as an
    equality of patterns states (where `rmHook` gives none the point is silent, `silentTable`, and the value is the interpretation's).

  The proof reads a range map by the function it describes (`RmCov`: an interval of the entries
  holds the key with the value). Concatenation has a value of `rmHook` exactly where the two functions have no
  key in common and then describes their union; the description of a function by maximal
  intervals in order is unique (`rmOK_unique`); so both groupings describe the union of the three
  functions by maximal intervals, and are one list.
-/
import KcoreSpec.RangeMapHooks
import KcoreSpec.OrderLaws

set_option autoImplicit false

namespace KCore

/-! ## Triples and entries -/

/-- The entries of triples. -/
def rmEntries (ts : List RmTriple) : Entries := ts.map fun (a, b, v) => (rangeT a b, v)

/-- The canonical triples of pairwise disjoint proper intervals (`rmCanon` before the range terms). -/
def rmCanonT (ts : List RmTriple) : List RmTriple := rmMerge (ts.foldr rmInsert [])

theorem rmCanon_eq (ts : List RmTriple) : rmCanon ts = rmEntries (rmCanonT ts) := rfl

/-- Maximal intervals in order, at triples: each proper, each ending at or before the next begins,
two that touch of different values (`rangesOK` of the entries). -/
def RmOK : List RmTriple → Prop
  | [] => True
  | [(a, b, _)] => a < b
  | (a, b, v) :: (a', b', v') :: ts => a < b ∧ b ≤ a' ∧ (b = a' → v ≠ v') ∧ RmOK ((a', b', v') :: ts)

/-- The triples hold the key k with the value x. -/
def RmCov (ts : List RmTriple) (k : Int) (x : GroundTerm) : Prop :=
  ∃ t ∈ ts, t.1 ≤ k ∧ k < t.2.1 ∧ t.2.2 = x

/-- No key is held by both. -/
def RmApart (ts us : List RmTriple) : Prop :=
  ∀ k x y, RmCov ts k x → RmCov us k y → False

theorem asRange_rangeT_eq (a b : Int) : asRange (rangeT a b) = if a < b then some (a, b) else none := by
  by_cases h : a < b <;> simp [asRange, rangeT, asKInt, kint, asInt, int, h]

theorem rmTriples_rmEntries : ∀ {ts : List RmTriple}, (∀ t ∈ ts, t.1 < t.2.1) →
    rmTriples (rmEntries ts) = some ts
  | [], _ => rfl
  | (a, b, v) :: ts, h => by
    have hab := h _ (List.mem_cons_self ..)
    have ih := rmTriples_rmEntries (ts := ts) (fun t ht => h t (List.mem_cons_of_mem _ ht))
    unfold rmTriples rmEntries at ih ⊢
    rw [List.map_cons, List.mapM_cons, ih]
    simp [asRange_rangeT hab]

theorem rmTriples_cons (k v : GroundTerm) (es : Entries) :
    rmTriples ((k, v) :: es) = (asRange k).bind fun p => (rmTriples es).map fun ts => (p.1, p.2, v) :: ts := by
  unfold rmTriples
  rw [List.mapM_cons]
  cases hk : asRange k with
  | none => simp [hk]
  | some p =>
    simp only [hk, Option.bind_some]
    generalize List.mapM (m := Option) _ es = r
    cases r <;> rfl

theorem rmEntries_of_rmTriples : ∀ {es : Entries} {ts : List RmTriple}, rmTriples es = some ts →
    es = rmEntries ts
  | [], ts, h => by simp [rmTriples] at h; subst h; rfl
  | (k, v) :: es, ts, h => by
    rw [rmTriples_cons] at h
    cases hk : asRange k with
    | none => simp [hk] at h
    | some p =>
      obtain ⟨a, b⟩ := p
      cases hr : rmTriples es with
      | none => simp [hk, hr] at h
      | some us =>
        simp only [hk, hr, Option.map_some, Option.bind_some, Option.some.injEq] at h
        subst h
        have := rmEntries_of_rmTriples (es := es) (ts := us) hr
        simp [rmEntries, (asRange_some hk).1, this]

theorem rmOK_of_rangesOK : ∀ {ts : List RmTriple}, rangesOK (rmEntries ts) = true → RmOK ts
  | [], _ => trivial
  | [(a, b, v)], h => by
    by_cases hab : a < b
    · exact hab
    · simp [rmEntries, rangesOK, asRange_rangeT_eq, hab] at h
  | (a, b, v) :: (a', b', v') :: ts, h => by
    have ih := @rmOK_of_rangesOK ((a', b', v') :: ts)
    simp only [rmEntries, List.map_cons, rangesOK, Bool.and_eq_true] at h ih
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_, ?_, ih h2⟩ <;>
    · by_cases hab : a < b <;> by_cases hab' : a' < b' <;>
        simp only [asRange_rangeT_eq, hab, hab', ite_true, ite_false] at h1 <;>
        simp at h1
      all_goals first
        | exact hab
        | exact h1.1
        | (intro he hv; subst hv; rcases h1.2 with h | h
           · exact h he
           · simp [GroundTerm.cmp_refl] at h)

theorem rangesOK_of_rmOK : ∀ {ts : List RmTriple}, RmOK ts → rangesOK (rmEntries ts) = true
  | [], _ => rfl
  | [(a, b, v)], h => by simp [rmEntries, rangesOK, asRange_rangeT h]
  | (a, b, v) :: (a', b', v') :: ts, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have ih := rangesOK_of_rmOK h4
    have h1' : a' < b' := by
      cases ts with
      | nil => exact h4
      | cons _ _ => exact h4.1
    simp only [rmEntries, List.map_cons] at ih ⊢
    simp only [rangesOK, asRange_rangeT h1, asRange_rangeT h1', ih, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨h2, ?_⟩
    by_cases hb : b = a'
    · right
      have hv := h3 hb
      cases hc : GroundTerm.cmp v v' with
      | eq => exact absurd (GroundTerm.cmp_eq v v' hc) hv
      | _ => decide
    · exact .inl hb

/-- A range map value's entries are the entries of maximal triples. -/
theorem rmOK_of_value {es : Entries} (h : rangesOK es = true) :
    ∃ ts, rmTriples es = some ts ∧ es = rmEntries ts ∧ RmOK ts := by
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp (rmTriples_of_rangesOK h)
  have he := rmEntries_of_rmTriples hts
  exact ⟨ts, hts, he, rmOK_of_rangesOK (he ▸ h)⟩

/-! ## What `RmOK` gives -/

theorem rmOK_tail {t : RmTriple} {ts : List RmTriple} (h : RmOK (t :: ts)) : RmOK ts := by
  match t, ts, h with
  | _, [], _ => trivial
  | (_, _, _), (_, _, _) :: _, h => exact h.2.2.2

theorem rmOK_head {t : RmTriple} {ts : List RmTriple} (h : RmOK (t :: ts)) : t.1 < t.2.1 := by
  match t, ts, h with
  | (_, _, _), [], h => exact h
  | (_, _, _), (_, _, _) :: _, h => exact h.1

theorem rmOK_proper : ∀ {ts : List RmTriple}, RmOK ts → ∀ t ∈ ts, t.1 < t.2.1
  | [], _, _, ht => absurd ht (List.not_mem_nil)
  | _ :: _, h, _, ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact rmOK_head h
    · exact rmOK_proper (rmOK_tail h) _ ht

/-- Every later interval begins at or after an interval ends. -/
theorem rmOK_after : ∀ {t : RmTriple} {ts : List RmTriple}, RmOK (t :: ts) → ∀ u ∈ ts, t.2.1 ≤ u.1
  | _, [], _, _, hu => absurd hu (List.not_mem_nil)
  | (a, b, v), (a', b', v') :: ts, h, u, hu => by
    obtain ⟨-, h2, -, h4⟩ := h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h2
    · have h5 := rmOK_after h4 u hu
      have h6 := rmOK_head h4
      simp only at h5 h6 ⊢
      omega

theorem rmOK_pairwise : ∀ {ts : List RmTriple}, RmOK ts → ts.Pairwise fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1
  | [], _ => .nil
  | _ :: _, h => .cons (fun u hu => .inl (rmOK_after h u hu)) (rmOK_pairwise (rmOK_tail h))

theorem rmCov_nil (k : Int) (x : GroundTerm) : ¬ RmCov [] k x := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem rmCov_cons {t : RmTriple} {ts : List RmTriple} {k : Int} {x : GroundTerm} :
    RmCov (t :: ts) k x ↔ (t.1 ≤ k ∧ k < t.2.1 ∧ t.2.2 = x) ∨ RmCov ts k x := by
  constructor
  · rintro ⟨u, hu, h⟩
    rcases List.mem_cons.mp hu with rfl | hu
    · exact .inl h
    · exact .inr ⟨u, hu, h⟩
  · rintro (h | ⟨u, hu, h⟩)
    · exact ⟨t, List.mem_cons_self .., h⟩
    · exact ⟨u, List.mem_cons_of_mem _ hu, h⟩

theorem rmCov_append {ts us : List RmTriple} {k : Int} {x : GroundTerm} :
    RmCov (ts ++ us) k x ↔ RmCov ts k x ∨ RmCov us k x := by
  constructor
  · rintro ⟨u, hu, h⟩
    rcases List.mem_append.mp hu with hu | hu
    · exact .inl ⟨u, hu, h⟩
    · exact .inr ⟨u, hu, h⟩
  · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
    · exact ⟨u, List.mem_append_left _ hu, h⟩
    · exact ⟨u, List.mem_append_right _ hu, h⟩

/-- The keys of maximal triples are at or after the first lower bound. -/
theorem rmOK_low {t : RmTriple} {ts : List RmTriple} (h : RmOK (t :: ts)) {k : Int} {x : GroundTerm}
    (hc : RmCov (t :: ts) k x) : t.1 ≤ k := by
  rcases rmCov_cons.mp hc with h1 | ⟨u, hu, h1⟩
  · exact h1.1
  · have := rmOK_after h u hu
    have := rmOK_head h
    omega

/-- A key of the tail is at or after the first interval ends. -/
theorem rmOK_tailCov {t : RmTriple} {ts : List RmTriple} (h : RmOK (t :: ts)) {k : Int} {x : GroundTerm}
    (hc : RmCov ts k x) : t.2.1 ≤ k := by
  obtain ⟨u, hu, h1⟩ := hc
  have := rmOK_after h u hu
  omega

/-- **The description of a function by maximal intervals in order is unique.** -/
theorem rmOK_unique : ∀ {ts us : List RmTriple}, RmOK ts → RmOK us →
    (∀ k x, RmCov ts k x ↔ RmCov us k x) → ts = us
  | [], [], _, _, _ => rfl
  | [], u :: us, _, hu, he => by
    have hp := rmOK_head hu
    exact absurd ((he u.1 u.2.2).mpr (rmCov_cons.mpr (.inl ⟨Int.le_refl _, hp, rfl⟩))) (rmCov_nil _ _)
  | t :: ts, [], ht, _, he => by
    have hp := rmOK_head ht
    exact absurd ((he t.1 t.2.2).mp (rmCov_cons.mpr (.inl ⟨Int.le_refl _, hp, rfl⟩))) (rmCov_nil _ _)
  | (a, b, v) :: ts, (a', b', v') :: us, ht, hu, he => by
    have hab := rmOK_head ht
    have hab' := rmOK_head hu
    simp only at hab hab'
    -- the first lower bounds
    have h1 : a ≤ a' := rmOK_low ht ((he a' v').mpr (rmCov_cons.mpr (.inl ⟨Int.le_refl _, hab', rfl⟩)))
    have h2 : a' ≤ a := rmOK_low hu ((he a v).mp (rmCov_cons.mpr (.inl ⟨Int.le_refl _, hab, rfl⟩)))
    have haa : a = a' := Int.le_antisymm h1 h2
    subst haa
    -- the first values
    have hvv : v = v' := by
      rcases rmCov_cons.mp ((he a v).mp (rmCov_cons.mpr (.inl ⟨Int.le_refl _, hab, rfl⟩))) with h | h
      · exact h.2.2.symm
      · have := rmOK_tailCov hu h; simp only at this; omega
    subst hvv
    -- the first upper bounds: at the smaller one, the other list still gives v, the one it ends
    -- has the key off its intervals or under a touching interval of another value
    have hlt : ∀ {b b' : Int} {ts us : List RmTriple}, RmOK ((a, b, v) :: ts) → RmOK ((a, b', v) :: us) →
        (∀ k x, RmCov ((a, b, v) :: ts) k x ↔ RmCov ((a, b', v) :: us) k x) → ¬ b < b' := by
      intro b b' ts us ht hu he hlt
      have hab := rmOK_head ht
      simp only at hab
      have hc := (he b v).mpr (rmCov_cons.mpr (.inl ⟨by omega, hlt, rfl⟩))
      rcases rmCov_cons.mp hc with h | h
      · simp only at h; omega
      · match ts, ht, h with
        | [], _, h => exact rmCov_nil _ _ h
        | (c, d, w) :: ts, ht, h =>
          obtain ⟨-, hbc, hne, ht'⟩ := ht
          have hcb := rmOK_low ht' h
          simp only at hcb
          have hcd := rmOK_head ht'
          simp only at hcd
          rcases rmCov_cons.mp h with h | h
          · exact hne (by omega) h.2.2.symm
          · have := rmOK_tailCov ht' h; simp only at this; omega
    have hbb : b = b' := by
      rcases Int.lt_trichotomy b b' with h | h | h
      · exact absurd h (hlt ht hu he)
      · exact h
      · exact absurd h (hlt hu ht (fun k x => (he k x).symm))
    subst hbb
    -- the tails
    have htl : ∀ k x, RmCov ts k x ↔ RmCov us k x := by
      intro k x
      constructor
      · intro h
        have hk := rmOK_tailCov ht h
        rcases rmCov_cons.mp ((he k x).mp (rmCov_cons.mpr (.inr h))) with h' | h'
        · simp only at h' hk; omega
        · exact h'
      · intro h
        have hk := rmOK_tailCov hu h
        rcases rmCov_cons.mp ((he k x).mpr (rmCov_cons.mpr (.inr h))) with h' | h'
        · simp only at h' hk; omega
        · exact h'
    rw [rmOK_unique (rmOK_tail ht) (rmOK_tail hu) htl]

/-! ## Canonical triples -/

/-- Merging keeps the function of proper intervals. -/
theorem rmCov_rmMerge : ∀ (l : List RmTriple), (∀ t ∈ l, t.1 < t.2.1) →
    ∀ k x, RmCov (rmMerge l) k x ↔ RmCov l k x
  | [], _, _, _ => by simp [rmMerge]
  | [_], _, _, _ => by simp [rmMerge]
  | (a, b, v) :: (a', b', v') :: ts, hp, k, x => by
    have h1 := hp _ (List.mem_cons_self ..)
    have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only at h1 h2
    unfold rmMerge
    split
    · rename_i hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, hvv⟩ := hm
      have hvv := GroundTerm.cmp_eq v v' hvv
      subst hvv
      rw [rmCov_rmMerge ((a, b', v) :: ts) (by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · simp only; omega
        · exact hp t (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))) k x]
      simp only [rmCov_cons]
      constructor
      · rintro (⟨h3, h4, h5⟩ | h)
        · by_cases hk : k < b
          · exact .inl ⟨h3, hk, h5⟩
          · exact .inr (.inl ⟨by omega, h4, h5⟩)
        · exact .inr (.inr h)
      · rintro (⟨h3, h4, h5⟩ | ⟨h3, h4, h5⟩ | h)
        · exact .inl ⟨h3, by omega, h5⟩
        · exact .inl ⟨by omega, h4, h5⟩
        · exact .inr h
    · rw [rmCov_cons, rmCov_rmMerge ((a', b', v') :: ts) (fun t ht => hp t (List.mem_cons_of_mem _ ht)) k x,
        ← rmCov_cons]
  termination_by l => l.length

theorem rmCov_perm {ts us : List RmTriple} (h : ts.Perm us) (k : Int) (x : GroundTerm) :
    RmCov ts k x ↔ RmCov us k x :=
  ⟨fun ⟨t, ht, h'⟩ => ⟨t, h.mem_iff.mp ht, h'⟩, fun ⟨t, ht, h'⟩ => ⟨t, h.mem_iff.mpr ht, h'⟩⟩

/-- The canonical triples of pairwise disjoint proper intervals are maximal, describe the same
function, and are the triples of `rmCanon`'s entries. -/
theorem rmCanonT_spec {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1)
    (hd : ts.Pairwise fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1) :
    RmOK (rmCanonT ts) ∧ (∀ k x, RmCov (rmCanonT ts) k x ↔ RmCov ts k x) := by
  have hok := rmOK_of_rangesOK (rangesOK_rmCanon hp hd)
  refine ⟨hok, fun k x => ?_⟩
  rw [rmCanonT, rmCov_rmMerge _ (fun t ht => hp t ((rmSort_perm ts).mem_iff.mp ht)) k x]
  exact rmCov_perm (rmSort_perm ts) k x

/-- `rmDisjoint` of proper intervals: no key in common. -/
theorem rmDisjoint_iff {ts us : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hq : ∀ u ∈ us, u.1 < u.2.1) :
    rmDisjoint ts us = true ↔ RmApart ts us := by
  have hall : rmDisjoint ts us = true ↔ ∀ t ∈ ts, ∀ u ∈ us, t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1 := by
    simp only [rmDisjoint, List.all_eq_true]
    constructor
    · intro h t ht u hu
      have := h t ht u hu
      obtain ⟨x, y, _⟩ := t; obtain ⟨x', y', _⟩ := u
      simpa using this
    · intro h t ht u hu
      have := h t ht u hu
      obtain ⟨x, y, _⟩ := t; obtain ⟨x', y', _⟩ := u
      simpa using this
  rw [hall]
  constructor
  · rintro h k x y ⟨t, ht, h1⟩ ⟨u, hu, h2⟩
    have := h t ht u hu
    omega
  · intro h t ht u hu
    have h1 := hp t ht
    have h2 := hq u hu
    by_cases hn : t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1
    · exact hn
    exfalso
    exact h (max t.1 u.1) t.2.2 u.2.2 ⟨t, ht, by omega, by omega, rfl⟩ ⟨u, hu, by omega, by omega, rfl⟩

/-! ## Concatenation at triples -/

/-- `_RangeMap_` at triples. -/
def rmCatT (ts us : List RmTriple) : Option (List RmTriple) :=
  if rmDisjoint ts us then some (rmCanonT (ts ++ us)) else none

/-- **Concatenation of maximal triples**: defined exactly where no key is in both, and then the
maximal triples of the union. -/
theorem rmCatT_some {ts us zs : List RmTriple} (ht : RmOK ts) (hu : RmOK us) :
    rmCatT ts us = some zs ↔ RmApart ts us ∧ RmOK zs ∧ ∀ k x, RmCov zs k x ↔ RmCov ts k x ∨ RmCov us k x := by
  have hd := rmDisjoint_iff (rmOK_proper ht) (rmOK_proper hu)
  have hpd : RmApart ts us → (∀ t ∈ ts ++ us, t.1 < t.2.1) ∧
      (ts ++ us).Pairwise fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1 := by
    intro ha
    refine ⟨fun t h => ?_, ?_⟩
    · rcases List.mem_append.mp h with h | h
      · exact rmOK_proper ht t h
      · exact rmOK_proper hu t h
    · rw [List.pairwise_append]
      have hall : ∀ t ∈ ts, ∀ u ∈ us, t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1 := by
        have := hd.mpr ha
        simp only [rmDisjoint, List.all_eq_true] at this
        intro t ht u hu
        have := this t ht u hu
        obtain ⟨x, y, _⟩ := t; obtain ⟨x', y', _⟩ := u
        simpa using this
      exact ⟨rmOK_pairwise ht, rmOK_pairwise hu, hall⟩
  unfold rmCatT
  constructor
  · intro h
    split at h
    · rename_i hdis
      cases h
      have ha := hd.mp hdis
      obtain ⟨hp, hpw⟩ := hpd ha
      obtain ⟨hok, hcov⟩ := rmCanonT_spec hp hpw
      exact ⟨ha, hok, fun k x => (hcov k x).trans rmCov_append⟩
    · cases h
  · rintro ⟨ha, hok, hcov⟩
    simp only [hd.mpr ha, ↓reduceIte]
    obtain ⟨hp, hpw⟩ := hpd ha
    obtain ⟨hok', hcov'⟩ := rmCanonT_spec hp hpw
    exact congrArg some (rmOK_unique hok' hok fun k x => (hcov' k x).trans (rmCov_append.trans (hcov k x).symm))

theorem rmCatT_ok {ts us zs : List RmTriple} (ht : RmOK ts) (hu : RmOK us) (h : rmCatT ts us = some zs) :
    RmOK zs := ((rmCatT_some ht hu).mp h).2.1

/-- What either grouping of three concatenations gives. -/
theorem rmCatT3 {ts us ws zs : List RmTriple} (ht : RmOK ts) (hu : RmOK us) (hw : RmOK ws) :
    ((rmCatT ts us).bind fun x => rmCatT x ws) = some zs ↔
      RmApart ts us ∧ RmApart ts ws ∧ RmApart us ws ∧ RmOK zs ∧
        ∀ k x, RmCov zs k x ↔ RmCov ts k x ∨ RmCov us k x ∨ RmCov ws k x := by
  constructor
  · intro h
    cases hx : rmCatT ts us with
    | none => simp [hx] at h
    | some xs =>
      simp only [hx, Option.bind_some] at h
      obtain ⟨hTU, hX, hcX⟩ := (rmCatT_some ht hu).mp hx
      obtain ⟨hXW, hZ, hcZ⟩ := (rmCatT_some hX hw).mp h
      refine ⟨hTU, fun k x y h1 h2 => hXW k x y ((hcX k x).mpr (.inl h1)) h2,
        fun k x y h1 h2 => hXW k x y ((hcX k x).mpr (.inr h1)) h2, hZ, fun k x => ?_⟩
      rw [hcZ, hcX, or_assoc]
  · rintro ⟨hTU, hTW, hUW, hZ, hcZ⟩
    have hd := rmDisjoint_iff (rmOK_proper ht) (rmOK_proper hu)
    have hpw : (ts ++ us).Pairwise fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1 := by
      rw [List.pairwise_append]
      have := hd.mpr hTU
      simp only [rmDisjoint, List.all_eq_true] at this
      refine ⟨rmOK_pairwise ht, rmOK_pairwise hu, fun t ht' u hu' => ?_⟩
      have := this t ht' u hu'
      obtain ⟨x, y, _⟩ := t; obtain ⟨x', y', _⟩ := u
      simpa using this
    have hp : ∀ t ∈ ts ++ us, t.1 < t.2.1 := fun t h => by
      rcases List.mem_append.mp h with h | h
      · exact rmOK_proper ht t h
      · exact rmOK_proper hu t h
    obtain ⟨hX, hcX⟩ := rmCanonT_spec hp hpw
    have hx : rmCatT ts us = some (rmCanonT (ts ++ us)) :=
      (rmCatT_some ht hu).mpr ⟨hTU, hX, fun k x => (hcX k x).trans rmCov_append⟩
    rw [hx, Option.bind_some, rmCatT_some hX hw]
    refine ⟨fun k x y h1 h2 => ?_, hZ, fun k x => ?_⟩
    · rcases rmCov_append.mp ((hcX k x).mp h1) with h1 | h1
      · exact hTW k x y h1 h2
      · exact hUW k x y h1 h2
    · rw [hcZ, hcX, rmCov_append, or_assoc]

theorem rmApart_symm {ts us : List RmTriple} (h : RmApart ts us) : RmApart us ts :=
  fun k x y h1 h2 => h k y x h2 h1

/-- Associativity at triples. -/
theorem rmCatT_assoc {ts us ws : List RmTriple} (ht : RmOK ts) (hu : RmOK us) (hw : RmOK ws) :
    ((rmCatT ts us).bind fun x => rmCatT x ws) = ((rmCatT us ws).bind fun y => rmCatT ts y) := by
  apply Option.ext
  intro zs
  rw [rmCatT3 ht hu hw]
  constructor
  · rintro ⟨hTU, hTW, hUW, hZ, hcZ⟩
    cases hy : rmCatT us ws with
    | none =>
      exfalso
      have hd := rmDisjoint_iff (rmOK_proper hu) (rmOK_proper hw)
      have hp : ∀ t ∈ us ++ ws, t.1 < t.2.1 := fun t h => by
        rcases List.mem_append.mp h with h | h
        · exact rmOK_proper hu t h
        · exact rmOK_proper hw t h
      have hpw : (us ++ ws).Pairwise fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1 := by
        rw [List.pairwise_append]
        have := hd.mpr hUW
        simp only [rmDisjoint, List.all_eq_true] at this
        refine ⟨rmOK_pairwise hu, rmOK_pairwise hw, fun t ht' u hu' => ?_⟩
        have := this t ht' u hu'
        obtain ⟨x, y, _⟩ := t; obtain ⟨x', y', _⟩ := u
        simpa using this
      obtain ⟨hY, hcY⟩ := rmCanonT_spec hp hpw
      have := (rmCatT_some hu hw).mpr ⟨hUW, hY, fun k x => (hcY k x).trans rmCov_append⟩
      rw [hy] at this; cases this
    | some ys =>
      obtain ⟨-, hY, hcY⟩ := (rmCatT_some hu hw).mp hy
      simp only [Option.bind_some]
      rw [rmCatT_some ht hY]
      refine ⟨fun k x y h1 h2 => ?_, hZ, fun k x => by rw [hcZ, hcY]⟩
      rcases (hcY k y).mp h2 with h2 | h2
      · exact hTU k x y h1 h2
      · exact hTW k x y h1 h2
  · intro h
    cases hy : rmCatT us ws with
    | none => simp [hy] at h
    | some ys =>
      simp only [hy, Option.bind_some] at h
      obtain ⟨hUW, hY, hcY⟩ := (rmCatT_some hu hw).mp hy
      obtain ⟨hTY, hZ, hcZ⟩ := (rmCatT_some ht hY).mp h
      exact ⟨fun k x y h1 h2 => hTY k x y h1 ((hcY k y).mpr (.inl h2)),
        fun k x y h1 h2 => hTY k x y h1 ((hcY k y).mpr (.inr h2)), hUW, hZ,
        fun k x => by rw [hcZ, hcY]⟩

/-! ## The laws at range-map values -/

theorem rmHook_rmUnit : rmHook rmUnit [] = some (some (rmV [])) := rfl

theorem rmHook_rmConcat (s s' : Srt) (m n : Entries) :
    rmHook rmConcat [.map s m, .map s' n] =
      some ((rmTriples m).bind fun ts => (rmTriples n).bind fun us =>
        if rmDisjoint ts us then some (rmV (rmCanon (ts ++ us))) else none) := rfl

/-- `_RangeMap_` at two range-map values, read through their maximal triples. -/
theorem rmConcat_value {ts us : List RmTriple} (ht : RmOK ts) (hu : RmOK us) :
    (rmHook rmConcat [rmV (rmEntries ts), rmV (rmEntries us)]).join =
      (rmCatT ts us).map fun zs => rmV (rmEntries zs) := by
  rw [rmV, rmV, rmHook_rmConcat, rmTriples_rmEntries (rmOK_proper ht), rmTriples_rmEntries (rmOK_proper hu)]
  simp only [Option.bind_some, Option.join_some, rmCatT, rmCanon_eq]
  split <;> rfl

/-- **`.RangeMap` is the unit of `_RangeMap_` at range-map values** (domains.md 508,
`unit(.RangeMap)`): `.RangeMap` is `rmV []`, and the concatenation of it and a value, either way
round, is the value. -/
theorem rmConcat_unit {es : Entries} (h : rangesOK es = true) :
    rmHook rmUnit [] = some (some (rmV [])) ∧
    rmHook rmConcat [rmV [], rmV es] = some (some (rmV es)) ∧
    rmHook rmConcat [rmV es, rmV []] = some (some (rmV es)) := by
  obtain ⟨ts, hts, rfl, hok⟩ := rmOK_of_value h
  have hp := rmOK_proper hok
  obtain ⟨hc, hcov⟩ := rmCanonT_spec hp (rmOK_pairwise hok)
  have hcanon : rmCanonT ts = ts := rmOK_unique hc hok hcov
  refine ⟨rfl, ?_, ?_⟩
  · rw [rmV, rmV, rmHook_rmConcat, hts]
    simp [rmTriples, rmDisjoint, rmCanon_eq, hcanon, rmV]
  · rw [rmV, rmV, rmHook_rmConcat, hts]
    simp [rmTriples, rmDisjoint, rmCanon_eq, hcanon, rmV]

/-- **`_RangeMap_` is associative at range-map values** (domains.md 508, `assoc`), as an equality
of patterns: `(m n) p` and `m (n p)` both have no value of `rmHook` (silent points of `_RangeMap_`), or have one value. -/
theorem rmConcat_assoc {es fs gs : Entries} (he : rangesOK es = true) (hf : rangesOK fs = true)
    (hg : rangesOK gs = true) :
    ((rmHook rmConcat [rmV es, rmV fs]).join.bind fun x => (rmHook rmConcat [x, rmV gs]).join) =
      ((rmHook rmConcat [rmV fs, rmV gs]).join.bind fun y => (rmHook rmConcat [rmV es, y]).join) := by
  obtain ⟨ts, -, rfl, ht⟩ := rmOK_of_value he
  obtain ⟨us, -, rfl, hu⟩ := rmOK_of_value hf
  obtain ⟨ws, -, rfl, hw⟩ := rmOK_of_value hg
  rw [rmConcat_value ht hu, rmConcat_value hu hw]
  have hl : ((rmCatT ts us).map fun zs => rmV (rmEntries zs)).bind
      (fun x => (rmHook rmConcat [x, rmV (rmEntries ws)]).join) =
      ((rmCatT ts us).bind fun x => rmCatT x ws).map fun zs => rmV (rmEntries zs) := by
    cases hx : rmCatT ts us with
    | none => rfl
    | some xs =>
      simp only [Option.map_some, Option.bind_some]
      exact rmConcat_value (rmCatT_ok ht hu hx) hw
  have hr : ((rmCatT us ws).map fun zs => rmV (rmEntries zs)).bind
      (fun y => (rmHook rmConcat [rmV (rmEntries ts), y]).join) =
      ((rmCatT us ws).bind fun y => rmCatT ts y).map fun zs => rmV (rmEntries zs) := by
    cases hy : rmCatT us ws with
    | none => rfl
    | some ys =>
      simp only [Option.map_some, Option.bind_some]
      exact rmConcat_value ht (rmCatT_ok hu hw hy)
  rw [hl, hr, rmCatT_assoc ht hu hw]

end KCore
