/-
  What the laws of the overloading symbols' normal forms (`Semantics.norm`, Value.lean) read, over
  a semantics whose overloading symbols are well formed (`overloadsOK`) and whose subsorts are
  transitive and irreflexive (`OvlHyp`):

  - lifting and stripping along the subsorts, on values and on argument lists;
  - the overloads' data: an overloading symbol's rank (its place in `ovls`, `ovlRank`), the
    signatures found among the constructors and the overloading symbols (`KnownSig`), and what
    `overloadsOK` says of each overloading symbol (`ovl_leaves_fad`, `ovl_parts`);
  - `norm` at a symbol that is no overloading symbol and at arguments no overload covers
    (`norm_none`, `norm_find_none`).

  The laws themselves, which hold at the arguments no function overload covers, are in
  OvlLawsFn.lean.
-/
import KcoreSpec.FaithOK

namespace KCore

/-- Values `us` of the sorts `as`, lifted to the sorts `bs`, position by position. -/
def liftAll (as bs : List Srt) (us : List GroundTerm) : List GroundTerm :=
  ((as.zip bs).zip us).map fun ((A, B), u) => lift A B u

namespace OvlLaws

/-! ## Positions -/

theorem zip3_all_iff {α β γ : Type} {p : α → β → γ → Bool} :
    ∀ {as : List α} {bs : List β} {vs : List γ},
    ((as.zip bs).zip vs).all (fun ((A, B), v) => p A B v) = true ↔
      ∀ i (h1 : i < as.length) (h2 : i < bs.length) (h3 : i < vs.length), p as[i] bs[i] vs[i] = true
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, [] => by simp
  | a :: as, b :: bs, v :: vs => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, zip3_all_iff]
    constructor
    · rintro ⟨h0, h⟩ i h1 h2 h3
      cases i with
      | zero => exact h0
      | succ i =>
        exact h i (by simpa using h1) (by simpa using h2) (by simpa using h3)
    · intro h
      exact ⟨h 0 (by simp) (by simp) (by simp),
        fun i h1 h2 h3 => h (i + 1) (by simpa using h1) (by simpa using h2) (by simpa using h3)⟩

theorem zip2_all_iff {α β : Type} {p : α → β → Bool} :
    ∀ {as : List α} {bs : List β},
    (as.zip bs).all (fun (A, B) => p A B) = true ↔
      ∀ i (h1 : i < as.length) (h2 : i < bs.length), p as[i] bs[i] = true
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: as, b :: bs => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, zip2_all_iff]
    constructor
    · rintro ⟨h0, h⟩ i h1 h2
      cases i with
      | zero => exact h0
      | succ i => exact h i (by simpa using h1) (by simpa using h2)
    · intro h
      exact ⟨h 0 (by simp) (by simp), fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2)⟩

theorem length_stripAll (as bs : List Srt) (vs : List GroundTerm) :
    (stripAll as bs vs).length = min (min as.length bs.length) vs.length := by
  simp [stripAll]

theorem getElem_stripAll {as bs : List Srt} {vs : List GroundTerm} {i : Nat}
    (h : i < (stripAll as bs vs).length) :
    (stripAll as bs vs)[i] =
      strip (as[i]'(by simp [stripAll] at h; omega)) (bs[i]'(by simp [stripAll] at h; omega))
        (vs[i]'(by simp [stripAll] at h; omega)) := by
  simp [stripAll]

theorem length_liftAll (as bs : List Srt) (vs : List GroundTerm) :
    (liftAll as bs vs).length = min (min as.length bs.length) vs.length := by
  simp [liftAll]

theorem getElem_liftAll {as bs : List Srt} {vs : List GroundTerm} {i : Nat}
    (h : i < (liftAll as bs vs).length) :
    (liftAll as bs vs)[i] =
      lift (as[i]'(by simp [liftAll] at h; omega)) (bs[i]'(by simp [liftAll] at h; omega))
        (vs[i]'(by simp [liftAll] at h; omega)) := by
  simp [liftAll]

/-! ## Lifting and stripping -/

variable {c : Semantics}

/-- What the laws read of a semantics: its overloading symbols are well formed, its subsorts
transitive and irreflexive. -/
structure OvlHyp (c : Semantics) : Prop where
  ok : c.overloadsOK = true
  trans : ∀ a b e, (a, b) ∈ c.subsorts → (b, e) ∈ c.subsorts → (a, e) ∈ c.subsorts
  irrefl : ∀ a, (a, a) ∉ c.subsorts

theorem le_iff {a b : Srt} : c.le a b = true ↔ a = b ∨ (a, b) ∈ c.subsorts := by
  simp [Semantics.le]

theorem le_refl (a : Srt) : c.le a a = true := le_iff.mpr (.inl rfl)

theorem le_of_mem {a b : Srt} (h : (a, b) ∈ c.subsorts) : c.le a b = true := le_iff.mpr (.inr h)

theorem mem_of_le {a b : Srt} (h : c.le a b = true) (hne : a ≠ b) : (a, b) ∈ c.subsorts :=
  (le_iff.mp h).resolve_left hne

section
variable (H : OvlHyp c)
include H

theorem le_trans {a b e : Srt} (h1 : c.le a b = true) (h2 : c.le b e = true) : c.le a e = true := by
  rcases le_iff.mp h1 with rfl | h1
  · exact h2
  rcases le_iff.mp h2 with rfl | h2
  · exact le_of_mem h1
  exact le_of_mem (H.trans _ _ _ h1 h2)

theorem le_antisymm {a b : Srt} (h1 : c.le a b = true) (h2 : c.le b a = true) : a = b := by
  rcases le_iff.mp h1 with rfl | h1
  · rfl
  rcases le_iff.mp h2 with rfl | h2
  · rfl
  exact absurd (H.trans _ _ _ h1 h2) (H.irrefl a)

end

theorem sortOf_inj_iff {a b : Srt} {t : GroundTerm} {s : Srt} :
    c.sortOf (.inj a b t) = some s ↔
      (a, b) ∈ c.subsorts ∧ t.isInj = false ∧ c.sortOf t = some a ∧ s = b := by
  simp only [Semantics.sortOf]
  constructor
  · intro h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true', beq_iff_eq] at hc
      exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨h1, h2, h3, rfl⟩
    simp [h1, h2, h3]

theorem strip_self (A : Srt) (v : GroundTerm) : strip A A v = v := by
  cases v <;> simp [strip]

theorem lift_self (A : Srt) (v : GroundTerm) : lift A A v = v := by
  simp [lift]

theorem lies_self (A : Srt) (v : GroundTerm) : c.lies A A v = true := by
  cases v <;> simp [Semantics.lies]

theorem lift_ne {A B : Srt} (h : A ≠ B) (v : GroundTerm) : lift A B v = injNormal A B v := by
  simp [lift, h]

/-- A value lying in a sort A below B and stripped to A, lifted back to B, is itself. -/
theorem lift_strip {A B : Srt} {v : GroundTerm} (hv : c.sortOf v = some B) (hl : c.lies A B v = true) :
    lift A B (strip A B v) = v := by
  by_cases hAB : A = B
  · subst hAB; rw [strip_self, lift_self]
  cases v with
  | inj C B' w =>
    obtain ⟨-, hw, -, rfl⟩ := sortOf_inj_iff.mp hv
    by_cases hCA : C = A
    · subst hCA
      simp only [strip, beq_iff_eq, hAB, ite_false, ite_true, lift_ne hAB]
      cases w <;> simp_all [GroundTerm.isInj, injNormal]
    · simp [strip, hAB, hCA, lift_ne hAB, injNormal]
  | _ => simp [Semantics.lies, hAB] at hl

/-- A value lies in its own sort lifted. -/
theorem lies_lift {A B : Srt} {u : GroundTerm} (hu : c.sortOf u = some A) :
    c.lies A B (lift A B u) = true := by
  by_cases hAB : A = B
  · subst hAB; exact lies_self _ _
  rw [lift_ne hAB]
  cases u with
  | inj a' A' w =>
    obtain ⟨h1, -, -, rfl⟩ := sortOf_inj_iff.mp hu
    simp [injNormal, Semantics.lies, le_of_mem h1]
  | _ => simp [injNormal, Semantics.lies, le_refl]

theorem sortOf_strip {A B : Srt} {v : GroundTerm} (hv : c.sortOf v = some B) (hl : c.lies A B v = true) :
    c.sortOf (strip A B v) = some A := by
  by_cases hAB : A = B
  · subst hAB; rw [strip_self]; exact hv
  cases v with
  | inj C B' w =>
    obtain ⟨h1, hw, hws, rfl⟩ := sortOf_inj_iff.mp hv
    simp only [Semantics.lies, beq_false_of_ne hAB, Bool.false_or] at hl
    by_cases hCA : C = A
    · subst hCA; simp [strip, hAB, hws]
    · simp only [strip, beq_iff_eq, hAB, hCA, ite_false]
      exact sortOf_inj_iff.mpr ⟨mem_of_le hl hCA, hw, hws, rfl⟩
  | _ => simp [Semantics.lies, hAB] at hl

section
variable (H : OvlHyp c)
include H

theorem sortOf_lift {A B : Srt} {u : GroundTerm} (hu : c.sortOf u = some A) (hle : c.le A B = true) :
    c.sortOf (lift A B u) = some B := by
  by_cases hAB : A = B
  · subst hAB; rw [lift_self]; exact hu
  have hab := mem_of_le hle hAB
  rw [lift_ne hAB]
  cases u with
  | inj a' a'' w =>
    obtain ⟨h1, h2, h3, rfl⟩ := sortOf_inj_iff.mp hu
    exact sortOf_inj_iff.mpr ⟨H.trans _ _ _ h1 hab, h2, h3, rfl⟩
  | ctor f ts => exact sortOf_inj_iff.mpr ⟨hab, rfl, hu, rfl⟩
  | dv s l => exact sortOf_inj_iff.mpr ⟨hab, rfl, hu, rfl⟩
  | map s es => exact sortOf_inj_iff.mpr ⟨hab, rfl, hu, rfl⟩
  | set s es => exact sortOf_inj_iff.mpr ⟨hab, rfl, hu, rfl⟩
  | list s es => exact sortOf_inj_iff.mpr ⟨hab, rfl, hu, rfl⟩

/-- A value of A lifted to B and stripped back to A is itself. -/
theorem strip_lift {A B : Srt} {u : GroundTerm} (hu : c.sortOf u = some A) :
    strip A B (lift A B u) = u := by
  by_cases hAB : A = B
  · subst hAB; rw [lift_self, strip_self]
  rw [lift_ne hAB]
  cases u with
  | inj a' A' w =>
    obtain ⟨h1, -, -, rfl⟩ := sortOf_inj_iff.mp hu
    have hne : a' ≠ A := fun he => H.irrefl a' (he ▸ h1)
    simp [injNormal, strip, hAB, hne]
  | _ => simp [injNormal, strip, hAB]

theorem lift_trans {A B C : Srt} (h1 : c.le A B = true) (h2 : c.le B C = true) (x : GroundTerm) :
    lift B C (lift A B x) = lift A C x := by
  by_cases hAB : A = B
  · subst hAB; rw [lift_self]
  by_cases hBC : B = C
  · subst hBC; rw [lift_self]
  have hAC : A ≠ C := fun he => hAB (le_antisymm H h1 (he ▸ h2))
  rw [lift_ne hAB, lift_ne hBC, lift_ne hAC]
  cases x <;> simp [injNormal]

theorem strip_trans {A K B : Srt} {v : GroundTerm} (h1 : c.le A K = true) (h2 : c.le K B = true)
    (hl : c.lies A B v = true) : strip A K (strip K B v) = strip A B v := by
  by_cases hKB : K = B
  · subst hKB; rw [strip_self]
  by_cases hAK : A = K
  · subst hAK; rw [strip_self]
  have hAB : A ≠ B := fun he => hKB (le_antisymm H h2 (he ▸ h1))
  cases v with
  | inj C B' w =>
    simp only [Semantics.lies, beq_false_of_ne hAB, Bool.false_or] at hl
    have hCK : C ≠ K := fun he => hAK (le_antisymm H h1 (he ▸ hl))
    by_cases hCA : C = A
    · simp [strip, hKB, hAK, hAB, hCA]
    · simp [strip, hKB, hAK, hAB, hCK, hCA]
  | _ => simp [strip]

theorem lies_strip {A K B : Srt} {v : GroundTerm} (h1 : c.le A K = true) (h2 : c.le K B = true)
    (hl : c.lies A B v = true) : c.lies A K (strip K B v) = true := by
  by_cases hKB : K = B
  · subst hKB; rw [strip_self]; exact hl
  by_cases hAK : A = K
  · subst hAK; exact lies_self _ _
  have hAB : A ≠ B := fun he => hKB (le_antisymm H h2 (he ▸ h1))
  cases v with
  | inj C B' w =>
    simp only [Semantics.lies, beq_false_of_ne hAB, Bool.false_or] at hl
    have hCK : C ≠ K := fun he => hAK (le_antisymm H h1 (he ▸ hl))
    simp [strip, hKB, hCK, Semantics.lies, hl]
  | _ => simp [Semantics.lies, hAB] at hl

end

/-! ## Argument lists -/

theorem sortsOf_cons_iff {v : GroundTerm} {vs : List GroundTerm} {s : Srt} {ss : List Srt} :
    c.sortsOf (v :: vs) = some (s :: ss) ↔ c.sortOf v = some s ∧ c.sortsOf vs = some ss := by
  simp only [Semantics.sortsOf]
  cases h1 : c.sortOf v <;> cases h2 : c.sortsOf vs <;> simp

theorem sortsOf_iff : ∀ {vs : List GroundTerm} {ss : List Srt},
    c.sortsOf vs = some ss ↔
      vs.length = ss.length ∧ ∀ i (h1 : i < vs.length) (h2 : i < ss.length), c.sortOf vs[i] = some ss[i]
  | [], ss => by
    cases ss <;> simp [Semantics.sortsOf]
  | v :: vs, [] => by
    simp only [Semantics.sortsOf]
    constructor
    · intro h; split at h <;> simp at h
    · rintro ⟨h, -⟩; simp at h
  | v :: vs, s :: ss => by
    rw [sortsOf_cons_iff, sortsOf_iff]
    constructor
    · rintro ⟨h0, hl, h⟩
      refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
      cases i with
      | zero => simpa using h0
      | succ i => simpa using h i (by simpa using h1) (by simpa using h2)
    · rintro ⟨hl, h⟩
      exact ⟨h 0 (by simp) (by simp), by simpa using hl,
        fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2)⟩

/-- Stripping a list of values lying in sorts below theirs gives values of those sorts. -/
theorem sortsOf_stripAll {as bs : List Srt} {vs : List GroundTerm} (hl : as.length = bs.length)
    (hv : c.sortsOf vs = some bs)
    (hlies : ((as.zip bs).zip vs).all (fun ((A, B), v) => c.lies A B v) = true) :
    c.sortsOf (stripAll as bs vs) = some as := by
  obtain ⟨hvl, hvi⟩ := sortsOf_iff.mp hv
  have hli := zip3_all_iff.mp hlies
  refine sortsOf_iff.mpr ⟨by simp [length_stripAll]; omega, fun i h1 h2 => ?_⟩
  rw [getElem_stripAll]
  exact sortOf_strip (hvi i (by omega) (by omega)) (hli i h2 (by omega) (by omega))

theorem sortsOf_liftAll (H : OvlHyp c) {as bs : List Srt} {us : List GroundTerm} (hl : as.length = bs.length)
    (hu : c.sortsOf us = some as) (hle : (as.zip bs).all (fun (A, B) => c.le A B) = true) :
    c.sortsOf (liftAll as bs us) = some bs := by
  obtain ⟨hul, hui⟩ := sortsOf_iff.mp hu
  have hli := zip2_all_iff.mp hle
  refine sortsOf_iff.mpr ⟨by simp [length_liftAll]; omega, fun i h1 h2 => ?_⟩
  rw [getElem_liftAll]
  exact sortOf_lift H (hui i (by omega) (by omega)) (hli i (by omega) h2)

theorem liftAll_self (as : List Srt) {us : List GroundTerm} (hl : us.length = as.length) :
    liftAll as as us = us := by
  refine List.ext_getElem (by simp [length_liftAll]; omega) fun i h1 h2 => ?_
  rw [getElem_liftAll, lift_self]

theorem stripAll_self (as : List Srt) {vs : List GroundTerm} (hl : vs.length = as.length) :
    stripAll as as vs = vs := by
  refine List.ext_getElem (by simp [length_stripAll]; omega) fun i h1 h2 => ?_
  rw [getElem_stripAll, strip_self]

theorem liftAll_stripAll {as bs : List Srt} {vs : List GroundTerm} (hl : as.length = bs.length)
    (hv : c.sortsOf vs = some bs)
    (hlies : ((as.zip bs).zip vs).all (fun ((A, B), v) => c.lies A B v) = true) :
    liftAll as bs (stripAll as bs vs) = vs := by
  obtain ⟨hvl, hvi⟩ := sortsOf_iff.mp hv
  have hli := zip3_all_iff.mp hlies
  refine List.ext_getElem (by simp [length_liftAll, length_stripAll]; omega) fun i h1 h2 => ?_
  rw [getElem_liftAll, getElem_stripAll]
  exact lift_strip (hvi i h2 (by omega)) (hli i (by simp [length_liftAll, length_stripAll] at h1; omega)
    (by omega) h2)

theorem stripAll_liftAll (H : OvlHyp c) {as bs : List Srt} {us : List GroundTerm} (hl : as.length = bs.length)
    (hu : c.sortsOf us = some as) :
    stripAll as bs (liftAll as bs us) = us := by
  obtain ⟨hul, hui⟩ := sortsOf_iff.mp hu
  refine List.ext_getElem (by simp [length_liftAll, length_stripAll]; omega) fun i h1 h2 => ?_
  rw [getElem_stripAll, getElem_liftAll]
  exact strip_lift H (hui i h2 (by omega))

theorem lies_liftAll {as bs : List Srt} {us : List GroundTerm} (hl : as.length = bs.length)
    (hu : c.sortsOf us = some as) :
    ((as.zip bs).zip (liftAll as bs us)).all (fun ((A, B), v) => c.lies A B v) = true := by
  obtain ⟨hul, hui⟩ := sortsOf_iff.mp hu
  refine zip3_all_iff.mpr fun i h1 h2 h3 => ?_
  rw [getElem_liftAll]
  exact lies_lift (hui i (by simp [length_liftAll] at h3; omega) h1)

theorem liftAll_trans (H : OvlHyp c) {as ks bs : List Srt} {us : List GroundTerm}
    (hl1 : as.length = ks.length) (hl2 : ks.length = bs.length) (hu : us.length = as.length)
    (h1 : (as.zip ks).all (fun (A, B) => c.le A B) = true)
    (h2 : (ks.zip bs).all (fun (A, B) => c.le A B) = true) :
    liftAll ks bs (liftAll as ks us) = liftAll as bs us := by
  have h1i := zip2_all_iff.mp h1
  have h2i := zip2_all_iff.mp h2
  refine List.ext_getElem (by simp [length_liftAll]; omega) fun i hi1 hi2 => ?_
  simp only [length_liftAll] at hi1 hi2
  rw [getElem_liftAll, getElem_liftAll, getElem_liftAll]
  exact lift_trans H (h1i i (by omega) (by omega)) (h2i i (by omega) (by omega)) _

theorem stripAll_trans (H : OvlHyp c) {as ks bs : List Srt} {vs : List GroundTerm}
    (hl1 : as.length = ks.length) (hl2 : ks.length = bs.length) (hv : vs.length = bs.length)
    (h1 : (as.zip ks).all (fun (A, B) => c.le A B) = true)
    (h2 : (ks.zip bs).all (fun (A, B) => c.le A B) = true)
    (hlies : ((as.zip bs).zip vs).all (fun ((A, B), v) => c.lies A B v) = true) :
    stripAll as ks (stripAll ks bs vs) = stripAll as bs vs := by
  have h1i := zip2_all_iff.mp h1
  have h2i := zip2_all_iff.mp h2
  have hli := zip3_all_iff.mp hlies
  refine List.ext_getElem (by simp [length_stripAll]; omega) fun i hi1 hi2 => ?_
  simp only [length_stripAll] at hi1 hi2
  rw [getElem_stripAll, getElem_stripAll, getElem_stripAll]
  exact strip_trans H (h1i i (by omega) (by omega)) (h2i i (by omega) (by omega))
    (hli i (by omega) (by omega) (by omega))

theorem lies_stripAll (H : OvlHyp c) {as ks bs : List Srt} {vs : List GroundTerm}
    (hl1 : as.length = ks.length) (hl2 : ks.length = bs.length) (hv : vs.length = bs.length)
    (h1 : (as.zip ks).all (fun (A, B) => c.le A B) = true)
    (h2 : (ks.zip bs).all (fun (A, B) => c.le A B) = true)
    (hlies : ((as.zip bs).zip vs).all (fun ((A, B), v) => c.lies A B v) = true) :
    ((as.zip ks).zip (stripAll ks bs vs)).all (fun ((A, B), v) => c.lies A B v) = true := by
  have h1i := zip2_all_iff.mp h1
  have h2i := zip2_all_iff.mp h2
  have hli := zip3_all_iff.mp hlies
  refine zip3_all_iff.mpr fun i hi1 hi2 hi3 => ?_
  simp only [length_stripAll] at hi3
  rw [getElem_stripAll]
  exact lies_strip H (h1i i (by omega) (by omega)) (h2i i (by omega) (by omega))
    (hli i (by omega) (by omega) (by omega))

theorem le_all_trans (H : OvlHyp c) {as ks bs : List Srt}
    (hl1 : as.length = ks.length) (hl2 : ks.length = bs.length)
    (h1 : (as.zip ks).all (fun (A, B) => c.le A B) = true)
    (h2 : (ks.zip bs).all (fun (A, B) => c.le A B) = true) :
    (as.zip bs).all (fun (A, B) => c.le A B) = true := by
  have h1i := zip2_all_iff.mp h1
  have h2i := zip2_all_iff.mp h2
  exact zip2_all_iff.mpr fun i hi1 hi2 =>
    le_trans H (h1i i hi1 (by omega)) (h2i i (by omega) hi2)

theorem le_all_self (as : List Srt) : (as.zip as).all (fun (A, B) => c.le A B) = true :=
  zip2_all_iff.mpr fun _ _ _ => le_refl _

/-! ## The overloads' data -/

/-- The symbol's rank: one more than its place among the overloading symbols, 0 for a symbol that
is none. Each symbol an overloading symbol overloads has a smaller rank (`overloadsOK`). -/
def ovlRank (c : Semantics) (f : Sym) : Nat :=
  if c.ovls.any (·.sig.name == f) then c.ovls.findIdx (·.sig.name == f) + 1 else 0

/-- k is the signature its name has among the constructors and the overloading symbols. -/
def KnownSig (c : Semantics) (k : CtorSig) : Prop :=
  lookupSig (c.ctorSigs ++ c.ovlSigs) k.name = some k

/-- A symbol found among `L` has there the signature it has among `L` followed by more. -/
theorem lookupSig_append_of_isSome {L L' : List CtorSig} {g : Sym} (h : (lookupSig L g).isSome = true) :
    lookupSig (L ++ L') g = lookupSig L g := by
  rw [lookupSig_eq] at h
  rw [lookupSig_eq, lookupSig_eq, List.find?_append]
  cases hL : L.find? (·.name == g) with
  | none => rw [hL] at h; cases h
  | some k => rfl

/-- A known signature is no function's (`ovlByFn`). -/
theorem ovlByFn_of_known {k : CtorSig} (hk : KnownSig c k) : c.ovlByFn k = false := by
  unfold KnownSig at hk
  simp [Semantics.ovlByFn, hk]

/-- No overload of an overloading symbol is a function, in a semantics without a function-overloaded
symbol. -/
theorem noFnOvl_label {c : Semantics} (h : c.fnOvlSyms = []) {o : OvlSig} (ho : o ∈ c.ovls) {g : Sym}
    (hg : g ∈ o.over) {fn : Fn} (hfn : fn ∈ c.fns) : (fn.label == g) = false := by
  cases hb : fn.label == g with
  | false => rfl
  | true =>
    have : o.sig.name ∈ c.fnOvlSyms := List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho,
      List.any_eq_true.mpr ⟨g, hg, List.any_eq_true.mpr ⟨fn, hfn, hb⟩⟩⟩, rfl⟩
    rw [h] at this; cases this

/-- For a semantics without a function-overloaded symbol, the symbols an overloading symbol
overloads are read among the constructors and the overloading symbols. -/
theorem ovlOver_of_noFnOvl {c : Semantics} (h : c.fnOvlSyms = []) {o : OvlSig} (ho : o ∈ c.ovls) :
    c.ovlOver o = o.over.filterMap fun g => lookupSig (c.ctorSigs ++ c.ovlSigs) g := by
  unfold Semantics.ovlOver
  have hcongr : ∀ (F G : Sym → Option CtorSig) (l : List Sym), (∀ g ∈ l, F g = G g) →
      l.filterMap F = l.filterMap G := by
    intro F G l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      simp only [List.filterMap_cons, hl a (List.mem_cons_self ..), ih fun g hg => hl g (List.mem_cons_of_mem _ hg)]
  refine hcongr _ _ _ fun g hg => ?_
  cases hs : (lookupSig (c.ctorSigs ++ c.ovlSigs) g).isSome with
  | true => exact lookupSig_append_of_isSome hs
  | false =>
    rw [lookupSig_eq] at hs
    rw [lookupSig_eq, lookupSig_eq, List.find?_append]
    have hn : (c.ctorSigs ++ c.ovlSigs).find? (·.name == g) = none := by
      cases hx : (c.ctorSigs ++ c.ovlSigs).find? (·.name == g) with
      | none => rfl
      | some _ => rw [hx] at hs; cases hs
    rw [hn, Option.none_or, List.find?_eq_none]
    intro k hk
    obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hk
    simp [noFnOvl_label h ho hg hfn]

/-- For a semantics without a function-overloaded symbol, no overload's signature is a function's. -/
theorem ovlByFn_of_noFnOvl {c : Semantics} (h : c.fnOvlSyms = []) {o : OvlSig} (ho : o ∈ c.ovls)
    {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) : c.ovlByFn kg = false := by
  rw [ovlOver_of_noFnOvl h ho] at hkg
  obtain ⟨g, -, hgk⟩ := List.mem_filterMap.mp hkg
  have hkn : kg.name = g := by
    rw [lookupSig_eq] at hgk
    simpa using List.find?_some hgk
  simp [Semantics.ovlByFn, hkn, hgk]

/-- For a semantics without a function-overloaded symbol, one step of `normN` is the first covering
overload's normal form at the stripped arguments, lifted, whichever symbol it is of. -/
theorem normN_succ_of_noFnOvl {c : Semantics} (h : c.fnOvlSyms = []) (n : Nat) (f : Sym) (vs : List GroundTerm) :
    c.normN (n + 1) f vs = match c.lookupOvl f with
      | none => .ctor f vs
      | some o => match (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
        | none => .ctor f vs
        | some kg => lift kg.result o.sig.result (c.normN n kg.name (stripAll kg.args o.sig.args vs)) := by
  cases ho : c.lookupOvl f with
  | none => simp only [Semantics.normN, ho]
  | some o =>
    cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
    | none => simp only [Semantics.normN, ho, hf]
    | some kg =>
      simp only [Semantics.normN, ho, hf,
        ovlByFn_of_noFnOvl h (List.mem_of_find?_eq_some ho) (List.mem_of_find?_eq_some hf),
        Bool.false_eq_true, ↓reduceIte]

theorem ovlRank_le (f : Sym) : ovlRank c f ≤ c.ovls.length := by
  unfold ovlRank
  split
  · rename_i h
    have := List.findIdx_lt_length_of_exists (p := (·.sig.name == f)) (xs := c.ovls)
      (by simpa using h)
    omega
  · omega

theorem lookupOvl_spec {f : Sym} {o : OvlSig} (h : c.lookupOvl f = some o) :
    o.sig.name = f ∧ ∃ (i : Nat) (hi : i < c.ovls.length), c.ovls[i] = o ∧ ovlRank c f = i + 1 := by
  unfold Semantics.lookupOvl at h
  obtain ⟨hp, i, hi, he, hj⟩ := List.find?_eq_some_iff_getElem.mp h
  have hn : o.sig.name = f := by simpa using hp
  refine ⟨hn, i, hi, he, ?_⟩
  have hany : c.ovls.any (·.sig.name == f) = true := List.any_eq_true.mpr ⟨o, he ▸ List.getElem_mem hi, hp⟩
  have hidx : c.ovls.findIdx (·.sig.name == f) = i := by
    rw [List.findIdx_eq hi]
    exact ⟨he ▸ hp, fun j hj' => by simpa using hj j hj'⟩
  simp [ovlRank, hany, hidx]

theorem lookupOvl_none_of_rank {f : Sym} (h : ovlRank c f = 0) : c.lookupOvl f = none := by
  cases ho : c.lookupOvl f with
  | none => rfl
  | some o => obtain ⟨-, _, -, -, hr⟩ := lookupOvl_spec ho; omega

theorem rank_of_take {f g : Sym} {i : Nat} (hr : ovlRank c f = i + 1) (ht : (c.ovls.take i).any (·.sig.name == g) = true) :
    ovlRank c g < ovlRank c f := by
  obtain ⟨o', hm, hp⟩ := List.any_eq_true.mp ht
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hm
  simp only [List.length_take] at hj
  have hjo : c.ovls[j]'(by omega) = o' := by simpa [List.getElem_take] using hje
  have hany : c.ovls.any (·.sig.name == g) = true :=
    List.any_eq_true.mpr ⟨o', hjo ▸ List.getElem_mem _, hp⟩
  have hle : c.ovls.findIdx (·.sig.name == g) ≤ j := by
    apply Nat.le_of_not_lt
    intro hlt
    exact absurd (hjo ▸ hp) (by simpa using List.not_of_lt_findIdx hlt)
  have hrg : ovlRank c g = c.ovls.findIdx (·.sig.name == g) + 1 := by simp [ovlRank, hany]
  rw [hrg, hr]
  omega

theorem find_ovlSigs (f : Sym) : c.ovlSigs.find? (·.name == f) = (c.lookupOvl f).map (·.sig) := by
  simp [Semantics.ovlSigs, Semantics.lookupOvl, List.find?_map, Function.comp_def]

/-- No function overload covers anything in a semantics without an overloading symbol. -/
theorem fnCover_none_of_nil (h : c.ovls = []) (f : Sym) (vs : List GroundTerm) : c.fnCover f vs = none :=
  c.fnCover_of_lookupOvl_none (by simp [Semantics.lookupOvl, h]) vs

/-- No function overload covers anything in a semantics without a function-overloaded symbol. -/
theorem fnCover_none_of_noFnOvl (h : c.fnOvlSyms = []) (f : Sym) (vs : List GroundTerm) :
    c.fnCover f vs = none :=
  c.fnCover_none_of_noByFn (fun _ ho _ hkg => ovlByFn_of_noFnOvl h ho hkg) f vs

section
variable (H : OvlHyp c)
include H

/-- A known signature is a constructor's, which is no overloading symbol, or an overloading
symbol's. -/
theorem knownSig_cases {k : CtorSig} (hk : KnownSig c k) :
    (lookupSig c.ctorSigs k.name = some k ∧ c.lookupOvl k.name = none) ∨
      (lookupSig c.ctorSigs k.name = none ∧ ∃ o, c.lookupOvl k.name = some o ∧ o.sig = k) := by
  unfold KnownSig at hk
  rw [lookupSig_eq, List.find?_append] at hk
  cases hc : c.ctorSigs.find? (·.name == k.name) with
  | some k' =>
    rw [hc, Option.some_or] at hk
    cases hk
    refine .inl ⟨by rw [lookupSig_eq, hc], ?_⟩
    cases ho : c.lookupOvl k.name with
    | none => rfl
    | some o =>
      obtain ⟨hn, i, hi, he, -⟩ := lookupOvl_spec ho
      have hok := H.ok
      simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
      have := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
      simp only [Bool.and_eq_true] at this
      have hio := this.1.1.1.1.1.1.1.1
      rw [hn] at hio
      have := (c.isOvl_parts hio).1
      simp [Semantics.isCtor, lookupSig_eq, hc] at this
  | none =>
    rw [hc, Option.none_or, find_ovlSigs] at hk
    cases ho : c.lookupOvl k.name with
    | none => rw [ho] at hk; cases hk
    | some o =>
      rw [ho] at hk; cases hk
      exact .inr ⟨by rw [lookupSig_eq, hc], o, rfl, rfl⟩

end

/-- An overloading symbol's declaration is the one its name finds. -/
theorem lookupOvl_of_mem (H : OvlHyp c) {o : OvlSig} (ho : o ∈ c.ovls) : c.lookupOvl o.sig.name = some o := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem ho
  have hok := H.ok
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, beq_iff_eq] at hoi
  exact hoi.1.1.1.1.1.1.1.2

/-- An overloading symbol's result sort is a constructor sort. -/
theorem ovl_result_cons (H : OvlHyp c) {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) :
    o.sig.result ∈ Faithful.consSorts c := by
  obtain ⟨-, i, hi, he, -⟩ := lookupOvl_spec ho
  have hok := H.ok
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true] at hoi
  exact List.contains_iff_mem.mp hoi.1.1.1.1.1.2

/-- What `overloadsOK` alone gives of an overloading symbol's declaration: it is one of the list,
an overloading symbol of no other kind, whose name the decoder reads as no instance, of a
constructor sort. -/
theorem ovl_parts {f : Sym} {o : OvlSig} (hok : c.overloadsOK = true) (ho : c.lookupOvl f = some o) :
    o ∈ c.ovls ∧ o.sig.name = f ∧ c.isOvl f = true ∧ instDecode? (c.symName f) = none ∧
      o.sig.result ∈ Faithful.consSorts c := by
  obtain ⟨hn, i, hi, he, -⟩ := lookupOvl_spec ho
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hoi
  refine ⟨he ▸ List.getElem_mem hi, hn, ?_, ?_, List.contains_iff_mem.mp hoi.1.1.1.1.1.2⟩
  · rw [← hn]; exact hoi.1.1.1.1.1.1.1.1
  · rw [← hn]; exact hoi.1.1.1.1.1.1.2

/-- What `overloadsOK` gives of an overloading symbol's name: the decoder reads it as no instance. -/
theorem ovl_noInst_irs {f : Sym} {o : OvlSig} (hok : c.overloadsOK = true) (ho : c.lookupOvl f = some o) :
    instDecode? (c.symName f) = none := by
  obtain ⟨hn, i, hi, he, -⟩ := lookupOvl_spec ho
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hoi
  rw [← hn]; exact hoi.1.1.1.1.1.1.2

/-- A constructor is no overloading symbol (`overloadsOK`: an overloading symbol is of no other
kind). -/
theorem lookupOvl_none_of_ctor (H : OvlHyp c) {k : CtorSig} (hk : k ∈ c.ctorSigs) :
    c.lookupOvl k.name = none := by
  cases ho : c.lookupOvl k.name with
  | none => rfl
  | some o =>
    have hct := (c.isOvl_parts (ovl_parts H.ok ho).2.2.1).1
    rw [Semantics.isCtor, lookupSig_eq] at hct
    have hnone : c.ctorSigs.find? (·.name == k.name) = none := by simpa using hct
    exact absurd (List.find?_eq_none.mp hnone k hk) (by simp)

/-- **What `overloadsOK` says of the overloading symbol listed at place `i`**: it is an overloading
symbol of no other kind, found by its name; each symbol it overloads is a constructor, an
overloading symbol listed before place `i`, or a function of the definition, with argument and
result sorts at most its own; any two of its overloads agree; and it lists every function among
the symbols it reaches along the overloads. -/
theorem ovl_leaves_fad (hok : c.overloadsOK = true) {o : OvlSig} {i : Nat} (hi : c.ovls[i]? = some o) :
    c.isOvl o.sig.name = true ∧ c.lookupOvl o.sig.name = some o ∧
      (∀ g ∈ o.over, (lookupSig c.ctorSigs g).isSome = true ∨ (c.ovls.take i).any (·.sig.name == g) = true ∨
        c.fns.any (·.label == g) = true) ∧
      (∀ kg ∈ c.ovlOver o, c.ovlPairOK o kg = true) ∧
      (∀ k1 ∈ c.ovlOver o, ∀ k2 ∈ c.ovlOver o, c.ovlCoherent k1 k2 = true) ∧
      (∀ g ∈ c.ovlClosure o.sig.name, c.fns.any (·.label == g) = true → g ∈ o.over) := by
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (List.mem_zipIdx_iff_getElem?.mpr hi)
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true] at hoi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, -⟩, h7⟩, h8⟩, h9⟩ := hoi
  refine ⟨h1, h2, fun g hg => or_assoc.mp (h5 g hg), h7, h8, fun g hg hf => ?_⟩
  rcases h9 g hg with h | h
  · rw [hf] at h; cases h
  · exact List.contains_iff_mem.mp h

theorem ovlReach_head (m : Nat) (f : Sym) : f ∈ c.ovlReach m f := by
  cases m <;> simp [Semantics.ovlReach]

/-- A symbol reached in two steps along the overloads is in the closure. -/
theorem ovlClosure_over2_fad {f g g' : Sym} {o o' : OvlSig} (hm : o ∈ c.ovls) (ho : c.lookupOvl f = some o)
    (hg : g ∈ o.over) (ho' : c.lookupOvl g = some o') (hg' : g' ∈ o'.over) : g' ∈ c.ovlClosure f := by
  obtain ⟨n, hn⟩ : ∃ n, c.ovls.length = n + 1 :=
    ⟨c.ovls.length - 1, by have := List.length_pos_of_mem hm; omega⟩
  have h1 : c.ovlReach (n + 1 + 1) f = f :: o.over.flatMap (c.ovlReach (n + 1)) := by
    rw [Semantics.ovlReach, ho]
  have h2 : c.ovlReach (n + 1) g = g :: o'.over.flatMap (c.ovlReach n) := by
    rw [Semantics.ovlReach, ho']
  unfold Semantics.ovlClosure
  rw [hn, h1]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, ?_⟩)
  rw [h2]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g', hg', ovlReach_head _ g'⟩)

theorem rank_of_none {f : Sym} (h : c.lookupOvl f = none) : ovlRank c f = 0 := by
  unfold Semantics.lookupOvl at h
  have : c.ovls.any (·.sig.name == f) = false := by
    rw [List.any_eq_false]
    intro o ho hp
    exact List.find?_eq_none.mp h o ho hp
  simp [ovlRank, this]

theorem pairOK_parts {o : OvlSig} {kg : CtorSig} (h : c.ovlPairOK o kg = true) :
    kg.args.length = o.sig.args.length ∧ (kg.args.zip o.sig.args).all (fun (A, B) => c.le A B) = true ∧
      c.le kg.result o.sig.result = true := by
  simp only [Semantics.ovlPairOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem covers_iff {kf kg : CtorSig} {vs : List GroundTerm} :
    c.ovlCovers kf kg vs = true ↔ kg.args.length = kf.args.length ∧ vs.length = kf.args.length ∧
      ((kg.args.zip kf.args).zip vs).all (fun ((A, B), v) => c.lies A B v) = true := by
  simp only [Semantics.ovlCovers, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Arguments that no overload covers. -/
theorem uncovered_of_find_none {f : Sym} {o : OvlSig} {vs : List GroundTerm} (ho : c.lookupOvl f = some o)
    (hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) = none) : c.uncovered f vs = true := by
  simp only [Semantics.uncovered, ho, List.all_eq_true, Bool.not_eq_true']
  intro kg hkg
  simpa using List.find?_eq_none.mp hf kg hkg

theorem covered_of_mem {f : Sym} {o : OvlSig} {vs : List GroundTerm} {kg : CtorSig} (ho : c.lookupOvl f = some o)
    (hkg : kg ∈ c.ovlOver o) (hc : c.ovlCovers o.sig kg vs = true) : c.uncovered f vs = false := by
  simp only [Semantics.uncovered, ho, List.all_eq_false, Bool.not_eq_true', Bool.not_eq_false]
  exact ⟨kg, hkg, by simpa using hc⟩

theorem uncovered_of_none {f : Sym} (h : c.lookupOvl f = none) (vs : List GroundTerm) :
    c.uncovered f vs = true := by
  simp [Semantics.uncovered, h]

theorem mem_ovlOver {o : OvlSig} {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) : kg.name ∈ o.over := by
  obtain ⟨g, hg, hgk⟩ := List.mem_filterMap.mp hkg
  rw [lookupSig_eq] at hgk
  have : kg.name = g := by simpa using List.find?_some hgk
  rw [this]; exact hg

/-- A known signature is a constructor's or an overloading symbol's. -/
theorem knownSig_mem {k : CtorSig} (hk : KnownSig c k) : k ∈ c.ctorSigs ∨ k ∈ c.ovlSigs := by
  unfold KnownSig at hk
  rw [lookupSig_eq] at hk
  exact List.mem_append.mp (List.mem_of_find?_eq_some hk)

/-! ## Unfolding `norm` -/

theorem normN_none {f : Sym} (h : c.lookupOvl f = none) (n : Nat) (vs : List GroundTerm) :
    c.normN n f vs = .ctor f vs := by
  cases n <;> simp [Semantics.normN, h]

/-- A symbol that is no overloading symbol denotes its raw application. -/
theorem norm_none {f : Sym} (h : c.lookupOvl f = none) (vs : List GroundTerm) :
    c.norm f vs = .ctor f vs :=
  normN_none h _ _

section
variable (H : OvlHyp c)
include H

omit H in
theorem norm_find_none {f : Sym} {o : OvlSig} {vs : List GroundTerm} (ho : c.lookupOvl f = some o)
    (hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) = none) : c.norm f vs = .ctor f vs := by
  simp [Semantics.norm, Semantics.normN, ho, hf]

/-! ## Values -/

theorem known_ctor_parts {k : CtorSig} (hk : KnownSig c k) (hn : c.lookupOvl k.name = none) :
    lookupSig c.ctorSigs k.name = some k := by
  rcases knownSig_cases H hk with ⟨hc, -⟩ | ⟨-, o, ho, -⟩
  · exact hc
  · rw [hn] at ho; cases ho

/-! ## Coherence -/

/-- A value lying in two sorts lies in each sort above a common lower sort of the two that the
value's position names: its injection's source, or its own sort. -/
theorem pos_lower {A1 A2 B : Srt} {v : GroundTerm} (hv : c.sortOf v = some B) (h1 : c.lies A1 B v = true)
    (h2 : c.lies A2 B v = true) :
    ∃ C, C ∈ (A1 :: A2 :: c.subsorts.map (·.1)).filter (fun C => c.le C A1 && c.le C A2) ∧
      ∀ X, c.le X B = true → c.le C X = true → c.lies X B v = true := by
  cases v with
  | inj C B' w =>
    obtain ⟨hCB, -, -, rfl⟩ := sortOf_inj_iff.mp hv
    have hle : ∀ A, c.lies A B (.inj C B w) = true → c.le C A = true := by
      intro A hA
      simp only [Semantics.lies, Bool.or_eq_true, beq_iff_eq] at hA
      rcases hA with rfl | hA
      · exact le_of_mem hCB
      · exact hA
    refine ⟨C, List.mem_filter.mpr ⟨?_, by simp [hle A1 h1, hle A2 h2]⟩,
      fun X _ hX => by simp [Semantics.lies, hX]⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(C, B), hCB, rfl⟩))
  | _ =>
    simp only [Semantics.lies, beq_iff_eq] at h1 h2
    have hB : (c.le B A1 && c.le B A2) = true := by
      rw [h1, h2, OvlLaws.le_refl]; rfl
    refine ⟨B, List.mem_filter.mpr ⟨List.mem_cons.mpr (.inl h1.symm), hB⟩, fun X hXB hBX => ?_⟩
    rw [le_antisymm H hXB hBX]
    exact lies_self _ _

/-! ## Normal forms -/

omit H in
theorem knownSig_inj {h h' : CtorSig} (hh : KnownSig c h) (hh' : KnownSig c h') (he : h.name = h'.name) :
    h = h' := by
  unfold KnownSig at hh hh'
  rw [he, hh'] at hh
  exact (Option.some.inj hh).symm

omit H in
/-- A lifted raw application determines its symbol and arguments. -/
theorem lift_ctor_inj {A A' B : Srt} {f f' : Sym} {us us' : List GroundTerm}
    (he : lift A B (.ctor f us) = lift A' B (.ctor f' us')) : f = f' ∧ us = us' := by
  by_cases h1 : A = B <;> by_cases h2 : A' = B
  · subst h1 h2; simpa [lift_self] using he
  · subst h1; simp [lift_self, lift_ne h2, injNormal] at he
  · subst h2; simp [lift_self, lift_ne h1, injNormal] at he
  · simp only [lift_ne h1, lift_ne h2, injNormal, GroundTerm.inj.injEq, GroundTerm.ctor.injEq] at he
    exact he.2.2

end

end OvlLaws

/-- **A function-overloaded symbol has a function's signature among its overloads**, where the
overloading symbols are well formed (`overloadsOK`: each is found by its name and is no function's
label) and no function is named like a constructor (`fnsApart`): the function's label an overload
names is then neither a constructor nor an overloading symbol, so the signature `ovlOver` finds for
it is the function's. -/
theorem fnOver_of_apart {c : Semantics} (hok : c.overloadsOK = true)
    (hfa : Faithful.Model.fnsApart c = true) :
    ∀ o ∈ c.ovls, o.sig.name ∈ c.fnOvlSyms → ∃ kg ∈ c.ovlOver o, c.ovlByFn kg = true := by
  intro o ho hm
  have hok' := hok
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok'; replace hok' := hok'.1; simp only [List.all_eq_true] at hok'
  have hat : ∀ o' ∈ c.ovls, c.isOvl o'.sig.name = true ∧ c.lookupOvl o'.sig.name = some o' := fun o' ho' => by
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem ho'
    have hoi := hok' (o', i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
    simp only [Bool.and_eq_true, beq_iff_eq] at hoi
    exact ⟨hoi.1.1.1.1.1.1.1.1, hoi.1.1.1.1.1.1.1.2⟩
  unfold Semantics.fnOvlSyms at hm
  obtain ⟨o', ho', hn⟩ := List.mem_map.mp hm
  obtain ⟨ho'm, hany⟩ := List.mem_filter.mp ho'
  have heq : o' = o := by
    have h1 := (hat o' ho'm).2
    rw [hn, (hat o ho).2] at h1
    exact (Option.some.inj h1).symm
  subst heq
  obtain ⟨g, hg, hfn⟩ := List.any_eq_true.mp hany
  obtain ⟨fn, hfnm, hl⟩ := List.any_eq_true.mp hfn
  have hl : fn.label = g := by simpa using hl
  have hmem : fn ∈ c.allFns := List.mem_append_left _ hfnm
  have hc : c.ctorSigs.find? (·.name == g) = none := by
    have := List.all_eq_true.mp hfa fn hmem
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    have hc := this.1.1
    rw [hl, Semantics.isCtor, lookupSig_eq] at hc
    simpa using hc
  have hov : c.ovlSigs.find? (·.name == g) = none := by
    rw [List.find?_eq_none]
    intro k hk hkn
    obtain ⟨o2, ho2, rfl⟩ := List.mem_map.mp hk
    have hnf := (c.isOvl_parts (hat o2 ho2).1).2.2.2.1
    rw [c.lookupFn_eq, List.find?_eq_none] at hnf
    have := hnf fn hmem
    rw [hl, beq_iff_eq.mp hkn] at this
    simp at this
  obtain ⟨kg, hkg, hkn⟩ : ∃ kg, (c.fns.map fun fn => (⟨fn.label, fn.args, fn.result⟩ : CtorSig)).find? (·.name == g) = some kg ∧
      kg.name = g := by
    cases hf : (c.fns.map fun fn => (⟨fn.label, fn.args, fn.result⟩ : CtorSig)).find? (·.name == g) with
    | none =>
      have := List.find?_eq_none.mp hf ⟨fn.label, fn.args, fn.result⟩ (List.mem_map.mpr ⟨fn, hfnm, rfl⟩)
      simp [hl] at this
    | some kg => exact ⟨kg, rfl, by simpa using List.find?_some hf⟩
  refine ⟨kg, List.mem_filterMap.mpr ⟨g, hg, ?_⟩, ?_⟩
  · rw [lookupSig_eq, List.find?_append, List.find?_append, hc, hov]
    exact hkg
  · simp only [Semantics.ovlByFn, Option.isNone_iff_eq_none]
    rw [hkn, lookupSig_eq, List.find?_append, hc, hov]
    rfl

/-- **What the readings of `Γ` over every model take of the overloading symbols**: their
declarations are well formed (`overloadsOK`), the subsorts are irreflexive, a sort of an
overloading symbol and a sort of a symbol it overloads have distinct names unless they are one sort,
so that the overload's items tell them apart (`namesApartK` and `sortsNumbered` give it), and a
function-overloaded symbol (`fnOvlSyms`, which reads the functions' labels) has a function's
signature among its overloads (`ovlByFn`, which reads the signature `ovlOver` finds; `overloadsOK`
and `fnsApart` give it). Found by instance resolution in the proofs that read `Γ`. -/
class OvlOK (c : Semantics) : Prop where
  ok : c.overloadsOK = true
  irrefl : ∀ a, (a, a) ∉ c.subsorts
  names : ∀ o ∈ c.ovls, ∀ kg ∈ c.ovlOver o, ∀ A ∈ kg.result :: kg.args, ∀ B ∈ o.sig.result :: o.sig.args,
    c.sortName A = c.sortName B → A = B
  fnOver : ∀ o ∈ c.ovls, o.sig.name ∈ c.fnOvlSyms → ∃ kg ∈ c.ovlOver o, c.ovlByFn kg = true

/-- `OvlOK` of a semantics without overloading symbols and with irreflexive subsorts. -/
theorem OvlOK.of_nil {c : Semantics} (hno : c.ovls = []) (hirr : c.subsorts.all (fun p => p.1 != p.2) = true) :
    OvlOK c :=
  ⟨by simp [Semantics.overloadsOK, Semantics.ovlPatsOK, Semantics.fnOvlSyms, hno], fun a ha => by have := List.all_eq_true.mp hirr _ ha; simp at this,
    fun o ho => (by rw [hno] at ho; cases ho), fun o ho => (by rw [hno] at ho; cases ho)⟩

/-- `idsOK` numbers each overloading symbol once: their names are without repetition. -/
theorem ovlsOnce_of_ids {c : Semantics} (h : c.idsOK = true) : (c.ovls.map (·.sig.name)).Nodup := by
  unfold Semantics.idsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have he : c.ownSyms = _ := h.1.1.2
  have hnd : c.ownSyms.Nodup := by rw [he]; exact List.nodup_range' ..
  unfold Semantics.ownSyms at hnd
  exact (List.nodup_append.mp hnd).2.1

/-- `OvlHyp` from `OvlOK` and transitive subsorts. -/
theorem OvlOK.hyp {c : Semantics} (h : OvlOK c)
    (htr : ∀ a b e, (a, b) ∈ c.subsorts → (b, e) ∈ c.subsorts → (a, e) ∈ c.subsorts) : OvlLaws.OvlHyp c :=
  ⟨h.ok, htr, h.irrefl⟩

/-- Irreflexive subsorts, decided pair by pair. -/
theorem irrefl_of_all {c : Semantics} (h : c.subsorts.all (fun p => p.1 != p.2) = true) :
    ∀ a, (a, a) ∉ c.subsorts := fun a ha => by
  have := List.all_eq_true.mp h _ ha
  simp at this

end KCore
