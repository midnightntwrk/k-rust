/-
  The laws of the overloading symbols' normal forms (`Semantics.norm`, Value.lean), over a
  semantics whose overloading symbols are well formed (`overloadsOK`) and whose subsorts are
  transitive and irreflexive (`OvlHyp`):

  - `norm` does not depend on the fuel past the symbol's rank (its place in `ovls`, `ovlRank`), so
    it unfolds by one overload step (`norm_find_none`, `norm_find_some`);
  - a normal form is a value of the symbol's result sort (`sortOf_norm`);
  - **coherence**: every overload covering the arguments gives the same value
    (`norm_coherent`), hence each overload equation `f(lift ā) = lift (g(ā))` (`norm_ovlEq`);
  - a normal form is the lift of a raw application `h(ū)` of a symbol h at most f along the
    overloads, whose arguments lift to f's (`norm_decomp`); so `norm f` is injective on argument
    lists of f's sorts (`norm_inj`), and `norm f v̄ = f(v̄)` exactly when v̄ is uncovered
    (`norm_eq_raw_iff`), in particular for a value `f(v̄)` (`norm_fixed`).
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

/-- Under `overloadsOK` a signature among the symbols an overloading symbol overloads is the one its
name has among the constructors and the overloading symbols. -/
theorem ovlOver_known_of_ok (hok : c.overloadsOK = true) {f : Sym} {o : OvlSig}
    (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) : KnownSig c kg := by
  obtain ⟨-, i, hi, he, -⟩ := lookupOvl_spec ho
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, List.all_eq_true] at hoi
  obtain ⟨g, hg, hgk⟩ := List.mem_filterMap.mp hkg
  have hfound : (lookupSig (c.ctorSigs ++ c.ovlSigs) g).isSome = true := by
    rcases Bool.or_eq_true _ _ |>.mp (hoi.1.1.1.2 g hg) with h1 | h2
    · rw [lookupSig_append_of_isSome h1]; exact h1
    · obtain ⟨o', ho', hn'⟩ := List.any_eq_true.mp h2
      rw [lookupSig_eq, List.find?_isSome]
      exact ⟨o'.sig, List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_mem_take ho')), hn'⟩
  rw [lookupSig_append_of_isSome hfound] at hgk
  have hkn : kg.name = g := by
    rw [lookupSig_eq] at hgk
    simpa using List.find?_some hgk
  unfold KnownSig; rw [hkn]; exact hgk

/-- No function overload covers anything where the overloading symbols are well formed
(`overloadsOK`): each overloaded symbol is a constructor or an overloading symbol. -/
theorem fnCover_none_of_ok (hok : c.overloadsOK = true) (f : Sym) (vs : List GroundTerm) :
    c.fnCover f vs = none := by
  rw [Semantics.fnCover_eq_none_iff]
  intro o ho kg hkg hb
  rw [ovlByFn_of_known (ovlOver_known_of_ok hok ho hkg)] at hb
  cases hb

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
      have hio := this.1.1.1.1.1.1.1
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

/-- A symbol an overloading symbol overloads is a constructor or an overloading symbol
(`overloadsOK`), and `ovlOver` holds its signature among those. -/
theorem ovlOver_known {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig}
    (hkg : kg ∈ c.ovlOver o) : KnownSig c kg := ovlOver_known_of_ok H.ok ho hkg

/-- What `overloadsOK` gives of an overloading symbol's declaration. -/
theorem ovl_facts {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) :
    o.sig.name = f ∧ c.isOvl f = true ∧ lookupSig c.ctorSigs f = none ∧ KnownSig c o.sig ∧
      0 < ovlRank c f ∧
      (∀ kg ∈ c.ovlOver o, KnownSig c kg ∧ c.ovlPairOK o kg = true ∧
        (c.lookupOvl kg.name = none ∨ ovlRank c kg.name < ovlRank c f)) ∧
      (∀ k1 ∈ c.ovlOver o, ∀ k2 ∈ c.ovlOver o, c.ovlCoherent k1 k2 = true) := by
  obtain ⟨hn, i, hi, he, hr⟩ := lookupOvl_spec ho
  have hok := H.ok
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, List.all_eq_true] at hoi
  obtain ⟨⟨⟨⟨⟨⟨⟨hio, -⟩, -⟩, -⟩, hover⟩, -⟩, hpair⟩, hcoh⟩ := hoi
  rw [hn] at hio
  have hct : lookupSig c.ctorSigs f = none := by
    have := (c.isOvl_parts hio).1
    simpa [Semantics.isCtor] using this
  have hks : KnownSig c o.sig := by
    unfold KnownSig
    rw [hn, lookupSig_eq, List.find?_append, ← lookupSig_eq, hct, Option.none_or, find_ovlSigs, ho]
    rfl
  refine ⟨hn, hio, hct, hks, by omega, fun kg hkg => ?_, hcoh⟩
  obtain ⟨g, hg, hgk⟩ := List.mem_filterMap.mp hkg
  have hkn : kg.name = g := by
    rw [lookupSig_eq] at hgk
    simpa using List.find?_some hgk
  have hkk : KnownSig c kg := ovlOver_known H ho hkg
  refine ⟨hkk, hpair kg hkg, ?_⟩
  rcases knownSig_cases H hkk with ⟨-, hn'⟩ | ⟨hc', -⟩
  · exact .inl hn'
  · have := hover g hg
    rw [Bool.or_eq_true, ← hkn, hc'] at this
    exact .inr (rank_of_take hr (this.resolve_left (by simp)))

end

/-- An overloading symbol's declaration is the one its name finds. -/
theorem lookupOvl_of_mem (H : OvlHyp c) {o : OvlSig} (ho : o ∈ c.ovls) : c.lookupOvl o.sig.name = some o := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem ho
  have hok := H.ok
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, beq_iff_eq] at hoi
  exact hoi.1.1.1.1.1.1.2

/-- An overloading symbol's result sort is a constructor sort. -/
theorem ovl_result_cons (H : OvlHyp c) {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) :
    o.sig.result ∈ Faithful.consSorts c := by
  obtain ⟨-, i, hi, he, -⟩ := lookupOvl_spec ho
  have hok := H.ok
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true] at hoi
  exact List.contains_iff_mem.mp hoi.1.1.1.1.2

/-- What `overloadsOK` alone gives of an overloading symbol's declaration: it is one of the list,
an overloading symbol of no other kind, named plainly (not like `ite` at a sort), of a constructor
sort. -/
theorem ovl_parts {f : Sym} {o : OvlSig} (hok : c.overloadsOK = true) (ho : c.lookupOvl f = some o) :
    o ∈ c.ovls ∧ o.sig.name = f ∧ c.isOvl f = true ∧ iteSort? (c.symName f) = none ∧
      o.sig.result ∈ Faithful.consSorts c := by
  obtain ⟨hn, i, hi, he, -⟩ := lookupOvl_spec ho
  simp only [Semantics.overloadsOK, Bool.and_eq_true] at hok; replace hok := hok.1; simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi] using he)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hoi
  refine ⟨he ▸ List.getElem_mem hi, hn, ?_, ?_, List.contains_iff_mem.mp hoi.1.1.1.1.2⟩
  · rw [← hn]; exact hoi.1.1.1.1.1.1.1
  · rw [← hn]; exact hoi.1.1.1.1.1.2

/-- A constructor is no overloading symbol. -/
theorem lookupOvl_none_of_ctor (H : OvlHyp c) {k : CtorSig} (hk : k ∈ c.ctorSigs) :
    c.lookupOvl k.name = none := by
  cases ho : c.lookupOvl k.name with
  | none => rfl
  | some o =>
    obtain ⟨-, -, hct, -⟩ := ovl_facts H ho
    rw [lookupSig_eq] at hct
    exact absurd (List.find?_eq_none.mp hct k hk) (by simp)

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

theorem ovlReach_head (m : Nat) (f : Sym) : f ∈ c.ovlReach m f := by
  cases m <;> simp [Semantics.ovlReach]

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

/-- `normN` is stable from the symbol's rank on. -/
theorem normN_stable : ∀ n f, ovlRank c f ≤ n → ∀ m, n ≤ m → ∀ vs, c.normN m f vs = c.normN n f vs
  | 0, f, hr, m, _, vs => by
    have hn := lookupOvl_none_of_rank (c := c) (f := f) (by omega)
    rw [normN_none hn, normN_none hn]
  | n + 1, f, hr, m, hm, vs => by
    cases ho : c.lookupOvl f with
    | none => rw [normN_none ho, normN_none ho]
    | some o =>
      obtain ⟨-, -, -, -, hpos, hover, -⟩ := ovl_facts H ho
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none => simp only [Semantics.normN, ho, hf]
      | some kg =>
        obtain ⟨hkk, -, hr'⟩ := hover kg (List.mem_of_find?_eq_some hf)
        simp only [Semantics.normN, ho, hf, ovlByFn_of_known hkk, Bool.false_eq_true, ↓reduceIte]
        have hrk : ovlRank c kg.name ≤ n := by
          rcases hr' with h | h
          · rw [rank_of_none h]; omega
          · omega
        rw [normN_stable n kg.name hrk m (by omega)]

omit H in
theorem norm_find_none {f : Sym} {o : OvlSig} {vs : List GroundTerm} (ho : c.lookupOvl f = some o)
    (hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) = none) : c.norm f vs = .ctor f vs := by
  simp [Semantics.norm, Semantics.normN, ho, hf]

/-- **One overload step**: where the first overload covering the arguments is that of kg, f's
normal form is kg's at the stripped arguments, lifted. -/
theorem norm_find_some {f : Sym} {o : OvlSig} {vs : List GroundTerm} {kg : CtorSig} (ho : c.lookupOvl f = some o)
    (hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) = some kg) :
    c.norm f vs = lift kg.result o.sig.result (c.norm kg.name (stripAll kg.args o.sig.args vs)) := by
  have hr := ovlRank_le (c := c) kg.name
  have e1 : ∀ xs, c.normN c.ovls.length kg.name xs = c.norm kg.name xs := by
    intro xs
    unfold Semantics.norm
    rw [normN_stable H _ _ (Nat.le_refl _) c.ovls.length hr,
      normN_stable H _ _ (Nat.le_refl _) (c.ovls.length + 1) (by omega)]
  unfold Semantics.norm
  simp only [Semantics.normN, ho, hf, ovlByFn_of_known (ovlOver_known H ho (List.mem_of_find?_eq_some hf)),
    Bool.false_eq_true, ↓reduceIte]
  rw [e1]
  rfl

/-! ## Values -/

theorem known_ctor_parts {k : CtorSig} (hk : KnownSig c k) (hn : c.lookupOvl k.name = none) :
    lookupSig c.ctorSigs k.name = some k := by
  rcases knownSig_cases H hk with ⟨hc, -⟩ | ⟨-, o, ho, -⟩
  · exact hc
  · rw [hn] at ho; cases ho

/-- **A normal form is a value** of the symbol's result sort. -/
theorem sortOf_norm_known : ∀ n k, KnownSig c k → ovlRank c k.name ≤ n → ∀ vs,
    c.sortsOf vs = some k.args → c.sortOf (c.norm k.name vs) = some k.result
  | n, k, hk, hr, vs, hvs => by
    cases hn : c.lookupOvl k.name with
    | none =>
      rw [norm_none hn]
      exact c.sortOf_ctor_iff.mpr (.inl ⟨k, known_ctor_parts H hk hn, hvs, rfl⟩)
    | some o =>
      rcases knownSig_cases H hk with ⟨-, hn'⟩ | ⟨hct, o', ho', hos⟩
      · rw [hn'] at hn; cases hn
      rw [hn] at ho'; cases ho'; subst hos
      obtain ⟨-, -, -, -, hpos, hover, -⟩ := ovl_facts H hn
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none =>
        rw [norm_find_none hn hf]
        exact c.sortOf_ctor_iff.mpr (.inr (.inl ⟨hct, o, hn, hvs, uncovered_of_find_none hn hf, rfl⟩))
      | some kg =>
        rw [norm_find_some H hn hf]
        have hkg := List.mem_of_find?_eq_some hf
        have hcv := List.find?_some hf
        obtain ⟨hkk, hpair, hr'⟩ := hover kg hkg
        obtain ⟨hl, hle, hres⟩ := pairOK_parts hpair
        obtain ⟨-, -, hlies⟩ := covers_iff.mp hcv
        match n with
        | 0 => omega
        | n + 1 =>
          have hrk : ovlRank c kg.name ≤ n := by
            rcases hr' with h | h
            · rw [rank_of_none h]; omega
            · omega
          exact sortOf_lift H (sortOf_norm_known n kg hkk hrk _ (sortsOf_stripAll hl hvs hlies)) hres

theorem sortOf_norm {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) : c.sortOf (c.norm f vs) = some o.sig.result := by
  obtain ⟨hn, -, -, hks, -⟩ := ovl_facts H ho
  have := sortOf_norm_known H _ o.sig hks (ovlRank_le _) vs hvs
  rwa [hn] at this

/-! ## Coherence -/

/-- A symbol of `ovlDown k`: k, or one that k overloads. -/
theorem down_parts {k h : CtorSig} (hk : KnownSig c k) (hh : h ∈ c.ovlDown k) :
    KnownSig c h ∧ h.args.length = k.args.length ∧ (h.args.zip k.args).all (fun (A, B) => c.le A B) = true ∧
      c.le h.result k.result = true ∧
      (h = k ∨ ∃ ok, c.lookupOvl k.name = some ok ∧ ok.sig = k ∧ h ∈ c.ovlOver ok) := by
  unfold Semantics.ovlDown at hh
  rcases List.mem_cons.mp hh with rfl | hh
  · exact ⟨hk, rfl, le_all_self _, OvlLaws.le_refl _, .inl rfl⟩
  · cases hn : c.lookupOvl k.name with
    | none => rw [hn] at hh; cases hh
    | some ok =>
      rw [hn] at hh
      rcases knownSig_cases H hk with ⟨-, hn'⟩ | ⟨-, o', ho', hos⟩
      · rw [hn'] at hn; cases hn
      rw [hn] at ho'; cases ho'
      obtain ⟨-, -, -, -, -, hover, -⟩ := ovl_facts H hn
      obtain ⟨hkh, hpair, -⟩ := hover h hh
      obtain ⟨hl, hle, hres⟩ := pairOK_parts hpair
      rw [hos] at hl hle hres
      exact ⟨hkh, hl, hle, hres, .inr ⟨ok, rfl, hos, hh⟩⟩

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

/-- Two overloads of one symbol that cover the same arguments have a common symbol below both,
among `ovlDown`, that covers them too (`ovlCoherent`). -/
theorem coherent_common {o : OvlSig} {k1 k2 : CtorSig} (hk1 : KnownSig c k1) (hp1 : c.ovlPairOK o k1 = true)
    (hcoh : c.ovlCoherent k1 k2 = true) {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args)
    (hc1 : c.ovlCovers o.sig k1 vs = true) (hc2 : c.ovlCovers o.sig k2 vs = true) :
    ∃ h, h ∈ c.ovlDown k1 ∧ h ∈ c.ovlDown k2 ∧ c.ovlCovers o.sig h vs = true := by
  obtain ⟨hl1, hvl, hli1⟩ := covers_iff.mp hc1
  obtain ⟨hl2, -, hli2⟩ := covers_iff.mp hc2
  obtain ⟨-, hvi⟩ := sortsOf_iff.mp hvs
  have hli1 := zip3_all_iff.mp hli1
  have hli2 := zip3_all_iff.mp hli2
  have hpos : ∀ i (h1 : i < k1.args.length) (h2 : i < k2.args.length),
      ∃ C, C ∈ (k1.args[i] :: k2.args[i] :: c.subsorts.map (·.1)).filter
          (fun C => c.le C k1.args[i] && c.le C k2.args[i]) ∧
        ∀ X, c.le X (o.sig.args[i]'(by omega)) = true → c.le C X = true →
          c.lies X (o.sig.args[i]'(by omega)) (vs[i]'(by omega)) = true :=
    fun i h1 h2 => pos_lower H (hvi i (by omega) (by omega)) (hli1 i h1 (by omega) (by omega))
      (hli2 i h2 (by omega) (by omega))
  simp only [Semantics.ovlCoherent, Bool.or_eq_true] at hcoh
  rcases hcoh with hany | hall
  · exfalso
    obtain ⟨x, hmem, hemp⟩ := List.any_eq_true.mp hany
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hmem
    subst hie
    simp only [List.length_zip] at hi
    obtain ⟨C, hC, -⟩ := hpos i (by omega) (by omega)
    have : C ∈ ([] : List Srt) := by
      rw [← List.isEmpty_iff.mp hemp]
      simpa only [List.getElem_zip] using hC
    simp at this
  · obtain ⟨h, hmem, hb⟩ := List.any_eq_true.mp hall
    obtain ⟨hd1, hd2⟩ := List.mem_filter.mp hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨hhl, hb⟩ := hb
    obtain ⟨-, hhl', hhle, -, -⟩ := down_parts H hk1 hd1
    obtain ⟨-, hle1, -⟩ := pairOK_parts hp1
    have hhle := zip2_all_iff.mp hhle
    have hle1 := zip2_all_iff.mp hle1
    refine ⟨h, hd1, List.contains_iff_mem.mp hd2, covers_iff.mpr ⟨by omega, hvl,
      zip3_all_iff.mpr fun i hi1 hi2 hi3 => ?_⟩⟩
    obtain ⟨C, hC, hX⟩ := hpos i (by omega) (by omega)
    have hmem3 : ((h.args[i], k1.args[i]'(by omega)), k2.args[i]'(by omega)) ∈ (h.args.zip k1.args).zip k2.args := by
      have := List.getElem_mem (show i < ((h.args.zip k1.args).zip k2.args).length by simp; omega)
      simpa only [List.getElem_zip] using this
    have hb' := List.all_eq_true.mp hb _ hmem3
    have hCH := List.all_eq_true.mp hb' C hC
    exact hX _ (le_trans H (hhle i hi1 (by omega)) (hle1 i (by omega) hi2)) hCH

/-- **Coherence**: every overload of f covering the arguments gives f's normal form, that of the
overloaded symbol at the stripped arguments, lifted. -/
theorem norm_coherent : ∀ n f o, c.lookupOvl f = some o → ovlRank c f ≤ n → ∀ vs,
    c.sortsOf vs = some o.sig.args → ∀ kg ∈ c.ovlOver o, c.ovlCovers o.sig kg vs = true →
    c.norm f vs = lift kg.result o.sig.result (c.norm kg.name (stripAll kg.args o.sig.args vs))
  | 0, f, o, ho, hr, _, _, _, _, _ => by
    obtain ⟨-, -, -, -, hpos, -⟩ := ovl_facts H ho
    omega
  | n + 1, f, o, ho, hr, vs, hvs, kg, hkg, hcv => by
    obtain ⟨-, -, -, -, hpos, hover, hcoh⟩ := ovl_facts H ho
    have hvl := (sortsOf_iff.mp hvs).1
    -- the step from an overload k to a symbol h below it, both covering
    have down : ∀ k ∈ c.ovlOver o, c.ovlCovers o.sig k vs = true → ∀ h ∈ c.ovlDown k,
        c.ovlCovers o.sig h vs = true →
        lift k.result o.sig.result (c.norm k.name (stripAll k.args o.sig.args vs)) =
          lift h.result o.sig.result (c.norm h.name (stripAll h.args o.sig.args vs)) := by
      intro k hk hck h hh hch
      obtain ⟨hkk, hpk, hrk⟩ := hover k hk
      obtain ⟨hlk, hlek, hresk⟩ := pairOK_parts hpk
      obtain ⟨-, hlh, hleh, hresh, hor⟩ := down_parts H hkk hh
      rcases hor with rfl | ⟨ok, hok, hos, hmem⟩
      · rfl
      subst hos
      have hrk' : ovlRank c ok.sig.name ≤ n := by
        rcases hrk with h' | h'
        · rw [hok] at h'; cases h'
        · omega
      obtain ⟨-, -, hlies⟩ := covers_iff.mp hck
      obtain ⟨-, -, hliesh⟩ := covers_iff.mp hch
      have hcov' : c.ovlCovers ok.sig h (stripAll ok.sig.args o.sig.args vs) = true :=
        covers_iff.mpr ⟨hlh, by simp [length_stripAll]; omega,
          lies_stripAll H hlh hlk (by omega) hleh hlek hliesh⟩
      rw [norm_coherent n ok.sig.name ok hok hrk' _ (sortsOf_stripAll hlk hvs hlies) h hmem hcov',
        lift_trans H hresh hresk, stripAll_trans H hlh hlk (by omega) hleh hlek hliesh]
    cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
    | none => exact absurd hcv (by simpa using List.find?_eq_none.mp hf kg hkg)
    | some k1 =>
      rw [norm_find_some H ho hf]
      have hk1 := List.mem_of_find?_eq_some hf
      have hc1 := List.find?_some hf
      obtain ⟨hkk1, hp1, -⟩ := hover k1 hk1
      obtain ⟨h, hd1, hd2, hch⟩ := coherent_common H hkk1 hp1 (hcoh k1 hk1 kg hkg) hvs hc1 hcv
      rw [down k1 hk1 hc1 h hd1 hch, down kg hkg hcv h hd2 hch]

/-- **The overload equations**: for each symbol g that f overloads, `f(lift ā) = lift (g(ā))` at
arguments ā of g's sorts. -/
theorem norm_ovlEq {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    {as : List GroundTerm} (has : c.sortsOf as = some kg.args) :
    c.norm f (liftAll kg.args o.sig.args as) = lift kg.result o.sig.result (c.norm kg.name as) := by
  obtain ⟨-, -, -, -, -, hover, -⟩ := ovl_facts H ho
  obtain ⟨-, hpair, -⟩ := hover kg hkg
  obtain ⟨hl, hle, -⟩ := pairOK_parts hpair
  have hal := (sortsOf_iff.mp has).1
  rw [norm_coherent H _ f o ho (ovlRank_le f) _ (sortsOf_liftAll H hl has hle) kg hkg
      (covers_iff.mpr ⟨hl, by simp [length_liftAll]; omega, lies_liftAll hl has⟩),
    stripAll_liftAll H hl has]

/-! ## Normal forms -/

/-- **A normal form is the lift of a raw application** `h(ū)`: of f itself at f's arguments where
they are uncovered, otherwise of a symbol of smaller rank; ū lifts to f's arguments. -/
theorem norm_decomp : ∀ n k, KnownSig c k → ovlRank c k.name ≤ n → ∀ vs, c.sortsOf vs = some k.args →
    ∃ h us, KnownSig c h ∧ h.args.length = k.args.length ∧
      (h.args.zip k.args).all (fun (A, B) => c.le A B) = true ∧ c.le h.result k.result = true ∧
      c.norm k.name vs = lift h.result k.result (.ctor h.name us) ∧ vs = liftAll h.args k.args us ∧
      us.length = h.args.length ∧
      ((c.uncovered k.name vs = true ∧ h = k ∧ us = vs) ∨
        (c.uncovered k.name vs = false ∧ ovlRank c h.name < ovlRank c k.name)) ∧
      ∀ m, ovlRank c k.name ≤ m → h.name ∈ c.ovlReach m k.name
  | n, k, hk, hr, vs, hvs => by
    have hvl := (sortsOf_iff.mp hvs).1
    have raw : c.norm k.name vs = .ctor k.name vs → c.uncovered k.name vs = true →
        ∃ h us, KnownSig c h ∧ h.args.length = k.args.length ∧
          (h.args.zip k.args).all (fun (A, B) => c.le A B) = true ∧ c.le h.result k.result = true ∧
          c.norm k.name vs = lift h.result k.result (.ctor h.name us) ∧ vs = liftAll h.args k.args us ∧
          us.length = h.args.length ∧
          ((c.uncovered k.name vs = true ∧ h = k ∧ us = vs) ∨
            (c.uncovered k.name vs = false ∧ ovlRank c h.name < ovlRank c k.name)) ∧
          ∀ m, ovlRank c k.name ≤ m → h.name ∈ c.ovlReach m k.name :=
      fun he hu => ⟨k, vs, hk, rfl, le_all_self _, OvlLaws.le_refl _, by rw [he, lift_self],
        (liftAll_self _ hvl).symm, hvl, .inl ⟨hu, rfl, rfl⟩, fun m _ => ovlReach_head m _⟩
    cases hn : c.lookupOvl k.name with
    | none => exact raw (norm_none hn vs) (uncovered_of_none hn vs)
    | some o =>
      rcases knownSig_cases H hk with ⟨-, hn'⟩ | ⟨hct, o', ho', hos⟩
      · rw [hn'] at hn; cases hn
      rw [hn] at ho'; cases ho'; subst hos
      obtain ⟨-, -, -, -, hpos, hover, -⟩ := ovl_facts H hn
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none => exact raw (norm_find_none hn hf) (uncovered_of_find_none hn hf)
      | some kg =>
        have hkg := List.mem_of_find?_eq_some hf
        have hcv := List.find?_some hf
        obtain ⟨hkk, hpair, hr'⟩ := hover kg hkg
        obtain ⟨hl, hle, hres⟩ := pairOK_parts hpair
        obtain ⟨-, -, hlies⟩ := covers_iff.mp hcv
        have hrk : ovlRank c kg.name < ovlRank c o.sig.name := by
          rcases hr' with h' | h'
          · rw [rank_of_none h']; omega
          · exact h'
        match n with
        | 0 => omega
        | n + 1 =>
          obtain ⟨h, us, hkh, hlh, hleh, hresh, hne, hvs', hul, hor, hreach⟩ :=
            norm_decomp n kg hkk (by omega) _ (sortsOf_stripAll hl hvs hlies)
          refine ⟨h, us, hkh, by omega, le_all_trans H hlh hl hleh hle, le_trans H hresh hres, ?_, ?_, hul,
            .inr ⟨covered_of_mem hn hkg hcv, ?_⟩, fun m hm => ?_⟩
          · rw [norm_find_some H hn hf, hne, lift_trans H hresh hres]
          · rw [← liftAll_trans H hlh hl hul hleh hle, ← hvs', liftAll_stripAll hl hvs hlies]
          · rcases hor with ⟨-, rfl, -⟩ | ⟨-, h'⟩ <;> omega
          · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            have hin := hreach m (by omega)
            simp only [Semantics.ovlReach, hn, List.mem_cons, List.mem_flatMap]
            exact .inr ⟨kg.name, mem_ovlOver hkg, hin⟩

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

/-- **`norm` is injective** on argument lists of the symbol's sorts. -/
theorem norm_inj_known {k : CtorSig} (hk : KnownSig c k) {vs ws : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hws : c.sortsOf ws = some k.args)
    (he : c.norm k.name vs = c.norm k.name ws) : vs = ws := by
  obtain ⟨h, us, hkh, -, -, -, hne, hv, -⟩ := norm_decomp H _ k hk (ovlRank_le _) vs hvs
  obtain ⟨h', us', hkh', -, -, -, hne', hw, -⟩ := norm_decomp H _ k hk (ovlRank_le _) ws hws
  rw [hne, hne'] at he
  obtain ⟨hn, rfl⟩ := lift_ctor_inj he
  rw [hv, hw, knownSig_inj hkh hkh' hn]

theorem norm_inj {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs ws : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) (hws : c.sortsOf ws = some o.sig.args)
    (he : c.norm f vs = c.norm f ws) : vs = ws := by
  obtain ⟨hn, -, -, hks, -⟩ := ovl_facts H ho
  exact norm_inj_known H hks hvs hws (by rw [hn]; exact he)

/-- **A normal form is the raw application exactly where no overload covers the arguments.** -/
theorem norm_eq_raw_iff {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) : c.norm f vs = .ctor f vs ↔ c.uncovered f vs = true := by
  obtain ⟨hn, -, -, hks, -⟩ := ovl_facts H ho
  obtain ⟨h, us, -, -, -, -, hne, -, -, hor, -⟩ := norm_decomp H _ o.sig hks (ovlRank_le _) vs hvs
  rw [hn] at hne hor
  constructor
  · intro he
    rcases hor with ⟨hu, -⟩ | ⟨-, hlt⟩
    · exact hu
    · rw [he, ← lift_self o.sig.result (.ctor f vs)] at hne
      obtain ⟨rfl, -⟩ := lift_ctor_inj hne
      omega
  · intro hu
    rcases hor with ⟨-, rfl, rfl⟩ | ⟨hu', -⟩
    · rw [hne, lift_self, hn]
    · rw [hu] at hu'; cases hu'

/-- **A value is its own normal form.** -/
theorem norm_fixed {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs : List GroundTerm} {s : Srt}
    (hv : c.sortOf (.ctor f vs) = some s) : c.norm f vs = .ctor f vs := by
  obtain ⟨-, -, hct, -⟩ := ovl_facts H ho
  rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, -⟩ | ⟨-, o', ho', hvs, hu, -⟩ | ⟨-, ho', -⟩
  · rw [hct] at hk; cases hk
  · rw [ho] at ho'; cases ho'
    exact (norm_eq_raw_iff H ho hvs).mpr hu
  · rw [ho] at ho'; cases ho'

/-- **A normal form's raw application is of a symbol in the overload closure.** -/
theorem norm_head {k : CtorSig} (hk : KnownSig c k) {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args) :
    ∃ A f us, c.norm k.name vs = lift A k.result (.ctor f us) ∧ f ∈ c.ovlClosure k.name := by
  obtain ⟨h, us, -, -, -, -, hne, -, -, -, hreach⟩ := norm_decomp H _ k hk (ovlRank_le _) vs hvs
  exact ⟨h.result, h.name, us, hne, hreach _ (by have := ovlRank_le (c := c) k.name; omega)⟩

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
    exact ⟨hoi.1.1.1.1.1.1.1, hoi.1.1.1.1.1.1.2⟩
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
