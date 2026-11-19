/-
  The row predsApart.1 of test/witnesses.toml: it is implied by `idsOK` for every semantics whose
  functions of `c.fns` are labelled apart.
  Run from the package root: `lake env lean -j1 test/WitRestApart.lean`.

  Kernel-checked here, for every semantics:
  - `predsApart_of_idsOK`: the functions evaluation reads are named apart, where `idsOK` holds and
    the functions of `c.fns` are labelled apart. No function of `c.fns` bears a registry symbol
    (`idsOK`), so none is `isK` or `isKItem`; the other sort predicates are `predOf X` for X a sort
    below KItem that labels no function of `c.fns` (`sortPreds`): the library's and the
    definition's sorts are apart and each once (`NamesApart.sorts_facts`), a registry sort's
    predicate is the registry's (`regPred`: distinct for distinct sorts, below `nRegSyms`, neither
    `isK` nor `isKItem`, decided over the registry's sorts), and an own sort, numbered below
    `nRegSorts + sortNames.length` (`idsOK`'s first conjunct), has the predicate
    `X - nRegSorts + nRegSyms`, below `symBase`.
  predsApart.1 cannot be dropped from `coreOK`: two functions of `c.fns` under one own sort's
  predicate number meet `idsOK` (test/PredFnCone.lean, `Twice`). `hooksApart` is not a conjunct
  of `coreOK`: `faithCoreOK` implies it (`Semantics.hooksApart_of_faithCoreOK`, HooksApart.lean),
  and `Definition.namesOK` asks it beside `predsApart`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestApart

open Faithful.Model

/-- A list without repetition keeps none under a map that is injective where it is defined. -/
theorem nodup_filterMap {f : Nat → Option Nat} : ∀ {l : List Nat}, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, ∀ p, f x = some p → f y = some p → x = y) → (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    have ih := nodup_filterMap hnd.2 fun x hx y hy => hinj x (.tail _ hx) y (.tail _ hy)
    rw [List.filterMap_cons]
    cases ha : f a with
    | none => exact ih
    | some p =>
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih⟩
      obtain ⟨y, hy, hfy⟩ := List.mem_filterMap.mp hm
      exact hnd.1 (hinj a (.head _) y (.tail _ hy) p ha hfy ▸ hy)

/-- The registry's sort predicates: distinct for distinct registry sorts, below `nRegSyms`, neither
`isK` nor `isKItem`. -/
theorem regPred_facts : ∀ X < nRegSorts, (regPred X).all (fun p => decide (p < nRegSyms) && p != isK && p != isKItem) = true ∧
    ∀ Y < nRegSorts, (regPred X).isSome = true → regPred X = regPred Y → X = Y := by
  decide

/-! The arithmetic, stated over `Nat` for `omega`. -/
theorem aux_bound (X A B n : Nat) (hB : 52 < B) (h1 : ¬ X < A) (h2 : X < A + n) :
    X - A + B < B + n ∧ X - A + B ≠ 51 ∧ X - A + B ≠ 52 := by omega
theorem aux_inj (X Y A B : Nat) (h1 : ¬ X < A) (h2 : ¬ Y < A) (h : X - A + B = Y - A + B) : X = Y := by omega
theorem aux_cross (X A B : Nat) (_h1 : ¬ X < A) (h : X - A + B < B) : False := by omega
theorem aux_ge (B n k : Nat) (hk : k < B) (h : B + n ≤ k) : False := by omega

/-- The predicate `sortPreds` builds for the sort `X`: `predOf X` where it labels no function of
`c.fns`. -/
def predIn (c : Semantics) (X : Srt) : Option Sym := (predOf X).filter fun p => !c.fns.any (·.label == p)

theorem sortPreds_labels (c : Semantics) :
    c.sortPreds.map (·.label) = isK :: isKItem :: c.sortsBelowKItem.filterMap (predIn c) := by
  simp only [Semantics.sortPreds, List.map_cons, List.map_filterMap, List.cons_append, List.nil_append]
  congr 2
  congr 1
  funext X
  unfold predIn
  cases (predOf X).filter fun p => !c.fns.any (·.label == p) <;> rfl

/-- A predicate `sortPreds` builds is `predOf`'s and labels no function of `c.fns`. -/
theorem predIn_some {c : Semantics} {X : Srt} {p : Sym} (h : predIn c X = some p) :
    predOf X = some p ∧ ∀ f ∈ c.fns, f.label ≠ p := by
  unfold predIn at h
  cases hX : predOf X with
  | none => rw [hX] at h; cases h
  | some a =>
    rw [hX] at h
    simp only [Option.filter] at h
    split at h
    · rename_i hq
      cases h
      refine ⟨rfl, fun f hf heq => ?_⟩
      rw [Bool.not_eq_true', List.any_eq_false] at hq
      exact hq f hf (by rw [heq]; exact beq_self_eq_true _)
    · cases h

theorem predsApart_of_idsOK {c : Semantics} (h : c.idsOK = true)
    (hfn : nodup (c.fns.map (·.label)) = true) : c.predsApart = true := by
  have hnd := (NamesApart.sorts_facts h).1
  have hlt := NamesApart.lib_sorts_lt (NamesApart.lib_ok h)
  have hids := h
  unfold Semantics.idsOK at hids
  simp only [Bool.and_eq_true, beq_iff_eq] at hids
  have hown : c.ownSorts = List.range' nRegSorts c.sortNames.length := hids.1.1.1
  -- the sorts below KItem: a registry sort, or an own sort numbered below `nRegSorts + n`
  have hS : ∀ X ∈ c.sortsBelowKItem, nRegSorts ≤ X → X < nRegSorts + c.sortNames.length := by
    intro X hX hge
    rcases NamesApart.mem_sortsBelowKItem.mp hX with hX | hX
    · exact absurd (hlt X hX).1 (Nat.not_lt.mpr hge)
    · have : X ∈ c.ownSorts := List.mem_filter.mpr ⟨hX, decide_eq_true hge⟩
      rw [hown, List.mem_range'_1] at this
      exact this.2
  have hreg := regPred_facts
  have hsb : c.symBase = nRegSyms + c.sortNames.length := rfl
  -- each predicate is below `symBase`, neither `isK` nor `isKItem`
  have hbound : ∀ X ∈ c.sortsBelowKItem, ∀ p, predOf X = some p → p < c.symBase ∧ p ≠ isK ∧ p ≠ isKItem := by
    intro X hX p hp
    unfold predOf at hp
    by_cases hXr : X < nRegSorts
    · rw [if_pos hXr] at hp
      have := (hreg X hXr).1
      rw [hp] at this
      simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at this
      exact ⟨Nat.lt_of_lt_of_le this.1.1 (Nat.le_add_right _ _), this.1.2, this.2⟩
    · rw [if_neg hXr] at hp
      have hp' := Option.some.inj hp
      subst hp'
      have := hS X hX (Nat.not_lt.mp hXr)
      rw [hsb]
      exact aux_bound X nRegSorts nRegSyms _ (by decide) hXr this
  have hinj : ∀ X ∈ c.sortsBelowKItem, ∀ Y ∈ c.sortsBelowKItem, ∀ p, predOf X = some p → predOf Y = some p →
      X = Y := by
    intro X _ Y _ p hpX hpY
    unfold predOf at hpX hpY
    by_cases hXr : X < nRegSorts <;> by_cases hYr : Y < nRegSorts
    · rw [if_pos hXr] at hpX; rw [if_pos hYr] at hpY
      exact (hreg X hXr).2 Y hYr (by rw [hpX]; rfl) (by rw [hpX, hpY])
    · rw [if_pos hXr] at hpX; rw [if_neg hYr] at hpY
      have hp' := Option.some.inj hpY
      subst hp'
      have := (hreg X hXr).1
      rw [hpX] at this
      simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at this
      exact (aux_cross Y nRegSorts nRegSyms hYr this.1.1).elim
    · rw [if_neg hXr] at hpX; rw [if_pos hYr] at hpY
      have hp' := Option.some.inj hpX
      subst hp'
      have := (hreg Y hYr).1
      rw [hpY] at this
      simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at this
      exact (aux_cross X nRegSorts nRegSyms hXr this.1.1).elim
    · rw [if_neg hXr] at hpX; rw [if_neg hYr] at hpY
      have h1 := Option.some.inj hpX
      have h2 := Option.some.inj hpY
      exact aux_inj X Y nRegSorts nRegSyms hXr hYr (h1.trans h2.symm)
  -- the definition's functions: once each, none a registry symbol
  have hF : (c.fns.map (·.label)).Nodup ∧ ∀ l ∈ c.fns.map (·.label), nRegSyms ≤ l := by
    refine ⟨(NamesApart.nodupB_iff _).mp hfn, fun l hl => ?_⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
    exact of_decide_eq_true (List.all_eq_true.mp hids.1.2.2 f hf)
  unfold Semantics.predsApart Semantics.allFns
  rw [NamesApart.nodupB_iff, List.map_append, sortPreds_labels]
  have hP := nodup_filterMap hnd (f := predIn c) (by
    intro X hX Y hY p hpX hpY
    exact hinj X (by simpa [Semantics.sortsBelowKItem] using hX) Y (by simpa [Semantics.sortsBelowKItem] using hY) p
      (predIn_some hpX).1 (predIn_some hpY).1)
  have hmemP : ∀ q ∈ c.sortsBelowKItem.filterMap (predIn c), (∀ f ∈ c.fns, f.label ≠ q) ∧ q ≠ isK ∧ q ≠ isKItem := by
    intro q hq
    obtain ⟨X, hX, hq⟩ := List.mem_filterMap.mp hq
    exact ⟨(predIn_some hq).2, (hbound X hX q (predIn_some hq).1).2⟩
  refine List.nodup_append.mpr ⟨hF.1, ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨fun hm => (hmemP _ hm).2.2 rfl, hP⟩⟩
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact (hmemP _ hm).2.1 rfl
  · intro a ha b hb heq
    subst heq
    have h1 := hF.2 a ha
    rcases List.mem_cons.mp hb with hb | hb
    · subst hb; exact (aux_ge nRegSyms 0 51 (by decide) h1).elim
    rcases List.mem_cons.mp hb with hb | hb
    · subst hb; exact (aux_ge nRegSyms 0 52 (by decide) h1).elim
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
      exact (hmemP _ hb).1 f hf rfl

/-- info: 'KCore.Faithful.WitRestApart.predsApart_of_idsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms predsApart_of_idsOK

end KCore.Faithful.WitRestApart
