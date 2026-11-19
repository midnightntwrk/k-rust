/-
  KCore. A sort `Semantics.hasValue` accepts has a value, on a definition with `coreOK`
  (`hasValue_value`): a probe literal `dvOK` accepts is a value of the sort (`hasLit_value`, for
  every definition), the empty collection of a collection sort is one (`hasEmpty_value`, for every
  definition), and each round of `witnessed` adds a sort with a constructor of `ctorSigs` or an
  injection whose argument sorts have values, which applied to those values is a value of it
  (`witnessed_value`). No hypothesis on the parameters: `sortOf` at a constructor of `ctorSigs` and
  at an injection reads no interpretation.
-/
import KcoreSpec.Confined
import KcoreSpec.HasValue

set_option autoImplicit false

namespace KCore

open Faithful

/-- **A sort with a probe literal has a value**: the literal. -/
theorem Semantics.hasLit_value {c : Semantics} {s : Srt} (h : c.hasLit s = true) : ∃ v, c.sortOf v = some s := by
  obtain ⟨lit, -, hl⟩ := List.any_eq_true.mp h
  exact ⟨.dv s lit, by simp [Semantics.sortOf, hl]⟩

/-- **A collection sort whose empty collection is a value has a value**: the empty map of a map or
range map sort with a value sort, the empty set of a set sort, the empty list of a list sort. -/
theorem Semantics.hasEmpty_value {c : Semantics} {s : Srt} (h : c.hasEmpty s = true) : ∃ v, c.sortOf v = some s := by
  cases hk : c.collOf s with
  | none => simp [Semantics.hasEmpty, hk] at h
  | some k =>
    cases hkind : k.kind with
    | map =>
      have hv : k.val.isSome = true := by simpa [Semantics.hasEmpty, hk, hkind] using h
      obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hv
      exact ⟨.map s [], by simp [Semantics.sortOf, hk, hvs, hkind, keysSorted, Semantics.entriesOK]⟩
    | rangeMap =>
      have hv : k.val.isSome = true := by simpa [Semantics.hasEmpty, hk, hkind] using h
      obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hv
      exact ⟨.map s [], by simp [Semantics.sortOf, hk, hvs, hkind, rangesOK, Semantics.entriesOK]⟩
    | set => exact ⟨.set s [], by simp [Semantics.sortOf, Semantics.sortsOf, hk, hkind, elemsSorted]⟩
    | list => exact ⟨.list s [], by simp [Semantics.sortOf, Semantics.sortsOf, hk, hkind]⟩

/-- **Each sort of `witnessed` has a value**, where the overloading symbols are well formed
(`OvlOK`), the subsorts transitive and the names apart: by the rounds, a constructor of `ctorSigs`
applied to values of its argument sorts, or the injection of a value. -/
theorem witnessed_value_of {c : Semantics} (hO : OvlOK c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hn : Model.NamesApartK c) {s : Srt} (hs : s ∈ c.witnessed) :
    ∃ v, c.sortOf v = some s := by
  -- the rounds keep "each listed sort has a value"
  have rounds : ∀ (step : List Srt → List Srt),
      (∀ l, (∀ a ∈ l, ∃ v, c.sortOf v = some a) → ∀ a ∈ step l, ∃ v, c.sortOf v = some a) →
      ∀ (n : Nat) (l : List Srt), (∀ a ∈ l, ∃ v, c.sortOf v = some a) →
        ∀ a ∈ Nat.repeat step n l, ∃ v, c.sortOf v = some a := by
    intro step hstep n
    induction n with
    | zero => exact fun l hl => hl
    | succ n ih => exact fun l hl => hstep _ (ih l hl)
  refine rounds _ (fun l hl a ha => ?_) _ _ (fun a ha => ?_) s hs
  · have okv : ∀ b, (l.contains b = true ∨ c.hasLit b = true) ∨ c.hasEmpty b = true → ∃ w, c.sortOf w = some b := by
      intro b hb
      rcases hb with (hb | hb) | hb
      · exact hl b (List.contains_iff_mem.mp hb)
      · exact Semantics.hasLit_value hb
      · exact Semantics.hasEmpty_value hb
    rcases List.mem_append.mp ha with ha | ha
    · exact hl a ha
    · have ha2 := (List.mem_filter.mp ha).2
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true] at ha2
      rcases ha2.2 with ⟨k, hk, rfl, hargs⟩ | ⟨p, hp, rfl, hp1⟩
      · obtain ⟨ws, hws⟩ := values_of_each k.args fun b hb => okv b (hargs b hb)
        exact ⟨_, OvlLaws.sortOf_norm_known_ovlF (hO.hyp htr) (hO.hyp htr).fnFacts _ k
          (knownSig_of_mem hn (List.mem_append_left _ hk)) (OvlLaws.ovlRank_le (c := c) k.name) ws hws
          (c.fnCover_of_lookupOvl_none (OvlLaws.lookupOvl_none_of_ctor (hO.hyp htr) hk) ws)⟩
      · obtain ⟨w, hw⟩ := okv p.1 hp1
        have hab : (p.1, p.2) ∈ c.subsorts := hp
        cases hni : w.isInj with
        | false => exact ⟨_, OvlLaws.sortOf_inj_iff.mpr ⟨hab, hni, hw, rfl⟩⟩
        | true =>
          cases w with
          | inj a0 a' w0 =>
            obtain ⟨h1, hni0, hw0, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hw
            exact ⟨_, OvlLaws.sortOf_inj_iff.mpr ⟨htr _ _ _ h1 hab, hni0, hw0, rfl⟩⟩
          | _ => simp [GroundTerm.isInj] at hni
  · have ha2 := (List.mem_filter.mp ha).2
    rw [Bool.or_eq_true] at ha2
    rcases ha2 with ha2 | ha2
    · exact Semantics.hasLit_value ha2
    · exact Semantics.hasEmpty_value ha2

/-- **Each sort of `witnessed` has a value**, on a definition with `coreOK`. -/
theorem witnessed_value {c : Semantics} (h : c.coreOK = true) {s : Srt} (hs : s ∈ c.witnessed) :
    ∃ v, c.sortOf v = some s := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  exact witnessed_value_of hno (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.1) hs

/-- **A sort `hasValue` accepts has a value**, where the overloading symbols are well formed, the
subsorts transitive and the names apart (`witnessed_value_of`), at every interpretation of the
parameters. -/
theorem hasValue_value_of {c : Semantics} (hO : OvlOK c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hn : Model.NamesApartK c) {s : Srt} (hs : c.hasValue s = true) :
    ∃ v, c.sortOf v = some s := by
  simp only [Semantics.hasValue, Bool.or_eq_true, List.contains_iff_mem] at hs
  rcases hs with (hs | hs) | hs
  · exact Semantics.hasLit_value hs
  · exact Semantics.hasEmpty_value hs
  · exact witnessed_value_of hO htr hn hs

/-- **`hasValue_value`.** On a definition with `coreOK`, a sort `hasValue` accepts has a value, at
every interpretation of the parameters. -/
theorem hasValue_value {c : Semantics} (h : c.coreOK = true) {s : Srt} (hs : c.hasValue s = true) :
    ∃ v, c.sortOf v = some s := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  exact hasValue_value_of hno (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.1) hs

end KCore
