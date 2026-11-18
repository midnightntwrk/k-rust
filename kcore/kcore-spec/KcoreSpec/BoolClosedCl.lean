/-
  KCore. The value model satisfies Bool's closure axiom where Bool holds only its literals
  (`boolClosed_modelClT`, at any step relation; `boolClosed_modelCl` at `StepM`): the values of
  Bool are then the two literals (`boolValuesCl`, which reads only `litSort`), and of the semantics
  the proof reads `HypModelCore`.
-/
import KcoreSpec.ModelHas
import KcoreSpec.HypWf

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-- **Where Bool holds only literals, its values are the two literals**: `boolValues`, which reads
only `litSort`. -/
theorem boolValuesCl {c : Semantics} (hl : c.litSort Srt.bool = true)
    {v : GroundTerm} (hv : c.sortOf v = some Srt.bool) : ∃ b, v = .dv Srt.bool (.bool b) := by
  simp only [Semantics.litSort, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨hct, hov⟩, hsub⟩, hpr⟩, hcoll⟩, htok⟩, hbyte⟩, -⟩ := hl
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, -, hs⟩ | ⟨-, o, ho, -, -, hs⟩ | ⟨-, -, k, hk, -, -, hs⟩
    · exact absurd hs.symm (hct k (lookupSig_spec hk).1)
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec ho
      exact absurd hs.symm (hov o.sig (List.mem_map.mpr ⟨o, he ▸ List.getElem_mem hi, rfl⟩))
    · obtain ⟨hm, hraw, -, -⟩ := c.lookupOpen_spec hk
      have := hpr k hm
      simp [hraw, ← hs] at this
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hv
    exact (hsub _ hab rfl).elim
  | dv s lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hv
    cases lit with
    | bool b => exact ⟨b, rfl⟩
    | int _ => simp only [dvOK, Lib.carrier_bool, beq_iff_eq] at hok; exact absurd hok (by decide)
    | float _ _ _ => simp only [dvOK, Lib.carrier_bool, Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
    | tok t =>
      simp only [dvOK, Lib.carrier_bool, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ((hk | hk) | hk) | ⟨hk, -⟩
      · cases hk
      · cases hk
      · exact absurd hk (by simpa using htok)
      · rcases hk with hk | hk
        · cases hk
        · exact absurd hk (by simpa using hbyte)
  | map s es => obtain ⟨rfl, hk⟩ := sortOf_map_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk
  | set s es => obtain ⟨rfl, hk⟩ := sortOf_set_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk
  | list s es => obtain ⟨rfl, hk⟩ := sortOf_list_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk

/-- **The value model satisfies the closure axiom** where Bool holds only literals:
`boolClosed_model`, which reads `coreOK` only through `boolValues`. -/
theorem boolClosed_modelClT {c : Semantics} {T : GroundTerm → GroundTerm → Prop} (h : HypModelCore c)
    (hl : c.litSort Srt.bool = true) : stdI_T c T ⊧ᴵ boolClosed c := by
  intro e m
  unfold boolClosed
  rw [KoreAML.interp_included AtT.defOK_std]
  intro a ha
  have ha' := (AtT.inhOf_sort h.namesK (bool_numbered (c := c)) e a).mp ha
  obtain ⟨v, rfl, hv⟩ := inSort_val ha'
  obtain ⟨b, rfl⟩ := boolValuesCl hl hv
  have hs := AtT.den_val (T := T) h (.dv Srt.bool (.bool b)) hv e
  simp only [Pattern.interpret]
  intro hn
  cases b with
  | true => exact absurd ((hs _).mpr rfl) hn
  | false => exact (hs _).mpr rfl

/-- The closure axiom in the value model at `StepM`: `boolClosed_modelClT`. -/
theorem boolClosed_modelCl {c : Semantics} (h : HypModelCore c)
    (hl : c.litSort Srt.bool = true) : stdI c ⊧ᴵ boolClosed c :=
  boolClosed_modelClT (T := StepM c) h hl

end KCore
