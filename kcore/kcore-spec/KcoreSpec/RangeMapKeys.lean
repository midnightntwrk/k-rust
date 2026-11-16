/-
  KCore. `rmKeysHook`, the function of RANGEMAP's `keys` (Hooks.lean), returns a Set value
  at a range map value wherever Range values are KItems (`RangeBelow`; `rmK_keys_sorted`, in
  SubjectReduction.lean):
  - `rmKeysHook_sorted_of_sub`: where `(Range, KItem)` is a subsort, the injection of each range
    is a KItem value, and the keys are a Set value;
  - `rmKeysHook_sorted`: under `genWf`, a semantics with a value of sort Range has Range below
    KItem (`rmK_range_below`): a range term is a constructor term, its sort a constructor sort,
    and a constructor sort is one of `c.sortsBelowKItem`. A range map with no entry has no key, so
    its keys are the empty Set whatever the subsorts.
  - `rangeBelow_of_genWf`, `rangeBelow_of_sound`, `rangeBelow_of_model`: `RangeBelow` under
    `genWf`, and of the semantics step soundness and the value model read.
-/
import KcoreSpec.RangeMapSorted
import KcoreSpec.FaithfulNeg
import KcoreSpec.ModelCarrier

set_option autoImplicit false

namespace KCore

open Faithful Faithful.Model

/-- **Under `genWf`, a Range value puts Range below KItem.** -/
theorem rmK_range_below {c : Semantics} (hg : genWf c = true) [OvlOK c] {a b : Int}
    (h : c.sortOf (rangeT a b) = some Srt.range) : (Srt.range, Srt.kitem) ∈ c.subsorts := by
  have hc : Srt.range ∈ consSorts c := ctor_sort_cons hg h
  obtain ⟨hap, -, -, -, ht, hy, hco⟩ := genWf_cons hg hc
  have hcar : c.lib.carriers.all (·.1 != Srt.range) = true := by
    unfold consSorts at hc
    simp only [List.mem_filter, Bool.and_eq_true] at hc
    exact hc.2.2
  unfold apartSort distinctSorts at hap
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hap
  unfold Semantics.subsorts
  refine List.mem_append_right _ (List.mem_map.mpr ⟨Srt.range, ?_, rfl⟩)
  rcases hap with ((h | h) | h) | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact h
  · rcases h with (((h | h) | h) | ⟨k, hk, hks⟩) | ⟨p, hp, hps⟩
    · rcases h with h | h | h | h | h | h <;> exact absurd h (by decide)
    · exact absurd h ht
    · exact absurd h hy
    · have : c.collOf Srt.range ≠ none := by
        unfold Semantics.collOf
        intro hn
        have := List.find?_eq_none.mp hn k hk
        simp [hks] at this
      exact absurd hco this
    · have := List.all_eq_true.mp hcar p hp
      simp [hps] at this

/-- `RangeBelow`, under `genWf`: a Range value puts Range below KItem (`rmK_range_below`). -/
theorem rangeBelow_of_genWf {c : Semantics} (hg : genWf c = true) [OvlOK c] : RangeBelow c :=
  fun _ _ h => rmK_range_below hg h

/-- `RangeBelow` of a semantics step soundness reads (`genWf` and `OvlOK` are among its parts). -/
theorem rangeBelow_of_sound {c : Semantics} (h : HypSoundCore c) : RangeBelow c :=
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- `RangeBelow` of a semantics the value model reads. -/
theorem rangeBelow_of_model {c : Semantics} (h : HypModelCore c) : RangeBelow c :=
  haveI := h.sound.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.sound.2.2.2.1

/-- `keys` at a range map value, where Range is below KItem. -/
theorem rmKeysHook_sorted_of_sub {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    (hr : (Srt.range, Srt.kitem) ∈ c.subsorts) {ws : List GroundTerm} {v : GroundTerm}
    (hws : c.sortsOf ws = some [Srt.rangeMap]) (hv : rmKeysHook ws = some v) : c.sortOf v = some Srt.set :=
  rmK_keys_sorted hco (fun _ _ _ => hr) hws hv

/-- **`keys` at a range map value is a Set value, under `genWf`.** -/
theorem rmKeysHook_sorted {c : Semantics} (hg : genWf c = true) [OvlOK c]
    (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap)) {ws : List GroundTerm} {v : GroundTerm}
    (hws : c.sortsOf ws = some [Srt.rangeMap]) (hv : rmKeysHook ws = some v) : c.sortOf v = some Srt.set :=
  rmK_keys_sorted hco (fun _ _ h => rmK_range_below hg h) hws hv

end KCore
