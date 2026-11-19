/-
  What FLOAT's sentence 1673 reads at a Float literal of a format `thinAt` names, on the combinators
  of Hooks.lean (KcoreSpec/FloatThinHooks.lean): each lemma at `p1x3` (precision 1, 3 exponent
  bits), `thin_isInf_iff` also at `p3x1` (one exponent bit, its largest finite datum subnormal), and
  the values the lemmas name decided by the kernel.

  `p1x3` (bias 3): the encoding `8·s + x`, the field `x` from 1 to 6 is `±2^(x − 3)`, 7 an infinity;
  6 is the largest finite datum 8 and 14 its negation. `p3x1`: the encoding `(2·s + x)·4 + f`, `x = 0`
  the subnormals `f/4·2^0` (3 is the largest finite datum 0.75), `x = 1, f = 0` an infinity (4).
-/
import KcoreSpec.FloatThinHooks

open KCore Float.Model

namespace KCore.FloatThin1673Test

/-- A Float literal. -/
def fv (p e b : Nat) : GroundTerm := .dv Srt.float (.float p e b)

/-! ## The lemmas at `p1x3` -/

example : tflInf [fv 1 3 7] = some (bool (KFloat.isInf (KFloat.tnUnpack 1 3 7))) := by
  obtain ⟨_, hm⟩ := KFloat.tnMax?_normal (p := 1) (e := 3) (by decide) (by decide)
  exact thin_inf_val (by decide) hm 7

example : flFmt (fun p _ => p) [fv 1 3 7] = some (int 1) ∧ flFmt (fun _ e => e) [fv 1 3 7] = some (int 3) :=
  ⟨thin_precision_val (by decide) 7, thin_exponentBits_val (by decide) 7⟩

example : ∃ m, KFloat.tnMax? 1 3 = some m ∧ tflAt KFloat.tnMax? [int 1, int 3] = some (tnFloatV 1 3 m) ∧
    asDatum (tnFloatV 1 3 m) = some m ∧
    tfl1 (fun _ _ => KFloat.neg?) [tnFloatV 1 3 m] = some (tnFloatV 1 3 m.neg) ∧
    asDatum (tnFloatV 1 3 m.neg) = some m.neg := by
  obtain ⟨_, hm⟩ := KFloat.tnMax?_normal (p := 1) (e := 3) (by decide) (by decide)
  exact ⟨_, hm, thin_max_val (by decide) hm, thin_max_datum (by decide) hm, thin_neg_val (by decide) hm,
    thin_negmax_datum (by decide) hm⟩

example : ∃ m, KFloat.tnMax? 1 3 = some m ∧
    flCmp (fun o => o == some .gt) [fv 1 3 7, tnFloatV 1 3 m] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack 1 3 7) m == some .gt)) ∧
    flCmp (fun o => o == some .lt) [fv 1 3 15, tnFloatV 1 3 m.neg] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack 1 3 15) m.neg == some .lt)) := by
  obtain ⟨_, hm⟩ := KFloat.tnMax?_normal (p := 1) (e := 3) (by decide) (by decide)
  exact ⟨_, hm, thin_gt_max_val (by decide) hm 7, thin_lt_negmax_val (by decide) hm 15⟩

/-- 1673's two sides at `+∞` (7), the largest finite datum (6), its negation (14) and `−∞` (15). -/
example : ∀ b ∈ [7, 6, 14, 15], ∃ m, KFloat.tnMax? 1 3 = some m ∧
    tflInf [fv 1 3 b] = some (bool (KFloat.cmpExact (KFloat.tnUnpack 1 3 b) m == some .gt ||
      KFloat.cmpExact (KFloat.tnUnpack 1 3 b) m.neg == some .lt)) := by
  intro b _
  obtain ⟨_, hm⟩ := KFloat.tnMax?_normal (p := 1) (e := 3) (by decide) (by decide)
  exact ⟨_, hm, thin_1673_vals (by decide) hm b⟩

/-! ## `thin_isInf_iff` at `p1x3` and at `p3x1` -/

example : ∃ m, KFloat.tnMax? 1 3 = some m ∧ KFloat.isInf (KFloat.tnUnpack 1 3 6) =
    (KFloat.cmpExact (KFloat.tnUnpack 1 3 6) m == some .gt || KFloat.cmpExact (KFloat.tnUnpack 1 3 6) m.neg == some .lt) := by
  obtain ⟨_, hm⟩ := KFloat.tnMax?_normal (p := 1) (e := 3) (by decide) (by decide)
  exact ⟨_, hm, thin_isInf_iff (by decide) (KFloat.tnIsDatum_unpack (by decide) 6) hm⟩

example : ∀ b ∈ [3, 4, 11, 12], ∃ m, KFloat.tnMax? 3 1 = some m ∧ KFloat.isInf (KFloat.tnUnpack 3 1 b) =
    (KFloat.cmpExact (KFloat.tnUnpack 3 1 b) m == some .gt || KFloat.cmpExact (KFloat.tnUnpack 3 1 b) m.neg == some .lt) := by
  intro b _
  obtain ⟨_, hm⟩ := KFloat.tnMax?_subnormal (p := 3) (by decide)
  exact ⟨_, hm, thin_isInf_iff (by decide) (KFloat.tnIsDatum_unpack (by decide) b) hm⟩

/-! ## The values, decided by the kernel -/

/-- `isInfinite`: true at `±∞`, false at the largest finite datum and its negation. -/
example : [tflInf [fv 1 3 7], tflInf [fv 1 3 6], tflInf [fv 1 3 14], tflInf [fv 1 3 15]] =
    [some (bool true), some (bool false), some (bool false), some (bool true)] := by decide +kernel

/-- `maxValueFloat(1, 3)` is the literal 6 (the datum 8), `--Float` of it the literal 14 (−8). -/
example : tflAt KFloat.tnMax? [int 1, int 3] = some (fv 1 3 6) ∧
    tfl1 (fun _ _ => KFloat.neg?) [fv 1 3 6] = some (fv 1 3 14) := by decide +kernel

/-- The right side of 1673 at the same four literals, on the exact comparisons with the largest
finite datum and its negation. -/
example : [7, 6, 14, 15].map (fun b => (KFloat.tnMax? 1 3).map fun m =>
    KFloat.cmpExact (KFloat.tnUnpack 1 3 b) m == some .gt || KFloat.cmpExact (KFloat.tnUnpack 1 3 b) m.neg == some .lt) =
    [some true, some false, some false, some true] := by decide +kernel

/-- At `p3x1`: `+∞` (4) and `−∞` (12) are beyond the largest finite datum 0.75 (3) and its negation (11). -/
example : [3, 4, 11, 12].map (fun b => ((KFloat.tnMax? 3 1).map fun m =>
    KFloat.cmpExact (KFloat.tnUnpack 3 1 b) m == some .gt || KFloat.cmpExact (KFloat.tnUnpack 3 1 b) m.neg == some .lt,
    KFloat.isInf (KFloat.tnUnpack 3 1 b))) =
    [(some false, false), (some true, true), (some false, false), (some true, true)] := by decide +kernel

/-- At `(1, 1)` no largest finite datum exists, and `isInfinite` has no value there. -/
example : KFloat.tnMax? 1 1 = none ∧ tflInf [fv 1 1 1] = none := by decide +kernel

#check @thin_inf_val
#check @thin_max_val
#check @thin_max_datum
#check @thin_neg_val
#check @thin_isInf_iff
#check @thin_1673_vals

#print axioms thin_inf_val
#print axioms thin_max_val
#print axioms thin_max_datum
#print axioms thin_neg_val
#print axioms thin_isInf_iff
#print axioms thin_precision_val
#print axioms thin_exponentBits_val
#print axioms thin_negmax_datum
#print axioms thin_gt_max_val
#print axioms thin_lt_negmax_val
#print axioms thin_1673_vals

end KCore.FloatThin1673Test
