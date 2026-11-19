/-
  KCore. What FLOAT's sentence 1673 (domains.md, K 7.1.337),
  `isInfinite(F) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool
  F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`,
  reads at a Float literal `F` of a format `thinAt` names, on the combinators of Hooks.lean
  (`tflInf`, `flFmt`, `tflAt`, `flCmp`, `tfl1`), not on `hook`.

  At such a format with a largest finite datum `m` (`KFloat.tnMax?`), with `u` the literal's datum:
  - `thin_inf_val`: `isInfinite` (`tflInf`) is `KFloat.isInf u`;
  - `thin_precision_val`, `thin_exponentBits_val`: the format is read off the literal (`flFmt`);
  - `thin_max_val`: `maxValueFloat` (`tflAt KFloat.tnMax?`) is the literal `tnFloatV p e m`, and
    `thin_max_datum` reads it back as `m` (`asDatum`, `KFloat.tnUnpack_pack`);
  - `thin_neg_val`: `--Float` of it (`tfl1`) is the literal of `m`'s negation, read back as that
    negation (`thin_negmax_datum`);
  - `thin_gt_max_val`, `thin_lt_negmax_val`: the two comparisons (`flCmp`) are the exact
    comparisons of `u` with `m` and with its negation;
  - `thin_isInf_iff`: a datum of the format is infinite exactly when it is above `m` or below its
    negation (`KFloat.tnIsInf_datum`), so `thin_1673_vals`: the left side's value is the `orBool`
    of the right side's two comparisons.

  The statements on the combinators hold at every format `thinAt` names; their proofs read `thinAt`
  through `thinAt_tnFormat` and `thinAt_spec_none`. `thin_isInf_iff` holds at every format with a
  field of 1 and a largest finite datum: at precision 1, where that datum `1·2^(2^e − 2 − shift)` is
  a power of two, and at one exponent bit, where it is subnormal (`KFloat.tnMax?_subnormal`). At
  `(1, 1)` `KFloat.tnMax?` is none and nothing is stated.
-/
import KcoreSpec.Hooks
import KcoreSpec.FloatThinLaws
import KcoreSpec.LibAdmitted

set_option autoImplicit false

namespace KCore

open Float.Model

section
variable {p e : Nat}

theorem thinAt_pos_ftw (ht : thinAt p e = true) : 1 ≤ p ∧ 1 ≤ e := by
  have h := thinAt_tnFormat ht
  simp only [KFloat.tnFormat, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1⟩

/-- The datum `asThin` reads off a Float literal of a format `thinAt` names. -/
theorem thin_asThin (ht : thinAt p e = true) (b : Nat) :
    asThin (.dv Srt.float (.float p e b)) = some (p, e, KFloat.tnUnpack p e b) := by
  simp [asThin, ht]

/-- `asThin` reads the literal of a datum of the format back as that datum. -/
theorem thin_asThin_tnFloatV (ht : thinAt p e = true) {u : UnpackedFloat}
    (hu : KFloat.tnIsDatum p e u = true) : asThin (tnFloatV p e u) = some (p, e, u) := by
  obtain ⟨hp, he⟩ := thinAt_pos_ftw ht
  rw [tnFloatV, thin_asThin ht, KFloat.tnUnpack_pack hp he u hu]

/-- The datum `asDatum` reads off a Float literal of a format `thinAt` names. -/
theorem thin_asDatum (ht : thinAt p e = true) (b : Nat) :
    asDatum (.dv Srt.float (.float p e b)) = some (KFloat.tnUnpack p e b) := by
  simp [asDatum, thinAt_spec_none ht, thinAt_tnFormat ht]

/-- `asDatum` reads the literal of a datum of the format back as that datum. -/
theorem thin_asDatum_tnFloatV (ht : thinAt p e = true) {u : UnpackedFloat}
    (hu : KFloat.tnIsDatum p e u = true) : asDatum (tnFloatV p e u) = some u := by
  obtain ⟨hp, he⟩ := thinAt_pos_ftw ht
  rw [tnFloatV, thin_asDatum ht, KFloat.tnUnpack_pack hp he u hu]

/-- **`isInfinite` of a Float literal of a format `thinAt` names with a largest finite datum** is
the test of its datum. -/
theorem thin_inf_val (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m)
    (b : Nat) :
    tflInf [.dv Srt.float (.float p e b)] = some (bool (KFloat.isInf (KFloat.tnUnpack p e b))) := by
  simp [tflInf, thin_asThin ht, hm]

/-- `precisionFloat` of a Float literal of a format `thinAt` names. -/
theorem thin_precision_val (ht : thinAt p e = true) (b : Nat) :
    flFmt (fun p _ => p) [.dv Srt.float (.float p e b)] = some (int p) := by
  obtain ⟨hp, he⟩ := thinAt_pos_ftw ht
  simp [flFmt, hp, he]

/-- `exponentBitsFloat` of a Float literal of a format `thinAt` names. -/
theorem thin_exponentBits_val (ht : thinAt p e = true) (b : Nat) :
    flFmt (fun _ e => e) [.dv Srt.float (.float p e b)] = some (int e) := by
  obtain ⟨hp, he⟩ := thinAt_pos_ftw ht
  simp [flFmt, hp, he]

/-- **`maxValueFloat` at a format `thinAt` names with a largest finite datum `m`** is the literal
of `m`. -/
theorem thin_max_val (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m) :
    tflAt KFloat.tnMax? [int (p : Int), int (e : Int)] = some (tnFloatV p e m) := by
  simp [tflAt, asInt, int, ht, hm]

/-- The literal of the largest finite datum reads back as that datum. -/
theorem thin_max_datum (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m) :
    asDatum (tnFloatV p e m) = some m :=
  thin_asDatum_tnFloatV ht (KFloat.tnMax?_datum hm)

/-- **`--Float` of the literal of the largest finite datum** is the literal of its negation. -/
theorem thin_neg_val (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m) :
    tfl1 (fun _ _ => KFloat.neg?) [tnFloatV p e m] = some (tnFloatV p e m.neg) := by
  have hneg : KFloat.neg? m = some m.neg := by
    match m, hm with
    | .notANumber, hm =>
      exfalso
      unfold KFloat.tnMax? KFloat.tnMk? at hm
      split at hm <;> split at hm <;> (try split at hm) <;> simp at hm
    | .finite _ _ _ _, _ => rfl
    | .zero _, _ => rfl
    | .infinity _, _ => rfl
  simp [tfl1, thin_asThin_tnFloatV ht (KFloat.tnMax?_datum hm), hneg]

/-- The literal of the negation of the largest finite datum reads back as that negation. -/
theorem thin_negmax_datum (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m) :
    asDatum (tnFloatV p e m.neg) = some m.neg :=
  thin_asDatum_tnFloatV ht (KFloat.tnIsDatum_neg (KFloat.tnMax?_datum hm))

/-- `>Float` of a Float literal of a format `thinAt` names and the literal of the largest finite
datum: the exact comparison of the two data. -/
theorem thin_gt_max_val (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m)
    (b : Nat) :
    flCmp (fun o => o == some .gt) [.dv Srt.float (.float p e b), tnFloatV p e m] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack p e b) m == some .gt)) := by
  simp [flCmp, thin_asDatum ht, thin_max_datum ht hm]

/-- `<Float` of a Float literal of a format `thinAt` names and the literal of the negation of the
largest finite datum: the exact comparison of the two data. -/
theorem thin_lt_negmax_val (ht : thinAt p e = true) {m : UnpackedFloat} (hm : KFloat.tnMax? p e = some m)
    (b : Nat) :
    flCmp (fun o => o == some .lt) [.dv Srt.float (.float p e b), tnFloatV p e m.neg] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack p e b) m.neg == some .lt)) := by
  simp [flCmp, thin_asDatum ht, thin_negmax_datum ht hm]

end

/-- **A datum of a format with a field of 1 and a largest finite datum `m` is infinite exactly when
it is above `m` or below its negation** by the exact comparison. -/
theorem thin_isInf_iff {p e : Nat} (hf : KFloat.tnFormat p e = true) {u m : UnpackedFloat}
    (hu : KFloat.tnIsDatum p e u = true) (hm : KFloat.tnMax? p e = some m) :
    KFloat.isInf u = (KFloat.cmpExact u m == some .gt || KFloat.cmpExact u m.neg == some .lt) := by
  simp only [KFloat.tnFormat, decide_eq_true_eq] at hf
  exact KFloat.tnIsInf_datum hf.1 hf.2.1 hu hm

/-- **1673 on the combinators**: at a Float literal of a format `thinAt` names with a largest finite
datum `m`, `isInfinite`'s value is the `orBool` of the values of the right side's two comparisons. -/
theorem thin_1673_vals {p e : Nat} (ht : thinAt p e = true) {m : UnpackedFloat}
    (hm : KFloat.tnMax? p e = some m) (b : Nat) :
    tflInf [.dv Srt.float (.float p e b)] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack p e b) m == some .gt ||
        KFloat.cmpExact (KFloat.tnUnpack p e b) m.neg == some .lt)) := by
  obtain ⟨hp, -⟩ := thinAt_pos_ftw ht
  rw [thin_inf_val ht hm, thin_isInf_iff (thinAt_tnFormat ht) (KFloat.tnIsDatum_unpack hp b) hm]

end KCore
