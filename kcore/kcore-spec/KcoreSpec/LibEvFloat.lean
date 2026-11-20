/-
  KCore, checked layer: FLOAT's library sentence 1648 (domains.md, K 7.1.337),
  `F1 =/=Float F2 => notBool (F1 ==Float F2)`, entailed at values (`EntailsAtValues`) in every
  semantics meeting `coreOK`, for every interpretation.

  Both sides read the two Floats through `==Float` and `=/=Float`, whose values are stated at every
  pair of data (domains.md 1631-1638 and 1541: the comparison of the exact values, the zeros equal,
  a NaN unequal to every datum), so the sentence's value reads no clause of an operation that the
  text takes from IEEE 754 by name. Where `hook` gives `=/=Float` a value it gives `==Float` one
  too, and the first is the negation of the second (`flCmp` at complementary tests). Where it gives
  `=/=Float` none it gives `==Float` none, neither is a key of `silentTable`, and both sides have
  no value.

  FLOAT's sentence 1673, `isInfinite(F) => F >Float maxValueFloat(precisionFloat(F),
  exponentBitsFloat(F)) orBool F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`
  (`fnIsInfinite`), entailed at values in the same way for every interpretation meeting
  `Semantics.isInfiniteEq`. At a Float of a format with a model, both sides are `hook`'s and agree
  at every format: a datum is infinite exactly when it is above the format's largest finite value
  or below its negation (`KFloat.isInf_unpack`, FloatUnpack.lean), and the literals of
  `maxValueFloat` and its negation read back as those data (`KFloat.unpackBits_packBits`). At a
  format `thinAt` names (precision 1 or one exponent bit) with a largest finite datum `m`
  (`KFloat.tnMax?`: every one but `(1, 1)`), both sides are `hook`'s too, by the combinators of that
  format: a datum of the format is infinite exactly when it is above `m` or below its negation
  (`thin_1673_vals`, FloatThinHooks.lean). At the format `(1, 1)` `isInfinite` is at a silent point
  and `isInfiniteEq` is the sentence there.
-/
import KcoreSpec.LibEvStr
import KcoreSpec.FloatUnpack
import KcoreSpec.FloatThinHooks

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- 1648: `F1 =/=Float F2 => notBool (F1 ==Float F2)`. -/
def fnNeFloat : FnEqn :=
  ⟨[("VarF1", Srt.float), ("VarF2", Srt.float)], floatNe,
    [(Srt.float, .var 0, none), (Srt.float, .var 1, none)], Srt.bool, none,
    .app boolNot [.app floatEq [.var 0, .var 1]]⟩

/-- `=/=Float` and `==Float` at two values, by `hook`: complementary where `=/=Float` has a value. -/
theorem flt_ne_eq {c : Semantics} (a b : GroundTerm) (h : hook floatNe [a, b] ≠ some none) :
    c.hv floatNe [a, b] = (c.hv floatEq [a, b]).bind fun v => c.hv boolNot [v] := by
  have h1 : hook floatNe [a, b] = some (flCmp (fun o => o != some .eq) [a, b]) := rfl
  have h2 : hook floatEq [a, b] = some (flCmp (fun o => o == some .eq) [a, b]) := rfl
  cases ha : asDatum a with
  | none => exact absurd (by rw [h1]; simp [flCmp, ha]) h
  | some u =>
    cases hb : asDatum b with
    | none => exact absurd (by rw [h1]; simp [flCmp, ha, hb]) h
    | some w =>
      have e1 : hook floatNe [a, b] = some (some (bool (KFloat.cmpExact u w != some .eq))) := by
        rw [h1]; simp [flCmp, ha, hb]
      have e2 : hook floatEq [a, b] = some (some (bool (KFloat.cmpExact u w == some .eq))) := by
        rw [h2]; simp [flCmp, ha, hb]
      rw [hv_of_value e1, hv_of_value e2, Option.bind_some, fhv_boolNot]
      rfl

/-- **1648 holds of the values, under every interpretation.** -/
theorem fnNeFloat_holds {c : Semantics} : fnNeFloat.Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha, -⟩ := hσ 0 ("VarF1", Srt.float) rfl
  obtain ⟨b, hb, -⟩ := hσ 1 ("VarF2", Srt.float) rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  have h2' : σ.lookup 2 = some a := st_arg h2 ha
  have h3' : σ.lookup 3 = some b := st_arg h3 hb
  have hl : val c σ fnNeFloat.lhs = c.hv floatNe [a, b] := by fq_eval [fnNeFloat, h2', h3']
  have hr : val c σ fnNeFloat.rhs = (c.hv floatEq [a, b]).bind fun v => c.hv boolNot [v] := by
    show val c σ (.app boolNot [.app floatEq [.var 0, .var 1]]) = _
    simp only [val, valList, allSome, ha, hb, Option.bind_some, Option.map_some]
    cases c.hv floatEq [a, b] <;> rfl
  rw [hl, hr]
  by_cases hs : hook floatNe [a, b] = some none
  · have h1 : hook floatNe [a, b] = some (flCmp (fun o => o != some .eq) [a, b]) := rfl
    have h2 : hook floatEq [a, b] = some (flCmp (fun o => o == some .eq) [a, b]) := rfl
    have he : hook floatEq [a, b] = some none := by
      rw [h1, Option.some.injEq] at hs
      rw [h2, flCmp_none hs]
    have kN : c.hookRes floatNe [a, b] = hook floatNe [a, b] :=
      Semantics.hookRes_of_notKey (by decide +kernel) [a, b]
    have kE : c.hookRes floatEq [a, b] = hook floatEq [a, b] :=
      Semantics.hookRes_of_notKey (by decide +kernel) [a, b]
    have eN : c.hv floatNe [a, b] = none := by
      show (c.hookRes floatNe [a, b]).join = none
      rw [kN, hs]; first | done | rfl
    have eE : c.hv floatEq [a, b] = none := by
      show (c.hookRes floatEq [a, b]).join = none
      rw [kE, he]; first | done | rfl
    rw [eN, eE]; first | done | rfl
  · exact flt_ne_eq a b hs

/-- **domains.md 1648** is entailed at values, under every interpretation. -/
theorem fnNeFloat_ev {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNeFloat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNeFloat (by decide) (by rfl) fnNeFloat_holds ad hp hsv

/-! ## 1673: `isInfinite(F) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool
F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`, under `isInfiniteEq` -/

/-- 1673: `isInfinite(F) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool
F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`. -/
def fnIsInfinite : FnEqn :=
  ⟨[("VarF", Srt.float)], floatIsInfinite, [(Srt.float, .var 0, none)], Srt.bool, none,
    .app boolOr
      [.app floatGt [.var 0, .app floatMaxValue [.app floatPrecision [.var 0], .app floatExponentBits [.var 0]]],
       .app floatLt [.var 0, .app floatNeg
         [.app floatMaxValue [.app floatPrecision [.var 0], .app floatExponentBits [.var 0]]]]]⟩

section
variable {c : Semantics}
open Float.Model

theorem fi_spec_ge {p e : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) : 2 ≤ p ∧ 2 ≤ e := by
  unfold KFloat.spec? at h
  split at h
  · assumption
  · cases h

theorem fi_asDatum {p e b : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    asDatum (.dv Srt.float (.float p e b)) = some (KFloat.unpackBits sp b) := by
  simp [asDatum, h]

theorem fi_asFloat {p e b : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    asFloat (.dv Srt.float (.float p e b)) = some (p, e, sp, KFloat.unpackBits sp b) := by
  simp [asFloat, h]

theorem fi_hv_isInfinite {p e b : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    c.hv floatIsInfinite [.dv Srt.float (.float p e b)] = some (bool (KFloat.isInf (KFloat.unpackBits sp b))) := by
  refine hv_of_value ?_
  show some (flOr (flTestM KFloat.isInf) tflInf [.dv Srt.float (.float p e b)]) = _
  simp [flOr, flTestM, fi_asFloat h]

/-- `isInfinite` has no value at a Float of a format without a model that `thinAt` does not name,
or that has no largest finite datum (`KFloat.tnMax?`: the format `(1, 1)`). -/
theorem fi_hook_isInfinite_none {p e b : Nat} (h : KFloat.spec? p e = none)
    (ht : thinAt p e = false ∨ KFloat.tnMax? p e = none) :
    hook floatIsInfinite [.dv Srt.float (.float p e b)] = some none := by
  show some (flOr (flTestM KFloat.isInf) tflInf [.dv Srt.float (.float p e b)]) = _
  rcases ht with ht | ht <;> simp [flOr, flTestM, tflInf, asFloat, asThin, h, ht]

theorem fi_hv_precision {p e b : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    c.hv floatPrecision [.dv Srt.float (.float p e b)] = some (int p) := by
  have := fi_spec_ge h
  refine hv_of_value ?_
  show some (flFmt (fun p _ => p) [.dv Srt.float (.float p e b)]) = _
  simp [flFmt]; omega

theorem fi_hv_exponentBits {p e b : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    c.hv floatExponentBits [.dv Srt.float (.float p e b)] = some (int e) := by
  have := fi_spec_ge h
  refine hv_of_value ?_
  show some (flFmt (fun _ e => e) [.dv Srt.float (.float p e b)]) = _
  simp [flFmt]; omega

theorem fi_hv_maxValue {p e : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    c.hv floatMaxValue [int p, int e] = some (floatV p e sp (KFloat.maxValue sp)) := by
  refine hv_of_value ?_
  show some (flOr (flAt KFloat.maxValue) (tflAt KFloat.tnMax?) [int p, int e]) = _
  simp [flOr, flAt, asInt, int, h]

theorem fi_hv_cmp {t : Option Ordering → Bool} {f : Sym} (hf : ∀ vs, hook f vs = some (flCmp t vs))
    {p e b : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) (u : UnpackedFloat) (hu : KFloat.Datum sp u) :
    c.hv f [.dv Srt.float (.float p e b), floatV p e sp u] =
      some (bool (t (KFloat.cmpExact (KFloat.unpackBits sp b) u))) := by
  refine hv_of_value ?_
  rw [hf]
  simp [flCmp, fi_asDatum h, floatV, KFloat.unpackBits_packBits sp u hu]

theorem fi_hv_neg {p e : Nat} {sp : Format} (h : KFloat.spec? p e = some sp) :
    c.hv floatNeg [floatV p e sp (KFloat.maxValue sp)] = some (floatV p e sp (KFloat.maxValue sp).neg) := by
  have h1 : fl1 (fun _ => KFloat.neg?) [floatV p e sp (KFloat.maxValue sp)] =
      some (floatV p e sp (KFloat.maxValue sp).neg) := by
    simp only [fl1, floatV, fi_asFloat h, Option.bind_some,
      KFloat.unpackBits_packBits sp _ (KFloat.datum_maxValue sp)]
    rw [KFloat.maxValue_eq]; rfl
  refine hv_of_value ?_
  show some (flOr (fl1 fun _ => KFloat.neg?) (tfl1 fun _ _ => KFloat.neg?)
    [floatV p e sp (KFloat.maxValue sp)]) = _
  rw [flOr_of_some h1]

theorem fi_hv_boolOr (x y : Bool) : c.hv boolOr [bool x, bool y] = some (bool (x || y)) := hv_of_value rfl

/-! At a Float of a format `thinAt` names, `hook` is each symbol's combinator of `thinHooks` (the
combinator of a format with a model has no value there), whose values FloatThinHooks.lean gives. -/

theorem fi_asFloat_thin {p e b : Nat} (h : KFloat.spec? p e = none) :
    asFloat (.dv Srt.float (.float p e b)) = none := by
  simp [asFloat, h]

theorem fi_hv_isInfinite_thin {p e b : Nat} (ht : thinAt p e = true) {m : UnpackedFloat}
    (hm : KFloat.tnMax? p e = some m) :
    c.hv floatIsInfinite [.dv Srt.float (.float p e b)] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack p e b) m == some .gt ||
        KFloat.cmpExact (KFloat.tnUnpack p e b) m.neg == some .lt)) := by
  refine hv_of_value ?_
  show some (flOr (flTestM KFloat.isInf) tflInf [.dv Srt.float (.float p e b)]) = _
  rw [flOr_of_none (by simp [flTestM, fi_asFloat_thin (thinAt_spec_none ht)]), thin_1673_vals ht hm b]

theorem fi_hv_precision_thin {p e b : Nat} (ht : thinAt p e = true) :
    c.hv floatPrecision [.dv Srt.float (.float p e b)] = some (int p) :=
  hv_of_value (by rw [show hook floatPrecision [.dv Srt.float (.float p e b)] =
    some (flFmt (fun p _ => p) [.dv Srt.float (.float p e b)]) from rfl, thin_precision_val ht b])

theorem fi_hv_exponentBits_thin {p e b : Nat} (ht : thinAt p e = true) :
    c.hv floatExponentBits [.dv Srt.float (.float p e b)] = some (int e) :=
  hv_of_value (by rw [show hook floatExponentBits [.dv Srt.float (.float p e b)] =
    some (flFmt (fun _ e => e) [.dv Srt.float (.float p e b)]) from rfl, thin_exponentBits_val ht b])

theorem fi_hv_maxValue_thin {p e : Nat} (ht : thinAt p e = true) {m : UnpackedFloat}
    (hm : KFloat.tnMax? p e = some m) :
    c.hv floatMaxValue [int p, int e] = some (tnFloatV p e m) := by
  refine hv_of_value ?_
  show some (flOr (flAt KFloat.maxValue) (tflAt KFloat.tnMax?) [int p, int e]) = _
  rw [flOr_of_none (by simp [flAt, asInt, int, thinAt_spec_none ht]), thin_max_val ht hm]

theorem fi_hv_neg_thin {p e : Nat} (ht : thinAt p e = true) {m : UnpackedFloat}
    (hm : KFloat.tnMax? p e = some m) :
    c.hv floatNeg [tnFloatV p e m] = some (tnFloatV p e m.neg) := by
  refine hv_of_value ?_
  show some (flOr (fl1 fun _ => KFloat.neg?) (tfl1 fun _ _ => KFloat.neg?) [tnFloatV p e m]) = _
  rw [flOr_of_none (by simp [fl1, tnFloatV, fi_asFloat_thin (thinAt_spec_none ht)]), thin_neg_val ht hm]

theorem fi_hv_gt_thin {p e b : Nat} (ht : thinAt p e = true) {m : UnpackedFloat}
    (hm : KFloat.tnMax? p e = some m) :
    c.hv floatGt [.dv Srt.float (.float p e b), tnFloatV p e m] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack p e b) m == some .gt)) :=
  hv_of_value (by rw [show hook floatGt [.dv Srt.float (.float p e b), tnFloatV p e m] =
    some (flCmp (fun o => o == some .gt) [.dv Srt.float (.float p e b), tnFloatV p e m]) from rfl,
    thin_gt_max_val ht hm b])

theorem fi_hv_lt_thin {p e b : Nat} (ht : thinAt p e = true) {m : UnpackedFloat}
    (hm : KFloat.tnMax? p e = some m) :
    c.hv floatLt [.dv Srt.float (.float p e b), tnFloatV p e m.neg] =
      some (bool (KFloat.cmpExact (KFloat.tnUnpack p e b) m.neg == some .lt)) :=
  hv_of_value (by rw [show hook floatLt [.dv Srt.float (.float p e b), tnFloatV p e m.neg] =
    some (flCmp (fun o => o == some .lt) [.dv Srt.float (.float p e b), tnFloatV p e m.neg]) from rfl,
    thin_lt_negmax_val ht hm b])

end

/-- **1673 holds of the values where the interpretation meets `isInfiniteEq`.** At a Float of a
format with a model, both sides are `hook`'s: the datum is infinite exactly when it is above the
format's largest finite value or below its negation (`KFloat.isInf_unpack`); at a Float of a
format `thinAt` names with a largest finite datum, both sides are `hook`'s by the combinators of
that format (`thin_1673_vals`); at a Float of the format `(1, 1)`, which has none, `isInfinite` is at
a silent point and `isInfiniteEq` is the sentence. -/
theorem fnIsInfinite_holds {c : Semantics} (hfs : c.floatShapeOK = true) (hc : c.isInfiniteEq) :
    fnIsInfinite.Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha, sa⟩ := hσ 0 ("VarF", Srt.float) rfl
  obtain ⟨h1, -⟩ := hm
  have h1' : σ.lookup 1 = some a := st_arg h1 ha
  have hl : val c σ fnIsInfinite.lhs = c.hv floatIsInfinite [a] := by fq_eval [fnIsInfinite, h1']
  have hr : val c σ fnIsInfinite.rhs =
      (c.hv floatPrecision [a]).bind fun p => (c.hv floatExponentBits [a]).bind fun e =>
      (c.hv floatMaxValue [p, e]).bind fun m => (c.hv floatGt [a, m]).bind fun g =>
      (c.hv floatNeg [m]).bind fun m' => (c.hv floatLt [a, m']).bind fun l => c.hv boolOr [g, l] := by
    show val c σ (.app boolOr
      [.app floatGt [.var 0, .app floatMaxValue [.app floatPrecision [.var 0], .app floatExponentBits [.var 0]]],
       .app floatLt [.var 0, .app floatNeg
         [.app floatMaxValue [.app floatPrecision [.var 0], .app floatExponentBits [.var 0]]]]]) = _
    simp only [val, valList, allSome, ha, Option.bind_some, Option.map_some]
    rcases c.hv floatPrecision [a] with _ | p <;> simp only [Option.bind_none, Option.bind_some, Option.map_none]
    rcases c.hv floatExponentBits [a] with _ | e <;> simp only [Option.bind_none, Option.bind_some, Option.map_none,
      Option.map_some]
    rcases c.hv floatMaxValue [p, e] with _ | m <;> simp only [Option.bind_none, Option.bind_some, Option.map_none,
      Option.map_some]
    rcases c.hv floatGt [a, m] with _ | g <;> rcases c.hv floatNeg [m] with _ | m' <;>
      simp only [Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]
    rcases c.hv floatLt [a, m'] with _ | l <;> simp only [Option.bind_none, Option.bind_some, Option.map_none,
      Option.map_some]
  rw [hl, hr]
  obtain ⟨p, e, b, rfl, -⟩ := shape_float hfs sa
  cases hsp : KFloat.spec? p e with
  | none =>
    cases ht : thinAt p e with
    | false => exact hc _ sa (fi_hook_isInfinite_none hsp (Or.inl ht))
    | true =>
      cases hm : KFloat.tnMax? p e with
      | none => exact hc _ sa (fi_hook_isInfinite_none hsp (Or.inr hm))
      | some m =>
      rw [fi_hv_isInfinite_thin ht hm, fi_hv_precision_thin ht, Option.bind_some, fi_hv_exponentBits_thin ht,
        Option.bind_some, fi_hv_maxValue_thin ht hm, Option.bind_some, fi_hv_gt_thin ht hm, Option.bind_some,
        fi_hv_neg_thin ht hm, Option.bind_some, fi_hv_lt_thin ht hm, Option.bind_some, fi_hv_boolOr]
  | some sp =>
    rw [fi_hv_isInfinite hsp, fi_hv_precision hsp, Option.bind_some, fi_hv_exponentBits hsp, Option.bind_some,
      fi_hv_maxValue hsp, Option.bind_some, fi_hv_cmp (t := fun o => o == some .gt) (f := floatGt) (fun _ => rfl) hsp _ (KFloat.datum_maxValue sp),
      Option.bind_some, fi_hv_neg hsp, Option.bind_some,
      fi_hv_cmp (t := fun o => o == some .lt) (f := floatLt) (fun _ => rfl) hsp _ (KFloat.datum_neg (KFloat.datum_maxValue sp)), Option.bind_some,
      fi_hv_boolOr]
    exact congrArg (fun x => some (bool x)) (KFloat.isInf_unpack sp (BitVec.ofNat sp.numBits b))

/-- **domains.md 1673** is entailed at values, for an interpretation meeting `isInfiniteEq`. -/
theorem fnIsInfinite_ev {c : Semantics} (h : c.coreOK = true) (hc : c.isInfiniteEq) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnIsInfinite.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnIsInfinite (by decide) (by rfl)
    (fnIsInfinite_holds (floatShapeOK_of_coreOK h) hc) ad hp hsv

end LibEv

end KCore
