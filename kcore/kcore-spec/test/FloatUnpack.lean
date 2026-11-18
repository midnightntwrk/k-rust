/-
  Facts of Lean core's binary floating-point model at every format it covers, from
  KcoreSpec/FloatUnpack.lean: their statements, and that they rest on no axiom beyond Lean's three.
  Run from the package root: `lake env lean test/FloatUnpack.lean`.
-/
import KcoreSpec.FloatUnpack

open Float.Model Float.Model.UnpackedFloat

namespace KCore.KFloat

example (s : Format) (b : BitVec s.numBits) (sg : Sign) (m : Nat) (q : Int) (h : 0 < m)
    (hu : UnpackedFloat.unpack s b = .finite sg m q h) :
    m < 2 ^ s.mantissaBits ∧
      q ≤ (2 ^ s.exponentBits : Nat) - 2 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit :=
  unpack_finite_bounds hu

example (s : Format) (u : UnpackedFloat) (hu : Datum s u) : UnpackedFloat.unpack s (UnpackedFloat.pack s u) = u :=
  unpack_pack s u hu

example (s : Format) (b : BitVec s.numBits) : Datum s (UnpackedFloat.unpack s b) := datum_unpack s b

example (s : Format) :
    maxValue s = .finite .positive (2 ^ s.mantissaBits - 1)
      ((s.exponentBias : Int) - s.mantissaBitsWithoutImplicit) (fu_maxValue_pos s) := maxValue_eq s

example (s : Format) :
    exact (maxValue s) =
      some (((2 ^ s.mantissaBits - 1 : Nat) : Int), (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit) :=
  exact_maxValue s

example (s : Format) (sg : Sign) (m : Nat) (q : Int) (hm : 0 < m)
    (ht : s.targetExponent (totalExponent m q) = q) : round s sg m q = .finite sg m q hm :=
  round_of_target s sg hm ht

end KCore.KFloat

/-- info: 'KCore.KFloat.datum_unpack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.KFloat.datum_unpack
/-- info: 'KCore.KFloat.unpack_finite_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.KFloat.unpack_finite_bounds
/-- info: 'KCore.KFloat.unpack_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.KFloat.unpack_pack
/-- info: 'KCore.KFloat.unpackBits_packBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.KFloat.unpackBits_packBits
/-- info: 'KCore.KFloat.round_of_target' depends on axioms: [propext] -/
#guard_msgs in #print axioms KCore.KFloat.round_of_target
/-- info: 'KCore.KFloat.maxValue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms KCore.KFloat.maxValue_eq
/-- info: 'KCore.KFloat.exact_maxValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms KCore.KFloat.exact_maxValue
