/-
  KCore. K's Float values and the IEEE 754 operations KCore interprets on them (KCORE-SPEC.md §6).
  Frozen layer; imports nothing but Init, whose `Float.Model` (Lean core's logical model of binary
  floating point) it uses.

  **Values.** A K Float carries its format: a precision p (significand bits, the implicit leading
  bit included) and an exponent width e. Its value is an IEEE 754 datum of that format: ±0,
  subnormal and normal numbers, ±∞, and NaN. K's syntax gives a NaN neither a sign nor a payload,
  so a format has one NaN. KCore represents the datum by its interchange encoding, the
  1 + e + (p − 1) bits of sign, biased exponent and trailing significand, NaN by the one canonical
  NaN pattern of Lean's model (`packedNaN`). `ok p e b` says that `b` is such an encoding (`spec?`,
  `validBits`): equal data are then equal literals (±0 distinct, the format part of the literal).
  Lean's model covers p ≥ 2 and e ≥ 2. A format K names with a field of 1 (`p1xM`, `pNx1`, N and
  M positive) has values too (`thinOK`): its encodings in the same p + e bits that are no NaN
  pattern, and one code past the bits for its NaN (at p = 1 there is no significand field to mark
  one). No operation computes on them; they are values an interpretation can give.

  **Operations.** Every operation rounds the exact result to the nearest value of the format,
  ties to the even significand (IEEE 754 §4.3.1, roundTiesToEven; K's FLOAT has no other
  rounding). The arithmetic is Lean core's (`UnpackedFloat.add`, `sub`, `mul`, `div`, `sqrt`,
  `round`, `ofInt`, `ofScientific`, `neg`, `abs`), computed on the unpacked datum
  (`unpack`, `pack`). This file adds what core does not have, each a transcription of its IEEE
  clause over Nat and Int: `roundToIntegral` toward −∞, +∞ or 0 (§5.3.1), `remainder` (§5.3.1),
  `cmpExact`, the comparison of two data of any formats by their exact values (§5.11: ±0 equal,
  NaN unordered), `convertFormat` (§5.4.2), and the format's largest finite and smallest positive
  values.

  **Text.** `text p e b` is a literal K reads back to the same datum: the exact decimal value of
  the datum with the suffix `pPxE` (`m·2^q` as the integer `m·2^q` followed by `.0` when q ≥ 0, as
  `m·5^k` followed by `e-k` when q = −k < 0), `-0.0pPxE`, `[-]InfinitypPxE`, `NaNpPxE`.
-/
set_option autoImplicit false

namespace KCore.KFloat

open Float.Model Float.Model.UnpackedFloat

/-! ## Formats and encodings -/

/-- The format of precision `p` and exponent width `e` in Lean core's model (`p − 1` stored
significand bits), for `p ≥ 2` and `e ≥ 2`. -/
def spec? (p e : Nat) : Option Format :=
  if h : 2 ≤ p ∧ 2 ≤ e then some ⟨p - 1, by omega, e, h.2⟩ else none

/-- `b` is an encoding of format `s`: it fits in the format's bits, and an exponent field of all
ones with a nonzero significand field (a NaN) is the canonical NaN (`Format.Valid`). -/
def validBits (s : Format) (b : Nat) : Bool :=
  decide (b < 2 ^ s.numBits) &&
    (let v := BitVec.ofNat s.numBits b
     unpackExponent v != -1#_ || unpackMantissa v == 0#_ || v == packedNaN s)

/-- `b` is an encoding of a format with a field of 1 (`p = 1` or `e = 1`, both positive: domains.md
1469-1476 names `pNxM` for N and M positive), which Lean core's model does not cover: a datum in the
`p + e` bits of sign, `e` exponent bits and `p − 1` significand bits that is no NaN pattern (an
exponent field of all ones with a nonzero significand field), or `2 ^ (p + e)`, the format's one NaN
(at `p = 1` there is no significand field, so no pattern of the bits is a NaN). -/
def thinOK (p e b : Nat) : Bool :=
  decide (1 ≤ p ∧ 1 ≤ e ∧ (p = 1 ∨ e = 1)) &&
    (b == 2 ^ (p + e) ||
      decide (b < 2 ^ (p + e)) && (b / 2 ^ (p - 1) % 2 ^ e != 2 ^ e - 1 || b % 2 ^ (p - 1) == 0))

/-- A Float literal's data: `b` is an encoding of the format `(p, e)`, one Lean core's model covers
(`spec?`, `validBits`) or one with a field of 1 (`thinOK`). -/
def ok (p e b : Nat) : Bool :=
  match spec? p e with
  | some s => validBits s b
  | none => thinOK p e b

/-- The datum the encoding `b` of format `s` stands for. -/
def unpackBits (s : Format) (b : Nat) : UnpackedFloat := unpack s (BitVec.ofNat s.numBits b)

/-- The encoding of a datum of format `s` (rounded for it: `pack` sends an exponent beyond the
format's range to ∞). -/
def packBits (s : Format) (u : UnpackedFloat) : Nat := (pack s u).toNat

theorem validBits_pack (s : Format) (u : UnpackedFloat) : validBits s (packBits s u) = true := by
  have hv := (valid_pack (spec := s) (f := u)).eq_packedNaN
  unfold validBits packBits
  simp only [BitVec.isLt, decide_true, Bool.true_and, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases h1 : unpackExponent (pack s u) = -1#_
  · by_cases h2 : unpackMantissa (pack s u) = 0#_
    · simp [h2]
    · simp [hv h1 h2]
  · simp [h1]

/-! ## The text of a literal -/

/-- The sign bit, the exponent field and the significand field of an encoding of the format
`(p, e)`. -/
def fields (p e b : Nat) : Nat × Nat × Nat :=
  (b / 2 ^ (p - 1 + e), b / 2 ^ (p - 1) % 2 ^ e, b % 2 ^ (p - 1))

/-- The significand of a zero or finite datum of the format with significand field `f` and exponent
field `x`: the implicit bit added when `x ≠ 0`. -/
def sig (p x f : Nat) : Nat := if x = 0 then f else f + 2 ^ (p - 1)

/-- The exponent field read as 1 for a subnormal or zero (`x = 0`). -/
def expo (x : Nat) : Nat := if x = 0 then 1 else x

/-- The bias of the format plus `p − 1`: a datum's value is `sig·2^(expo − shift)`. -/
def shift (p e : Nat) : Nat := 2 ^ (e - 1) - 1 + (p - 1)

/-- The magnitude of a zero or finite datum of the format `(p, e)` with exponent field `x` and
significand field `f`, as K's decimal syntax writes it exactly. Its value is `M·2^(E − D)` for
`M = sig`, `E = expo`, `D = shift`: with `E ≥ D` (or `M = 0`) the integer `M·2^(E − D)`, written
with `.0`; otherwise `M·5^k·10^(−k)` for `k = D − E`, written `M·5^k` then `e-k`. -/
def magText (p e x f : Nat) : String :=
  if sig p x f = 0 then Nat.repr 0 ++ ".0"
  else if shift p e ≤ expo x then Nat.repr (sig p x f * 2 ^ (expo x - shift p e)) ++ ".0"
  else Nat.repr (sig p x f * 5 ^ (shift p e - expo x)) ++ "e-" ++ Nat.repr (shift p e - expo x)

/-- The datum of the encoding `b` of the format `(p, e)` as a literal of K's syntax: its exact
decimal value (`magText`) or `Infinity`, after `-` when its sign bit is set, or `NaN` (also for the
NaN code `2 ^ (p + e)` of a format with a field of 1, `thinOK`); then the format as the suffix
`pPxE`. K reads it back to the same datum: the decimal is exact, so rounding it to the format
changes nothing. -/
def text (p e b : Nat) : String :=
  let (sg, x, f) := fields p e b
  let sign := if sg = 0 then "" else "-"
  let body := if 2 ^ (p + e) ≤ b then "NaN"
    else if x = 2 ^ e - 1 then (if f = 0 then sign ++ "Infinity" else "NaN") else sign ++ magText p e x f
  body ++ "p" ++ Nat.repr p ++ "x" ++ Nat.repr e

/-! ## Operations core does not have -/

/-- The rounding direction of `roundToIntegral`. -/
inductive Dir where
  | down
  | up
  | zero
  deriving Repr, DecidableEq

/-- roundToIntegral (IEEE 754 §5.3.1) toward −∞ (`down`), +∞ (`up`) or 0: the integral value of
the format nearest the datum in that direction. NaN, ±∞ and ±0 are their own result, and a zero
result keeps the datum's sign. A datum `±m·2^q` with `q ≥ 0` is integral; otherwise its magnitude's
integer part is `m / 2^(−q)`, raised by one when the direction points away from zero and a fraction
is dropped. The result is at most `2^p` in magnitude, so representable, and `round` gives its
canonical form. -/
def roundToIntegral (s : Format) (d : Dir) : UnpackedFloat → UnpackedFloat
  | .finite sg m q h =>
    if 0 ≤ q then .finite sg m q h
    else
      let k := (-q).toNat
      let n := m / 2 ^ k
      let up := match d, sg with
        | .down, .negative => true
        | .up, .positive => true
        | _, _ => false
      let n := if up && m % 2 ^ k != 0 then n + 1 else n
      if n = 0 then .zero sg else round s sg n 0
  | u => u

/-- A zero or finite datum as `(a, q)` with value `a·2^q`; `none` for ∞ and NaN. -/
def exact : UnpackedFloat → Option (Int × Int)
  | .zero _ => some (0, 0)
  | .finite sg m q _ => some (sg.apply m, q)
  | _ => none

/-- `a·2^qa` against `b·2^qb`, exactly: both scaled to the smaller exponent. -/
def cmpScaled (a qa b qb : Int) : Ordering :=
  let q := min qa qb
  compare (a * 2 ^ (qa - q).toNat) (b * 2 ^ (qb - q).toNat)

/-- The comparison of two data of any formats by their exact values (IEEE 754 §5.11): NaN is
unordered with everything, ±0 are equal, −∞ is below and +∞ above every other datum. -/
def cmpExact : UnpackedFloat → UnpackedFloat → Option Ordering
  | .notANumber, _ => none
  | _, .notANumber => none
  | .infinity s₁, .infinity s₂ => some (compare s₁ s₂)
  | .infinity .positive, _ => some .gt
  | .infinity .negative, _ => some .lt
  | _, .infinity .positive => some .lt
  | _, .infinity .negative => some .gt
  | x, y => match exact x, exact y with
    | some (a, qa), some (b, qb) => some (cmpScaled a qa b qb)
    | _, _ => none

/-- `n`, the integer nearest `x / y` for naturals `x` and `y > 0`, ties to even. -/
def divNearestEven (x y : Nat) : Nat :=
  let n := x / y
  let r := x % y
  if 2 * r > y then n + 1 else if 2 * r = y then n + n % 2 else n

/-- remainder (IEEE 754 §5.3.1): `x − y·n` for `n` the integer nearest `x / y`, ties to even; exact,
so representable in the format. NaN when either is NaN, when `x` is infinite or `y` is zero; `x`
itself when `y` is infinite or `x` is zero; a zero result has the sign of `x`. For finite data both
are scaled to the smaller exponent `q`: `x = ±X·2^q`, `y = ±Y·2^q`, and the result is
`±(X − n·Y)·2^q` with the sign of `x`. -/
def remainder (s : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity _, _ => .notANumber
  | _, .zero _ => .notANumber
  | x, .infinity _ => x
  | .zero sg, _ => .zero sg
  | .finite sx mx qx _, .finite _ my qy _ =>
    let q := min qx qy
    let X := mx * 2 ^ (qx - q).toNat
    let Y := my * 2 ^ (qy - q).toNat
    let n := divNearestEven X Y
    normalize s (sx.apply ((X : Int) - (n * Y : Nat))) q sx

/-- convertFormat (IEEE 754 §5.4.2) to the format `s`: a finite datum rounded to it; NaN, ±∞ and
±0 kept. -/
def convertFormat (s : Format) : UnpackedFloat → UnpackedFloat
  | .finite sg m q _ => round s sg m q
  | u => u

/-- The largest finite value of the format, `(2^p − 1)·2^(emax − p + 1)`. -/
def maxValue (s : Format) : UnpackedFloat :=
  round s .positive (2 ^ s.mantissaBits - 1) ((s.exponentBias : Int) - s.mantissaBitsWithoutImplicit)

/-- The smallest positive (subnormal) value of the format, `2^(emin − p + 1)`. -/
def minValue (s : Format) : UnpackedFloat := round s .positive 1 s.minExponent

/-- `sqrtFloat` (domains.md FLOAT, 1671: `rule sqrtFloat(F:Float) => rootFloat(F, 2)`, and described
as the square root): IEEE 754 squareRoot (§5.4.1, Lean core's `sqrt`) at every datum but −0, none at
−0. The two operations the text names, rootn(x, 2) (§9.2.1) and squareRoot, agree at every datum
but −0, where squareRoot gives −0 and rootn(−0, 2) gives +0. -/
def sqrt? (s : Format) : UnpackedFloat → Option UnpackedFloat
  | .zero .negative => none
  | u => some (UnpackedFloat.sqrt s u)

/-- NaN. -/
def isNaN : UnpackedFloat → Bool
  | .notANumber => true
  | _ => false

/-- ±∞. -/
def isInf : UnpackedFloat → Bool
  | .infinity _ => true
  | _ => false

end KCore.KFloat
