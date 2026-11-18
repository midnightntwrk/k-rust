/-
  KCore. K's Float values and the FLOAT operations KCore interprets on them (KCORE-SPEC.md §6).
  Frozen layer; imports nothing but Init, whose `Float.Model` (Lean core's logical model of binary
  floating point) it uses.

  **Values.** A K Float carries its format: a precision p (significand bits, the implicit leading
  bit included) and an exponent width e. Its value is an IEEE 754 datum of that format: ±0,
  subnormal and normal numbers, ±∞, and NaN. K's syntax gives a NaN neither a sign nor a payload,
  so a format has one NaN (domains.md 1497). KCore represents the datum by its interchange encoding,
  the 1 + e + (p − 1) bits of sign, biased exponent and trailing significand. Which encoding stands
  for the format's NaN is KCore's choice of a name for that one datum, not a property of a model
  of floats: here the exponent field of all ones with the top significand bit (`packedNaN`); no
  statement depends on which. `ok p e b` says that `b` is such an encoding (`spec?`,
  `validBits`): equal data are then equal literals (±0 distinct, the format part of the literal).
  Lean's model covers p ≥ 2 and e ≥ 2. A format K names with a field of 1 (`p1xM`, `pNx1`, N and
  M positive) has values too (`thinOK`): its encodings in the same p + e bits that are no NaN
  pattern, and one code past the bits for its NaN (at p = 1 there is no significand field to mark
  one). At precision 1 and at least 2 exponent bits their data are read (`thinUnpack`) for `isNaN`
  and the comparisons (Hooks.lean `asDatum`); no other operation computes on them.

  **Operations.** An operation has a value here exactly where K's text (domains.md, FLOAT) states
  one; elsewhere it gives none, and Γ states the interpretation's value (`silentTable`, Hooks.lean).
  The text names IEEE 754 for the representation of a format's data (1481-1490) and for equality at
  NaN and the zeros (1636-1638); its general reference ("based on a generalization of the IEEE 754
  standard", 1464-1466) names no operation and is taken to state no value. So: an arithmetic
  result is the exact result rounded to the nearest value of the format, a tie to the even
  significand (the rounding the productions' attributes name, 1565-1570), where the exact result
  is not zero, is at most the format's largest finite value in magnitude and rounds to a nonzero
  datum (`nearest?`), and positive zero at `0.0 -Float 0.0` (1553); `roundFloat`, `Int2Float`, the
  three roundings to an integer and `%Float` have a value where the value the text describes is one
  the format holds (`held?`), with the sign of a zero where the operation's own words give it; no
  arithmetic operation has a value at an infinity or NaN, nor a division at a zero divisor.
  Rounding is Lean core's (`normalize`, `div`, `ofScientific`, on the unpacked datum, `unpack`,
  `pack`); the regions and the exact values are written here over Nat and Int. Comparisons
  (`cmpExact`) are by the exact values of two data of any formats.

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

/-! ## Operations, where K's text states their value -/

/-- The rounding direction of `roundToIntegral`. -/
inductive Dir where
  | down
  | up
  | zero
  deriving Repr, DecidableEq

/-- A zero or finite datum as `(a, q)` with value `a·2^q`; `none` for ∞ and NaN. -/
def exact : UnpackedFloat → Option (Int × Int)
  | .zero _ => some (0, 0)
  | .finite sg m q _ => some (sg.apply m, q)
  | _ => none

/-- `a·2^qa` against `b·2^qb`, exactly: both scaled to the smaller exponent. -/
def cmpScaled (a qa b qb : Int) : Ordering :=
  let q := min qa qb
  compare (a * 2 ^ (qa - q).toNat) (b * 2 ^ (qb - q).toNat)

/-- The comparison of two data of any formats by their exact values (domains.md 1631-1638, 1541):
NaN, which is no number, stands in no order with any datum and is unequal to every one, itself
included; ±0 are equal; −∞ is below and +∞ above every other datum. -/
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

/-- The largest finite value of the format, `(2^p − 1)·2^(emax − p + 1)`. -/
def maxValue (s : Format) : UnpackedFloat :=
  round s .positive (2 ^ s.mantissaBits - 1) ((s.exponentBias : Int) - s.mantissaBitsWithoutImplicit)

/-- The smallest positive (subnormal) value of the format, `2^(emin − p + 1)`. -/
def minValue (s : Format) : UnpackedFloat := round s .positive 1 s.minExponent

/-- The value `a·2^q` rounded to the format `s`, to the nearest of its values, a tie to the one of
even significand (`normalize`; the rounding the attributes of `+Float`, `-Float`, `*Float` and
`/Float` name, domains.md 1565-1570), where the text states the result of an operation whose exact
value it is: the value is not zero (the text gives a zero result no sign), its magnitude is at most
the format's largest finite value (`maxValue`, 1601-1602: above it the text does not say whether an
infinity is a value to round to), and the rounding is a nonzero datum. `none` elsewhere. -/
def nearest? (s : Format) (a q : Int) : Option UnpackedFloat :=
  match exact (maxValue s) with
  | some (M, Q) =>
    if a ≠ 0 ∧ cmpScaled a.natAbs q M Q ≠ .gt then
      match normalize s a q .positive with
      | .finite sg m e h => some (.finite sg m e h)
      | _ => none
    else none
  | none => none

/-- The datum of the format `s` whose value is `a·2^q`, where that value is not zero and the format
holds it: `nearest?`, kept where its value is `a·2^q` itself. `none` elsewhere. -/
def held? (s : Format) (a q : Int) : Option UnpackedFloat :=
  (nearest? s a q).filter fun r =>
    match exact r with
    | some (b, e) => cmpScaled a q b e == .eq
    | none => false

/-- `--Float` (domains.md 1552-1554): the datum of the other sign, of a finite datum, a zero
("`--Float 0.0` is negative zero") or an infinity. `none` at NaN, of which the text says nothing. -/
def neg? : UnpackedFloat → Option UnpackedFloat
  | .notANumber => none
  | u => some u.neg

/-- `absFloat` (domains.md 1578): the datum of the same magnitude and the positive sign, of a finite
datum, a zero or an infinity. `none` at NaN. -/
def abs? : UnpackedFloat → Option UnpackedFloat
  | .notANumber => none
  | u => some u.abs

/-- `+Float` (domains.md 1559, 1569) at two zero or finite data: their exact sum, rounded
(`nearest?`). `none` at an infinity or NaN and where `nearest?` gives none (a zero sum, a sum above
the largest finite value, a rounding to zero). -/
def sum? (s : Format) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match exact u, exact v with
  | some (a, qa), some (b, qb) =>
    nearest? s (a * 2 ^ (qa - min qa qb).toNat + b * 2 ^ (qb - min qa qb).toNat) (min qa qb)
  | _, _ => none

/-- `-Float` (domains.md 1559, 1570) at two zero or finite data: their exact difference, rounded
(`nearest?`); and positive zero at two positive zeros ("`0.0 -Float 0.0` is positive zero", 1553),
the one zero difference the text gives a sign. `none` elsewhere. -/
def diff? (s : Format) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match u, v with
  | .zero .positive, .zero .positive => some (.zero .positive)
  | _, _ =>
    match exact u, exact v with
    | some (a, qa), some (b, qb) =>
      nearest? s (a * 2 ^ (qa - min qa qb).toNat - b * 2 ^ (qb - min qa qb).toNat) (min qa qb)
    | _, _ => none

/-- `*Float` (domains.md 1556, 1565) at two zero or finite data: their exact product, rounded
(`nearest?`). `none` elsewhere (a zero factor among them: a zero product has no sign in the text). -/
def prod? (s : Format) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match exact u, exact v with
  | some (a, qa), some (b, qb) => nearest? s (a * b) (qa + qb)
  | _, _ => none

/-- `/Float` (domains.md 1556, 1566) at two finite nonzero data `a·2^qa` and `b·2^qb` whose
quotient is at most the format's largest finite value `M·2^Q` in magnitude (`|a|·2^qa ≤ M·|b|·2^(Q + qb)`):
the quotient rounded to the nearest value of the format, a tie to the even significand (`div`),
where that is a nonzero datum. `none` elsewhere: an infinity or NaN, a zero divisor, a zero
dividend (a zero quotient has no sign in the text), a quotient above the largest finite value, a
rounding to zero. -/
def quot? (s : Format) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match exact u, exact v, exact (maxValue s) with
  | some (a, qa), some (b, qb), some (M, Q) =>
    if a ≠ 0 ∧ b ≠ 0 ∧ cmpScaled a.natAbs qa (M * b.natAbs) (Q + qb) ≠ .gt then
      match UnpackedFloat.div s u v with
      | .finite sg m e h => some (.finite sg m e h)
      | _ => none
    else none
  | _, _, _ => none

/-- `%Float` (domains.md 1557-1558: "computed based on rounding the quotient of the two floats to
the nearest integer") at two finite nonzero data `x` and `y`: `x − y·n` for `n` the integer nearest
`x / y`, where one integer is nearest and the result is a nonzero datum of the format. Both are
scaled to the smaller exponent `q`: `|x| = X·2^q`, `|y| = Y·2^q`, `r = X mod Y`; the quotient is
halfway between two integers when `2·r = Y`; otherwise `|x| − |y|·n'` for `n'` nearest `X / Y` is
`r` when `2·r < Y` and `r − Y` when `2·r > Y`, and `x − y·n` is that with the sign of `x`, times
`2^q` (`held?`: kept where the format holds it). `none` elsewhere: an infinity or NaN, a zero
divisor or dividend, a quotient halfway between two integers (the text names no integer there), a
zero result (`r = 0`; no sign in the text). -/
def remainder (s : Format) : UnpackedFloat → UnpackedFloat → Option UnpackedFloat
  | .finite sx mx qx _, .finite _ my qy _ =>
    let q := min qx qy
    let X := mx * 2 ^ (qx - q).toNat
    let Y := my * 2 ^ (qy - q).toNat
    let r := X % Y
    if 2 * r = Y then none
    else held? s (sx.apply (if Y < 2 * r then (r : Int) - Y else r)) q
  | _, _ => none

/-- `floorFloat` (`down`), `ceilFloat` (`up`), `truncFloat` (`zero`) (domains.md 1583-1588: "the
next lowest / next highest / next closest, in the direction of zero, floating-point value which is
an integer"). A zero, and a finite datum `±m·2^q` with `q ≥ 0`, is an integer and its own result.
Otherwise the magnitude's integer part is `m / 2^(−q)`, raised by one when the direction points
away from zero and a fraction is dropped; the result is the datum of that integer with the
operand's sign, where it is not zero and the format holds it (`held?`). `none` elsewhere: an
infinity or NaN (the sentence names no value), a zero result of a nonzero operand (no sign in the
text), an integer the format does not hold. -/
def roundToIntegral (s : Format) (d : Dir) : UnpackedFloat → Option UnpackedFloat
  | .zero sg => some (.zero sg)
  | .finite sg m q h =>
    if 0 ≤ q then some (.finite sg m q h)
    else
      let k := (-q).toNat
      let up := match d, sg with
        | .down, .negative => true
        | .up, .positive => true
        | _, _ => false
      held? s (sg.apply (if up && m % 2 ^ k != 0 then m / 2 ^ k + 1 else m / 2 ^ k : Nat)) 0
  | _ => none

/-- `roundFloat` (domains.md 1579-1582) to the format `s`: the datum of `s` with the operand's
value, where `s` holds it (`held?`); a zero is the zero of its sign. `none` elsewhere: a value `s`
does not hold (the text gives no direction to round in), an infinity, NaN. -/
def convertFormat (s : Format) : UnpackedFloat → Option UnpackedFloat
  | .zero sg => some (.zero sg)
  | .finite sg m q _ => held? s (sg.apply m) q
  | _ => none

/-- `Int2Float` (domains.md 1653-1654) to the format `s`: the datum of `s` with the Int's value,
where `s` holds it (`held?`); positive zero at 0 (0 is not negative). `none` at an Int `s` does not
hold (the text gives no direction to round in). -/
def ofInt? (s : Format) (n : Int) : Option UnpackedFloat :=
  if n = 0 then some (.zero .positive) else held? s n 0

/-- `m·10^x` against `M·2^Q`, exactly (naturals `m` and `M`). -/
def cmpDec (m : Nat) (x : Int) (M : Nat) (Q : Int) : Ordering :=
  compare (m * 10 ^ x.toNat * 2 ^ (-Q).toNat) (M * 2 ^ Q.toNat * 10 ^ (-x).toNat)

/-- The format `s` holds `m·10^x`, a nonzero value: its rounding to `s` (`ofScientific`) is a finite
datum of that value. -/
def decHeld (s : Format) (m : Nat) (x : Int) : Bool :=
  match ofScientific s m x with
  | .finite _ M Q _ => cmpDec m x M Q == .eq
  | _ => false

/-- The datum of a decimal literal of value `m·10^x` in the format `s` (domains.md 1478-1483:
"rounded to the nearest possible value"), `s'` the format of one more bit of precision and the same
exponent bits. Positive zero at `m = 0`. Otherwise the value rounded to the nearest datum of `s`
(`ofScientific`), where the text states it: the value is at most the format's largest finite value
(above it the text does not say whether an infinity is a possible value), the rounding is a
nonzero datum (the text does not say which zero a nonzero value nearer to zero rounds to), and the
value is not halfway between two data of `s` (the text names no value at a tie). Up to the largest
finite value of `s`, the data of `s'` are the data of `s` and the points halfway between two
neighbours (and between zero and the smallest), so the value is at a tie exactly when `s'` holds it
and `s` does not. `none` elsewhere. -/
def ofDecimal? (s s' : Format) (m : Nat) (x : Int) : Option UnpackedFloat :=
  if m = 0 then some (.zero .positive)
  else
    match exact (maxValue s), ofScientific s m x with
    | some (M, Q), .finite sg M' Q' h =>
      if cmpDec m x M.toNat Q != .gt && (cmpDec m x M' Q' == .eq || !decHeld s' m x) then
        some (.finite sg M' Q' h)
      else none
    | _, _ => none

/-- `sqrtFloat` (domains.md 1600: "Compute the square root `sqrtFloat` of a float"; `[function]`,
not `total`, 1624): the datum of the format whose value is the square root of the operand's value,
where the format holds that root exactly. At a positive finite datum `m·2^q`: the candidate is Lean
core's square root rounded to the format (`UnpackedFloat.sqrt`), kept only where it is a positive
finite `r·2^e` with `r²·2^(2e) = m·2^q`, so it is the root itself. `none` elsewhere: NaN (no
number), a negative datum and −∞ (no real root), a root the format does not hold (the text names no
rounding for `sqrtFloat`, and so no datum for an inexact root), +∞ (an infinite operand, of which
the sentence names no value, as of floor, ceil and trunc), and both zeros: the root of a zero is a
zero, and the text gives the sign of a zero result only where an operation's own words give it
(`--Float 0.0` and `0.0 -Float 0.0`, 1553-1554; `absFloat`, floor, ceil, trunc and `roundFloat` at a
zero; `Int2Float` at 0), and gives none for `sqrtFloat` (1600, 1671), so which zero is unstated. -/
def sqrt? (s : Format) : UnpackedFloat → Option UnpackedFloat
  | .finite .positive m q h =>
    match UnpackedFloat.sqrt s (.finite .positive m q h) with
    | .finite .positive r e h' =>
      if cmpScaled ((r * r : Nat) : Int) (2 * e) (m : Int) q == .eq then some (.finite .positive r e h')
      else none
    | _ => none
  | _ => none

/-- NaN. -/
def isNaN : UnpackedFloat → Bool
  | .notANumber => true
  | _ => false

/-- ±∞. -/
def isInf : UnpackedFloat → Bool
  | .infinity _ => true
  | _ => false

/-- The datum of the encoding `b` of the format `(1, e)`, `e ≥ 2`, which Lean core's model does not
cover (`thinOK`): with no significand field, the sign bit is bit `e` and the exponent field the `e`
bits below it (`fields`); the field 0 is a zero, the field of all ones an infinity, and another
field `x` the value `2^(x − bias)`, bias `2^(e−1) − 1` (the significand is the implicit 1 alone, as
`text` reads it: `sig`, `shift`); `2 ^ (1 + e)` is the format's NaN. -/
def thinUnpack (e b : Nat) : UnpackedFloat :=
  if 2 ^ (1 + e) ≤ b then .notANumber
  else
    let sg : UnpackedFloat.Sign := if b / 2 ^ e = 0 then .positive else .negative
    let x := b % 2 ^ e
    if x = 0 then .zero sg
    else if x = 2 ^ e - 1 then .infinity sg
    else .finite sg 1 ((x : Int) - (2 ^ (e - 1) - 1 : Nat)) Nat.one_pos

end KCore.KFloat
