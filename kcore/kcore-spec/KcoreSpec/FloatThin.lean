/-
  KCore. The formats `pNxM` with a field of 1 (`p = 1` or `e = 1`, both positive; domains.md
  1469-1476 names a format for every positive N and M), which Lean core's float model does not cover
  (`KFloat.spec?`), written here from the values of their data.

  **Data.** The encoding of sign, `e` exponent bits and `p − 1` significand bits, read at the small
  parameter (`fields`, `sig`, `expo`, `shift`, as `text` reads it): an exponent field of 0 is a zero
  or a subnormal datum `f·2^(1 − shift)`; the field of all ones an infinity; another field `x` the
  normal datum `(f + 2^(p−1))·2^(x − shift)`.
  - `p = 1`, `e ≥ 2`: no significand field. ±0, ±2^x for `1 − bias ≤ x ≤ bias`, ±∞, NaN.
  - `e = 1`: the one exponent bit is the field of the zeros and subnormal data (0) or of the
    infinities (1); no normal datum. ±0, ±f·2^(2 − p) for `0 < f < 2^(p−1)`, ±∞, NaN.
  - `(1, 1)`: ±0, ±∞, NaN.
  A finite nonzero datum is kept as `m·2^q` with `q` the exponent of its last significand digit
  (`tnIsDatum`), so that a datum has one form and one encoding (`tnPack`, `tnUnpack`).

  **Rounding.** One rounding, of a positive rational `N / D` to the nearest datum (`tnRound`): the
  last digit's exponent `q` is the one of the binade of `N / D` (`tnLog`), or the format's smallest;
  the significand is the integer nearest `N / (D·2^q)`; a value halfway between two integers goes to
  the even one, and has no rounding at `p = 1`, where a significand is the one digit 1 and neither
  neighbour is even. An operation's value is then the exact result rounded, on the region where the
  text states it (FloatDomain.lean): the operations are the formulas of FloatDomain.lean over this
  rounding (`sumBy` … `ofIntBy`, of which the operations there are the instances at Lean core's
  rounding). At `(1, 1)` the format has no largest finite and no smallest positive datum
  (`tnMax?`, `tnMin?`), so no arithmetic result is stated there.
-/
import KcoreSpec.FloatDomain

set_option autoImplicit false

namespace KCore.KFloat

open Float.Model Float.Model.UnpackedFloat

/-! ## Data and encodings -/

/-- `(p, e)` is a format with a field of 1. -/
def tnFormat (p e : Nat) : Bool := decide (1 ≤ p ∧ 1 ≤ e ∧ (p = 1 ∨ e = 1))

/-- `u` is a datum of the format `(p, e)`: NaN, an infinity, a zero, a subnormal datum `m·2^q`
(`m < 2^(p−1)`, exponent field 0: `q = 1 − shift`) or a normal one (`2^(p−1) ≤ m < 2^p`, exponent
field `q + shift` from 1 to `2^e − 2`). -/
def tnIsDatum (p e : Nat) : UnpackedFloat → Bool
  | .finite _ m q _ =>
    decide (m < 2 ^ (p - 1) ∧ q = 1 - (shift p e : Int)) ||
      decide (2 ^ (p - 1) ≤ m ∧ m < 2 ^ p ∧ 1 ≤ q + (shift p e : Int) ∧ q + (shift p e : Int) ≤ (2 ^ e - 2 : Nat))
  | _ => true

/-- The datum of the encoding `b` of the format `(p, e)` (`fields`): at or past `2 ^ (p + e)` the
format's NaN (`thinOK`); the exponent field of all ones is an infinity (a NaN where the significand
field is not 0); otherwise the value is `sig·2^(expo − shift)`, a zero where `sig` is 0. -/
def tnUnpack (p e b : Nat) : UnpackedFloat :=
  if 2 ^ (p + e) ≤ b then .notANumber
  else
    let sg : Sign := if b / 2 ^ (p - 1 + e) = 0 then .positive else .negative
    let x := b / 2 ^ (p - 1) % 2 ^ e
    let f := b % 2 ^ (p - 1)
    if x = 2 ^ e - 1 then (if f = 0 then .infinity sg else .notANumber)
    else if h : sig p x f = 0 then .zero sg
    else .finite sg (sig p x f) ((expo x : Int) - (shift p e : Int)) (Nat.pos_of_ne_zero h)

/-- The encoding of the format `(p, e)` with sign bit `s`, exponent field `x` and significand field
`f`. -/
def tnBits (p e s x f : Nat) : Nat := s * 2 ^ (p - 1 + e) + x * 2 ^ (p - 1) + f

/-- The sign bit. -/
def tnSignBit : Sign → Nat
  | .positive => 0
  | .negative => 1

/-- The encoding of a datum of the format `(p, e)` (`tnIsDatum`), `2 ^ (p + e)` for its NaN. -/
def tnPack (p e : Nat) : UnpackedFloat → Nat
  | .notANumber => 2 ^ (p + e)
  | .infinity sg => tnBits p e (tnSignBit sg) (2 ^ e - 1) 0
  | .zero sg => tnBits p e (tnSignBit sg) 0 0
  | .finite sg m q _ =>
    if m < 2 ^ (p - 1) then tnBits p e (tnSignBit sg) 0 m
    else tnBits p e (tnSignBit sg) (q + (shift p e : Int)).toNat (m - 2 ^ (p - 1))

/-- The datum `±m·2^q` of the format `(p, e)`, where `m` is not 0 and that is one of its data in the
form `tnIsDatum` asks. -/
def tnMk? (p e : Nat) (sg : Sign) (m : Nat) (q : Int) : Option UnpackedFloat :=
  if h : 0 < m then (if tnIsDatum p e (.finite sg m q h) then some (.finite sg m q h) else none)
  else none

/-- The largest finite datum of the format: `(2^p − 1)·2^(2^e − 2 − shift)` where the format has
normal data (`e ≥ 2`), and the largest subnormal one, `(2^(p−1) − 1)·2^(1 − shift)`, at `e = 1`.
None at `(1, 1)`, whose finite data are the zeros. -/
def tnMax? (p e : Nat) : Option UnpackedFloat :=
  if 2 ≤ e then tnMk? p e .positive (2 ^ p - 1) (((2 ^ e - 2 : Nat) : Int) - (shift p e : Int))
  else tnMk? p e .positive (2 ^ (p - 1) - 1) (1 - (shift p e : Int))

/-- The smallest positive datum of the format, `2^(1 − shift)`. None at `(1, 1)`, which has no
positive finite datum. -/
def tnMin? (p e : Nat) : Option UnpackedFloat := tnMk? p e .positive 1 (1 - (shift p e : Int))

/-! ## The rounding -/

/-- The integer `k` with `2^k ≤ N / D < 2^(k+1)`, for positive `N` and `D`: the difference of the
two bit lengths, or one less. -/
def tnLog (N D : Nat) : Int :=
  let k : Int := (Nat.log2 N : Int) - (Nat.log2 D : Int)
  if D * 2 ^ k.toNat ≤ N * 2 ^ (-k).toNat then k else k - 1

/-- The integer nearest `N / D`. Halfway between two integers: the even one where `even` is set,
none otherwise. -/
def tnNearInt (even : Bool) (N D : Nat) : Option Nat :=
  if 2 * (N % D) < D then some (N / D)
  else if D < 2 * (N % D) then some (N / D + 1)
  else if even then some (if N / D % 2 = 0 then N / D else N / D + 1)
  else none

/-- The datum of the format `(p, e)` nearest the positive rational `N / D`, with the sign `sg`.
`q` is the exponent of the last of the `p` significand digits of `N / D` (`tnLog`), and not below
the format's smallest, `1 − shift`; the significand is the integer nearest `N / (D·2^q)`, `2^p`
being `2^(p−1)` at the next exponent. A tie goes to the even significand; at `p = 1` it has no
value. None where the significand is 0 (a rounding to zero) and where the result is no datum of the
format (above its largest finite one). -/
def tnRound (p e : Nat) (sg : Sign) (N D : Nat) : Option UnpackedFloat :=
  let q : Int := max (tnLog N D - ((p - 1 : Nat) : Int)) (1 - (shift p e : Int))
  (tnNearInt (decide (2 ≤ p)) (N * 2 ^ (-q).toNat) (D * 2 ^ q.toNat)).bind fun n =>
    if n = 2 ^ p then tnMk? p e sg (2 ^ (p - 1)) (q + 1) else tnMk? p e sg n q

/-- The sign of a nonzero Int. -/
def tnSign (a : Int) : Sign := if a < 0 then .negative else .positive

/-- The value `a·2^q` rounded to the format `(p, e)` (`tnRound`), on the region where the text
states the result of an operation whose exact value it is (`nearest?`): the value is not zero and
its magnitude is at most the format's largest finite datum. `none` elsewhere, at `(1, 1)` always. -/
def tnNearest? (p e : Nat) (a q : Int) : Option UnpackedFloat :=
  match (tnMax? p e).bind exact with
  | some (M, Q) =>
    if a ≠ 0 ∧ cmpScaled a.natAbs q M Q ≠ .gt then
      tnRound p e (tnSign a) (a.natAbs * 2 ^ q.toNat) (2 ^ (-q).toNat)
    else none
  | none => none

/-! ## The operations over a rounding -/

/-- `held?` over the rounding `nr`: its result, kept where its value is `a·2^q` itself. -/
def heldBy (nr : Int → Int → Option UnpackedFloat) (a q : Int) : Option UnpackedFloat :=
  (nr a q).filter fun r =>
    match exact r with
    | some (b, e) => cmpScaled a q b e == .eq
    | none => false

/-- `sum?` over the rounding `nr`. -/
def sumBy (nr : Int → Int → Option UnpackedFloat) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match exact u, exact v with
  | some (a, qa), some (b, qb) =>
    nr (a * 2 ^ (qa - min qa qb).toNat + b * 2 ^ (qb - min qa qb).toNat) (min qa qb)
  | _, _ => none

/-- `diff?` over the rounding `nr`. -/
def diffBy (nr : Int → Int → Option UnpackedFloat) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match u, v with
  | .zero .positive, .zero .positive => some (.zero .positive)
  | _, _ =>
    match exact u, exact v with
    | some (a, qa), some (b, qb) =>
      nr (a * 2 ^ (qa - min qa qb).toNat - b * 2 ^ (qb - min qa qb).toNat) (min qa qb)
    | _, _ => none

/-- `prod?` over the rounding `nr`. -/
def prodBy (nr : Int → Int → Option UnpackedFloat) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match exact u, exact v with
  | some (a, qa), some (b, qb) => nr (a * b) (qa + qb)
  | _, _ => none

/-- `remainder` over `hd`, the datum of a value the format holds. -/
def remainderBy (hd : Int → Int → Option UnpackedFloat) : UnpackedFloat → UnpackedFloat → Option UnpackedFloat
  | .finite sx mx qx _, .finite _ my qy _ =>
    let q := min qx qy
    let X := mx * 2 ^ (qx - q).toNat
    let Y := my * 2 ^ (qy - q).toNat
    let r := X % Y
    if 2 * r = Y then none
    else hd (sx.apply (if Y < 2 * r then (r : Int) - Y else r)) q
  | _, _ => none

/-- `roundToIntegral` over `hd`, the datum of a value the format holds. -/
def roundToIntegralBy (hd : Int → Int → Option UnpackedFloat) (d : Dir) : UnpackedFloat → Option UnpackedFloat
  | .zero sg => some (.zero sg)
  | .finite sg m q h =>
    if 0 ≤ q then some (.finite sg m q h)
    else
      let k := (-q).toNat
      let up := match d, sg with
        | .down, .negative => true
        | .up, .positive => true
        | _, _ => false
      hd (sg.apply (if up && m % 2 ^ k != 0 then m / 2 ^ k + 1 else m / 2 ^ k : Nat)) 0
  | _ => none

/-- `convertFormat` over `hd`, the datum of a value the target format holds. -/
def convertBy (hd : Int → Int → Option UnpackedFloat) : UnpackedFloat → Option UnpackedFloat
  | .zero sg => some (.zero sg)
  | .finite sg m q _ => hd (sg.apply m) q
  | _ => none

/-- `ofInt?` over `hd`, the datum of a value the target format holds. -/
def ofIntBy (hd : Int → Int → Option UnpackedFloat) (n : Int) : Option UnpackedFloat :=
  if n = 0 then some (.zero .positive) else hd n 0

/-! ## The operations at a format with a field of 1 -/

/-- The datum of the format `(p, e)` whose value is `a·2^q`, where that value is not zero and the
format holds it (`held?`). -/
def tnHeld? (p e : Nat) : Int → Int → Option UnpackedFloat := heldBy (tnNearest? p e)

/-- `/Float` at the format `(p, e)` (`quot?`): at two finite nonzero data `a·2^qa` and `b·2^qb`
whose quotient is at most the format's largest finite datum `M·2^Q` in magnitude, the quotient
`|a|·2^qa / (|b|·2^qb)` rounded (`tnRound`), negative where the two signs differ. `none` elsewhere. -/
def tnQuot? (p e : Nat) (u v : UnpackedFloat) : Option UnpackedFloat :=
  match exact u, exact v, (tnMax? p e).bind exact with
  | some (a, qa), some (b, qb), some (M, Q) =>
    if a ≠ 0 ∧ b ≠ 0 ∧ cmpScaled a.natAbs qa (M * b.natAbs) (Q + qb) ≠ .gt then
      tnRound p e (if decide (a < 0) == decide (b < 0) then .positive else .negative)
        (a.natAbs * 2 ^ (qa - min qa qb).toNat) (b.natAbs * 2 ^ (qb - min qa qb).toNat)
    else none
  | _, _, _ => none

/-- `sqrtFloat` at the format `(p, e)` (`sqrt?`): at a positive finite datum `m·2^q`, written
`m'·2^q'` with `q'` even, the datum `r·2^(q'/2)` where `m' = r²` and the format holds that value.
`none` elsewhere. -/
def tnSqrt? (p e : Nat) : UnpackedFloat → Option UnpackedFloat
  | .finite .positive m q _ =>
    let m' := if q % 2 = 0 then m else 2 * m
    let q' := if q % 2 = 0 then q else q - 1
    if Nat.sqrt m' * Nat.sqrt m' = m' then tnHeld? p e (Nat.sqrt m' : Nat) (q' / 2) else none
  | _ => none

end KCore.KFloat
