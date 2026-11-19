/-
  KCore. The meaning of the interpreted hooked symbols on ground values (KCORE-SPEC.md §6).
  Frozen layer. Bool's and Int's operations, `==K` and `=/=K`, finite maps (`.Map`, `|->`, `_Map_`,
  update, removal, lookup, `in_keys`, size, `keys`, `removeAll`) and finite sets (`.Set`,
  `SetItem`, `_Set_` and `|Set` (union), `intersectSet`, `Set:difference`, `Set:in`, `<=Set`,
  `size`) and finite lists (`.List`, `ListItem`, `_List_`, `pushList`, `L[I]`, `range`, `inList`,
  `size`, and `L[I <- V]`, `makeList`, `updateList`, `fillList` on the ranges the text describes),
  and FLOAT's operations where K's text states their value (FloatDomain.lean): `+ - * / %Float`, `--Float`,
  `absFloat`, floor, ceil, trunc, `sqrtFloat`, `roundFloat`, `Int2Float`, the comparisons, `isNaN`,
  `isInfinite`, precision, exponent width, `maxValueFloat`, `minValueFloat`; STRING's operations on
  Strings (StringDomain.lean): `+String`, `lengthString`, `ordChar`, `substrString`, `findString`,
  `rfindString`, `findChar`, `rfindChar`, `String2Bool`, `String2Int`, `String2Base`, `replace`,
  `replaceFirst`, `countAllOccurrences` and `replaceAll` (at a non-empty needle), the six comparisons, `chrChar`, `Int2String`, `Bool2String`; BYTES' operations on
  Bytes: `Bytes2Int`, `B[I]`, `B[I <- V]`, `substrBytes`, `replaceAtBytes`, `memsetBytes`,
  `padRightBytes`, `padLeftBytes`, `reverseBytes`, `lengthBytes`, `+Bytes`, `.Bytes`, `Int2Bytes`
  (String and Bytes literals are values in every definition, `dvOK`); RANGEMAP's operations on
  range maps (RangeMapHooks.lean): `.RangeMap`, `r|->`, `_RangeMap_`, lookup, `orDefault`,
  `find_range`, update, `[_ <- undef]`, `-RangeMap`, `updateRangeMap`, `removeAll`, `in_keys`,
  `size`, `<=RangeMap`, `keys`. Every other builtin hook
  is a parameter (Builtins.lean): `Set:choice` (an unspecified element), RANGEMAP's
  `keys_list`, `values` and `choice`, the K-IO hooks; STRING's and BYTES' where K's documentation leaves the
  value open (`Float2String`, `String2Float`, `FloatFormat`, `Base2String`, `Bytes2String`, `String2Bytes`, `Bytes2Hex`,
  `decodeBytes`, `encodeBytes`, `Int2Bytes` without a length, the deprecated `categoryChar`,
  `directionalityChar`, `newUUID`); and FLOAT's where K's documentation
  leaves the value open (`Float2Int` at NaN and ∞, `signFloat` at NaN, `exponentFloat`, `minFloat`
  and `maxFloat` at NaN and ±0) or IEEE 754 only recommends the operation (exp, log, the
  trigonometric ones, `^Float`, `rootFloat`).

  A registry hook's value has the library's collection sort (`Map`, `Set`, `List`); its arguments
  are read by their entries, whatever their collection sort. A definition's own hooked symbol
  implemented by a registry hook (`_AccountCellMap_`, `MAP.concat`) takes its declared result
  sort (`Semantics.paramVal`, `GroundTerm.withSort`).

  `hook f vs`: `none` if `f` is not an interpreted symbol; `some none` if it is, and is undefined
  at `vs` (division by zero, a lookup off the keys, the union of maps with a common key, arguments
  of the wrong shape); `some (some v)` its value. Every argument is a value (evaluation is strict,
  Evaluation.lean).

  This function is the standard model of the domain theories: Γ's domains (`ΓDomains`,
  Faithful.lean) get, for each interpreted symbol, the graph of `hook` on ground values of its
  argument sorts, ⊥ where it is undefined. So the domain theories
  are not written by hand symbol by symbol; they are read off this one function, which is what a
  reviewer checks against K's documented meaning of each hook (domains.md): Int is ℤ with
  truncating `/Int` and `%Int` and Euclidean `divInt` and `modInt`, all undefined at divisor 0
  (domains.md:1233-1237: t-division and Euclidean division, "Division by zero is `#False`"),
  `X <<Int N` the product X · 2^N and `X >>Int N` the arithmetic right shift, the floor of X / 2^N,
  both undefined at a negative N (domains.md 1238-1242), `log2Int(X)` the index of the highest bit
  set of a positive X, undefined at X ≤ 0 (1298-1301), `bitRangeInt` and `signExtendBitRangeInt`
  the right sides of their equations (1438, 1440), which apply the shifts, so undefined at a
  negative index or length and the second also at length 0, `A ^%Int B C` undefined at C = 0
  and elsewhere `(A ^Int B) %Int C` (equal in value to it, 1229-1231) at B ≥ 0, the truncating
  remainder of the power, `A ^Int B` the power at B ≥ 0 (1228);
  a Float is a datum of its format (represented as IEEE 754 represents it, domains.md 1481-1490), an
  arithmetic result the exact result rounded to nearest, ties to even, where the text states it
  (FloatDomain.lean; no value at an infinity, NaN or zero divisor, at a zero result the text gives
  no sign, above the format's largest finite value, or where `roundFloat` or `Int2Float` would have
  to round); a String is a sequence of code points and a Bytes value one of bytes, positions
  counted from 0; Bool is the two-element Boolean
  algebra; `==K` is equality of values; a Map is a finite function
  from KItem to KItem, `_Map_` the union of two maps with disjoint keys.

  Where `hook` gives no value, the text says either that there is none (`#False`, `#Bottom`: division
  by zero, a shift by a negative amount, `log2Int` of a number not above 0, a bit range at a
  negative index or length, `^%Int` at a zero modulus, a lookup off the keys, `_Map_` and `_Set_` on a common key or member, `B[I]`, `B[I <- V]`,
  `substrBytes`, `padRightBytes`, `padLeftBytes` and `replaceAtBytes` off their stated ranges), and Γ
  states ⊥; or nothing of the value (an index off a String or a List, a binary Float operation on two
  formats, a Float operation off the region the text states, a format without a model, a string off
  a conversion's syntax, …: `silentTable`), and Γ
  states the interpretation's value there.
-/
import KcoreSpec.Value
import KcoreSpec.StringDomain
import KcoreSpec.FloatThin

set_option autoImplicit false

namespace KCore

/-! ## Maps -/

def hasKey (k : GroundTerm) (m : Entries) : Bool := m.any fun e => GroundTerm.cmp k e.1 == .eq

/-- `m[k <- v]`: replace the entry of k, or insert it in key order. -/
def insertE (k v : GroundTerm) : Entries → Entries
  | [] => [(k, v)]
  | (k', v') :: es => match GroundTerm.cmp k k' with
    | .lt => (k, v) :: (k', v') :: es
    | .eq => (k, v) :: es
    | .gt => (k', v') :: insertE k v es

def eraseK (k : GroundTerm) : Entries → Entries
  | [] => []
  | (k', v') :: es => if GroundTerm.cmp k k' == .eq then es else (k', v') :: eraseK k es

def findK (k : GroundTerm) : Entries → Option GroundTerm
  | [] => none
  | (k', v') :: es => if GroundTerm.cmp k k' == .eq then some v' else findK k es

def addNew (k v : GroundTerm) (m : Entries) : Option Entries :=
  if hasKey k m then none else some (insertE k v m)

/-- `_Map_`: the union of two maps, defined when their keys are disjoint. -/
def union : Entries → Entries → Option Entries
  | [], m => some m
  | (k, v) :: es, m => (union es m).bind (addNew k v)

/-! ## Sets: elements strictly increasing in `GroundTerm.cmp` -/

def memS (k : GroundTerm) (s : List GroundTerm) : Bool := s.any fun e => GroundTerm.cmp k e == .eq

/-- Insert an element in order (no change if present). -/
def insertS (k : GroundTerm) : List GroundTerm → List GroundTerm
  | [] => [k]
  | e :: es => match GroundTerm.cmp k e with
    | .lt => k :: e :: es
    | .eq => e :: es
    | .gt => e :: insertS k es

def unionS (a b : List GroundTerm) : List GroundTerm := a.foldr insertS b

/-- `_Set_`: the union of two sets with no member in common, undefined where they share one. -/
def concatS (a b : List GroundTerm) : Option (List GroundTerm) :=
  if a.all (fun x => !memS x b) then some (unionS a b) else none

/-- The keys of a map, in order (they already are). -/
def keysOf (m : Entries) : List GroundTerm := m.map (·.1)

/-! ## The hooks -/

def bool (b : Bool) : GroundTerm := .dv Srt.bool (.bool b)

def asBool : GroundTerm → Option Bool
  | .dv s (.bool b) => if s == Srt.bool then some b else none
  | _ => none

def int2 (vs : List GroundTerm) (f : Int → Int → Option GroundTerm) : Option GroundTerm :=
  match vs with
  | [a, b] => (asInt a).bind fun x => (asInt b).bind fun y => f x y
  | _ => none

def bool2 (vs : List GroundTerm) (f : Bool → Bool → Bool) : Option GroundTerm :=
  match vs with
  | [a, b] => (asBool a).bind fun x => (asBool b).map fun y => bool (f x y)
  | _ => none

def nonzero (y : Int) (r : Int) : Option GroundTerm := if y = 0 then none else some (int r)

/-- A hook of three Int arguments. -/
def intArgs3 (vs : List GroundTerm) (f : Int → Int → Int → Option GroundTerm) : Option GroundTerm :=
  match vs with
  | [a, b, c] => (asInt a).bind fun x => (asInt b).bind fun y => (asInt c).bind fun z => f x y z
  | _ => none

/-- `bitRangeInt(x, idx, len)` at `idx ≥ 0` and `len ≥ 0`: the right side of its equation
(domains.md 1438), `(x >>Int idx) modInt (1 <<Int len)`, with the shifts' values. -/
def bitRangeVal (x i l : Int) : Int := (x.fdiv (2 ^ i.toNat)).emod (2 ^ l.toNat)

/-- `signExtendBitRangeInt(x, idx, len)` at `idx ≥ 0` and `len ≥ 1`: the right side of its equation
(domains.md 1440), `(bitRangeInt(x, idx, len) +Int (1 <<Int (len -Int 1))) modInt (1 <<Int len)
-Int (1 <<Int (len -Int 1))`. -/
def signExtVal (x i l : Int) : Int :=
  (bitRangeVal x i l + 2 ^ (l - 1).toNat).emod (2 ^ l.toNat) - 2 ^ (l - 1).toNat

def boolHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(boolNot, fun vs => match vs with | [a] => (asBool a).map fun x => bool !x | _ => none),
   (boolAnd, fun vs => bool2 vs (· && ·)), (boolAndThen, fun vs => bool2 vs (· && ·)),
   (boolOr, fun vs => bool2 vs (· || ·)), (boolOrElse, fun vs => bool2 vs (· || ·)),
   (boolXor, fun vs => bool2 vs (· != ·)), (boolImplies, fun vs => bool2 vs fun x y => !x || y),
   (boolEq, fun vs => bool2 vs (· == ·)), (boolNe, fun vs => bool2 vs (· != ·))]

def intHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(intAdd, fun vs => int2 vs fun x y => some (int (x + y))),
   (intSub, fun vs => int2 vs fun x y => some (int (x - y))),
   (intMul, fun vs => int2 vs fun x y => some (int (x * y))),
   (intTDiv, fun vs => int2 vs fun x y => nonzero y (x.tdiv y)),
   (intTMod, fun vs => int2 vs fun x y => nonzero y (x.tmod y)),
   (intEDiv, fun vs => int2 vs fun x y => nonzero y (x.ediv y)),
   (intEMod, fun vs => int2 vs fun x y => nonzero y (x.emod y)),
   (intMin, fun vs => int2 vs fun x y => some (int (min x y))),
   (intMax, fun vs => int2 vs fun x y => some (int (max x y))),
   (intLt, fun vs => int2 vs fun x y => some (bool (decide (x < y)))),
   (intLe, fun vs => int2 vs fun x y => some (bool (decide (x ≤ y)))),
   (intGt, fun vs => int2 vs fun x y => some (bool (decide (x > y)))),
   (intGe, fun vs => int2 vs fun x y => some (bool (decide (x ≥ y)))),
   (intEq, fun vs => int2 vs fun x y => some (bool (decide (x = y)))),
   (intNe, fun vs => int2 vs fun x y => some (bool (decide (x ≠ y)))),
   (intAbs, fun vs => match vs with | [a] => (asInt a).map fun x => int x.natAbs | _ => none),
   -- `freshInt` has no hook in the text: it is a total function with the one equation
   -- freshInt(I) => I (domains.md:1456-1457; hw-h1-fun.kore:158, :1447-1464). It is listed here
   -- because its graph at values is that equation.
   (freshInt, fun vs => match vs with | [a] => (asInt a).map int | _ => none),
   (intShr, fun vs => int2 vs fun x n => if n < 0 then none else some (int (x.fdiv (2 ^ n.toNat)))),
   (intShl, fun vs => int2 vs fun x n => if n < 0 then none else some (int (x * 2 ^ n.toNat))),
   (intLog2, fun vs => match vs with
     | [a] => (asInt a).bind fun x => if 0 < x then some (int x.toNat.log2) else none
     | _ => none),
   (intPowMod, fun vs => intArgs3 vs fun a b m =>
     if b < 0 ∨ m = 0 then none
     else some (int ((a ^ b.toNat).tmod m))),
   (intBitRange, fun vs => intArgs3 vs fun x i l => if i < 0 ∨ l < 0 then none else some (int (bitRangeVal x i l))),
   (intSignExtBitRange, fun vs =>
     intArgs3 vs fun x i l => if i < 0 ∨ l < 1 then none else some (int (signExtVal x i l))),
   (intPow, fun vs => int2 vs fun a b => if b < 0 then none else some (int (a ^ b.toNat)))]

def kHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(kEq, fun vs => match vs with | [a, b] => some (bool (GroundTerm.cmp a b == .eq)) | _ => none),
   (kNe, fun vs => match vs with | [a, b] => some (bool (GroundTerm.cmp a b != .eq)) | _ => none)]

def mapHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(mapUnit, fun vs => match vs with | [] => some (.map Srt.map []) | _ => none),
   (mapElem, fun vs => match vs with | [k, v] => some (.map Srt.map [(k, v)]) | _ => none),
   (mapConcat, fun vs => match vs with
     | [.map _ a, .map _ b] => (union a b).map (.map Srt.map) | _ => none),
   (mapUpdate, fun vs => match vs with
     | [.map _ m, k, v] => some (.map Srt.map (insertE k v m)) | _ => none),
   (mapRemove, fun vs => match vs with
     | [.map _ m, k] => some (.map Srt.map (eraseK k m)) | _ => none),
   (mapLookup, fun vs => match vs with | [.map _ m, k] => findK k m | _ => none),
   (mapLookupOrDefault, fun vs => match vs with
     | [.map _ m, k, d] => some ((findK k m).getD d) | _ => none),
   (mapInKeys, fun vs => match vs with | [k, .map _ m] => some (bool (hasKey k m)) | _ => none),
   (mapSize, fun vs => match vs with | [.map _ m] => some (int m.length) | _ => none),
   (mapRemoveAll, fun vs => match vs with
     | [.map _ m, .set _ ks] => some (.map Srt.map (m.filter fun e => !memS e.1 ks)) | _ => none),
   (mapKeys, fun vs => match vs with | [.map _ m] => some (.set Srt.set (keysOf m)) | _ => none)]

/-- Sets. `_Set_` is the union of two disjoint sets, undefined where they share a member (as
`_Map_` is undefined where two maps share a key; KCORE-SPEC.md Q29); `|Set` is the union of any
two sets. `<=Set` is true where every member of the first set is a member of the second
(domains.md 780-786: inclusion; the sentence at 782 speaks of two different sets, where a subset is
a strict subset), so true at two equal sets. -/
def setHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(setUnit, fun vs => match vs with | [] => some (.set Srt.set []) | _ => none),
   (setElem, fun vs => match vs with | [k] => some (.set Srt.set [k]) | _ => none),
   (setConcat, fun vs => match vs with
     | [.set _ a, .set _ b] => (concatS a b).map (.set Srt.set) | _ => none),
   (setUnion, fun vs => match vs with
     | [.set _ a, .set _ b] => some (.set Srt.set (unionS a b)) | _ => none),
   (setIntersect, fun vs => match vs with
     | [.set _ a, .set _ b] => some (.set Srt.set (a.filter (memS · b))) | _ => none),
   (setDifference, fun vs => match vs with
     | [.set _ a, .set _ b] => some (.set Srt.set (a.filter (!memS · b))) | _ => none),
   (setIn, fun vs => match vs with | [k, .set _ a] => some (bool (memS k a)) | _ => none),
   (setInclusion, fun vs => match vs with
     | [.set _ a, .set _ b] => some (bool (a.all (memS · b)))
     | _ => none),
   (setSize, fun vs => match vs with | [.set _ a] => some (int a.length) | _ => none)]

/-! ## Lists -/

/-- The index of `L[I]`: from the front for `0 ≤ I`, from the back for `I < 0` (`-1` is the
last element); `none` out of range. -/
def listIndex (n : Nat) (i : Int) : Option Nat :=
  if 0 ≤ i then (if i < n then some i.toNat else none)
  else if -(n : Int) ≤ i then some (n - i.natAbs) else none

/-- `range(L, a, b)`: L without its first a and its last b elements; `none` if a or b is negative
or they overlap. -/
def listRangeOf (es : List GroundTerm) (a b : Int) : Option (List GroundTerm) :=
  if 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ es.length then
    some ((es.drop a.toNat).take (es.length - a.toNat - b.toNat))
  else none

/-- Lists: `.List`, `ListItem`, `_List_` (concatenation, total), `pushList`, `L[I]`, `range`,
`inList`, `size`, and where the text describes them (domains.md 974-975, 984-985, 993-995,
1003-1004) `L[I <- V]` at an index `0 ≤ I < size` (the list with `V` at `I`), `makeList(N, V)` at
`N ≥ 0` (`N` copies of `V`), `updateList(D, I, S)` at `0 ≤ I` and `I + size(S) ≤ size(D)` (`D` with
the elements from `I` replaced by `S`'s) and `fillList(D, I, N, V)` at `0 ≤ I`, `0 ≤ N` and
`I + N ≤ size(D)` (`D` with the `N` elements from `I` replaced by `V`). -/
def listHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(listConcat, fun vs => match vs with
     | [.list _ a, .list _ b] => some (.list Srt.list (a ++ b)) | _ => none),
   (listUnit, fun vs => match vs with | [] => some (.list Srt.list []) | _ => none),
   (listElem, fun vs => match vs with | [k] => some (.list Srt.list [k]) | _ => none),
   (listPush, fun vs => match vs with
     | [k, .list _ a] => some (.list Srt.list (k :: a)) | _ => none),
   (listGet, fun vs => match vs with
     | [.list _ a, i] => (asInt i).bind fun i => (listIndex a.length i).bind (a[·]?) | _ => none),
   (listRange, fun vs => match vs with
     | [.list _ a, x, y] => (asInt x).bind fun x => (asInt y).bind fun y =>
         (listRangeOf a x y).map (.list Srt.list)
     | _ => none),
   (listIn, fun vs => match vs with
     | [k, .list _ a] => some (bool (a.any fun e => GroundTerm.cmp k e == .eq)) | _ => none),
   (listSize, fun vs => match vs with | [.list _ a] => some (int a.length) | _ => none),
   (listSet, fun vs => match vs with
     | [.list _ a, i, v] => (asInt i).bind fun i =>
         if 0 ≤ i ∧ i < a.length then some (.list Srt.list (a.set i.toNat v)) else none
     | _ => none),
   (listMake, fun vs => match vs with
     | [n, v] => (asInt n).bind fun n => if 0 ≤ n then some (.list Srt.list (List.replicate n.toNat v)) else none
     | _ => none),
   (listUpdateAll, fun vs => match vs with
     | [.list _ d, i, .list _ s] => (asInt i).bind fun i =>
         if 0 ≤ i ∧ i + s.length ≤ d.length then
           some (.list Srt.list (d.take i.toNat ++ s ++ d.drop (i.toNat + s.length)))
         else none
     | _ => none),
   (listFill, fun vs => match vs with
     | [.list _ d, i, n, v] => (asInt i).bind fun i => (asInt n).bind fun n =>
         if 0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ d.length then
           some (.list Srt.list (d.take i.toNat ++ List.replicate n.toNat v ++ d.drop (i.toNat + n.toNat)))
         else none
     | _ => none)]

/-! ## Floats -/

open Float.Model in
/-- A Float value: its format `(p, e)`, the format's model, and its datum. -/
def asFloat : GroundTerm → Option (Nat × Nat × Format × UnpackedFloat)
  | .dv s (.float p e b) =>
    if s == Srt.float then (KFloat.spec? p e).map fun sp => (p, e, sp, KFloat.unpackBits sp b) else none
  | _ => none

open Float.Model in
/-- The Float value of format `(p, e)` (model `sp`) of the datum `u`, rounded for it. -/
def floatV (p e : Nat) (sp : Format) (u : UnpackedFloat) : GroundTerm :=
  .dv Srt.float (.float p e (KFloat.packBits sp u))

open Float.Model in
/-- An operation on one Float, in its format; undefined where the operation gives no datum. -/
def fl1 (op : Format → UnpackedFloat → Option UnpackedFloat) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a] => (asFloat a).bind fun (p, e, sp, u) => (op sp u).map (floatV p e sp)
  | _ => none

open Float.Model in
/-- An operation on two Floats of one format, in that format; undefined on two formats and where
the operation gives no datum. -/
def fl2 (op : Format → UnpackedFloat → UnpackedFloat → Option UnpackedFloat) (vs : List GroundTerm) :
    Option GroundTerm :=
  match vs with
  | [a, b] => (asFloat a).bind fun (p, e, sp, u) => (asFloat b).bind fun (p', e', _, v) =>
      if p = p' ∧ e = e' then (op sp u v).map (floatV p e sp) else none
  | _ => none

open Float.Model in
/-- A Float value's datum, without its format: at a format with a model (`asFloat`), and at a format
of precision 1 and at least 2 exponent bits (`KFloat.thinUnpack`); none at a format of one exponent
bit. -/
def asDatum : GroundTerm → Option UnpackedFloat
  | .dv s (.float p e b) =>
    if s == Srt.float then
      match KFloat.spec? p e with
      | some sp => some (KFloat.unpackBits sp b)
      | none => if p = 1 ∧ 2 ≤ e then some (KFloat.thinUnpack e b) else none
    else none
  | _ => none

open Float.Model in
/-- A test of one Float's datum (`asDatum`). -/
def flTest (t : UnpackedFloat → Bool) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a] => (asDatum a).map fun u => bool (t u)
  | _ => none

open Float.Model in
/-- A test of one Float of a format with a model (`asFloat`): `isInfinite` there, whose equation
(domains.md 1673) reads `maxValueFloat` and `--Float`, which compute at such a format (`tflInf` is
its counterpart at a format `thinAt` names). -/
def flTestM (t : UnpackedFloat → Bool) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a] => (asFloat a).map fun (_, _, _, u) => bool (t u)
  | _ => none

/-- A comparison of two Floats of any formats, by their exact values (`asDatum`, `KFloat.cmpExact`). -/
def flCmp (t : Option Ordering → Bool) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a, b] => (asDatum a).bind fun u => (asDatum b).map fun v => bool (t (KFloat.cmpExact u v))
  | _ => none

/-- A property of a Float's format `(p, e)`, read off the value: `p` and `e` positive (domains.md
1469-1476, `pNxM`), a format with a field of 1 included (`KFloat.thinOK`). -/
def flFmt (f : Nat → Nat → Int) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [.dv s (.float p e _)] => if s == Srt.float ∧ 1 ≤ p ∧ 1 ≤ e then some (int (f p e)) else none
  | _ => none

open Float.Model in
/-- A datum of the format `(p, e)` given by two Ints; undefined at a format without a model. -/
def flAt (op : Format → UnpackedFloat) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [x, y] => (asInt x).bind fun p => (asInt y).bind fun e =>
      (KFloat.spec? p.toNat e.toNat).map fun sp => floatV p.toNat e.toNat sp (op sp)
  | _ => none

open Float.Model in
/-- A datum converted to the format `(p, e)` given by two Ints (`roundFloat`); undefined at a format
without a model and where the conversion gives no datum. -/
def flTo (op : Format → UnpackedFloat → Option UnpackedFloat) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a, x, y] => (asFloat a).bind fun (_, _, _, u) => (asInt x).bind fun p => (asInt y).bind fun e =>
      (KFloat.spec? p.toNat e.toNat).bind fun sp => (op sp u).map (floatV p.toNat e.toNat sp)
  | _ => none

/-- An Int converted to the format `(p, e)` given by two Ints (`Int2Float`); undefined at a format
without a model and at an Int the format does not hold (`KFloat.ofInt?`). -/
def flOfInt (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [i, x, y] => (asInt i).bind fun n => (asInt x).bind fun p => (asInt y).bind fun e =>
      (KFloat.spec? p.toNat e.toNat).bind fun sp => (KFloat.ofInt? sp n).map (floatV p.toNat e.toNat sp)
  | _ => none

/-! ### The formats with a field of 1 (FloatThin.lean)

The operations at a format with a field of 1 that has a model of its data (`KFloat.tnFormat`), on the
formats `thinAt` names: the same formulas as at a format of Lean core's model, over the rounding to
the nearest datum of the format (`KFloat.tnRound`). -/

/-- The formats with a field of 1 at which the operations below compute: precision 1 and at least
2 exponent bits. -/
def thinAt (p e : Nat) : Bool := decide (p = 1 ∧ 2 ≤ e)

open Float.Model in
/-- A Float value of a format `thinAt` names: its format `(p, e)` and its datum. -/
def asThin : GroundTerm → Option (Nat × Nat × UnpackedFloat)
  | .dv s (.float p e b) =>
    if s == Srt.float ∧ thinAt p e = true then some (p, e, KFloat.tnUnpack p e b) else none
  | _ => none

open Float.Model in
/-- The Float value of the format `(p, e)`, one with a field of 1, of its datum `u`. -/
def tnFloatV (p e : Nat) (u : UnpackedFloat) : GroundTerm := .dv Srt.float (.float p e (KFloat.tnPack p e u))

/-- `f`'s value, and `g`'s where `f` has none: an operation at a format with a model, then at a
format with a field of 1. -/
def flOr (f g : List GroundTerm → Option GroundTerm) (vs : List GroundTerm) : Option GroundTerm :=
  match f vs with
  | some v => some v
  | none => g vs

open Float.Model in
/-- An operation on one Float of a format `thinAt` names, in its format. -/
def tfl1 (op : Nat → Nat → UnpackedFloat → Option UnpackedFloat) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a] => (asThin a).bind fun (p, e, u) => (op p e u).map (tnFloatV p e)
  | _ => none

open Float.Model in
/-- An operation on two Floats of one format `thinAt` names, in that format; undefined on two
formats. -/
def tfl2 (op : Nat → Nat → UnpackedFloat → UnpackedFloat → Option UnpackedFloat) (vs : List GroundTerm) :
    Option GroundTerm :=
  match vs with
  | [a, b] => (asThin a).bind fun (p, e, u) => (asThin b).bind fun (p', e', v) =>
      if p = p' ∧ e = e' then (op p e u v).map (tnFloatV p e) else none
  | _ => none

/-- `isInfinite` at a format `thinAt` names that has a largest finite datum (`KFloat.tnMax?`), so
that `maxValueFloat` has a value there: domains.md 1673 reads both. -/
def tflInf (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a] => (asThin a).bind fun (p, e, u) => (KFloat.tnMax? p e).map fun _ => bool (KFloat.isInf u)
  | _ => none

open Float.Model in
/-- A datum of the format `(p, e)` given by two Ints, at a format `thinAt` names. -/
def tflAt (op : Nat → Nat → Option UnpackedFloat) (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [x, y] => (asInt x).bind fun p => (asInt y).bind fun e =>
      if thinAt p.toNat e.toNat = true then (op p.toNat e.toNat).map (tnFloatV p.toNat e.toNat) else none
  | _ => none

/-- `roundFloat` of a Float of any format with a datum (`asDatum`) to the format `(p, e)` given by
two Ints: at a format with a model, Lean core's conversion; at a format `thinAt` names, the datum
of the value where the format holds it. -/
def tflTo (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [a, x, y] => (asDatum a).bind fun u => (asInt x).bind fun p => (asInt y).bind fun e =>
      match KFloat.spec? p.toNat e.toNat with
      | some sp => (KFloat.convertFormat sp u).map (floatV p.toNat e.toNat sp)
      | none =>
        if thinAt p.toNat e.toNat = true then
          (KFloat.convertBy (KFloat.tnHeld? p.toNat e.toNat) u).map (tnFloatV p.toNat e.toNat)
        else none
  | _ => none

/-- `Int2Float` at a format `thinAt` names: the datum of the Int where the format holds it. -/
def tflOfInt (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [i, x, y] => (asInt i).bind fun n => (asInt x).bind fun p => (asInt y).bind fun e =>
      if thinAt p.toNat e.toNat = true then
        (KFloat.ofIntBy (KFloat.tnHeld? p.toNat e.toNat) n).map (tnFloatV p.toNat e.toNat)
      else none
  | _ => none

open KFloat in
/-- FLOAT's interpreted symbols at the formats `thinAt` names, where they have a value. -/
def thinHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(floatAdd, tfl2 fun p e => sumBy (tnNearest? p e)), (floatSub, tfl2 fun p e => diffBy (tnNearest? p e)),
   (floatMul, tfl2 fun p e => prodBy (tnNearest? p e)), (floatDiv, tfl2 tnQuot?),
   (floatRem, tfl2 fun p e => remainderBy (tnHeld? p e)),
   (floatNeg, tfl1 fun _ _ => neg?), (floatAbs, tfl1 fun _ _ => abs?),
   (floatFloor, tfl1 fun p e => roundToIntegralBy (tnHeld? p e) .down),
   (floatCeil, tfl1 fun p e => roundToIntegralBy (tnHeld? p e) .up),
   (floatTrunc, tfl1 fun p e => roundToIntegralBy (tnHeld? p e) .zero),
   (floatSqrt, tfl1 tnSqrt?), (floatIsInfinite, tflInf),
   (floatRound, tflTo), (int2Float, tflOfInt),
   (floatMaxValue, tflAt tnMax?), (floatMinValue, tflAt tnMin?)]

/-- A format `thinAt` names has a field of 1. -/
theorem thinAt_tnFormat {p e : Nat} (h : thinAt p e = true) : KFloat.tnFormat p e = true := by
  simp only [thinAt, KFloat.tnFormat, decide_eq_true_eq] at h ⊢
  omega

/-- A format `thinAt` names has no model in Lean core. -/
theorem thinAt_spec_none {p e : Nat} (h : thinAt p e = true) : KFloat.spec? p e = none := by
  simp only [thinAt, decide_eq_true_eq] at h
  unfold KFloat.spec?
  simp only [show ¬ (2 ≤ p ∧ 2 ≤ e) by omega, ↓reduceDIte]

/-- A Float of a format with a model is no Float of a format `thinAt` names. -/
theorem asThin_none_of_asFloat {a : GroundTerm} (h : (asFloat a).isSome = true) : asThin a = none := by
  match a, h with
  | .dv s (.float p e b), h =>
    simp only [asFloat] at h
    simp only [asThin]
    split
    · rename_i ht
      rw [thinAt_spec_none ht.2] at h
      simp at h
    · rfl

/-- Where `f` has a value, `flOr f g` has it. -/
theorem flOr_of_some {f g : List GroundTerm → Option GroundTerm} {vs : List GroundTerm} {v : GroundTerm}
    (h : f vs = some v) : flOr f g vs = some v := by
  simp only [flOr, h]

/-- Where `f` has no value, `flOr f g` is `g`. -/
theorem flOr_of_none {f g : List GroundTerm → Option GroundTerm} {vs : List GroundTerm}
    (h : f vs = none) : flOr f g vs = g vs := by
  simp only [flOr, h]

/-- FLOAT's interpreted symbols, each with a value where K's text states one (FloatDomain.lean:
the exact result rounded to nearest, ties to even, off the infinities, NaN, a zero divisor, the
zero results the text gives no sign and the values above the format's largest finite one;
`roundFloat` and `Int2Float` at a value the format holds). A binary operation on two formats is
undefined (K's documentation leaves it open; the symbols are not total); a comparison of two
formats compares the exact values. Each operation that computes a Float, and `isInfinite`, is
paired by `flOr` with its entry of `thinHooks`: at a format with a model Lean core's, at a format
`thinAt` names the same formulas over the rounding to the nearest datum of that format. -/
def floatHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(floatAdd, flOr (fl2 KFloat.sum?) (tfl2 fun p e => KFloat.sumBy (KFloat.tnNearest? p e))),
   (floatSub, flOr (fl2 KFloat.diff?) (tfl2 fun p e => KFloat.diffBy (KFloat.tnNearest? p e))),
   (floatMul, flOr (fl2 KFloat.prod?) (tfl2 fun p e => KFloat.prodBy (KFloat.tnNearest? p e))),
   (floatDiv, flOr (fl2 KFloat.quot?) (tfl2 KFloat.tnQuot?)),
   (floatRem, flOr (fl2 KFloat.remainder) (tfl2 fun p e => KFloat.remainderBy (KFloat.tnHeld? p e))),
   (floatNeg, flOr (fl1 fun _ => KFloat.neg?) (tfl1 fun _ _ => KFloat.neg?)),
   (floatAbs, flOr (fl1 fun _ => KFloat.abs?) (tfl1 fun _ _ => KFloat.abs?)),
   (floatFloor, flOr (fl1 fun s => KFloat.roundToIntegral s .down)
     (tfl1 fun p e => KFloat.roundToIntegralBy (KFloat.tnHeld? p e) .down)),
   (floatCeil, flOr (fl1 fun s => KFloat.roundToIntegral s .up)
     (tfl1 fun p e => KFloat.roundToIntegralBy (KFloat.tnHeld? p e) .up)),
   (floatTrunc, flOr (fl1 fun s => KFloat.roundToIntegral s .zero)
     (tfl1 fun p e => KFloat.roundToIntegralBy (KFloat.tnHeld? p e) .zero)),
   (floatSqrt, flOr (fun vs => match vs with
     | [a] => (asFloat a).bind fun (p, e, sp, u) => (KFloat.sqrt? sp u).map (floatV p e sp) | _ => none)
     (tfl1 KFloat.tnSqrt?)),
   (floatLe, flCmp fun o => o == some .lt || o == some .eq), (floatLt, flCmp fun o => o == some .lt),
   (floatGe, flCmp fun o => o == some .gt || o == some .eq), (floatGt, flCmp fun o => o == some .gt),
   (floatEq, flCmp fun o => o == some .eq), (floatNe, flCmp fun o => o != some .eq),
   (floatIsNaN, flTest KFloat.isNaN), (floatIsInfinite, flOr (flTestM KFloat.isInf) tflInf),
   (floatPrecision, flFmt fun p _ => p), (floatExponentBits, flFmt fun _ e => e),
   (floatRound, flOr (flTo KFloat.convertFormat) tflTo), (int2Float, flOr flOfInt tflOfInt),
   (floatMaxValue, flOr (flAt KFloat.maxValue) (tflAt KFloat.tnMax?)),
   (floatMinValue, flOr (flAt KFloat.minValue) (tflAt KFloat.tnMin?))]

/-! ## Strings and Bytes -/

/-- A String value: its code points. -/
def asStr : GroundTerm → Option (List Char)
  | .dv s (.tok t) => if s == Srt.string then some t.toList else none
  | _ => none

/-- The String value of the code points `cs`. -/
def strV (cs : List Char) : GroundTerm := .dv Srt.string (.tok (String.ofList cs))

/-- A Bytes value: its bytes, one character each. -/
def asBytes : GroundTerm → Option (List Char)
  | .dv s (.tok t) => if s == Srt.bytes then some t.toList else none
  | _ => none

/-- The Bytes value of the bytes `cs`. -/
def bytesV (cs : List Char) : GroundTerm := .dv Srt.bytes (.tok (String.ofList cs))

/-- An Endianness value: `BE` (most significant byte first) is true, `LE` false. -/
def asEndian : GroundTerm → Option Bool
  | .ctor f [] => if f == bigEndianBytes then some true else if f == littleEndianBytes then some false else none
  | _ => none

/-- A Signedness value: `Signed` is true, `Unsigned` false. -/
def asSigned : GroundTerm → Option Bool
  | .ctor f [] => if f == signedBytes then some true else if f == unsignedBytes then some false else none
  | _ => none

/-- A test of two Strings. -/
def str2 (vs : List GroundTerm) (f : List Char → List Char → Bool) : Option GroundTerm :=
  match vs with
  | [a, b] => (asStr a).bind fun x => (asStr b).map fun y => bool (f x y)
  | _ => none

/-- STRING's interpreted symbols (StringDomain.lean). -/
def stringHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(stringConcat, fun vs => match vs with
     | [a, b] => (asStr a).bind fun x => (asStr b).map fun y => strV (x ++ y) | _ => none),
   (stringLength, fun vs => match vs with | [a] => (asStr a).map fun x => int x.length | _ => none),
   (stringOrd, fun vs => match vs with | [a] => (asStr a).bind fun x => (KStr.ord x).map fun n => int n | _ => none),
   (stringSubstr, fun vs => match vs with
     | [a, i, j] => (asStr a).bind fun x => (asInt i).bind fun i => (asInt j).bind fun j => (KStr.substrString x i j).map strV
     | _ => none),
   (stringFind, fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i => (KStr.find x y i).map int
     | _ => none),
   (stringRfind, fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i => (KStr.rfind x y i).map int
     | _ => none),
   (stringFindChar, fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i =>
         (KStr.findChar x y i).map int
     | _ => none),
   (stringRfindChar, fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i =>
         (KStr.rfindChar x y i).map int
     | _ => none),
   (string2Bool, fun vs => match vs with | [a] => (asStr a).bind fun x => (KStr.toBool x).map bool | _ => none),
   (string2Int, fun vs => match vs with | [a] => (asStr a).bind fun x => (KStr.toInt x).map int | _ => none),
   (string2Base, fun vs => match vs with
     | [a, b] => (asStr a).bind fun x => (asInt b).bind fun b => (KStr.toIntBase x b).map int | _ => none),
   (stringReplace, fun vs => match vs with
     | [a, b, r, k] => (asStr a).bind fun x => (asStr b).bind fun y => (asStr r).bind fun z => (asInt k).bind fun k =>
         (KStr.replace x y z k).map strV
     | _ => none),
   (stringReplaceFirst, fun vs => match vs with
     | [a, b, r] => (asStr a).bind fun x => (asStr b).bind fun y => (asStr r).map fun z => strV (KStr.replaceFirst x y z)
     | _ => none),
   (stringCountAll, fun vs => match vs with
     | [a, b] => (asStr a).bind fun x => (asStr b).bind fun y => (KStr.countAll x y).map fun k => int k
     | _ => none),
   (stringReplaceAll, fun vs => match vs with
     | [a, b, r] => (asStr a).bind fun x => (asStr b).bind fun y => (asStr r).bind fun z =>
         (KStr.replaceAll x y z).map strV
     | _ => none),
   (stringEq, fun vs => str2 vs fun x y => x == y), (stringNe, fun vs => str2 vs fun x y => x != y),
   (stringLt, fun vs => str2 vs KStr.lexLt), (stringLe, fun vs => str2 vs fun x y => !KStr.lexLt y x),
   (stringGt, fun vs => str2 vs fun x y => KStr.lexLt y x), (stringGe, fun vs => str2 vs fun x y => !KStr.lexLt x y),
   (stringChr, fun vs => match vs with | [i] => (asInt i).bind fun x => (KStr.chr x).map strV | _ => none),
   (int2String, fun vs => match vs with | [i] => (asInt i).map fun x => strV (intRepr x).toList | _ => none),
   (bool2String, fun vs => match vs with | [b] => (asBool b).map fun x => strV (boolRepr x).toList | _ => none)]

/-- BYTES' interpreted symbols (StringDomain.lean). -/
def bytesHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(bytes2Int, fun vs => match vs with
     | [b, e, s] => (asBytes b).bind fun x => (asEndian e).bind fun be => (asSigned s).map fun sg =>
         int (KBytes.toInt x be sg)
     | _ => none),
   (bytesUpdate, fun vs => match vs with
     | [b, i, v] => (asBytes b).bind fun x => (asInt i).bind fun i => (asInt v).bind fun v =>
         (KBytes.update x i v).map bytesV
     | _ => none),
   (bytesGet, fun vs => match vs with
     | [b, i] => (asBytes b).bind fun x => (asInt i).bind fun i => (KBytes.get x i).map int | _ => none),
   (bytesSubstr, fun vs => match vs with
     | [b, i, j] => (asBytes b).bind fun x => (asInt i).bind fun i => (asInt j).bind fun j =>
         (KStr.substr x i j).map bytesV
     | _ => none),
   (bytesReplaceAt, fun vs => match vs with
     | [d, i, s] => (asBytes d).bind fun x => (asInt i).bind fun i => (asBytes s).bind fun y =>
         (KBytes.replaceAt x i y).map bytesV
     | _ => none),
   (bytesMemset, fun vs => match vs with
     | [d, i, n, v] => (asBytes d).bind fun x => (asInt i).bind fun i => (asInt n).bind fun n => (asInt v).bind fun v =>
         (KBytes.memset x i n v).map bytesV
     | _ => none),
   (bytesPadRight, fun vs => match vs with
     | [b, l, v] => (asBytes b).bind fun x => (asInt l).bind fun l => (asInt v).bind fun v =>
         (KBytes.padRight x l v).map bytesV
     | _ => none),
   (bytesPadLeft, fun vs => match vs with
     | [b, l, v] => (asBytes b).bind fun x => (asInt l).bind fun l => (asInt v).bind fun v =>
         (KBytes.padLeft x l v).map bytesV
     | _ => none),
   (bytesReverse, fun vs => match vs with | [b] => (asBytes b).map fun x => bytesV x.reverse | _ => none),
   (bytesLength, fun vs => match vs with | [b] => (asBytes b).map fun x => int x.length | _ => none),
   (bytesConcat, fun vs => match vs with
     | [a, b] => (asBytes a).bind fun x => (asBytes b).map fun y => bytesV (x ++ y) | _ => none),
   (bytesEmpty, fun vs => match vs with | [] => some (bytesV []) | _ => none),
   (int2Bytes, fun vs => match vs with
     | [l, v, e] => (asInt l).bind fun l => (asInt v).bind fun v => (asEndian e).bind fun be =>
         (KBytes.ofInt l v be).map bytesV
     | _ => none)]

/-- `ite(C, A, B)`: A if C is true, B if C is false, at every sort of A and B: domains.md:2314-2317
describes the polymorphic conditional so ("If the first argument evaluates to `true`, the second
argument is returned. Otherwise, the third argument is returned"), of every instance; the text's two
equations are stated at the instance of sort K only (2357-2358) and agree with it. -/
def iteHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(kIte, fun vs => match vs with
     | [c, x, y] => (asBool c).map fun b => if b then x else y | _ => none)]

/-! ## Range maps

RANGEMAP's fifteen interpreted symbols, on the carrier of `CollKind.rangeMap` (`rangesOK`,
Value.lean): fourteen in `rangeMapHooks`, `keys` in `rangeMapKeysHooks`. What the text states of
each, why `keys` stands apart, and the carrier's lemmas: RangeMapHooks.lean. -/

/-- An interval `[a, b)` with its value. -/
abbrev RmTriple := Int × Int × GroundTerm

/-- The entries as triples, where every key is a proper range. -/
def rmTriples (m : Entries) : Option (List RmTriple) :=
  m.mapM fun (k, v) => (asRange k).map fun (a, b) => (a, b, v)

/-- Insert a triple by its lower bound. -/
def rmInsert (t : RmTriple) : List RmTriple → List RmTriple
  | [] => [t]
  | u :: us => if t.1 ≤ u.1 then t :: u :: us else u :: rmInsert t us

/-- Touching intervals of one value merged, in order. -/
def rmMerge : List RmTriple → List RmTriple
  | (a, b, v) :: (a', b', v') :: ts =>
      if b == a' && GroundTerm.cmp v v' == .eq then rmMerge ((a, b', v) :: ts)
      else (a, b, v) :: rmMerge ((a', b', v') :: ts)
  | ts => ts
  termination_by ts => ts.length

/-- The canonical entries of pairwise disjoint proper intervals: sorted by lower bound, touching
intervals of one value merged. -/
def rmCanon (ts : List RmTriple) : Entries :=
  (rmMerge (ts.foldr rmInsert [])).map fun (a, b, v) => (rangeT a b, v)

/-- One interval less `[a, b)`: the parts below and above it. -/
def rmCutOne (a b : Int) : RmTriple → List RmTriple
  | (x, y, v) =>
    (if x < min y a then [(x, min y a, v)] else []) ++ (if max x b < y then [(max x b, y, v)] else [])

/-- The intervals of `ts` less `[a, b)`. -/
def rmCut (a b : Int) (ts : List RmTriple) : List RmTriple := ts.flatMap (rmCutOne a b)

/-- The interval holding `k`, with its value. -/
def rmFind (k : Int) (ts : List RmTriple) : Option RmTriple := ts.find? fun (x, y, _) => x ≤ k && k < y

/-- A key of `[a, b)` is in an interval of `ts`: a part of the range is present. -/
def rmMeets (a b : Int) (ts : List RmTriple) : Bool := ts.any fun (x, y, _) => a < y && x < b

/-- No interval of one meets an interval of the other. -/
def rmDisjoint (ts us : List RmTriple) : Bool :=
  ts.all fun (x, y, _) => us.all fun (x', y', _) => y ≤ x' || y' ≤ x

/-- Every key of `ts` has its value in `us`: what remains of each interval after cutting `us`'s
intervals of the same value is empty. -/
def rmIncluded (ts us : List RmTriple) : Bool :=
  ts.all fun t => ((us.filter fun u => GroundTerm.cmp u.2.2 t.2.2 == .eq).foldl
    (fun acc u => rmCut u.1 u.2.1 acc) [t]).isEmpty

/-- `m -RangeMap n`: m less each part where n gives the same value (584-588). -/
def rmDiffT (ts us : List RmTriple) : List RmTriple :=
  us.foldl (fun acc (a, b, w) => acc.flatMap fun t =>
    if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t]) ts

/-- `updateRangeMap(m, n)`: n's intervals written over m in turn (594-605). -/
def rmOverT (ts us : List RmTriple) : List RmTriple :=
  us.foldl (fun acc (a, b, w) => rmCut a b acc ++ [(a, b, w)]) ts

/-- A range map value of the library's sort. -/
def rmV (es : Entries) : GroundTerm := .map Srt.rangeMap es

/-- RANGEMAP's fourteen interpreted symbols. `[_ <- undef]` and `removeAll` give a value only where
a part of the range (of every range of the Set, each against the map given) is in the map
(`rmMeets`): "If all or any part of the range is present in the range map, it will be removed"
(domains.md 575-576), "For every range in the set, all or any part of it that is present in the
range map will be removed" (611-613), neither declared `total` (579, 616); `removeAll` at the
empty Set names no range and gives the map. -/
def rangeMapHooks : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  [(rmUnit, fun vs => match vs with | [] => some (rmV []) | _ => none),
   (rmElem, fun vs => match vs with
     | [r, v] => (asRange r).map fun (a, b) => rmV [(rangeT a b, v)] | _ => none),
   (rmConcat, fun vs => match vs with
     | [.map _ m, .map _ n] => (rmTriples m).bind fun ts => (rmTriples n).bind fun us =>
         if rmDisjoint ts us then some (rmV (rmCanon (ts ++ us))) else none
     | _ => none),
   (rmLookup, fun vs => match vs with
     | [.map _ m, k] => (rmTriples m).bind fun ts => (asKInt k).bind fun i => (rmFind i ts).map (·.2.2)
     | _ => none),
   (rmLookupOrDefault, fun vs => match vs with
     | [.map _ m, k, d] => (rmTriples m).map fun ts =>
         (((asKInt k).bind fun i => rmFind i ts).map (·.2.2)).getD d
     | _ => none),
   (rmFindRange, fun vs => match vs with
     | [.map _ m, k] => (rmTriples m).bind fun ts => (asKInt k).bind fun i =>
         (rmFind i ts).map fun (a, b, _) => rangeT a b
     | _ => none),
   (rmUpdate, fun vs => match vs with
     | [.map _ m, r, v] => (rmTriples m).bind fun ts => (asRange r).map fun (a, b) =>
         rmV (rmCanon (rmCut a b ts ++ [(a, b, v)]))
     | _ => none),
   (rmRemove, fun vs => match vs with
     | [.map _ m, r] => (rmTriples m).bind fun ts => (asRange r).bind fun (a, b) =>
         if rmMeets a b ts then some (rmV (rmCanon (rmCut a b ts))) else none
     | _ => none),
   (rmDifference, fun vs => match vs with
     | [.map _ m, .map _ n] => (rmTriples m).bind fun ts => (rmTriples n).map fun us => rmV (rmCanon (rmDiffT ts us))
     | _ => none),
   (rmUpdateAll, fun vs => match vs with
     | [.map _ m, .map _ n] => (rmTriples m).bind fun ts => (rmTriples n).map fun us =>
         rmV (rmCanon (rmOverT ts us))
     | _ => none),
   (rmRemoveAll, fun vs => match vs with
     | [.map _ m, .set _ rs] => (rmTriples m).bind fun ts => (rs.mapM asKRange).bind fun ps =>
         if ps.all (fun (a, b) => rmMeets a b ts) then
           some (rmV (rmCanon (ps.foldl (fun acc (a, b) => rmCut a b acc) ts)))
         else none
     | _ => none),
   (rmInKeys, fun vs => match vs with
     | [k, .map _ m] => (rmTriples m).map fun ts => bool (((asKInt k).bind fun i => rmFind i ts).isSome)
     | _ => none),
   (rmSize, fun vs => match vs with | [.map _ m] => some (int m.length) | _ => none),
   (rmInclusion, fun vs => match vs with
     | [.map _ m, .map _ n] => (rmTriples m).bind fun ts => (rmTriples n).map fun us => bool (rmIncluded ts us)
     | _ => none)]

/-- `keys(M)`: the set of M's ranges, each as a KItem (domains.md 620-625). A Set value wherever
every Range value is a KItem (`RangeBelow`, `rmK_keys_sorted`). -/
def rmKeysHook : List GroundTerm → Option GroundTerm
  | [.map _ m] => some (.set Srt.set (m.foldr (fun (k, _) s => insertS (.inj Srt.range Srt.kitem k) s) []))
  | _ => none

/-- RANGEMAP's `keys`, apart from `rangeMapHooks`: its value is a Set value where every Range value
is a KItem, where the fourteen give a value of their result sort in every semantics. -/
def rangeMapKeysHooks : List (Sym × (List GroundTerm → Option GroundTerm)) := [(rmKeys, rmKeysHook)]

/-- The interpreted symbols and their meaning. -/
def hookTable : List (Sym × (List GroundTerm → Option GroundTerm)) :=
  boolHooks ++ intHooks ++ kHooks ++ mapHooks ++ setHooks ++ listHooks ++ floatHooks ++ stringHooks ++ bytesHooks ++
    iteHooks ++ rangeMapHooks ++ rangeMapKeysHooks

/-- The trie of `hookTable`, built level by level (`NatMap.ofListBy`), 16 levels deep: every
number of the table is below 2^16 - 1 (`hookTable_keys`). One term for every lookup, so its levels
are unfolded (evaluated) once. -/
def hookTrie : NatMap (List GroundTerm → Option GroundTerm) := NatMap.ofListBy 16 hookTable

/-- `none`: not an interpreted symbol; `some r`: interpreted, with value `r` (`none`: undefined).
Reaching an entry of `hookTrie` unfolds about log₂ f levels, however many entries the table has. -/
def hook (f : Sym) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  (hookTrie.find f).map fun h => h vs

theorem hookTable_keys : ∀ e ∈ hookTable, e.1 + 1 < 2 ^ 16 := by decide +kernel

/-- `hook` (by the trie of the hooks' numbers) is the table's first entry of that number. -/
theorem hook_eq (f : Sym) (vs : List GroundTerm) :
    hook f vs = (hookTable.find? (·.1 == f)).map fun (_, h) => h vs := by
  rw [hook, hookTrie, NatMap.find_ofListBy]
  split
  · cases hookTable.find? (·.1 == f) <;> rfl
  · rename_i hf
    have : hookTable.find? (·.1 == f) = none := List.find?_eq_none.mpr fun e he h =>
      hf (by have := hookTable_keys e he; simp only [beq_iff_eq] at h; rw [← h]; exact this)
    rw [this]; rfl

/-! ## Silent points -/

/-- Where `hook f vs` gives no value, whether K's text says nothing of the value there (a silent
point) rather than that there is none: per interpreted symbol, a test of the argument values,
consulted only where `hook` gives `some none` (`Semantics.hookRes`). A key with `fun _ => true` makes
every point where `hook` gives no value silent; every interpreted symbol off the table gives no value
only where the text says there is none (`#False`, `#Bottom`). Where the text declares the symbol
`total`, it states that a value exists at its silent points and not which: the interpretations it
admits give one there (`totalSilentKeys`, `Semantics.silentTotal`, ParamsTotal.lean). A library
equation whose instance at values reaches a silent point is likewise a condition on the
interpretation (`Semantics.libAdmitted`, LibAdmitted.lean). Line numbers are domains.md's
(K 7.1.337).
- `L[I]`, `range`: the text describes an index of the list (960-963) and removing that many elements
  from the front and the back (1012-1013); an index off the list, or more elements than there are, is
  not described.
- `+Float`, `-Float`, `*Float`, `/Float`, `%Float`: the exact result rounded (1556-1570); on two
  formats the format of the result is not given. Nor does the text give (it writes no `#False` in
  FLOAT, and names IEEE 754 for no operation, 1464-1466) a value at an infinite or NaN operand or
  a zero divisor, the sign of a zero result other than `0.0 -Float 0.0` (1553), a result whose
  exact value is above the format's largest finite value, or the integer nearest a quotient halfway
  between two (`%Float`, 1557-1558).
- `roundFloat`, `Int2Float` at a value the format asked for does not hold: no direction to round in
  (1579, 1653); `roundFloat` at an infinity or NaN.
- `--Float`, `absFloat` at NaN; `floorFloat`, `ceilFloat`, `truncFloat` at an infinity or NaN, at a
  zero result of a nonzero operand (no sign, 1583-1588) and at an integer the format does not hold
  (the "double-rounding" of 1655-1658 is described nowhere).
- `roundFloat`, `Int2Float`, `maxValueFloat`, `minValueFloat` at a format without a model (`p < 2` or
  `e < 2`) that `thinAt` does not name: `pNxM` names a format for positive N and M only
  (1469-1476); at one exponent bit the format is named and KCore computes none of its data
  (`KFloat.thinOK`). At a format `thinAt` names (precision 1, at least 2 exponent bits) they compute
  (`thinHooks`), with the silent points of the bullet above.
- `ordChar`, `chrChar`: a string of one code point (1738-1739), a code point 0 … 0x10ffff (1702-1703);
  another string or Int is not described; at a surrogate the string is not a value here.
- `substrString`: "only defined on valid indices" (1753-1755), declared `total` (1758): a value exists
  and none is given off `0 ≤ start < end ≤ length`, nor at an empty range strictly inside.
- `findString`, `rfindString`, `findChar`, `rfindChar`: a search "starting at a certain `index`"
  (1763-1765, 1774-1776); an index that is no position of the string is not described.
- `String2Int`, `String2Base`: INT's syntax (1820-1822), a radix 2 … 36 (1825-1829); other strings
  and radixes are not described.
- `replace` at a negative count: "undefined … This allows different backends to implement their own
  behavior" (1908-1910).
- `String2Bool`: two equations, at `"true"` and `"false"` (1792-1794), and no `total`.
- `countAllOccurrences`, `replaceAll` at the empty needle: both are declared `total` (1852, 1855), so
  a value exists. The prose speaks of "the number of times a string occurs within another string"
  (1848-1849) and does not say how often the empty string occurs; the second equation of
  `countAllOccurrences` (1898-1899) reads at the empty needle `c = 1 +Int c`, which no Int meets, so
  that instance is a sentence of the text no interpretation satisfies and is not stated; at a
  non-empty needle the two equations give the count, and `hook` has it. `replaceAll` is `replace` at
  that count (1917), also at the empty needle.
- `memsetBytes`: "This will throw an exception" (2158-2164), of a run, where the text writes `#False`
  for no value (227-228). Its sibling `replaceAtBytes` is no key: "`dest` except the `N` elements
  starting at `index` are replaced" (2143-2144) names N elements of `dest` exactly when 0 ≤ `index`
  and `index + N` ≤ the length, and the `#False` of 2146-2147 is read of every other range (one that
  leaves `dest`); its bound "`index + N` is not a valid index" would deny by one position the value
  the defining sentence describes at `index + N` = the length, and the defining sentence decides.
- `Bytes2Int`, `Int2Bytes`: declared `total` (2082, 2083); a negative length, or an Endianness or
  Signedness that is no constructor of BYTES, is not described.
- `sqrtFloat` (1600, not `total`) where the format does not hold the operand's square root (the
  text names no rounding for it), at NaN, a negative datum and the infinities; and at both zeros,
  whose root is a zero of a sign the text does not give (FloatDomain.lean `sqrt?`).
- `--Float`, `absFloat`, `floorFloat`, `ceilFloat`, `truncFloat`, `isInfinite` (and the operations
  above), the six comparisons and `isNaN` at a value of a format of one exponent bit
  (`KFloat.thinOK`): KCore computes no operation there, so Γ states there only the interpretation's
  value, less than the text states (an operation at such a format has the status it has at any
  format, 1475, 1481-1488). At precision 1 and at least 2 exponent bits (`thinAt`) the comparisons
  and `isNaN` read the datum (`asDatum`, `KFloat.thinUnpack`), and the other operations compute on
  it by the formulas of a format with a model over the rounding to the nearest datum of that format
  (`thinHooks`, FloatThin.lean), with the silent points the bullets above name, and at an exact
  result halfway between two data of the format (zero and the smallest positive datum included).
- RANGEMAP's `lookup` and `find_range` off the keys: "yield an exception during concrete execution"
  (534-535, 555-556), of a run, and no `#False`, the reading taken for `memsetBytes`.
- RANGEMAP's element symbol `r|->`, update, `[_ <- undef]` and `removeAll` at a range that is no proper Int range (for
  `removeAll`, a member of the set that is none): the text describes ranges of Int keys bounded
  inclusively below and exclusively above (471-477, 498-499) and says nothing of another.
- RANGEMAP's concatenation `_RangeMap_` at two maps with a key in common: "an exception will be
  thrown during concrete execution" (503-504), of a run, and no `#False`; "a partial function only
  defined on range maps with non overlapping ranges" (600-602) says that it is not total (508),
  not what it is off them, as "only defined on valid indices" of `substrString`.
- RANGEMAP's `[_ <- undef]` and `removeAll` at a proper range no part of which is in the map: the
  sentences speak of a range of which "all or any part" is present (575-576, 611-613), neither
  operation is declared `total` (579, 616), and of another range nothing is said.
- `^%Int` at a negative exponent and a modulus other than 0: "equal in value to `(A ^Int B) %Int C`"
  (1229-1231), and of `A ^Int B` at a negative exponent the text says nothing (1228). At an exponent
  not negative `hook` gives the truncating remainder of the power (1233-1234), at every modulus
  other than 0; `smt-hook((mod (^ #1 #2) #3))` (1251) is how a solver query encodes the production
  (MAN 2381-2389; "SMT hooks need to convert from Euclidian division operations", 1255) and states
  no value. At a zero modulus `(A ^Int B) %Int 0` has none (1233-1234), and the point is not
  silent.
- `^Int` at a negative exponent: "the exponentiation `^Int` of two integers" (1228) names no
  integer there and writes no `#False`.
- `L[I <- V]` off `0 ≤ I < size`: "a new `List` with a new value at a particular index" (974-975);
  of an index that is none of the list's nothing is said, and whether a negative one counts from
  the back, as the index of `L[I]` does (961-963), is not said either.
- `makeList` at a negative length: "a list with `length` elements" (984-985) names none.
- `updateList` off `0 ≤ index` and `index + N ≤ K`: `index + N > K` "yields an exception"
  (993-995), of a run, and no `#False` (the reading taken for `memsetBytes`); of a negative index
  nothing is said.
- `fillList` off `0 ≤ index`, `0 ≤ length` and `index + length ≤ size`: "the `length` elements
  starting at `index`" (1003-1004) name no elements of the list there. -/
def silentTable : List (Sym × (List GroundTerm → Bool)) :=
  [(listGet, fun _ => true), (listRange, fun _ => true),
   (floatAdd, fun _ => true), (floatSub, fun _ => true), (floatMul, fun _ => true),
   (floatDiv, fun _ => true), (floatRem, fun _ => true),
   (floatRound, fun _ => true), (int2Float, fun _ => true),
   (floatMaxValue, fun _ => true), (floatMinValue, fun _ => true),
   (stringOrd, fun _ => true), (stringChr, fun _ => true), (stringSubstr, fun _ => true),
   (stringFind, fun _ => true), (stringRfind, fun _ => true),
   (stringFindChar, fun _ => true), (stringRfindChar, fun _ => true),
   (string2Int, fun _ => true), (string2Base, fun _ => true), (stringReplace, fun _ => true),
   (string2Bool, fun _ => true),
   (stringCountAll, fun _ => true), (stringReplaceAll, fun _ => true),
   (bytesMemset, fun _ => true), (bytes2Int, fun _ => true), (int2Bytes, fun _ => true),
   (floatSqrt, fun _ => true),
   (floatNeg, fun _ => true), (floatAbs, fun _ => true), (floatFloor, fun _ => true),
   (floatCeil, fun _ => true), (floatTrunc, fun _ => true),
   (floatLe, fun _ => true), (floatLt, fun _ => true), (floatGe, fun _ => true),
   (floatGt, fun _ => true), (floatEq, fun _ => true), (floatNe, fun _ => true),
   (floatIsNaN, fun _ => true), (floatIsInfinite, fun _ => true),
   (rmElem, fun _ => true), (rmConcat, fun _ => true), (rmLookup, fun _ => true),
   (rmFindRange, fun _ => true), (rmUpdate, fun _ => true), (rmRemove, fun _ => true),
   (rmRemoveAll, fun _ => true),
   (intPowMod, fun vs => match vs with | [_, _, m] => (asInt m).any (· != 0) | _ => false),
   (intPow, fun _ => true),
   (listSet, fun _ => true), (listMake, fun _ => true), (listUpdateAll, fun _ => true), (listFill, fun _ => true)]

/-- `vs` is a silent point of the interpreted symbol `f` (`silentTable`). -/
def silent (f : Sym) (vs : List GroundTerm) : Bool :=
  match silentTable.find? (·.1 == f) with
  | some (_, p) => p vs
  | none => false

/-- `f` has silent points somewhere (a key of `silentTable`). -/
def silentKey (f : Sym) : Bool := silentTable.any (·.1 == f)

/-- A silent point is one of a key. -/
theorem silentKey_of_silent {f : Sym} {vs : List GroundTerm} (h : silent f vs = true) :
    silentKey f = true := by
  unfold silent at h
  unfold silentKey
  cases he : silentTable.find? (·.1 == f) with
  | none => rw [he] at h; cases h
  | some e => exact List.any_eq_true.mpr ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩

/-- Off the keys, no point is silent. -/
theorem silent_of_not_silentKey {f : Sym} (h : silentKey f = false) (vs : List GroundTerm) :
    silent f vs = false := by
  cases hs : silent f vs
  · rfl
  · rw [silentKey_of_silent hs] at h; cases h

/-- The interpreted symbols whose meaning the proofs read through `hook` directly, so that none
may be a key of `silentTable` (`silentKey_fixed`): the map and collection pattern symbols (a pattern
denotes `hook`'s value, `PatVal`, `Semantics.collVal`), `ite`, and the Bool, K equality, Int
comparison and map update operations that deciders evaluate. -/
def neverSilent : List Sym :=
  patternHooks ++ collPatternHooks ++
    [kIte, boolAnd, boolOr, boolNot, kEq, kNe, intLt, intLe, intGt, intGe, intEq, intNe, mapUpdate]

theorem silentKey_fixed : ∀ f ∈ neverSilent, silentKey f = false := by decide +kernel

/-- No symbol has two entries in `silentTable` (`silent` reads the first). -/
theorem silentTable_nodup : (silentTable.map (·.1)).Nodup := by decide +kernel

/-- Every key of `silentTable` is an interpreted symbol (`isHook`). -/
theorem silentTable_hook : ∀ e ∈ silentTable, (hook e.1 []).isSome = true := by decide +kernel

/-- Every key of `silentTable` is among `partialHooks`, which the totality deciders do not count
total, but `Bytes2Int`, which has a value where Endianness and Signedness have only BYTES'
constructors (`enumShapesOK`). -/
theorem silentTable_partial : ∀ e ∈ silentTable, partialHooks.contains e.1 = true ∨ e.1 = bytes2Int := by
  decide +kernel

/-- The names of `hookSigs` are distinct: `lookupSig` finds each signature by its name, so
`Semantics.fallback` (the result sort of the first signature of the name) and `Faithful.ΓFallback`
(every signature) speak of the same signatures. -/
theorem hookSigs_lookup : ∀ k ∈ hookSigs, lookupSig hookSigs k.name = some k := by decide +kernel

theorem silentKey_of_mem {f : Sym} (h : neverSilent.contains f = true) : silentKey f = false :=
  silentKey_fixed f (List.contains_iff_mem.mp h)

theorem silentKey_of_patternHook {f : Sym} (h : patternHooks.contains f = true) : silentKey f = false :=
  silentKey_fixed f (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h)))

theorem silentKey_of_collPatternHook {f : Sym} (h : collPatternHooks.contains f = true) :
    silentKey f = false :=
  silentKey_fixed f (List.mem_append_left _ (List.mem_append_right _ (List.contains_iff_mem.mp h)))

theorem silentKey_boolAnd : silentKey boolAnd = false := silentKey_of_mem rfl
theorem silentKey_boolNot : silentKey boolNot = false := silentKey_of_mem rfl
theorem silentKey_kIte : silentKey kIte = false := silentKey_of_mem rfl

end KCore
