/-
  KCore, checked layer: an interpretation of the silent points under which the library's sentences
  over Γ's symbols hold at values.

  At a silent point (`silentTable`) Γ states the interpretation's value (`Semantics.fallback`). A
  library sentence whose instance at values reaches such a point is, at that instance, a condition
  on the interpretation; the interpretations the text admits are those meeting every such condition.

  - `HookParams.lib`: `HookParams.totals`' values at the silent points of the `total` symbols, and:
    `maxValueFloat` at a format with a field of 1 that format's NaN; `rootFloat` at a Float and 2 what `hook` gives
    `sqrtFloat` there; `replace` at a silent point its first argument and `replaceAll` at one the
    value of `replace` at the count; nothing elsewhere.
  - `libSentences`: the library sentences over Γ's symbols, besides the `functional` sentences of
    `totalSilentKeys`, that read the interpretation (test/LibProbe.lean checks the list).
  - `Semantics.libAdmitted c`: `silentTotal` and one condition per sentence of `libSentences`
    (`isInfiniteEq`, `rfindCharEq`, `findCharEq`, `sqrtFloatEq`, `replaceAllEq`,
    `rangeMapAssocEq`), each the sentence at the values where it reads the interpretation: where its
    left side is at a silent point, for `sqrtFloat`'s at every Float, its right side being
    `rootFloat`, which no hook interprets, and for `_RangeMap_`'s associativity at every three range
    maps, `_RangeMap_` being silent at every point. The
    conditions are named, not read off the text: a statement over
    every library sentence would hold the reader's selection of sentences and a meaning of KORE
    patterns at values, and Γ's meaning of a sentence is the reader's translation.
  - `libAdmitted_lib`: `HookParams.lib` meets them in every semantics with `floatShapeOK`, so in
    every semantics meeting `coreOK` (`floatShapeOK_of_coreOK`, `libAdmitted_lib_of_coreOK`).
    `rangeMapAssocEq` holds under every interpretation that gives `_RangeMap_` no value
    (`rangeMapAssocEq_of_app_none`), `HookParams.lib` among them.
-/
import KcoreSpec.ParamsTotal

set_option autoImplicit false

namespace KCore

/-- The value `HookParams.lib` gives `maxValueFloat` at two Ints: at a format with a field of 1
(`p = 1` or `e = 1`, both positive) its one NaN, `2 ^ (p + e)` (`KFloat.thinOK`); nothing elsewhere.
It is read only where `hook` gives no value (`Semantics.fallback`): at the format `(1, 1)`, whose
finite data are the two zeros, since `hook` computes the largest finite datum at every other format
`thinAt` names. -/
def libMaxValue (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [x, y] => (asInt x).bind fun p => (asInt y).bind fun e =>
      if 1 ≤ p ∧ 1 ≤ e ∧ (p = 1 ∨ e = 1) then
        some (.dv Srt.float (.float p.toNat e.toNat (2 ^ (p.toNat + e.toNat))))
      else none
  | _ => none

/-- FLOAT's `rootFloat` (domains.md 1607, `hook(FLOAT.root)`), by its number in the registry
(`libRootFloat_name`). No hook of Hooks.lean interprets it: where a text uses it, it is a parameter
symbol (`libParams`), and its value is the interpretation's at every argument. -/
def libRootFloat : Sym := 235

theorem libRootFloat_name : regSymNames[libRootFloat]? =
    some "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int" := by decide +kernel

/-- The value `HookParams.lib` gives `rootFloat` at a Float and the Int 2: what `hook` gives
`sqrtFloat` at that Float, none where it gives none; nothing at another argument list. -/
def libRootVal (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [F, n] => if asInt n = some 2 then (hook floatSqrt [F]).join else none
  | _ => none

/-- The value `HookParams.lib` gives `replaceAll` at three arguments: `replace` at them and the
count, where the count is `hook`'s value of `countAllOccurrences` and 0 where it has none, and
`replace` is `hook`'s value and the first argument where it has none. -/
def libReplaceAll (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [s, n, r] =>
    some (((hook stringReplace [s, n, r, ((hook stringCountAll [s, n]).join).getD (int 0)]).join).getD s)
  | _ => none

/-- **An interpretation under which the library's sentences hold at values**: `replaceAll` at a
silent point `replace` at the count (`libReplaceAll`) and `replace` at one its first argument;
`totalsVal` at the other symbols of `totalSilentKeys` (so `countAllOccurrences` 0); `maxValueFloat` at a format with a field of 1 its NaN (`libMaxValue`);
`rootFloat` at a
Float and 2 `hook`'s value of `sqrtFloat` (`libRootVal`); nothing elsewhere.
At an interpreted symbol it is read only at silent points (`Semantics.fallback`), where `hook` gives
no value; at `rootFloat`, a parameter symbol, at every argument. At the Float points of a format with
a model where K's text states no value (FloatDomain.lean) that is the operand itself for `--Float`
and `absFloat` at NaN and for `floorFloat`, `ceilFloat`, `truncFloat` at an infinity, NaN, a zero
result of a nonzero operand or an integer the format does not hold (`totalsVal`), and no value for
the five arithmetic operations, `roundFloat` and `Int2Float`, which are not `total`. No sentence of
`libSentences` reads those points: 1673 negates a `maxValueFloat`, a NaN only at the format `(1, 1)`
(`libMaxValue`), where `--Float` of it is the NaN (`totalsVal`). -/
def HookParams.lib : HookParams :=
  ⟨fun f vs =>
    if f == stringReplaceAll then libReplaceAll vs
    else if f == stringReplace then vs.head?
    else if totalSilentKeys.contains f then totalsVal f vs
    else if f == floatMaxValue then libMaxValue vs
    else if f == libRootFloat then libRootVal vs
    else Option.none⟩

/-- The library sentences over Γ's symbols, other than the `functional` sentences of
`totalSilentKeys` (`Semantics.silentTotal`), that read the interpretation at some value, by their
line in domains.md (K 7.1.337), and the condition each states on it:
`isInfinite` (1673), `rfindChar` (1893), `findChar` (1891), `sqrtFloat` (1671), `replaceAll` (1917),
and the `assoc` attribute of `_RangeMap_` (508), a collection law: where two of its three range
maps have a key in common, `_RangeMap_` is at a silent point.
One sentence that reads it is not listed: the instance of `countAllOccurrences`' second equation
(1898) at the empty needle, `c = 1 +Int c` of the count `c`, which no interpretation that gives the
count a value there meets (one meeting `silentTotal` gives it one, `countAllOccurrences` being of
`totalSilentKeys`); where the count has no value both sides have none. test/LibProbe.lean checks the list against the sentences a
text holds: a sentence that reads the interpretation at a probed point is one of these or a
`functional` sentence of `totalSilentKeys`; on f2-examples/allbuiltins.kompile.kore, every module of
the K 7.1.337 builtin files the library holds, the list is closed. The probe names a collection
law by its symbol, since a law sentence carries no line of its own: line 508 is that of
`_RangeMap_`'s declaration, whose attributes the law sentences are generated from. -/
def libSentences : List (Nat × String) :=
  [(1673, "isInfiniteEq"), (1893, "rfindCharEq"), (1891, "findCharEq"),
   (1671, "sqrtFloatEq"), (1917, "replaceAllEq"), (508, "rangeMapAssocEq")]

/-! ## The conditions the library's sentences state on the interpretation -/

namespace Semantics
variable (c : Semantics)

/-- The value of the interpreted symbol `f` at `vs` in Γ's reading (`hookRes`), none where Γ
states ⊥. -/
def hv (f : Sym) (vs : List GroundTerm) : Option GroundTerm := (c.hookRes f vs).join

/-- **domains.md 1673** `isInfinite(F) => F >Float maxValueFloat(precisionFloat(F),
exponentBitsFloat(F)) orBool F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`,
at the Floats where `isInfinite` is at a silent point. -/
def isInfiniteEq : Prop :=
  ∀ F, c.sortOf F = some Srt.float → hook floatIsInfinite [F] = some none →
    c.hv floatIsInfinite [F] =
      (c.hv floatPrecision [F]).bind fun p => (c.hv floatExponentBits [F]).bind fun e =>
      (c.hv floatMaxValue [p, e]).bind fun m => (c.hv floatGt [F, m]).bind fun g =>
      (c.hv floatNeg [m]).bind fun m' => (c.hv floatLt [F, m']).bind fun l => c.hv boolOr [g, l]

/-- **domains.md 1893** `rfindChar(S1, S2, I) => maxInt(rfindString(S1, substrString(S2, 0, 1), I),
rfindChar(S1, substrString(S2, 1, lengthString(S2)), I)) requires S2 =/=String ""`, at the points
where `rfindChar` is at a silent point. -/
def rfindCharEq : Prop :=
  ∀ s1 s2 i, c.sortsOf [s1, s2, i] = some [Srt.string, Srt.string, Srt.int] →
    c.hv stringNe [s2, strV []] = some (bool true) → hook stringRfindChar [s1, s2, i] = some none →
    c.hv stringRfindChar [s1, s2, i] =
      (c.hv stringSubstr [s2, int 0, int 1]).bind fun h => (c.hv stringLength [s2]).bind fun n =>
      (c.hv stringSubstr [s2, int 1, n]).bind fun t =>
      (c.hv stringRfind [s1, h, i]).bind fun a => (c.hv stringRfindChar [s1, t, i]).bind fun b =>
      c.hv intMax [a, b]

/-- **domains.md 1891** `findChar(S1, S2, I) => #if findString(S1, substrString(S2, 0, 1), I) ==Int -1
#then findChar(S1, substrString(S2, 1, lengthString(S2)), I) #else #if findChar(S1, substrString(S2,
1, lengthString(S2)), I) ==Int -1 #then findString(S1, substrString(S2, 0, 1), I) #else
minInt(findString(S1, substrString(S2, 0, 1), I), findChar(S1, substrString(S2, 1, lengthString(S2)),
I)) #fi #fi requires S2 =/=String ""`, at the points where `findChar` is at a silent point. The
right side has a value only where both searches have one: `#if` is a symbol applied to its three
arguments, and each of the two searches is an argument of the outer or of the inner one. -/
def findCharEq : Prop :=
  ∀ s1 s2 i, c.sortsOf [s1, s2, i] = some [Srt.string, Srt.string, Srt.int] →
    c.hv stringNe [s2, strV []] = some (bool true) → hook stringFindChar [s1, s2, i] = some none →
    c.hv stringFindChar [s1, s2, i] =
      (c.hv stringSubstr [s2, int 0, int 1]).bind fun h => (c.hv stringLength [s2]).bind fun n =>
      (c.hv stringSubstr [s2, int 1, n]).bind fun t =>
      (c.hv stringFind [s1, h, i]).bind fun a => (c.hv stringFindChar [s1, t, i]).bind fun b =>
      (c.hv intEq [a, int (-1)]).bind fun ea => (c.hv intEq [b, int (-1)]).bind fun eb =>
      (c.hv intMin [a, b]).bind fun m => (c.hv kIte [eb, a, m]).bind fun r => c.hv kIte [ea, b, r]

/-- The interpretation's value of `rootFloat` at the Float `F` and the Int 2, kept where it has
sort Float: `paramVal`'s value where `rootFloat` is the library's parameter symbol
(`paramVal_libRootFloat`). -/
def rootAt2 (F : GroundTerm) : Option GroundTerm :=
  (c.hooks.app libRootFloat [F, int 2]).filter fun v => c.sortOf v == some Srt.float

/-- **domains.md 1671** `sqrtFloat(F) => rootFloat(F, 2)`, at every value of sort Float: the right
side is the interpretation's value everywhere, so the sentence is a condition on it also where
`hook` gives `sqrtFloat` a value. Both sides have a value, the same, or neither has one. -/
def sqrtFloatEq : Prop :=
  ∀ F, c.sortOf F = some Srt.float → c.rootAt2 F = c.hv floatSqrt [F]

/-- **domains.md 1917** `replaceAll(Source, ToReplace, Replacement) => replace(Source, ToReplace,
Replacement, countAllOccurrences(Source, ToReplace))`, at the points where `replaceAll` is at a
silent point (the empty needle, where `countAllOccurrences` is at one too). -/
def replaceAllEq : Prop :=
  ∀ s n r, c.sortsOf [s, n, r] = some [Srt.string, Srt.string, Srt.string] →
    hook stringReplaceAll [s, n, r] = some none →
    c.hv stringReplaceAll [s, n, r] =
      (c.hv stringCountAll [s, n]).bind fun k => c.hv stringReplace [s, n, r, k]

/-- **domains.md 508** `_RangeMap_`'s `assoc` attribute, the law `(M N) P = M (N P)` as an
equality of patterns, at every three values of sort RangeMap. `_RangeMap_` is silent at every
point (`silentTable`), and `hook` gives it a value at two range maps exactly where they have no key
in common; where two of the three have one, a side reads the interpretation's value. Where none
has one, both sides are `hook`'s, the same value (`rmConcat_assoc`). -/
def rangeMapAssocEq : Prop :=
  ∀ m n p, c.sortsOf [m, n, p] = some [Srt.rangeMap, Srt.rangeMap, Srt.rangeMap] →
    ((c.hv rmConcat [m, n]).bind fun x => c.hv rmConcat [x, p]) =
      ((c.hv rmConcat [n, p]).bind fun y => c.hv rmConcat [m, y])

/-- **The interpretations the text admits**: every library sentence over Γ's symbols, two
excepted, holds at the values where it reads the interpretation: the `functional` sentences of
`totalSilentKeys` (`silentTotal`) and the sentences of `libSentences`. Each conjunct after the
first is one sentence of domains.md as a condition on the interpretation:
`isInfiniteEq` (1673), `rfindCharEq` (1893), `findCharEq` (1891) and `replaceAllEq` (1917) where
the sentence's left side is at a silent point, `sqrtFloatEq` (1671) at every Float,
`rangeMapAssocEq` (508) at every three range maps. The two
sentences that are no condition: set idempotence, which the reading of `_Set_` does not hold of;
and the instance of `countAllOccurrences`' second equation (1898-1899) at the empty needle, which
reads `c = 1 +Int c` of the count c that `silentTotal` asks for, and which no interpretation
meets: with it the text has no model, and the interpretations admitted here are those of the
text without that instance. At the other values a library sentence reads `hook` only, and holds
or fails for every interpretation alike. Γ does not state it; the statements over Γ hold for
every interpretation, admitted or not. -/
def libAdmitted : Prop :=
  c.silentTotal ∧ c.isInfiniteEq ∧ c.rfindCharEq ∧ c.findCharEq ∧ c.sqrtFloatEq ∧
    c.replaceAllEq ∧ c.rangeMapAssocEq

/-- Where `rootFloat` is the library's parameter symbol, its value at a Float and 2 is `rootAt2`. -/
theorem paramVal_libRootFloat
    (h : c.lookupParam libRootFloat = some { sig := ⟨libRootFloat, [Srt.float, Srt.int], Srt.float⟩ })
    (F : GroundTerm) : c.paramVal libRootFloat [F, int 2] = c.rootAt2 F := by
  unfold paramVal rootAt2; rw [h]; rfl

end Semantics

/-- The row 9 part. -/
theorem silentTotal_of_libAdmitted {c : Semantics} (h : c.libAdmitted) : c.silentTotal := h.1

/-! ## `HookParams.lib` is admitted -/

section Lib
variable {c : Semantics}

theorem hv_of_value {f : Sym} {vs : List GroundTerm} {v : GroundTerm} (h : hook f vs = some (some v)) :
    c.hv f vs = some v := by
  unfold Semantics.hv; rw [Semantics.hookRes_of_value h]; rfl

/-- At a silent point, the interpretation's value, kept where it has the result sort. -/
theorem hv_of_silent {f : Sym} {vs : List GroundTerm} {k : CtorSig} {v : GroundTerm}
    (hk : lookupSig hookSigs f = some k) (hh : hook f vs = some none) (hs : silent f vs = true)
    (hv : c.hooks.app f vs = some v) (hsrt : c.sortOf v = some k.result) : c.hv f vs = some v := by
  unfold Semantics.hv; rw [Semantics.hookRes_of_silent hh hs]
  unfold Semantics.fallback; rw [hk, hv]
  simp [Option.filter, hsrt]

/-- Where `hook` gives no value and the interpretation none, no value. -/
theorem hv_none {f : Sym} {vs : List GroundTerm} (hh : hook f vs = some none) (hv : c.hooks.app f vs = none) :
    c.hv f vs = none := by
  unfold Semantics.hv Semantics.hookRes
  split
  · rw [hh]; unfold Semantics.fallback; split <;> simp [hv]
  · rw [hh]; rfl

end Lib

/-! ### `isInfinite`, `rfindChar`, `findChar`, `sqrtFloat` under `HookParams.lib` -/

theorem flCmp_none {t t' : Option Ordering → Bool} {vs : List GroundTerm} (h : flCmp t vs = none) :
    flCmp t' vs = none := by
  match vs with
  | [a, b] =>
    unfold flCmp at h ⊢
    cases ha : asDatum a <;> cases hb : asDatum b <;> simp_all
  | [] | [_] | _ :: _ :: _ :: _ => rfl

/-- The NaN `HookParams.lib` gives `maxValueFloat` at a format with a field of 1 is a Float value. -/
theorem thin_nan_ok {p e : Nat} (hp : 1 ≤ p) (he : 1 ≤ e) (h1 : p = 1 ∨ e = 1) :
    KFloat.ok p e (2 ^ (p + e)) = true := by
  have hs : KFloat.spec? p e = none := by
    unfold KFloat.spec?; split
    · rename_i h; omega
    · rfl
  unfold KFloat.ok; rw [hs]
  unfold KFloat.thinOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_self_eq_true, true_or, and_true]
  omega

/-- `isInfinite`'s sentence holds under `HookParams.lib` where every Float value is a Float literal.
`isInfinite` is silent only at a Float of the format `(1, 1)` (at a format with a model and at every
other one `thinAt` names `hook` computes it); there `isInfinite` is `false` (`totalsVal`),
`maxValueFloat(1, 1)` the format's NaN (`libMaxValue`), both comparisons with it `false` (by `hook`:
the NaN is unordered, `KFloat.cmpExact`), `--Float` of the NaN the NaN (silent there, `totalsVal`). -/
theorem isInfiniteEq_lib (c : Semantics) (hfs : c.floatShapeOK = true) :
    (c.withHooks HookParams.lib).isInfiniteEq := by
  intro F hF hh
  obtain ⟨p, e, b, rfl, hok⟩ := shape_float (c := c.withHooks HookParams.lib) hfs hF
  obtain ⟨hp, he⟩ := KFloat.ok_pos hok
  have h0 : hook floatIsInfinite [.dv Srt.float (.float p e b)] =
      some (flOr (flTestM KFloat.isInf) tflInf [.dv Srt.float (.float p e b)]) := rfl
  have hsp : KFloat.spec? p e = none := by
    cases hs : KFloat.spec? p e with
    | none => rfl
    | some _ => rw [h0] at hh; simp [flOr, flTestM, asFloat, hs] at hh
  have ht : thinAt p e = true := by
    simp only [thinAt, KFloat.tnFormat, decide_eq_true_eq]
    unfold KFloat.spec? at hsp; split at hsp
    · cases hsp
    · rename_i h; omega
  have hmn : KFloat.tnMax? p e = none := by
    cases hm : KFloat.tnMax? p e with
    | none => rfl
    | some _ => rw [h0] at hh; simp [flOr, flTestM, asFloat, hsp, tflInf, asThin, ht, hm] at hh
  obtain ⟨rfl, rfl⟩ : p = 1 ∧ e = 1 := by
    simp only [thinAt, KFloat.tnFormat, decide_eq_true_eq] at ht
    by_cases he2 : 2 ≤ e
    · obtain ⟨_, hm⟩ := KFloat.tnMax?_normal hp he2; rw [hm] at hmn; cases hmn
    · obtain rfl : e = 1 := by omega
      by_cases hp2 : 2 ≤ p
      · obtain ⟨_, hm⟩ := KFloat.tnMax?_subnormal hp2; rw [hm] at hmn; cases hmn
      · omega
  let m : GroundTerm := .dv Srt.float (.float 1 1 (2 ^ (1 + 1)))
  have hcn : ∀ u, KFloat.cmpExact u .notANumber = none := by intro u; cases u <;> rfl
  have hdm : asDatum m = some .notANumber := by
    simp [m, asDatum, hsp, KFloat.tnFormat, KFloat.tnUnpack]
  have hdF : ∃ u, asDatum (.dv Srt.float (.float 1 1 b)) = some u := by
    simp [asDatum, hsp, KFloat.tnFormat]
  obtain ⟨u, hu⟩ := hdF
  have hms : (c.withHooks HookParams.lib).sortOf m = some Srt.float := by
    rw [sortOf_dv]; exact ⟨by simp [dvOK, thin_nan_ok (Nat.le_refl 1) (Nat.le_refl 1) (Or.inr rfl)], rfl⟩
  rw [hv_of_silent (k := ⟨floatIsInfinite, [Srt.float], Srt.bool⟩) rfl hh rfl rfl
      (sortOf_bool false)]
  have hpr : hook floatPrecision [.dv Srt.float (.float 1 1 b)] = some (some (int 1)) := by
    rw [hook_floatPrecision]; simp [flFmt]
  have hex : hook floatExponentBits [.dv Srt.float (.float 1 1 b)] = some (some (int 1)) := by
    rw [hook_floatExponentBits]; simp [flFmt]
  have hmx : hook floatMaxValue [int 1, int 1] = some none := by
    have h0 : hook floatMaxValue [int 1, int 1] =
      some (flOr (flAt KFloat.maxValue) (tflAt KFloat.tnMax?) [int 1, int 1]) := rfl
    rw [h0]; simp [flOr, flAt, tflAt, asInt, int, hsp, ht, hmn]
  have hmv : HookParams.lib.app floatMaxValue [int 1, int 1] = some m := by
    show libMaxValue [int 1, int 1] = some m
    simp [libMaxValue, asInt, int, m]
  have hgt : hook floatGt [.dv Srt.float (.float 1 1 b), m] = some (some (bool false)) := by
    rw [show hook floatGt [.dv Srt.float (.float 1 1 b), m] =
      some (flCmp (fun o => o == some .gt) [.dv Srt.float (.float 1 1 b), m]) from rfl]
    simp [flCmp, hu, hdm, hcn]
  have hng : hook floatNeg [m] = some none := by
    have h0 : hook floatNeg [m] = some (flOr (fl1 fun _ => KFloat.neg?) (tfl1 fun _ _ => KFloat.neg?) [m]) := rfl
    rw [h0]; simp [flOr, fl1, tfl1, asFloat, asThin, m, hsp, ht, KFloat.tnUnpack, KFloat.neg?]
  have hlt : hook floatLt [.dv Srt.float (.float 1 1 b), m] = some (some (bool false)) := by
    rw [show hook floatLt [.dv Srt.float (.float 1 1 b), m] =
      some (flCmp (fun o => o == some .lt) [.dv Srt.float (.float 1 1 b), m]) from rfl]
    simp [flCmp, hu, hdm, hcn]
  rw [hv_of_value hpr, Option.bind_some, hv_of_value hex, Option.bind_some,
    hv_of_silent (k := ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩) rfl hmx rfl hmv
      hms, Option.bind_some,
    hv_of_value hgt, Option.bind_some,
    hv_of_silent (k := ⟨floatNeg, [Srt.float], Srt.float⟩) rfl hng rfl rfl
      hms, Option.bind_some,
    hv_of_value hlt, Option.bind_some,
    hv_of_value (rfl : hook boolOr [bool false, bool false] = some (some (bool false)))]
  rfl

/-- `rfindChar`'s sentence holds under `HookParams.lib` in every semantics: where `rfindChar` is
silent at a nonempty needle, `rfindString` is silent at the same haystack and index, whatever
its needle, and `lib` gives neither a value; both sides have none. -/
theorem rfindCharEq_lib (c : Semantics) : (c.withHooks HookParams.lib).rfindCharEq := by
  intro s1 s2 i _ _ hh
  rw [hv_none hh rfl]
  symm
  have hrc : hook stringRfindChar [s1, s2, i] = some ((asStr s1).bind fun x => (asStr s2).bind fun y =>
      (asInt i).bind fun j => (KStr.rfindChar x y j).map int) := rfl
  rw [hrc, Option.some.injEq] at hh
  cases h2 : asStr s2 with
  | none =>
    have hl : hook stringLength [s2] = some none := by
      show some ((asStr s2).map fun x => int x.length) = _; rw [h2]; rfl
    have hlv : (c.withHooks HookParams.lib).hv stringLength [s2] = none := hv_none hl rfl
    simp [hlv]
  | some y =>
    have hr : ∀ h, (c.withHooks HookParams.lib).hv stringRfind [s1, h, i] = none := by
      intro h
      apply hv_none _ rfl
      show some ((asStr s1).bind fun x => (asStr h).bind fun y => (asInt i).bind fun j =>
        (KStr.rfind x y j).map int) = some none
      rw [Option.some.injEq]
      rw [h2] at hh
      cases h1 : asStr s1 with
      | none => rfl
      | some x =>
        cases hi : asInt i with
        | none => simp
        | some j =>
          rw [h1, hi] at hh
          simp only [Option.bind_some, Option.map_eq_none_iff] at hh
          have hpos : KStr.isPos x j = false := by
            unfold KStr.rfindChar at hh
            split at hh
            · cases hh
            · split at hh
              · cases hh
              · rename_i hp; simpa using hp
          simp [KStr.rfind, hpos]
    simp [hr]

/-- `findChar`'s sentence holds under `HookParams.lib` in every semantics: where `findChar` is
silent at a nonempty search string, `findString` is silent at the same haystack and index, whatever
its needle, and `lib` gives neither a value; both sides have none. -/
theorem findCharEq_lib (c : Semantics) : (c.withHooks HookParams.lib).findCharEq := by
  intro s1 s2 i _ _ hh
  rw [hv_none hh rfl]
  symm
  have hrc : hook stringFindChar [s1, s2, i] = some ((asStr s1).bind fun x => (asStr s2).bind fun y =>
      (asInt i).bind fun j => (KStr.findChar x y j).map int) := rfl
  rw [hrc, Option.some.injEq] at hh
  cases h2 : asStr s2 with
  | none =>
    have hl : hook stringLength [s2] = some none := by
      show some ((asStr s2).map fun x => int x.length) = _; rw [h2]; rfl
    have hlv : (c.withHooks HookParams.lib).hv stringLength [s2] = none := hv_none hl rfl
    simp [hlv]
  | some y =>
    have hr : ∀ h, (c.withHooks HookParams.lib).hv stringFind [s1, h, i] = none := by
      intro h
      apply hv_none _ rfl
      show some ((asStr s1).bind fun x => (asStr h).bind fun y => (asInt i).bind fun j =>
        (KStr.find x y j).map int) = some none
      rw [Option.some.injEq]
      rw [h2] at hh
      cases h1 : asStr s1 with
      | none => rfl
      | some x =>
        cases hi : asInt i with
        | none => simp
        | some j =>
          rw [h1, hi] at hh
          simp only [Option.bind_some, Option.map_eq_none_iff] at hh
          have hpos : KStr.isPos x j = false := by
            unfold KStr.findChar at hh
            split at hh
            · cases hh
            · split at hh
              · cases hh
              · rename_i hp; simpa using hp
          simp [KStr.find, hpos]
    simp [hr]

/-- `sqrtFloat`'s sentence holds under `HookParams.lib` in every semantics: `lib` gives `rootFloat`
at a Float and 2 the value `hook` gives `sqrtFloat` there, which has sort Float, and gives
`sqrtFloat` nothing at its silent points. -/
theorem sqrtFloatEq_lib (c : Semantics) : (c.withHooks HookParams.lib).sqrtFloatEq := by
  intro F hF
  have happ : HookParams.lib.app libRootFloat [F, int 2] = (hook floatSqrt [F]).join := rfl
  unfold Semantics.rootAt2
  rw [show (c.withHooks HookParams.lib).hooks.app libRootFloat [F, int 2] = (hook floatSqrt [F]).join from happ]
  have hk : lookupSig hookSigs floatSqrt = some ⟨floatSqrt, [Srt.float], Srt.float⟩ := by decide +kernel
  cases hh : hook floatSqrt [F] with
  | none => exact absurd hh (by rw [show hook floatSqrt [F] = some _ from rfl]; exact Option.some_ne_none _)
  | some r =>
    cases r with
    | none => rw [hv_none hh rfl]; rfl
    | some v =>
      have hs : (c.withHooks HookParams.lib).sortOf v = some Srt.float :=
        hook_sorted (c := c.withHooks HookParams.lib) (fun h => by cases h) hk
          (by show (c.withHooks HookParams.lib).sortsOf [F] = some [Srt.float]
              simp [Semantics.sortsOf, hF]) hh
      rw [hv_of_value hh]
      simp [Option.filter, hs]

/-- What `HookParams.lib` reads at `replaceAll` and three Strings: the count k, `hook`'s or 0, of
sort Int and the value of `countAllOccurrences` under `lib`; and a String w, `hook`'s value of
`replace` at k or the first argument, the value of `replace` at k under `lib` and `lib`'s answer at
`replaceAll`. -/
theorem libReplaceAll_parts (c : Semantics) {s n r : GroundTerm}
    (hs : (c.withHooks HookParams.lib).sortsOf [s, n, r] = some [Srt.string, Srt.string, Srt.string]) :
    ∃ k w, (c.withHooks HookParams.lib).hv stringCountAll [s, n] = some k ∧
      (c.withHooks HookParams.lib).hv stringReplace [s, n, r, k] = some w ∧
      HookParams.lib.app stringReplaceAll [s, n, r] = some w ∧
      (c.withHooks HookParams.lib).sortOf w = some Srt.string := by
  have hs' := hs
  simp only [sortsOf_eq_cons] at hs'
  obtain ⟨hs1, hs2, hs3, -⟩ := hs'
  have hkC : lookupSig hookSigs stringCountAll = some ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩ := by
    decide +kernel
  have hkR : lookupSig hookSigs stringReplace =
      some ⟨stringReplace, [Srt.string, Srt.string, Srt.string, Srt.int], Srt.string⟩ := by decide +kernel
  have hsC : (c.withHooks HookParams.lib).sortsOf [s, n] = some [Srt.string, Srt.string] := by
    exact sortsOf_eq_cons.mpr ⟨hs1, sortsOf_eq_cons.mpr ⟨hs2, rfl⟩⟩
  -- the count
  obtain ⟨k, hk, hkv, hks⟩ : ∃ k, (c.withHooks HookParams.lib).hv stringCountAll [s, n] = some k ∧
      ((hook stringCountAll [s, n]).join).getD (int 0) = k ∧
      (c.withHooks HookParams.lib).sortOf k = some Srt.int := by
    obtain ⟨o, ho⟩ : ∃ o, hook stringCountAll [s, n] = some o := ⟨_, rfl⟩
    cases o with
    | none =>
      exact ⟨int 0, hv_of_silent (k := ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩) hkC ho rfl rfl
        (sortOf_int 0), by rw [ho]; rfl, sortOf_int 0⟩
    | some k =>
      exact ⟨k, hv_of_value ho, by rw [ho]; rfl, hook_sorted (fun h => by cases h) hkC hsC ho⟩
  have hsR : (c.withHooks HookParams.lib).sortsOf [s, n, r, k] =
      some [Srt.string, Srt.string, Srt.string, Srt.int] := by
    exact sortsOf_eq_cons.mpr ⟨hs1, sortsOf_eq_cons.mpr ⟨hs2, sortsOf_eq_cons.mpr ⟨hs3,
      sortsOf_eq_cons.mpr ⟨hks, rfl⟩⟩⟩⟩
  have happ : HookParams.lib.app stringReplaceAll [s, n, r] =
      some (((hook stringReplace [s, n, r, ((hook stringCountAll [s, n]).join).getD (int 0)]).join).getD s) := rfl
  rw [hkv] at happ
  obtain ⟨o, ho⟩ : ∃ o, hook stringReplace [s, n, r, k] = some o := ⟨_, rfl⟩
  rw [ho] at happ
  cases o with
  | none =>
    exact ⟨k, s, hk, hv_of_silent (k := ⟨stringReplace, [Srt.string, Srt.string, Srt.string, Srt.int], Srt.string⟩)
      hkR ho rfl rfl hs1, happ, hs1⟩
  | some w =>
    exact ⟨k, w, hk, hv_of_value ho, happ, hook_sorted (fun h => by cases h) hkR hsR ho⟩

/-- `replaceAll`'s sentence holds under `HookParams.lib` in every semantics: at a silent point of
`replaceAll`, `lib`'s answer is the value of `replace` at the count under `lib`. -/
theorem replaceAllEq_lib (c : Semantics) : (c.withHooks HookParams.lib).replaceAllEq := by
  intro s n r hs hh
  obtain ⟨k, w, hk, hw, happ, hsw⟩ := libReplaceAll_parts c hs
  rw [hk, Option.bind_some, hw]
  exact hv_of_silent (k := ⟨stringReplaceAll, [Srt.string, Srt.string, Srt.string], Srt.string⟩)
    (by decide +kernel) hh rfl happ hsw

/-! ### `_RangeMap_`'s associativity where the interpretation gives `_RangeMap_` no value -/

/-- Where the interpretation gives `_RangeMap_` no value, its value at every argument list is
`hook`'s. -/
theorem hv_rmConcat_of_appNone {c : Semantics} (h : ∀ vs, c.hooks.app rmConcat vs = none)
    (vs : List GroundTerm) : c.hv rmConcat vs = (rmHook rmConcat vs).join := by
  have hf : c.fallback rmConcat vs = none := by
    unfold Semantics.fallback; split <;> simp [h]
  rw [← rmM_concat_eq]
  unfold Semantics.hv Semantics.hookRes
  rw [hf]
  split <;> cases hook rmConcat vs <;> simp

/-- A value of sort RangeMap is a range map of maximal intervals in order, or no map at all. -/
theorem rmAssoc_shape {c : Semantics} {v : GroundTerm} (h : c.sortOf v = some Srt.rangeMap) :
    (∃ es, v = rmV es ∧ rangesOK es = true) ∨ ∀ s es, v ≠ .map s es := by
  cases v with
  | map s es =>
    obtain ⟨rfl, hr, -⟩ := (rmS_sortOf_map rfl).mp h
    exact .inl ⟨es, rfl, hr⟩
  | _ => exact .inr fun _ _ he => by cases he

/-- `_RangeMap_`'s hook gives no value where its first argument is no map. -/
theorem rmAssoc_noMap_l {v : GroundTerm} (hv : ∀ s es, v ≠ .map s es) (w : GroundTerm) :
    (rmHook rmConcat [v, w]).join = none := by
  cases v <;> first | exact (hv _ _ rfl).elim | rfl

/-- `_RangeMap_`'s hook gives no value where its second argument is no map. -/
theorem rmAssoc_noMap_r {v : GroundTerm} (hv : ∀ s es, v ≠ .map s es) (w : GroundTerm) :
    (rmHook rmConcat [w, v]).join = none := by
  cases w <;> cases v <;> first | exact (hv _ _ rfl).elim | rfl

/-- **`_RangeMap_`'s associativity holds under every interpretation that gives `_RangeMap_` no
value**: both sides are `hook`'s; at three range maps they are one result (`rmConcat_assoc`), and
where one of the three is no map, neither side has a value. -/
theorem rangeMapAssocEq_of_app_none {c : Semantics} (h : ∀ vs, c.hooks.app rmConcat vs = none) :
    c.rangeMapAssocEq := by
  intro m n p hs
  simp only [sortsOf_eq_cons] at hs
  obtain ⟨hm, hn, hp, -⟩ := hs
  simp only [hv_rmConcat_of_appNone h]
  rcases rmAssoc_shape hm with ⟨es, rfl, he⟩ | hm'
  · rcases rmAssoc_shape hn with ⟨fs, rfl, hf⟩ | hn'
    · rcases rmAssoc_shape hp with ⟨gs, rfl, hg⟩ | hp'
      · exact rmConcat_assoc he hf hg
      · simp [rmAssoc_noMap_r hp']
    · simp [rmAssoc_noMap_r hn', rmAssoc_noMap_l hn']
  · simp [rmAssoc_noMap_l hm']

/-- `HookParams.lib` gives `_RangeMap_` no value. -/
theorem lib_app_rmConcat_none : ∀ vs, HookParams.lib.app rmConcat vs = none := fun _ => rfl

/-- `_RangeMap_`'s associativity holds under `HookParams.lib` in every semantics. -/
theorem rangeMapAssocEq_lib (c : Semantics) : (c.withHooks HookParams.lib).rangeMapAssocEq :=
  rangeMapAssocEq_of_app_none lib_app_rmConcat_none

/-- **`HookParams.lib` is an interpretation the text admits**, in every semantics where every Float
value is a Float literal. -/
theorem libAdmitted_lib (c : Semantics) (hfs : c.floatShapeOK = true) :
    (c.withHooks HookParams.lib).libAdmitted := by
  refine ⟨?_, isInfiniteEq_lib c hfs, rfindCharEq_lib c, findCharEq_lib c, sqrtFloatEq_lib c,
    replaceAllEq_lib c, rangeMapAssocEq_lib c⟩
  intro k hk hkey vs hvs _ _
  unfold Semantics.fallback
  rw [hookSigs_lookup k hk]
  by_cases hra : k.name = stringReplaceAll
  · have hk' := hookSigs_lookup k hk
    rw [hra, show lookupSig hookSigs stringReplaceAll =
      some ⟨stringReplaceAll, [Srt.string, Srt.string, Srt.string], Srt.string⟩ by decide +kernel] at hk'
    cases hk'
    obtain ⟨s, n, r, rfl, -, -, -⟩ := sortsOf_three hvs
    obtain ⟨_, w, -, -, happ, hsw⟩ := libReplaceAll_parts c hvs
    show ((HookParams.lib.app stringReplaceAll [s, n, r]).filter _).isSome = true
    rw [happ]
    simp [Option.filter, hsw]
  · obtain ⟨v, hv, hs⟩ := totalsVal_sort (c.withHooks HookParams.lib) hk hkey hvs
    have hne : (k.name == stringReplaceAll) = false := by simpa using hra
    have hne2 : (k.name == stringReplace) = false := by
      rcases Bool.eq_false_or_eq_true (k.name == stringReplace) with h | h
      · rw [beq_iff_eq] at h; rw [h] at hkey; exact absurd hkey (by decide)
      · exact h
    show ((if (k.name == stringReplaceAll) = true then _ else if (k.name == stringReplace) = true then _
      else if totalSilentKeys.contains k.name then totalsVal k.name vs else _).filter _).isSome = true
    simp only [hne, hne2, Bool.false_eq_true, ↓reduceIte,
      show totalSilentKeys.contains k.name = true from List.contains_iff_mem.mpr hkey, hv]
    simp [Option.filter, hs]

/-! ## `coreOK` gives `floatShapeOK` -/

open Faithful in
/-- A sort of constructor terms is not Float (`genWf`). -/
theorem consSorts_not_float {c : Semantics} (hg : genWf c = true) {s : Srt}
    (hs : (consSorts c).contains s = true) : s ≠ Srt.float := by
  unfold genWf at hg
  simp only [Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.2 s (List.contains_iff_mem.mp hs)
  simp only [bne_iff_ne, ne_eq] at this
  exact this.1.1.2

open Faithful Faithful.Model in
/-- **`coreOK` gives `floatShapeOK`**: a constructor's, a subsort's upper, an overloading symbol's
and a raw parameter's result sort is a sort of constructor terms (`genWf`, `overloadsOK`), which is
not Float; no token or byte sort is Float (`LitsApart`); no collection sort is Float
(`collSortsOK`). So under `coreOK` every value of sort Float is a Float literal. -/
theorem floatShapeOK_of_coreOK {c : Semantics} (h : c.coreOK = true) : c.floatShapeOK = true := by
  obtain ⟨-, hf, -, -, -⟩ := Semantics.coreOK_parts h
  have ho := Semantics.coreOK_ovls h
  unfold Semantics.faithCoreOK at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hg⟩, hcs⟩, -⟩, -⟩, -⟩, hl⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have hg' := hg
  unfold genWf at hg'
  simp only [Bool.and_eq_true, List.all_eq_true] at hg'
  unfold Semantics.floatShapeOK
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨fun k hk => consSorts_not_float hg (hg'.1.1.1.1 k hk), fun p hp => ?_⟩, ?_⟩, fun k hk => ?_⟩, ?_⟩,
    fun k hk => ?_⟩
  · exact consSorts_not_float hg (hg'.1.1.1.2 p hp).1
  · unfold LitsApart at hl
    simp only [Bool.and_eq_true] at hl
    simpa using hl.2
  · unfold collSortsOK at hcs
    have := List.all_eq_true.mp hcs k (List.mem_append_right _ hk)
    unfold collSortOK at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1.1.1.2
  · intro k hk
    obtain ⟨o, ho', rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp ho'
    unfold Semantics.overloadsOK at ho
    have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ho).1 (o, i) (by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simpa using hi.1, by simp [List.getElem_zipIdx, hi.2]⟩)
    simp only [Bool.and_eq_true] at this
    exact consSorts_not_float hg this.1.1.1.1.2
  · cases hraw : k.raw
    · rfl
    · have := hg'.1.2 k hk
      rw [hraw] at this
      have hne := consSorts_not_float hg (s := k.sig.result) (by simpa using this)
      simpa using hne

/-- **`HookParams.lib` is admitted in every semantics meeting `coreOK`.** -/
theorem libAdmitted_lib_of_coreOK {c : Semantics} (h : c.coreOK = true) :
    (c.withHooks HookParams.lib).libAdmitted :=
  libAdmitted_lib c (floatShapeOK_of_coreOK h)

end KCore
