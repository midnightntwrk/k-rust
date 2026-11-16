/-
  KCore, checked layer: an interpretation of the silent points under which the library's sentences
  over Γ's symbols hold at values.

  At a silent point (`silentTable`) Γ states the interpretation's value (`Semantics.fallback`). A
  library sentence whose instance at values reaches such a point is, at that instance, a condition
  on the interpretation; the interpretations the text admits are those meeting every such condition.

  - `HookParams.lib`: `HookParams.totals`' values at the silent points of the `total` symbols, and:
    `maxValueFloat` at a format with a field of 1 that format's NaN, the five Float comparisons at a
    silent point `false`, `=/=Float` `true`; nothing elsewhere.
  - `libSentences`: the library sentences over Γ's symbols, besides the `functional` sentences of
    `totalSilentKeys`, that read the interpretation (test/LibProbe.lean checks the list).
  - `Semantics.libAdmitted c`: `silentTotal` and one condition per sentence of `libSentences`
    (`neFloatEq`, `isInfiniteEq`, `rfindCharEq`), each the sentence at the values where its left
    side is at a silent point. The conditions are named, not read off the text: a statement over
    every library sentence would hold the reader's selection of sentences and a meaning of KORE
    patterns at values, and Γ's meaning of a sentence is the reader's translation.
  - `libAdmitted_lib`: `HookParams.lib` meets them in every semantics with `floatShapeOK`, so in
    every semantics meeting `coreOK` (`floatShapeOK_of_coreOK`, `libAdmitted_lib_of_coreOK`).
-/
import KcoreSpec.ParamsTotal

set_option autoImplicit false

namespace KCore

/-- The value `HookParams.lib` gives `maxValueFloat` at two Ints: at a format with a field of 1
(`p = 1` or `e = 1`, both positive) its one NaN, `2 ^ (p + e)` (`KFloat.thinOK`); nothing elsewhere. -/
def libMaxValue (vs : List GroundTerm) : Option GroundTerm :=
  match vs with
  | [x, y] => (asInt x).bind fun p => (asInt y).bind fun e =>
      if 1 ≤ p ∧ 1 ≤ e ∧ (p = 1 ∨ e = 1) then
        some (.dv Srt.float (.float p.toNat e.toNat (2 ^ (p.toNat + e.toNat))))
      else none
  | _ => none

/-- The Float comparisons `HookParams.lib` gives `false` at their silent points. -/
def libFalseCmps : List Sym := [floatLe, floatLt, floatGe, floatGt, floatEq]

/-- **An interpretation under which the library's sentences hold at values**: `totalsVal` at the
symbols of `totalSilentKeys`; `maxValueFloat` at a format with a field of 1 its NaN (`libMaxValue`);
`<=Float`, `<Float`, `>=Float`, `>Float`, `==Float` `false` and `=/=Float` `true`; nothing elsewhere.
Read only at silent points (`Semantics.fallback`), where `hook` gives no value. -/
def HookParams.lib : HookParams :=
  ⟨fun f vs =>
    if totalSilentKeys.contains f then totalsVal f vs
    else if f == floatMaxValue then libMaxValue vs
    else if f == floatNe then some (bool true)
    else if libFalseCmps.contains f then some (bool false)
    else Option.none⟩

/-- The library sentences over Γ's symbols, other than the `functional` sentences of
`totalSilentKeys` (`Semantics.silentTotal`), that read the interpretation at some value, by their
line in domains.md (K 7.1.337), and the condition each states on it: `=/=Float` (1648),
`isInfinite` (1673), `rfindChar` (1893). test/LibProbe.lean checks the list against the sentences a
text holds: a sentence that reads the interpretation at a probed point is one of these or a
`functional` sentence of `totalSilentKeys`; on f2-examples/allbuiltins.kompile.kore, every module of
the K 7.1.337 builtin files the library holds, the list is closed. -/
def libSentences : List (Nat × String) :=
  [(1648, "neFloatEq"), (1673, "isInfiniteEq"), (1893, "rfindCharEq")]

/-! ## The conditions the library's sentences state on the interpretation -/

namespace Semantics
variable (c : Semantics)

/-- The value of the interpreted symbol `f` at `vs` in Γ's reading (`hookRes`), none where Γ
states ⊥. -/
def hv (f : Sym) (vs : List GroundTerm) : Option GroundTerm := (c.hookRes f vs).join

/-- **domains.md 1648** `F1 =/=Float F2 => notBool (F1 ==Float F2)`, at the pairs of Floats where
`=/=Float` is at a silent point (there both sides read the interpretation; elsewhere neither does). -/
def neFloatEq : Prop :=
  ∀ a b, c.sortsOf [a, b] = some [Srt.float, Srt.float] → hook floatNe [a, b] = some none →
    c.hv floatNe [a, b] = (c.hv floatEq [a, b]).bind fun v => c.hv boolNot [v]

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

/-- **The interpretations the text admits**: every library sentence over Γ's symbols, set
idempotence excepted, holds at the values where it reads the interpretation: the `functional`
sentences of `totalSilentKeys` (`silentTotal`) and the sentences of `libSentences` (`neFloatEq`,
`isInfiniteEq`, `rfindCharEq`). At the other values a library sentence reads `hook` only, and
holds or fails for every interpretation alike. Γ does not state it; the statements over Γ hold
for every interpretation, admitted or not. -/
def libAdmitted : Prop :=
  c.silentTotal ∧ c.neFloatEq ∧ c.isInfiniteEq ∧ c.rfindCharEq

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

/-! ### The Float comparisons, `isInfinite`, `rfindChar` under `HookParams.lib` -/

theorem flCmp_none {t t' : Option Ordering → Bool} {vs : List GroundTerm} (h : flCmp t vs = none) :
    flCmp t' vs = none := by
  match vs with
  | [a, b] =>
    unfold flCmp at h ⊢
    cases ha : asFloat a <;> cases hb : asFloat b <;> simp_all
  | [] | [_] | _ :: _ :: _ :: _ => rfl

/-- `=/=Float`'s sentence holds under `HookParams.lib` in every semantics: where `=/=Float` is silent
so is `==Float` (both read the two Floats' data), and `lib` gives them `true` and `false`. -/
theorem neFloatEq_lib (c : Semantics) : (c.withHooks HookParams.lib).neFloatEq := by
  intro a b _ hh
  have h1 : hook floatNe [a, b] = some (flCmp (fun o => o != some .eq) [a, b]) := rfl
  have h2 : hook floatEq [a, b] = some (flCmp (fun o => o == some .eq) [a, b]) := rfl
  rw [h1, Option.some.injEq] at hh
  have he : hook floatEq [a, b] = some none := by rw [h2, flCmp_none hh]
  rw [hh] at h1
  rw [hv_of_silent (k := ⟨floatNe, [Srt.float, Srt.float], Srt.bool⟩) rfl h1 rfl rfl (sortOf_bool true),
    hv_of_silent (k := ⟨floatEq, [Srt.float, Srt.float], Srt.bool⟩) rfl he rfl rfl (sortOf_bool false),
    Option.bind_some, hv_of_value (rfl : hook boolNot [bool false] = some (some (bool true)))]
  rfl

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

/-- `isInfinite`'s sentence holds under `HookParams.lib` where every Float value is a Float literal:
at a Float of a format with a field of 1, `isInfinite` is `false`, `maxValueFloat` the format's NaN,
both comparisons `false`, `--Float` of the NaN the NaN. -/
theorem isInfiniteEq_lib (c : Semantics) (hfs : c.floatShapeOK = true) :
    (c.withHooks HookParams.lib).isInfiniteEq := by
  intro F hF hh
  obtain ⟨p, e, b, rfl, hok⟩ := shape_float (c := c.withHooks HookParams.lib) hfs hF
  obtain ⟨hp, he⟩ := KFloat.ok_pos hok
  have hsp : KFloat.spec? p e = none := by
    have h0 : hook floatIsInfinite [.dv Srt.float (.float p e b)] =
        some (((KFloat.spec? p e).map fun sp => (p, e, sp, KFloat.unpackBits sp b)).map
          fun (_, _, _, u) => bool (KFloat.isInf u)) := rfl
    rw [h0] at hh
    cases hs : KFloat.spec? p e with
    | none => rfl
    | some _ => rw [hs] at hh; cases hh
  have h1 : p = 1 ∨ e = 1 := by
    unfold KFloat.spec? at hsp; split at hsp
    · cases hsp
    · rename_i h; omega
  have hpi : asFloat (.dv Srt.float (.float p e b)) = none := by
    unfold asFloat; simp [hsp]
  let m : GroundTerm := .dv Srt.float (.float p e (2 ^ (p + e)))
  have hm : asFloat m = none := by
    unfold asFloat; simp [m, hsp]
  have hms : (c.withHooks HookParams.lib).sortOf m = some Srt.float := by
    rw [sortOf_dv]; exact ⟨by simp [dvOK, thin_nan_ok hp he h1], rfl⟩
  rw [hv_of_silent (k := ⟨floatIsInfinite, [Srt.float], Srt.bool⟩) rfl hh rfl rfl
      (sortOf_bool false)]
  have hpr : hook floatPrecision [.dv Srt.float (.float p e b)] = some (some (int p)) := by
    rw [hook_floatPrecision]; simp [flFmt, hp, he]
  have hex : hook floatExponentBits [.dv Srt.float (.float p e b)] = some (some (int e)) := by
    rw [hook_floatExponentBits]; simp [flFmt, hp, he]
  have hmx : hook floatMaxValue [int p, int e] = some none := by
    have h0 : hook floatMaxValue [int p, int e] = some (flAt KFloat.maxValue [int p, int e]) := rfl
    rw [h0]; simp [flAt, asInt, int, hsp]
  have hmv : HookParams.lib.app floatMaxValue [int p, int e] = some m := by
    show libMaxValue [int p, int e] = some m
    have : (1 : Int) ≤ p ∧ (1 : Int) ≤ e ∧ ((p : Int) = 1 ∨ (e : Int) = 1) := by omega
    simp [libMaxValue, asInt, int, this, m]
  have hgt : hook floatGt [.dv Srt.float (.float p e b), m] = some none := by
    have h0 : hook floatGt [.dv Srt.float (.float p e b), m] =
      some (flCmp (fun o => o == some .gt) [.dv Srt.float (.float p e b), m]) := rfl
    rw [h0]; simp [flCmp, hpi]
  have hng : hook floatNeg [m] = some none := by
    have h0 : hook floatNeg [m] = some (fl1 (fun _ => Float.Model.UnpackedFloat.neg) [m]) := rfl
    rw [h0]; simp [fl1, hm]
  have hlt : hook floatLt [.dv Srt.float (.float p e b), m] = some none := by
    have h0 : hook floatLt [.dv Srt.float (.float p e b), m] =
      some (flCmp (fun o => o == some .lt) [.dv Srt.float (.float p e b), m]) := rfl
    rw [h0]; simp [flCmp, hpi]
  rw [hv_of_value hpr, Option.bind_some, hv_of_value hex, Option.bind_some,
    hv_of_silent (k := ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩) rfl hmx rfl hmv
      hms, Option.bind_some,
    hv_of_silent (k := ⟨floatGt, [Srt.float, Srt.float], Srt.bool⟩) rfl hgt rfl rfl
      (sortOf_bool false), Option.bind_some,
    hv_of_silent (k := ⟨floatNeg, [Srt.float], Srt.float⟩) rfl hng rfl rfl
      hms, Option.bind_some,
    hv_of_silent (k := ⟨floatLt, [Srt.float, Srt.float], Srt.bool⟩) rfl hlt rfl rfl
      (sortOf_bool false), Option.bind_some,
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

/-- **`HookParams.lib` is an interpretation the text admits**, in every semantics where every Float
value is a Float literal. -/
theorem libAdmitted_lib (c : Semantics) (hfs : c.floatShapeOK = true) :
    (c.withHooks HookParams.lib).libAdmitted := by
  refine ⟨?_, neFloatEq_lib c, isInfiniteEq_lib c hfs, rfindCharEq_lib c⟩
  intro k hk hkey vs hvs _ _
  obtain ⟨v, hv, hs⟩ := totalsVal_sort (c.withHooks HookParams.lib) hk hkey hvs
  unfold Semantics.fallback
  rw [hookSigs_lookup k hk]
  show ((if totalSilentKeys.contains k.name then totalsVal k.name vs else _).filter _).isSome = true
  simp only [show totalSilentKeys.contains k.name = true from List.contains_iff_mem.mpr hkey, ↓reduceIte, hv]
  simp [Option.filter, hs]

/-! ## `coreOK` gives `floatShapeOK` -/

open Faithful in
/-- A sort of constructor terms is not Float (`genWf`). -/
theorem consSorts_not_float {c : Semantics} (hg : genWf c = true) {s : Srt}
    (hs : (consSorts c).contains s = true) : s ≠ Srt.float := by
  unfold genWf at hg
  simp only [Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.2 s (List.contains_iff_mem.mp hs)
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
  refine ⟨⟨⟨⟨⟨fun k hk => consSorts_not_float hg (hg'.1.1.1 k hk), fun p hp => ?_⟩, ?_⟩, fun k hk => ?_⟩, ?_⟩,
    fun k hk => ?_⟩
  · exact consSorts_not_float hg (hg'.1.1.2 p hp).1
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
    have := List.all_eq_true.mp ho (o, i) (by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simpa using hi.1, by simp [List.getElem_zipIdx, hi.2]⟩)
    simp only [Bool.and_eq_true] at this
    exact consSorts_not_float hg this.1.1.1.1.2
  · cases hraw : k.raw
    · rfl
    · have := hg'.2 k hk
      rw [hraw] at this
      have hne := consSorts_not_float hg (s := k.sig.result) (by simpa using this)
      simpa using hne

/-- **`HookParams.lib` is admitted in every semantics meeting `coreOK`.** -/
theorem libAdmitted_lib_of_coreOK {c : Semantics} (h : c.coreOK = true) :
    (c.withHooks HookParams.lib).libAdmitted :=
  libAdmitted_lib c (floatShapeOK_of_coreOK h)

end KCore
