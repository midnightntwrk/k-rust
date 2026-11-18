/-
  Silent points: where K's text says nothing of an interpreted operation's value, KCore's theory
  states the interpretation's value (`Faithful.ΓFallback`, `Semantics.fallback`), so over all
  interpretations it entails neither that there is no value nor a particular value. Run from the
  package root: `lake env lean test/SilentPoints.lean`.

  - The schema `undetermined`: for every semantics with `coreOK`, and every argument list of an
    interpreted symbol's argument sorts at which `hook` gives no value and which the library's
    `silentTable` calls silent, two interpretations (the one giving nothing, `HookParams.none`, and
    one giving a value `v` of the result sort) both have models of Γ, and the models differ there:
    the application is ⊥ in every model of the first and `v` in every model of the second.
  - The schema at one point of every key of `silentTable` (`pts`), in the semantics of
    `f2-examples/strbytes.kompile.kore` (`coreOK`, no function): `hook` gives no value, the point is
    silent, its arguments have the signature's sorts and `v` has exactly the result sort (decided),
    so neither `f(vs) = ⊥` nor `f(vs) = v` holds for every interpretation (`pts_undetermined`).
    `Bytes2Int` gives no value only at an Endianness or Signedness that is no constructor of BYTES:
    its points are in `strbytes` with one more Endianness constructor, which `coreOK` admits
    (`bytes2Int_extra`, with `Int2Bytes` at that constructor). RANGEMAP's (`lookup` and
    `find_range` off the keys, `r|->`, update, `[_ <- undef]` and `removeAll` at no proper range,
    `_RangeMap_` at two maps with a key in common, `[_ <- undef]` and `removeAll` at a proper range
    no part of which is in the map) are in a semantics with the Range constructor
    (`rangeMap_undetermined`), `[5, 3) r|-> 7` among them.
  - At a described point of the same keys, the result is `hook`'s value whatever the
    interpretation (`vals_hookRes`).
  - Where the text says there is no value, Γ states ⊥ for every semantics (`gamma_bot`), at each
    `#False` / `#Bottom` point of the text (`bots`), `replaceAtBytes` at a range that leaves `dest`
    included.
  - `replaceAtBytes` has no silent point; `isInfinite` against its equation on the
    special data of binary32 and binary64; the residual at a surrogate: no String value has a code
    point 0xD800 … 0xDFFF, so `ordChar(chrChar(55296)) = 55296` is refuted at every interpretation.
  - The evaluation-level part at a one-entry table made here (`hookResWith`).
  - `FallbackTotal` (ParamsTotal.lean): an interpretation satisfying it at `strbytes` (`fbH_total`),
    and `HookParams.none` not (`none_not_total`).
  - `<=Set` is inclusion and no key of `silentTable`: at `.Set`, `{1}`, `{1, 2}` against each other
    the result is the text's value and Γ states it, for every interpretation (`incl_gamma`), and
    `S <=Set S` is true at every set (`setInclusion_refl`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.SilentPointsTest

open KCore ML Faithful

/-! ## The evaluation, at a one-entry table -/

/-- `silent` at a table given as an argument. -/
def silentWith (T : List (Sym × (List GroundTerm → Bool))) (f : Sym) (vs : List GroundTerm) : Bool :=
  match T.find? (·.1 == f) with
  | some (_, p) => p vs
  | none => false

/-- `Semantics.hookRes` at a table given as an argument. -/
def hookResWith (T : List (Sym × (List GroundTerm → Bool))) (c : Semantics) (f : Sym)
    (vs : List GroundTerm) : Option (Option GroundTerm) :=
  if silentWith T f vs then (hook f vs).map fun r => r.or (c.fallback f vs) else hook f vs

/-- At the library's table, `hookResWith` is `hookRes`. -/
theorem hookRes_eq (c : Semantics) (f : Sym) (vs : List GroundTerm) :
    c.hookRes f vs = hookResWith silentTable c f vs := rfl

/-- A table with one entry: every point of `findString` where `hook` gives no value is silent. -/
def T1 : List (Sym × (List GroundTerm → Bool)) := [(stringFind, fun _ => true)]

def sem : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.string, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

def abc : List GroundTerm := [strV "abc".toList, strV "b".toList, int 7]

/-- `findString("abc", "b", 7)`: `hook` gives no value; at `T1`, no value under `HookParams.none`
and `5` under `constH 5`, while a value of `hook` is kept whatever the interpretation. -/
example : hook stringFind abc = some none ∧
    hookResWith T1 (sem.withHooks HookParams.none) stringFind abc = some none ∧
    hookResWith T1 (sem.withHooks (constH (int 5))) stringFind abc = some (some (int 5)) ∧
    hookResWith T1 (sem.withHooks (constH (int 5))) stringFind [strV "abc".toList, strV "b".toList, int 0] =
      some (some (int 1)) ∧
    hookResWith T1 (sem.withHooks (constH (strV []))) stringFind abc = some none := by
  decide +kernel

/-! ## Γ, at a silent point of the library's table -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

/-- At a silent point, `Γ (c.withHooks H)` holds the fallback's graph. -/
theorem gamma_fallback (c : Semantics) (H : HookParams) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : (c.withHooks H).sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    Γ (c.withHooks H) (appP (c.withHooks H) k vs ≡ (match (c.withHooks H).fallback k.name vs with
      | some v => den (c.withHooks H) v
      | none => ⊥)) :=
  Or.inr (Or.inl ⟨k, vs, (lookupSig_spec hks).1, hvs, hh, hs, rfl⟩)

theorem fallback_none (c : Semantics) (k : CtorSig) (vs : List GroundTerm) :
    (c.withHooks HookParams.none).fallback k.name vs = none := by
  unfold Semantics.fallback; split <;> rfl

theorem fallback_const (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) (vs : List GroundTerm) {v : GroundTerm}
    (hv : c.sortOf v = some k.result) : (c.withHooks (constH v)).fallback k.name vs = some v := by
  unfold Semantics.fallback; rw [hks, Semantics.sortOf_withHooks c _ hr]
  simp [Semantics.withHooks, constH, Option.filter, hv]

/-- **Γ does not determine a silent point.** Over all interpretations, Γ entails neither that the
application has no value nor that it is `v`: under `HookParams.none` it is ⊥ in every model, under
`constH v` it is `v` in every model, and both theories have models (`sound_hyp`). -/
theorem undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true)
    {v : GroundTerm} (hv : c.sortOf v = some k.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ den (c.withHooks H) v)) := by
  constructor
  · -- under `constH v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constH v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constH v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback c (constH v) hks (by rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs) hh hs)
    rw [fallback_const c hr hks vs hv] at hfb
    have hbot := hall (constH v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constH v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback c HookParams.none hks (by rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs) hh hs)
    rw [fallback_none c k vs] at hfb
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-- **Off the silent points, Γ states ⊥ where `hook` gives no value**, in every semantics. -/
theorem gamma_bot (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = false) :
    Γ c (appP c k vs ≡ ⊥) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, none, hk, hvs, hh, fun _ => hs, rfl⟩)))))

/-! ## A test semantics: `strbytes` (STRING, BYTES, LIST, SET, MAP imported; no function) -/

definition_of defn from "f2-examples/strbytes.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

tables_of T from "f2-examples/strbytes.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

set_option maxHeartbeats 1000000 in
open Faithful.Model in
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fns_nil : c.fns = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := fns_nil
  have hrc : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c.withHooks H) (show ∀ k ∈ c.params, k.raw = false by decide +kernel)⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-! ## Values -/

def ki (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (int n)
def lst (es : List GroundTerm) : GroundTerm := .list Srt.list es
def st (es : List GroundTerm) : GroundTerm := .set Srt.set es
def mp (es : List (GroundTerm × GroundTerm)) : GroundTerm := .map Srt.map es
def s (t : String) : GroundTerm := strV t.toList
def b (t : String) : GroundTerm := bytesV t.toList
def f64 (n : Nat) : GroundTerm := .dv Srt.float (.float 53 11 n)
def f32 (n : Nat) : GroundTerm := .dv Srt.float (.float 24 8 n)
def be : GroundTerm := .ctor bigEndianBytes []
/-- `1.0p1x8`, a value of a format with a field of 1 (`KFloat.thinOK`). -/
def t18 : GroundTerm := .dv Srt.float (.float 1 8 127)
/-- `1.0p2x1` and `NaNp2x1`, values of a format of one exponent bit, where neither the comparisons
nor `isNaN` and `isInfinite` are computed (`asDatum`). -/
def t21 : GroundTerm := .dv Srt.float (.float 2 1 1)
def n21 : GroundTerm := .dv Srt.float (.float 2 1 8)
def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-! ## The schema at one point of every key -/

/-- A point: the interpreted symbol, its arguments, and a value of its result sort (E2). -/
structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm
  deriving DecidableEq

/-- One point per key of `silentTable` but `Bytes2Int` (some keys two). The value `v` has exactly
the result sort: `ki 0` (`inj{Int,KItem}(0)`) for `L[I]`'s KItem, `.List`, `0.0`, `0`, `""`,
`true`, `.Bytes`. -/
def pts : List Pt :=
  [⟨listGet, [lst [ki 1], int 3], ki 0⟩,
   ⟨listRange, [lst [ki 1], int 1, int 1], lst []⟩,
   ⟨floatAdd, [f64 0x3FF0000000000000, f32 0x3F800000], f64 0⟩,
   ⟨floatSub, [f64 0x3FF0000000000000, f32 0x3F800000], f64 0⟩,
   ⟨floatMul, [f64 0x3FF0000000000000, f32 0x3F800000], f64 0⟩,
   ⟨floatDiv, [f64 0x3FF0000000000000, f32 0x3F800000], f64 0⟩,
   ⟨floatRem, [f64 0x3FF0000000000000, f32 0x3F800000], f64 0⟩,
   ⟨floatRound, [f64 0x3FF0000000000000, int 0, int 8], f64 0⟩,
   ⟨floatRound, [f64 0x3FF0000000000000, int 1, int 8], f64 0⟩,
   ⟨int2Float, [int 1, int 24, int 0], f64 0⟩,
   ⟨floatMaxValue, [int 0, int 8], f64 0⟩,
   ⟨floatMinValue, [int 53, int 1], f64 0⟩,
   ⟨stringOrd, [s "ab"], int 0⟩,
   ⟨stringChr, [int (-1)], s ""⟩,
   ⟨stringChr, [int 55296], s ""⟩,
   ⟨stringSubstr, [s "abc", int 2, int 1], s ""⟩,
   ⟨stringSubstr, [s "abc", int 1, int 1], s ""⟩,
   ⟨stringFind, [s "abc", s "b", int 7], int 0⟩,
   ⟨stringRfind, [s "abc", s "b", int (-1)], int 0⟩,
   ⟨stringFindChar, [s "abc", s "b", int 7], int 0⟩,
   ⟨stringRfindChar, [s "abc", s "b", int 7], int 0⟩,
   ⟨string2Int, [s "x"], int 0⟩,
   ⟨string2Base, [s "10", int 1], int 0⟩,
   ⟨stringReplace, [s "a", s "a", s "b", int (-1)], s ""⟩,
   ⟨string2Bool, [s "x"], bool true⟩,
   ⟨stringCountAll, [s "a", s ""], int 0⟩,
   ⟨stringReplaceAll, [s "a", s "", s "b"], s ""⟩,
   ⟨bytesMemset, [b "abc", int 0, int 1, int 200], b ""⟩,
   ⟨int2Bytes, [int (-1), int 0, be], b ""⟩,
   ⟨floatSqrt, [f64 0x8000000000000000], f64 0⟩, ⟨floatSqrt, [f64 0], f64 0⟩,
   ⟨floatNeg, [t18], f64 0⟩, ⟨floatAbs, [t18], f64 0⟩, ⟨floatFloor, [t18], f64 0⟩,
   ⟨floatCeil, [t18], f64 0⟩, ⟨floatTrunc, [t18], f64 0⟩,
   ⟨floatLe, [t21, t21], bool true⟩, ⟨floatLt, [t21, f64 0], bool true⟩, ⟨floatGe, [f64 0, t21], bool true⟩,
   ⟨floatGt, [t21, t21], bool true⟩, ⟨floatEq, [t21, t21], bool true⟩, ⟨floatNe, [t21, t21], bool false⟩,
   ⟨floatIsNaN, [n21], bool false⟩, ⟨floatIsInfinite, [t21], bool true⟩,
   ⟨intPowMod, [int (-2), int 3, int 5], int 0⟩, ⟨intPowMod, [int 2, int (-1), int 5], int 0⟩,
   ⟨intPow, [int 2, int (-1)], int 0⟩,
   ⟨listSet, [lst [ki 1], int 1, ki 3], lst []⟩, ⟨listSet, [lst [ki 1], int (-1), ki 3], lst []⟩,
   ⟨listMake, [int (-1), ki 7], lst []⟩,
   ⟨listUpdateAll, [lst [ki 1, ki 2], int 1, lst [ki 8, ki 9]], lst []⟩,
   ⟨listFill, [lst [ki 1], int 0, int 2, ki 7], lst []⟩]

/-- RANGEMAP's seven keys of `silentTable`. -/
def rmKeysSilent : List Sym := [rmElem, rmConcat, rmLookup, rmFindRange, rmUpdate, rmRemove, rmRemoveAll]

/-- Every key but `Bytes2Int` and RANGEMAP's has a point here (`Bytes2Int`'s are in `ptsB`,
RANGEMAP's in `ptsR`, at other semantics: `ptsR_cover`). -/
theorem pts_cover : silentTable.all (fun e => e.1 == bytes2Int || pts.any (·.f == e.1) ||
    rmKeysSilent.contains e.1) = true := by
  decide +kernel

/-- E1 and E2 at every point: the symbol's signature, its arguments of the argument sorts, no value
of `hook`, a silent point, and `v` of exactly the result sort. -/
theorem pts_ok : pts.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **E3: Γ determines none of the points**: over all interpretations it entails neither that the
application has no value nor that it is the point's `v`. -/
theorem pts_undetermined : ∀ p ∈ pts,
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v)) := by
  intro p hp
  have h := List.all_eq_true.mp pts_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hks, hvs⟩, hh⟩, hs⟩, hv⟩ := h
  have hname : (sig p.f).name = p.f := (lookupSig_spec hks).2
  exact undetermined c coreOK (by decide +kernel) (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact hs) hv (fnHyp _) (fnHyp _)

/-! ## `Bytes2Int` and `Int2Bytes` at an Endianness that is no constructor of BYTES -/

/-- The next symbol number of `strbytes`. -/
noncomputable def midN : Sym := c.symBase + (c.symNames.length - c.sortNames.length)

/-- `strbytes` with one more constructor of sort Endianness: `coreOK` admits it (`c2_coreOK`), and
`enumShapesOK` does not (the deciders count on `Bytes2Int`'s totality only under it). -/
noncomputable def c2 : Semantics :=
  { c with ctors := c.ctors ++ [⟨midN, [], Srt.endianness⟩], symNames := c.symNames ++ ["LblmidEndianBytes"] }

theorem c2_coreOK : c2.coreOK = true := by decide_cheap
theorem c2_enumShapes : c2.enumShapesOK = false := by decide +kernel

theorem fnHyp2 (H : HookParams) : FnHyp (c2.withHooks H) := by
  have h : (c2.withHooks H).fns = [] := fns_nil
  have hrc : (c2.withHooks H).readsConfined = false :=
    (Semantics.readsConfined_withHooks c2 H).trans readsConfined_c
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c2.withHooks H) (show ∀ k ∈ c2.params, k.raw = false by decide +kernel)⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-- `Bytes2Int(b"a", mid, Signed)` and `Int2Bytes(1, 0, mid)`, `mid` the added constructor. -/
noncomputable def ptsB : List Pt :=
  [⟨bytes2Int, [b "a", .ctor midN [], .ctor signedBytes []], int 0⟩,
   ⟨int2Bytes, [int 1, int 0, .ctor midN []], b ""⟩]

theorem ptsB_ok : ptsB.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c2.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c2.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **`Bytes2Int` is not inert**: at an added constructor of Endianness, Γ determines neither ⊥ nor a
value (and likewise `Int2Bytes`). -/
theorem bytes2Int_extra : ∀ p ∈ ptsB,
    ¬ (∀ H : HookParams, Γ (c2.withHooks H) ⊧ (appP (c2.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c2.withHooks H) ⊧
      (appP (c2.withHooks H) (sig p.f) p.vs ≡ den (c2.withHooks H) p.v)) := by
  intro p hp
  have h := List.all_eq_true.mp ptsB_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hks, hvs⟩, hh⟩, hs⟩, hv⟩ := h
  have hname : (sig p.f).name = p.f := (lookupSig_spec hks).2
  exact undetermined c2 c2_coreOK (by decide +kernel) (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact hs) hv (fnHyp2 _) (fnHyp2 _)

/-! ## RANGEMAP's silent points -/

/-- A semantics with the Range constructor (`Range` of two KItems, so that Range has values), Int
and Range below KItem, the configuration `<k> K </k>` with the generated counter, and no function
(the cells as in ModelItesWitness.lean). -/
def c3 : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := []
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c3 := .of_nil rfl (by decide +kernel)

theorem c3_coreOK : c3.coreOK = true := by decide_cheap

theorem fnHyp3 (H : HookParams) : FnHyp (c3.withHooks H) := by
  have h : (c3.withHooks H).fns = [] := rfl
  have hrc : (c3.withHooks H).readsConfined = false :=
    (Semantics.readsConfined_withHooks c3 H).trans (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c3.withHooks H) (show ∀ k ∈ c3.params, k.raw = false by decide +kernel)⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-- `[5, 3) r|-> 7`; `[0,3) ↦ 7` with `[2,5) ↦ 8` (the key 2 in both); `lookup` and `find_range`
off the keys (of `[0,3) ↦ 7`, at 5); update, `[_ <- undef]` and `removeAll` at the range `[3, 3)`
and at the member `7`: no proper ranges; `[_ <- undef]` and `removeAll` of `[0,3) ↦ 7` at the
proper range `[5, 7)`, no part of which is in the map. -/
def ptsR : List Pt :=
  [⟨rmElem, [rangeT 5 3, ki 7], rmV []⟩,
   ⟨rmConcat, [rmV [(rangeT 0 3, ki 7)], rmV [(rangeT 2 5, ki 8)]], rmV []⟩,
   ⟨rmRemove, [rmV [(rangeT 0 3, ki 7)], rangeT 5 7], rmV []⟩,
   ⟨rmRemoveAll, [rmV [(rangeT 0 3, ki 7)], st [.inj Srt.range Srt.kitem (rangeT 5 7)]], rmV []⟩,
   ⟨rmLookup, [rmV [(rangeT 0 3, ki 7)], ki 5], ki 0⟩,
   ⟨rmFindRange, [rmV [(rangeT 0 3, ki 7)], ki 5], rangeT 0 1⟩,
   ⟨rmUpdate, [rmV [], rangeT 3 3, ki 0], rmV []⟩,
   ⟨rmRemove, [rmV [], rangeT 3 3], rmV []⟩,
   ⟨rmRemoveAll, [rmV [], st [ki 7]], rmV []⟩]

/-- Each of RANGEMAP's seven keys has a point in `ptsR`. -/
theorem ptsR_cover : rmKeysSilent.all (fun f => ptsR.any (·.f == f)) = true := by decide +kernel

theorem ptsR_ok : ptsR.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c3.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c3.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **RANGEMAP's silent points are undetermined**: Γ entails neither ⊥ nor a value there. -/
theorem rangeMap_undetermined : ∀ p ∈ ptsR,
    ¬ (∀ H : HookParams, Γ (c3.withHooks H) ⊧ (appP (c3.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c3.withHooks H) ⊧
      (appP (c3.withHooks H) (sig p.f) p.vs ≡ den (c3.withHooks H) p.v)) := by
  intro p hp
  have h := List.all_eq_true.mp ptsR_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hks, hvs⟩, hh⟩, hs⟩, hv⟩ := h
  have hname : (sig p.f).name = p.f := (lookupSig_spec hks).2
  exact undetermined c3 c3_coreOK (by decide +kernel) (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact hs) hv (fnHyp3 _) (fnHyp3 _)

/-! ## E4: at a described point, `hook`'s value whatever the interpretation -/

/-- Described points of the keys, and of `<=Set` (which has no silent point), with `hook`'s value. -/
def vals : List Pt :=
  [⟨listGet, [lst [ki 1], int (-1)], ki 1⟩,
   ⟨listRange, [lst [ki 1], int 1, int 0], lst []⟩,
   ⟨floatAdd, [f64 0x3FF0000000000000, f64 0x3FF0000000000000], f64 0x4000000000000000⟩,
   ⟨floatRound, [f64 0x3FF0000000000000, int 24, int 8], f32 0x3F800000⟩,
   ⟨floatMaxValue, [int 24, int 8], f32 0x7F7FFFFF⟩,
   ⟨stringOrd, [s "a"], int 97⟩,
   ⟨stringChr, [int 97], s "a"⟩,
   ⟨stringSubstr, [s "abc", int 0, int 0], s ""⟩,
   ⟨stringSubstr, [s "abc", int 3, int 3], s ""⟩,
   ⟨stringSubstr, [s "abc", int 1, int 2], s "b"⟩,
   ⟨stringFind, [s "abc", s "b", int 3], int (-1)⟩,
   ⟨stringRfind, [s "abc", s "b", int 3], int 1⟩,
   ⟨stringFindChar, [s "abc", s "", int 7], int (-1)⟩,
   ⟨string2Int, [s "-12"], int (-12)⟩,
   ⟨string2Base, [s "ff", int 16], int 255⟩,
   ⟨stringReplace, [s "aa", s "a", s "b", int 1], s "ba"⟩,
   ⟨string2Bool, [s "false"], bool false⟩,
   ⟨bytesReplaceAt, [b "ab", int 1, b "c"], b "ac"⟩,
   ⟨bytesMemset, [b "abc", int 0, int 3, int 0], b "\x00\x00\x00"⟩,
   ⟨int2Bytes, [int 1, int 255, be], b "\xff"⟩,
   ⟨floatSqrt, [f64 0x4010000000000000], f64 0x4000000000000000⟩,
   ⟨setInclusion, [st [], st [ki 1]], bool true⟩,
   ⟨setInclusion, [st [ki 1], st []], bool false⟩,
   ⟨setInclusion, [st [ki 1], st [ki 1]], bool true⟩,
   ⟨setInclusion, [st [], st []], bool true⟩,
   ⟨floatNeg, [f64 0x3FF0000000000000], f64 0xBFF0000000000000⟩,
   ⟨floatLe, [f64 0, f64 0x3FF0000000000000], bool true⟩,
   ⟨floatIsNaN, [f64 0x7FF8000000000000], bool true⟩,
   ⟨intPow, [int 2, int 10], int 1024⟩, ⟨intPow, [int (-2), int 3], int (-8)⟩,
   ⟨intPowMod, [int 2, int 3, int 5], int 3⟩, ⟨intPowMod, [int (-2), int 3, int 4], int 0⟩,
   ⟨listSet, [lst [ki 1, ki 2], int 1, ki 3], lst [ki 1, ki 3]⟩,
   ⟨listMake, [int 2, ki 7], lst [ki 7, ki 7]⟩,
   ⟨listUpdateAll, [lst [ki 1, ki 2, ki 3], int 1, lst [ki 8, ki 9]], lst [ki 1, ki 8, ki 9]⟩,
   ⟨listFill, [lst [ki 1, ki 2, ki 3], int 1, int 2, ki 7], lst [ki 1, ki 7, ki 7]⟩]

theorem vals_hook : vals.all (fun p => hook p.f p.vs == some (some p.v)) = true := by decide +kernel

/-- At each described point the result is `hook`'s value under every interpretation. -/
theorem vals_hookRes : ∀ p ∈ vals, ∀ H : HookParams, (c.withHooks H).hookRes p.f p.vs = some (some p.v) :=
  fun p hp _ => Semantics.hookRes_of_value (by simpa using List.all_eq_true.mp vals_hook p hp)

/-! ## Still ⊥ where the text says there is no value -/

/-- The text's `#False` / `#Bottom` points (DOM: K 7.1.337 domains.md): `/Int`, `%Int`, `divInt`,
`modInt` at 0 (1233-1237); a lookup off the keys (266-267); `_Map_` on a common key (227-228);
`_Set_` on a common member (706-707); `B[I <- V]` at `I = length` and at `V = 256` (2103-2105);
`B[I]` at `I = length` (2115); `substrBytes(B, 2, 1)` (2136-2139); `padRightBytes(B, -1, 0)`,
`padLeftBytes(B, 1, 256)` (2176-2177); `replaceAtBytes(b"ab", 1, b"xy")`, an end above the length,
and `replaceAtBytes(b"abc", -1, b"xy")`, a negative index (2146-2147: a range that leaves `dest`);
`2 ^%Int 3 0`, `(2 ^Int 3) %Int 0` (1229-1231, 1233-1234); `bitRangeInt(1, -1, 1)` and
`signExtendBitRangeInt(1, 0, 0)`, whose equations (1438, 1440) apply a shift by a negative amount
(1238-1242). -/
def bots : List Pt :=
  [⟨intTDiv, [int 7, int 0], int 0⟩, ⟨intTMod, [int 7, int 0], int 0⟩,
   ⟨intEDiv, [int 7, int 0], int 0⟩, ⟨intEMod, [int 7, int 0], int 0⟩,
   ⟨mapLookup, [mp [(ki 1, ki 2)], ki 3], int 0⟩,
   ⟨mapConcat, [mp [(ki 1, ki 2)], mp [(ki 1, ki 3)]], int 0⟩,
   ⟨setConcat, [st [ki 1], st [ki 1]], int 0⟩,
   ⟨bytesUpdate, [b "ab", int 2, int 0], int 0⟩, ⟨bytesUpdate, [b "ab", int 0, int 256], int 0⟩,
   ⟨bytesGet, [b "ab", int 2], int 0⟩,
   ⟨bytesSubstr, [b "abc", int 2, int 1], int 0⟩,
   ⟨bytesPadRight, [b "a", int (-1), int 0], int 0⟩, ⟨bytesPadLeft, [b "a", int 1, int 256], int 0⟩,
   ⟨bytesReplaceAt, [b "ab", int 1, b "xy"], int 0⟩,
   ⟨bytesReplaceAt, [b "abc", int (-1), b "xy"], int 0⟩,
   ⟨intPowMod, [int 2, int 3, int 0], int 0⟩,
   ⟨intBitRange, [int 1, int (-1), int 1], int 0⟩, ⟨intSignExtBitRange, [int 1, int 0, int 0], int 0⟩]

theorem bots_ok : bots.all (fun p => (sig p.f) ∈ hookSigs && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && !silent p.f p.vs) = true := by
  decide +kernel

/-- **At each, Γ states ⊥.** -/
theorem bots_gamma : ∀ p ∈ bots, Γ c (appP c (sig p.f) p.vs ≡ ⊥) := by
  intro p hp
  have h := List.all_eq_true.mp bots_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩, hs⟩ := h
  exact gamma_bot c hk hvs (by rw [hname]; exact hh) (by rw [hname]; exact hs)

/-! ## `replaceAtBytes`, `isInfinite`'s equation, the surrogate residual -/

/-- `replaceAtBytes` has no silent point: where `hook` gives it no value (a negative index, an end
above the length) the text says `#False` (2146-2147). -/
theorem replaceAt_guard (vs : List GroundTerm) : silent bytesReplaceAt vs = false :=
  silent_of_not_silentKey (by decide +kernel) vs

/-- `isInfinite(F)` by its equation (domains.md 1673): `F >Float maxValueFloat(p, e)` or
`F <Float --Float maxValueFloat(p, e)`, `p` and `e` F's precision and exponent width. -/
def isInfRule (F : GroundTerm) : Option GroundTerm := do
  let p ← (hook floatPrecision [F]).join
  let e ← (hook floatExponentBits [F]).join
  let mx ← (hook floatMaxValue [p, e]).join
  let nmx ← (hook floatNeg [mx]).join
  let x ← (hook floatGt [F, mx]).join
  let y ← (hook floatLt [F, nmx]).join
  (hook boolOr [x, y]).join

/-- `isInfinite` agrees with its equation on ±0, ±∞, NaN, ±the largest finite value, the least
subnormal and 1.0 of binary64 and binary32. -/
theorem isInfinite_rule :
    ([f64 0, f64 0x8000000000000000, f64 0x7FF0000000000000, f64 0xFFF0000000000000, f64 0x7FF8000000000000,
      f64 0x7FEFFFFFFFFFFFFF, f64 0xFFEFFFFFFFFFFFFF, f64 1, f64 0x3FF0000000000000,
      f32 0, f32 0x80000000, f32 0x7F800000, f32 0xFF800000, f32 0x7FC00000,
      f32 0x7F7FFFFF, f32 0xFF7FFFFF, f32 1, f32 0x3F800000].all fun F =>
      (hook floatIsInfinite [F]).join == isInfRule F && (isInfRule F).isSome) = true := by
  decide +kernel

/-- **The carrier gap at a surrogate.** No String value has a code point 0xD800 … 0xDFFF, so
`ordChar` gives none: the text's "a string containing a single code point" makes
`ordChar(chrChar(55296)) = 55296`, which Γ refutes at every interpretation (`chrChar(55296)` is ⊥ or
a String value). -/
theorem ord_not_surrogate (w : GroundTerm) (n : Int) (h : hook stringOrd [w] = some (some (int n))) :
    ¬ (0xD800 ≤ n ∧ n < 0xE000) := by
  rw [hook_eq] at h
  have hf : hookTable.find? (·.1 == stringOrd) = some (stringOrd, fun vs => match vs with
      | [a] => (asStr a).bind fun x => (KStr.ord x).map fun n => int n | _ => none) := rfl
  rw [hf] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m, hm, hint⟩ := Option.map_eq_some_iff.mp h
  have hmn : (m : Int) = n := by simpa [int] using hint
  match x, hm with
  | [ch], hm =>
    have hm' : ch.toNat = m := Option.some.inj hm
    have hv := ch.valid
    simp only [UInt32.isValidChar, Nat.isValidChar] at hv
    have : ch.toNat = ch.val.toNat := rfl
    omega

/-! ## `FallbackTotal` -/

/-- A value of each result sort of `totalSilent`: `""` (`substrString`), `0` (`Bytes2Int`), `.Bytes`
(`Int2Bytes`). -/
def totalVal (f : Sym) : Option GroundTerm :=
  if f = stringSubstr then some (s "") else if f = bytes2Int then some (int 0)
  else if f = int2Bytes then some (b "") else none

/-- The interpretation that gives each symbol of `totalSilent` the value `totalVal`. -/
def fbH : HookParams := ⟨fun f _ => totalVal f⟩

theorem totalVal_ok : totalSilent.all (fun f => (lookupSig hookSigs f).all fun k =>
    (totalVal f).any fun v => c.sortOf v == some k.result) = true := by
  decide +kernel

/-- **`fbH` satisfies `FallbackTotal` at `strbytes`.** -/
theorem fbH_total : FallbackTotal c fbH := by
  intro f hf k vs hk _ _ _
  have h := List.all_eq_true.mp totalVal_ok f hf
  rw [hk] at h
  cases hv : totalVal f with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    simp only [Option.all_some, Option.any_some, beq_iff_eq] at h
    refine ⟨v, ?_⟩
    unfold Semantics.fallback; rw [hk, Semantics.sortOf_withHooks _ _ noRaw]
    simp [Semantics.withHooks, fbH, hv, Option.filter, h]

/-- **`HookParams.none` does not**: `substrString("abc", 2, 1)` has no value under it. -/
theorem none_not_total : ¬ FallbackTotal c HookParams.none := by
  intro h
  obtain ⟨v, hv⟩ := h stringSubstr (by decide) (sig stringSubstr) [s "abc", int 2, int 1]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have : (c.withHooks HookParams.none).fallback stringSubstr [s "abc", int 2, int 1] = none := by
    unfold Semantics.fallback; split <;> rfl
  rw [this] at hv; cases hv

/-- Under `fbH`, `substrString` has a value at every argument list of its sorts. -/
example (vs : List GroundTerm) (hvs : c.sortsOf vs = some (sig stringSubstr).args) :
    ∃ v, (c.withHooks fbH).hookRes stringSubstr vs = some (some v) :=
  hookRes_of_fallbackTotal fbH_total (by decide) (by decide +kernel) hvs

/-! ## `<=Set`: inclusion, true at two equal sets -/

/-- Sets of the `<=Set` fixture: `.Set`, `{1}`, `{1, 2}`. -/
def sets3 : List GroundTerm := [st [], st [ki 1], st [ki 1, ki 2]]

/-- `<=Set` is no key, so has no silent point; at every pair of the fixture, `hook` gives a value. -/
theorem setInclusion_not_silent : silentKey setInclusion = false := by decide +kernel

/-- The fixture's values (domains.md 780-786, inclusion): `S <=Set S` at the three sets,
`{1} <=Set {1, 2}`, `.Set <=Set {1}` true; `{1, 2} <=Set {1}`, `{1} <=Set {2}` false. -/
def incl : List Pt :=
  sets3.map (fun x => ⟨setInclusion, [x, x], bool true⟩) ++
  [⟨setInclusion, [st [ki 1], st [ki 1, ki 2]], bool true⟩,
   ⟨setInclusion, [st [ki 1, ki 2], st [ki 1]], bool false⟩,
   ⟨setInclusion, [st [ki 1], st [ki 2]], bool false⟩,
   ⟨setInclusion, [st [], st [ki 1]], bool true⟩]

theorem incl_ok : incl.all (fun p => (sig p.f) ∈ hookSigs && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v) && !silent p.f p.vs) = true := by
  decide +kernel

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, nofun, rfl⟩)))))

/-- **At each, for every interpretation, the result is the fixture's value, and Γ states it.** -/
theorem incl_gamma : ∀ p ∈ incl, ∀ H : HookParams,
    (c.withHooks H).hookRes p.f p.vs = some (some p.v) ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp incl_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩, -⟩ := h
  refine ⟨Semantics.hookRes_of_value hh, ?_⟩
  exact gamma_val (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs) (by rw [hname]; exact hh)

/-- `S <=Set S = true` at every set and for every interpretation. -/
theorem setInclusion_refl (es : List GroundTerm) (H : HookParams) :
    (c.withHooks H).hookRes setInclusion [st es, st es] = some (some (bool true)) := by
  apply Semantics.hookRes_of_value
  show some (some (bool (es.all (memS · es)))) = _
  have : es.all (memS · es) = true := List.all_eq_true.mpr fun x hx => (Set.memS_iff x es).mpr hx
  rw [this]

#print axioms undetermined
#print axioms pts_undetermined
#print axioms bytes2Int_extra
#print axioms rangeMap_undetermined
#print axioms vals_hookRes
#print axioms bots_gamma
#print axioms replaceAt_guard
#print axioms isInfinite_rule
#print axioms ord_not_surrogate
#print axioms fbH_total
#print axioms none_not_total
#print axioms incl_gamma
#print axioms setInclusion_refl

end KCore.SilentPointsTest
