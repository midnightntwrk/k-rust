/-
  The interpretations the text admits at the silent points of the symbols it declares `total`
  (`totalSilentKeys`, `Semantics.silentTotal`, ParamsTotal.lean). Run from the package root:
  `lake env lean test/SilentTotal.lean`.

  - The table against the builtin text (native): an interpreted symbol is a key of `silentTable`
    whose declaration in the library's text carries `total` (or `functional`) exactly when it is in
    `totalSilentKeys`; the symbols the text declares `total` that are neither off `partialHooks` nor
    in `totalSilentKeys` are exactly `isNaN`, `precisionFloat` and `exponentBitsFloat` (`floatLitTotal`), which
    `total_hook_value` covers where every Float value is a Float literal (`floatShapeOK`): every
    interpreted symbol the text declares `total` is in one of its three cases.
  - Non-vacuity: `HookParams.totals` meets `silentTotal` in every semantics (`silentTotal_totals`,
    kernel); `HookParams.none` does not (`none_not_silentTotal`).
  - Both directions at one point per key, in the semantics of `f2-examples/strbytes.kompile.kore`:
    `substrString("abc", 2, 1)`, `Int2Bytes(-1, 0, BE)`, `countAllOccurrences("a", "")`,
    `replaceAll("a", "", "b")`, `isInfinite` at `0.0p1x1`, and `--Float`, `absFloat`, `floorFloat`,
    `ceilFloat`, `truncFloat` at `NaNp1x1`: under `HookParams.none` Γ states the application ⊥ (the
    text's `functional` sentence fails there), under `HookParams.totals` it states a value
    (`both_ways`), and the result has a value (`total_hook_value`'s conclusion, `totals_value`).
    `Bytes2Int` has no such point where the sorts have their shapes (`bytes2Int_value`). `isNaN`,
    no key, has `hook`'s value at every Float where every Float value is a Float literal
    (`isNaN_value`).
  - The interpretations the text admits (`Semantics.libAdmitted`, LibAdmitted.lean), in the same
    semantics: `HookParams.lib` meets every condition (`lib_admitted`); each of `isInfiniteEq`,
    `rfindCharEq`, `findCharEq`, `sqrtFloatEq` fails at one point under an interpretation that gives
    values the sentence does not hold with (`HookParams.totals` at `0.0p1x1`; `rc5`, `rfindChar` 5,
    at `("ab", "a", 5)`; `fc5`, `findChar` 5 and `findString` 7, at `("abc", "a", 7)`; `root3`,
    `rootFloat` 3.0, at binary64 4.0, where `hook` gives `sqrtFloat` 2.0; `HookParams.totals`,
    `replaceAll` `""` and `countAllOccurrences` 0, at `("a", "", "b")`, where `replace("a", "", "b", 0)`
    is `"a"`: `totals_not_replaceAllEq`); `=/=Float` has `hook`'s value at every two Floats where
    every Float value is a Float literal (`neFloat_value`), so its sentence (1648) is no condition;
    `rootFloat`'s number
    is a parameter of FLOAT with the signature `paramVal_libRootFloat` reads (`rootFloat_param`);
    `precisionFloat` and `exponentBitsFloat` at `1.0p1x2` and binary32 `1.0` (`fmt_values`).
    `coreOK` gives `floatShapeOK` (`floatShapeOK_of_coreOK`), so `HookParams.lib` is admitted in
    every semantics meeting `coreOK` (`libAdmitted_lib_of_coreOK`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.SilentTotalTest

open KCore ML Faithful

/-! ## The table against the builtin text -/

/-- Whether the library's text declares the symbol named `n` `total` (or `functional`); none if it
declares no symbol of that name. -/
def declTotal (n : String) : Option Bool := Id.run do
  let all := (List.range library.length).flatMap (moduleText false)
  let mut r := none
  for s in all do
    match s with
    | .hookedSymbol h =>
      if h.symbol.ident.ident.name == n then
        r := some (KoreAML.Parse.hasAttr h.attributes "total" || KoreAML.Parse.hasAttr h.attributes "functional")
    | .symbol h =>
      if h.symbol.ident.ident.name == n then
        r := some (KoreAML.Parse.hasAttr h.attributes "total" || KoreAML.Parse.hasAttr h.attributes "functional")
    | _ => pure ()
  return r

def textTotal (f : Sym) : Bool := (declTotal (regSymNames.getD f "")).getD false

def tableCheck : IO Unit := do
  let ks := hookSigs.map (·.name)
  let bad := ks.filter fun f => (silentKey f && textTotal f) != totalSilentKeys.contains f
  if !bad.isEmpty then
    throw (IO.userError s!"totalSilentKeys differs from the text at {bad.map (regSymNames.getD · "")}")
  let third := ks.filter fun f => textTotal f && partialHooks.contains f && !totalSilentKeys.contains f
  if third.any (!floatLitTotal.contains ·) || floatLitTotal.any (!third.contains ·) then
    throw (IO.userError s!"declared total, in partialHooks, not in totalSilentKeys: {third.map (regSymNames.getD · "")}")
  IO.println s!"totalSilentKeys: the {totalSilentKeys.length} keys of silentTable the text declares total; declared total, in partialHooks and no key (total_hook_value's third case, floatLitTotal): {third.map (regSymNames.getD · "")}"

#eval tableCheck

/-! ## Non-vacuity -/

example (c : Semantics) : (c.withHooks HookParams.totals).silentTotal := silentTotal_totals c

def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default
def s (t : String) : GroundTerm := strV t.toList
def b (t : String) : GroundTerm := bytesV t.toList
def be : GroundTerm := .ctor bigEndianBytes []
/-- `1.0p1x2`: the format with a precision of 1 and an exponent width of 2 (`KFloat.thinOK`). -/
def t12 : GroundTerm := .dv Srt.float (.float 1 2 1)
/-- `0.0p1x1` and `NaNp1x1` (codes 0 and 4): the format with a precision of 1 and an exponent width
of 1, whose finite data are the two zeros, so that `maxValueFloat(1, 1)` and with it `isInfinite`
have no value there (`thinAt`, `tflInf`); `--Float` and the roundings to an integer have none at a
NaN. -/
def z11 : GroundTerm := .dv Srt.float (.float 1 1 0)
def n11 : GroundTerm := .dv Srt.float (.float 1 1 4)

/-- **`HookParams.none` is not an interpretation the text admits**, in any semantics:
`substrString("abc", 2, 1)` is a silent point and has no value under it. -/
theorem none_not_silentTotal (c : Semantics) : ¬ (c.withHooks HookParams.none).silentTotal := by
  intro h
  have := h (sig stringSubstr) (by decide +kernel) (by decide +kernel) [s "abc", int 2, int 1]
    rfl (by decide +kernel) (by decide +kernel)
  have hf : (c.withHooks HookParams.none).fallback (sig stringSubstr).name [s "abc", int 2, int 1] = none := by
    unfold Semantics.fallback; split <;> rfl
  rw [hf] at this; cases this

/-! ## Both directions at one point per key -/

definition_of defn from "f2-examples/strbytes.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- A point: the symbol, its arguments, and `HookParams.totals`' value there. -/
structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm

def pts : List Pt :=
  [⟨stringSubstr, [s "abc", int 2, int 1], s ""⟩,
   ⟨int2Bytes, [int (-1), int 0, be], b ""⟩,
   ⟨floatIsInfinite, [z11], bool false⟩,
   ⟨floatNeg, [n11], n11⟩, ⟨floatAbs, [n11], n11⟩, ⟨floatFloor, [n11], n11⟩,
   ⟨floatCeil, [n11], n11⟩, ⟨floatTrunc, [n11], n11⟩,
   ⟨stringCountAll, [s "a", s ""], int 0⟩, ⟨stringReplaceAll, [s "a", s "", s "b"], s ""⟩]

/-- Every key but `Bytes2Int` has a point. -/
theorem pts_cover : totalSilentKeys.all (fun f => f == bytes2Int || pts.any (·.f == f)) = true := by
  decide +kernel

/-- At each: the signature, arguments of its sorts, no value of `hook`, a silent point,
`HookParams.totals`' value, of the result sort. -/
theorem pts_ok : pts.all (fun p => (sig p.f) ∈ hookSigs && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    HookParams.totals.app p.f p.vs == some p.v && c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

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

/-- **Both directions**: Γ under `HookParams.none` states the application ⊥, Γ under
`HookParams.totals` states `HookParams.totals`' value. -/
theorem both_ways : ∀ p ∈ pts,
    Γ (c.withHooks HookParams.none) (appP (c.withHooks HookParams.none) (sig p.f) p.vs ≡ ⊥) ∧
    Γ (c.withHooks HookParams.totals)
      (appP (c.withHooks HookParams.totals) (sig p.f) p.vs ≡ den (c.withHooks HookParams.totals) p.v) := by
  intro p hp
  have h := List.all_eq_true.mp pts_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩, hs⟩, hv⟩, hsrt⟩ := h
  have hks := hookSigs_lookup _ hk
  rw [← hname] at hh hs hv
  constructor
  · have h0 := gamma_fallback c HookParams.none hks (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs) hh hs
    have hf : (c.withHooks HookParams.none).fallback (sig p.f).name p.vs = none := by
      unfold Semantics.fallback; split <;> rfl
    rw [hf] at h0; exact h0
  · have h1 := gamma_fallback c HookParams.totals hks (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs) hh hs
    have hf : (c.withHooks HookParams.totals).fallback (sig p.f).name p.vs = some p.v := by
      unfold Semantics.fallback; rw [hks]
      show (HookParams.totals.app (sig p.f).name p.vs).filter _ = _
      rw [hv]
      simp [Option.filter, Semantics.sortOf_withHooks _ _ noRaw, hsrt]
    rw [hf] at h1; exact h1

/-- **The result has a value under `HookParams.totals`** at each point. -/
theorem totals_value : ∀ p ∈ pts, (c.withHooks HookParams.totals).hookRes p.f p.vs = some (some p.v) := by
  intro p hp
  have h := List.all_eq_true.mp pts_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩, hs⟩, hv⟩, hsrt⟩ := h
  have hks := hookSigs_lookup _ hk
  rw [Semantics.hookRes_of_silent hh hs, ← hname]
  rw [← hname] at hv
  unfold Semantics.fallback; rw [hks]
  show some ((HookParams.totals.app (sig p.f).name p.vs).filter _) = _
  rw [hv]
  simp [Option.filter, Semantics.sortOf_withHooks _ _ noRaw, hsrt]

/-- `Bytes2Int` gives a value at every argument list of its sorts where the sorts interpreted
symbols read have their shapes (`shapesOK`, which holds `enumShapesOK`): its silent region is empty
there, whatever the interpretation. -/
theorem bytes2Int_value {c : Semantics} (hs : c.shapesOK = true) (H : HookParams) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.bytes, Srt.endianness, Srt.signedness]) :
    ∃ v, (c.withHooks H).hookRes bytes2Int vs = some (some v) := by
  obtain ⟨v, hv⟩ := bytes2Int_total hs hvs
  exact ⟨v, Semantics.hookRes_of_value hv⟩

/-- `isNaN` gives a value at every value of sort Float where every Float value is a Float literal,
whatever the interpretation. -/
theorem isNaN_value {c : Semantics} (hf : c.floatShapeOK = true) (H : HookParams) {v : GroundTerm}
    (hv : c.sortOf v = some Srt.float) : ∃ w, (c.withHooks H).hookRes floatIsNaN [v] = some (some w) := by
  obtain ⟨u, hu⟩ := asDatum_sorted hf hv
  have hh : hook floatIsNaN [v] = some (flTest KFloat.isNaN [v]) := rfl
  exact ⟨bool (KFloat.isNaN u), Semantics.hookRes_of_value (by rw [hh]; simp [flTest, hu])⟩

/-- **`=/=Float` gives a value at every two values of sort Float** where every Float value is a
Float literal, whatever the interpretation: `hook` compares their data (`flCmp`, `asDatum_sorted`). -/
theorem neFloat_value {c : Semantics} (hf : c.floatShapeOK = true) (H : HookParams) {a b : GroundTerm}
    (hs : (c.withHooks H).sortsOf [a, b] = some [Srt.float, Srt.float]) :
    ∃ w, (c.withHooks H).hookRes floatNe [a, b] = some (some w) := by
  obtain ⟨a', b', he, ha, hb⟩ := _root_.KCore.sortsOf_two hs
  obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by simpa using he
  obtain ⟨u, hu⟩ := asDatum_sorted (c := c.withHooks H) hf ha
  obtain ⟨w, hw⟩ := asDatum_sorted (c := c.withHooks H) hf hb
  have h1 : hook floatNe [a, b] = some (flCmp (fun o => o != some .eq) [a, b]) := rfl
  exact ⟨bool (KFloat.cmpExact u w != some .eq),
    Semantics.hookRes_of_value (by rw [h1]; simp [flCmp, hu, hw])⟩

/-! ## The interpretations the text admits -/

theorem c_floatShapeOK : c.floatShapeOK = true := by decide +kernel

/-- **`HookParams.lib` is admitted** in the semantics of strbytes. -/
theorem lib_admitted : (c.withHooks HookParams.lib).libAdmitted := libAdmitted_lib c c_floatShapeOK

/-- `isInfinite`'s condition fails under `HookParams.totals` at `0.0p1x1`: `isInfinite` has its
value `false` there and `maxValueFloat(1, 1)` none, so the right side has none. -/
theorem totals_not_isInfiniteEq : ¬ (c.withHooks HookParams.totals).isInfiniteEq := by
  intro h
  have := h z11 (by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

/-- `rfindChar` 5 at its silent points, `rfindString` none. -/
def rc5 : HookParams := ⟨fun f _ => if f == stringRfindChar then some (int 5) else Option.none⟩

theorem rc5_not_rfindCharEq : ¬ (c.withHooks rc5).rfindCharEq := by
  intro h
  have := h (s "ab") (s "a") (int 5) (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

/-- `findChar` 5 and `findString` 7 at their silent points. -/
def fc5 : HookParams :=
  ⟨fun f _ => if f == stringFindChar then some (int 5) else if f == stringFind then some (int 7) else Option.none⟩

/-- `findChar`'s condition fails under `fc5` at `("abc", "a", 7)`, an index off the string: the left
side is 5; on the right `findString("abc", "a", 7)` is 7 and `findChar("abc", "", 7)` is `hook`'s -1,
so the right side is 7. -/
theorem fc5_not_findCharEq : ¬ (c.withHooks fc5).findCharEq := by
  intro h
  have := h (s "abc") (s "a") (int 7) (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

/-- binary64 4.0, 3.0, 2.0. -/
def f64 (b : Nat) : GroundTerm := .dv Srt.float (.float 53 11 b)

/-- `rootFloat` 3.0 at every argument. -/
def root3 : HookParams :=
  ⟨fun f _ => if f == libRootFloat then some (f64 0x4008000000000000) else Option.none⟩

/-- `sqrtFloat`'s condition fails under `root3` at 4.0: `hook` gives `sqrtFloat(4.0)` the value 2.0,
no silent point, and the interpretation gives `rootFloat(4.0, 2)` the value 3.0. -/
theorem root3_not_sqrtFloatEq : ¬ (c.withHooks root3).sqrtFloatEq := by
  intro h
  have := h (f64 0x4010000000000000) (by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel)
  revert this
  decide +kernel

theorem sqrt4 : hook floatSqrt [f64 0x4010000000000000] = some (some (f64 0x4000000000000000)) := by
  decide +kernel

/-- `rootFloat`'s number is a parameter of a library module, with a Float and an Int argument and
a Float result. -/
theorem rootFloat_param :
    library.any (fun m => m.params.contains ⟨libRootFloat, [Srt.float, Srt.int], Srt.float⟩) = true := by
  decide +kernel

/-- `replaceAll`'s condition fails under `HookParams.totals` at `("a", "", "b")`: `replaceAll` is `""`
there, the count 0, and `replace("a", "", "b", 0)` is `hook`'s `"a"`. -/
theorem totals_not_replaceAllEq : ¬ (c.withHooks HookParams.totals).replaceAllEq := by
  intro h
  have := h (s "a") (s "") (s "b") (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)
    (by decide +kernel)
  revert this
  decide +kernel

/-- `precisionFloat` and `exponentBitsFloat` at `1.0p1x2` (1, 2) and at binary32 `1.0` (24, 8). -/
theorem fmt_values :
    hook floatPrecision [t12] = some (some (int 1)) ∧ hook floatExponentBits [t12] = some (some (int 2)) ∧
    hook floatPrecision [.dv Srt.float (.float 24 8 0x3F800000)] = some (some (int 24)) ∧
    hook floatExponentBits [.dv Srt.float (.float 24 8 0x3F800000)] = some (some (int 8)) := by
  decide +kernel

#print axioms lib_admitted
#print axioms floatShapeOK_of_coreOK
#print axioms libAdmitted_lib_of_coreOK
#print axioms libAdmitted_lib
#print axioms totals_not_isInfiniteEq
#print axioms isNaN_value
#print axioms neFloat_value
#print axioms rc5_not_rfindCharEq
#print axioms fc5_not_findCharEq
#print axioms root3_not_sqrtFloatEq
#print axioms sqrt4
#print axioms totals_not_replaceAllEq
#print axioms replaceAllEq_lib
#print axioms rootFloat_param
#print axioms findCharEq_lib
#print axioms sqrtFloatEq_lib
#print axioms libAdmitted_lawHooks
#print axioms fmt_values
#print axioms fmt_total
#print axioms shape_float
#print axioms silentTotal_totals
#print axioms none_not_silentTotal
#print axioms both_ways
#print axioms totals_value
#print axioms bytes2Int_value
#print axioms total_hook_value

end KCore.SilentTotalTest
