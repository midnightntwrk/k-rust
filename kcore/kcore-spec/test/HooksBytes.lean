/-
  The supported hook rows of BYTES (14) of test/constructs/rows.toml (`hook:BYTES.*` with status
  `supported`): the sort row `BYTES.Bytes` and the thirteen operations of `rows`. Each has its three
  statements (DONE-0 C2, evidence of a `supported` hook): one in-domain value; for each region the
  builtin prose excludes or leaves unstated, Γ's statement at a point of it (⊥ under every
  interpretation where the prose states that there is no value; neither ⊥ nor a value over all
  interpretations where the prose states nothing); and that the hook's silent predicate in
  `silentTable` is the unstated region, or why the prose covers every argument list. Run from the
  package root: `lake env lean test/HooksBytes.lean`.

  The expected side is the builtin prose: DOM is K 7.1.337's
  k-distribution/include/kframework/builtin/domains.md, cited by line. No expected value is taken
  from a run: each is derived by hand from the cited sentence. Not rows here: the `MInt` variants
  (DOM 2109, 2119, 2133, 2153, 2185-2186, 2206; refused rows), `Bytes2String`, `Bytes2Hex`,
  `String2Bytes`, `decodeBytes`, `encodeBytes` (DOM 2015-2016, 2094-2096; parameter rows), and
  `Int2Bytes(Int, Endianness, Signedness)` (DOM 2084, `symbol(Int2BytesNoLen)`, no `hook`; its rules
  2250-2259).

  "Stated" and "unstated". DOM 14-16: "some functions in the K prelude functions are not total …
  When you invoke such a function on an undefined input, the behavior is undefined": a region the
  prose does not describe is unstated. Where the prose writes "The result is `#False`" (DOM 2103,
  2115, 2146, 2176) or "is `#Bottom`" (2136) it states that there is no value: Γ states ⊥ there
  under every interpretation, and no interpretation gives one. "This will throw an exception" (DOM
  2162-2164) is about a run and writes no `#False`: unstated.

  The four rows the prose declares `total` with a value described at every argument list (none is a
  key of `silentTable` nor among `partialHooks`, `groups`; a value at every argument list of the
  sorts under every interpretation, `plain_covered`):

  | row | prose |
  |---|---|
  | `BYTES.empty` | DOM 2030 "The byte array of length zero is represented by `.Bytes`"; `total` 2033 |
  | `BYTES.reverse` | DOM 2191 "reverse a `Bytes` object"; `total` 2196 |
  | `BYTES.length` | DOM 2201 "the length of a `Bytes` term"; `total` 2205 |
  | `BYTES.concat` | DOM 2212-2213 "concatenating two `Bytes` objects"; `total` 2216 |

  The six rows with a region where the prose states that there is no value, and no unstated region
  (none is a key of `silentTable`, each is among `partialHooks`, `groups`): `hook` gives no value
  exactly on the region (`*_none`, at every argument list of literals; every argument list of the
  signature is one under `shapesOK`, `covered_bii`, `covered_bi`), and there Γ states ⊥ in every
  semantics under every interpretation (`*_bot`).

  | row | prose | region of no value |
  |---|---|---|
  | `BYTES.update` | DOM 2101-2105 "The result is `#False` if `value` is not in the range [0..255] or if `index` is not a valid index (ie, less than zero or greater than or equal to the length …)"; 2108, no `total` | index < 0, index ≥ length, value < 0, value > 255 |
  | `BYTES.get` | DOM 2114-2115 "The result is `#False` if `index` is not a valid index (see above)"; 2118, no `total` | index < 0, index ≥ length |
  | `BYTES.substr` | DOM 2124-2126 the range `[startIndex..endIndex)`; 2136-2139 "The function is not total: … is `#Bottom` if `startIndex <Int 0` or `endIndex <Int startIndex` or `lengthBytes(B) <Int endIndex`"; 2132, no `total` | start < 0, end < start, length < end |
  | `BYTES.padRight`, `BYTES.padLeft` | DOM 2172-2177 "The result is `#False` if `value` is not in the range `[0..255]`, or if the length is negative"; 2183, 2184, no `total`; the `#Ceil` rules 2241-2242 state the same region (a simplification block: a consequence, not a source) | length < 0, value < 0, value > 255 |
  | `BYTES.replaceAt` | DOM 2143-2144 "equal to `dest` except the `N` elements starting at `index` are replaced with the contents of `src`" (N the length of `src`), 2146-2147 "The result is `#False` if `index` + `N` is not a valid index"; 2152, no `total`. The defining sentence names N elements of `dest` exactly when 0 ≤ index and index + N ≤ length, and has a value there, the last byte included (index + N = length: `boundary_hook`); the `#False` sentence is read of every other range, one that leaves `dest` (ruling 1 below) | index < 0, index + N > length (`replaceAt_none`, `replaceAt_bot`) |

  The three keys of `silentTable`:

  | row | prose | where `hook` gives no value | silent predicate |
  |---|---|---|---|
  | `BYTES.memset` | DOM 2158-2164 "This will throw an exception if `index` + `count` is not a valid index. The acceptable range of values for `v` is -128 to 127. This will throw an exception if `v` is outside of this range"; 2167, no `total` | index < 0, count < 0, index + count > length, v < -128, v > 127 (`memset_none`); a value at index + count = length, the count bytes being the last ones (ruling 2) | true at every argument list (`keys_silent`): the whole region is unstated |
  | `BYTES.int2bytes` | DOM 2065-2072; `total` 2083 | length < 0 (`int2Bytes_none`), and an Endianness that is no constructor of BYTES | true at every argument list: a negative length is not described, and `total` says a value exists, not which |
  | `BYTES.bytes2int` | DOM 2059-2063; `total` 2082 | nowhere at an argument list of the signature under `shapesOK` (`covered_bytes2Int`): only at an Endianness or Signedness that is no constructor of BYTES (DOM 2043-2044, 2053-2054 give two each) | true at every argument list; the region is empty where the two sorts have only BYTES' constructors, so the prose covers every argument list there |

  Statements:
  - **(1)** `vals`: points with the value derived from the cited sentence; `hook` gives it
    (`vals_ok`), it is the result under every interpretation and Γ states it (`vals_gamma`), in the
    semantics of `f2-examples/strbytes.kompile.kore` (BYTES imported, `coreOK`, no function). The
    plain rows also at every argument list of literals (`empty_at`, `reverse_at`, `length_at`,
    `concat_at`), `Bytes2Int` at every Bytes, Endianness and Signedness of BYTES (`bytes2Int_at`).
  - **(2)** stated: `bots`, a point of each part of each `#False` / `#Bottom` region, where Γ entails
    ⊥ under every interpretation (`bots_entails`), and the `*_bot` theorems on the whole region in
    every semantics. Unstated: `pts`, a point of each part of each unstated region, where Γ over all
    interpretations entails neither ⊥ nor a value (`pts_undetermined`); `ptsB`, `Bytes2Int` and
    `Int2Bytes` at one more constructor of Endianness (`extra_undetermined`).
  - **(3)** `groups`, `keys_silent`, `replaceAt_silent`, `replaceAt_bot_region`, the `*_none` theorems, `plain_covered`, `covered_bytes2Int`,
    `covered_bii`, `covered_bi`, `covered_bib`, `covered_biii`, `covered_iie`.

  The sort row `BYTES.Bytes` (DOM 1987 "fixed-width arrays of Bytes", 2001-2002): every sequence of
  bytes is a value (`bytes_value`: a literal whose characters are below 256, one character a byte),
  two sequences are two values (`bytes_inj`), nothing else is one (`bytes_only`, under `shapesOK`);
  a sort has no argument list. DOM 1989-1995 (a mutable representation on one backend) says
  nothing of the values.

  Readings ruled (1-3) and findings (4-6; prose against `hook` and `silentTable`, none of which makes
  a statement here unprovable):
  1. `replaceAtBytes`. `N` is the length of `src` (the prose does not say; DOM 2148 "values for
     `index` and `N`" is about `MInt`). DOM 2143-2144 defines the operation: `dest` except the `N`
     elements starting at `index` replaced. That names N elements of `dest` exactly when 0 ≤ index
     and index + N ≤ length, and then describes a value; so at index + N = length (the N elements
     are the last N; `replaceAtBytes(B, 0, B)`) there is a value. DOM 2146-2147 "`#False` if
     `index` + `N` is not a valid index" with the definition of 2104-2105 ("less than zero or
     greater than or equal to the length") would deny that value by one position; where a
     sentence's bound contradicts the operation's own defining sentence by one position, the
     defining sentence decides. The `#False` sentence is about a range that leaves `dest`: index < 0
     or index + N > length, where it is `#False` and Γ states ⊥. `replaceAtBytes` is no key of
     `silentTable`.
  2. `memsetBytes` likewise has a value at index + count = length (DOM 2158-2160 names the `count`
     bytes starting at `index`, which are bytes of `dest` there).
  3. `memsetBytes`: "will throw an exception" twice, no `#False`: unstated by the ruling on such
     wording. A negative count and a negative index are not mentioned. `v` is bounded by
     -128 … 127 where `Int2Bytes(1, v, LE/BE)` (the value the sentence names) is described at
     every `v`. DOM 2164: "This is implemented only for the LLVM backend".
  4. `Int2Bytes(length, I, E)`. A negative `length` is not described and the production is `total`
     (2083): unstated. DOM 2067-2071 compares the `length` (in bytes) with "the highest set bit";
     padding is described for a positive and a negative number, and 0 is neither (read: no bit set,
     padded with 0 bits, marked; no point of `vals` has I = 0 with a positive length). A negative
     number cut to fewer bytes: "the most-significant bits of the integer will be truncated" names
     the bits of the integer, and "the magnitude" two lines above; read as the two's-complement
     bits (DOM 2061), marked; no point of `vals` cuts a negative number.
  5. `Bytes2Int` at `.Bytes`: the sentence (2059-2063) does not single out no byte. Derived, not
     read off it: DOM 2250-2251 `Int2Bytes(I, _, _) => .Bytes requires I ==Int 0` with DOM 2075-2077
     "convertible back to the original integer via `Bytes2Int`" gives 0.
  6. Padding: "at least `length` bytes long by taking the input sequence and padding it" (DOM
     2172-2174) does not say how many bytes are added; read as the fewest (the result has length
     max(length of the input, `length`)), marked; DOM 2174-2176 "return the input unchanged" when
     the input is already that long.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HooksBytesTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/HooksString.lean writes it) -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, nofun, rfl⟩)))))

/-- Off the silent points, Γ states ⊥ where `hook` gives no value, in every semantics. -/
theorem gamma_bot (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = false) :
    Γ c (appP c k vs ≡ ⊥) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, none, hk, hvs, hh, fun _ => hs, rfl⟩)))))

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

/-! ## Values -/

/-- The Bytes literal whose bytes are the characters of `t` (one character a byte). -/
def bv (t : String) : GroundTerm := .dv Srt.bytes (.tok t)

/-- `BE` (true) and `LE` (DOM 2043-2044). -/
def en (bigEndian : Bool) : GroundTerm := .ctor (if bigEndian then bigEndianBytes else littleEndianBytes) []

/-- `Signed` (true) and `Unsigned` (DOM 2053-2054). -/
def sn (signed : Bool) : GroundTerm := .ctor (if signed then signedBytes else unsignedBytes) []

theorem hook_at {f : Sym} {h : List GroundTerm → Option GroundTerm}
    (hf : hookTable.find? (·.1 == f) = some (f, h)) (vs : List GroundTerm) : hook f vs = some (h vs) := by
  rw [hook_eq, hf]; rfl

theorem asBytes_bv (t : String) : asBytes (bv t) = some t.toList := by simp [asBytes, bv]
theorem asInt_int (i : Int) : asInt (int i) = some i := by simp [asInt, int]
theorem asEndian_en (b : Bool) : asEndian (en b) = some b := by cases b <;> rfl
theorem asSigned_sn (b : Bool) : asSigned (sn b) = some b := by cases b <;> rfl

/-! ## `hook` at every argument list of literals -/

/-- `.Bytes` is the byte array of length zero (DOM 2030). -/
theorem empty_at : hook bytesEmpty [] = some (some (bytesV [])) := by
  rw [hook_at (h := fun vs => match vs with | [] => some (bytesV []) | _ => none) rfl]

/-- `reverseBytes`: the bytes in the reverse order (DOM 2191). -/
theorem reverse_at (t : String) : hook bytesReverse [bv t] = some (some (bytesV t.toList.reverse)) := by
  rw [hook_at (h := fun vs => match vs with | [b] => (asBytes b).map fun x => bytesV x.reverse | _ => none) rfl]
  simp [asBytes_bv]

/-- `lengthBytes`: the number of bytes (DOM 2201). -/
theorem length_at (t : String) : hook bytesLength [bv t] = some (some (int t.toList.length)) := by
  rw [hook_at (h := fun vs => match vs with | [b] => (asBytes b).map fun x => int x.length | _ => none) rfl]
  simp [asBytes_bv]

/-- `+Bytes`: the bytes of the first, then those of the second (DOM 2212-2213). -/
theorem concat_at (x y : String) :
    hook bytesConcat [bv x, bv y] = some (some (bytesV (x.toList ++ y.toList))) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b] => (asBytes a).bind fun x => (asBytes b).map fun y => bytesV (x ++ y) | _ => none) rfl]
  simp [asBytes_bv]

/-- `Bytes2Int` has a value at every Bytes, Endianness and Signedness of BYTES. -/
theorem bytes2Int_at (t : String) (e s : Bool) :
    hook bytes2Int [bv t, en e, sn s] = some (some (int (KBytes.toInt t.toList e s))) := by
  rw [hook_at (h := fun vs => match vs with
     | [b, e, s] => (asBytes b).bind fun x => (asEndian e).bind fun be => (asSigned s).map fun sg =>
         int (KBytes.toInt x be sg)
     | _ => none) rfl]
  simp [asBytes_bv, asEndian_en, asSigned_sn]

theorem update_hook (t : String) (i v : Int) :
    hook bytesUpdate [bv t, int i, int v] = some ((KBytes.update t.toList i v).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [b, i, v] => (asBytes b).bind fun x => (asInt i).bind fun i => (asInt v).bind fun v =>
         (KBytes.update x i v).map bytesV
     | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem get_hook (t : String) (i : Int) :
    hook bytesGet [bv t, int i] = some ((KBytes.get t.toList i).map int) := by
  rw [hook_at (h := fun vs => match vs with
     | [b, i] => (asBytes b).bind fun x => (asInt i).bind fun i => (KBytes.get x i).map int | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem substr_hook (t : String) (i j : Int) :
    hook bytesSubstr [bv t, int i, int j] = some ((KStr.substr t.toList i j).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [b, i, j] => (asBytes b).bind fun x => (asInt i).bind fun i => (asInt j).bind fun j =>
         (KStr.substr x i j).map bytesV
     | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem replaceAt_hook (d : String) (i : Int) (s : String) :
    hook bytesReplaceAt [bv d, int i, bv s] = some ((KBytes.replaceAt d.toList i s.toList).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [d, i, s] => (asBytes d).bind fun x => (asInt i).bind fun i => (asBytes s).bind fun y =>
         (KBytes.replaceAt x i y).map bytesV
     | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem memset_hook (d : String) (i n v : Int) :
    hook bytesMemset [bv d, int i, int n, int v] = some ((KBytes.memset d.toList i n v).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [d, i, n, v] => (asBytes d).bind fun x => (asInt i).bind fun i => (asInt n).bind fun n => (asInt v).bind fun v =>
         (KBytes.memset x i n v).map bytesV
     | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem padRight_hook (t : String) (l v : Int) :
    hook bytesPadRight [bv t, int l, int v] = some ((KBytes.padRight t.toList l v).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [b, l, v] => (asBytes b).bind fun x => (asInt l).bind fun l => (asInt v).bind fun v =>
         (KBytes.padRight x l v).map bytesV
     | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem padLeft_hook (t : String) (l v : Int) :
    hook bytesPadLeft [bv t, int l, int v] = some ((KBytes.padLeft t.toList l v).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [b, l, v] => (asBytes b).bind fun x => (asInt l).bind fun l => (asInt v).bind fun v =>
         (KBytes.padLeft x l v).map bytesV
     | _ => none) rfl]
  simp [asBytes_bv, asInt_int]

theorem int2Bytes_hook (l v : Int) (e : Bool) :
    hook int2Bytes [int l, int v, en e] = some ((KBytes.ofInt l v e).map bytesV) := by
  rw [hook_at (h := fun vs => match vs with
     | [l, v, e] => (asInt l).bind fun l => (asInt v).bind fun v => (asEndian e).bind fun be =>
         (KBytes.ofInt l v be).map bytesV
     | _ => none) rfl]
  simp [asInt_int, asEndian_en]

/-! ## Where `hook` gives no value -/

/-- `B[I <- V]`: no value exactly where DOM 2103-2105 says `#False`. -/
theorem update_none (t : String) (i v : Int) : hook bytesUpdate [bv t, int i, int v] = some none ↔
    (i < 0 ∨ (t.toList.length : Int) ≤ i ∨ v < 0 ∨ 255 < v) := by
  rw [update_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.update
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `B[I]`: no value exactly where DOM 2115 says `#False`. -/
theorem get_none (t : String) (i : Int) : hook bytesGet [bv t, int i] = some none ↔
    (i < 0 ∨ (t.toList.length : Int) ≤ i) := by
  rw [get_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.get
  split
  · rename_i h; rw [Option.map_eq_none_iff, List.getElem?_eq_none_iff]; omega
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `substrBytes`: no value exactly where DOM 2136-2139 says `#Bottom`. -/
theorem substr_none (t : String) (i j : Int) : hook bytesSubstr [bv t, int i, int j] = some none ↔
    (i < 0 ∨ j < i ∨ (t.toList.length : Int) < j) := by
  rw [substr_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KStr.substr
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `padRightBytes`: no value exactly where DOM 2176-2177 says `#False`. -/
theorem padRight_none (t : String) (l v : Int) : hook bytesPadRight [bv t, int l, int v] = some none ↔
    (l < 0 ∨ v < 0 ∨ 255 < v) := by
  rw [padRight_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.padRight
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `padLeftBytes`: the same region. -/
theorem padLeft_none (t : String) (l v : Int) : hook bytesPadLeft [bv t, int l, int v] = some none ↔
    (l < 0 ∨ v < 0 ∨ 255 < v) := by
  rw [padLeft_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.padLeft
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `replaceAtBytes`: no value at a negative index, and where the end index + N is beyond the
length (N the length of `src`); a value where 0 ≤ index and index + N ≤ length, the boundary
index + N = length included. -/
theorem replaceAt_none (d : String) (i : Int) (s : String) : hook bytesReplaceAt [bv d, int i, bv s] = some none ↔
    (i < 0 ∨ (d.toList.length : Int) < i + (s.toList.length : Int)) := by
  rw [replaceAt_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.replaceAt
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `memsetBytes`: no value at a negative index or count, an end index + count beyond the length, or
`v` off -128 … 127; a value elsewhere, the boundary index + count = length included. -/
theorem memset_none (d : String) (i n v : Int) : hook bytesMemset [bv d, int i, int n, int v] = some none ↔
    (i < 0 ∨ n < 0 ∨ (d.toList.length : Int) < i + n ∨ v < -128 ∨ 127 < v) := by
  rw [memset_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.memset
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- `Int2Bytes(length, I, E)` at an Endianness of BYTES: no value exactly at a negative length. -/
theorem int2Bytes_none (l v : Int) (e : Bool) : hook int2Bytes [int l, int v, en e] = some none ↔ l < 0 := by
  rw [int2Bytes_hook, Option.some.injEq, Option.map_eq_none_iff]
  unfold KBytes.ofInt
  by_cases h : l < 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]; exact ⟨fun h' => (nomatch h'), fun h' => (nomatch h')⟩

/-! ## The rows -/

/-- The thirteen supported operation rows: the symbol and its `hook` attribute in the prose's
productions (DOM 2033 `BYTES.empty`, 2082 `bytes2int`, 2083 `int2bytes`, 2108 `update`, 2118 `get`,
2132 `substr`, 2152 `replaceAt`, 2167 `memset`, 2183 `padRight`, 2184 `padLeft`, 2196 `reverse`, 2205
`length`, 2216 `concat`). The fourteenth row is the sort (`BYTES.Bytes`, DOM 2001). -/
def rows : List (Sym × String) :=
  [(bytesEmpty, "BYTES.empty"), (bytes2Int, "BYTES.bytes2int"), (int2Bytes, "BYTES.int2bytes"),
   (bytesUpdate, "BYTES.update"), (bytesGet, "BYTES.get"), (bytesSubstr, "BYTES.substr"),
   (bytesReplaceAt, "BYTES.replaceAt"), (bytesMemset, "BYTES.memset"), (bytesPadRight, "BYTES.padRight"),
   (bytesPadLeft, "BYTES.padLeft"), (bytesReverse, "BYTES.reverse"), (bytesLength, "BYTES.length"),
   (bytesConcat, "BYTES.concat")]

/-- The four rows declared `total` whose value the prose describes at every argument list. -/
def plain : List Sym := [bytesEmpty, bytesReverse, bytesLength, bytesConcat]

/-- The six rows with a region where the prose states `#False` or `#Bottom`, and no unstated one. -/
def bottoms : List Sym := [bytesUpdate, bytesGet, bytesSubstr, bytesPadRight, bytesPadLeft, bytesReplaceAt]

/-- The three rows with an unstated region. -/
def keys : List Sym := [bytesMemset, bytes2Int, int2Bytes]

/-- The rows are the registry's entries with a `BYTES.` hook, and `plain`, `bottoms` and `keys` part
them. -/
theorem rows_registry :
    ((regHookNames.filter (fun e => e.2.toList.take 6 == "BYTES.".toList)).all rows.contains &&
    rows.all regHookNames.contains &&
    rows.all (fun r => (plain ++ bottoms ++ keys).count r.1 == 1) &&
    (plain ++ bottoms ++ keys).all (fun f => rows.any (·.1 == f))) = true := by
  decide +kernel

/-- The signatures (DOM's productions, by sort). -/
def sigTable : List (Sym × List Srt × Srt) :=
  [(bytesEmpty, [], Srt.bytes), (bytes2Int, [Srt.bytes, Srt.endianness, Srt.signedness], Srt.int),
   (int2Bytes, [Srt.int, Srt.int, Srt.endianness], Srt.bytes),
   (bytesUpdate, [Srt.bytes, Srt.int, Srt.int], Srt.bytes), (bytesGet, [Srt.bytes, Srt.int], Srt.int),
   (bytesSubstr, [Srt.bytes, Srt.int, Srt.int], Srt.bytes),
   (bytesReplaceAt, [Srt.bytes, Srt.int, Srt.bytes], Srt.bytes),
   (bytesMemset, [Srt.bytes, Srt.int, Srt.int, Srt.int], Srt.bytes),
   (bytesPadRight, [Srt.bytes, Srt.int, Srt.int], Srt.bytes), (bytesPadLeft, [Srt.bytes, Srt.int, Srt.int], Srt.bytes),
   (bytesReverse, [Srt.bytes], Srt.bytes), (bytesLength, [Srt.bytes], Srt.int),
   (bytesConcat, [Srt.bytes, Srt.bytes], Srt.bytes)]

theorem sig_ok : ∀ r ∈ sigTable, sig r.1 ∈ hookSigs ∧ (sig r.1).name = r.1 ∧ (sig r.1).args = r.2.1 ∧
    (sig r.1).result = r.2.2 := by
  decide +kernel

theorem sigTable_rows : (rows.map (·.1) == sigTable.map (·.1)) = true := by decide +kernel

/-! ## Statement 3 -/

/-- **The groups against `silentTable` and `partialHooks`**: no plain row is a key or partial; no
row of `bottoms` is a key, and each is partial; every row of `keys` is a key, and partial but
`Bytes2Int` (which has a value at every argument list where Endianness and Signedness have only
BYTES' constructors). -/
theorem groups :
    (plain.all (fun f => !silentKey f && !partialHooks.contains f) &&
     bottoms.all (fun f => !silentKey f && partialHooks.contains f) &&
     keys.all (fun f => silentKey f && (partialHooks.contains f != (f == bytes2Int)))) = true := by
  decide +kernel

/-- **Each plain row has a value at every argument list of its sorts, whatever the interpretation**
(the library's `hook_total`). -/
theorem plain_covered (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true) {f : Sym}
    (hf : f ∈ plain) {vs : List GroundTerm} (hvs : (c.withHooks H).sortsOf vs = some (sig f).args) :
    ∃ v, (c.withHooks H).hookRes f vs = some (some v) := by
  have hp : partialHooks.contains f = false ∧ sig f ∈ hookSigs ∧ (sig f).name = f := by
    simp only [plain, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨hp, hk, hname⟩ := hp
  obtain ⟨v, hv⟩ := hook_total hs (sig f) hk (by rw [hname]; exact hp) vs hvs
  rw [hname] at hv
  exact ⟨v, Semantics.hookRes_of_value hv⟩

/-- The silent predicate of no row of `plain` or `bottoms` is true anywhere: where `hook` gives no
value, the prose states that there is none. -/
theorem not_silent : ∀ f ∈ plain ++ bottoms, ∀ vs : List GroundTerm, silent f vs = false := by
  intro f hf vs
  refine silent_of_not_silentKey ?_ vs
  simp only [plain, bottoms, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **The predicate of `memsetBytes`, `Bytes2Int` and `Int2Bytes` is true at every argument list**:
their silent points are the argument lists where `hook` gives no value. -/
theorem keys_silent : ∀ f ∈ [bytesMemset, bytes2Int, int2Bytes], ∀ vs : List GroundTerm, silent f vs = true := by
  intro f hf vs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

/-- **`replaceAtBytes` has no silent point**: it is no key of `silentTable`. -/
theorem replaceAt_silent (vs : List GroundTerm) : silent bytesReplaceAt vs = false :=
  not_silent _ (by decide) vs

/-- Where `hook` gives `replaceAtBytes` no value, the range leaves `dest` (a negative index, or an
end index + N above the length), which DOM 2146-2147 states as `#False`; the point is not silent. -/
theorem replaceAt_bot_region (d : String) (i : Int) (s : String) :
    (hook bytesReplaceAt [bv d, int i, bv s] = some none ∧ silent bytesReplaceAt [bv d, int i, bv s] = false) ↔
      (i < 0 ∨ (d.toList.length : Int) < i + (s.toList.length : Int)) := by
  rw [replaceAt_none]
  exact ⟨fun h => h.1, fun h => ⟨h, replaceAt_silent _⟩⟩

/-! ## The sort row `BYTES.Bytes` -/

theorem int_value (c : Semantics) (i : Int) : c.sortOf (int i) = some Srt.int := by
  simp [int, Semantics.sortOf, dvOK]

/-- Every sequence of bytes is a value of sort Bytes (DOM 1987, 2001), in every semantics: the
literal whose characters, one a byte, are below 256. -/
theorem bytes_value (c : Semantics) {t : String} (ht : t.toList.all (·.toNat < 256) = true) :
    c.sortOf (bv t) = some Srt.bytes :=
  sortOf_dv.mpr ⟨by simp [dvOK, Lib.carrier_of_lt _ (by decide : Srt.bytes < nRegSorts), ht], rfl⟩

/-- Two sequences are two values. -/
theorem bytes_inj {t u : String} (h : bv t = bv u) : t = u := by
  simp only [bv, GroundTerm.dv.injEq, Lit.tok.injEq, true_and] at h; exact h

/-- Nothing else is a value of sort Bytes (under `shapesOK`): the prose gives Bytes no constructor,
only the tokens of DOM 2002. -/
theorem bytes_only {c : Semantics} (hs : c.shapesOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.bytes) : ∃ t, v = bv t :=
  shape_bytes hs h

/-! ## Every argument list of a signature (under `shapesOK`) -/

/-- **`Bytes2Int` has a value at every argument list of its sorts**, whatever the interpretation:
the region where `hook` gives none is empty where Endianness and Signedness have only BYTES'
constructors. -/
theorem covered_bytes2Int (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true)
    {vs : List GroundTerm} (hvs : (c.withHooks H).sortsOf vs = some [Srt.bytes, Srt.endianness, Srt.signedness]) :
    ∃ v, (c.withHooks H).hookRes bytes2Int vs = some (some v) := by
  obtain ⟨v, hv⟩ := bytes2Int_total hs hvs
  exact ⟨v, Semantics.hookRes_of_value hv⟩

/-- An argument list of `B[I <- V]`, `substrBytes`, `padRightBytes`, `padLeftBytes` is a Bytes
literal and two integers: with `update_none`, `substr_none`, `padRight_none`, `padLeft_none`, a value
or the prose's `#False` / `#Bottom` at each. -/
theorem covered_bii {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.bytes, Srt.int, Srt.int]) : ∃ t i j, vs = [bv t, int i, int j] := by
  obtain ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩ := sortsOf_three hvs
  obtain ⟨t, rfl⟩ := shape_bytes hs h₁
  obtain ⟨i, rfl⟩ := shape_int hs h₂
  obtain ⟨j, rfl⟩ := shape_int hs h₃
  exact ⟨t, i, j, rfl⟩

/-- An argument list of `B[I]` (with `get_none`). -/
theorem covered_bi {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.bytes, Srt.int]) : ∃ t i, vs = [bv t, int i] := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨t, rfl⟩ := shape_bytes hs h₁
  obtain ⟨i, rfl⟩ := shape_int hs h₂
  exact ⟨t, i, rfl⟩

/-- An argument list of `replaceAtBytes` (with `replaceAt_none`, `replaceAt_bot_region`). -/
theorem covered_bib {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.bytes, Srt.int, Srt.bytes]) : ∃ d i s, vs = [bv d, int i, bv s] := by
  obtain ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩ := sortsOf_three hvs
  obtain ⟨d, rfl⟩ := shape_bytes hs h₁
  obtain ⟨i, rfl⟩ := shape_int hs h₂
  obtain ⟨s, rfl⟩ := shape_bytes hs h₃
  exact ⟨d, i, s, rfl⟩

/-- An argument list of `memsetBytes` (with `memset_none`). -/
theorem covered_biii {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.bytes, Srt.int, Srt.int, Srt.int]) :
    ∃ d i n v, vs = [bv d, int i, int n, int v] := by
  obtain ⟨w₁, ws, rfl, h₁, hws⟩ := sortsOf_inv_cons hvs
  obtain ⟨w₂, w₃, w₄, rfl, h₂, h₃, h₄⟩ := sortsOf_three hws
  obtain ⟨d, rfl⟩ := shape_bytes hs h₁
  obtain ⟨i, rfl⟩ := shape_int hs h₂
  obtain ⟨n, rfl⟩ := shape_int hs h₃
  obtain ⟨v, rfl⟩ := shape_int hs h₄
  exact ⟨d, i, n, v, rfl⟩

/-- An argument list of `Int2Bytes` (with `int2Bytes_none`): two integers and `LE` or `BE`. -/
theorem covered_iie {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.int, Srt.int, Srt.endianness]) : ∃ l v e, vs = [int l, int v, en e] := by
  obtain ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩ := sortsOf_three hvs
  obtain ⟨l, rfl⟩ := shape_int hs h₁
  obtain ⟨v, rfl⟩ := shape_int hs h₂
  rcases shape_endian hs h₃ with rfl | rfl
  · exact ⟨l, v, false, rfl⟩
  · exact ⟨l, v, true, rfl⟩

/-! ## Statement 2, stated: Γ states ⊥ on the whole `#False` / `#Bottom` region, in every semantics -/

theorem sorts_cons (c : Semantics) {v : GroundTerm} {vs : List GroundTerm} {s : Srt} {ss : List Srt}
    (h1 : c.sortOf v = some s) (h2 : c.sortsOf vs = some ss) : c.sortsOf (v :: vs) = some (s :: ss) :=
  sortsOf_cons.mpr ⟨s, ss, h1, h2, rfl⟩

/-- Γ states ⊥ where `hook` gives no value and the point is not silent, at a row of `sigTable`. -/
theorem bot_of (c : Semantics) {f : Sym} {as : List Srt} {r : Srt} (hf : (f, as, r) ∈ sigTable)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some as) (hh : hook f vs = some none)
    (hs : silent f vs = false) : Γ c (appP c (sig f) vs ≡ ⊥) := by
  obtain ⟨hk, hname, hargs, -⟩ : sig f ∈ hookSigs ∧ (sig f).name = f ∧ (sig f).args = as ∧
      (sig f).result = r := sig_ok _ hf
  exact gamma_bot c hk (by rw [hargs]; exact hvs) (by rw [hname]; exact hh) (by rw [hname]; exact hs)

/-- The bytes of a literal are bytes. -/
abbrev IsBytes (t : String) : Prop := t.toList.all (·.toNat < 256) = true

/-- **`B[I <- V]` is ⊥ on the region of DOM 2103-2105**, under every interpretation. -/
theorem update_bot (c : Semantics) (H : HookParams) {t : String} (ht : IsBytes t) {i v : Int}
    (h : i < 0 ∨ (t.toList.length : Int) ≤ i ∨ v < 0 ∨ 255 < v) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig bytesUpdate) [bv t, int i, int v] ≡ ⊥) :=
  bot_of _ (as := [Srt.bytes, Srt.int, Srt.int]) (r := Srt.bytes) (by decide)
    (sorts_cons _ (bytes_value _ ht) (sorts_cons _ (int_value _ i) (sorts_cons _ (int_value _ v) sortsOf_nil)))
    ((update_none t i v).mpr h) (not_silent _ (by decide) _)

/-- **`B[I]` is ⊥ on the region of DOM 2115.** -/
theorem get_bot (c : Semantics) (H : HookParams) {t : String} (ht : IsBytes t) {i : Int}
    (h : i < 0 ∨ (t.toList.length : Int) ≤ i) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig bytesGet) [bv t, int i] ≡ ⊥) :=
  bot_of _ (as := [Srt.bytes, Srt.int]) (r := Srt.int) (by decide)
    (sorts_cons _ (bytes_value _ ht) (sorts_cons _ (int_value _ i) sortsOf_nil))
    ((get_none t i).mpr h) (not_silent _ (by decide) _)

/-- **`substrBytes` is ⊥ on the region of DOM 2136-2139.** -/
theorem substr_bot (c : Semantics) (H : HookParams) {t : String} (ht : IsBytes t) {i j : Int}
    (h : i < 0 ∨ j < i ∨ (t.toList.length : Int) < j) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig bytesSubstr) [bv t, int i, int j] ≡ ⊥) :=
  bot_of _ (as := [Srt.bytes, Srt.int, Srt.int]) (r := Srt.bytes) (by decide)
    (sorts_cons _ (bytes_value _ ht) (sorts_cons _ (int_value _ i) (sorts_cons _ (int_value _ j) sortsOf_nil)))
    ((substr_none t i j).mpr h) (not_silent _ (by decide) _)

/-- **`padRightBytes` is ⊥ on the region of DOM 2176-2177.** -/
theorem padRight_bot (c : Semantics) (H : HookParams) {t : String} (ht : IsBytes t) {l v : Int}
    (h : l < 0 ∨ v < 0 ∨ 255 < v) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig bytesPadRight) [bv t, int l, int v] ≡ ⊥) :=
  bot_of _ (as := [Srt.bytes, Srt.int, Srt.int]) (r := Srt.bytes) (by decide)
    (sorts_cons _ (bytes_value _ ht) (sorts_cons _ (int_value _ l) (sorts_cons _ (int_value _ v) sortsOf_nil)))
    ((padRight_none t l v).mpr h) (not_silent _ (by decide) _)

/-- **`padLeftBytes` is ⊥ on the same region.** -/
theorem padLeft_bot (c : Semantics) (H : HookParams) {t : String} (ht : IsBytes t) {l v : Int}
    (h : l < 0 ∨ v < 0 ∨ 255 < v) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig bytesPadLeft) [bv t, int l, int v] ≡ ⊥) :=
  bot_of _ (as := [Srt.bytes, Srt.int, Srt.int]) (r := Srt.bytes) (by decide)
    (sorts_cons _ (bytes_value _ ht) (sorts_cons _ (int_value _ l) (sorts_cons _ (int_value _ v) sortsOf_nil)))
    ((padLeft_none t l v).mpr h) (not_silent _ (by decide) _)

/-- **`replaceAtBytes` is ⊥ at a negative index and where the end index + N is above the length**
(DOM 2146-2147: the range leaves `dest`). -/
theorem replaceAt_bot (c : Semantics) (H : HookParams) {d s : String} (hd : IsBytes d) (hs : IsBytes s) {i : Int}
    (h : i < 0 ∨ (d.toList.length : Int) < i + (s.toList.length : Int)) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig bytesReplaceAt) [bv d, int i, bv s] ≡ ⊥) :=
  have hr := (replaceAt_bot_region d i s).mpr h
  bot_of _ (as := [Srt.bytes, Srt.int, Srt.bytes]) (r := Srt.bytes) (by decide)
    (sorts_cons _ (bytes_value _ hd) (sorts_cons _ (int_value _ i) (sorts_cons _ (bytes_value _ hs) sortsOf_nil)))
    hr.1 hr.2

/-! ## The semantics of `strbytes` (STRING, BYTES, LIST, SET, MAP imported; no function) -/

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
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fns_nil : c.fns = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := fns_nil
  have hrc : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c.withHooks H) (show ∀ k ∈ c.params, k.raw = false by decide +kernel)⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

def b (t : String) : GroundTerm := bv t
def big : GroundTerm := en true
def little : GroundTerm := en false
def sgn : GroundTerm := sn true
def uns : GroundTerm := sn false

structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm
  deriving DecidableEq

/-! ## Statement 1: in-domain values, derived from the prose -/

/-- The expected values, each derived by hand from the cited sentence. A byte is written by its
character: `a` is 97 (0x61), `A` 65, `X` 88, `Y` 89; `\x00`, `\x01`, `\x80`, `\xfe`, `\xff` are 0,
1, 128, 254, 255.
- `.Bytes` (DOM 2030): the byte array of length zero.
- `Bytes2Int` (2059-2063, byte orders 2038-2040). The bytes 01 00: least significant first (`LE`)
  the number 0x0001 = 1, most significant first (`BE`) 0x0100 = 256, unsigned. The byte ff: unsigned
  255; as an 8-bit two's-complement number, all ones, -1. The bytes 00 80, `LE`, signed: the 16 bits
  0x8000, the top bit alone, -2^15 = -32768. At `.Bytes`: 0 (finding 5).
- `Int2Bytes(length, I, E)` (2065-2072). 1 in two bytes: its highest set bit is bit 0, so the 15
  bits above are padding, 0 bits for a positive number: 00 01 most significant first, 01 00 least.
  -1 in one byte: padded with 1 bits, the 8-bit two's complement of -1, ff. -2 in two bytes, `LE`:
  the low byte 1111 1110 = fe, the padding ff. 256 in one byte: its only set bit is bit 8, above
  the 8 bits kept ("the most-significant bits of the integer will be truncated"): 00. In no byte:
  the Bytes of length 0.
- `B[I <- V]` (2101-2102): `b"abc"` with the byte at index 1 set to 0; at index 0 to 65 (`A`); at
  index 2 (the last valid index, 2104-2105) to 255.
- `B[I]` (2114): the byte at index 0 of `b"abc"` is 97; at index 1 of 00 ff it is 255.
- `substrBytes` (2124-2126): of `b"abcd"`, `[1..3)` holds the bytes at 1 and 2, `bc`; `[0..4)` all
  four; `[2..2)` none, and none of the three conditions of 2137-2139 holds there.
- `replaceAtBytes` (2143-2144): `b"abcd"` except the 2 elements starting at index 1 replaced with
  `XY`: `aXYd`; the 2 elements starting at index 2 (the last two, 2 + 2 = the length): `abXY`; the
  0 elements starting at index 4: `abcd` (ruling 1).
- `memsetBytes` (2158-2160): `b"abcd"` except the 2 bytes starting at index 1 replaced with 2 bytes
  of value `Int2Bytes(1, 65, _)`, the byte 65 (`A`): `aAAd`; of value `Int2Bytes(1, -1, _)`, ff
  (above): a ff ff d; the 2 bytes starting at index 2, the last two: `abAA` (ruling 2).
- `padRightBytes`, `padLeftBytes` (2172-2174): `b"a"` to length 3 with 0 on the right, a 00 00; with
  255 on the left, ff ff a; `b"abc"` to length 2 is already at least 2 long: `abc` (2174-2176).
- `reverseBytes` (2191): `cba`. `lengthBytes` (2201): 00 ff `a` has 3 bytes; `.Bytes` has 0 (2030).
- `+Bytes` (2212-2213): `ab` then `c`. -/
def vals : List Pt :=
  [⟨bytesEmpty, [], b ""⟩,
   ⟨bytes2Int, [b "\x01\x00", little, uns], int 1⟩, ⟨bytes2Int, [b "\x01\x00", big, uns], int 256⟩,
   ⟨bytes2Int, [b "\xff", big, uns], int 255⟩, ⟨bytes2Int, [b "\xff", big, sgn], int (-1)⟩,
   ⟨bytes2Int, [b "\x00\x80", little, sgn], int (-32768)⟩, ⟨bytes2Int, [b "", big, sgn], int 0⟩,
   ⟨int2Bytes, [int 2, int 1, big], b "\x00\x01"⟩, ⟨int2Bytes, [int 2, int 1, little], b "\x01\x00"⟩,
   ⟨int2Bytes, [int 1, int (-1), big], b "\xff"⟩, ⟨int2Bytes, [int 2, int (-2), little], b "\xfe\xff"⟩,
   ⟨int2Bytes, [int 1, int 256, big], b "\x00"⟩, ⟨int2Bytes, [int 0, int 5, big], b ""⟩,
   ⟨bytesUpdate, [b "abc", int 1, int 0], b "a\x00c"⟩, ⟨bytesUpdate, [b "abc", int 0, int 65], b "Abc"⟩,
   ⟨bytesUpdate, [b "abc", int 2, int 255], b "ab\xff"⟩,
   ⟨bytesGet, [b "abc", int 0], int 97⟩, ⟨bytesGet, [b "\x00\xff", int 1], int 255⟩,
   ⟨bytesSubstr, [b "abcd", int 1, int 3], b "bc"⟩, ⟨bytesSubstr, [b "abcd", int 0, int 4], b "abcd"⟩,
   ⟨bytesSubstr, [b "abcd", int 2, int 2], b ""⟩,
   ⟨bytesReplaceAt, [b "abcd", int 1, b "XY"], b "aXYd"⟩,
   ⟨bytesReplaceAt, [b "abcd", int 2, b "XY"], b "abXY"⟩, ⟨bytesReplaceAt, [b "abcd", int 4, b ""], b "abcd"⟩,
   ⟨bytesMemset, [b "abcd", int 2, int 2, int 65], b "abAA"⟩,
   ⟨bytesMemset, [b "abcd", int 1, int 2, int 65], b "aAAd"⟩,
   ⟨bytesMemset, [b "abcd", int 1, int 2, int (-1)], b "a\xff\xffd"⟩,
   ⟨bytesPadRight, [b "a", int 3, int 0], b "a\x00\x00"⟩, ⟨bytesPadRight, [b "abc", int 2, int 0], b "abc"⟩,
   ⟨bytesPadLeft, [b "a", int 3, int 255], b "\xff\xffa"⟩, ⟨bytesPadLeft, [b "abc", int 2, int 0], b "abc"⟩,
   ⟨bytesReverse, [b "abc"], b "cba"⟩,
   ⟨bytesLength, [b "\x00\xffa"], int 3⟩, ⟨bytesLength, [b ""], int 0⟩,
   ⟨bytesConcat, [b "ab", b "c"], b "abc"⟩]

/-- Every row has a point, and every point is of a row. -/
theorem vals_rows : (rows.all (fun r => vals.any fun p => p.f == r.1) &&
    vals.all (fun p => rows.any (·.1 == p.f))) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived from the prose**, the arguments of the
signature's sorts. -/
theorem vals_ok : vals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- **(1) At each point the result is that value and Γ states it, under every interpretation.** -/
theorem vals_gamma : ∀ p ∈ vals, ∀ H : HookParams,
    (c.withHooks H).hookRes p.f p.vs = some (some p.v) ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp vals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  refine ⟨Semantics.hookRes_of_value hh, ?_⟩
  exact gamma_val (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)
    (by rw [hname]; exact hh)

/-! ## Statement 2, stated: a point of each part of each `#False` / `#Bottom` region -/

/-- `B[I <- V]` at index -1, at index 3 = the length, at value 256 and -1 (DOM 2103-2105); `B[I]` at
index -1 and 3 (2115); `substrBytes(b"abcd", …)` at start -1, at end 2 < start 3, at end 5 > length 4
(2137-2139); the two paddings at length -1, value 256 and value -1 (2176-2177); `replaceAtBytes` at
an end 3 + 2 = 5 above the length 4, and at a negative index with the end -3 + 2 = -1 below 0, the
end -1 + 2 = 1 within the bytes, and the end -1 + 3 = 2 = the length (2146-2147, ruling 1). -/
def bots : List Pt :=
  [⟨bytesUpdate, [b "abc", int (-1), int 0], b ""⟩, ⟨bytesUpdate, [b "abc", int 3, int 0], b ""⟩,
   ⟨bytesUpdate, [b "abc", int 0, int 256], b ""⟩, ⟨bytesUpdate, [b "abc", int 0, int (-1)], b ""⟩,
   ⟨bytesGet, [b "abc", int (-1)], int 0⟩, ⟨bytesGet, [b "abc", int 3], int 0⟩,
   ⟨bytesSubstr, [b "abcd", int (-1), int 2], b ""⟩, ⟨bytesSubstr, [b "abcd", int 3, int 2], b ""⟩,
   ⟨bytesSubstr, [b "abcd", int 3, int 5], b ""⟩,
   ⟨bytesPadRight, [b "a", int (-1), int 0], b ""⟩, ⟨bytesPadRight, [b "a", int 3, int 256], b ""⟩,
   ⟨bytesPadRight, [b "a", int 3, int (-1)], b ""⟩,
   ⟨bytesPadLeft, [b "a", int (-1), int 0], b ""⟩, ⟨bytesPadLeft, [b "a", int 3, int 256], b ""⟩,
   ⟨bytesPadLeft, [b "a", int 3, int (-1)], b ""⟩,
   ⟨bytesReplaceAt, [b "abcd", int 3, b "XY"], b ""⟩, ⟨bytesReplaceAt, [b "abcd", int (-3), b "XY"], b ""⟩,
   ⟨bytesReplaceAt, [b "abcd", int (-1), b "XY"], b ""⟩, ⟨bytesReplaceAt, [b "ab", int (-1), b "XYZ"], b ""⟩]

/-- Every row of `bottoms` has a point, and every point is of one. -/
theorem bots_rows : (bottoms.all (fun f => bots.any (·.f == f)) &&
    bots.all (fun p => bottoms.contains p.f)) = true := by
  decide +kernel

theorem bots_ok : bots.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && !silent p.f p.vs) = true := by
  decide +kernel

/-- At each, Γ states ⊥ under every interpretation. -/
theorem bots_gamma : ∀ p ∈ bots, ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥) := by
  intro p hp H
  have h := List.all_eq_true.mp bots_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩, hs⟩ := h
  exact gamma_bot (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)
    (by rw [hname]; exact hh) (by rw [hname]; exact hs)

/-- **(2, stated) No interpretation gives a value there**: over all H, Γ entails ⊥, the negation of
the first half of the `param_undetermined` shape. -/
theorem bots_entails : ∀ p ∈ bots, ∀ H : HookParams,
    Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥) := by
  intro p hp H M _ I hI
  exact hI _ (bots_gamma p hp H)

/-! ## Statement 2, unstated: a point of each part of each unstated region -/

/-- `memsetBytes(b"abcd", …)`: an end 3 + 2 = 5 above the length; index -1 with the end 1 valid;
count -1; `v` = 128 and -129 (DOM 2162-2164, ruling 3). `Int2Bytes(-1, 0, BE)`: a negative length
(finding 4). The value `v` has the result sort. -/
def pts : List Pt :=
  [⟨bytesMemset, [b "abcd", int 3, int 2, int 0], b ""⟩, ⟨bytesMemset, [b "abcd", int (-1), int 2, int 0], b ""⟩,
   ⟨bytesMemset, [b "abcd", int 0, int (-1), int 0], b ""⟩, ⟨bytesMemset, [b "abcd", int 0, int 1, int 128], b ""⟩,
   ⟨bytesMemset, [b "abcd", int 0, int 1, int (-129)], b ""⟩,
   ⟨int2Bytes, [int (-1), int 0, big], b ""⟩]

/-- Every key but `Bytes2Int` has a point here (its points are in `ptsB`), and every point is of a
key. -/
theorem pts_keys : (keys.all (fun f => f == bytes2Int || pts.any (·.f == f)) &&
    pts.all (fun p => keys.contains p.f)) = true := by
  decide +kernel

theorem pts_ok : pts.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **(2, unstated) Γ determines none of the points**: over all interpretations it entails neither
that the application has no value nor that it is the point's `v`. -/
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

/-- `strbytes` with one more constructor of sort Endianness (as test/SilentPoints.lean's `c2`):
`coreOK` admits it, and `enumShapesOK` does not. -/
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

/-- `Bytes2Int(b"a", mid, Signed)` and `Int2Bytes(1, 0, mid)`, `mid` the added constructor: the
prose describes the two byte orders `LE` and `BE` (DOM 2038-2040) and no other. -/
noncomputable def ptsB : List Pt :=
  [⟨bytes2Int, [b "a", .ctor midN [], sgn], int 0⟩,
   ⟨int2Bytes, [int 1, int 0, .ctor midN []], b ""⟩]

theorem ptsB_ok : ptsB.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c2.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c2.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **Where Endianness has another constructor, Γ determines neither ⊥ nor a value** at it. -/
theorem extra_undetermined : ∀ p ∈ ptsB,
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

/-! ## The boundary index + N = length (rulings 1 and 2) -/

/-- On the boundary `hook` gives the value the defining sentence describes:
`replaceAtBytes(b"abcd", 2, b"XY")` (the last two bytes replaced), `replaceAtBytes(b"abcd", 4, b"")`
(nothing replaced), `memsetBytes(b"abcd", 2, 2, 65)` (the last two bytes set). The three are points
of `vals`, so Γ states the value under every interpretation (`vals_gamma`). -/
theorem boundary_hook :
    (hook bytesReplaceAt [b "abcd", int 2, b "XY"] == some (some (b "abXY")) &&
     hook bytesReplaceAt [b "abcd", int 4, b ""] == some (some (b "abcd")) &&
     hook bytesMemset [b "abcd", int 2, int 2, int 65] == some (some (b "abAA")) &&
     [(⟨bytesReplaceAt, [b "abcd", int 2, b "XY"], b "abXY"⟩ : Pt), ⟨bytesReplaceAt, [b "abcd", int 4, b ""], b "abcd"⟩,
      ⟨bytesMemset, [b "abcd", int 2, int 2, int 65], b "abAA"⟩].all vals.contains) = true := by
  decide +kernel

/-- `replaceAtBytes(b"ab", -1, b"XYZ")`: a negative index with the end -1 + 3 = 2 = the length. The
range leaves `dest`: `hook` gives no value, the point is not silent, and it is a point of `bots`,
so Γ entails ⊥ there under every interpretation (`bots_entails`). One position past the boundary,
`replaceAtBytes(b"abcd", 3, b"XY")` and `memsetBytes(b"abcd", 3, 2, 65)` have no value. -/
theorem boundary_bot :
    (hook bytesReplaceAt [b "ab", int (-1), b "XYZ"] == some none &&
     !silent bytesReplaceAt [b "ab", int (-1), b "XYZ"] &&
     bots.contains ⟨bytesReplaceAt, [b "ab", int (-1), b "XYZ"], b ""⟩ &&
     hook bytesReplaceAt [b "abcd", int 3, b "XY"] == some none &&
     hook bytesMemset [b "abcd", int 3, int 2, int 65] == some none) = true := by
  decide +kernel

/-- A character that is no byte is no value of Bytes in `strbytes`. -/
theorem not_byte : c.sortOf (bv (String.ofList [Char.ofNat 256])) = none := by decide +kernel

/-! ## Axioms -/

#print axioms rows_registry
#print axioms groups
#print axioms plain_covered
#print axioms not_silent
#print axioms keys_silent
#print axioms replaceAt_silent
#print axioms replaceAt_bot_region
#print axioms update_none
#print axioms get_none
#print axioms substr_none
#print axioms padRight_none
#print axioms padLeft_none
#print axioms replaceAt_none
#print axioms memset_none
#print axioms int2Bytes_none
#print axioms bytes2Int_at
#print axioms concat_at
#print axioms bytes_value
#print axioms bytes_only
#print axioms covered_bytes2Int
#print axioms covered_biii
#print axioms covered_iie
#print axioms update_bot
#print axioms get_bot
#print axioms substr_bot
#print axioms padRight_bot
#print axioms padLeft_bot
#print axioms replaceAt_bot
#print axioms vals_gamma
#print axioms bots_entails
#print axioms pts_undetermined
#print axioms extra_undetermined
#print axioms boundary_hook
#print axioms boundary_bot

end KCore.HooksBytesTest
