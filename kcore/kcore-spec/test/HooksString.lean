/-
  The supported hook rows of STRING (23) of test/constructs/rows.toml (`hook:STRING.*` with status
  `supported`): the sort row `STRING.String` and the twenty-two operations of `rows`. Each has its three
  statements (DONE-0 C2, evidence of a `supported` hook): one in-domain value; for each region the
  builtin prose leaves unstated, that Γ over all interpretations entails neither ⊥ nor a value at a
  point of it; and that the hook's silent predicate in `silentTable` is that region, or why the prose
  covers every argument list. Run from the package root: `lake env lean test/HooksString.lean`.

  The expected side is the builtin prose: DOM is K 7.1.337's
  k-distribution/include/kframework/builtin/domains.md, cited by line. No expected value is taken
  from a run: each is derived by hand from the cited sentence. `String2Bool` and `Bool2String`
  (DOM 1786-1794) have no `hook` attribute and no row.

  "Unstated" is DOM 14-16: "some functions in the K prelude functions are not total … When you
  invoke such a function on an undefined input, the behavior is undefined". STRING's prose writes no
  `#False`, and `#Bottom` once (DOM 1910), as one behaviour a backend may choose for `replace` at a
  negative count ("a symbolic backend can return #Bottom for that case, while a concrete backend can
  throw an exception"), not as the value: no row has a point where the prose states that there is
  no value.

  The ten rows with no unstated region (none is a key of `silentTable`, `plain_no_key`; each has a
  value at every argument list of its sorts under every interpretation, `plain_covered`):

  | row | prose |
  |---|---|
  | `STRING.concat` | DOM 1721 "concatenate two strings"; `total` 1725 |
  | `STRING.length` | DOM 1730 "the length of a string"; `total` 1733 |
  | `STRING.eq`, `STRING.ne` | DOM 1860 "equal or unequal"; `total` 1865, 1866; equation 1867 |
  | `STRING.lt`, `le`, `gt`, `ge` | DOM 1860-1862 "the natural lexicographic ordering of strings"; `total` 1869-1872; equations 1887-1889 |
  | `STRING.int2string` | DOM 1820-1823; `total` 1835 |
  | `STRING.replaceFirst` | DOM 1842-1845; `total` 1854; equations 1901-1905 |

  The twelve rows with an unstated region, each a key of `silentTable` whose predicate is true at every
  argument list (`keys_silent`), so that its silent points are the argument lists where `hook` gives
  no value: the region of the `*_none` theorem, at every argument list of literals (every argument
  list of the signature is one, `str_only` and `shape_int`, under `shapesOK`).

  | row | prose | region where `hook` gives no value (`*_none`) |
  |---|---|---|
  | `STRING.ord` | DOM 1738-1739 "a string containing a single code point"; 1743, no `total` | a string of no or of several code points |
  | `STRING.chr` | DOM 1738-1739, code points 0 … 0x10ffff (1702-1703); 1742, no `total` | I < 0, I > 0x10FFFF, and 0xD800 ≤ I ≤ 0xDFFF (finding 2) |
  | `STRING.substr` | DOM 1751-1755; `total` 1758 | start < 0, end < start, end > length, and 0 < start = end < length (finding 1) |
  | `STRING.find`, `STRING.rfind` | DOM 1763-1765; 1768, 1769, no `total` | index < 0, index > length (finding 3) |
  | `STRING.findChar`, `STRING.rfindChar` | DOM 1774-1776; equations 1891-1894; 1779, 1780, no `total` | the same, where the search string is not empty (1892, 1894 give -1 at the empty one) |
  | `STRING.string2int` | DOM 1820-1822 "a nonempty sequence of digits optionally prefixed by a sign"; 1834, no `total` | a string off that syntax |
  | `STRING.string2base` | DOM 1825-1829 radix 2 … 36 and its digits; 1837, no `total` | radix < 2, radix > 36, a string off the radix's syntax |
  | `STRING.replace` | DOM 1845; 1908-1910 "undefined when Count < 0. This allows different backends to implement their own behavior"; 1853, no `total` | count < 0 |
  | `STRING.countAllOccurrences` | DOM 1848-1849 "count the number of times a string occurs within another string"; equations 1896-1899; `total` 1855 | the empty needle (finding 4) |
  | `STRING.replaceAll` | DOM 1847 "`replaceAll` replaces every occurrence"; equation 1917; `total` 1852 | the empty needle (finding 4) |

  Statements:
  - **(1)** `vals`: points with the value derived from the cited sentence; `hook` gives it
    (`vals_ok`), it is the result under every interpretation and Γ states it (`vals_gamma`), in the
    semantics of `f2-examples/strbytes.kompile.kore` (STRING imported, `coreOK`, no function). The
    plain rows also at every argument list by their sentence (`concat_at`, `length_at`, `eq_at`,
    `ne_at`, `le_at`, `gt_at`, `ge_at`); `replaceFirst` against its equation 1901-1902 (`rule1901`).
  - **(2)** `pts`: one point of each part of each region; Γ over all interpretations entails neither
    ⊥ nor a value there (`pts_undetermined`).
  - **(3)** `keys_silent` with the twelve `*_none` theorems; `plain_no_key`, `plain_covered`.
    `String2Bool` (DOM 1792-1794), a key of `silentTable` that no registry hook names (the row
    `symbol:STRING-COMMON:…String2Bool…`, not among `rows`): `string2Bool_silent` with
    `string2Bool_none`, no value exactly off `"true"` and `"false"`.

  The sort row `STRING.String` (DOM 1681, 1707-1708): every string of the carrier is a value
  (`str_value`), two strings are two values (`str_inj`), nothing else is one (`str_only`); a sort has
  no argument list.

  Findings (prose against `hook` and `silentTable`), none of which makes a statement here
  unprovable:
  1. `substrString`, two readings. DOM 1753-1755: "this function is only defined on valid indices
     (i.e., it is defined when `startIndex < endIndex` and `endIndex` is less than or equal to the
     string length)", and DOM 1758 declares it `total`. (A) "only defined on" states that there is no
     value off the valid indices: Γ would state ⊥ there under every interpretation. (B) `total`
     states that a value exists, and the prose names none: unstated. `silentTable` takes (B)
     (`pts_undetermined` at four points; `totalSilentKeys`, test/SilentTotal.lean). Under (A) the
     `total` of 1758 is contradicted at `substrString("abc", 2, 1)`. Apart from the two readings, the
     sentence's condition `startIndex < endIndex` excludes every empty range and says nothing of
     `startIndex ≥ 0`, while `hook` gives `""` at an empty range at 0 and at the length
     (`empty_range`): the equations 1901-1902 apply `substrString(Source, 0, 0)` and
     `substrString(Source, length, length)` (`rule1901` at `("ab", "a", "x")` and
     `("ab", "b", "x")`), and `replaceFirst` is `total` (1854) with "replaces exactly one
     occurrence" (1844-1845), which needs `""` there.
  2. Code points. DOM 1700-1703 gives code points 0x0000 … 0x10ffff, the surrogates 0xD800 … 0xDFFF
     among them; a String of the carrier holds none (`KStr.chr`, `chr_none`), so `chrChar(55296)` is
     silent where the prose describes a string (test/SilentPoints.lean `ord_not_surrogate`). DOM
     1683-1686: "The implementation is currently incomplete and does not fully support encodings and
     code points beyond the initial 256 code points …"; `hook` gives values there and no predicate
     of `silentTable` reads a code point (`beyond_latin1`): Γ states `ordChar("Ā") = 256` and
     `lengthString` of one code point above 0xFFFF as 1 under every interpretation.
  3. `findString`, `rfindString`, `findChar`, `rfindChar` at an index above the length, two readings.
     DOM 1763-1765: "starting at a certain `index` … Returns `-1` if the substring is not found".
     (A) no occurrence starts at or after such an index, so the value is the stated -1. (B) the
     index is no position of the string, which the sentence does not describe: unstated.
     `silentTable` takes (B) (`pts_undetermined` at index 4 of `"abc"`). A negative index is
     unstated in both.
  4. `countAllOccurrences` and `replaceAll` at the empty needle. DOM 1898-1899 at the empty needle
     reads `c = 1 +Int c` (`findString(S, "", 0)` is 0, and the rest after the occurrence is S), and
     1855 declares the symbol `total`: with Int the integers no value meets both. The prose (1848-1849)
     does not say how often the empty string occurs. `silentTable` reads the two equations as stating
     the count at a non-empty needle only (`hook` has it, `vals`), and the empty needle as a point
     where a value exists (`total`) and none is given: unstated (`pts_undetermined` at `("a", "")`).
     Under the letter of the text no interpretation is admitted at all. `replaceAll` follows the
     count through 1917.
  Readings, marked: a position is 0 … length (the empty string occurs at the length); the length and
  the positions count code points (the points of `vals` are below 128); `rfindString(S, N, I)` is the
  last occurrence at or before I (the point of `vals` has the same value if read as at or after I);
  `String2Base` takes a sign as `String2Int` does (DOM 1825 "You can also convert … in a particular
  radix").
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HooksStringTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/SilentPoints.lean writes it) -/

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


/-! ## `hook` at literals, and where it gives no value -/

def sv (t : String) : GroundTerm := .dv Srt.string (.tok t)

theorem hook_at {f : Sym} {h : List GroundTerm → Option GroundTerm}
    (hf : hookTable.find? (·.1 == f) = some (f, h)) (vs : List GroundTerm) : hook f vs = some (h vs) := by
  rw [hook_eq, hf]; rfl

theorem asStr_sv (t : String) : asStr (sv t) = some t.toList := by simp [asStr, sv]
theorem asInt_int (i : Int) : asInt (int i) = some i := by simp [asInt, int]

theorem ord_none (t : String) : hook stringOrd [sv t] = some none ↔ t.toList.length ≠ 1 := by
  rw [hook_at (h := fun vs => match vs with
      | [a] => (asStr a).bind fun x => (KStr.ord x).map fun n => int n | _ => none) rfl]
  simp only [asStr_sv, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff]
  rcases t.toList with _ | ⟨ch, _ | ⟨ch2, rest⟩⟩ <;> simp [KStr.ord]

theorem chr_none (i : Int) : hook stringChr [int i] = some none ↔
    (i < 0 ∨ 0x10FFFF < i ∨ (0xD800 ≤ i ∧ i ≤ 0xDFFF)) := by
  rw [hook_at (h := fun vs => match vs with
      | [i] => (asInt i).bind fun x => (KStr.chr x).map strV | _ => none) rfl]
  simp only [asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.chr]
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem substr_none (t : String) (a b : Int) : hook stringSubstr [sv t, int a, int b] = some none ↔
    (a < 0 ∨ b < a ∨ (t.toList.length : Int) < b ∨ (0 < a ∧ a = b ∧ b < t.toList.length)) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, i, j] => (asStr a).bind fun x => (asInt i).bind fun i => (asInt j).bind fun j => (KStr.substrString x i j).map strV
     | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.substrString,
    KStr.substr]
  split
  · rename_i h1; exact ⟨fun _ => Or.inr (Or.inr (Or.inr h1)), fun _ => rfl⟩
  · rename_i h1
    split
    · rename_i h2; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
    · rename_i h2; exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem find_none (t n : String) (i : Int) : hook stringFind [sv t, sv n, int i] = some none ↔
    (i < 0 ∨ (t.toList.length : Int) < i) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i => (KStr.find x y i).map int
     | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.find, KStr.isPos]
  by_cases h : 0 ≤ i ∧ i ≤ t.toList.length
  · simp [h]; all_goals omega
  · simp [h]; all_goals omega

theorem rfind_none (t n : String) (i : Int) : hook stringRfind [sv t, sv n, int i] = some none ↔
    (i < 0 ∨ (t.toList.length : Int) < i) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i => (KStr.rfind x y i).map int
     | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.rfind, KStr.isPos]
  by_cases h : 0 ≤ i ∧ i ≤ t.toList.length
  · simp [h]; all_goals omega
  · simp [h]; all_goals omega

theorem findChar_none (t n : String) (i : Int) : hook stringFindChar [sv t, sv n, int i] = some none ↔
    (n.toList ≠ [] ∧ (i < 0 ∨ (t.toList.length : Int) < i)) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i =>
         (KStr.findChar x y i).map int
     | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.findChar, KStr.isPos]
  by_cases h0 : n.toList = []
  · simp [h0]
  · by_cases h : 0 ≤ i ∧ i ≤ t.toList.length
    · simp [h0, h]; all_goals omega
    · simp [h0, h]; all_goals omega

theorem rfindChar_none (t n : String) (i : Int) : hook stringRfindChar [sv t, sv n, int i] = some none ↔
    (n.toList ≠ [] ∧ (i < 0 ∨ (t.toList.length : Int) < i)) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b, i] => (asStr a).bind fun x => (asStr b).bind fun y => (asInt i).bind fun i =>
         (KStr.rfindChar x y i).map int
     | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.rfindChar, KStr.isPos]
  by_cases h0 : n.toList = []
  · simp [h0]
  · by_cases h : 0 ≤ i ∧ i ≤ t.toList.length
    · simp [h0, h]; all_goals omega
    · simp [h0, h]; all_goals omega

theorem countAll_none (t n : String) : hook stringCountAll [sv t, sv n] = some none ↔ n.toList = [] := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b] => (asStr a).bind fun x => (asStr b).bind fun y => (KStr.countAll x y).map fun k => int k
     | _ => none) rfl]
  simp only [asStr_sv, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.countAll]
  by_cases h : n.toList = [] <;> simp [h]

theorem replaceAll_none (t n r : String) :
    hook stringReplaceAll [sv t, sv n, sv r] = some none ↔ n.toList = [] := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b, r] => (asStr a).bind fun x => (asStr b).bind fun y => (asStr r).bind fun z =>
         (KStr.replaceAll x y z).map strV
     | _ => none) rfl]
  simp only [asStr_sv, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.replaceAll,
    KStr.countAll]
  by_cases h : n.toList = [] <;> simp [h]

theorem replace_none (t n r : String) (k : Int) :
    hook stringReplace [sv t, sv n, sv r, int k] = some none ↔ k < 0 := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b, r, k] => (asStr a).bind fun x => (asStr b).bind fun y => (asStr r).bind fun z => (asInt k).bind fun k =>
         (KStr.replace x y z k).map strV
     | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.replace]
  by_cases h : 0 ≤ k
  · simp [h]
  · simp [h]; omega

/-! INT's syntax in a radix -/

/-- A digit of radix `b` (DOM 1826-1829): `0`-`9` of value below b, a Latin letter of either
case of value 10 + its place below b. -/
def radixDigit (b : Nat) (ch : Char) : Bool :=
  (decide (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) && decide (ch.toNat - 48 < b)) ||
  (decide (97 ≤ ch.toNat ∧ ch.toNat ≤ 122) && decide (ch.toNat - 87 < b)) ||
  (decide (65 ≤ ch.toNat ∧ ch.toNat ≤ 90) && decide (ch.toNat - 55 < b))

/-- A nonempty sequence of digits of radix `b`, optionally after one sign (DOM 1821-1822, 1215). -/
def inSyntax (b : Nat) (cs : List Char) : Bool :=
  match cs with
  | [] => false
  | ch :: ds => if ch = '-' ∨ ch = '+' then !ds.isEmpty && ds.all (radixDigit b)
                else (ch :: ds).all (radixDigit b)

theorem digit_isSome (b : Nat) (ch : Char) : (KStr.digit b ch).isSome = radixDigit b ch := by
  unfold KStr.digit radixDigit
  by_cases h1 : 48 ≤ ch.toNat ∧ ch.toNat ≤ 57 <;> by_cases h2 : 97 ≤ ch.toNat ∧ ch.toNat ≤ 122 <;>
  by_cases h3 : 65 ≤ ch.toNat ∧ ch.toNat ≤ 90 <;> by_cases a1 : ch.toNat - 48 < b <;>
  by_cases a2 : ch.toNat - 87 < b <;> by_cases a3 : ch.toNat - 55 < b <;>
  first
    | (exfalso; omega)
    | simp only [h1, h2, h3, a1, a2, a3, decide_true, decide_false, Bool.or_false, Bool.or_true, Bool.and_true,
        Bool.and_false, ite_true, ite_false, Option.bind_some, Option.bind_none, Option.isSome_some,
        Option.isSome_none, and_self]

theorem digits_isSome (b : Nat) : ∀ (ds : List Char) (acc : Nat),
    (KStr.digits b ds acc).isSome = ds.all (radixDigit b)
  | [], acc => rfl
  | ch :: ds, acc => by
    unfold KStr.digits
    rw [List.all_cons, ← digit_isSome]
    cases h : KStr.digit b ch with
    | none => rfl
    | some d => simpa using digits_isSome b ds _

theorem toIntRadix_isSome (b : Nat) (cs : List Char) : (KStr.toIntRadix b cs).isSome = inSyntax b cs := by
  cases cs with
  | nil => simp [KStr.toIntRadix, inSyntax]
  | cons ch ds =>
    by_cases hm : ch = '-'
    · subst hm
      cases ds with
      | nil => simp [KStr.toIntRadix, inSyntax]
      | cons d ds =>
        simp only [KStr.toIntRadix, inSyntax, true_or, ite_true]
        rw [← digits_isSome b (d :: ds) 0]
        cases KStr.digits b (d :: ds) 0 <;> rfl
    · by_cases hp : ch = '+'
      · subst hp
        cases ds with
        | nil => simp [KStr.toIntRadix, inSyntax]
        | cons d ds =>
          simp only [KStr.toIntRadix, inSyntax, or_true, ite_true]
          rw [← digits_isSome b (d :: ds) 0]
          cases KStr.digits b (d :: ds) 0 <;> rfl
      · have : (KStr.toIntRadix b (ch :: ds)).isSome = (KStr.digits b (ch :: ds) 0).isSome := by
          unfold KStr.toIntRadix
          split
          · rename_i h; cases h; exact absurd rfl hm
          · rename_i h; cases h; exact absurd rfl hp
          · cases KStr.digits b (ch :: ds) 0 <;> rfl
        rw [this, digits_isSome]; simp [inSyntax, hm, hp]

/-- At radix 10 a digit is `0`-`9`. -/
theorem radixDigit_ten (ch : Char) : radixDigit 10 ch = decide (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) := by
  unfold radixDigit
  by_cases h1 : 48 ≤ ch.toNat ∧ ch.toNat ≤ 57 <;> by_cases h2 : 97 ≤ ch.toNat ∧ ch.toNat ≤ 122 <;>
  by_cases h3 : 65 ≤ ch.toNat ∧ ch.toNat ≤ 90 <;> by_cases a1 : ch.toNat - 48 < 10 <;>
  by_cases a2 : ch.toNat - 87 < 10 <;> by_cases a3 : ch.toNat - 55 < 10 <;>
  first
    | (exfalso; omega)
    | simp only [h1, h2, h3, a1, a2, a3, decide_true, decide_false, Bool.or_false, Bool.and_true,
        Bool.and_false, and_self]

theorem string2Int_none (t : String) : hook string2Int [sv t] = some none ↔ inSyntax 10 t.toList = false := by
  rw [hook_at (h := fun vs => match vs with
      | [a] => (asStr a).bind fun x => (KStr.toInt x).map int | _ => none) rfl]
  simp only [asStr_sv, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.toInt]
  rw [← toIntRadix_isSome]
  cases KStr.toIntRadix 10 t.toList <;> simp

theorem string2Base_none (t : String) (b : Int) : hook string2Base [sv t, int b] = some none ↔
    (b < 2 ∨ 36 < b ∨ inSyntax b.toNat t.toList = false) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b] => (asStr a).bind fun x => (asInt b).bind fun b => (KStr.toIntBase x b).map int | _ => none) rfl]
  simp only [asStr_sv, asInt_int, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff, KStr.toIntBase]
  rw [← toIntRadix_isSome]
  split
  · rename_i h
    cases KStr.toIntRadix b.toNat t.toList <;> simp <;> omega
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- The silent predicate of `String2Bool` is true at every argument list: its silent points are the
argument lists where `hook` gives no value (`string2Bool_none`). -/
theorem string2Bool_silent (vs : List GroundTerm) : silent string2Bool vs = true := rfl

/-- `String2Bool` (DOM 1792-1794, two equations, no `total`), a library symbol of STRING-COMMON that
`hook` interprets and a key of `silentTable`, with no registry hook (so it is none of `rows`): no
value exactly off `"true"` and `"false"`. -/
theorem string2Bool_none (t : String) : hook string2Bool [sv t] = some none ↔
    (t.toList ≠ "true".toList ∧ t.toList ≠ "false".toList) := by
  rw [hook_at (h := fun vs => match vs with
      | [a] => (asStr a).bind fun x => (KStr.toBool x).map bool | _ => none) rfl]
  simp only [asStr_sv, Option.bind_some, Option.some.injEq, Option.map_eq_none_iff]
  unfold KStr.toBool
  split
  · rename_i h; simp [h]
  · rename_i h
    split
    · rename_i h'; simp [h']
    · rename_i h'; exact ⟨fun _ => ⟨h, h'⟩, fun _ => rfl⟩


/-! ## The rows -/

/-- The twenty-two supported operation rows: the symbol and its `hook` attribute in the prose's
productions (DOM 1725 `STRING.concat`, 1733 `length`, 1742 `chr`, 1743 `ord`, 1758 `substr`, 1768
`find`, 1769 `rfind`, 1779 `findChar`, 1780 `rfindChar`, 1834 `string2int`, 1835 `int2string`, 1837
`string2base`, 1853 `replace`, 1854 `replaceFirst`, 1865 `eq`, 1866 `ne`, 1869 `lt`, 1870 `le`, 1871
`gt`, 1872 `ge`, 1855 `countAllOccurrences`, 1852 `replaceAll`). The twenty-third row is the sort (`STRING.String`, DOM 1707). -/
def rows : List (Sym × String) :=
  [(stringConcat, "STRING.concat"), (stringLength, "STRING.length"), (stringChr, "STRING.chr"),
   (stringOrd, "STRING.ord"), (stringSubstr, "STRING.substr"), (stringFind, "STRING.find"),
   (stringRfind, "STRING.rfind"), (stringFindChar, "STRING.findChar"), (stringRfindChar, "STRING.rfindChar"),
   (string2Int, "STRING.string2int"), (int2String, "STRING.int2string"), (string2Base, "STRING.string2base"),
   (stringReplace, "STRING.replace"), (stringReplaceFirst, "STRING.replaceFirst"),
   (stringEq, "STRING.eq"), (stringNe, "STRING.ne"), (stringLt, "STRING.lt"), (stringLe, "STRING.le"),
   (stringGt, "STRING.gt"), (stringGe, "STRING.ge"),
   (stringCountAll, "STRING.countAllOccurrences"), (stringReplaceAll, "STRING.replaceAll")]

/-- The ten rows with no unstated region. -/
def plain : List Sym :=
  [stringConcat, stringLength, int2String, stringReplaceFirst, stringEq, stringNe, stringLt, stringLe,
   stringGt, stringGe]

/-- The twelve rows with an unstated region. -/
def keys : List Sym :=
  [stringChr, stringOrd, stringSubstr, stringFind, stringRfind, stringFindChar, stringRfindChar,
   string2Int, string2Base, stringReplace, stringCountAll, stringReplaceAll]

/-- The rows are the registry's entries with a `STRING.` hook, and `plain` and `keys` part them. -/
theorem rows_registry :
    ((regHookNames.filter (fun e => e.2.toList.take 7 == "STRING.".toList)).all rows.contains &&
    rows.all regHookNames.contains &&
    rows.all (fun r => plain.contains r.1 != keys.contains r.1) &&
    (plain ++ keys).all (fun f => rows.any (·.1 == f)) &&
    rows.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1)) = true := by
  decide +kernel

/-! ## Statement 3 -/

/-- **None of the ten plain rows is a key of `silentTable`**, and none is among `partialHooks`. -/
theorem plain_no_key : plain.all (fun f => !silentKey f && !partialHooks.contains f &&
    decide (sig f ∈ hookSigs) && (sig f).name == f) = true := by
  decide +kernel

/-- **Each plain row has a value at every argument list of its sorts, whatever the interpretation**
(the library's `hook_total`). -/
theorem plain_covered (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true) {f : Sym}
    (hf : f ∈ plain) {vs : List GroundTerm} (hvs : (c.withHooks H).sortsOf vs = some (sig f).args) :
    ∃ v, (c.withHooks H).hookRes f vs = some (some v) := by
  have h := List.all_eq_true.mp plain_no_key f hf
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨-, hp⟩, hk⟩, hname⟩ := h
  obtain ⟨v, hv⟩ := hook_total hs (sig f) hk (by rw [hname]; exact hp) vs hvs
  rw [hname] at hv
  exact ⟨v, Semantics.hookRes_of_value hv⟩

/-- **Each of the twelve keys is a key of `silentTable` whose predicate is true at every argument
list**: its silent points are the argument lists where `hook` gives no value. -/
theorem keys_silent : ∀ f ∈ keys, ∀ vs : List GroundTerm, silent f vs = true := by
  intro f hf vs
  simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The plain rows at every argument list of literals, by their sentence: the concatenation (DOM
1721), the length (1730), equality (1860), `=/=String` as `notBool (S1 ==String S2)` (1867),
`<=String` as `notBool (S2 <String S1)` (1887), `>String` as `S2 <String S1` (1888), `>=String` as
`notBool (S1 <String S2)` (1889). -/
theorem concat_at (x y : String) : hook stringConcat [sv x, sv y] = some (some (strV (x.toList ++ y.toList))) := by
  rw [hook_at (h := fun vs => match vs with
     | [a, b] => (asStr a).bind fun x => (asStr b).map fun y => strV (x ++ y) | _ => none) rfl]
  simp [asStr_sv]

theorem length_at (x : String) : hook stringLength [sv x] = some (some (int x.toList.length)) := by
  rw [hook_at (h := fun vs => match vs with | [a] => (asStr a).map fun x => int x.length | _ => none) rfl]
  simp [asStr_sv]

theorem str2_at (x y : String) (f : List Char → List Char → Bool) :
    str2 [sv x, sv y] f = some (bool (f x.toList y.toList)) := by
  simp [str2, asStr_sv]

theorem eq_at (x y : String) : hook stringEq [sv x, sv y] = some (some (bool (decide (x.toList = y.toList)))) := by
  have h : (x.toList == y.toList) = decide (x.toList = y.toList) := by
    by_cases h : x.toList = y.toList <;> simp [h]
  rw [hook_at (h := fun vs => str2 vs fun x y => x == y) rfl, str2_at, h]

theorem ne_at (x y : String) : hook stringNe [sv x, sv y] = some (some (bool (!decide (x.toList = y.toList)))) := by
  have h : (x.toList != y.toList) = !decide (x.toList = y.toList) := by
    by_cases h : x.toList = y.toList <;> simp [h]
  rw [hook_at (h := fun vs => str2 vs fun x y => x != y) rfl, str2_at, h]

theorem lt_at (x y : String) : hook stringLt [sv x, sv y] = some (some (bool (KStr.lexLt x.toList y.toList))) := by
  rw [hook_at (h := fun vs => str2 vs KStr.lexLt) rfl, str2_at]

theorem le_at (x y : String) : hook stringLe [sv x, sv y] = some (some (bool (!KStr.lexLt y.toList x.toList))) := by
  rw [hook_at (h := fun vs => str2 vs fun x y => !KStr.lexLt y x) rfl, str2_at]

theorem gt_at (x y : String) : hook stringGt [sv x, sv y] = some (some (bool (KStr.lexLt y.toList x.toList))) := by
  rw [hook_at (h := fun vs => str2 vs fun x y => KStr.lexLt y x) rfl, str2_at]

theorem ge_at (x y : String) : hook stringGe [sv x, sv y] = some (some (bool (!KStr.lexLt x.toList y.toList))) := by
  rw [hook_at (h := fun vs => str2 vs fun x y => !KStr.lexLt x y) rfl, str2_at]

/-! ## The sort row `STRING.String` -/

/-- Every string of the carrier is a value of sort String (DOM 1681, 1707), in every semantics under
every interpretation. -/
theorem str_value (c : Semantics) (H : HookParams) (t : String) :
    (c.withHooks H).sortOf (sv t) = some Srt.string :=
  sortOf_dv.mpr ⟨by simp [dvOK, Lib.carrier_of_lt _ (by decide : Srt.string < nRegSorts)], rfl⟩

/-- Two strings are two values. -/
theorem str_inj {t u : String} (h : sv t = sv u) : t = u := by
  simp only [sv, GroundTerm.dv.injEq, Lit.tok.injEq, true_and] at h; exact h

/-- Nothing else is a value of sort String (under `shapesOK`): the prose gives String no constructor,
only the tokens of DOM 1708. -/
theorem str_only (c : Semantics) (H : HookParams) (hs : (c.withHooks H).shapesOK = true) {v : GroundTerm}
    (h : (c.withHooks H).sortOf v = some Srt.string) : ∃ t, v = sv t :=
  shape_string hs h

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


def s (t : String) : GroundTerm := sv t

structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm
  deriving DecidableEq

/-! ## Statement 1: in-domain values, derived from the prose -/

/-- The expected values, each derived by hand from the cited sentence.
- `+String` (DOM 1721): `"ab"` then `"cd"` is `"abcd"`.
- `lengthString` (1730): `"abc"` has three characters.
- `chrChar`, `ordChar` (1738-1739): the character `a` is code point 97 (0x61).
- `substrString` (1751-1752): of `"hello"`, the range `[1..3)` holds the characters at 1 and 2, `el`.
- `findString` (1763-1765): in `"abcb"` from 0 the first `b` is at 1; `"x"` is not found in `"abc"`,
  -1. `rfindString`: in `"abcb"` the last `b` is at 3, and the index is 3.
- `findChar` (1774-1775): in `"abc"` from 0, of the characters `c` and `b` the first to occur is `b`,
  at 1; at the empty search string -1 (1892). `rfindChar`: in `"abc"` up to 2, of `a` and `b` the last
  is `b`, at 1; -1 at the empty search string (1894).
- `String2Int` (1820-1822): `-12` is a sign and two digits, the integer -12. `Int2String`
  (1822-1823): of -12 `"-12"`, of 12 `"12"` ("the sign will not be present unless the integer is
  negative").
- `String2Base` (1825-1829): in radix 16, `f` is the sixth letter, 15; `ff` is 15 · 16 + 15 = 255,
  and `FF` the same ("Both uppercase and lowercase letters are supported"); in radix 2, `101` is 5.
- `replace` (1845): the first 2 occurrences of `a` in `"aaa"` by `b`: `"bba"`; 0 occurrences:
  `"aaa"` (1915-1916). `replaceFirst` (1844-1845): `"baa"`; no occurrence of `x`: `"aaa"` (1904-1905).
- `countAllOccurrences` (1848-1849, 1896-1899): `"aa"` occurs in `"aaa"` at 0, and after it `"a"`
  holds none: 1; `"a"` occurs in `"aa"` at 0 and, after it, in `"a"`: 2; `"x"` does not occur in
  `"abc"`: 0. `replaceAll` (1847, 1917): `replace` at the count 2 of `"X"` in `"aXbX"`, both
  occurrences by `"yy"`: `"ayybyy"`.
- `==String`, `=/=String` (1860, 1867): `"a"` and `"a"` are equal, `"a"` and `"b"` are not.
- `<String` (1862, lexicographic): `"a"` before `"b"`; `"ab"` before `"b"` (the first characters
  decide); `"a"` before `"ab"` (a proper prefix); not `"b"` before `"a"`. `<=String` (1887), `>String`
  (1888), `>=String` (1889) from it. -/
def vals : List Pt :=
  [⟨stringConcat, [s "ab", s "cd"], s "abcd"⟩,
   ⟨stringLength, [s "abc"], int 3⟩,
   ⟨stringChr, [int 97], s "a"⟩, ⟨stringOrd, [s "a"], int 97⟩,
   ⟨stringSubstr, [s "hello", int 1, int 3], s "el"⟩,
   ⟨stringFind, [s "abcb", s "b", int 0], int 1⟩, ⟨stringFind, [s "abc", s "x", int 0], int (-1)⟩,
   ⟨stringRfind, [s "abcb", s "b", int 3], int 3⟩,
   ⟨stringFindChar, [s "abc", s "cb", int 0], int 1⟩, ⟨stringFindChar, [s "abc", s "", int 0], int (-1)⟩,
   ⟨stringRfindChar, [s "abc", s "ab", int 2], int 1⟩, ⟨stringRfindChar, [s "abc", s "", int 2], int (-1)⟩,
   ⟨string2Int, [s "-12"], int (-12)⟩,
   ⟨int2String, [int (-12)], s "-12"⟩, ⟨int2String, [int 12], s "12"⟩,
   ⟨string2Base, [s "ff", int 16], int 255⟩, ⟨string2Base, [s "FF", int 16], int 255⟩,
   ⟨string2Base, [s "101", int 2], int 5⟩,
   ⟨stringReplace, [s "aaa", s "a", s "b", int 2], s "bba"⟩,
   ⟨stringReplace, [s "aaa", s "a", s "b", int 0], s "aaa"⟩,
   ⟨stringReplaceFirst, [s "aaa", s "a", s "b"], s "baa"⟩,
   ⟨stringReplaceFirst, [s "aaa", s "x", s "b"], s "aaa"⟩,
   ⟨stringCountAll, [s "aaa", s "aa"], int 1⟩, ⟨stringCountAll, [s "aa", s "a"], int 2⟩,
   ⟨stringCountAll, [s "abc", s "x"], int 0⟩,
   ⟨stringReplaceAll, [s "aXbX", s "X", s "yy"], s "ayybyy"⟩,
   ⟨stringEq, [s "a", s "a"], bool true⟩, ⟨stringEq, [s "a", s "b"], bool false⟩,
   ⟨stringNe, [s "a", s "a"], bool false⟩, ⟨stringNe, [s "a", s "b"], bool true⟩,
   ⟨stringLt, [s "a", s "b"], bool true⟩, ⟨stringLt, [s "ab", s "b"], bool true⟩,
   ⟨stringLt, [s "a", s "ab"], bool true⟩, ⟨stringLt, [s "b", s "a"], bool false⟩,
   ⟨stringLe, [s "a", s "a"], bool true⟩, ⟨stringLe, [s "b", s "a"], bool false⟩,
   ⟨stringGt, [s "b", s "a"], bool true⟩, ⟨stringGt, [s "a", s "a"], bool false⟩,
   ⟨stringGe, [s "a", s "a"], bool true⟩, ⟨stringGe, [s "a", s "b"], bool false⟩]

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

/-- The right-hand side of DOM 1901-1902 by the hooks of its symbols:
`substrString(S, 0, findString(S, N, 0)) +String R +String
substrString(S, findString(S, N, 0) +Int lengthString(N), lengthString(S))`. -/
def rhs1901 (S N R : GroundTerm) : Option GroundTerm := do
  let i ← (hook stringFind [S, N, int 0]).join
  let a ← (hook stringSubstr [S, int 0, i]).join
  let ln ← (hook stringLength [N]).join
  let j ← (hook intAdd [i, ln]).join
  let ls ← (hook stringLength [S]).join
  let b ← (hook stringSubstr [S, j, ls]).join
  let ab ← (hook stringConcat [a, R]).join
  (hook stringConcat [ab, b]).join

/-- `replaceFirst` is its equation 1901-1902 where the first argument holds the second (its premise
`findString(S, N, 0) >=Int 0`): at `("abc", "b", "x")`, and at `("ab", "a", "x")` and
`("ab", "b", "x")`, where the equation applies `substrString` at the empty ranges `[0..0)` and
`[2..2)` of `"ab"`; the values are the prose's "replaces exactly one occurrence … the first" (DOM
1844-1845). -/
theorem rule1901 :
    ([(s "abc", s "b", s "x", s "axc"), (s "ab", s "a", s "x", s "xb"), (s "ab", s "b", s "x", s "ax")].all
      fun (S, N, R, v) => rhs1901 S N R == some v && hook stringReplaceFirst [S, N, R] == some (some v)) = true := by
  decide +kernel

/-- `hook` gives the empty string at an empty range at 0 and at the length (finding 1). -/
theorem empty_range : hook stringSubstr [s "ab", int 0, int 0] = some (some (s "")) ∧
    hook stringSubstr [s "ab", int 2, int 2] = some (some (s "")) := by
  decide +kernel

/-- Code points above 255 (finding 2): `ordChar` of U+0100 and `lengthString` of U+1F600. -/
def beyond : List Pt :=
  [⟨stringOrd, [strV [Char.ofNat 0x100]], int 256⟩, ⟨stringLength, [strV [Char.ofNat 0x1F600]], int 1⟩]

theorem beyond_ok : beyond.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- Γ states a value at each, under every interpretation: no silent predicate reads a code point. -/
theorem beyond_latin1 : ∀ p ∈ beyond, ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp beyond_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  exact gamma_val (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)
    (by rw [hname]; exact hh)

/-! ## Statement 2: a point of each part of each unstated region -/

/-- `ordChar` at no and at two code points; `chrChar` below 0, above 0x10FFFF and at a surrogate;
`substrString("abc", …)` at start < 0, end < start, end > length and an empty range strictly inside;
the four searches in `"abc"` at index -1 and at index 4; `String2Int` at a letter, at the empty
string and at a sign alone; `String2Base` at radix 1 and 37, at a digit off radix 16 and at the
empty string; `replace` at count -1; `countAllOccurrences` and `replaceAll` at the empty needle. The
value `v` has the result sort. -/
def pts : List Pt :=
  [⟨stringOrd, [s ""], int 0⟩, ⟨stringOrd, [s "ab"], int 0⟩,
   ⟨stringChr, [int (-1)], s ""⟩, ⟨stringChr, [int 0x110000], s ""⟩, ⟨stringChr, [int 55296], s ""⟩,
   ⟨stringSubstr, [s "abc", int (-1), int 2], s ""⟩, ⟨stringSubstr, [s "abc", int 2, int 1], s ""⟩,
   ⟨stringSubstr, [s "abc", int 0, int 4], s ""⟩, ⟨stringSubstr, [s "abc", int 1, int 1], s ""⟩,
   ⟨stringFind, [s "abc", s "b", int (-1)], int 0⟩, ⟨stringFind, [s "abc", s "b", int 4], int 0⟩,
   ⟨stringRfind, [s "abc", s "b", int (-1)], int 0⟩, ⟨stringRfind, [s "abc", s "b", int 4], int 0⟩,
   ⟨stringFindChar, [s "abc", s "b", int (-1)], int 0⟩, ⟨stringFindChar, [s "abc", s "b", int 4], int 0⟩,
   ⟨stringRfindChar, [s "abc", s "b", int (-1)], int 0⟩, ⟨stringRfindChar, [s "abc", s "b", int 4], int 0⟩,
   ⟨string2Int, [s "x"], int 0⟩, ⟨string2Int, [s ""], int 0⟩, ⟨string2Int, [s "-"], int 0⟩,
   ⟨string2Base, [s "10", int 1], int 0⟩, ⟨string2Base, [s "10", int 37], int 0⟩,
   ⟨string2Base, [s "g", int 16], int 0⟩, ⟨string2Base, [s "", int 16], int 0⟩,
   ⟨stringReplace, [s "a", s "a", s "b", int (-1)], s ""⟩,
   ⟨stringCountAll, [s "a", s ""], int 0⟩, ⟨stringReplaceAll, [s "a", s "", s "b"], s ""⟩]

/-- Every key has a point, and every point is of a key. -/
theorem pts_keys : (keys.all (fun f => pts.any (·.f == f)) && pts.all (fun p => keys.contains p.f)) = true := by
  decide +kernel

theorem pts_ok : pts.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **(2) Γ determines none of the points**: over all interpretations it entails neither that the
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

#print axioms rows_registry
#print axioms plain_covered
#print axioms keys_silent
#print axioms ord_none
#print axioms chr_none
#print axioms substr_none
#print axioms countAll_none
#print axioms replaceAll_none
#print axioms find_none
#print axioms rfind_none
#print axioms findChar_none
#print axioms rfindChar_none
#print axioms string2Int_none
#print axioms string2Base_none
#print axioms replace_none
#print axioms string2Bool_silent
#print axioms string2Bool_none
#print axioms concat_at
#print axioms ge_at
#print axioms str_value
#print axioms str_only
#print axioms vals_gamma
#print axioms rule1901
#print axioms beyond_latin1
#print axioms pts_undetermined

end KCore.HooksStringTest
