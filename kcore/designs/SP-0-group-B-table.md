# FD-B: design for SP-0 group B (filling `silentTable`)

2026-11-14. Read-only; no lean, lake or kompile was run. Every Lean text below is marked "to run" where it is a claim.

Abbreviations: DOM = `k-distribution/include/kframework/builtin/domains.md` of K 7.1.337 (line numbers as in `findings/K4-K5-quotes.md`, section K5); Q = that quotes file; HK = `KcoreSpec/Hooks.lean`, SD = `StringDomain.lean`, FD = `FloatDomain.lean`, FS = `FixedSignature.lean` in `<worktree:kcore-merge>/.../kcore-spec`.

Classes: **(a)** the text says there is no value (`#False`, `#Bottom`): ⊥ stays. **(b)** the text describes the operation on part of its arguments, says "exception", or says backends may differ: silent point. **(c)** the text gives a value: computed.

## 0. What was read, and what was not

- Read: RULES.md; SP-0 (whole); Q section K5; REVIEW-SYNTH (whole); GATE-R1 (whole); HK, SD, FD (whole); `test/SilentPoints.lean`; `test/FloatFieldOne.lean`; `Evaluation.lean:55-110` (`fallback`, `hookRes`); `Faithful.lean:186-236` (`ΓDomains`, `ΓFallback`); FS:486-580 (`hookSigs`, `partialHooks`); KCORE-vs-krust-readings.md by grep of the hook rows (insight only).
- **Path deviation.** The brief's SP-0 path (`<worktree:kcore-merge>/.../designs/SP-0-silent-points.md`) does not exist; kcore-merge has no `designs/`. I read the only copy found, `<worktree:kcore-kinds>/draft-personal/k-semantics-core-2026-11/designs/SP-0-silent-points.md` (579 lines, with §5.2's group A state).
- **Outside the set, read narrowly.** Q has no quote for the List, Map, Int and several String hooks. I read these lines of DOM directly (`k/result/include/kframework/builtin/domains.md`): 222-232, 262-270, 283-300, 326-358, 366-374, 700-722, 751-795, 958-1027, 1218-1240, 1735-1745, 1770-1836, 1857-1873, 2037-2050, 2059-2070, 2097-2120, 2140-2150, 2190-2217. Quotes from those lines below are first-hand and marked "DOM direct".
- Two greps outside the set to locate, not to read: `silentKey` over `KcoreSpec/` (proof sites that need a symbol off the table), `sortOf`/`enumShapesOK` (existence only).
- Not read: `Parse.lean` (`floatLit?`), `Value.lean`, `Core.lean`, `FloatLaws.lean`, every proof file, the cone listing, the ticket file, KN-4 findings, the K manual. Cone membership of `KFloat.ok`, `Lit` and `hookTable` is assumed from SP-0 and GATE-R1, not checked.
- The 79 hooks that never give ⊥ were checked by group against Q's table K5.7 and the DOM lines above, not one sentence each. Where a group rests on a reading, §1.4 says so.

## 1. The table

### 1.1 Entries to add (class b)

The table is consulted only where `hook f vs = some none` (`hookRes`, `ΓFallback`), so the silent region of a key is `hook f vs = some none ∧ p vs`. Where every ⊥ point of a hook at arguments of its sorts is silent, the predicate is `fun _ => true` and the region is the hook's whole ⊥ set, read off `hook` (already in the cone). Only `replaceAtBytes` has both (a) and (b) points and needs a guard. This puts no helper predicate in the cone (N1).

"Region" is written on the unwrapped arguments (`asInt`, `asStr`, …), for an argument list of the declared sorts.

| # | Key | Region (where today's `hook` gives ⊥) | Quote that makes it silent | Why not (a) | Why not (c) |
|---|---|---|---|---|---|
| 1 | `listGet` `[.list _ a, i]` | `¬ (-(a.length : Int) ≤ i ∧ i < a.length)` | DOM direct 960-963: "Positive `Int` indices are 0-indexed from the beginning of the list, and negative indices are -1-indexed from the end of the list. In other words, 0 is the first element and -1 is the last element." | no `#False`; not `total` | no element at that offset is described |
| 2 | `listRange` `[.list _ a, x, y]` | `¬ (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a.length)` | DOM direct 1012-1013: "removing `fromFront` elements from the front of the list and `fromBack` elements from the back of the list" | none stated | removing more elements than there are, or a negative number, is not described |
| 3-7 | `floatAdd`, `floatSub`, `floatMul`, `floatDiv`, `floatRem` `[a, b]` | the two values have different formats (`p ≠ p' ∨ e ≠ e'`, `fl2`) | DOM:1556-1558, 1562-1570: the operations are described and declared with `fp.add roundNearestTiesToEven` etc.; no sentence names the format of a result of two formats | none stated; not `total` | the result is "the exact result rounded", and the format to round to is not given |
| 8-11 | `floatRound` `[a, p, e]`, `int2Float` `[i, p, e]`, `floatMaxValue` `[p, e]`, `floatMinValue` `[p, e]` | `p < 2 ∨ e < 2` (`KFloat.spec?` none). Two parts: (i) `p ≤ 0 ∨ e ≤ 0`; (ii) `1 ≤ p ∧ 1 ≤ e ∧ (p = 1 ∨ e = 1)` | (i) DOM:1469-1476: "`pNxM` where `N` and `M` are positive integers": no format is named. (ii) the format is named and the text gives a value the carrier cannot hold (§4.1) | none stated; not `total` | (i) no format, so no value described. (ii) carrier gap: silent is the interim, it removes a ⊥ the text contradicts (§4.1) |
| 12 | `stringOrd` `[s]` | `s.length ≠ 1` | DOM:1738-1739: "a character (as represented by a string containing a single code point)" | none; not `total` (DOM:1743) | only one-code-point strings are described |
| 13 | `stringChr` `[i]` | `¬ (0 ≤ i ∧ i < 0x110000)`, and surrogates `0xD800 ≤ i < 0xE000` | same sentence; DOM:1702-1703 "a code point between 0x000000 and 0x10ffff" | none; not `total` (DOM:1742) | off the code points: nothing described. Surrogates: carrier gap (§4.2) |
| 14 | `stringSubstr` `[s, a, b]` | `¬ (0 ≤ a ∧ a ≤ b ∧ b ≤ s.length)`; after correction X1 also `0 < a ∧ a = b ∧ b < s.length` | DOM:1753-1755: "this function is only defined on valid indices (i.e., it is defined when `startIndex < endIndex` and `endIndex` is less than or equal to the string length)"; DOM:1758 `total` | "only defined" is not `#False`; the symbol is `total`, so a value exists (OD-5, T) | no sentence gives the value |
| 15, 16 | `stringFind`, `stringRfind` `[s, n, i]` | `¬ (0 ≤ i ∧ i ≤ s.length)` | DOM:1763-1765: "starting at a certain `index`, in another string … Returns `-1` if the substring is not found." | none; not `total` | a search starting at no position of the string is not described; −1 is the result of a search that took place (OD-10, O9) |
| 17, 18 | `stringFindChar`, `stringRfindChar` `[s, cs, i]` | `cs ≠ [] ∧ ¬ (0 ≤ i ∧ i ≤ s.length)` | DOM direct 1774-1776: "starting at a certain `index`, in another string"; rules DOM:1891-1894 reduce to `findString` at the same index | none | the rules' value at such an index is `findString`'s, which is silent. At `cs = []` the rule `findChar(_, "", _) => -1` gives −1 at every index, and `hook` computes it (c) |
| 19 | `string2Int` `[s]` | `s` not `[+-]?[0-9]+` | DOM direct 1820-1822: "in the syntax of the `INT` module (i.e., a nonempty sequence of digits optionally prefixed by a sign)" | none; not `total` (1834) | other strings are not described |
| 20 | `string2Base` `[s, b]` | `¬ (2 ≤ b ∧ b ≤ 36)`, or `s` no numeral of radix `b` | DOM direct 1825-1829: "This radix can be anywhere between 2 and 36. …" | none | nothing for another radix or another string |
| 21 | `stringReplace` `[s, n, r, k]` | `k < 0` | DOM:1908-1910: "Note that the replace function is undefined when Count < 0. This allows different backends to implement their own behavior without contradicting these semantics. For instance, a symbolic backend can return #Bottom for that case, while a concrete backend can throw an exception." | the passage names `#Bottom` as one admissible behaviour among several, so ⊥ is not stated (OD-10, O3) | no value; both rules require `Count ≥ 0` |
| 22 | `string2Bool` `[s]` | `s ≠ "true" ∧ s ≠ "false"` | DOM direct 1792-1794: two rules, no `total`, no prose | none stated | no equation covers it. Follows OD-4 (iii); see §3.6 |
| 23 | `bytesReplaceAt` `[d, i, s]` | `i < 0 ∧ 0 ≤ i + s.length ∧ i + s.length ≤ d.length` (guarded predicate) | DOM:2143-2147: "equal to `dest` except the `N` elements starting at `index` are replaced … The result is `#False` if `index` + `N` is not a valid index." | the `#False` condition speaks of `index + N` only; here `index + N` is within the bytes | no element of `dest` is at a negative `index`, so "the N elements starting at index" names nothing |
| 24 | `bytesMemset` `[d, i, n, v]` | `¬ (0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ d.length ∧ -128 ≤ v ∧ v ≤ 127)` | DOM:2158-2164: "This will throw an exception if `index` + `count` is not a valid index. The acceptable range of values for `v` is -128 to 127. This will throw an exception if `v` is outside of this range." | "exception" is about a run. The text keeps the two apart where it means ⊥: DOM direct 227-228 "The result is `#False` if the maps have keys in common (in particular, this will yield an exception during concrete execution)", and DOM:1908-1910 lists an exception as one behaviour for a value left open | none described there; a negative `index` or `count` is not described either |
| 25 | `bytes2Int` `[b, e, s]` | `e` or `s` is no constructor of BYTES (`asEndian`/`asSigned` none) | DOM:2082 `total`; DOM:2059-2063 "the endianness and signedness of the `Bytes` must be provided"; DOM direct 2043-2044 names `LE`, `BE` only | `total` (T) | no sentence for another constructor |
| 26 | `int2Bytes` `[l, v, e]` | `l < 0`, or `e` no constructor of BYTES | DOM:2083 `total`; DOM:2065-2067 "the `length` of the resulting `Bytes` in bytes is explicitly specified" | `total` (T) | no Bytes has a negative length; nothing for another constructor |
| 27 | `floatSqrt` `[a]` | after correction X2: `a` is −0.0 of its format | DOM:1671 `rule sqrtFloat(F:Float) => rootFloat(F, 2)`; DOM:1577, 1600 | not `total` (DOM:1624), no `#False` | the rule and the prose name two operations that differ there (§3.5) |
| 28 | `setInclusion` `[.set _ a, .set _ b]` | after correction X3: `a` and `b` have the same members | DOM direct 782 "a strict subset of another `Set`" against DOM direct 786 `Set "<=Set" Set [function, total, hook(SET.inclusion)]` | no `#False`; `total` (T) | the text gives two values there, false and true, and no rule chooses (§3.7) |

The table text, for the gate to compare entry by entry (N1). Twenty-seven keys by `fun _ => true`, one guard:

```lean
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
   (bytesReplaceAt, fun vs => match vs with
     | [d, i, s] => (asBytes d).any fun x => (asInt i).any fun i => (asBytes s).any fun y =>
         decide (i < 0 ∧ 0 ≤ i + y.length ∧ i + y.length ≤ x.length)
     | _ => false),
   (bytesMemset, fun _ => true), (bytes2Int, fun _ => true), (int2Bytes, fun _ => true),
   (floatSqrt, fun _ => true), (setInclusion, fun _ => true)]
```

`floatSqrt` enters only with correction X2 (without X2 `hook floatSqrt` never gives ⊥ at a Float value and the entry is dead text; leave it out then). `setInclusion` enters only with correction X3, for the same reason.

Two properties of `fun _ => true` to know:
- At an argument list not of the declared sorts `hook` gives `some none` too, so `hookRes` is the fallback there. Neither Γ (`c.sortsOf vs = some k.args`) nor the evaluation of a well-sorted term reaches such a list (SP-0 §1.1). Suspected harmless; group A's proofs were built with the table irreducible, so none depends on it.
- A later change of `hook` that adds a ⊥ point to one of these 27 keys makes it silent without a table edit. The gate for any later `hook` change must read the key's row here.

### 1.2 Where today's ⊥ stays (class a)

None of these is a key. Each ⊥ is stated by Γ for every interpretation.

| Hook | Region | Quote |
|---|---|---|
| `intTDiv`, `intTMod` | divisor 0 | DOM direct 1233-1234: "using t-division, which rounds towards zero. Division by zero is `#False`." |
| `intEDiv`, `intEMod` | divisor 0 | DOM direct 1235-1237: "Euclidean division, in which the remainder is always non-negative. Division by zero is `#False`." |
| `mapConcat` | a common key | DOM direct 227-228: "The result is `#False` if the maps have keys in common" |
| `mapLookup` | key not in the map | DOM direct 266-267: "The value is `#False` if the key is not in the map" |
| `setConcat` | a common member | DOM:706-707: "the concatenation of two sets containing elements in common is `#False`" (§3.3) |
| `bytesUpdate` | index off `0 … length−1`, or value off `0 … 255` | DOM:2103-2105: "The result is `#False` if `value` is not in the range [0..255] or if `index` is not a valid index (ie, less than zero or greater than or equal to the length of the `Bytes` term)." |
| `bytesGet` | index off `0 … length−1` | DOM:2115: "The result is `#False` if `index` is not a valid index (see above)." |
| `bytesSubstr` | `start < 0 ∨ end < start ∨ length < end` | DOM:2136-2139: "The function is not total: `substrBytes(B, startIndex, endIndex)` is `#Bottom` if …" (the three conditions are exactly `KStr.substr`'s) |
| `bytesPadRight`, `bytesPadLeft` | length < 0, or value off `0 … 255` | DOM:2176-2177: "The result is `#False` if `value` is not in the range `[0..255]`, or if the length is negative." |
| `bytesReplaceAt` | `i + N > length`, or `i + N < 0` | DOM:2146-2147: "The result is `#False` if `index` + `N` is not a valid index." (the guard of row 23 is false here) |

`mapConcat` and `setConcat` are also in `neverSilent` (pattern symbols), so they could not be keys in any case.

### 1.3 Corrections: where today's Lean computes a value the text does not give

Each changes `hook` (cone), so each changes what is computed at `HookParams.none`. They are not table-only and go in their own unit (§5, unit 1).

| Id | Place | Today | The text | Correction | Sure |
|---|---|---|---|---|---|
| X1 | `KStr.substr` as used by `stringSubstr` (SD:37-38, HK:367-369) | `substrString(S, A, A) = ""` for every `0 ≤ A ≤ length` | DOM:1753-1755 asks `startIndex < endIndex`. The text's rules fix `""` only at `A = 0` and `A = length` (§3.1) | `stringSubstr` gives ⊥ at `0 < A = B < length`; row 14 then makes it silent. `substrBytes` keeps `KStr.substr` (its `#Bottom` list does not include `start = end`, and DOM:2124 gives the range `[startIndex..endIndex)`) | shown by reading |
| X2 | `floatSqrt` (HK:318) | IEEE squareRoot everywhere; `sqrtFloat(-0.0) = -0.0` | The rule DOM:1671 makes it `rootFloat(F, 2)`; the prose says "square root". The two IEEE operations differ at −0.0 only (§3.5) | ⊥ at −0.0, silent by row 27 | shown by reading for the rule; the IEEE values of `rootn` are from memory of IEEE 754-2008 §9.2.1, to be checked against the standard |
| X3 | `setInclusion` (HK:197-198) | inclusion: `S <=Set S = true` | The prose says "strict subset" (DOM direct 782), the declaration `<=Set` and `hook(SET.inclusion)` (DOM direct 786); no rule of DOM applies `<=Set` | ⊥ at two equal sets, silent by the table (§3.7). `setInclusion` joins `partialHooks` and `totalSilent` | shown by reading |

Value regions I checked and found a sentence for (not corrections): `substrString` at `A = B ∈ {0, length}` (§3.1); `findString` at `index = length` (§3.4); `Bytes2Int(.Bytes, E, Signed) = 0` (the rule DOM:2250-2251 gives `Int2Bytes(0, _, _) = .Bytes` and DOM:2074-2078 says that result is "convertible back to the original integer via `Bytes2Int`"); `findChar`/`rfindChar` at the empty needle (rules DOM:1892, 1894); `replace` and `replaceFirst` at the empty needle (their rules, given `findString(S, "", 0) = 0`); `freshInt` (rule DOM:1457); `isInfinite` and `=/=Float` (their rules DOM:1673, 1648 give `KFloat.isInf` and the negation of `==Float`; to run as a lemma, §2.3 item 7); `padRightBytes` where the input is already long enough (DOM:2172-2176 "at least `length` bytes long"); the Float comparisons on two formats ("Compute whether a float is less than … another float", DOM:1631-1632: the result is a Bool and needs no result format, unlike arithmetic).

### 1.4 Values that rest on a reading (kept; each is the orchestrator's to overturn)

| Id | Place | Reading the value rests on | Alternative, and what it costs |
|---|---|---|---|
| R1 | `replaceAtBytes`, `memsetBytes` at `index ≥ 0 ∧ index + N = length` (SD:193-201) | "valid index" of an end bound means the N elements exist (`index + N ≤ length`). Decided in §3.4, which **supersedes OD-10's row 50** | silent there: `hook` changes, every write that reaches the last byte becomes dependent on the interpretation |
| R2 | (moved) | `setInclusion` at two equal sets is no longer a kept reading: decided silent, correction X3 (§1.3, §3.7) | — |
| R3 | `stringRfind`, `stringRfindChar` (SD:47-48, 62-65): last position `≤ index` | "find the … last occurrence …, starting at a certain `index`" read as a search backwards from `index` (the `r` of the name). Q notes: "Not found: … what 'starting at' means for `rfindString`" | last position `≥ index`: differs wherever an occurrence exists off `index`. Or silent wherever the two differ: nearly the whole function |
| R4 | Float: floor, ceil, trunc at NaN, ±∞ and the sign of a zero result; `roundFloat`, `Int2Float` and literal ties; `%Float`; `minValueFloat` as the least subnormal | **Reading I**: Float arithmetic is IEEE 754's. The text says so twice: DOM:1481-1483 "a floating-point type represented like an IEEE754 floating-point type", DOM:1637-1638 "in IEEE 754 arithmetic"; and five declarations name `roundNearestTiesToEven` (DOM:1562-1570), the only rounding direction the module names. An operation whose description is one IEEE 754 operation's has that operation's value at every datum | without Reading I, floor/ceil/trunc are `total` and described on finite non-integers only, so NaN, ±∞ and zero results become T points; every inexact `roundFloat`/`Int2Float` becomes silent (no rounding direction stated). `hook` changes on values wasm runs use |
| R5 | `mapRemove`, `mapRemoveAll` at an absent key: the map unchanged | "remove a key/value pair from a map via its key" (DOM direct 295), `total`: the map without a binding for the key | T point (a value exists, undetermined). `mapRemove` would need `partialHooks` or `FallbackTotal` |
| R6 | String order by code point (`lexLt`); `String2Base` accepts a sign; the empty needle occurs at every position; a String is a sequence of code points of any plane | DOM direct 1860-1862 "natural lexicographic ordering"; 1825 "also convert … in a particular radix"; the ordinary meaning of "substring"; DOM:1681-1686 speaks of what "the implementation" supports, not of the meaning | each is a narrowing to a silent region; none proposed |

Reversal for Reading I: a sentence of the text giving another value at a special datum, or an operation whose description fits two IEEE 754 operations with different values; then the points where they differ are silent (X2 is this case).

## 2. Constraints from N1-N3 and group A

### 2.1 `neverSilent`

`neverSilent` = `[mapUnit, mapElem, mapConcat]` ++ `[setUnit, setElem, setConcat, listUnit, listElem, listConcat]` ++ `[kIte, boolAnd, boolOr, boolNot, kEq, kNe, intLt, intLe, intGt, intGe, intEq, intNe, mapUpdate]` (HK:514-516, FS:687-697). None of the 28 keys is among them (checked name by name), so `silentKey_fixed` (`decide +kernel`) still holds with `neverSilent` unedited. The brief must name `neverSilent` as not to be edited (N3).

Other symbols proofs need off the table (grep of `silentKey`): `intSub`, `intTDiv` (SP-0 §5.2: `int2_val_inv`, `ModelUndefRhsWitness`), the pairs of `Semantics.intCompl` (FnExclusive:222-226, by `silentKey_of_mem`), the three symbols of each `builtinColl` (ModelDen:308-311). None is a key. Three lemmas take `silentKey f = false := by decide +kernel` as an auto-param (DecreasingL:621, FnExclusive:175, AgreeInst:533): a caller that instantiates `f` at a key fails to build at that site. Suspected none does (their statements are about Bool-valued comparisons); the build settles it.

### 2.2 N2: is name uniqueness of `hookSigs` needed

Yes, as a decided lemma, outside the cone. `fallback` filters by the result sort of the first entry of that name (`lookupSig hookSigs f`); `ΓFallback` ranges over every `k ∈ hookSigs`. They state the same sentence only if no name occurs twice. By reading FS:486-538 each of the 117 names occurs once (shown by reading, one pass; not run). It is also the hypothesis `hks` of `undetermined` and `gamma_fallback`, needed once per tested entry.

To run (end of `Hooks.lean` or the test):

```lean
theorem hookSigs_lookup : ∀ k ∈ hookSigs, lookupSig hookSigs k.name = some k := by decide +kernel
```

If `CtorSig` has no `DecidableEq` at hand, `(hookSigs.map (·.name)).Nodup` by `decide +kernel` and a two-line corollary.

### 2.3 Decided lemmas beside the table (all outside the cone, `decide +kernel`)

1. `silentKey_fixed` unchanged in text (N3).
2. `(silentTable.map (·.1)).Nodup`: `silent` takes the first entry of a name; a second entry for a key would be dead text the listing cannot see (N1).
3. `∀ e ∈ silentTable, isHook e.1 = true`.
4. `∀ e ∈ silentTable, partialHooks.contains e.1 = true ∨ e.1 = bytes2Int`: the totality deciders read `partialHooks` and stay sound, since off the keys `hookRes = hook` and `bytes2Int` has a value under `enumShapesOK` (`bytes2Int_total`). Checked by reading: every key is in `partialHooks` (`listGet`, `listRange`; `floatResFloat` holds the nine Float keys and `floatSqrt`; `stringPartial` holds the eleven String keys, `string2Bool` among them; `bytesPartial` holds `bytesReplaceAt`, `bytesMemset`, `int2Bytes`) except `bytes2Int`.
5. `hookSigs_lookup` (§2.2).
6. The guard of row 23 against the text's region, to run:
   ```lean
   example (d s : List Char) (i : Int) :
       silent bytesReplaceAt [bytesV d, int i, bytesV s] = decide (i < 0 ∧ 0 ≤ i + s.length ∧ i + s.length ≤ d.length)
   ```
   (needs `asBytes (bytesV d) = some d`; if `String.ofList`/`toList` does not reduce under a variable, state it at `.dv Srt.bytes (.tok t)` with `t.toList`).
7. `isInfinite` agrees with its rule, to run on the special data of binary32 and binary64 by `decide +kernel`: `hook floatIsInfinite [F] = hook boolOr [hook floatGt [F, max], hook floatLt [F, neg max]]` with `max = maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`.

### 2.4 What the Opus lane must prove per entry

`test/SilentPoints.lean` already has the schema `undetermined` (for every `coreOK` semantics and every silent point: neither `≡ ⊥` nor `≡ v` is entailed for every interpretation). Per key, one instance. For each key the lane supplies, at a concrete point `vs` and a concrete test semantics `sem'` that has the argument and result sorts:

- **E1** `hook f vs = some none ∧ silent f vs = true`, by `decide +kernel`.
- **E2** a value `v` with `sem'.sortOf v = some k.result`. This is the non-vacuity of the entry: `fallback` keeps a value only when `sortOf v == some k.result` exactly. For `listGet` the result sort is `KItem`, and a value of sort exactly `KItem` is an injection (`.inj a b t`, Value.lean:231). If no such `v` exists for a key in some semantics, the fallback is ⊥ at every interpretation and the entry asserts ⊥ after all. Result sorts to cover: `KItem` (`listGet`), `List`, `Float`, `Int`, `String`, `Bool` (`string2Bool`), `Bytes`.
- **E3** `undetermined sem' … ` instantiated: `¬ ∀ H, Γ ⊧ app ≡ ⊥` and `¬ ∀ H, Γ ⊧ app ≡ den v`. Needs `coreOK sem'` and `FnHyp` at both interpretations (`sem'` has no function).
- **E4** at one described point of the same key, the value is `hook`'s at every interpretation (`hookRes_of_value`), e.g. `substrString("abc", 0, 0) = ""`, `findString("abc", "b", 3) = -1`, `replaceAtBytes(b"ab", 1, b"c")`.

Points to use (one per row of §1.1): `ListItem(1)[3]`; `range(ListItem(1), 1, 1)`; `1.0 +Float 1.0f`; `roundFloat(1.0, 0, 8)` and `roundFloat(1.0, 1, 8)`; `Int2Float(1, 24, 0)`; `maxValueFloat(0, 8)`; `minValueFloat(53, 1)`; `ordChar("ab")`; `chrChar(-1)` and `chrChar(55296)`; `substrString("abc", 2, 1)`, and after X1 `substrString("abc", 1, 1)`; `findString("abc", "b", 7)`; `rfindString("abc", "b", -1)`; `findChar("abc", "b", 7)`; `rfindChar("abc", "b", 7)`; `String2Int("x")`; `String2Base("10", 1)`; `replace("a", "a", "b", -1)`; `String2Bool("x")`; `replaceAtBytes(b"abc", -1, b"xy")`; `memsetBytes(b"abc", 0, 1, 200)`; `Int2Bytes(-1, 0, BE)`; after X2 `sqrtFloat(-0.0)`; after X3 `SetItem(1) <=Set SetItem(1)`, with E4 at `.Set <=Set SetItem(1)` (true) and `SetItem(1) <=Set .Set` (false).

`bytes2Int` and the added-constructor part of `int2Bytes`: the test needs a semantics with a constructor of sort `Endianness` beyond `LE`, `BE`. If `coreOK` admits none, state that instead: under `coreOK`, `hook bytes2Int vs ≠ some none` at arguments of its sorts, the entry is inert, and say so in the findings.

**Still ⊥ where the text says so.** One generic lemma, then instances:

```lean
/-- to run: off the silent points, Γ states ⊥ where `hook` gives no value, at every semantics. -/
theorem gamma_bot (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = false) :
    Γ c (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ ⊥)
```

(the term of `roundFloat_x1_bot` in `test/FloatFieldOne.lean`, generalized). Instances, one per row of §1.2: `7 /Int 0`, `7 %Int 0`, `7 divInt 0`, `7 modInt 0`; a lookup off the keys; `_Map_` on a common key; `_Set_` on a common member; `B[I <- V]` at `I = length` and at `V = 256`; `B[I]` at `I = length`; `substrBytes(B, 2, 1)`; `padRightBytes(B, -1, 0)`, `padLeftBytes(B, 1, 256)`; `replaceAtBytes(b"ab", 1, b"xy")` (a key, guard false: this is the instance that tests the guard).

`no_silent_point` (`silent f vs = false := rfl`) is false once the table has an entry: delete it.

`test/FloatFieldOne.lean`: its four theorems go through `ΓDomains` with `silent_of_not_silentKey (by decide +kernel)`, which fails once the four format operations are keys. Rewrite as: (1) the same four statements at `c.withHooks HookParams.none`, through `ΓFallback`; (2) `undetermined` at the four points; (3) the residual of §4.1 as a theorem.

### 2.5 `hookRes`' cost

`hookRes` is `if silent f vs then … else hook f vs`: one `silentTable.find?` per hook application, also where `hook` gives a value (SP-0 §5.2). With 28 keys that is up to 28 `Nat` comparisons per application of a symbol that is not a key, in every kernel run. Not measured. The lane measures one existing kernel-decided run test before and after the table (wall time), natively and in the kernel. Do not change `hookRes` in group B: it is a cone definition this design does not name. If the measured cost matters, report it with the proposal (SP-0 §2.3's match-first form, equal at every table by GATE-R1 §3) and stop.

### 2.6 `pureT`

`Determinism.pureT` excludes every key (`isHook f && !silentKey f`), so `groundRefutes` refutes no closed literal that applies one of the 28 keys. That is required (`evalT_pure` is false through a silent point) and it can change a determinism verdict on a definition with such a literal. Validation: `kcore fn-facts` natively on the three texts group A recorded (KEVM 94, mir 50, wasm 1,047) and a diff of the counts.

## 3. Decisions

Each: the options, the decision, the reason from K's text or from what Lean shows, the reversal criterion.

### 3.1 OD-5: `substrString`

**Off `0 ≤ start ≤ end ≤ length`: silent, T** (row 14). `total` (DOM:1758) says a value exists; "only defined on valid indices" (DOM:1753) gives none and is not `#False`. T satisfies both sentences; ⊥ refutes `total`; a fixed value has no sentence. This is OD-5 as decided; nothing in Q overturns it: the sentence does not use `#False` or `#Bottom`, unlike `substrBytes` (DOM:2136).

**`start = end` at 0 and at `length`: `""`, computed.** The rule of `replaceFirst` (DOM:1901-1902), declared `total` and described as replacing "the first occurrence" (DOM:1844-1845), applies `substrString(Source, 0, findString(…))`, which is `(0, 0)` at a match at 0, and `substrString(Source, k + lengthString(ToReplace), lengthString(Source))`, which is `(length, length)` at a match at the end. The rule gives the described result only if both are `""`. The rules of `findChar` (DOM:1891, `substrString(S2, 1, lengthString(S2))` at `S2` of length 1) and `countAllOccurrences` (DOM:1898) need the same.

**`start = end` strictly inside: silent** (correction X1). I went through every rule of DOM that applies `substrString` (1891, 1893, 1898, 1901-1902, 1912-1913, 2749-2750, 2760): each range is `(0, k)` or `(k, length)`, so an empty range arises only at 0 or at the length. No rule reaches the interior. Sentence 1 ("the range is `[startIndex..endIndex)`", DOM:1751-1752) would give the empty string; sentence 2 asks `startIndex < endIndex`. The text says two things there and its rules do not choose, so Γ asserts neither; `total` gives a value.
- What `""` would make provable: `substrString(S, A, A) = ""` for all `A`, and steps of definitions that take interior empty slices, at every interpretation. What silent makes unprovable: exactly those.
- Cost of silent: `hook` changes (X1), so runs through an interior empty slice compute ⊥ at `HookParams.none` where they compute `""` today.
- Wrong if: K's authors say the empty range is valid (upstream list, already there), or ordinary example runs report this point (SP-0 D1's report; criterion 4 of OD-4). Then it returns to the orchestrator with the count.

**Other `total` hooks described partially.** `Int2Bytes` at a negative length and `Bytes2Int`/`Int2Bytes` at an added constructor: T (rows 25, 26), as OD-5 decided. No other interpreted `total` hook has a ⊥ point: by HK, the remaining interpreted hooks declared `total` in Q's K5.7 compute a value at every argument of their sorts. Whether each such value has a sentence is §1.4 (R2, R4, R5).

`FallbackTotal` with `totalSilent := [stringSubstr, bytes2Int, int2Bytes, setInclusion]` is how the text's `total` is stated (SP-0 §2.12, O6 E1): a condition on the interpretation, outside Γ and outside the cone. It belongs in group B as a definition and one lemma (unit 4); taking the three out of `partialHooks` under it stays optional.

### 3.2 The four text-against-declaration conflicts

**(1) `substrString`: `total` against the prose.** §3.1: both read, as T.

**(2) `_Set_`: `idem` against "`#False`".** ⊥ on a common member stays (row of §1.2); `idem` is the sentence left unread (OD-1). Group B adds one argument and changes nothing: the same passage says "(note however, this may be silently allowed during concrete execution)" (DOM:707-708). By OD-10's rule, "backends may differ" makes a silent point. It does not here: the sentence states the meaning (`#False`) and then says that an execution may depart from it ("note however"), the same separation of meaning from run as in the Map sentence (DOM direct 227-228). And `setConcat` is a collection pattern symbol in `neverSilent`: `PatVal` and `collVal` read `hook` for it, so it cannot be a key without redoing the pattern proofs. Wrong if: OD-1's criteria.

**(3) Float literal: prose against the regexes.** Three differences (DOM:1469-1476 against DOM:1495-1497): the prose requires a decimal point, the regex does not (`1e5`, `1f`, `1p24x8`); the prose's sign applies to both forms, the regex's only before digits (`+.5` is no token); the prose asks N and M positive, the regex admits `p0x8`. `Infinity` and `NaN` have regexes and no prose.
Decision: **the regexes say which texts are Float literals; the prose's second paragraph (DOM:1478-1490) gives the value** wherever its computation applies: mantissa as a rational, times 10 to the exponent, rounded to the format the suffix names.
- `1e5`, `1f`: literals with a value (the computation applies to a mantissa without a point).
- `p0xM`, `pNx0`: a token with no format named, so no value described. It is a literal, not an operation, so there is nothing to make silent: the reader refuses it (today's `literal` refusal). That asserts nothing.
- `p1xM`, `pNx1`: a format is named: carrier gap (§4.1); refused today.
- `Infinity…`, `NaN…`: the infinities and the NaN of the format (the regexes name them; Reading I).
Reason: the production is what makes a text a token of the sort; the syntax paragraph contradicts it and the value paragraph does not depend on the contradicted part, so only "followed by a decimal point" is left unread.
This is a reader matter (`Parse.floatLit?`, not read). To run, and report each result: `Parse.floatLit? "1e5"`, `"1f"`, `"1p24x8"`, `"+.5"`, `".5"`, `"1.0p0x8"`, `"Infinityf"`, `"NaNp24x8"`. Expected under this decision: `some` for the first three, the fifth and the last two; `none` for `"+.5"` and `"1.0p0x8"`. A difference is a reader ticket, not group B's.
Wrong if: a corpus text holds a `\dv{SortFloat}` the reader refuses for the missing point (then the reader, not the reading, is wrong), or K's authors say the prose is the syntax.

**(4) `Int2Bytes(Int, Endianness, Signedness)`: `total` with no rule at a negative Int with `Unsigned`.** The symbol has no hook and five rules (DOM:2250-2259); KCore reads it as a parameter wholly (HK:20), so Γ asserts nothing about it and no table entry is possible (it is not in `hookTable`).
Decision: **T at `I < 0` with `Unsigned`; no change in group B.** Reason: the prose asks for the fewest bytes "convertible back to the original integer via `Bytes2Int`" (DOM:2074-2078); no Bytes read unsigned is negative, so the description is unsatisfiable there and gives no value; `total` says one exists. It is an uncovered point of a function declared `total`, which OD-4 and SP-0 group C (`RestTotal`) handle; reading its five rules as clauses belongs to group C or later (they call `log2Int`, a parameter).
Wrong if: group C lands and the reader still drops the five rules; then Γ states less than the text on the covered part, which is allowed and is a coverage ticket.

### 3.3 The contested hooks

- **`memsetBytes` (O2): silent at every ⊥ point** (row 24). Reason in the row: the text uses `#False` where it means no value and "exception" for a run, in its own Map sentence. Wrong if a sentence states `#False` for it.
- **`replace` at `Count < 0` (O3): silent** (row 21). "undefined" is glossed by the next sentence as "different backends … their own behavior", with `#Bottom` one of them.
- **`findString` beyond the string (O9): silent, not −1** (rows 15, 16). Both pass; −1 states more.
- **`findString` at `index = length`: a value, as today.** The text's rules start searches at `index = length`: `findString(Source, ToCount, 0)` with `Source = ""` in the rules of `countAllOccurrences` and `replaceFirst` (DOM:1896-1904), both `total`. So `length` is a position the text searches from, and the search finds nothing for a non-empty needle (−1).

### 3.4 `replaceAtBytes` and `memsetBytes` at the end bound: a value. This supersedes OD-10, row 50

OD-10 lists "`replaceAtBytes` at `index + N = length` silent". **Decided: the value stays, and this section replaces that item of OD-10.** The record has one answer: computed at `0 ≤ index ∧ index + N ≤ length`, ⊥ at `index + N > length` or `index + N < 0`, silent at `index < 0 ≤ index + N ≤ length`.

Why this supersedes rather than the reverse: OD-10 was written from second-hand rows without the passage (REVIEW-SYNTH's own "Not read" lists domains.md, and it made its values "pending K5"). K5's quote is now in hand (Q, DOM:2143-2153), and OD-10's reversal criterion is "a quoted sentence states more than the table assumed". It does: sentence 1 gives the value. OD-10's rule is unchanged; only its application to this row is corrected. Its request to report the literal sentence upstream stands.

- Sentence 1 (DOM:2143-2144) gives the value in full when the N elements starting at `index` exist, that is `0 ≤ index ∧ index + N ≤ length`: "equal to `dest` except the `N` elements starting at `index` are replaced with the contents of `src`". So OD-10's own rule ("a value only with a quoted sentence") is met.
- Sentence 2: "`#False` if `index` + `N` is not a valid index". "Valid index" is defined two sections earlier for the position of one byte ("less than zero or greater than or equal to the length", DOM:2104-2105). Applied to the end bound `index + N` it makes `replaceAtBytes(B, 0, B)` and `replaceAtBytes(.Bytes, 0, .Bytes)` `#False`, against sentence 1 at arguments sentence 1 describes completely. Read as "the end is within the bytes" (`index + N ≤ length`), the two sentences agree everywhere.
- A reading under which the passage is consistent is taken over one under which it contradicts itself; nothing is then left unread.
- What silent would cost: it is not a table entry. `hook` would have to give ⊥ at the end bound, so at `HookParams.none` every write reaching the last byte computes ⊥.
- Wrong if: K's authors confirm the literal reading, or a second passage of the text applies "valid index" to an end bound with `<`. Then the end bound becomes ⊥ (the sentence says `#False`), not silent, and `hook` changes.

`memsetBytes` uses the same phrase ("not a valid index", DOM:2162) and gets the same reading.

### 3.5 `sqrtFloat`

OD-10: "follows the text's rule to `rootFloat` if K5 confirms the rule is there". Q confirms DOM:1671; DOM:1624 declares `sqrtFloat(Float) [function]`, no hook, not `total`; `rootFloat` is "the Nth integer root" (DOM:1577), hooked, not `total`, a parameter in KCore.

Options: (1) today, IEEE squareRoot everywhere; (2) a parameter wholly, `sqrtFloat(F)` being whatever `rootFloat(F, 2)` is: every use computes ⊥ at `HookParams.none`; (3) computed where the rule's operation and the prose's operation agree, silent where they differ.

Decision: **(3).** Under Reading I the rule names IEEE `rootn(x, 2)` and the prose IEEE squareRoot. They agree at every datum (correctly rounded root of a non-negative value, NaN at a negative value, at −∞ and at NaN, +∞ at +∞, +0 at +0) except −0.0: squareRoot gives −0.0, `rootn(−0, 2)` gives +0.0. So −0.0 is a silent point (X2) and nothing else changes.
What (3) still does not state: the equation `sqrtFloat(F) = rootFloat(F, 2)` itself, since `rootFloat` is free. Γ is weaker than the text there, which the headline allows (OD-9).
Wrong if: the IEEE values of `rootn` recalled here are wrong (check §9.2.1 of 754-2008), or `rootFloat` becomes interpreted (then `sqrtFloat` is defined through it and X2's point takes its value).

### 3.6 `String2Bool`

It is an interpreted symbol with two equations and no `total`: the question of OD-4. OD-4 is decided (iii), pending group C. For an interpreted symbol the mechanism is group A's, which has landed with the statements unchanged, so the entry (row 22) goes in with group B.
Wrong if: group C does not land and OD-4 falls back to closure; then delete this one entry (it is the only one that depends on OD-4).

### 3.7 `<=Set`: silent at two equal sets (correction X3)

Prose: "You can determine whether a `Set` is a strict subset of another `Set`" (DOM direct 782). Declaration: `Set "<=Set" Set [function, total, hook(SET.inclusion)]` (DOM direct 786). Today: inclusion, true at equal sets. No rule of DOM applies `<=Set` (grep of the file), so nothing in the text fixes the value at equal sets the way `replaceFirst` fixes `substrString(S, 0, 0)`.

- Inclusion (today): Γ proves `S <=Set S = true`; the word "strict" is unread.
- Strict: Γ proves `S <=Set S = false`; the names `<=` and `inclusion` are unread.
- Silent at equal sets: Γ proves neither; off equal sets the two agree (true exactly when the first is a proper subset) and that value is computed.

All three have models and keep both theorems (a hook's value on values).

**Decided: silent at two equal sets, T** (`total`, so a value exists).
Reason: at equal sets the text states two values, and unlike §3.4 no reading makes both sentences true: "strict subset" excludes equality, and `<=` is the non-strict comparison everywhere else in DOM ("less than or equal to", DOM:1631, DOM direct 1861). Choosing either value asserts a sentence the text also denies. This is the rule already applied to the interior empty range of `substrString` (§3.1): two statements, no rule of the text chooses, Γ asserts neither. It differs from `_Set_` (§3.2 (2)), where one sentence had to be left unread because the symbol is a pattern symbol and cannot be a key.

What it changes (it is a correction, not a table-only entry):
- `hook setInclusion` gives ⊥ where each set includes the other, else `bool (a.all (memS · b))` as today; the key `(setInclusion, fun _ => true)`.
- `setInclusion` joins `partialHooks`: `LazySound.hook_total` states every interpreted symbol off `partialHooks` defined everywhere, so it must. This is the one edit to `partialHooks` this design names. Totality verdicts then change for every function whose right side applies `<=Set`, and `Emit.lean:300` reads `partialHooks`, so generated text may change for such definitions (suspected; not read).
- `setInclusion` joins `totalSilent`; under `FallbackTotal` it is total again.
- At `HookParams.none`, `S <=Set S` computes ⊥ where it computes `true` today.
- `setInclusion` is not in `neverSilent` (checked against HK:514-516).

Default until unit 1 lands: today's inclusion. `<=Map` has the same prose (DOM:378) and is a parameter in KCore, so Γ already asserts nothing about it.

Wrong if: K's authors say which is meant (then the one value, a one-line change of `hook` and the entry removed), a rule of a corpus text's library is found that needs a value at equal sets, or the `kcore fn-facts` diff of unit 1 shows totality facts lost on ordinary definitions in a number the orchestrator judges too high; the last is a scope question about when to land it, not about the reading.

## 4. Carrier gaps

### 4.1 Float formats with a field of 1

With rows 8-11 the four ⊥ statements of `test/FloatFieldOne.lean` are no longer entailed for every interpretation. A residual stays, for every interpretation `H`: `roundFloat(V, 1, 8)` is ⊥ or a Float value, and every Float value has `p ≥ 2` (`KFloat.ok`), so Γ refutes `precisionFloat(roundFloat(V, 1, 8)) = 1`, which the text asserts (DOM:1579-1581: "The resulting `Float` will yield the specified values when calling `precisionFloat`"). To state as a theorem in the test (to run):

```lean
/-- The carrier gap: no Float value has precision 1. -/
theorem precision_ge_two (v : GroundTerm) (n : Int) (h : hook floatPrecision [v] = some (some (int n))) : 2 ≤ n
```

Why silent is right as the interim whatever is decided next: the statements entailed for every `H` under the entry are a subset of those entailed at `HookParams.none`, which is today's Γ. The entry only removes assertions.

Two sizes of extension (both are my estimates from HK, FD and the list of files that name `spec?` or `KFloat.ok`: Core, Value, Parse, Hooks, FloatLaws, ModelDen, SubjectReduction; none of those was read, so the numbers are suspected, not measured):

**X, values only.** `KFloat.ok p e b` also admits `1 ≤ p ∧ 1 ≤ e` with `p = 1 ∨ e = 1`, by a KCore test of the encoding width (Lean core's `Format` needs `p ≥ 2`, `e ≥ 2`); `precisionFloat` and `exponentBitsFloat` read the format off the literal without `spec?`; every other Float hook gives ⊥ at such a value (`asFloat` none) and gets a `fun _ => true` entry (`floatNeg`, `floatAbs`, `floatFloor`, `floatCeil`, `floatTrunc`, the six comparisons, `floatIsNaN`, `floatIsInfinite`: 13 keys, all already in `partialHooks`); the reader keeps refusing the literals.
- Buys: the residual is gone (an interpretation can give a value of format `p1x8`).
- Does not buy: the value itself; Γ still cannot say "a value of that format", since `fallback` filters by sort only.
- Open inside it: at `p = 1` the encoding has no significand field, so the format's NaN has no bit pattern and needs a reserved code; whether `e = 1` has any normal number (`emin = 1 > emax = 0` by the IEEE formulas) is not in the text.
- Cost: cone about +30 to +45 lines (`ok` and its width test 15 to 25, `flFmt` 2 changed, 13 table lines); proof files 4 to 6 (FloatLaws, SubjectReduction's `hook_sorted`, ModelDen where it reads `ok`, the Hooks lemmas, LazySound if it reads `asFloat`); tests `FloatLib`, `FloatFieldOne`. One Opus unit. Generated packages unchanged (no literal of such a format is read).

**Y, computed.** KCore's own data and rounding for the degenerate formats, for all 25 Float hooks and the reader. At `p = 1` round-to-nearest ties have two odd neighbours, so ties stay silent; the datum set at `e = 1` would be asserted from the IEEE formulas with no sentence of K's. Cost: cone +150 to +300 lines, new laws beside FloatLaws (444 lines today for the regular formats). Not recommended: most of what it would assert has no sentence.

Placement: **not in group B's table units.** X changes `KFloat.ok`, a cone definition, so it is before the freeze at R2 or not at all. Recommended: X as its own unit after the table (unit 5), if the owner takes W4; otherwise the gap stays recorded by `precision_ge_two` and one line beside `SoundC`.

### 4.2 `chrChar` at a surrogate

With row 13 the ⊥ is no longer entailed for every interpretation. Residual, for every `H`: `chrChar(55296)` is ⊥ or a string of Unicode scalar values, so Γ refutes `ordChar(chrChar(55296)) = 55296`, which the text's "a string containing a single code point" gives (DOM:1702-1703 counts `0x000000 … 0x10ffff` as code points with no exclusion).

Extension: `Lit.tok` holds a Lean `String`, whose characters are scalar values. Holding a surrogate needs another representation of String values (code points as numbers), which changes `Lit` or `dvOK` (cone), `cmp`, `den` of a domain value, every function of StringDomain (`List Char`), `asStr`/`strV`, the reader's and the printer's string literal, and the `Semantics` literal of every generated package (regeneration and kernel rebuild of all of them). Suspected cost: cone 40 to 80 lines changed, ten or more proof files, every package. KORE cannot write such a string, so the value could never come from a text, only from an interpretation.

Decision: **not before R2; keep the silent entry and record the residual** as a theorem beside `precision_ge_two` and in the upstream list. Reason: the text itself limits its claim here ("does not fully support encodings and code points beyond the initial 256 code points … there may be breaking changes to the semantics of this module", DOM:1681-1686), and the cost is of another order than 4.1's.
Wrong if: a corpus text applies `chrChar` at a surrogate or its KORE holds one.

## 5. The Opus briefs

Two briefs, at most three units each. Common to both:

- Workspace: from release R1's tree (c68b1a1a), with a copied `.lake/build`. `Hooks.lean` is imported by nearly the whole library, so each commit that edits it costs a full rebuild (lake-serial). Unit 1 and unit 2 both edit it: make both edits, then build once; commit them separately.
- Must not change: the text of `sound_hyp`, `complete_hyp`, `SoundC`, `CompleteC`, `StepIs`, `FnHyp`, `coreOK` (`test/Pins.lean` unchanged); `neverSilent` (not edited, not shortened); `silent`, `silentKey`, `Semantics.fallback`, `Semantics.hookRes`, `ΓDomains`, `ΓFallback`, `Γ`; `hookSigs`, `regHookNames`; `partialHooks` except that unit 1 adds `setInclusion`; every `hookTable` entry except the three unit 1 names. If a proof site needs a key off the table, stop and report the lemma's name; do not edit `neverSilent` to pass.
- Lanes do not run `run.sh`, `final.sh`, the judge, syn30/syn100 or KEVM/mir package builds.
- Comments say what the code states and cite DOM lines; no ticket ids.

### Brief 1: corrections, table, tests

**Unit 1. The three corrections to `hook` (cone: `hookTable`'s `stringSubstr`, `floatSqrt` and `setInclusion` entries; SD gets one definition; `partialHooks` gains `setInclusion`).**
- SD: a String-only range function beside `KStr.substr`, giving none also at `0 < a ∧ a = b ∧ b < length`; `substr_mem`'s counterpart. `bytesSubstr` keeps `KStr.substr`.
- HK: `stringSubstr` reads it; `floatSqrt` gives none at the negative zero of the value's format and Lean core's `sqrt` elsewhere; `setInclusion` gives none where each set includes the other (X3, §3.7).
- FS: `setInclusion` appended to `partialHooks`; fix the proofs that enumerate it (`hook_total` and its consumers). Commit X3 separately from X1 and X2, and run `kcore fn-facts` natively on KEVM, mir and wasm before and after it; report the facts that moved.
- Files: SD, HK, whichever proof names `KStr.substr` for strings (SubjectReduction's `hook_sorted`, suspected), `test/StringBytesLib.lean`, `test/FloatLib.lean` where they state the two points.
- Done when: the library builds; `hook stringSubstr [str "abc", int 1, int 1] = some none`, `[…, int 0, int 0]` and `[…, int 3, int 3]` give `""`, `hook floatSqrt` at −0.0 of binary64 gives `some none` and at 4.0 gives 2.0, all by `decide +kernel`.
- This unit changes what is computed at `HookParams.none`. Report it under "most likely to break elsewhere": any example or kernel run through an interior empty substring or `sqrtFloat(-0.0)`.

**Unit 2. The table (cone: `silentTable` only).**
- HK: `silentTable` as in §1.1, exactly that text (the gate compares entry by entry); its docstring says per group which sentence makes the points silent; the header comment of HK (lines 40-46: "an index off the sequence giving no value …") rewritten to what the file now states.
- HK, after `silentKey_fixed`: the decided lemmas of §2.3 items 2 to 5.
- Files: HK; `test/SilentPoints.lean` (`no_silent_point` deleted); `test/FloatFieldOne.lean` (its four `Γ` memberships no longer hold through `ΓDomains`; restate at `withHooks HookParams.none` through `ΓFallback`).
- Validation: the library and its importers build; the existing tests that read hooks or Γ (`FloatLib`, `StringBytesLib`, `TotalsG`, `FnDeciders`, `TerminationGaps`, `AgreeInst`, `EnsGuard`, `ParamsTotal`, `MapItem`, `CallGroups`, `Pins`); native regeneration of the packages and diff (identical expected: the table is not in generated text); `kcore account` over the corpus (identical expected); `kcore fn-facts` on KEVM, mir, wasm natively against 94 / 50 / 1,047 (§2.6; a change is reported with the facts that moved, not fixed); the cone listing: `silentTable` grows by about 12 lines, `hookTable` by the lines of unit 1, nothing else.
- Also measure §2.5 and report the two times.

**Unit 3. The entailment tests.**
- `test/SilentPoints.lean`: per key E1 to E4 of §2.4 at the listed points; `gamma_bot` and its instances; §2.3 items 6 and 7; `precision_ge_two` and the surrogate residual; `#print axioms` on each headline of the file (the three standard axioms only).
- `test/FloatFieldOne.lean`: `undetermined` at the four points.
- Report per key: the point, the value `v` used for E2, and for `bytes2Int` which of the two outcomes of §2.4 holds.
- Must not: weaken `undetermined`'s statement; use a table made in the test for the Γ statements (they are about the library's table).

### Brief 2: totality, the reader check, the carrier

**Unit 4. `FallbackTotal` (outside the cone).**
- `ParamsTotal.lean`: `totalSilent := [stringSubstr, bytes2Int, int2Bytes, setInclusion]`, `FallbackTotal` as SP-0 §2.12, and one lemma: under `FallbackTotal c H`, `(c.withHooks H).hookRes f vs` has a value at every argument list of the sorts, for `f ∈ totalSilent`. No decider reads it yet; `partialHooks` unchanged.
- Test: an `H` that satisfies it at the test semantics, and `HookParams.none` does not.

**Unit 5. The reader check of §3.2 (3) (no change expected).**
- Run the eight `Parse.floatLit?` lines; report each. A difference from the expected column becomes a reader ticket with the literal; do not change `Parse.lean` in this unit.

**Unit 6. Carrier extension X for Float (only if the owner takes W4; cone change, so it ends in the R2 gate).**
- As §4.1 X: `KFloat.ok`, `flFmt`, 13 more `fun _ => true` keys, the reserved NaN code at `p = 1`. Before writing proofs, report the measured cone delta and the list of proof files that fail to build; stop if the delta exceeds 60 lines or more than eight files fail.
- Done when: `precision_ge_two` is false and replaced by a witness (`precisionFloat` of a value of format `p1x8` is 1), and `undetermined` holds at `roundFloat(1.0, 1, 8)` with a `v` of format `p1x8`.

### Things most likely to break elsewhere (for the integration lane)

- Unit 1: runs through an interior empty `substrString` or `sqrtFloat(-0.0)`.
- Unit 2: determinism facts over closed literals that apply a key (§2.6); hand-written User modules or tests that close `silentKey f = false` by `decide` for a symbol that is now a key (grep found the Float format operations in `test/FloatFieldOne.lean` only); kernel time of long runs (§2.5).
- Unit 6: anything that enumerates Float values or relies on `KFloat.ok → spec? = some _`.

## 6. Findings, numbered

Kinds: T table entry, K kept ⊥, X correction, R reading kept, D decision, G gap, C constraint.

| # | Kind | Place | Claim | Sure | Settles it |
|---|---|---|---|---|---|
| 1 | T | `silentTable` | 28 keys (27 `fun _ => true`, one guard), §1.1 | shown by reading | E1-E3 per key |
| 2 | K | 13 hooks, §1.2 | ⊥ stays, each with a `#False`/`#Bottom` sentence | shown by reading | `gamma_bot` instances |
| 3 | X | `stringSubstr` | interior empty range has no sentence | shown by reading | owner of readings: orchestrator; test in unit 1 |
| 4 | X | `floatSqrt` | −0.0: rule and prose name different IEEE values | reading shown; IEEE values suspected | IEEE 754-2008 §9.2.1 |
| 5 | D | `replaceAtBytes`, `memsetBytes` end bound | value kept; §3.4 supersedes OD-10 row 50 | shown by reading | decided; upstream for the literal sentence |
| 6 | X | `setInclusion` | prose "strict subset" against `<=Set`: silent at equal sets (X3); `partialHooks` gains it | shown by reading (DOM direct 782, 786) | decided (§3.7); `kcore fn-facts` diff of unit 1 |
| 7 | R | `stringRfind` | direction of the search has no sentence | suspected | upstream |
| 8 | R | Float specials | values rest on Reading I | shown by reading | a sentence of the text against it |
| 9 | R | `mapRemove` at an absent key | `total`, described as removing a pair | suspected | upstream |
| 10 | C | E2 of §2.4 | an entry is vacuous where no value has exactly the result sort (`KItem` for `listGet`) | suspected | E2 per key |
| 11 | C | `hookSigs` | names unique by reading; needed for `fallback` against `ΓFallback` | shown by reading, not run | `hookSigs_lookup` |
| 12 | C | `hookRes` | one table lookup per hook application, 28 keys | suspected cost | the two timings of unit 2 |
| 13 | C | `pureT` | fewer closed literals refuted | shown by reading | `kcore fn-facts` diff |
| 14 | C | `test/FloatFieldOne.lean`, `no_silent_point` | fail to build once the table is filled | shown by reading | unit 2 |
| 15 | G | Float field of 1 | residual `precisionFloat … ≠ 1` at every interpretation; X costs about one unit and +30 to +45 cone lines | residual shown by reading; cost suspected | unit 6's measured delta; W4 |
| 16 | G | surrogates | residual at every interpretation; extension touches `Lit` and every package | suspected | not before R2 |
| 17 | D | Float literal | regexes say what is a literal, the value paragraph its value; `p0xM` refused | reader behaviour not read | the eight `floatLit?` lines |
| 18 | D | `Int2Bytes` without a length | T at negative `Unsigned`; not group B's | shown by reading | group C |
| 19 | D | `String2Bool` | entry now; the only one tied to OD-4 | shown by reading | group C landing |
| 20 | C | SP-0 path | the brief's path does not exist; kcore-kinds' copy read | shown | — |
