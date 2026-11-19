/-
  K's STRING and BYTES operations interpreted (StringDomain.lean, Hooks.lean `stringHooks`,
  `bytesHooks`; findings/KN-4-string-bytes.md §3). Run from the package root:
  `lake env lean test/StringBytesLib.lean`.
  - Each interpreted operation on concrete values, in the kernel (`hook`): positions count code
    points (`"héllo"` has 5), an index off the sequence gives no value (`substrString` too), the
    empty needle occurs at every position, `replace` with a negative count has none, the
    comparisons are lexicographic by code point, `String2Int` takes INT's syntax, `String2Base` both
    letter cases; Bytes are bytes 0–255, `Bytes2Int` in both byte orders and signednesses, `memset`'s
    value read as a signed byte, an Endianness that is no constructor of BYTES gives no value;
    `chrChar` (none off the Unicode scalar values), `Int2String`, `Bool2String`, `.Bytes`, `Int2Bytes`
    (the low bytes in two's complement, none at a negative length).
  - STRING-COMMON's and BYTES-SYMBOLIC-CEIL's hand-written axioms about the interpreted symbols,
    checked on all words over {a, b} up to a length (`replaceFirst`'s, `replace`'s and `findChar`'s
    equations, `countAllOccurrences`' and `replaceAll`'s at a non-empty needle, `padRightBytes`'
    definedness); and the two places where the library's text and the interpretation part:
    `substrString`'s functional axiom (`substrString("abc", 2, 1)` has no value) and
    `countAllOccurrences`' recursive equation at the empty needle (whose premise holds at
    `("a", "")` and makes the count its own successor; `hook` gives no value there, a silent point).
  - `f2-examples/strbytes.kompile.kore` (STRING and BYTES imported): the verdict, no parameter
    symbol, `shapesOK`, `coreOK`, and the step of `go("hello", b"ab")` to `done("el!", 4)`.
  - String and Bytes literals are values of their sorts in a definition importing neither module
    (`f2-examples/fltadd.kompile.kore`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

def s (x : String) : GroundTerm := .dv Srt.string (.tok x)
def b (x : String) : GroundTerm := .dv Srt.bytes (.tok x)
def le : GroundTerm := .ctor littleEndianBytes []
def be : GroundTerm := .ctor bigEndianBytes []
def sg : GroundTerm := .ctor signedBytes []
def us : GroundTerm := .ctor unsignedBytes []

/-! ## STRING, decided in the kernel -/

/-- Concatenation; the length counts code points (`é` is one, U+1F600 is one). -/
example : hook stringConcat [s "ab", s "cé"] = some (some (s "abcé")) ∧
    hook stringConcat [s "", s ""] = some (some (s "")) ∧
    hook stringLength [s "héllo"] = some (some (int 5)) ∧
    hook stringLength [.dv Srt.string (.tok (String.ofList [Char.ofNat 0x1F600]))] = some (some (int 1)) ∧
    hook stringLength [s ""] = some (some (int 0)) := by decide +kernel

/-- `ordChar` at one code point; no value at another length. -/
example : hook stringOrd [s "A"] = some (some (int 65)) ∧ hook stringOrd [s "é"] = some (some (int 233)) ∧
    hook stringOrd [s "ab"] = some none ∧ hook stringOrd [s ""] = some none := by decide +kernel

/-- `substrString` on `[start..end)`, start = end the empty string at 0 and at the length, no value
at an empty range strictly inside; no value off valid indices. -/
example : hook stringSubstr [s "hello", int 1, int 3] = some (some (s "el")) ∧
    hook stringSubstr [s "hello", int 2, int 2] = some none ∧
    hook stringSubstr [s "hello", int 0, int 0] = some (some (s "")) ∧
    hook stringSubstr [s "hello", int 5, int 5] = some (some (s "")) ∧
    hook stringSubstr [s "", int 0, int 0] = some (some (s "")) ∧
    hook stringSubstr [s "hello", int 0, int 5] = some (some (s "hello")) ∧
    hook stringSubstr [s "hello", int 3, int 6] = some none ∧
    hook stringSubstr [s "hello", int (-1), int 2] = some none ∧
    hook stringSubstr [s "hello", int 3, int 2] = some none := by decide +kernel

/-- `findString`: the first occurrence at or after the index, −1 if none, the empty needle at the
index; no value at an index off 0 … length. -/
example : hook stringFind [s "abcabc", s "bc", int 0] = some (some (int 1)) ∧
    hook stringFind [s "abcabc", s "bc", int 2] = some (some (int 4)) ∧
    hook stringFind [s "abc", s "x", int 0] = some (some (int (-1))) ∧
    hook stringFind [s "abc", s "", int 1] = some (some (int 1)) ∧
    hook stringFind [s "abc", s "", int 3] = some (some (int 3)) ∧
    hook stringFind [s "abc", s "a", int 4] = some none ∧
    hook stringFind [s "abc", s "a", int (-1)] = some none := by decide +kernel

/-- `rfindString`: the last occurrence at or before the index. -/
example : hook stringRfind [s "abcabc", s "bc", int 6] = some (some (int 4)) ∧
    hook stringRfind [s "abcabc", s "bc", int 3] = some (some (int 1)) ∧
    hook stringRfind [s "abc", s "x", int 3] = some (some (int (-1))) ∧
    hook stringRfind [s "abc", s "", int 2] = some (some (int 2)) ∧
    hook stringRfind [s "abc", s "a", int 4] = some none := by decide +kernel

/-- `findChar` and `rfindChar`: a position of any needle character; −1 for no needle at any index. -/
example : hook stringFindChar [s "hello", s "lo", int 0] = some (some (int 2)) ∧
    hook stringFindChar [s "hello", s "xyz", int 0] = some (some (int (-1))) ∧
    hook stringFindChar [s "hello", s "", int 9] = some (some (int (-1))) ∧
    hook stringFindChar [s "hello", s "l", int 9] = some none ∧
    hook stringRfindChar [s "hello", s "lo", int 5] = some (some (int 4)) ∧
    hook stringRfindChar [s "hello", s "h", int 0] = some (some (int 0)) := by decide +kernel

/-- `String2Bool`, `String2Int` (INT's syntax: an optional sign, digits, leading zeros admitted) and
`String2Base` (radix 2–36, letters of either case). -/
example : hook string2Bool [s "true"] = some (some (bool true)) ∧
    hook string2Bool [s "false"] = some (some (bool false)) ∧ hook string2Bool [s "True"] = some none ∧
    hook string2Int [s "42"] = some (some (int 42)) ∧ hook string2Int [s "-0042"] = some (some (int (-42))) ∧
    hook string2Int [s "+7"] = some (some (int 7)) ∧ hook string2Int [s ""] = some none ∧
    hook string2Int [s "-"] = some none ∧ hook string2Int [s "4a"] = some none ∧
    hook string2Int [s "0x10"] = some none := by decide +kernel

example : hook string2Base [s "ff", int 16] = some (some (int 255)) ∧
    hook string2Base [s "FF", int 16] = some (some (int 255)) ∧
    hook string2Base [s "-101", int 2] = some (some (int (-5))) ∧
    hook string2Base [s "z", int 36] = some (some (int 35)) ∧
    hook string2Base [s "2", int 2] = some none ∧ hook string2Base [s "1", int 37] = some none ∧
    hook string2Base [s "1", int 1] = some none := by decide +kernel

/-- `replace` (the first K occurrences, none overlapping; none for K < 0) and `replaceFirst`. -/
example : hook stringReplace [s "aXbXcX", s "X", s "-", int 2] = some (some (s "a-b-cX")) ∧
    hook stringReplace [s "aXbXcX", s "X", s "-", int 0] = some (some (s "aXbXcX")) ∧
    hook stringReplace [s "aXb", s "X", s "-", int (-1)] = some none ∧
    hook stringReplace [s "ab", s "", s "-", int 2] = some (some (s "--ab")) ∧
    hook stringReplace [s "aaa", s "aa", s "b", int 5] = some (some (s "ba")) ∧
    hook stringReplaceFirst [s "aXbX", s "X", s "-"] = some (some (s "a-bX")) ∧
    hook stringReplaceFirst [s "abc", s "", s "-"] = some (some (s "-abc")) ∧
    hook stringReplaceFirst [s "abc", s "x", s "-"] = some (some (s "abc")) := by decide +kernel

/-- The comparisons: lexicographic by code point (`é`, U+00E9, after `z`). -/
example : hook stringLt [s "abc", s "abd"] = some (some (bool true)) ∧
    hook stringLt [s "ab", s "abc"] = some (some (bool true)) ∧
    hook stringLt [s "abc", s "ab"] = some (some (bool false)) ∧
    hook stringLe [s "", s ""] = some (some (bool true)) ∧
    hook stringGt [s "é", s "z"] = some (some (bool true)) ∧
    hook stringGe [s "a", s "b"] = some (some (bool false)) ∧
    hook stringEq [s "a", s "a"] = some (some (bool true)) ∧
    hook stringNe [s "a", s "b"] = some (some (bool true)) := by decide +kernel

/-! ## BYTES, decided in the kernel -/

/-- Length, concatenation, reversal. -/
example : hook bytesLength [b "\x00\xffa"] = some (some (int 3)) ∧
    hook bytesConcat [b "a\x00", b "\xff"] = some (some (b "a\x00\xff")) ∧
    hook bytesReverse [b "abc"] = some (some (b "cba")) := by decide +kernel

/-- `B[I]` and `B[I <- V]`: no value off the indices or at a value outside 0–255. -/
example : hook bytesGet [b "\x00\xff", int 1] = some (some (int 255)) ∧
    hook bytesGet [b "\x00\xff", int 2] = some none ∧ hook bytesGet [b "\x00\xff", int (-1)] = some none ∧
    hook bytesUpdate [b "abc", int 1, int 0] = some (some (b "a\x00c")) ∧
    hook bytesUpdate [b "abc", int 3, int 0] = some none ∧
    hook bytesUpdate [b "abc", int 0, int 256] = some none ∧
    hook bytesUpdate [b "abc", int 0, int (-1)] = some none := by decide +kernel

/-- `substrBytes` and `replaceAtBytes` on ranges within the bytes. -/
example : hook bytesSubstr [b "abcd", int 1, int 3] = some (some (b "bc")) ∧
    hook bytesSubstr [b "abcd", int 2, int 2] = some (some (b "")) ∧
    hook bytesSubstr [b "abcd", int 3, int 5] = some none ∧
    hook bytesSubstr [b "abcd", int 3, int 2] = some none ∧
    hook bytesReplaceAt [b "abcd", int 1, b "XY"] = some (some (b "aXYd")) ∧
    hook bytesReplaceAt [b "abcd", int 2, b "XY"] = some (some (b "abXY")) ∧
    hook bytesReplaceAt [b "abcd", int 3, b "XY"] = some none ∧
    hook bytesReplaceAt [b "abcd", int (-1), b ""] = some none := by decide +kernel

/-- `memsetBytes` (the value a signed byte), `padRightBytes`, `padLeftBytes`. -/
example : hook bytesMemset [b "abcd", int 1, int 2, int (-1)] = some (some (b "a\xff\xffd")) ∧
    hook bytesMemset [b "abcd", int 1, int 2, int 65] = some (some (b "aAAd")) ∧
    hook bytesMemset [b "abcd", int 3, int 2, int 0] = some none ∧
    hook bytesMemset [b "abcd", int 0, int 1, int 128] = some none ∧
    hook bytesMemset [b "abcd", int 0, int (-1), int 0] = some none ∧
    hook bytesPadRight [b "a", int 3, int 0] = some (some (b "a\x00\x00")) ∧
    hook bytesPadRight [b "abc", int 2, int 0] = some (some (b "abc")) ∧
    hook bytesPadRight [b "a", int (-1), int 0] = some none ∧
    hook bytesPadRight [b "a", int 3, int 256] = some none ∧
    hook bytesPadLeft [b "a", int 3, int 255] = some (some (b "\xff\xffa")) := by decide +kernel

/-- `Bytes2Int` in both byte orders and signednesses; no byte is 0; an Endianness value that is no
constructor of BYTES gives no value. -/
example : hook bytes2Int [b "\x01\x00", le, us] = some (some (int 1)) ∧
    hook bytes2Int [b "\x01\x00", be, us] = some (some (int 256)) ∧
    hook bytes2Int [b "\xff", be, sg] = some (some (int (-1))) ∧
    hook bytes2Int [b "\xff", be, us] = some (some (int 255)) ∧
    hook bytes2Int [b "\x00\x80", le, sg] = some (some (int (-32768))) ∧
    hook bytes2Int [b "\x80\x00", le, sg] = some (some (int 128)) ∧
    hook bytes2Int [b "", be, sg] = some (some (int 0)) ∧
    hook bytes2Int [b "\x01", .ctor 1000 [], us] = some none := by decide +kernel

/-- `chrChar` at a Unicode scalar value; none at a surrogate, a negative integer, or above U+10FFFF;
`Int2String` in decimal, `-` only when negative; `Bool2String`. -/
example : hook stringChr [int 65] = some (some (s "A")) ∧ hook stringChr [int 0xE9] = some (some (s "é")) ∧
    hook stringChr [int 0xD800] = some none ∧ hook stringChr [int (-1)] = some none ∧
    hook stringChr [int 0x110000] = some none ∧
    hook int2String [int (-42)] = some (some (s "-42")) ∧ hook int2String [int 0] = some (some (s "0")) ∧
    hook int2String [int 1234567890123] = some (some (s "1234567890123")) ∧
    hook bool2String [bool true] = some (some (s "true")) ∧
    hook bool2String [bool false] = some (some (s "false")) := by decide +kernel

/-- `.Bytes`; `Int2Bytes(L, V, E)`: the L low bytes of V in two's complement, in byte order E; none at
L < 0; `Bytes2Int` reads them back. -/
example : hook bytesEmpty [] = some (some (b "")) ∧
    hook int2Bytes [int 2, int 1, be] = some (some (b "\x00\x01")) ∧
    hook int2Bytes [int 2, int 1, le] = some (some (b "\x01\x00")) ∧
    hook int2Bytes [int 1, int (-1), be] = some (some (b "\xff")) ∧
    hook int2Bytes [int 2, int (-2), le] = some (some (b "\xfe\xff")) ∧
    hook int2Bytes [int 1, int 256, be] = some (some (b "\x00")) ∧
    hook int2Bytes [int 0, int 5, be] = some (some (b "")) ∧
    hook int2Bytes [int (-1), int 5, be] = some none ∧
    hook int2Bytes [int 1, int 5, .ctor 1000 []] = some none ∧
    hook bytes2Int [b "\xfe\xff", le, sg] = some (some (int (-2))) := by decide +kernel

/-! ## The library's axioms read under the interpretation -/

/-- The words over {a, b} of length at most n. -/
def words : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: (words n).flatMap fun w => ['a' :: w, 'b' :: w]

/-- STRING-COMMON's equations of `replaceFirst`: `substrString(S, 0, P) +String R +String
substrString(S, P +Int lengthString(T), lengthString(S))` where `P = findString(S, T, 0) >=Int 0`,
`S` where it is negative. -/
example : (words 3).all (fun x => (words 2).all fun t => [[], ['c']].all fun r =>
    match KStr.find x t 0 with
    | some p => if 0 ≤ p then
        ((KStr.substrString x 0 p).bind fun a => (KStr.substrString x (p + t.length) x.length).map fun z => a ++ r ++ z) ==
          some (KStr.replaceFirst x t r)
      else KStr.replaceFirst x t r == x
    | none => false) = true := by decide +kernel

/-- STRING-COMMON's equations of `replace`, for counts 0 … 2. -/
example : (words 3).all (fun x => (words 2).all fun t => [[], ['c']].all fun r => [0, 1, 2].all fun (k : Int) =>
    match KStr.find x t 0 with
    | some p => if 0 < k ∧ 0 ≤ p then
        ((KStr.substrString x 0 p).bind fun a => (KStr.substrString x (p + t.length) x.length).bind fun z =>
          (KStr.replace z t r (k - 1)).map fun w => a ++ r ++ w) == KStr.replace x t r k
      else KStr.replace x t r k == some x
    | none => false) = true := by decide +kernel

/-- STRING-COMMON's equations of `findChar`: −1 for no needle; else the least of `findString` at the
first needle character and `findChar` at the others, −1 counting as none. -/
example : (words 3).all (fun x => (words 2).all fun cs => (List.range (x.length + 1)).all fun i =>
    match cs with
    | [] => KStr.findChar x cs i == some (-1)
    | ch :: rest => KStr.findChar x cs i == ((KStr.find x [ch] i).bind fun a => (KStr.findChar x rest i).map fun d =>
        if a == -1 then d else if d == -1 then a else min a d)) = true := by decide +kernel

/-- `countAllOccurrences` and `replaceAll` at a non-empty needle: the occurrences found left to
right, the search going on behind each (`"aaa"` holds `"aa"` once); at the empty needle `hook` gives
no value and the point is silent. -/
example : hook stringCountAll [s "aaa", s "aa"] = some (some (int 1)) ∧
    hook stringCountAll [s "aa", s "a"] = some (some (int 2)) ∧
    hook stringCountAll [s "abc", s "x"] = some (some (int 0)) ∧
    hook stringCountAll [s "", s "x"] = some (some (int 0)) ∧
    hook stringReplaceAll [s "aXbX", s "X", s "yy"] = some (some (s "ayybyy")) ∧
    hook stringReplaceAll [s "aaa", s "aa", s "b"] = some (some (s "ba")) ∧
    hook stringReplaceAll [s "abc", s "x", s "y"] = some (some (s "abc")) ∧
    hook stringCountAll [s "a", s ""] = some none ∧ silent stringCountAll [s "a", s ""] = true ∧
    hook stringReplaceAll [s "a", s "", s "b"] = some none ∧
    silent stringReplaceAll [s "a", s "", s "b"] = true := by decide +kernel

/-- STRING-COMMON's equations of `countAllOccurrences` (domains.md 1896-1899), the empty needle
excepted: 0 where `findString(S, T, 0) <Int 0`, and otherwise `1 +Int countAllOccurrences(
substrString(S, findString(S, T, 0) +Int lengthString(T), lengthString(S)), T)`. -/
example : (words 4).all (fun x => (words 2).all fun t => t.isEmpty ||
    match KStr.find x t 0 with
    | some p => if p < 0 then KStr.countAll x t == some 0
        else ((KStr.substrString x (p + t.length) x.length).bind fun z =>
          (KStr.countAll z t).map fun k => 1 + k) == KStr.countAll x t
    | none => false) = true := by decide +kernel

/-- STRING-COMMON's equation of `replaceAll` (domains.md 1917), the empty needle excepted:
`replace(S, T, R, countAllOccurrences(S, T))`. -/
example : (words 4).all (fun x => (words 2).all fun t => t.isEmpty || [[], ['c'], ['a', 'a']].all fun r =>
    KStr.replaceAll x t r == (KStr.countAll x t).bind fun k => KStr.replace x t r k) = true := by
  decide +kernel

/-- BYTES-SYMBOLIC-CEIL: `padRightBytes(_, LEN, VAL)` is defined exactly when `0 <=Int LEN`, `0 <=Int VAL`
and `VAL <Int 256`; `padLeftBytes` likewise. -/
example : [-1, 0, 2].all (fun (l : Int) => [-1, 0, 255, 256].all fun (v : Int) =>
    (KBytes.padRight ['a'] l v).isSome == decide (0 ≤ l ∧ 0 ≤ v ∧ v < 256) &&
    (KBytes.padLeft ['a'] l v).isSome == decide (0 ≤ l ∧ 0 ≤ v ∧ v < 256)) = true := by decide +kernel

/-- Where the library's text and the interpretation part: `substrString` has no value off valid
indices (its text declares it `total`); at `("a", "")` the premise of `countAllOccurrences`'
recursive equation holds (`findString("a", "", 0) = 0`) and its right side calls the count at the
same arguments (`substrString("a", 0 +Int 0, 1) = "a"`), so the equation makes the count its own
successor. -/
example : KStr.substrString "abc".toList 2 1 = none ∧ KStr.find "a".toList [] 0 = some 0 ∧
    KStr.substrString "a".toList (0 + 0) 1 = some "a".toList := by decide +kernel

/-! ## `strbytes`: STRING and BYTES imported, a rule computing with both -/

/-- The reader's verdict on the text at `path`. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; missing {(Parse.missingBuiltin k d).map (·.head)}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/-- info: read; unaccounted []; missing [] -/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/strbytes.kompile.kore")

namespace StrBytes

definition_of defn from "f2-examples/strbytes.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The definition's symbols and sort the step names, by number. -/
def kCell : Sym := 383
def doneL : Sym := 385
def goL : Sym := 386
def cmdS : Srt := 32

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName goL = "Lblgo" ∧ c.symName doneL = "Lbldone" ∧
    c.sortName cmdS = "Cmd" ∧ c.sortName Srt.bytes = "Bytes" := by decide +kernel

/-- The rule's operations (`substrString`, `+String`, `+Bytes`, `lengthBytes`) are all interpreted:
the definition has no parameter symbol. -/
theorem noParams : c.params = [] := by decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

/-- The sorts the interpreted symbols read have their shapes, Endianness and Signedness only BYTES'
constructors (`enumShapesOK`): `Bytes2Int` counts as total for the deciders. -/
theorem shapes : c.shapesOK = true := by decide +kernel

def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def Go : Config c := ⟨cfg (.ctor goL [s "hello", b "ab"]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor doneL [s "el!", int 4]), by decide +kernel⟩

/-- `go("hello", b"ab")` steps to `done("el!", 4)`: `substrString("hello", 1, 3) +String "!"` and
`lengthBytes(b"ab" +Bytes b"\x00\xff")`, computed by the hooks. -/
theorem step_go : Step c Go Done :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

tables_of T from "f2-examples/strbytes.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end StrBytes

#print axioms StrBytes.coreOK
#print axioms StrBytes.step_go

/-! ## String and Bytes literals are values without STRING or BYTES among the imports -/

namespace NoStr

definition_of defn from "f2-examples/fltadd.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- fltadd imports neither STRING nor BYTES; a String literal and a Bytes literal of bytes below 256
are values of their sorts all the same, and a "Bytes" literal with a character above U+00FF is none. -/
theorem lits : c.lib.tokenSorts.contains Srt.string = false ∧ c.lib.byteSorts.contains Srt.bytes = false ∧
    c.sortOf (s "héllo") = some Srt.string ∧ c.sortOf (b "\x00\xff") = some Srt.bytes ∧
    c.sortOf (b "\u0100") = none := by decide +kernel

end NoStr

#print axioms NoStr.lits
