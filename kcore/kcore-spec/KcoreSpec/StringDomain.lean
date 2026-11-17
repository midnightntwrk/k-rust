/-
  KCore. STRING's and BYTES' operations as K's documentation states them (domains.md: STRING-COMMON,
  BYTES-HOOKED), on the characters of their literals (findings/KN-4-string-bytes.md §1–§3).
  A String is its sequence of code points (`List Char`); a Bytes value is its sequence of bytes, one
  character per byte, the character of the byte's number (below 256, `dvOK`). Natural-number,
  integer and list definitions only; Hooks.lean reads them.

  Positions count code points (bytes) from 0. A needle "occurs at" p when it is a prefix of the
  characters from p on, so the empty needle occurs at every position 0 … length.
-/
set_option autoImplicit false

namespace KCore

namespace KStr

/-- `n` occurs in `s` at position `p`. -/
def occursAt (n s : List Char) (p : Nat) : Bool := n.isPrefixOf (s.drop p)

/-- The positions 0 … length of `s`. -/
def positions (s : List Char) : List Nat := List.range (s.length + 1)

/-- The first of a list of positions, −1 for none. -/
def firstOr : List Nat → Int
  | [] => -1
  | p :: _ => p

/-- The last of a list of positions, −1 for none. -/
def lastOr (ps : List Nat) : Int := firstOr ps.reverse

/-- `i` is a position of `s`: 0 ≤ i ≤ length. -/
def isPos (s : List Char) (i : Int) : Bool := decide (0 ≤ i ∧ i ≤ s.length)

/-- `substrBytes(B, a, b)`: the characters at positions a … b − 1; none unless 0 ≤ a ≤ b ≤ length
(domains.md BYTES-HOOKED: `#Bottom` if `startIndex < 0`, `endIndex < startIndex` or
`endIndex > length`; the range `[startIndex..endIndex)`, empty at a = b). -/
def substr (s : List Char) (a b : Int) : Option (List Char) :=
  if 0 ≤ a ∧ a ≤ b ∧ b ≤ s.length then some ((s.drop a.toNat).take (b - a).toNat) else none

/-- `substrString(S, a, b)`: as `substr`, and none also at an empty range strictly inside the string,
0 < a = b < length. domains.md STRING-COMMON (1751-1755) gives the range `[startIndex..endIndex)` and
says the function "is only defined on valid indices (i.e., it is defined when `startIndex < endIndex`
…)"; the module's equations apply an empty range only at 0 and at the length (`findChar`,
`countAllOccurrences`, `replaceFirst`), where the two sentences are both read as the empty string. -/
def substrString (s : List Char) (a b : Int) : Option (List Char) :=
  if 0 < a ∧ a = b ∧ b < s.length then none else substr s a b

/-- `findString(S, N, I)`: the first position p ≥ I at which N occurs, −1 if none; none unless I is a
position of S. -/
def find (s n : List Char) (i : Int) : Option Int :=
  if isPos s i then some (firstOr ((positions s).filter fun p => decide (i ≤ p) && occursAt n s p)) else none

/-- `rfindString(S, N, I)`: the last position p ≤ I at which N occurs, −1 if none; none unless I is a
position of S. -/
def rfind (s n : List Char) (i : Int) : Option Int :=
  if isPos s i then some (lastOr ((positions s).filter fun p => decide (p ≤ i) && occursAt n s p)) else none

/-- The character at position p is one of `cs`. -/
def charIn (s cs : List Char) (p : Nat) : Bool := s[p]?.any cs.contains

/-- `findChar(S, C, I)`: −1 if C is empty; else the first position p ≥ I whose character is one of
C's, −1 if none, and none unless I is a position of S (STRING-COMMON's equations: the least `findString` of
C's characters). -/
def findChar (s cs : List Char) (i : Int) : Option Int :=
  if cs.isEmpty then some (-1)
  else if isPos s i then some (firstOr ((List.range s.length).filter fun p => decide (i ≤ p) && charIn s cs p))
  else none

/-- `rfindChar(S, C, I)`: as `findChar`, the last position p ≤ I. -/
def rfindChar (s cs : List Char) (i : Int) : Option Int :=
  if cs.isEmpty then some (-1)
  else if isPos s i then some (lastOr ((List.range s.length).filter fun p => decide (p ≤ i) && charIn s cs p))
  else none

/-- The first position at which `n` occurs in `s`. -/
def firstAt (s n : List Char) : Option Nat := ((positions s).filter (occursAt n s)).head?

/-- `replaceFirst(S, N, R)`: S with its first occurrence of N replaced by R; S if N does not occur. -/
def replaceFirst (s n r : List Char) : List Char :=
  match firstAt s n with
  | some p => s.take p ++ r ++ s.drop (p + n.length)
  | none => s

/-- The first k occurrences of `n` replaced by `r`, left to right, none overlapping (after an
occurrence the search goes on behind it). -/
def replaceN (n r : List Char) : Nat → List Char → List Char
  | 0, s => s
  | k + 1, s => match firstAt s n with
    | some p => s.take p ++ r ++ replaceN n r k (s.drop (p + n.length))
    | none => s

/-- `replace(S, N, R, K)`: the first K occurrences replaced; none for K < 0. -/
def replace (s n r : List Char) (k : Int) : Option (List Char) :=
  if 0 ≤ k then some (replaceN n r k.toNat s) else none

/-- The occurrences of `n` in `s` counted left to right, the search going on behind each one (none
overlapping), at most `fuel` of them. -/
def countFrom (n : List Char) : Nat → List Char → Nat
  | 0, _ => 0
  | fuel + 1, s => match firstAt s n with
    | some p => 1 + countFrom n fuel (s.drop (p + n.length))
    | none => 0

/-- `countAllOccurrences(S, N)` at a non-empty N: 0 where N does not occur in S, and otherwise one
more than the count in what follows the first occurrence (domains.md STRING-COMMON's two equations,
1896-1899). Behind an occurrence of a non-empty N the rest is shorter than S, so S has at most
`length` of them. None at the empty N, where the second equation makes the count its own successor. -/
def countAll (s n : List Char) : Option Nat :=
  if n.isEmpty then none else some (countFrom n s.length s)

/-- `replaceAll(S, N, R)` at a non-empty N: `replace` at the count of N's occurrences in S
(domains.md STRING-COMMON's equation, 1917); none at the empty N. -/
def replaceAll (s n r : List Char) : Option (List Char) :=
  (countAll s n).map fun k => replaceN n r k s

/-- The lexicographic order of code-point sequences: `<String`. -/
def lexLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x.toNat < y.toNat) || (decide (x.toNat = y.toNat) && lexLt xs ys)

/-- `ordChar(S)`: the code point of a string of one code point; none at another length. -/
def ord : List Char → Option Nat
  | [ch] => some ch.toNat
  | _ => none

/-- A digit of radix `b`: `0`–`9`, then `a`–`z` or `A`–`Z` for 10–35, below b. -/
def digit (b : Nat) (ch : Char) : Option Nat :=
  let n := ch.toNat
  let d := if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
    else if 97 ≤ n ∧ n ≤ 122 then some (n - 87)
    else if 65 ≤ n ∧ n ≤ 90 then some (n - 55)
    else none
  d.bind fun d => if d < b then some d else none

/-- The value of a sequence of radix-b digits after the value `acc` of those before. -/
def digits (b : Nat) : List Char → Nat → Option Nat
  | [], acc => some acc
  | ch :: chs, acc => (digit b ch).bind fun d => digits b chs (b * acc + d)

/-- A non-empty sequence of radix-b digits, optionally after `+` or `-`, as an Int. -/
def toIntRadix (b : Nat) : List Char → Option Int
  | '-' :: ds => if ds.isEmpty then none else (digits b ds 0).map fun n => -(n : Int)
  | '+' :: ds => if ds.isEmpty then none else (digits b ds 0).map fun n => (n : Int)
  | ds => if ds.isEmpty then none else (digits b ds 0).map fun n => (n : Int)

/-- `String2Int(S)`: S in INT's syntax (`[+-]?[0-9]+`); none otherwise. -/
def toInt (s : List Char) : Option Int := toIntRadix 10 s

/-- `String2Base(S, B)`: S as an Int in radix B, letters of either case; none unless 2 ≤ B ≤ 36. -/
def toIntBase (s : List Char) (b : Int) : Option Int :=
  if 2 ≤ b ∧ b ≤ 36 then toIntRadix b.toNat s else none

/-- `String2Bool(S)`: true at `"true"`, false at `"false"`, none otherwise (STRING-COMMON's equations). -/
def toBool (s : List Char) : Option Bool :=
  if s = "true".toList then some true else if s = "false".toList then some false else none

theorem substr_mem {s r : List Char} {a b : Int} {ch : Char} (h : substr s a b = some r) (hc : ch ∈ r) :
    ch ∈ s := by
  unfold substr at h
  split at h
  · cases h; exact List.mem_of_mem_drop (List.mem_of_mem_take hc)
  · cases h

theorem substrString_mem {s r : List Char} {a b : Int} {ch : Char} (h : substrString s a b = some r)
    (hc : ch ∈ r) : ch ∈ s := by
  unfold substrString at h
  split at h
  · cases h
  · exact substr_mem h hc

theorem take_drop_mem {s r : List Char} {p q : Nat} {ch : Char} (hc : ch ∈ s.take p ++ r ++ s.drop q) :
    ch ∈ s ∨ ch ∈ r := by
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact Or.inl (List.mem_of_mem_take hc)
  · exact Or.inr hc
  · exact Or.inl (List.mem_of_mem_drop hc)

theorem replaceFirst_mem {s n r : List Char} {ch : Char} (hc : ch ∈ replaceFirst s n r) : ch ∈ s ∨ ch ∈ r := by
  unfold replaceFirst at hc
  split at hc
  · exact take_drop_mem hc
  · exact Or.inl hc

theorem replaceN_mem (n r : List Char) {ch : Char} : ∀ (k : Nat) (s : List Char), ch ∈ replaceN n r k s → ch ∈ s ∨ ch ∈ r
  | 0, s, hc => Or.inl hc
  | k + 1, s, hc => by
    unfold replaceN at hc
    split at hc
    · simp only [List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact Or.inl (List.mem_of_mem_take hc)
      · exact Or.inr hc
      · exact (replaceN_mem n r k _ hc).imp_left List.mem_of_mem_drop
    · exact Or.inl hc

theorem replace_mem {s n r x : List Char} {k : Int} {ch : Char} (h : replace s n r k = some x) (hc : ch ∈ x) :
    ch ∈ s ∨ ch ∈ r := by
  unfold replace at h
  split at h
  · cases h; exact replaceN_mem n r _ s hc
  · cases h

theorem replaceAll_mem {s n r x : List Char} {ch : Char} (h : replaceAll s n r = some x) (hc : ch ∈ x) :
    ch ∈ s ∨ ch ∈ r := by
  unfold replaceAll at h
  obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact replaceN_mem n r k s hc

/-- `chrChar(I)`: the string of the code point I; none unless I is a Unicode scalar value
(0 … 0x10FFFF, no surrogate 0xD800 … 0xDFFF), the code points a KORE string holds. -/
def chr (i : Int) : Option (List Char) :=
  if 0 ≤ i ∧ i < 0x110000 ∧ ¬(0xD800 ≤ i ∧ i < 0xE000) then some [Char.ofNat i.toNat] else none

end KStr

namespace KBytes

/-- The character of a byte. -/
def byte (v : Nat) : Char := Char.ofNat v

/-- `B[I]`: the byte at I; none unless 0 ≤ I < length. -/
def get (b : List Char) (i : Int) : Option Int :=
  if 0 ≤ i then (b[i.toNat]?).map fun ch => (ch.toNat : Int) else none

/-- `B[I <- V]`: B with the byte at I set to V; none unless 0 ≤ I < length and 0 ≤ V < 256. -/
def update (b : List Char) (i v : Int) : Option (List Char) :=
  if 0 ≤ i ∧ i < b.length ∧ 0 ≤ v ∧ v < 256 then some (b.set i.toNat (byte v.toNat)) else none

/-- `replaceAtBytes(D, I, S)`: D with the bytes I … I + |S| − 1 replaced by S; none unless 0 ≤ I and
I + |S| ≤ |D|, the ranges that are |S| elements of D (so a replacement may reach the last byte, where
I + |S| = |D|). -/
def replaceAt (d : List Char) (i : Int) (s : List Char) : Option (List Char) :=
  if 0 ≤ i ∧ i + s.length ≤ d.length then some (d.take i.toNat ++ s ++ d.drop (i.toNat + s.length)) else none

/-- `memsetBytes(D, I, N, V)`: D with the bytes I … I + N − 1 set to V's byte (`Int2Bytes(1, V, _)`, V
mod 256); none unless 0 ≤ I, 0 ≤ N, I + N ≤ |D| (the N bytes are bytes of D, the last one included
at I + N = |D|) and −128 ≤ V ≤ 127. -/
def memset (d : List Char) (i n v : Int) : Option (List Char) :=
  if 0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ d.length ∧ -128 ≤ v ∧ v ≤ 127 then
    some (d.take i.toNat ++ List.replicate n.toNat (byte (v % 256).toNat) ++ d.drop (i.toNat + n.toNat))
  else none

/-- `padRightBytes(B, L, V)`: B followed by bytes V up to length L; none unless 0 ≤ L and
0 ≤ V < 256. -/
def padRight (b : List Char) (l v : Int) : Option (List Char) :=
  if 0 ≤ l ∧ 0 ≤ v ∧ v < 256 then some (b ++ List.replicate (l.toNat - b.length) (byte v.toNat)) else none

/-- `padLeftBytes(B, L, V)`: as `padRight`, the bytes V before B. -/
def padLeft (b : List Char) (l v : Int) : Option (List Char) :=
  if 0 ≤ l ∧ 0 ≤ v ∧ v < 256 then some (List.replicate (l.toNat - b.length) (byte v.toNat) ++ b) else none

/-- The bytes, most significant first, as an unsigned number. -/
def unsignedBE (b : List Char) : Nat := b.foldl (fun acc ch => 256 * acc + ch.toNat) 0

/-- `Bytes2Int(B, E, S)`: B read in byte order E (`bigEndian`: most significant byte first), unsigned or
two's complement (`signed`: the top bit of the most significant byte gives −256^|B|); 0 for no byte. -/
def toInt (b : List Char) (bigEndian signed : Bool) : Int :=
  let be := if bigEndian then b else b.reverse
  match be with
  | [] => 0
  | ch :: _ => if signed && decide (128 ≤ ch.toNat) then (unsignedBE be : Int) - 256 ^ be.length else unsignedBE be

theorem byte_lt (v : Nat) (h : v < 256) : (byte v).toNat < 256 := by
  unfold byte Char.ofNat
  split
  · simp [Char.ofNatAux, Char.toNat]; omega
  · simp

theorem update_mem {b r : List Char} {i v : Int} {ch : Char} (h : update b i v = some r) (hc : ch ∈ r) :
    ch ∈ b ∨ ch.toNat < 256 := by
  unfold update at h
  split at h
  · rename_i hr
    cases h
    rcases List.mem_or_eq_of_mem_set hc with hc | rfl
    · exact Or.inl hc
    · exact Or.inr (byte_lt _ (by omega))
  · cases h

theorem replaceAt_mem {d s r : List Char} {i : Int} {ch : Char} (h : replaceAt d i s = some r) (hc : ch ∈ r) :
    ch ∈ d ∨ ch ∈ s := by
  unfold replaceAt at h
  split at h
  · cases h; exact KStr.take_drop_mem hc
  · cases h

theorem memset_mem {d r : List Char} {i n v : Int} {ch : Char} (h : memset d i n v = some r) (hc : ch ∈ r) :
    ch ∈ d ∨ ch.toNat < 256 := by
  unfold memset at h
  split at h
  · cases h
    rcases KStr.take_drop_mem hc with hc | hc
    · exact Or.inl hc
    · rw [List.eq_of_mem_replicate hc]
      have h1 := Int.emod_lt_of_pos v (by decide : (0 : Int) < 256)
      have h0 := Int.emod_nonneg v (by decide : (256 : Int) ≠ 0)
      exact Or.inr (byte_lt _ (by omega))
  · cases h

theorem padRight_mem {b r : List Char} {l v : Int} {ch : Char} (h : padRight b l v = some r) (hc : ch ∈ r) :
    ch ∈ b ∨ ch.toNat < 256 := by
  unfold padRight at h
  split at h
  · cases h
    rcases List.mem_append.mp hc with hc | hc
    · exact Or.inl hc
    · rw [List.eq_of_mem_replicate hc]; exact Or.inr (byte_lt _ (by omega))
  · cases h

theorem padLeft_mem {b r : List Char} {l v : Int} {ch : Char} (h : padLeft b l v = some r) (hc : ch ∈ r) :
    ch ∈ b ∨ ch.toNat < 256 := by
  unfold padLeft at h
  split at h
  · cases h
    rcases List.mem_append.mp hc with hc | hc
    · rw [List.eq_of_mem_replicate hc]; exact Or.inr (byte_lt _ (by omega))
    · exact Or.inl hc
  · cases h

/-- `Int2Bytes(L, V, E)`: the L bytes of V modulo 256^L (two's complement, truncated to its low
bytes), most significant first for `BE` (`bigEndian`), least for `LE`; none for L < 0. -/
def ofInt (l v : Int) (bigEndian : Bool) : Option (List Char) :=
  if l < 0 then none
  else
    let u := (v % (256 ^ l.toNat : Nat)).toNat
    let be := (List.range l.toNat).reverse.map fun i => byte (u / 256 ^ i % 256)
    some (if bigEndian then be else be.reverse)

theorem ofInt_lt {l v : Int} {be : Bool} {r : List Char} (h : ofInt l v be = some r) :
    ∀ ch ∈ r, ch.toNat < 256 := by
  intro ch hc
  unfold ofInt at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    have key : ∀ (u n : Nat) (ch : Char), ch ∈ (List.range n).reverse.map (fun i => byte (u / 256 ^ i % 256)) →
        ch.toNat < 256 := by
      intro u n ch hc
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
      exact byte_lt _ (Nat.mod_lt _ (by decide))
    split at hc
    · exact key _ _ ch hc
    · exact key _ _ ch (List.mem_reverse.mp hc)

end KBytes

end KCore
