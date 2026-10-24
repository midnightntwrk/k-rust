import KPrelude.Coll
import KPrelude.Hooks
import KPrelude.Rules

/-!
# Hooks and matching beyond kimp

* `MapHook.choose`: the matches of a map pattern `K |-> V REST` whose key is not bound by the
  rest of the left-hand side (a free key: K's cell collections, `<thread>... </thread>`). Each
  binding of the map is one match; the continuation receives the proof that the map is
  `K |-> V` joined with `remove m K`, which is how a matcher certifies its relation hypothesis.
* `SetHook`: K's `Set` as a map to `Unit` (`SetItem(K)` is `K |-> ()`): `_Set_` is the same
  partial disjoint union as `_Map_` (`domains.md`: "the concatenation of two sets containing
  elements in common is `#False`").
* `ListHook`: K's `List` (associative, unit `.List`, `ListItem`), over a carrier isomorphic to
  `List E`.
* `StringHook`, `IntHook` bit operations, `IOHook`.
* `pick`: the result a rule with several matches gives to `step`.
-/

set_option linter.unusedSectionVars false

namespace KPrelude

/-! ## Free-key map patterns -/

namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
variable [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem lookup_of_mem_toList {m : M} (hw : WF m) {k : K} {v : V} (h : (k, v) ∈ toList m) :
    lookup m k = some v := by
  rw [lookup_def]; exact SAL.lookup_of_mem hw h

/-- Every binding `k |-> v` of a well-formed map, each with the certificate that `m` is
`k |-> v` joined with `remove m k` (the match of `K |-> V REST` with `REST = remove m k`). -/
def choose {β : Type} (m : M) (hw : WF m)
    (f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → List β) : List β :=
  (toList m).attach.flatMap fun p =>
    f p.1.1 p.1.2 (concat_element_remove hw (lookup_of_mem_toList hw p.2))

/-- Completeness of `choose`: every match `k |-> v r` of `m` is visited. -/
theorem exists_mem_choose {β : Type} {m : M} {hw : WF m}
    {f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → List β}
    {k : K} {v : V} {r : M} (h : concat (element k v) r = some m) {P : β → Prop}
    (hx : ∀ hc, ∃ x ∈ f k v hc, P x) : ∃ x ∈ choose m hw f, P x := by
  have hl := lookup_of_concat_element h
  rw [lookup_def] at hl
  have hmem := SAL.lookup_mem hl
  obtain ⟨x, hx1, hx2⟩ := hx (concat_element_remove hw (lookup_of_mem_toList hw hmem))
  refine ⟨x, ?_, hx2⟩
  simp only [choose, List.mem_flatMap]
  exact ⟨⟨(k, v), hmem⟩, List.mem_attach _ _, hx1⟩

/-- `exists_mem_choose` for a match found in a map equal to the enumerated one (the rest of an
earlier match). -/
theorem exists_mem_choose' {β : Type} {m m' : M} {hw : WF m}
    {f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → List β}
    {k : K} {v : V} {r : M} (h : concat (element k v) r = some m') (he : m' = m) {P : β → Prop}
    (hx : ∀ hc, ∃ x ∈ f k v hc, P x) : ∃ x ∈ choose m hw f, P x := by
  subst he; exact exists_mem_choose h hx

/-- Membership form of `exists_mem_choose`. -/
theorem mem_choose {β : Type} {m : M} {hw : WF m}
    {f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → List β}
    {k : K} {v : V} {r : M} (h : concat (element k v) r = some m) {x : β}
    (hx : ∀ hc, x ∈ f k v hc) : x ∈ choose m hw f := by
  obtain ⟨y, hy, rfl⟩ := exists_mem_choose (P := fun y => y = x) h (fun hc => ⟨x, hx hc, rfl⟩)
  exact hy

/-- The first binding of a well-formed map, in the map's order, at which `f` has a value, and
that value: how a function equation with a free-key map pattern `K |-> V REST` is evaluated
(`docs/design.md`, §2, "Functions"). `f` is `none` at a binding where the rest of the
equation's left-hand side or its requires fails. -/
def chooseFirst {β : Type} (m : M) (hw : WF m)
    (f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → Option β) : Option β :=
  (toList m).attach.findSome? fun p =>
    f p.1.1 p.1.2 (concat_element_remove hw (lookup_of_mem_toList hw p.2))

/-- A value of `chooseFirst` is the value of `f` at some binding of `m`. -/
theorem chooseFirst_eq_some {β : Type} {m : M} {hw : WF m}
    {f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → Option β} {b : β}
    (h : chooseFirst m hw f = some b) : ∃ k v hc, f k v hc = some b := by
  unfold chooseFirst at h
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨_, _, _, hp⟩

/-- `chooseFirst` has no value exactly when `f` has none at any match `k |-> v (remove m k)`. -/
theorem chooseFirst_eq_none {β : Type} {m : M} {hw : WF m}
    {f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → Option β} :
    chooseFirst m hw f = none ↔ ∀ k v hc, f k v hc = none := by
  unfold chooseFirst
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro h k v hc
    have hl := lookup_of_concat_element hc
    rw [lookup_def] at hl
    exact h ⟨(k, v), SAL.lookup_mem hl⟩ (List.mem_attach _ _)
  · intro h p _
    exact h _ _ _

/-- When `f` has a value at some binding and every value it has at any binding is `b`, the value
is `b`: a function equation with a free key, whose matches all give one value, gives that value
whichever binding comes first. -/
theorem chooseFirst_eq_of_agree {β : Type} {m : M} {hw : WF m}
    {f : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → Option β} {b : β}
    (hex : ∃ k v hc, f k v hc = some b) (hall : ∀ k v hc b', f k v hc = some b' → b' = b) :
    chooseFirst m hw f = some b := by
  cases h : chooseFirst m hw f with
  | none =>
    obtain ⟨k, v, hc, hb⟩ := hex
    rw [chooseFirst_eq_none.1 h k v hc] at hb
    exact absurd hb (by simp)
  | some b' =>
    obtain ⟨k, v, hc, hb⟩ := chooseFirst_eq_some h
    rw [hall k v hc b' hb]

end MapHook

/-! ## More `MAP` hooks -/

namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]

/-- `M -Map N`: the bindings of `M` whose key is not bound to the same value in `N`. -/
def difference [DecidableEq V] (a b : M) : M :=
  ofList ((toList a).filter fun p => lookup b p.1 != some p.2)
/-- `updateMap(M, N)`: `M` updated with every binding of `N`. -/
def updateAll (a b : M) : M := (toList b).foldl (fun m p => update m p.1 p.2) a
/-- `M <=Map N` -/
def inclusion [DecidableEq V] (a b : M) : Bool := (toList a).all fun p => lookup b p.1 == some p.2
/-- `choice(M)`: some key (the least one); undefined on `.Map`. -/
def choice (m : M) : Option K := ((toList m).head?).map (·.1)
/-- `keys_list(M)` -/
def keysList {L : Type} [ListIso L K] (m : M) : L := ofList ((toList m).map (·.1))
/-- `values(M)` -/
def values {L : Type} [ListIso L V] (m : M) : L := ofList ((toList m).map (·.2))
/-- `keys(M)`: a set (a map to `Unit`). -/
def keys {S : Type} [ListIso S (K × Unit)] (m : M) : S := ofList ((toList m).map fun p => (p.1, ()))
/-- `removeAll(M, S)` -/
def removeAll {S : Type} [ListIso S (K × Unit)] (m : M) (s : S) : M :=
  (toList s).foldl (fun m p => remove m p.1) m

end MapHook

/-! ## `SET` hooks: a set is a map to `Unit` -/

namespace SetHook

open ListIso

variable {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]

/-- `.Set` -/
def unit : S := MapHook.unit
/-- `SetItem(K)` -/
def element (k : K) : S := MapHook.element k ()
/-- `S₁ S₂` (partial: undefined on a common element) -/
def concat (a b : S) : Option S := MapHook.concat a b
/-- `K in S` -/
def inSet (k : K) (s : S) : Bool := MapHook.inKeys k s
/-- `S₁ -Set S₂` -/
def difference (a b : S) : S := ofList ((toList a).filter fun p => !(MapHook.inKeys p.1 b))
/-- `S₁ |Set S₂` -/
def union (a b : S) : S := (toList b).foldl (fun s p => MapHook.update s p.1 ()) a
/-- `intersectSet(S₁, S₂)` -/
def intersection (a b : S) : S := ofList ((toList a).filter fun p => MapHook.inKeys p.1 b)
/-- `S₁ <=Set S₂` -/
def inclusion (a b : S) : Bool := (toList a).all fun p => MapHook.inKeys p.1 b
/-- `size(S)` -/
def size (s : S) : Int := (toList s).length
/-- `choice(S)` (undefined on `.Set`) -/
def choice (s : S) : Option K := ((toList s).head?).map (·.1)
/-- `List2Set(L)` -/
def ofListHook {L : Type} [ListIso L K] (l : L) : S := (toList l).foldl (fun s k => MapHook.update s k ()) unit
/-- `Set2List(S)` -/
def toListHook {L : Type} [ListIso L K] (s : S) : L := ofList ((toList s).map (·.1))
/-- A set literal (concrete terms). -/
def ofElems (l : List K) : S := l.foldl (fun s k => MapHook.update s k ()) unit

end SetHook

/-! ## `LIST` hooks -/

namespace ListHook

open ListIso

variable {L E : Type} [ListIso L E]

/-- `.List` -/
def unit : L := ofList []
/-- `ListItem(E)` -/
def element (x : E) : L := ofList [x]
/-- `L₁ L₂` (total) -/
def concat (a b : L) : L := ofList (toList a ++ toList b)
/-- `pushList(E, L)` -/
def push (x : E) (l : L) : L := ofList (x :: toList l)
/-- `size(L)` -/
def size (l : L) : Int := (toList l).length
/-- `L[I]`: a negative index counts from the end; undefined out of range. -/
def get (l : L) (i : Int) : Option E :=
  let xs := toList l
  if 0 ≤ i then xs[i.toNat]? else if 0 ≤ xs.length + i then xs[(xs.length + i).toNat]? else none
/-- `L[I <- V]` (undefined out of range) -/
def update (l : L) (i : Int) (v : E) : Option L :=
  let xs := toList l
  if 0 ≤ i ∧ i < xs.length then some (ofList (xs.set i.toNat v)) else none
/-- `makeList(N, V)` (undefined for `N < 0`) -/
def make (n : Int) (v : E) : Option L := if 0 ≤ n then some (ofList (List.replicate n.toNat v)) else none
/-- `range(L, A, B)`: drop `A` elements at the front and `B` at the back (undefined if too many). -/
def range (l : L) (a b : Int) : Option L :=
  let xs := toList l
  if 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ xs.length then some (ofList ((xs.drop a.toNat).take (xs.length - a.toNat - b.toNat)))
  else none
/-- `E in L` -/
def inList [DecidableEq E] (x : E) (l : L) : Bool := (toList l).contains x
/-- A list literal (concrete terms). -/
def ofElems (l : List E) : L := ofList l

/-- The first element and the rest (for the pattern `ListItem(X) REST`). -/
def uncons (l : L) : Option (E × L) :=
  match toList l with
  | [] => none
  | x :: t => some (x, ofList t)

/-- The last element and the front (for the pattern `REST ListItem(X)`). -/
def unsnoc (l : L) : Option (L × E) :=
  match (toList l).getLast? with
  | none => none
  | some x => some (ofList (toList l).dropLast, x)

theorem concat_element_of_uncons {l t : L} {x : E} (h : uncons l = some (x, t)) : concat (element x) t = l := by
  unfold uncons at h
  split at h
  · simp at h
  · next y ys hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold concat element
    rw [toList_ofList, toList_ofList, List.singleton_append, ← hl, ofList_toList]

theorem uncons_concat_element (x : E) (t : L) : uncons (concat (element x) t) = some (x, t) := by
  unfold uncons concat element
  rw [toList_ofList, toList_ofList, List.singleton_append]
  simp [ofList_toList]

theorem concat_element_of_unsnoc {l t : L} {x : E} (h : unsnoc l = some (t, x)) : concat t (element x) = l := by
  unfold unsnoc at h
  split at h
  · simp at h
  · next y hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold concat element
    rw [toList_ofList, toList_ofList]
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hl
    rw [hys, List.dropLast_concat, ← hys, ofList_toList]

theorem unsnoc_concat_element (t : L) (x : E) : unsnoc (concat t (element x)) = some (t, x) := by
  unfold unsnoc concat element
  rw [toList_ofList, toList_ofList]
  simp [ofList_toList]

end ListHook

/-! ## `STRING` hooks

Lean's `String` is a sequence of Unicode code points, as K's `String` is; indices count code
points. `substrString` is declared `total` in `domains.md` but documented only on valid indices
(`0 ≤ start ≤ end ≤ length`); `total` makes it defined everywhere with an unspecified value off
that range, and this model takes the range clamped to the string (a choice, not K's).
-/

namespace StringHook

def concat (a b : String) : String := a ++ b
def length (s : String) : Int := s.length
def substr (s : String) (i j : Int) : String :=
  let n := s.length
  let i' := (max i 0).toNat
  let j' := (min (max j 0) n).toNat
  if i' ≤ j' then String.ofList ((s.toList.drop i').take (j' - i')) else ""
/-- The first index `≥ i` at which `needle` occurs, or `-1`; undefined for a negative `i`. -/
def find (h n : String) (i : Int) : Option Int :=
  if i < 0 then none else
  let hs := h.toList
  let ns := n.toList
  let rec go : Nat → List Char → Option Int
    | _, [] => if ns.isEmpty then some hs.length else some (-1)
    | k, c :: t => if ns.isPrefixOf (c :: t) then some k else go (k + 1) t
  if i.toNat > hs.length then some (-1) else go i.toNat (hs.drop i.toNat)
/-- The last index `≤ i` at which `needle` occurs, or `-1`. -/
def rfind (h n : String) (i : Int) : Option Int :=
  if i < 0 then none else
  let hs := h.toList
  let ns := n.toList
  let cands := (List.range (min i.toNat hs.length + 1)).reverse
  some ((cands.find? fun k => ns.isPrefixOf (hs.drop k)).map (fun k => (k : Int)) |>.getD (-1))
/-- The first index `≥ i` holding one of the characters of `cs`, or `-1`.
With an empty `cs` the result is `-1` at every index, negative ones included: that is the
equation `findChar(_, "", _) => -1` of `domains.md`, and a model satisfies every equation of the
definition. With a non-empty `cs` it is undefined at a negative `i`: there the definition's other
equation reduces `findChar` to `findString`, which `domains.md` leaves unspecified at a negative
index (`find` is undefined there). -/
def findChar (h cs : String) (i : Int) : Option Int :=
  if cs.isEmpty then some (-1) else
  if i < 0 then none else
  let hs := h.toList
  let rec go : Nat → List Char → Int
    | _, [] => -1
    | k, c :: t => if cs.toList.contains c then k else go (k + 1) t
  some (go i.toNat (hs.drop i.toNat))
/-- The last index `≤ i` holding one of the characters of `cs`, or `-1`.
As for `findChar`: `-1` for an empty `cs` at every index (`rfindChar(_, "", _) => -1`), and
undefined for a non-empty `cs` at a negative `i`, where the definition's other equation reduces
`rfindChar` to `rfindString`, unspecified at a negative index (`rfind` is undefined there). -/
def rfindChar (h cs : String) (i : Int) : Option Int :=
  if cs.isEmpty then some (-1) else
  if i < 0 then none else
  let hs := h.toList
  let cands := (List.range (min i.toNat hs.length + 1)).reverse
  some ((cands.find? fun k => match hs[k]? with | some c => cs.toList.contains c | none => false).map
    (fun k => (k : Int)) |>.getD (-1))
/-- `chrChar(N)`: the one-code-point string; undefined outside the Unicode scalar values. -/
def chr (n : Int) : Option String :=
  if 0 ≤ n ∧ n < 0x110000 then
    let c := Char.ofNat n.toNat
    if c.toNat = n.toNat then some (String.singleton c) else none
  else none
/-- `ordChar(S)`: the code point of a one-character string. -/
def ord (s : String) : Option Int :=
  match s.toList with
  | [c] => some c.toNat
  | _ => none
/-- `String2Int`: an optional sign and a nonempty sequence of decimal digits. -/
def toInt (s : String) : Option Int :=
  let digits (l : List Char) : Option Nat :=
    if l.isEmpty || !l.all Char.isDigit then none
    else some (l.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  match s.toList with
  | '-' :: t => (digits t).map fun n => -(n : Int)
  | '+' :: t => (digits t).map fun n => (n : Int)
  | l => (digits l).map fun n => (n : Int)
def ofInt (i : Int) : String := toString i
/-- `Int2String` in a radix `2 ≤ b ≤ 36` (lower-case letters). -/
def base2string (i : Int) (b : Int) : Option String :=
  if 2 ≤ b ∧ b ≤ 36 then
    let digs := Nat.toDigits b.toNat i.natAbs
    some ((if i < 0 then "-" else "") ++ String.ofList digs)
  else none
def string2base (s : String) (b : Int) : Option Int :=
  if 2 ≤ b ∧ b ≤ 36 then
    let val (c : Char) : Option Nat :=
      if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat + 10)
      else none
    let digits (l : List Char) : Option Nat :=
      if l.isEmpty then none else
      l.foldlM (fun n c => (val c).bind fun d => if d < b.toNat then some (b.toNat * n + d) else none) 0
    match s.toList with
    | '-' :: t => (digits t).map fun n => -(n : Int)
    | '+' :: t => (digits t).map fun n => (n : Int)
    | l => (digits l).map fun n => (n : Int)
  else none
/-- Every occurrence of the nonempty `n` in `h`, scanned from the left and not overlapping, replaced
by `r` (`fuel` bounds the scan: each step consumes at least one character of `h`). -/
def replaceAllChars : Nat → List Char → List Char → List Char → List Char
  | 0, h, _, _ => h
  | _ + 1, [], _, _ => []
  | fuel + 1, c :: cs, n, r =>
    if (c :: cs).take n.length = n then r ++ replaceAllChars fuel ((c :: cs).drop n.length) n r
    else c :: replaceAllChars fuel cs n r
/-- `replaceAll`, by structural recursion on the characters: the kernel evaluates it, so a proof
can compute its value at literals (`String.replace` is a loop the kernel does not unfold).
Irreducible for the elaborator, which the kernel ignores: at a string that is not a literal,
unification would otherwise unfold the scan until it is stuck on the string, for every hypothesis
that mentions the call (a `cases` on `K.parseByteStack DATA = some r` cost 67 million heartbeats
on KEVM, and 0.2 million with it irreducible). -/
@[irreducible] def replaceAll (h n r : String) : String :=
  if n.isEmpty then h else String.ofList (replaceAllChars h.length h.toList n.toList r.toList)
def replaceFirst (h n r : String) : String :=
  if n.isEmpty then h else
  match (find h n 0) with
  | some k => if k < 0 then h else
      String.ofList ((h.toList.take k.toNat) ++ r.toList ++ (h.toList.drop (k.toNat + n.length)))
  | none => h
/-- The number of occurrences of the nonempty `n` in `h`, scanned from the left and not
overlapping (`fuel` bounds the scan as in `replaceAllChars`). -/
def countChars : Nat → List Char → List Char → Nat
  | 0, _, _ => 0
  | _ + 1, [], _ => 0
  | fuel + 1, c :: cs, n =>
    if (c :: cs).take n.length = n then countChars fuel ((c :: cs).drop n.length) n + 1
    else countChars fuel cs n
/-- `countAllOccurrences`: K's equations count the first occurrence and continue after it. By
structural recursion on the characters, so the kernel evaluates it at literals
(`String.splitOn` is a loop over string positions that the kernel does not unfold).
Irreducible for the elaborator, as `replaceAll` is. -/
@[irreducible] def countAllOccurrences (h n : String) : Int :=
  if n.isEmpty then 0 else countChars h.length h.toList n.toList
def eq (a b : String) : Bool := a == b
def ne (a b : String) : Bool := a != b
def lt (a b : String) : Bool := decide (a < b)
def le (a b : String) : Bool := decide (a ≤ b)
def gt (a b : String) : Bool := decide (b < a)
def ge (a b : String) : Bool := decide (b ≤ a)

end StringHook

/-! ## `INT` bit operations (two's complement on unbounded integers) -/

namespace IntHook

/-- `x` as (sign, magnitude bits): `ofNat n` is `n`, `negSucc n` is the complement of `n`. -/
def land : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a - (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b - (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)
def lor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b - (a &&& b))
  | .negSucc a, .ofNat b => .negSucc (a - (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)
def lxor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)
def lnot (a : Int) : Int := -a - 1
/-- `log2Int(N)`: the index of the highest set bit; undefined for `N ≤ 0`. -/
def log2 (a : Int) : Option Int := if 0 < a then some (Nat.log2 a.toNat) else none
/-- `bitRangeInt(I, IDX, LEN)`: bits `IDX .. IDX+LEN-1` of `I`; undefined for negative `IDX`/`LEN`. -/
def bitRange (i idx len : Int) : Option Int :=
  if 0 ≤ idx ∧ 0 ≤ len then some ((i >>> idx.toNat) % (2 ^ len.toNat)) else none
/-- `signExtendBitRangeInt(I, IDX, LEN)`: that range read as a two's-complement number;
undefined for `LEN ≤ 0` (`domains.md` defines it through `1 <<Int (LEN -Int 1)`). -/
def signExtendBitRange (i idx len : Int) : Option Int :=
  if 0 ≤ idx ∧ 0 < len then
    let r := (i >>> idx.toNat) % (2 ^ len.toNat)
    some (if r ≥ 2 ^ (len.toNat - 1) then r - 2 ^ len.toNat else r)
  else none
/-- `(I1 ^Int I2) modInt I3`; undefined for a negative exponent or a zero modulus. -/
def powmod (a b m : Int) : Option Int := if b < 0 ∨ m = 0 then none else some ((a ^ b.toNat).emod m)

end IntHook

/-! ## Impure `IO` and `KREFLECTION` hooks

They read or change the world outside the configuration, which a closed model of the rewrite
theory does not contain: here they are undefined (`none`), so a rule that calls one applies but
has no successor (`step` reports `undefined`). With `$IO = "off"` (`krun --io off`) the stream
rules that call them never apply: input comes from the `$STDIN` buffer and output stays in the
`<output>` cell. -/

namespace IOHook

def undef0 {β : Type} : Option β := none
def undef1 {α β : Type} (_ : α) : Option β := none
def undef2 {α₁ α₂ β : Type} (_ : α₁) (_ : α₂) : Option β := none
def undef3 {α₁ α₂ α₃ β : Type} (_ : α₁) (_ : α₂) (_ : α₃) : Option β := none
def undef4 {α₁ α₂ α₃ α₄ β : Type} (_ : α₁) (_ : α₂) (_ : α₃) (_ : α₄) : Option β := none

end IOHook

/-! ## Rules with several matches -/

variable {α : Type} {A : α → Prop} {R : α → α → Prop} {c : α}

/-- The result of a rule with several matches as `step` uses it (k-rust `--strategy any`): the
first match whose right-hand side is defined; `undefined` if matches exist but none is defined. -/
def pick : List (RuleResult A R c) → RuleResult A R c
  | [] => .none
  | .next c' h :: _ => .next c' h
  | .undefined h :: rs =>
    match pick rs with
    | .next c' h' => .next c' h'
    | _ => .undefined h
  | .none :: rs => pick rs

theorem pick_applies : ∀ (l : List (RuleResult A R c)), (pick l).applies = l.any RuleResult.applies
  | [] => rfl
  | .next _ _ :: _ => rfl
  | .undefined _ :: rs => by
    simp only [pick, List.any_cons, RuleResult.applies_undefined, Bool.true_or]
    split <;> rfl
  | .none :: rs => by simp only [pick, List.any_cons, RuleResult.applies_none, Bool.false_or]; exact pick_applies rs

theorem pick_next_of_mem : ∀ (l : List (RuleResult A R c)) (r : RuleResult A R c) (c' : α),
    r ∈ l → r.next? = some c' → ∃ c'', (pick l).next? = some c''
  | [], _, _, h, _ => by simp at h
  | .next c₀ _ :: _, _, _, _, _ => ⟨c₀, rfl⟩
  | .undefined _ :: rs, r, c', hm, hr => by
    rcases List.mem_cons.1 hm with rfl | hm
    · simp at hr
    · obtain ⟨c'', h''⟩ := pick_next_of_mem rs r c' hm hr
      simp only [pick]
      split
      · next c₁ _ _ => exact ⟨c₁, rfl⟩
      · next hne => exact absurd h'' (by
          intro e; cases hp : pick rs with
          | next c₁ h₁ => exact hne c₁ h₁ hp
          | none => rw [hp] at e; simp at e
          | undefined => rw [hp] at e; simp at e)
  | .none :: rs, r, c', hm, hr => by
    rcases List.mem_cons.1 hm with rfl | hm
    · simp at hr
    · simpa only [pick] using pick_next_of_mem rs r c' hm hr

theorem pick_next_none : ∀ (l : List (RuleResult A R c)), (pick l).next? = Option.none →
    ∀ r ∈ l, r.next? = Option.none := by
  intro l h r hm
  cases e : r.next? with
  | none => rfl
  | some c' =>
    obtain ⟨c'', h''⟩ := pick_next_of_mem l r c' hm e
    rw [h] at h''; exact absurd h'' (by simp)

/-- The successors a list of match results names. -/
def nexts (l : List (RuleResult A R c)) : List α := l.filterMap RuleResult.next?

theorem mem_nexts {l : List (RuleResult A R c)} {c' : α} : c' ∈ nexts l ↔ ∃ r ∈ l, r.next? = some c' := by
  simp [nexts]

theorem sound_of_mem_nexts {l : List (RuleResult A R c)} {c' : α} (h : c' ∈ nexts l) : R c c' := by
  obtain ⟨r, _, hr⟩ := mem_nexts.1 h
  exact RuleResult.sound_of_next? hr

theorem exists_applies_of_next {l : List (RuleResult A R c)} (h : ∃ r ∈ l, ∃ c', r.next? = some c') :
    ∃ r ∈ l, r.applies = true := by
  obtain ⟨r, hm, c', hr⟩ := h
  exact ⟨r, hm, RuleResult.applies_of_next? hr⟩

/-- `o` is `.stuck` (no rule of a rank applies). -/
def isStuck {β : Type} : Outcome β → Bool
  | .stuck => true
  | _ => false

theorem isStuck_iff {β : Type} {o : Outcome β} : isStuck o = true ↔ o = .stuck := by
  cases o <;> simp [isStuck]

/-- All elements equal (at most one distinct successor). -/
def allEq {β : Type} [DecidableEq β] : List β → Bool
  | [] => true
  | x :: t => t.all (· = x)

theorem allEq_spec {β : Type} [DecidableEq β] {l : List β} (h : allEq l = true) :
    ∀ a ∈ l, ∀ b ∈ l, a = b := by
  cases l with
  | nil => simp
  | cons x t =>
    simp only [allEq, List.all_eq_true, decide_eq_true_eq] at h
    intro a ha b hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (h b hb).symm
    · exact h a ha
    · exact (h a ha).trans (h b hb).symm

theorem pick_applies_of_exists {l : List (RuleResult A R c)} (h : ∃ r ∈ l, r.applies = true) :
    (pick l).applies = true := by
  rw [pick_applies, List.any_eq_true]; exact h

end KPrelude

/-! ## `BYTES`: byte sequences as `List UInt8`

The carrier is a list (proofs by list induction); its serialization is one string token whose
characters are the bytes, and `ofString` reads a KORE `Bytes` domain value (one character per
byte). The endianness and signedness arguments of `Bytes2Int`/`Int2Bytes` are generated
constructors, unknown to this library: `bytes2int` and `int2bytes` take them as `Bool` flags, and
the generated library compares its arguments with the constructors `domains.md` declares. -/

namespace KPrelude.BytesHook

def ofString (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8
def toStr (b : List UInt8) : String := String.ofList (b.map fun x => Char.ofNat x.toNat)
def ser (b : List UInt8) : List Tok := [.s (toStr b)]
def dec : Nat → List Tok → Option (List UInt8 × List Tok)
  | _, .s s :: t => some (ofString s, t)
  | _, _ => none

theorem byte_rt (x : UInt8) : (Char.ofNat x.toNat).toNat.toUInt8 = x := by
  have h : x.toNat < 256 := x.toNat_lt
  have hv : x.toNat.isValidChar := Or.inl (by omega)
  simp only [Char.ofNat, dite_eq_left hv, Char.ofNatAux, Char.toNat]
  apply UInt8.toNat_inj.1
  simp [Nat.toUInt8, UInt32.toNat]

theorem ofString_toStr (a : List UInt8) : ofString (toStr a) = a := by
  unfold ofString toStr
  induction a with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, String.toList_ofList] at *; rw [byte_rt, ih]

theorem dec_ser (a : List UInt8) (r : List Tok) (n : Nat) (_ : (ser a).length ≤ n) :
    dec n (ser a ++ r) = some (a, r) := by
  simp [ser, dec, ofString_toStr]

/-- The unsigned value of little-endian bytes. -/
def toNatLE : List UInt8 → Nat
  | [] => 0
  | b :: t => b.toNat + 256 * toNatLE t
/-- `Bytes2Int(B, E, S)` (`domains.md`): `B` read in byte order `E` (`big` for big-endian), as an
unsigned number or as two's complement (`signed`); the empty sequence is `0`. -/
def bytes2int (b : List UInt8) (big signed : Bool) : Int :=
  let n := toNatLE (if big then b.reverse else b)
  if signed && decide (0 < b.length) && decide (2 ^ (8 * b.length - 1) ≤ n) then (n : Int) - 2 ^ (8 * b.length) else n
/-- `k` little-endian bytes of `i` modulo `256^k` (two's complement truncation). -/
def int2bytesLE : Nat → Int → List UInt8
  | 0, _ => []
  | k + 1, i => (Int.emod i 256).toNat.toUInt8 :: int2bytesLE k (Int.ediv i 256)
/-- `Int2Bytes(LEN, I, E)` (`domains.md`): `LEN` bytes of `I` in two's complement, truncated or
sign-extended, in byte order `E`. `domains.md` does not say what a negative `LEN` gives; the
model returns the empty sequence (a model choice, like `substrString`'s clamping). -/
def int2bytes (len i : Int) (big : Bool) : List UInt8 :=
  let l := int2bytesLE len.toNat i
  if big then l.reverse else l

def empty : List UInt8 := []
def concat (a b : List UInt8) : List UInt8 := a ++ b
def length (b : List UInt8) : Int := b.length
def reverse (b : List UInt8) : List UInt8 := b.reverse
/-- `substrBytes(B, I, J)`: undefined unless `0 ≤ I ≤ J ≤ length`. -/
def substr (b : List UInt8) (i j : Int) : Option (List UInt8) :=
  if 0 ≤ i ∧ i ≤ j ∧ j ≤ b.length then some ((b.drop i.toNat).take (j - i).toNat) else none
/-- `B[I]`: undefined out of range. -/
def get (b : List UInt8) (i : Int) : Option Int :=
  if 0 ≤ i then (b[i.toNat]?).map fun x => (x.toNat : Int) else none
/-- `B[I <- V]`: undefined out of range or for a value outside `0 ≤ V < 256`. -/
def update (b : List UInt8) (i v : Int) : Option (List UInt8) :=
  if 0 ≤ i ∧ i < b.length ∧ 0 ≤ v ∧ v < 256 then some (b.set i.toNat v.toNat.toUInt8) else none
/-- `replaceAtBytes(B, I, B')`: undefined unless the replacement fits. -/
def replaceAt (b : List UInt8) (i : Int) (r : List UInt8) : Option (List UInt8) :=
  if 0 ≤ i ∧ i + r.length ≤ b.length then some (b.take i.toNat ++ r ++ b.drop (i.toNat + r.length)) else none
/-- `padRightBytes(B, L, V)` / `padLeftBytes(B, L, V)` -/
def padRight (b : List UInt8) (l v : Int) : Option (List UInt8) :=
  if 0 ≤ v ∧ v < 256 then some (b ++ List.replicate (l.toNat - b.length) v.toNat.toUInt8) else none
def padLeft (b : List UInt8) (l v : Int) : Option (List UInt8) :=
  if 0 ≤ v ∧ v < 256 then some (List.replicate (l.toNat - b.length) v.toNat.toUInt8 ++ b) else none
/-- `memsetBytes(B, I, N, V)` -/
def memset (b : List UInt8) (i n v : Int) : Option (List UInt8) :=
  if 0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ b.length ∧ 0 ≤ v ∧ v < 256 then
    some (b.take i.toNat ++ List.replicate n.toNat v.toNat.toUInt8 ++ b.drop (i + n).toNat)
  else none
def toStringHook (b : List UInt8) : String := toStr b
def ofStringHook (s : String) : Option (List UInt8) :=
  if s.toList.all (fun c => c.toNat < 256) then some (ofString s) else none

end KPrelude.BytesHook
