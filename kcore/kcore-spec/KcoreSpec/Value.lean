/-
  KCore. Ground values of a definition (KCORE-SPEC.md §5). Frozen layer.

  A value is canonical, so equal values are equal terms:
  - `GroundTerm.map s es` and `GroundTerm.set s es`: finite maps and sets of the collection sort
    s, their keys or elements strictly increasing in `GroundTerm.cmp`. `keys(M)` and `X in S`
    read them (IMP's declaration rule: `requires notBool (X in keys(Rho))`).
  - `GroundTerm.list s es`: finite lists of the collection sort s; a list is its elements in
    order, so it is canonical as it is.
  - Domain values, including the library's token sorts (`Id`, `String` under `domains`): every
    literal is canonical, and distinct literals denote distinct elements (a token's value is its
    text, a Float's its format and encoding, `KFloat.ok`).
  This file defines their order (`cmp`) and their sorts (`sortOf`).
-/
import KcoreSpec.Core
import KcoreSpec.FloatDomain

set_option autoImplicit false

namespace KCore

/- `GroundTerm` is declared in Core.lean, before `Semantics`, whose parameter hooks return one. -/

namespace GroundTerm

def isInj : GroundTerm → Bool
  | .inj _ _ _ => true
  | _ => false

/-- The order of numbers, of strings (token literals) and of Ints, as one shape. -/
def ncmp (s t : Nat) : Ordering := if s = t then .eq else if s < t then .lt else .gt
def scmp (s t : String) : Ordering := if s = t then .eq else if s < t then .lt else .gt
def icmp (s t : Int) : Ordering := if s = t then .eq else if s < t then .lt else .gt
def bcmp (s t : Bool) : Ordering := if s = t then .eq else if s = false then .lt else .gt

def andThen : Ordering → Ordering → Ordering
  | .eq, o => o
  | o, _ => o

/-- Literals: Ints before Bools before tokens before Floats; Floats by precision, exponent width
and encoding. -/
def lcmp : Lit → Lit → Ordering
  | .int a, .int b => icmp a b
  | .int _, _ => .lt
  | _, .int _ => .gt
  | .bool a, .bool b => bcmp a b
  | .bool _, _ => .lt
  | _, .bool _ => .gt
  | .tok a, .tok b => scmp a b
  | .tok _, _ => .lt
  | _, .tok _ => .gt
  | .float p e b, .float p' e' b' => andThen (ncmp p p') (andThen (ncmp e e') (ncmp b b'))

mutual
  /-- A total order on ground terms (lexicographic on the tree); it only puts map keys in a
  canonical order. -/
  def cmp : GroundTerm → GroundTerm → Ordering
    | .ctor f as, .ctor g bs => andThen (ncmp f g) (cmpList as bs)
    | .ctor .., _ => .lt
    | _, .ctor .. => .gt
    | .inj a b t, .inj a' b' t' => andThen (ncmp a a') (andThen (ncmp b b') (cmp t t'))
    | .inj .., _ => .lt
    | _, .inj .. => .gt
    | .dv s l, .dv s' l' => andThen (ncmp s s') (lcmp l l')
    | .dv .., _ => .lt
    | _, .dv .. => .gt
    | .map s es, .map s' es' => andThen (ncmp s s') (cmpEntries es es')
    | .map .., _ => .lt
    | _, .map .. => .gt
    | .set s es, .set s' es' => andThen (ncmp s s') (cmpList es es')
    | .set .., _ => .lt
    | _, .set .. => .gt
    | .list s es, .list s' es' => andThen (ncmp s s') (cmpList es es')
    termination_by structural a => a
  def cmpList : List GroundTerm → List GroundTerm → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | a :: as, b :: bs => andThen (cmp a b) (cmpList as bs)
    termination_by structural as => as
  def cmpEntries : List (GroundTerm × GroundTerm) → List (GroundTerm × GroundTerm) → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | e :: es, e' :: es' => andThen (cmpPair e e') (cmpEntries es es')
    termination_by structural es => es
  def cmpPair : GroundTerm × GroundTerm → GroundTerm × GroundTerm → Ordering
    | (k, v), (k', v') => andThen (cmp k k') (cmp v v')
    termination_by structural p => p
end

/-- The collection `v` as a value of the collection sort `s`; any other value unchanged. -/
def withSort (s : Srt) : GroundTerm → GroundTerm
  | .map _ es => .map s es
  | .set _ es => .set s es
  | .list _ es => .list s es
  | v => v

/-- A literal of a sort hooked to a library sort as that library sort's literal (`Lib.carrier`);
any other value unchanged. -/
def toLib (l : Lib) : GroundTerm → GroundTerm
  | .dv s lit => .dv (l.carrier s) lit
  | v => v

/-- A value as one of the sort `s`: a literal of `s`'s carrier as a literal of `s`, a collection
as `withSort`, any other value unchanged. -/
def asSort (l : Lib) (s : Srt) : GroundTerm → GroundTerm
  | .dv b lit => if l.carrier s == b then .dv s lit else .dv b lit
  | v => v.withSort s

/-- Where `s` is its own carrier, `asSort` is `withSort`. -/
theorem asSort_of_self {l : Lib} {s : Srt} (h : l.carrier s = s) (v : GroundTerm) :
    v.asSort l s = v.withSort s := by
  cases v with
  | dv b lit => simp only [asSort, withSort, h]; split <;> rename_i hb <;> simp_all
  | _ => rfl

/-- Without carriers, `toLib` is the identity. -/
theorem toLib_nil {l : Lib} (h : l.carriers = []) (v : GroundTerm) : v.toLib l = v := by
  cases v <;> simp [toLib, Lib.carrier_nil l h]

end GroundTerm

/-! ## Domain values -/

def digitVal (ch : Char) : Option Nat :=
  if '0' ≤ ch && ch ≤ '9' then some (ch.toNat - '0'.toNat) else none

def digitsVal : List Char → Nat → Option Nat
  | [], acc => some acc
  | ch :: chs, acc => (digitVal ch).bind fun d => digitsVal chs (10 * acc + d)

/-- The value of a canonical Int literal's text: `0`, or an optional `-` then digits not starting
with `0`. Anything else (`"05"`, `"-0"`, `"+1"`, `""`) is not a literal. Read by `parse` only:
the core holds the Int itself (`Lit.int`). -/
def intLit? (lit : String) : Option Int :=
  match lit.toList with
  | ['0'] => some 0
  | '-' :: d :: ds => if d = '0' then none else (digitsVal (d :: ds) 0).map fun n => -(n : Int)
  | d :: ds => if d = '0' then none else (digitsVal (d :: ds) 0).map fun n => (n : Int)
  | [] => none

/-- The canonical literal of an Int (`emit`). -/
def intRepr : Int → String
  | .ofNat n => Nat.repr n
  | .negSucc n => "-" ++ Nat.repr (n + 1)

def boolLit? (lit : String) : Option Bool :=
  if lit = "true" then some true else if lit = "false" then some false else none

def boolRepr (b : Bool) : String := if b then "true" else "false"

/-- The text of a literal, as the KORE writes it. -/
def Lit.text : Lit → String
  | .int i => intRepr i
  | .bool b => boolRepr b
  | .tok s => s
  | .float p e b => KFloat.text p e b

/-- The sorts with domain values, and their literals: an Int of Int, a Bool of Bool, a token of
KConfigVar, of String and of the library's token sorts, a byte string of Bytes and of the library's
byte sorts (the literal's characters are its bytes, so each is below 256), a Float of Float when its format has
a model and its encoding is one of the format's (`KFloat.ok`: a NaN only as the canonical NaN). A
sort hooked under its own name to one of these (`Lib.carrier`) has that sort's literals. A
literal is a value of its kind, so every literal is canonical. -/
def dvOK (l : Lib) (s : Srt) : Lit → Bool
  | .int _ => l.carrier s == Srt.int
  | .bool _ => l.carrier s == Srt.bool
  | .tok t => l.carrier s == Srt.kconfigVar || l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) ||
    ((l.carrier s == Srt.bytes || l.byteSorts.contains (l.carrier s)) && t.toList.all (·.toNat < 256))
  | .float p e b => l.carrier s == Srt.float && KFloat.ok p e b

/-- A literal of a sort is one of its carrier. -/
theorem dvOK_carrier {l : Lib} {s : Srt} {lit : Lit} : dvOK l (l.carrier s) lit = dvOK l s lit := by
  cases lit <;> simp only [dvOK, Lib.carrier_carrier]

/-- At a sort that is its own carrier, the literals are its own (`dvOK`'s text before carriers). -/
theorem dvOK_self {l : Lib} {s : Srt} (h : l.carrier s = s) (lit : Lit) :
    dvOK l s lit = (match lit with
      | .int _ => s == Srt.int
      | .bool _ => s == Srt.bool
      | .tok t => s == Srt.kconfigVar || s == Srt.string || l.tokenSorts.contains s ||
        ((s == Srt.bytes || l.byteSorts.contains s) && t.toList.all (·.toNat < 256))
      | .float p e b => s == Srt.float && KFloat.ok p e b) := by
  cases lit <;> simp only [dvOK, h]

/-- Without carriers, the literals of each sort are its own (`dvOK`'s text before carriers). -/
theorem dvOK_nil {l : Lib} (h : l.carriers = []) (s : Srt) (lit : Lit) :
    dvOK l s lit = (match lit with
      | .int _ => s == Srt.int
      | .bool _ => s == Srt.bool
      | .tok t => s == Srt.kconfigVar || s == Srt.string || l.tokenSorts.contains s ||
        ((s == Srt.bytes || l.byteSorts.contains s) && t.toList.all (·.toNat < 256))
      | .float p e b => s == Srt.float && KFloat.ok p e b) := by
  cases lit <;> simp only [dvOK, Lib.carrier_nil l h]

/-! ## Canonical maps -/

def keysSorted : List (GroundTerm × GroundTerm) → Bool
  | (k, _) :: (k', v') :: es => GroundTerm.cmp k k' == .lt && keysSorted ((k', v') :: es)
  | _ => true

def elemsSorted : List GroundTerm → Bool
  | k :: k' :: es => GroundTerm.cmp k k' == .lt && elemsSorted (k' :: es)
  | _ => true

/-! ## Range maps

A range map's keys are the `Range` terms of its maximal intervals in order (`rangesOK`); `sortOf` reads
it, the hooks of RangeMapHooks.lean build them. -/

abbrev Entries := List (GroundTerm × GroundTerm)

def int (i : Int) : GroundTerm := .dv Srt.int (.int i)

def asInt : GroundTerm → Option Int
  | .dv s (.int i) => if s == Srt.int then some i else none
  | _ => none

/-- An Int injected into KItem, as a range bound or a key is written. -/
def kint (i : Int) : GroundTerm := .inj Srt.int Srt.kitem (int i)

/-- A KItem that is an Int. -/
def asKInt : GroundTerm → Option Int
  | .inj a b v => if a == Srt.int && b == Srt.kitem then asInt v else none
  | _ => none

/-- The range term `[a, b)`. -/
def rangeT (a b : Int) : GroundTerm := .ctor rangeCtor [kint a, kint b]

/-- `[a, b)` with Int bounds, `a < b`: a proper range (476-477 name Int keys only; an empty or
inverted range is not described). -/
def asRange : GroundTerm → Option (Int × Int)
  | .ctor f [x, y] => if f == rangeCtor then
      (asKInt x).bind fun a => (asKInt y).bind fun b => if a < b then some (a, b) else none else none
  | _ => none

/-- A KItem that is a proper range (a member of a Set of ranges). -/
def asKRange : GroundTerm → Option (Int × Int)
  | .inj a b r => if a == Srt.range && b == Srt.kitem then asRange r else none
  | _ => none

/-- Maximal intervals in order: each key a proper range, each ending at or before the next begins,
and two that touch carry different values. -/
def rangesOK : Entries → Bool
  | [] => true
  | [(k, _)] => (asRange k).isSome
  | (k, v) :: (k', v') :: es => (match asRange k, asRange k' with
      | some (_, b), some (a', _) => decide (b ≤ a') && !(b == a' && GroundTerm.cmp v v' == .eq)
      | _, _ => false) && rangesOK ((k', v') :: es)

theorem asKInt_some {z : GroundTerm} {i : Int} (h : asKInt z = some i) : z = kint i := by
  unfold asKInt at h
  split at h
  · split at h
    · rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      unfold asInt at h
      split at h
      · split at h
        · rename_i hs
          simp only [beq_iff_eq] at hs
          simp only [Option.some.injEq] at h
          subst hs h
          rfl
        · cases h
      · cases h
    · cases h
  · cases h

theorem asRange_some {k : GroundTerm} {a b : Int} (h : asRange k = some (a, b)) : k = rangeT a b ∧ a < b := by
  match k, h with
  | .ctor f [x, y], h =>
    simp only [asRange] at h
    split at h
    · rename_i hf
      cases hx : asKInt x with
      | none => simp [hx] at h
      | some a' =>
        cases hy : asKInt y with
        | none => simp [hx, hy] at h
        | some b' =>
          simp only [hx, hy, Option.bind_some] at h
          split at h
          · rename_i hab
            cases h
            rw [asKInt_some hx, asKInt_some hy, beq_iff_eq.mp hf]
            exact ⟨rfl, hab⟩
          · cases h
    · cases h

/-- **The order of `rangesOK` is the order of `keysSorted`**: maximal intervals listed by their
lower bounds are listed in `GroundTerm.cmp`'s order of their keys, which compares two range terms
by their lower bounds first. So a map that `rangesOK` accepts is a map with sorted keys. -/
theorem keysSorted_of_rangesOK : ∀ {es : Entries}, rangesOK es = true → keysSorted es = true
  | [], _ => rfl
  | [_], _ => rfl
  | (k, v) :: (k', v') :: es, h => by
    simp only [rangesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := keysSorted_of_rangesOK h2
    cases hk : asRange k with
    | none => simp [hk] at h1
    | some p =>
      cases hk' : asRange k' with
      | none => simp [hk, hk'] at h1
      | some p' =>
        obtain ⟨a, b⟩ := p
        obtain ⟨a', b'⟩ := p'
        simp only [hk, hk', Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨rfl, hab⟩ := asRange_some hk
        obtain ⟨rfl, -⟩ := asRange_some hk'
        have hlt : a < a' := by omega
        simp only [keysSorted, ih, Bool.and_true, beq_iff_eq]
        simp [rangeT, kint, int, GroundTerm.cmp, GroundTerm.cmpList, GroundTerm.ncmp, GroundTerm.andThen,
          GroundTerm.lcmp, GroundTerm.icmp, hlt, Int.ne_of_lt hlt]

/-! ## Overloading symbols

An overloading symbol f (`Semantics.ovls`) overloads symbols g of argument sorts below its own:
`f(lift ā) = lift (g(ā))`. For a value v of sort B and a sort A ≤ B, v *lies in* A when A = B or v
is an injection from a sort at most A (`lies`); `strip A B v` is then v as a value of A, and
`lift A B` the converse. `f(v̄)` is *covered* by the overload of g when each vᵢ lies in g's i-th
argument sort, *uncovered* when no overload of f covers it; the raw application `f(v̄)` is a value
only there (`sortOf`). -/

/-- The value v of sort a as a value of a sort b above a: its injection, or, for an injected value,
the same core injected into b. -/
def injNormal (a b : Srt) : GroundTerm → GroundTerm
  | .inj a' _ w => .inj a' b w
  | v => .inj a b v

/-- A value of sort B lying in A, as a value of A. -/
def strip (A B : Srt) : GroundTerm → GroundTerm
  | .inj C B' w => if A == B then .inj C B' w else if C == A then w else .inj C A w
  | v => v

/-- A value of sort A as a value of B (A ≤ B). -/
def lift (A B : Srt) (v : GroundTerm) : GroundTerm := if A == B then v else injNormal A B v

/-- The values `vs` of the sorts `bs`, stripped to the sorts `as`, position by position. -/
def stripAll (as bs : List Srt) (vs : List GroundTerm) : List GroundTerm :=
  ((as.zip bs).zip vs).map fun ((A, B), v) => strip A B v

namespace Semantics
variable (c : Semantics)

/-- v, a value of sort B, lies in the sort A ≤ B: A is B, or v is an injection from a sort at most
A. -/
def lies (A B : Srt) : GroundTerm → Bool
  | .inj C _ _ => A == B || c.le C A
  | _ => A == B

/-- The overload of `kg` covers the arguments `vs` of `kf`: each lies in kg's argument sort. -/
def ovlCovers (kf kg : CtorSig) (vs : List GroundTerm) : Bool :=
  kg.args.length == kf.args.length && vs.length == kf.args.length &&
    ((kg.args.zip kf.args).zip vs).all fun ((A, B), v) => c.lies A B v

/-- The signatures of the symbols the overloading symbol `o` overloads: constructors, overloading
symbols or functions of the definition, read in that order (the signature of a symbol of two kinds
is the first's). -/
def ovlOver (o : OvlSig) : List CtorSig := o.over.filterMap fun g =>
  lookupSig (c.ctorSigs ++ c.ovlSigs ++ c.fns.map fun fn => ⟨fn.label, fn.args, fn.result⟩) g

/-- The signature `kg` of an overloaded symbol (`ovlOver`) is a function's: its symbol is neither a
constructor nor an overloading symbol, whose signatures `ovlOver` reads first. -/
def ovlByFn (kg : CtorSig) : Bool := (lookupSig (c.ctorSigs ++ c.ovlSigs) kg.name).isNone

/-- No overload of f covers `vs` (true of a symbol that is not an overloading symbol). -/
def uncovered (f : Sym) (vs : List GroundTerm) : Bool :=
  match c.lookupOvl f with
  | none => true
  | some o => (c.ovlOver o).all fun kg => !c.ovlCovers o.sig kg vs

/-- The open generator `f`, if it is one: a `raw` parameter whose symbol is no registry symbol. A
symbol numbered below `nRegSyms` has the library's fixed meaning (a constructor where its module is
imported, a hook, or nothing), so whether an application of it is a value never reads the
interpretation. -/
def lookupOpen (f : Sym) : Option ParamSig :=
  if nRegSyms ≤ f then c.params.find? fun k => k.raw && k.sig.name == f else none

/-- The interpretation leaves `f(vs)` raw: it gives no value there, or gives the application
itself back. -/
def keepsRaw (f : Sym) (vs : List GroundTerm) : Bool :=
  match c.hooks.app f vs with
  | none => true
  | some w => GroundTerm.cmp w (.ctor f vs) == .eq

theorem lookupOpen_none_of_any {f : Sym} (h : (c.params.any fun k => k.raw && k.sig.name == f) = false) :
    c.lookupOpen f = none := by
  unfold lookupOpen
  split
  · rw [List.find?_eq_none]
    intro k hk
    have := List.any_eq_false.mp h k hk
    simpa using this
  · rfl

/-- A registry symbol is no open generator, in every semantics. -/
theorem lookupOpen_reg {f : Sym} (h : f < nRegSyms) : c.lookupOpen f = none := by
  unfold lookupOpen
  simp [Nat.not_le.mpr h]

theorem lookupOpen_spec {f : Sym} {k : ParamSig} (h : c.lookupOpen f = some k) :
    k ∈ c.params ∧ k.raw = true ∧ k.sig.name = f ∧ nRegSyms ≤ f := by
  unfold lookupOpen at h
  split at h
  · rename_i hf
    have h1 := List.mem_of_find?_eq_some h
    have h2 := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2.1, h2.2, hf⟩
  · cases h

/-- Where no parameter is raw, no symbol is an open generator. -/
theorem lookupOpen_of_noRaw (hr : ∀ k ∈ c.params, k.raw = false) (f : Sym) : c.lookupOpen f = none :=
  c.lookupOpen_none_of_any (List.any_eq_false.mpr fun k hk => by simp [hr k hk])

end Semantics

/-! ## Sorts -/

namespace Semantics
variable (c : Semantics)

mutual
  /-- The sort of a ground term in `c`, or `none`: a constructor applied to arguments of its
  argument sorts, an overloading symbol applied to arguments of its argument sorts that no overload
  covers (`uncovered`), an open generator (`lookupOpen`) applied to arguments of its argument sorts
  where the interpretation leaves the application raw (`keepsRaw`), an injection from a subsort,
  domain values in canonical form; a collection of
  a collection sort of its kind (`collOf`): a map with sorted keys and entries of its key and
  value sorts, a range map with the maximal intervals of its keys in order (`rangesOK`) and
  entries of its key and value sorts (a collection sort without a value sort has no maps), a set with sorted elements of its element sort, a list of elements of its
  element sort. -/
  def sortOf : GroundTerm → Option Srt
    | .ctor f ts => match lookupSig c.ctorSigs f with
      | some k => if sortsOf ts == some k.args then some k.result else none
      | none => match c.lookupOvl f with
        | some o => if sortsOf ts == some o.sig.args && c.uncovered f ts then some o.sig.result
                    else none
        | none => match c.lookupOpen f with
          | some k => if sortsOf ts == some k.sig.args && c.keepsRaw f ts then some k.sig.result
                      else none
          | none => none
    | .inj a b t => if c.subsorts.contains (a, b) && !t.isInj && sortOf t == some a then some b
                    else none
    | .dv s lit => if dvOK c.lib s lit then some s else none
    | .map s es => match c.collOf s with
      | some k => match k.val with
        | some vs => if (match k.kind with | .map => keysSorted es | .rangeMap => rangesOK es | _ => false)
                        && entriesOK k.key vs es then some s
                     else none
        | none => none
      | none => none
    | .set s es => match c.collOf s, sortsOf es with
      | some k, some ss => if k.kind == .set && elemsSorted es && ss.all (· == k.key) then some s
                           else none
      | _, _ => none
    | .list s es => match c.collOf s, sortsOf es with
      | some k, some ss => if k.kind == .list && ss.all (· == k.key) then some s else none
      | _, _ => none
    termination_by structural t => t
  def sortsOf : List GroundTerm → Option (List Srt)
    | [] => some []
    | t :: ts => match sortOf t, sortsOf ts with
      | some s, some ss => some (s :: ss)
      | _, _ => none
    termination_by structural ts => ts
  def entriesOK (ks vs : Srt) : List (GroundTerm × GroundTerm) → Bool
    | [] => true
    | e :: es => entryOK ks vs e && entriesOK ks vs es
    termination_by structural es => es
  def entryOK (ks vs : Srt) : GroundTerm × GroundTerm → Bool
    | (k, v) => sortOf k == some ks && sortOf v == some vs
    termination_by structural e => e
end

/-- A map value: its collection, the value sort, the keys of its kind (`sortOf`'s arm), the
entries' sorts. -/
theorem sortOf_map_inv {s : Srt} {es : List (GroundTerm × GroundTerm)} {t : Srt}
    (h : c.sortOf (.map s es) = some t) :
    ∃ k vs, c.collOf s = some k ∧ k.val = some vs ∧
      (match k.kind with | .map => keysSorted es | .rangeMap => rangesOK es | _ => false) = true ∧
      c.entriesOK k.key vs es = true ∧ t = s := by
  simp only [sortOf] at h
  cases hk : c.collOf s with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    dsimp only at h
    cases hv : k.val with
    | none => rw [hv] at h; cases h
    | some vs =>
      rw [hv] at h
      dsimp only at h
      by_cases hb : ((match k.kind with | .map => keysSorted es | .rangeMap => rangesOK es | _ => false) &&
          c.entriesOK k.key vs es) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at h
        simp only [Bool.and_eq_true] at hb
        exact ⟨k, vs, rfl, hv, hb.1, hb.2, h.symm⟩
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

theorem sortOf_ctor_iff {f : Sym} {ts : List GroundTerm} {s : Srt} :
    c.sortOf (.ctor f ts) = some s ↔
      (∃ k, lookupSig c.ctorSigs f = some k ∧ c.sortsOf ts = some k.args ∧ s = k.result) ∨
      (lookupSig c.ctorSigs f = none ∧ ∃ o, c.lookupOvl f = some o ∧ c.sortsOf ts = some o.sig.args ∧
        c.uncovered f ts = true ∧ s = o.sig.result) ∨
      (lookupSig c.ctorSigs f = none ∧ c.lookupOvl f = none ∧ ∃ k, c.lookupOpen f = some k ∧
        c.sortsOf ts = some k.sig.args ∧ c.keepsRaw f ts = true ∧ s = k.sig.result) := by
  constructor
  · intro h
    simp only [sortOf] at h
    split at h
    · rename_i k hk
      split at h
      · rename_i he; cases h; exact .inl ⟨k, hk, beq_iff_eq.mp he, rfl⟩
      · cases h
    · rename_i hk
      split at h
      · rename_i o ho
        split at h
        · rename_i he
          simp only [Bool.and_eq_true, beq_iff_eq] at he
          cases h; exact .inr (.inl ⟨hk, o, ho, he.1, he.2, rfl⟩)
        · cases h
      · rename_i ho
        split at h
        · rename_i k hko
          split at h
          · rename_i he
            simp only [Bool.and_eq_true, beq_iff_eq] at he
            cases h; exact .inr (.inr ⟨hk, ho, k, hko, he.1, he.2, rfl⟩)
          · cases h
        · cases h
  · rintro (⟨k, hk, he, rfl⟩ | ⟨hk, o, ho, he, hu, rfl⟩ | ⟨hk, ho, k, hko, he, hkr, rfl⟩)
    · simp [sortOf, hk, he]
    · simp [sortOf, hk, ho, he, hu]
    · simp [sortOf, hk, ho, hko, he, hkr]

/-- A constructor term with a sort has arguments with sorts. -/
theorem sortsOf_of_sortOf_ctor {f : Sym} {ts : List GroundTerm} {s : Srt}
    (h : c.sortOf (.ctor f ts) = some s) : ∃ ss, c.sortsOf ts = some ss := by
  rcases c.sortOf_ctor_iff.mp h with ⟨k, -, hs, -⟩ | ⟨-, o, -, hs, -, -⟩ | ⟨-, -, k, -, hs, -, -⟩
  · exact ⟨_, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨_, hs⟩

/-- Without overloading symbols and raw parameters, a constructor term's sort is its constructor's. -/
theorem sortOf_ctor_of_none {f : Sym} {ts : List GroundTerm} {s : Srt} (hno : c.ovls = [])
    (_hr : ∀ k ∈ c.params, k.raw = false) :
    c.sortOf (.ctor f ts) = some s ↔
      ∃ k, lookupSig c.ctorSigs f = some k ∧ c.sortsOf ts = some k.args ∧ s = k.result := by
  rw [sortOf_ctor_iff]
  have : c.lookupOvl f = none := by simp [lookupOvl, hno]
  simp [this, c.lookupOpen_of_noRaw _hr f]

/-- The value `f(vs)` denotes, with `n` steps along the overloads: the raw application where no
overload of f covers `vs`, otherwise the value of the first symbol g whose overload covers it at
the stripped arguments, lifted to f's result sort. Where that g is a function (`ovlByFn`) the
application is left as it is: what it denotes is the function's value at the stripped arguments,
lifted, which evaluation gives and no function on values does. -/
def normN : Nat → Sym → List GroundTerm → GroundTerm
  | 0, f, vs => .ctor f vs
  | n + 1, f, vs => match c.lookupOvl f with
    | none => .ctor f vs
    | some o => match (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none => .ctor f vs
      | some kg =>
        if c.ovlByFn kg then .ctor f vs
        else lift kg.result o.sig.result (normN n kg.name (stripAll kg.args o.sig.args vs))

/-- **The value an application denotes**: `normN` with one step per overloading symbol and one
more (each overloaded overloading symbol is listed before the one overloading it,
`overloadsOK`). For a symbol that is not an overloading symbol, the raw application; so is an
application the overload of a function covers, which denotes no value of its own. -/
def norm (f : Sym) (vs : List GroundTerm) : GroundTerm := c.normN (c.ovls.length + 1) f vs

/-- The function overload of the overloading symbol `f` that covers the arguments `vs`: the first
signature among the symbols `f` overloads (`ovlOver`) that is a function's (`ovlByFn`) and covers
`vs`. There the application `f(vs)` denotes that function's value at the stripped arguments, lifted
to `f`'s result sort (the overload's equation), whichever other overloads cover `vs` too. -/
def fnCover (f : Sym) (vs : List GroundTerm) : Option CtorSig :=
  (c.lookupOvl f).bind fun o => (c.ovlOver o).find? fun kg => c.ovlByFn kg && c.ovlCovers o.sig kg vs

/-- No function overload covers `vs`: no function's signature among the overloads of `f` does. -/
theorem fnCover_eq_none_iff {f : Sym} {vs : List GroundTerm} :
    c.fnCover f vs = none ↔
      ∀ o, c.lookupOvl f = some o → ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true → c.ovlCovers o.sig kg vs = false := by
  unfold fnCover
  cases h : c.lookupOvl f with
  | none => simp
  | some o =>
    simp only [Option.bind_some, List.find?_eq_none, Bool.and_eq_true, not_and, Bool.not_eq_true,
      Option.some.injEq, forall_eq']

/-- A symbol that is no overloading symbol has no function overload. -/
theorem fnCover_of_lookupOvl_none {f : Sym} (h : c.lookupOvl f = none) (vs : List GroundTerm) :
    c.fnCover f vs = none := by
  simp [fnCover, h]

/-- No function overload covers anything where no overloaded symbol's signature is a function's. -/
theorem fnCover_none_of_noByFn (h : ∀ o ∈ c.ovls, ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = false) (f : Sym)
    (vs : List GroundTerm) : c.fnCover f vs = none := by
  rw [fnCover_eq_none_iff]
  intro o ho kg hkg hb
  rw [h o (List.mem_of_find?_eq_some ho) kg hkg] at hb
  cases hb

end Semantics

def Value (c : Semantics) (s : Srt) : Type := { t : GroundTerm // c.sortOf t = some s }

abbrev Config (c : Semantics) : Type := Value c topCellSort

/-- The keys a map of a collection of kind `kind` has: sorted for a map, the maximal intervals in
order for a range map (`sortOf`'s arm). -/
theorem mapKeys_sorted {kind : CollKind} {es : Entries}
    (h : (match kind with | .map => keysSorted es | .rangeMap => rangesOK es | _ => false) = true) :
    (kind = .map ∨ kind = .rangeMap) ∧ keysSorted es = true := by
  cases kind with
  | map => exact ⟨.inl rfl, h⟩
  | rangeMap => exact ⟨.inr rfl, keysSorted_of_rangesOK h⟩
  | set => cases h
  | list => cases h

mutual
  /-- The value applies no open generator: none of its constructor nodes is the symbol of a `raw`
  parameter (inside injections and collections too). -/
  def Semantics.rawFree (c : Semantics) : GroundTerm → Bool
    | .ctor f ts => !(c.params.any fun k => k.raw && k.sig.name == f) && c.rawFreeList ts
    | .inj _ _ t => c.rawFree t
    | .dv _ _ => true
    | .map _ es => c.rawFreeEntries es
    | .set _ es => c.rawFreeList es
    | .list _ es => c.rawFreeList es
    termination_by structural t => t
  def Semantics.rawFreeList (c : Semantics) : List GroundTerm → Bool
    | [] => true
    | t :: ts => c.rawFree t && c.rawFreeList ts
    termination_by structural ts => ts
  def Semantics.rawFreeEntries (c : Semantics) : List (GroundTerm × GroundTerm) → Bool
    | [] => true
    | e :: es => c.rawFreeEntry e && c.rawFreeEntries es
    termination_by structural es => es
  def Semantics.rawFreeEntry (c : Semantics) : GroundTerm × GroundTerm → Bool
    | (k, v) => c.rawFree k && c.rawFree v
    termination_by structural e => e
end

-- Where no parameter is raw, every value is `rawFree`.
mutual
  theorem Semantics.rawFree_of_noRaw {c : Semantics} (hr : ∀ k ∈ c.params, k.raw = false) :
      ∀ v, c.rawFree v = true
    | .ctor f ts => by
      simp only [Semantics.rawFree, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨List.any_eq_false.mpr fun k hk => by simp [hr k hk], Semantics.rawFreeList_of_noRaw hr ts⟩
    | .inj _ _ t => by rw [Semantics.rawFree]; exact Semantics.rawFree_of_noRaw hr t
    | .dv _ _ => by rw [Semantics.rawFree]
    | .map _ es => by rw [Semantics.rawFree]; exact Semantics.rawFreeEntries_of_noRaw hr es
    | .set _ es => by rw [Semantics.rawFree]; exact Semantics.rawFreeList_of_noRaw hr es
    | .list _ es => by rw [Semantics.rawFree]; exact Semantics.rawFreeList_of_noRaw hr es
    termination_by structural v => v
  theorem Semantics.rawFreeList_of_noRaw {c : Semantics} (hr : ∀ k ∈ c.params, k.raw = false) :
      ∀ ts, c.rawFreeList ts = true
    | [] => by rw [Semantics.rawFreeList]
    | t :: ts => by
      rw [Semantics.rawFreeList, Semantics.rawFree_of_noRaw hr t, Semantics.rawFreeList_of_noRaw hr ts]; rfl
    termination_by structural ts => ts
  theorem Semantics.rawFreeEntries_of_noRaw {c : Semantics} (hr : ∀ k ∈ c.params, k.raw = false) :
      ∀ es, c.rawFreeEntries es = true
    | [] => by rw [Semantics.rawFreeEntries]
    | e :: es => by
      rw [Semantics.rawFreeEntries, Semantics.rawFreeEntry_of_noRaw hr e,
        Semantics.rawFreeEntries_of_noRaw hr es]; rfl
    termination_by structural es => es
  theorem Semantics.rawFreeEntry_of_noRaw {c : Semantics} (hr : ∀ k ∈ c.params, k.raw = false) :
      ∀ e, c.rawFreeEntry e = true
    | (k, v) => by rw [Semantics.rawFreeEntry, Semantics.rawFree_of_noRaw hr k, Semantics.rawFree_of_noRaw hr v]; rfl
    termination_by structural e => e
end

end KCore
