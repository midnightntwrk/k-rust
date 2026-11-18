/-
  KCore. The conditions of `wf` (KCORE-SPEC.md §7). Reviewed layer, root track. Among them:
  - **subsorts** a strict partial order, given transitively closed as kompile writes it, over the
    user's sorts and the library's value sorts, every supersort a user sort; a sort may lie below
    several (`Int < AExp`, `Int < KResult`), and below a sort that is itself a subsort
    (`subsortsOK`);
  - not among them: that two equations of a function of one priority agree where both apply.
    `fnExclusiveOK` decides it where their patterns are apart (`overlapList`), their `requires` exclude each other
    (`reqsExclusive`: Bool literals, `==K` of different values, complementary or disjoint Int
    bounds, disjunctions) or their right-hand sides are one closed term (`clausesAgree`); the
    other functions are named obligations (`agreeObligations`). Two injections `inj{A,N}(p)`,
    `inj{B,N}(q)` overlap when A and B have a common lower bound, not only when they are
    comparable (`Int` below `AExp` and `KResult` makes `inj{AExp,KItem}(_)` and
    `inj{KResult,KItem}(_)` both match `inj{Int,KItem}(5)`), and then only if one of the injected
    patterns can itself denote an injection (`injable`); two collection patterns always overlap;
  - not among them: that two matches of one clause at one argument list give one result
    (`MatchIndependent`). `clauseFixed` decides it where the clause's patterns fix its variables;
    the other clauses are named obligations (`matchObligations`);
  - declarations and terms over the library's sorts with values (Set, the token sorts, the
    K-IO sorts) and its constructors; domain values of the token sorts;
  - the generated sort predicates callable in right-hand sides and `requires`;
  - rule and equation attributes: `owise` and `priority` are read into `Rule.prio` (Step.lean)
    and `Clause.prio` (Evaluation.lean); a priority without `priority{}("n")` is 50 or 200
    (`owise`);
  - the builtin library: the core's is the union of the imported modules' (`Presentation.ok`,
    Builtins.lean), with the facts the generic theorems read (`Lib.ok`).
-/
import KcoreSpec.Definition
import KcoreSpec.Value
import KcoreSpec.Builtins

set_option autoImplicit false

namespace KCore

def Fn.sig (f : Fn) : CtorSig := ⟨f.label, f.args, f.result⟩

def nodup {α : Type} [BEq α] : List α → Bool
  | [] => true
  | a :: as => !as.contains a && nodup as

def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: as => as.map (a, ·) ++ pairs as

/-! ## Terms -/

/-- Where a term occurs: a left-hand side (patterns: constructors, the map pattern symbols,
as-patterns), or a right-hand side / `requires` (constructors, hooks, functions). -/
structure TermCtx where
  lib : Lib
  subs : List (Srt × Srt)
  heads : List CtorSig
  asOK : Bool

mutual
  def sortOfTerm (x : TermCtx) (vs : List Srt) : Term → Option Srt
    | .var i => vs[i]?
    | .dv s lit => if dvOK x.lib s lit then some s else none
    | .app f ts => match lookupSig x.heads f with
      | some s => if sortsOfTerms x vs ts == some s.args then some s.result else none
      | none => none
    | .inj a b t => if x.subs.contains (a, b) && sortOfTerm x vs t == some a then some b else none
    | .as t i => match x.asOK, vs[i]?, sortOfTerm x vs t with
      | true, some v, some s => if v == s then some s else none
      | _, _, _ => none
    termination_by structural t => t
  def sortsOfTerms (x : TermCtx) (vs : List Srt) : List Term → Option (List Srt)
    | [] => some []
    | t :: ts => match sortOfTerm x vs t, sortsOfTerms x vs ts with
      | some s, some ss => some (s :: ss)
      | _, _ => none
    termination_by structural ts => ts
end

/-- A term's sort over some heads is its sort over more heads after them. -/
theorem lookupSig_append_some {l l' : List CtorSig} {f : Sym} {k : CtorSig} (h : lookupSig l f = some k) :
    lookupSig (l ++ l') f = some k := by
  rw [lookupSig_eq] at h ⊢; rw [List.find?_append, h]; rfl

mutual
  theorem sortOfTerm_heads (x : TermCtx) (H : List CtorSig) (vs : List Srt) : ∀ (t : Term) {s : Srt},
      sortOfTerm x vs t = some s → sortOfTerm { x with heads := x.heads ++ H } vs t = some s
    | .var _, _, h => by simpa [sortOfTerm] using h
    | .dv _ _, _, h => by simpa [sortOfTerm] using h
    | .app f ts, s, h => by
      simp only [sortOfTerm] at h ⊢
      cases hk : lookupSig x.heads f with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h; rw [lookupSig_append_some hk]
        simp only at h ⊢
        by_cases he : (sortsOfTerms x vs ts == some k.args) = true
        · rw [if_pos he] at h
          rw [if_pos (by rw [sortsOfTerms_heads x H vs ts (beq_iff_eq.mp he)]; simp)]; exact h
        · rw [if_neg he] at h; cases h
    | .inj a b t, s, h => by
      simp only [sortOfTerm] at h ⊢
      by_cases hc : (x.subs.contains (a, b) && sortOfTerm x vs t == some a) = true
      · rw [if_pos hc] at h
        have hc' := hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc'
        have h2 := sortOfTerm_heads x H vs t hc'.2
        rw [if_pos (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨hc'.1, h2⟩)]; exact h
      · rw [if_neg hc] at h; cases h
    | .as t i, s, h => by
      simp only [sortOfTerm] at h ⊢
      cases ht : sortOfTerm x vs t with
      | none => rw [ht] at h; split at h <;> simp_all
      | some u => rw [ht] at h; rw [sortOfTerm_heads x H vs t ht]; exact h
  theorem sortsOfTerms_heads (x : TermCtx) (H : List CtorSig) (vs : List Srt) : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms x vs ts = some ss → sortsOfTerms { x with heads := x.heads ++ H } vs ts = some ss
    | [], _, h => by simpa [sortsOfTerms] using h
    | t :: ts, ss, h => by
      simp only [sortsOfTerms] at h ⊢
      cases h1 : sortOfTerm x vs t with
      | none => rw [h1] at h; cases h
      | some a =>
        cases h2 : sortsOfTerms x vs ts with
        | none => rw [h1, h2] at h; cases h
        | some b => rw [h1, h2] at h; rw [sortOfTerm_heads x H vs t h1, sortsOfTerms_heads x H vs ts h2]; exact h
end

mutual
  def varOccs : Term → List Nat
    | .var i => [i]
    | .app _ ts => varOccsList ts
    | .inj _ _ t => varOccs t
    | .as t i => varOccs t ++ [i]
    | .dv _ _ => []
    termination_by structural t => t
  def varOccsList : List Term → List Nat
    | [] => []
    | t :: ts => varOccs t ++ varOccsList ts
    termination_by structural ts => ts
end

def linearCover (n : Nat) (occs : List Nat) : Bool :=
  occs.length == n && (List.range n).all occs.contains

/-- Every variable `0, …, n-1` occurs (repetitions allowed). -/
def binds (n : Nat) (occs : List Nat) : Bool := (List.range n).all occs.contains

/-- The free variables of a condition, n variables in scope. -/
def varOccsCond (n : Nat) : Cond → List Nat
  | .top | .bot => []
  | .not p => varOccsCond n p
  | .and p q | .or p q | .implies p q => varOccsCond n p ++ varOccsCond n q
  | .ceil _ t => varOccs t
  | .equals _ t u | .mem _ t u => varOccs t ++ varOccs u
  | .exMatch ys _ p t body => varOccs t ++
      (varOccs p ++ varOccsCond (n + ys.length) body).filter (· < n)
  | .ex _ body | .all _ body => (varOccsCond (n + 1) body).filter (· < n)

def Rule.condVars (r : Rule) : List Nat :=
  (r.req.map varOccs).getD [] ++ varOccsCond r.vars.length r.pre
def Rule.leftVars (r : Rule) : List Nat := varOccs r.lhs ++ r.condVars
/-- The variables the left side does not bind. -/
def Rule.opens (r : Rule) : List Nat :=
  (List.range r.vars.length).filter fun i => !(varOccs r.lhs).contains i
def Rule.openCondVars (r : Rule) : List Nat := r.opens.filter r.condVars.contains
/-- A condition of the left side holds a variable the left side does not bind. -/
def Rule.reqOpen (r : Rule) : Bool := !r.openCondVars.isEmpty
/-- No condition of the left side holds a variable the left side binds. -/
def Rule.reqClosed (r : Rule) : Bool := r.condVars.all fun i => !(varOccs r.lhs).contains i

def Clause.condVars (cl : Clause) : List Nat :=
  (cl.req.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.pre
def Clause.leftVars (cl : Clause) : List Nat := varOccsList cl.pats ++ cl.condVars
def Clause.opens (cl : Clause) : List Nat :=
  (List.range cl.vars.length).filter fun i => !(varOccsList cl.pats).contains i
def Clause.openCondVars (cl : Clause) : List Nat := cl.opens.filter cl.condVars.contains
def Clause.reqOpen (cl : Clause) : Bool := !cl.openCondVars.isEmpty
def Clause.reqClosed (cl : Clause) : Bool := cl.condVars.all fun i => !(varOccsList cl.pats).contains i

theorem Cond.eq_top_of_isTop {p : Cond} (h : p.isTop = true) : p = .top := by
  cases p <;> simp_all [Cond.isTop]

mutual
  /-- A map pattern: `_Map_` trees of `k |-> v` (any patterns), `.Map`, and variables; the result
  counts the variables at map positions (frames). -/
  def mapFrames : Term → Option Nat
    | .app f ts => mapFramesApp f ts
    | .var _ => some 1
    | _ => none
    termination_by structural t => t
  def mapFramesApp (f : Sym) : List Term → Option Nat
    | [a, b] => if f == mapConcat then
        match mapFrames a, mapFrames b with
        | some m, some n => some (m + n)
        | _, _ => none
      else if f == mapElem then (if noMapIn a && noMapIn b then some 0 else none) else none
    | [] => if f == mapUnit then some 0 else none
    | _ => none
    termination_by structural ts => ts
  /-- A pattern outside map positions: every map subpattern has at most one frame. -/
  def noMapIn : Term → Bool
    | .app f ts => if patternHooks.contains f then (match mapFramesApp f ts with
        | some n => n ≤ 1
        | none => false) else noMapInList ts
    | .inj _ _ t => noMapIn t
    | .as t _ => noMapIn t
    | .var _ => true
    | .dv _ _ => true
    termination_by structural t => t
  def noMapInList : List Term → Bool
    | [] => true
    | t :: ts => noMapIn t && noMapInList ts
    termination_by structural ts => ts
end

mutual
  /-- No map pattern symbol at all (function clauses). -/
  def mapFree : Term → Bool
    | .app f ts => !patternHooks.contains f && mapFreeList ts
    | .inj _ _ t => mapFree t
    | .as t _ => mapFree t
    | _ => true
    termination_by structural t => t
  def mapFreeList : List Term → Bool
    | [] => true
    | t :: ts => mapFree t && mapFreeList ts
    termination_by structural ts => ts
end

def peelAs : Term → Term
  | .as t _ => peelAs t
  | t => t

/-- Whether a pattern can denote an injection: a variable, an injection, or an alias of one. A
literal denotes a domain value, a constructor its constructor term, and the map, list and
cell-map symbols a collection (`PatVal`): none of them an injection. -/
def injable (t : Term) : Bool :=
  match peelAs t with
  | .var _ => true
  | .inj .. => true
  | _ => false

/-- The library's collection symbols: the unit, element and concatenation of maps, sets and lists. -/
def collHooks : List Sym := patternHooks ++ [setUnit, setElem, setConcat] ++ listPatternHooks

mutual
  /-- `false` only if no value matches both patterns (distinct literals apart).
  `meet a b`: the sorts a and b have a common lower bound (one of them, or a third sort below
  both), so injections from them can denote the same value. Two injections `inj{a,N}(p)` and
  `inj{b,N}(q)` with a ≠ b denote one value `inj{a',N}(v)` only from a sort a' below both
  (`injNormal`); a' differs from a or from b, and there p or q denotes the injection
  `inj{a',a}(v)` or `inj{a',b}(v)`, so one of them must be able to denote an injection
  (`injable`): `inj{ExceptionalStatusCode,StatusCode}(EVMC_FAILURE)` and
  `inj{EndStatusCode,StatusCode}(EVMC_SUCCESS)` are apart.
  `coll f`: f is a collection symbol (`Semantics.collHead`). Two patterns headed by collection
  symbols overlap whatever their heads and arguments: a collection is the same value however it is
  built, so `.Map` and `M N`, or `1 |-> A M` and `2 |-> B N`, denote one map. Constructor terms and
  collections are different values. -/
  def overlap (meet : Srt → Srt → Bool) (coll : Sym → Bool) : Term → Term → Bool
    | .var _, _ => true
    | .as p _, q => overlap meet coll p q
    | .dv s l, q => match peelAs q with
      | .var _ => true
      | .dv s' l' => s == s' && l == l'
      | _ => false
    | .app f ps, q => match peelAs q with
      | .var _ => true
      | .app g qs => (coll f && coll g) || (f == g && overlapList meet coll ps qs)
      | _ => false
    | .inj a _ p, q => match peelAs q with
      | .var _ => true
      | .inj b _ q' => if a == b then overlap meet coll p q' else meet a b && (injable p || injable q')
      | _ => false
    termination_by structural p => p
  def overlapList (meet : Srt → Srt → Bool) (coll : Sym → Bool) : List Term → List Term → Bool
    | p :: ps, q :: qs => overlap meet coll p q && overlapList meet coll ps qs
    | _, _ => true
    termination_by structural ps => ps
end

/-! ## Syntactic facts the function conditions read (moved from Determinism.lean, 2026-11-09:
the clause conditions of `fnOK` call them; DetSound.lean and Uniq.lean prove what they mean) -/

/-- The literals a `requires` equal to `true` asserts: each conjunct of `_andBool_`, `notBool A`
as `A = false`, `true` none, anything else `A = true`. -/
def lits : Term → List (Term × Bool)
  | .app f [t₁, t₂] => if f == boolAnd then lits t₁ ++ lits t₂ else [(.app f [t₁, t₂], true)]
  | .app f [t] => if f == boolNot then [(t, false)] else [(.app f [t], true)]
  | .dv s l => if s == Srt.bool && l == .bool true then [] else [(.dv s l, true)]
  | t => [(t, true)]

mutual
  def Term.beq : Term → Term → Bool
    | .var i, .var j => i == j
    | .app f ts, .app g us => f == g && Term.beqList ts us
    | .inj a b t, .inj a' b' t' => a == a' && b == b' && Term.beq t t'
    | .as t i, .as t' j => i == j && Term.beq t t'
    | .dv s l, .dv s' l' => s == s' && l == l'
    | _, _ => false
    termination_by structural t => t
  def Term.beqList : List Term → List Term → Bool
    | [], [] => true
    | t :: ts, u :: us => Term.beq t u && Term.beqList ts us
    | _, _ => false
    termination_by structural ts => ts
end

/-! `uniq c D p`: the variables a match of p fixes, given those of D (`f` is a constructor of c
when `lookupSig c.ctorSigs f` finds it, `Semantics.isCtor`). -/

mutual
  /-- `some D'`: two well-sorted σ, σ' under which p denotes one value, and that agree on D,
  agree on D'. -/
  def uniq (c : Semantics) (D : List Nat) : Term → Option (List Nat)
    | .var i => some (i :: D)
    | .dv _ _ => some D
    | .inj _ _ p => uniq c D p
    | .as p i => (uniq c D p).map (i :: ·)
    | .app f ps =>
      if (lookupSig c.ctorSigs f).isSome then uniqList c D ps
      else if f == mapUnit then (if ps.isEmpty then some D else none)
      else if f == mapConcat then uniqConcat c D ps
      else none
    termination_by structural p => p
  def uniqList (c : Semantics) (D : List Nat) : List Term → Option (List Nat)
    | [] => some D
    | p :: ps => (uniq c D p).bind fun D' => uniqList c D' ps
    termination_by structural ps => ps
  /-- `K |-> V M`, the key's variables in D: V's value, then M's, are fixed. -/
  def uniqConcat (c : Semantics) (D : List Nat) : List Term → Option (List Nat)
    | [.app e [k, v], rest] =>
      if e == mapElem && (varOccs k).all D.contains then (uniq c D v).bind fun D' => uniq c D' rest
      else none
    | _ => none
    termination_by structural ps => ps
end

/-! ## Coverage -/

/-- A generator of a sort: a constructor, or the injection from a direct subsort. -/
inductive Gen where
  | ctor (c : CtorSig)
  | inj (src : Srt)
  deriving Repr

def Gen.argSorts : Gen → List Srt
  | .ctor c => c.args
  | .inj a => [a]

namespace Semantics
variable (c : Semantics)

/-- The generators of N: its constructors, its overloading symbols (whose raw applications are
values where no overload covers their arguments), its open generators (the `raw` parameters of
result N, whose raw applications are values where the interpretation leaves them raw) and the
injections from its subsorts. -/
def gens (N : Srt) : List Gen :=
  (c.ctorSigs.filter (·.result == N)).map .ctor ++
  (c.ovlSigs.filter (·.result == N)).map .ctor ++
  (((c.params.filter (·.raw)).map (·.sig)).filter (·.result == N)).map .ctor ++
  (sortBy id ((c.subsorts.filter (·.2 == N)).map (·.1))).map .inj

/-- The generator is an open generator: a symbol `lookupOpen` answers for. -/
def isOpenGen : Gen → Bool
  | .ctor k => (c.lookupOpen k.name).isSome
  | .inj _ => false

/-- The sorts whose generators `covers` enumerates: those whose values are exactly the applications
of their generators (`gens`: constructor terms of the sort, and injections from its subsorts). A
user sort is one, unless it is a collection sort (`collOf`: its values are collections, which no
generator builds) or holds domain values (Int, Bool, KConfigVar, the library's token and byte sorts,
Float, String, Bytes, a sort hooked to a library carrier: its literals, `dvOK`). Base sorts, K, KItem and those sorts are covered only by
variables, and so is every sort of a semantics with overloading symbols (whose raw applications no
constructor pattern matches), and every sort of a semantics with a raw parameter (an open
generator's application is a value of its result sort only where the interpretation leaves it raw,
so the values of a sort are not fixed by the data). -/
def enumerable (N : Srt) : Bool :=
  c.ovls.isEmpty && c.userSorts.contains N && (c.collOf N).isNone &&
    !(N == Srt.int || N == Srt.bool || N == Srt.kconfigVar || c.lib.tokenSorts.contains N ||
      c.lib.byteSorts.contains N || N == Srt.float || N == Srt.string || N == Srt.bytes) &&
    c.lib.carriers.all (·.1 != N) && !c.params.any (·.raw)

/-- a and b have a common lower bound. -/
def meet (a b : Srt) : Bool :=
  c.le a b || c.le b a || c.subsorts.any fun (s, _) => c.le s a && c.le s b

/-- A collection symbol: one of the library's (`collHooks`), or a parameter implemented by one (a
collection sort's unit, element and concatenation, `collOK`). -/
def collHead (f : Sym) : Bool :=
  collHooks.contains f || c.params.any fun k => k.sig.name == f && (k.impl.map collHooks.contains).getD false

end Semantics

/-- Row `ps` specialised to generator `g`: `none` if its head pattern cannot match a `g` value. -/
def specialize (g : Gen) : List Term → Option (List Term)
  | [] => none
  | p :: ps => match peelAs p, g with
    | .var _, g => some ((g.argSorts.map fun _ => Term.var 0) ++ ps)
    | .app f qs, .ctor k => if f == k.name then some (qs ++ ps) else none
    | .inj a _ q, .inj a' => if a == a' then some (q :: ps) else none
    | _, _ => none

namespace Semantics
variable (c : Semantics)

/-- Every well-sorted vector of values of the sorts `ss` matches some row (the classic
usefulness check, without `requires`). Fuel bounds the recursion; running out answers `false`,
so the check can only reject more. -/
def covers : Nat → List Srt → List (List Term) → Bool
  | 0, _, _ => false
  | _ + 1, [], rows => !rows.isEmpty
  | n + 1, s :: ss, rows =>
    let varRows := rows.filterMap fun r => match r with
      | p :: ps => (match peelAs p with | .var _ => some ps | _ => none)
      | [] => none
    if c.enumerable s && varRows.length != rows.length then
      (c.gens s).all fun g => covers n (g.argSorts ++ ss) (rows.filterMap (specialize g))
    else covers n ss varRows

/-! ## Declarations, cells, functions, rules -/

end Semantics

def reqOK (x : TermCtx) (vs : List Srt) : Option Term → Bool
  | none => true
  | some t => sortOfTerm x vs t == some Srt.bool

namespace Semantics
variable (c : Semantics)

/-- The library's sorts whose elements are all values: its sorts below KItem (a List is the
sequence of its elements, `GroundTerm.list`, a Float a datum of its format, `Lit.float`). -/
def libValueSorts : List Srt :=
  c.lib.sortsBelowKItem

/-- The library's sorts with generators: constructors (K-IO's) or injections from library sorts. -/
def libCtorSorts : List Srt :=
  c.lib.sortsBelowKItem.filter fun s => c.lib.ctors.any (·.result == s) || c.lib.subsorts.any (·.2 == s)

/-- The library's sorts whose values are constructor terms: those with generators
(`libCtorSorts`) that hold no domain value (Int, Bool, KConfigVar, the library's token and byte
sorts, whose values are their literals, `dvOK`) and are no collection sort (`collOf`, whose values
are collections). JSON is one (`null`, `JSONEntry`, …, and injections); Int and Map are not. -/
def libConsSorts : List Srt :=
  c.libCtorSorts.filter fun s => s != Srt.int && s != Srt.bool && s != Srt.kconfigVar &&
    !c.lib.tokenSorts.contains s && !c.lib.byteSorts.contains s && (c.collOf s).isNone

/-- A declared argument sort: one of the definition's sorts (a cell sort among them: KEVM's `{_|_}`
of `Accounts` takes two cells, `getTxData` the top cell), K, KItem, a library sort with values, or
Int, whose values are its literals whatever the library (`dvOK`; the counter cell holds one). -/
def argSortOK (s : Srt) : Bool :=
  c.userSorts.contains s || [Srt.k, Srt.kitem, Srt.int].contains s || c.libValueSorts.contains s

/-- A declared result sort of a function: one of the definition's sorts, K (a function to K
sequences, `syntax K ::= f(Int) [function]`, or an instance at K of a sort-parametric one), KItem, or
a library sort with values. -/
def resultSortOK (s : Srt) : Bool :=
  c.userSorts.contains s || s == Srt.k || s == Srt.kitem || c.libValueSorts.contains s

/-- A declared result sort of a constructor: one of the definition's sorts, KItem, or a library
sort of constructor terms (`libConsSorts`: K-REFLECTION's `#noParse` builds K-IO's `IOError`,
`ReadingNote.reflectionAsOwn`). -/
def ctorResultOK (s : Srt) : Bool :=
  c.userSorts.contains s || s == Srt.kitem || c.libConsSorts.contains s

/-- The declarations are over declared sorts and the `$PGM` sort is one of them. -/
def declsOK : Bool :=
  (c.ctors.all fun k => k.args.all c.argSortOK && c.ctorResultOK k.result) &&
  (c.fns.all fun f => f.args.all c.argSortOK && c.resultSortOK f.result) &&
  (c.userSorts.contains c.pgmSort || [Srt.k, Srt.kitem, Srt.int, Srt.bool].contains c.pgmSort)

mutual
  def cellNames : Cell → List String
    | .leaf n _ _ => [n]
    | .node n cs _ => n :: cellNamesList cs
    | .coll _ => []
    termination_by structural x => x
  def cellNamesList : List Cell → List String
    | [] => []
    | x :: xs => cellNames x ++ cellNamesList xs
    termination_by structural xs => xs
  def cellLeaves : Cell → List (String × Srt)
    | .leaf n s _ => [(n, s)]
    | .node _ cs _ => cellLeavesList cs
    | .coll _ => []
    termination_by structural x => x
  def cellLeavesList : List Cell → List (String × Srt)
    | [] => []
    | x :: xs => cellLeaves x ++ cellLeavesList xs
    termination_by structural xs => xs
  /-- The sorts of the cell collections among a cell's descendants. -/
  def cellCollSortsR : Cell → List Srt
    | .leaf _ _ _ => []
    | .node _ cs _ => cellCollSortsListR cs
    | .coll s => [s]
    termination_by structural x => x
  def cellCollSortsListR : List Cell → List Srt
    | [] => []
    | x :: xs => cellCollSortsR x ++ cellCollSortsListR xs
    termination_by structural xs => xs
end

mutual
  /-- A user cell has the sorts and symbols of its kind: its `Opt` sort and `noXCell`, and for a
  node its fragment sort and `<x>-fragment`, which a leaf has not; and so have its children. A
  cell collection, which has none of them, is a node's child beside a cell (`Presentation.cellsOK`
  asks its sort to be a collection of the definition). -/
  def cellIdsShaped : Cell → Bool
    | .leaf _ _ i => i.opt.isSome && i.no.isSome && i.frag.isNone && i.fragLabel.isNone
    | .node _ cs i =>
      i.opt.isSome && i.no.isSome && i.frag.isSome && i.fragLabel.isSome && cellIdsShapedList cs &&
      cs.any (fun | .coll _ => false | _ => true)
    | .coll _ => true
    termination_by structural x => x
  def cellIdsShapedList : List Cell → Bool
    | [] => true
    | x :: xs => cellIdsShaped x && cellIdsShapedList xs
    termination_by structural xs => xs
end

def alnum (n : String) : Bool := !n.isEmpty && n.toList.all Char.isAlphanum

/-- A cell name: letters, digits and inner dashes (`exit-code`, whose sort is `ExitCodeCell`). The
names derived from it are told apart by `namesOK`. -/
def cellNameOK (n : String) : Bool :=
  !n.isEmpty && n.toList.all (fun ch => ch.isAlphanum || ch == '-') && n.toList.head? != some '-'

/-- The declared subsorts form a strict partial order into sorts whose values are constructor
terms: each declared pair `a < b` has a lower sort a that is a user sort or a library sort with
values, and an upper sort b that is a user sort or a library sort whose values are constructor
terms (`libConsSorts`: KEVM's `Account < JSON`); the closure (`declaredClosure`) is irreflexive, so
there is no cycle; the pairs are declared once. A value of b is a constructor or an injection
applied to values, and `inj{a,b}(v)` is one of b's generators (`gens`) whichever module declares b:
the injection is read like the library's own. A sort of domain values or a collection sort is no
upper sort: its values are its literals or collections, and an injected value there would be one
no hook is defined on. A sort may lie below several sorts and chains may be long (KCORE-SPEC.md
Q24): values stay unique because an injection is never nested (`sortOf`), so a value of sort b
holding a value of sort a is `inj{a,b}(v)` with v not an injection, through any chain. -/
def subsortsOK : Bool :=
  let subs := c.userSubsorts
  subs.all (fun (a, b) => a != b && (c.userSorts.contains a || c.libValueSorts.contains a) &&
    (c.userSorts.contains b || c.libConsSorts.contains b)) &&
  c.declaredClosure.all (fun (a, b) => a != b) &&
  nodup subs

/-- The library's facts the generic theorems read (NamesApart.lean): its sorts below KItem are
registry sorts other than KItem and the generated cells', each once; its subsorts relate them; no
constructor of it is a map-pattern symbol. Every union of the library's modules has them; they
are checked on the definition's. -/
def _root_.KCore.Lib.ok (l : Lib) : Bool :=
  l.sortsBelowKItem.all (fun s => decide (s < nRegSorts) && !(17 ≤ s && s ≤ 20) && s != Srt.kitem) &&
  nodup l.sortsBelowKItem &&
  l.subsorts.all (fun p => l.sortsBelowKItem.contains p.1 && l.sortsBelowKItem.contains p.2) &&
  l.ctors.all (fun k => !patternHooks.contains k.name)

/-- The definition's own sorts and symbols are numbered as Core.lean says: its own sorts
(`ownSorts`) are `nRegSorts, nRegSorts + 1, …`, one name each; its symbols but the sort predicates
(`ownSyms`: constructors, functions, parameters, overloading symbols) are `symBase, symBase + 1, …`,
one name each, after the predicates of its own sorts. So all of them are distinct, from each other and from the registry's, and `predOf` gives each own
sort its own predicate. Linear in their number. Its other sorts are the registry's generated
configuration sorts (`genSorts`), each once, and its other constructors the generated
configuration's (`genSyms`); no library sort is one of them, nor KItem (`Lib.ok`). -/
def idsOK : Bool :=
  c.ownSorts == List.range' nRegSorts c.sortNames.length &&
  c.ownSyms == List.range' c.symBase (c.symNames.length - c.sortNames.length) &&
  decide (c.sortNames.length ≤ c.symNames.length) &&
  ((let reg := c.userSorts.filter fun s => decide (s < nRegSorts)
    nodup reg && reg.all genSorts.contains &&
    c.ctors.all fun k => decide (nRegSyms ≤ k.name) || genSyms.contains k.name) && c.lib.ok)

/-- The sorts with a value: the least set of sorts closed under generators whose argument sorts it
holds (constructors and injections), from K, KItem, Int, the library's value sorts, the token
sorts (each literal is a value), the sorts hooked to a library carrier (each of the carrier's
literals is a value, `dvOK`) and the definition's collection sorts (each has its empty
collection), in as many rounds as there are user sorts (each round adds one or reaches the
fixpoint). -/
def valueSorts : List Srt :=
  let univ := c.userSorts
  let step := fun (inh : List Srt) =>
    inh ++ univ.filter fun N =>
      !inh.contains N && (c.gens N).any fun g => g.argSorts.all inh.contains
  Nat.repeat step univ.length
    ([Srt.k, Srt.kitem, Srt.int] ++ c.libValueSorts ++ c.lib.tokenSorts ++ c.lib.carriers.map (·.1) ++
      c.colls.map (·.sort))

/-- The user sorts without a value (`valueSorts`): no finite term of the definition's generators
has the sort, so a rule or equation with a variable of such a sort has no instance through it.
Not a condition of `wf`: `Step`, the theory's model and the statements over `coreOK` ask no sort
to have a value. A fact the account prints. -/
def valueless : List Srt := c.userSorts.filter fun N => !c.valueSorts.contains N

/-- Every sort of the definition has a value (`valueless` is empty). Not a condition of `wf`. -/
def inhabited : Bool := c.userSorts.all c.valueSorts.contains

def patCtx : TermCtx := ⟨c.lib, c.subsorts, c.ctorSigs ++ hookSigs.filter (patternHooks.contains ·.name), true⟩

/-- The collection pattern symbols' signatures (`PatVal.coll`): the library's set and list symbols
(`collPatternHooks`), and the parameters implemented by a map pattern symbol or by one of those (a
cell map's, a cell set's, a cell list's). -/
def collPatSigs : List CtorSig :=
  hookSigs.filter (collPatternHooks.contains ·.name) ++
    (c.params.filter fun k => match k.impl with
      | some g => patternHooks.contains g || collPatternHooks.contains g
      | none => false).map (·.sig)

/-- The well-formedness context of a rule's left-hand side: the matcher's (`patCtx`), then the
collection pattern symbols and the overloading symbols. -/
def patCtxAll : TermCtx := { c.patCtx with heads := c.patCtx.heads ++ (c.collPatSigs ++ c.ovlSigs) }
/-- Right-hand sides and `requires`: constructors, hooks, the parameter symbols, the generated
sort predicates, the functions given and the overloading symbols. -/
def rhsCtx (fns : List CtorSig) : TermCtx :=
  ⟨c.lib, c.subsorts, c.ctorSigs ++ hookSigs ++ c.params.map (·.sig) ++ c.sortPreds.map Fn.sig ++ fns ++ c.ovlSigs,
    false⟩

/-- The clause's match fixes every variable: two well-sorted substitutions under which its
patterns denote one list of arguments agree on all of its variables (`uniqList`). A map pattern
`K |-> V M` is allowed where its key's variables are fixed by the arguments before it, since a
map's keys are unique: kimp's `<env>` lookup, and `lev(X:Id, X |-> L _)` in a function. So a
clause has at most one instance at given arguments, and it is match independent
(`clauseFixed_sound`). It is not a condition of `clauseOK`: the clauses it does not confirm are
named obligations (`matchObligations`), and the executable evaluation's completeness reads it of
every clause (`clausesFixed`). -/
def clauseFixed (cl : Clause) : Bool :=
  match uniqList c [] cl.pats with
  | some D => (List.range cl.vars.length).all D.contains
  | none => false

/-- Well-sorted patterns of the argument sorts, each map pattern with at most one frame
(`noMapIn`), binding every variable (repetitions allowed: a key bound in one argument and looked
up in a map in a later one); a Bool `requires` and a right-hand side of the result sort. That the
match fixes the variables is not checked here (`clauseFixed`, `matchObligations`). -/
def clauseOK (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms c.patCtx cl.vars cl.pats == some f.args &&
  noMapInList cl.pats &&
  binds cl.vars.length (varOccsList cl.pats) &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtx rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.ens

def coverFuel (f : Fn) : Nat := 1000 * (f.clauses.length + 1)

end Semantics

mutual
  def callsOf (f : Sym) : Term → List (List Term)
    | .app g ts => (if g == f then [ts] else []) ++ callsOfList f ts
    | .inj _ _ t => callsOf f t
    | .as t _ => callsOf f t
    | _ => []
    termination_by structural t => t
  def callsOfList (f : Sym) : List Term → List (List Term)
    | [] => []
    | t :: ts => callsOf f t ++ callsOfList f ts
    termination_by structural ts => ts
end

/-- A constructor of `c` that is no map pattern symbol: an application of it in a pattern denotes
only the constructor term (`PatVal.ctor`; `PatVal.hook` reads the map pattern symbols,
`PatVal.coll` symbols that are no constructor). -/
def Semantics.ctorPat (c : Semantics) (g : Sym) : Bool :=
  (lookupSig c.ctorSigs g).isSome && !patternHooks.contains g

mutual
  /-- The variable `j` occurs in the pattern on a path of applications of symbols `pat` admits,
  injections and aliases only. -/
  def ctorPathIn (pat : Sym → Bool) (j : Nat) : Term → Bool
    | .var i => i == j
    | .app g ts => pat g && ctorPathInList pat j ts
    | .inj _ _ t => ctorPathIn pat j t
    | .as t _ => ctorPathIn pat j t
    | .dv _ _ => false
    termination_by structural t => t
  def ctorPathInList (pat : Sym → Bool) (j : Nat) : List Term → Bool
    | [] => false
    | t :: ts => ctorPathIn pat j t || ctorPathInList pat j ts
    termination_by structural ts => ts
end

/-- The variable `j` lies strictly inside the pattern: under at least one application of a symbol
`pat` admits, on a path of such applications, injections and aliases only (`ctorPathIn`). With
`pat` the constructors that are no map pattern symbol (`Semantics.ctorPat`), a value the pattern
denotes is strictly larger than j's (`GroundTerm.size`, `strictlyIn_size` in Terminates.lean): on
such an application only the constructor case of `PatVal` applies, a constructor value is strictly
larger than each argument, and injections and aliases do not shrink a value. A collection pattern
gives no such bound: a frame variable can denote the whole value (`_Map_(.Map, M)`,
`_List_(L₁, L₂)` with L₁ empty). -/
def strictlyIn (pat : Sym → Bool) (j : Nat) : Term → Bool
  | .app g ts => pat g && ctorPathInList pat j ts
  | .inj _ _ t => strictlyIn pat j t
  | .as t _ => strictlyIn pat j t
  | _ => false

/-- The self calls of `f`, each with the patterns of the clause it is in: in the right-hand sides
and the `requires`. -/
def selfCalls (f : Fn) : List (List Term × List Term) :=
  f.clauses.flatMap fun cl =>
    (callsOf f.label cl.rhs ++ (cl.req.map (callsOf f.label)).getD [] ++
      (cl.ens.map (callsOf f.label)).getD []).map (cl.pats, ·)

/-- Self calls decrease at `dec`, in the right-hand side and in the `requires`: the argument at
`dec` is a variable strictly inside the clause's pattern there (`strictlyIn`). -/
def decreasingOK (c : Semantics) (f : Fn) (dec : Option Nat) : Bool :=
  let calls := selfCalls f
  calls.isEmpty || match dec with
    | none => false
    | some i => calls.all fun (pats, args) => match args[i]?, pats[i]? with
      | some (.var j), some p => strictlyIn c.ctorPat j p
      | _, _ => false

namespace Semantics
variable (c : Semantics)

/-- The sorts whose values the interpreted symbols take apart: Int, Bool, Map, Set, List and
RangeMap. -/
def _root_.KCore.shapeSorts : List Srt := [Srt.int, Srt.bool, Srt.map, Srt.set, Srt.list, Srt.rangeMap]

/-- The sorts whose literals the interpreted symbols read as their characters: String and Bytes. -/
def _root_.KCore.litShapeSorts : List Srt := [Srt.string, Srt.bytes]

/-- Endianness and Signedness have only BYTES' constructors as values: every constructor of either
sort is one of BYTES' two of it (`LE`, `BE`; `Signed`, `Unsigned`) without arguments, and no
injection, collection sort of the definition's own, token or byte sort, overloading symbol nor raw
parameter has either as its sort. Then `Bytes2Int` has a value at every argument list of its sorts. -/
def enumShapesOK : Bool :=
  c.ctorSigs.all (fun k =>
    (k.result != Srt.endianness || ((k.name == littleEndianBytes || k.name == bigEndianBytes) && k.args.isEmpty)) &&
    (k.result != Srt.signedness || ((k.name == signedBytes || k.name == unsignedBytes) && k.args.isEmpty))) &&
  c.subsorts.all (fun p => p.2 != Srt.endianness && p.2 != Srt.signedness) &&
  c.colls.all (fun k => k.sort != Srt.endianness && k.sort != Srt.signedness) &&
  !(c.lib.tokenSorts ++ c.lib.byteSorts).any (fun s => s == Srt.endianness || s == Srt.signedness) &&
  c.ovlSigs.all (fun k => k.result != Srt.endianness && k.result != Srt.signedness) &&
  c.params.all (fun k => !(k.raw && (k.sig.result == Srt.endianness || k.sig.result == Srt.signedness)))

/-- Every value of a sort of `shapeSorts` is a domain value or a collection of that sort, and every
value of a sort of `litShapeSorts` a literal: no constructor, injection, collection sort of the
definition's own, overloading symbol nor raw parameter has one of them as its sort, and no token or
byte sort is one of `shapeSorts`. Then an Int is an Int literal, a Map a map, a RangeMap a range
map, a String a token literal, and so on, which the interpreted symbols read. -/
def shapesOK : Bool :=
  c.ctorSigs.all (fun k => !(shapeSorts ++ litShapeSorts).contains k.result) &&
  c.subsorts.all (fun p => !(shapeSorts ++ litShapeSorts).contains p.2) &&
  !(c.lib.tokenSorts ++ c.lib.byteSorts).any shapeSorts.contains &&
  c.colls.all (fun k => !(shapeSorts ++ litShapeSorts).contains k.sort) &&
  c.ovlSigs.all (fun k => !(shapeSorts ++ litShapeSorts).contains k.result) &&
  c.params.all (fun k => !(k.raw && (shapeSorts ++ litShapeSorts).contains k.sig.result)) &&
  c.enumShapesOK

mutual
  /-- A term whose value is defined wherever its variables have values: variables, domain values,
  injections, constructors, the interpreted symbols that are total (all but `partialHooks`), and
  calls of the functions named in `tot` that are no interpreted symbol, no parameter symbol (an
  application of one of those has its value, `EvalTerm.hook`, `EvalTerm.param`, whatever function
  bears its number, and it may be undefined) and no overloading symbol (whose application is the
  value of a function it overloads where one covers the arguments, `EvalTerm.ovlFn`). -/
  def totalTerm (tot : List Sym) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .inj _ _ t => totalTerm tot t
    | .as _ _ => false
    | .app f ts =>
      ((lookupSig c.ctorSigs f).isSome || (hookSigs.any (·.name == f) && !partialHooks.contains f) ||
        (tot.contains f && !hookSigs.any (·.name == f) && !c.params.any (·.sig.name == f) &&
          (c.lookupOvl f).isNone)) &&
        totalTermList tot ts
    termination_by structural t => t
  def totalTermList (tot : List Sym) : List Term → Bool
    | [] => true
    | t :: ts => totalTerm tot t && totalTermList tot ts
    termination_by structural ts => ts
end

/-- The functions declared total before f. -/
def totalBefore (f : Fn) : List Sym :=
  ((c.fns.takeWhile (·.label != f.label)).filter (·.total)).map (·.label)

/-- The rows of a clause in `covers`: its patterns, when it has no `requires` and its pattern
variables occur at most once across the row. A row with a repeated variable matches only arguments
equal at those positions, so reading it as independent variables overstates what it covers. -/
def coverRows (f : Fn) : List (List Term) :=
  (f.clauses.filter fun cl => cl.req.isNone && nodup (varOccsList cl.pats)).map (·.pats)

/-- The first argument at which f's self calls decrease (`decreasingOK`), if any; `none` (no self
call allowed) when there is none. -/
def decArg (f : Fn) : Option Nat :=
  (List.range f.args.length).find? fun i => decreasingOK c f (some i)

/-- A function declared `[total]` is defined at every argument of its sorts: the values of the
sorts the interpreted symbols read have their shapes (`shapesOK`, so the hooks but `partialHooks`
are defined at values of their sorts); its self calls decrease (`decreasingOK` at `decArg`); its
covering rows (`coverRows`, of every priority) cover its argument sorts; and every right-hand side
is total over the total functions before it, the sort predicates and itself (`total_of_totalOK`,
Totals.lean). Then the functional axiom kompile writes for it, `∃y. f(x̄) = y`, holds where
evaluation gives its value. The total functions before it are the well-founded order of the
argument. A `[total]` declaration this check cannot confirm is listed in `totalObligations`: under
the reading of partial functions (§2.5), its axiom could be false. -/
def totalOK (f : Fn) : Bool :=
  let tot := c.totalBefore f ++ c.sortPreds.map (·.label) ++ [f.label]
  c.shapesOK && decreasingOK c f (c.decArg f) &&
  c.covers (coverFuel f) f.args (coverRows f) &&
  f.clauses.all (fun cl => c.totalTerm tot cl.rhs) && f.clauses.all (·.ens.isNone)

/-- `t ==K u` as a literal asserted true. -/
def eqKLit : Term × Bool → Option (Term × Term)
  | (.app f [t, u], true) => if f == kEq then some (t, u) else none
  | _ => none

mutual
  /-- A ground term of constructors, domain values and injections, no injection directly over
  another: its value is the term itself read as a value, so two such terms that differ have
  different values. -/
  def groundValue : Term → Bool
    | .dv _ _ => true
    | .app f ts => (lookupSig c.ctorSigs f).isSome && groundValueList ts
    | .inj _ _ t => (match t with | .inj .. => false | _ => true) && groundValue t
    | _ => false
    termination_by structural t => t
  def groundValueList : List Term → Bool
    | [] => true
    | t :: ts => groundValue t && groundValueList ts
    termination_by structural ts => ts
end

/-- Two Int comparisons that are each other's negation on every pair of Ints. -/
def intCompl : List (Sym × Sym) :=
  [(intLt, intGe), (intGe, intLt), (intLe, intGt), (intGt, intLe), (intEq, intNe), (intNe, intEq)]

/-- `x op y` and `x op' y` with `op'` the complement of `op` (`intCompl`), asserted alike. -/
def complLits (x : TermCtx) (vs : List Srt) : Term × Bool → Term × Bool → Bool
  | (.app f [t, u], b), (.app g [t', u'], b') =>
      intCompl.contains (f, g) && Term.beq t t' && Term.beq u u' && b == b' &&
        (sortOfTerm x vs t).isSome && (sortOfTerm x vs u).isSome
  | _, _ => false

/-- The value of an Int literal term. -/
def intLitOf : Term → Option Int
  | .dv s (.int k) => if s == Srt.int then some k else none
  | _ => none

/-- The bounds `x op k` asserts of the Int x, for an Int comparison op asserted `true`
(`lo ≤ x ≤ hi`, each bound optional; `=/=Int` none). -/
def cmpBound (f : Sym) (k : Int) : Option (Option Int × Option Int) :=
  if f == intLt then some (none, some (k - 1))
  else if f == intLe then some (none, some k)
  else if f == intGt then some (some (k + 1), none)
  else if f == intGe then some (some k, none)
  else if f == intEq then some (some k, some k)
  else none

/-- The comparison asserted: `op` itself when asserted `true`, its complement (`intCompl`) when
`false`. -/
def cmpAsserted (f : Sym) (b : Bool) : Option Sym :=
  if f == intLt then some (if b then intLt else intGe)
  else if f == intGe then some (if b then intGe else intLt)
  else if f == intLe then some (if b then intLe else intGt)
  else if f == intGt then some (if b then intGt else intLe)
  else if f == intEq then some (if b then intEq else intNe)
  else if f == intNe then some (if b then intNe else intEq)
  else none

/-- `k op x` read as `x op' k`. -/
def cmpFlip (f : Sym) : Option Sym :=
  if f == intLt then some intGt else if f == intLe then some intGe
  else if f == intGt then some intLt else if f == intGe then some intLe
  else if f == intEq then some intEq else if f == intNe then some intNe else none

/-- A literal comparing an Int term with an Int literal, as the term and the bounds it puts on
the term's value: `x op k`, or `k op x`, asserted `b`. -/
def intBound : Term × Bool → Option (Term × Option Int × Option Int)
  | (.app f [x, y], b) =>
    match cmpAsserted f b with
    | none => none
    | some g =>
      match intLitOf y with
      | some k => (cmpBound g k).map fun r => (x, r)
      | none =>
        match intLitOf x, cmpFlip g with
        | some k, some g' => (cmpBound g' k).map fun r => (y, r)
        | _, _ => none
  | _ => none

/-- Two bounded ranges with nothing in common: one's lower bound above the other's upper. -/
def boundsApart : Option Int × Option Int → Option Int × Option Int → Bool
  | (lo, hi), (lo', hi') =>
    (match lo, hi' with | some l, some h => decide (h < l) | _, _ => false) ||
    (match lo', hi with | some l, some h => decide (h < l) | _, _ => false)

/-- Two literals never both hold under one substitution (`reqsExclusive`'s cases): a Bool
literal negated; `t ==K a` and `t ==K b` with a, b different ground values; complementary
comparisons of the same Ints (`complLits`); or bounds on one Int term by Int literals with no
value in common (`intBound`: `I <Int 0` and `0 <=Int I`, `sgn(I) ==Int -1` and
`sgn(I) ==Int 1`). -/
def litsApart (heads : List CtorSig) (vs : List Srt) : Term × Bool → Term × Bool → Bool
  | (A, b), (A', b') =>
      (Term.beq A A' && b != b' && sortOfTerm (c.rhsCtx heads) vs A == some Srt.bool) ||
      (match eqKLit (A, b), eqKLit (A', b') with
       | some (x, a), some (x', a') => Term.beq x x' && (sortOfTerm (c.rhsCtx heads) vs x).isSome &&
           c.groundValue a && c.groundValue a' && !Term.beq a a'
       | _, _ => false) ||
      complLits (c.rhsCtx heads) vs (A, b) (A', b') ||
      (match intBound (A, b), intBound (A', b') with
       | some (x, r), some (x', r') => Term.beq x x' && (sortOfTerm (c.rhsCtx heads) vs x).isSome &&
           boundsApart r r'
       | _, _ => false)

/-- A literal of one `requires` that the other's literals exclude: some literal apart from it,
or, for a disjunction `A orBool B` asserted `true`, both disjuncts excluded. -/
def litExcluded (heads : List CtorSig) (vs : List Srt) (ls' : List (Term × Bool)) : Term × Bool → Bool
  | (.app f [A₁, A₂], true) =>
    if f == boolOr then
      ls'.any (c.litsApart heads vs (A₁, true)) && ls'.any (c.litsApart heads vs (A₂, true))
    else ls'.any (c.litsApart heads vs (.app f [A₁, A₂], true))
  | l => ls'.any (c.litsApart heads vs l)

/-- Two `requires` over the variables `vs` that are never both `true` under one substitution:
a literal of one excluded by the other's (`litExcluded`, `litsApart`). -/
def reqsExclusive (heads : List CtorSig) (vs : List Srt) : Option Term → Option Term → Bool
  | some q, some q' => (lits q).any (c.litExcluded heads vs (lits q'))
  | _, _ => false

/-- Two clauses whose patterns may match one argument list, with one variable list and one pattern
list and `requires` that exclude each other: then at most one applies at any arguments. -/
def clausesExclusive (heads : List CtorSig) (cl cl' : Clause) : Bool :=
  cl.vars == cl'.vars && Term.beqList cl.pats cl'.pats && c.reqsExclusive heads cl.vars cl.req cl'.req

/-- Two clauses whose right-hand sides are one term without variables: wherever both apply, they
are the same instance of one right-hand side. -/
def _root_.KCore.clausesAgree (cl cl' : Clause) : Bool :=
  Term.beq cl.rhs cl'.rhs && (varOccs cl.rhs).isEmpty && cl.ens.isNone && cl'.ens.isNone

mutual
  /-- The symbols a term applies. -/
  def _root_.KCore.Term.heads : Term → List Sym
    | .app f ts => f :: Term.headsList ts
    | .inj _ _ t => Term.heads t
    | .as t _ => Term.heads t
    | _ => []
    termination_by structural t => t
  def _root_.KCore.Term.headsList : List Term → List Sym
    | [] => []
    | t :: ts => Term.heads t ++ Term.headsList ts
    termination_by structural ts => ts
end

/-- The symbols a function's right-hand sides, `requires` and `ensures` apply. -/
def _root_.KCore.Fn.callees (f : Fn) : List Sym :=
  f.clauses.flatMap fun cl => Term.heads cl.rhs ++ (cl.req.map Term.heads).getD [] ++ (cl.ens.map Term.heads).getD []

/-- The symbols some rule's right-hand side or `requires`, or some function, applies. -/
def appliedSyms : List Sym :=
  c.rules.flatMap (fun r => Term.heads r.rhs ++ (r.req.map Term.heads).getD []) ++
  c.fns.flatMap (·.callees)

/-- The functions that apply a function-overloaded symbol (`fnOvlSyms`). At arguments a function
it overloads covers, an application of such a symbol is that function's value (`EvalTerm.ovlFn`):
a call of a function the term does not name, which neither the declaration order nor a rank of the
functions counts. The termination of these functions is a named obligation (`orderObligations`,
`rankObligations`). -/
def fnOvlCallers : List Sym :=
  (c.fns.filter fun f => f.callees.any c.fnOvlSyms.contains).map (·.label)

/-- The functions that call a function declared after them, and those that apply a
function-overloaded symbol (`fnOvlCallers`). Declaration order, with decreasing
self calls (`Certificates.ok`), is KCore's argument that evaluation terminates
(`terminates_of_order`, Terminates.lean); for these functions it does not apply, and their
termination is a named obligation (`Obligations`, Statements.lean). -/
def orderObligations : List Sym :=
  let labels := c.fns.map (·.label)
  let rec go (earlier : List Sym) : List Fn → List Sym
    | [] => []
    | f :: fs =>
      (if f.callees.all (fun g => g == f.label || earlier.contains g || !labels.contains g) then []
       else [f.label]) ++ go (earlier ++ [f.label]) fs
  go [] c.fns ++ c.fnOvlCallers

/-- Well-formed clauses over constructors, hooks and the functions `heads` (`fnsOK`: every
function of the definition, in any order: functions may call one another, mutually recursively,
since `Eval` is an inductive relation and the proofs about it proceed by induction on derivations);
at least one clause, unless no rule, `requires` or function applies it (`used`, `appliedSyms`:
then its meaning is never read, and kompile's declared-only symbols, such as macros expanded away,
are admitted; a used function with neither would be read as undefined everywhere, which is not what
the KORE says of it, so it is refused). That two equations of one priority which both apply give
one result is not checked here: `fnExclusiveOK` decides it where it can, and the functions it does not confirm are
`agreeObligations`. A function declared total and not confirmed by `totalOK` is not refused: it is
one of `totalObligations`. -/
def fnOK (heads : List CtorSig) (used : List Sym) (f : Fn) : Bool :=
  f.clauses.all (c.clauseOK f heads) &&
  (!f.clauses.isEmpty || !used.contains f.label)

/-- Every function's clauses, over every function's signature. -/
def fnsOK : Bool := c.fns.all (c.fnOK (c.fns.map Fn.sig) c.appliedSyms)

/-- Each two of f's equations that compete give one result wherever both apply (`ClausesAgree`,
ClausesAgree.lean; `Det.fnExclusiveOK_sound`), clauses of different priorities neither of which is
`aside` never competing (`Eval.clause`): their patterns are apart
(`overlapList`), or they are alike but for exclusive `requires` (`clausesExclusive`), or their
right-hand sides are one closed term (`clausesAgree`). The second case reads that the first
clause's patterns fix its variables (`clauseFixed`), so that the two clauses' matches at one argument
list are one substitution. `heads` are the functions the `requires` may call, as in `fnOK`. -/
def fnExclusiveOK (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all (fun (cl, cl') => (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
    !overlapList c.meet c.collHead cl.pats cl'.pats || (c.clauseFixed cl && c.clausesExclusive heads cl cl') ||
      clausesAgree cl cl')

/-- The functions whose equations of one priority `fnExclusiveOK` does not show to agree where two
apply: that they do (`ClausesAgree`) is a named obligation (`Obligations`, Statements.lean). The
decider reads patterns as the executable matcher does, without overloading symbols: with one, every
function is named. -/
def agreeObligations : List Sym :=
  (c.fns.filter fun f => !(c.ovls.isEmpty && c.fnExclusiveOK (c.fns.map Fn.sig) f)).map (·.label)

/-- The clauses whose patterns `clauseFixed` does not show to fix their variables, each as its
function and its index among the function's clauses: that each is match independent (two matches
at one argument list give one result, `MatchIndependent`) is a named obligation (`Obligations`,
Statements.lean). The decider reads patterns as the executable matcher does, without overloading
symbols: with one, every clause is named. -/
def matchObligations : List (Sym × Nat) :=
  c.fns.flatMap fun f =>
    ((List.range f.clauses.length).filter fun i => !(c.ovls.isEmpty && f.clauses[i]?.all c.clauseFixed)).map
      (f.label, ·)

/-- Every clause of every function, the sort predicates' among them, fixes its variables
(`clauseFixed`): with no agreement named, the clauses of one priority are then coherent
(`Det.coherentAll_of_nil`, FnExclusive.lean), which the executable evaluation's completeness reads
(`EvalTerm.exec`, EvalComplete.lean). -/
def clausesFixed : Bool := c.allFns.all fun f => f.clauses.all c.clauseFixed

/-- The functions declared `[total]` that `totalOK` does not confirm: the functional axiom kompile
writes for each (`∃y. f(x̄) = y`) is not shown to hold of `Eval`, and is a named obligation
(`Obligations`, Statements.lean; KCORE-SPEC.md §2.5). The others are total (`totals_of_order`,
Totals.lean). -/
def totalObligations : List Sym :=
  (c.fns.filter fun f => f.total && !c.totalOK f).map (·.label)

/-- A rule: a left-hand side of the configuration sort whose map patterns have at most one
frame, binding every variable (repetitions allowed); a Bool `requires` and a right-hand side of
the configuration sort over constructors, hooks and the user's functions; a Bool `ensures`; no
existential variable (the left side binds every variable, so none is left for one); `\top`
predicates (the executable step reads neither `pre` nor `post`, so it is the step of rules whose
predicates say nothing). -/
def ruleOK (r : Rule) : Bool :=
  sortOfTerm c.patCtx r.vars r.lhs == some topCellSort &&
  noMapIn r.lhs &&
  binds r.vars.length (varOccs r.lhs) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort &&
  r.exs.isEmpty && r.pre.isTop && r.post.isTop

/-- A rule as `ruleOK` asks, its predicates aside: the conjuncts of `ruleOK` other than
`pre.isTop` and `post.isTop`. -/
def ruleOKM (r : Rule) : Bool :=
  sortOfTerm c.patCtx r.vars r.lhs == some topCellSort &&
  noMapIn r.lhs &&
  binds r.vars.length (varOccs r.lhs) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort &&
  r.exs.isEmpty

/-- `ruleOK` is `ruleOKM` and the two `\top` predicates. -/
theorem ruleOK_iff {r : Rule} :
    c.ruleOK r = true ↔ c.ruleOKM r = true ∧ r.pre.isTop = true ∧ r.post.isTop = true := by
  show ((c.ruleOKM r && r.pre.isTop) && r.post.isTop) = true ↔ _
  simp only [Bool.and_eq_true, and_assoc]

/-- A rule, as `ruleOK`, its left-hand side well-sorted over the collection pattern symbols too
(`patCtxAll`), and each of its variables occurring somewhere in it rather than in its left side
(which variables the left side may leave open is `rulesPlain`'s, Tie.lean); its existential
variables distinct variables the left side and the conditions do not hold (as `ruleSorted`). -/
def ruleOKAll (r : Rule) : Bool :=
  sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort &&
  noMapIn r.lhs &&
  binds r.vars.length (varOccs r.lhs ++ r.condVars ++ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
    varOccsCond r.vars.length r.post) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort &&
  nodup r.exs && r.exs.all (fun i => r.opens.contains i && !r.condVars.contains i)

/-- A clause, as `clauseOK`, its patterns well-sorted over the collection pattern symbols too
(`patCtxAll`: KEVM's `#lookup(K |-> V M, K)`, a list's `ListItem(P) L`), and each of its variables
occurring in its patterns, its `requires`, its right-hand side or its `ensures` (which of them the
patterns may leave open is `clausesPlain`'s). -/
def clauseOKAll (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats == some f.args &&
  noMapInList cl.pats &&
  binds cl.vars.length (cl.leftVars ++ varOccs cl.rhs ++ (cl.ens.map varOccs).getD []) &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtx rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.ens

/-- `fnOK`, its clauses as `clauseOKAll`. -/
def fnOKAll (heads : List CtorSig) (used : List Sym) (f : Fn) : Bool :=
  f.clauses.all (c.clauseOKAll f heads) &&
  (!f.clauses.isEmpty || !used.contains f.label)

def fnsOKAll : Bool := c.fns.all (c.fnOKAll (c.fns.map Fn.sig) c.appliedSyms)

theorem clauseOKAll_of {f : Fn} {H : List CtorSig} {cl : Clause} (h : c.clauseOK f H cl = true) :
    c.clauseOKAll f H cl = true := by
  simp only [clauseOK, clauseOKAll, Bool.and_eq_true, beq_iff_eq] at h ⊢
  refine ⟨⟨⟨⟨⟨sortsOfTerms_heads _ _ _ _ h.1.1.1.1.1, h.1.1.1.1.2⟩, ?_⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  have hbd := h.1.1.1.2
  simp only [binds, List.all_eq_true, List.contains_iff_mem, List.mem_append, Clause.leftVars] at hbd ⊢
  exact fun i hi => Or.inl (Or.inl (Or.inl (hbd i hi)))

theorem fnsOKAll_of (h : c.fnsOK = true) : c.fnsOKAll = true := by
  simp only [fnsOK, fnsOKAll, List.all_eq_true] at h ⊢
  intro f hf
  have := h f hf
  simp only [fnOK, fnOKAll, Bool.and_eq_true, List.all_eq_true] at this ⊢
  exact ⟨fun cl hcl => c.clauseOKAll_of (this.1 cl hcl), this.2⟩

/-- `ruleOKAll_of` from `ruleOKM`: it reads no predicate. -/
theorem ruleOKAll_of_M {r : Rule} (h : c.ruleOKM r = true) : c.ruleOKAll r = true := by
  simp only [ruleOKM, ruleOKAll, Bool.and_eq_true, beq_iff_eq] at h ⊢
  have hex : r.exs = [] := List.isEmpty_iff.mp h.2
  have h := h.1
  refine ⟨⟨⟨⟨⟨⟨⟨sortOfTerm_heads _ _ _ _ h.1.1.1.1.1, h.1.1.1.1.2⟩, ?_⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩, ?_⟩, ?_⟩
  · have hb := h.1.1.1.2
    simp only [binds, List.all_eq_true, List.contains_iff_mem, List.mem_append] at hb ⊢
    exact fun i hi => Or.inl (Or.inl (Or.inl (Or.inl (hb i hi))))
  · simp [hex, nodup]
  · simp [hex]

theorem ruleOKAll_of {r : Rule} (h : c.ruleOK r = true) : c.ruleOKAll r = true := by
  simp only [ruleOK, ruleOKAll, Bool.and_eq_true, beq_iff_eq] at h ⊢
  have hex : r.exs = [] := List.isEmpty_iff.mp h.1.1.2
  have h := h.1.1.1
  refine ⟨⟨⟨⟨⟨⟨⟨sortOfTerm_heads _ _ _ _ h.1.1.1.1.1, h.1.1.1.1.2⟩, ?_⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩, ?_⟩, ?_⟩
  · have hb := h.1.1.1.2
    simp only [binds, List.all_eq_true, List.contains_iff_mem, List.mem_append] at hb ⊢
    exact fun i hi => Or.inl (Or.inl (Or.inl (Or.inl (hb i hi))))
  · simp [hex, nodup]
  · simp [hex]

end Semantics

/-! ## Certificate and presentation (as F0) -/

/-- A decreasing argument the certificate names is one: its self calls decrease there. A function
with self calls and no decreasing argument is not refused; it is one of `obligations`. -/
def Certificates.ok (z : Certificates) (c : Semantics) : Bool :=
  (withPres c.fns z.decreasing).all fun (f, dec) => dec.isNone || decreasingOK c f dec

/-- The functions whose self calls the certificate does not show to decrease: their termination
is a named obligation of any statement that reads it (totality, and the meaning of their equations
as the least one, `Eval`). -/
def Certificates.obligations (z : Certificates) (c : Semantics) : List Sym :=
  ((withPres c.fns z.decreasing).filter fun (f, dec) => !decreasingOK c f dec).map (·.1.label)

def namesFor (n : Nat) (names : List String) : Bool := names.length == n && nodup names

/-- Rule attributes that leave the rule's ground steps unchanged: `concrete` (every ground
configuration is concrete), kompile's `cool-like` and `cool` (hints to a backend's strategy; the
rule is an ordinary rewrite), `preserves-definedness` (no K text gives the attribute a meaning:
kore-syntax.md:223-229 makes an attribute a hint whose semantic content belongs in explicit axioms,
and the user manual has no occurrence of it; kompile writes it on the axiom and no sentence beside
it, e2-rule/kore.txt:193-199), `symbolic` (which terms a prover
applies the rule to, no statement of the theory: the text states the rewrite axiom and `Step` has
its steps), `comm` (K gives it no meaning on a rule). Not among them: `anywhere`, `non-executable`,
`simplification`, which the reader refuses (`Parse.attrVerdictOf` at class `rule`). `owise` and `priority` are not attributes here:
they are read into `Rule.prio`. -/
def inertRuleAttrs : List String := ["concrete", "cool-like", "cool", "preserves-definedness", "symbolic", "comm"]

/-- Rule attributes with an argument that only present the rule: those kompile copies from a
production onto its heating and cooling rules. -/
def inertArgAttrs : List String := ["symbol'Kywd'", "format", "colors"]

/-- Strictly increasing. -/
def sortedNat : List Nat → Bool
  | a :: b :: l => decide (a < b) && sortedNat (b :: l)
  | _ => true

/-- The configuration's cell tree: its cells named apart (from each other and the generated ones),
alphanumerically, the leaf holding `$PGM` (`pgmCell`, where one does) a leaf of content K or
`$PGM`'s sort (the two contents `emit` writes `$PGM`'s projection into), each with the sorts and symbols of its kind
(`cellIdsShaped`), each cell collection among a node's children a collection of the core
(`colls`, whose unit `emit` writes as its initial value); and the sorts, constructors and subsorts it derives (`Presentation.cellSorts`,
`cellCtors`, `cellSubsorts`) are the first of the core's (`userSorts`, `ctors`, `userSubsorts`),
which `emit` writes from the tree and the rest from the core. -/
def Presentation.cellsOK (p : Presentation) (c : Semantics) : Bool :=
  let ns := Semantics.cellNamesList p.config
  nodup (ns ++ ["generatedTop", "generatedCounter"]) && ns.all Semantics.cellNameOK &&
  (match p.pgmCell with
   | some n => (Semantics.cellLeavesList p.config).any (fun l => l.1 == n && (l.2 == Srt.k || l.2 == c.pgmSort))
   | none => true) &&
  !p.config.isEmpty &&
  Semantics.cellIdsShapedList p.config &&
  (Semantics.cellCollSortsListR p.config).all (fun s => c.colls.any (·.sort == s)) &&
  p.cellSorts.isPrefixOf c.userSorts && p.cellCtors.isPrefixOf c.ctors &&
  p.cellSubsorts.isPrefixOf c.userSubsorts

/-- The presentation: the core's library is the union of the imported modules' (`libOf`) with the
definition's own token sorts (numbered from `nRegSorts`) after the modules' token sorts and its
own sorts hooked to a library carrier, the
imports increasing; rule attributes inert; a rule's or an equation's priority 50 or 200 unless
written `priority{}("n")`, or, for an equation written as a symbol-overload axiom
(`ClausePres.overload`), `aside` and of priority 0, which that attribute gives; variable names
distinct; the cell tree as `cellsOK` says. -/
def Presentation.ok (p : Presentation) (c : Semantics) : Bool :=
  (let l := libOf p.imports
   c.lib == { l with tokenSorts := l.tokenSorts ++ c.lib.tokenSorts.filter (fun s => decide (nRegSorts ≤ s)),
                     carriers := c.lib.carriers.filter fun p => decide (nRegSorts ≤ p.1) }) &&
  sortedNat p.imports &&
  p.rules.all (fun rp => rp.attrs.all inertRuleAttrs.contains && rp.argAttrs.all (inertArgAttrs.contains ·.1)) &&
  (withPres c.rules p.rules).all (fun (r, rp) => rp.prioAttr || r.prio == 50 || r.prio == 200) &&
  ((withPres c.fns p.fns).all fun (f, fp) =>
    (withPres f.clauses fp.clauses).all fun (cl, cp) =>
      namesFor cl.vars.length cp.names && namesFor cl.vars.length cp.exclNames &&
      (cp.prioAttr || cl.prio == 50 || cl.prio == 200 || (cp.overload.isSome && cl.aside && cl.prio == 0))) &&
  ((withPres c.rules p.rules).all fun (r, rp) => namesFor r.vars.length rp.names) &&
  p.cellsOK c

end KCore
