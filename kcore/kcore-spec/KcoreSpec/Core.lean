/-
  KCore. The semantic core of a definition (KCORE-SPEC.md §2). Frozen layer: this is what `Step`
  reads.

  A `Semantics` holds:
  - **Sorts and symbols, as numbers** (`Srt`, `Sym`). The builtin registry has fixed numbers
    (FixedSignature.lean). A definition's own sorts are numbered from `nRegSorts` in the order
    `ownSorts` lists them; its own symbols from `nRegSyms`: first the predicate `isX` of each
    own sort, in the same order (`predOf`), then its constructors, its functions, its
    parameter symbols and its overloading symbols (`ownSyms`). `wf` checks the numbering (`idsOK`). The names (`sortNames`,
    `symNames`) are read only by `emit` and the matching-logic translation; nothing that decides
    or steps compares them.
  - **Typed literals** (`Lit`): an Int, a Bool, a token's text, or a Float of K's format `(p, e)`
    as its IEEE 754 encoding (FloatDomain.lean).
  - **Subsorts**, a strict partial order over the user's and the library's sorts (DefinitionWf):
    `syntax KResult ::= Int` beside `syntax AExp ::= Int` (KCORE-SPEC.md §3). The builtin library
    the definition imports (`lib`) puts its sorts below KItem and adds its subsorts and
    constructors.
  - **Functions** (`Fn`), with their clauses, each with a priority (`Clause.prio`, smaller
    first: 50 without an attribute, 200 for `[owise]`, n for `[priority(n)]`), and `total` for a
    function declared `[total]` (its KORE symbol carries `functional` and a functional axiom).
    The order of the clauses carries no meaning. The generated `isX` sort predicates are functions
    of the definition too (`sortPreds`): kompile writes their equations into every definition, and
    `strict`'s heating and cooling rules call `isKResult` in their `requires`.
  - **Rules**, each with a priority (`Rule.prio`, smaller first): 50 without an attribute, 200 for
    `[owise]`, n for `[priority(n)]`, K's documented defaults. Step.lean gives them their meaning
    (KCORE-SPEC.md §4).
  - **The configuration sort** `topCellSort`, a registry sort: the sort the rules rewrite. A
    configuration's cells are ordinary constructors of ordinary sorts (`<k>`, of `KCell`, takes a
    `K`), its `XCell < XCellOpt` ordinary subsorts; the cell tree they come from is presentation
    (Definition.lean), read by `emit` and the tie only.
  - **Parameter symbols** (`params`): hooked symbols whose hook has no meaning in Lean, and their
    interpretation (`hooks`), for which every theorem holds.
  - **Overloading symbols** (`ovls`): symbols that overload others (`OvlSig`); their applications
    denote normal forms (`Semantics.norm`, Value.lean).
-/
import KcoreSpec.FixedSignature
import KcoreSpec.NatMap

set_option autoImplicit false

namespace KCore

/-- A literal: an Int, a Bool, the text of a token (`Id`, `String`, `KConfigVar`), or a Float. -/
inductive Lit where
  | int (i : Int)
  | bool (b : Bool)
  | tok (s : String)
  /-- A Float of precision `p` (significand bits with the implicit one) and exponent width `e`:
  its IEEE 754 interchange encoding `bits` (sign, biased exponent, trailing significand), a NaN as
  the one canonical NaN (`KFloat.ok`, FloatDomain.lean). -/
  | float (p e bits : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A term of a clause or a rule: a variable, an application, an injection between sorts, an
alias (`p #as V`), or a domain value. `app` applies a constructor, a
function of the definition, or an interpreted hooked symbol (FixedSignature.lean). -/
inductive Term where
  | var (i : Nat)
  | app (f : Sym) (args : List Term)
  | inj (a b : Srt) (t : Term)
  | as (t : Term) (i : Nat)
  | dv (s : Srt) (lit : Lit)
  deriving Repr, Inhabited

/-- A ground value (Value.lean has its order, its sorts and its laws). -/
inductive GroundTerm where
  | ctor (f : Sym) (args : List GroundTerm)
  | inj (a b : Srt) (t : GroundTerm)
  | dv (s : Srt) (lit : Lit)
  /-- a finite map of the collection sort `s`: entries `(key, value)`, keys strictly increasing
  in `GroundTerm.cmp`. The sort tells apart maps of different collection sorts with the same
  entries (the empty `Map` and the empty `AccountCellMap`). -/
  | map (s : Srt) (es : List (GroundTerm × GroundTerm))
  /-- a finite set of the collection sort `s`: elements strictly increasing in `GroundTerm.cmp` -/
  | set (s : Srt) (es : List GroundTerm)
  /-- a finite list of the collection sort `s`: its elements in order -/
  | list (s : Srt) (es : List GroundTerm)
  deriving Repr, Inhabited

/-- The kind of a collection sort. -/
inductive CollKind where
  | map
  | set
  | list
  /-- a range map: a `GroundTerm.map` whose keys are `Range` terms of its maximal intervals -/
  | rangeMap
  deriving Repr, DecidableEq, Inhabited

/-- A collection sort: a sort whose values are finite maps from `key` to `val`, finite sets of
`key`, or finite lists of `key` (a map has a value sort, a set or a list has none: `val` is `none`
for them). K declares one with a hooked sort
(`hook(MAP.Map)`, `hook(SET.Set)`, `hook(LIST.List)`) and its unit, element and concatenation
symbols; a cell of multiplicity `*` declares one (`AccountCellMap`, from its key cell's sort to
its own sort). -/
structure CollSig where
  sort : Srt
  kind : CollKind
  key : Srt
  val : Option Srt := none
  /-- its unit (`.Map`, `.AccountCellMap`), element (`|->`, `AccountCellMapItem`) and
  concatenation (`_Map_`, `_AccountCellMap_`) symbols, which build and print its values -/
  unit : Sym
  elem : Sym
  concat : Sym
  deriving Repr, DecidableEq, Inhabited

/-- A condition of a rule or a clause: a matching-logic predicate over terms. Each form is the
KORE connective of the same name at the sentence's sort, its arguments terms. A binder binds the
next indices after the variables in scope: the sentence's, then those of each enclosing binder. -/
inductive Cond where
  | top | bot
  | not (p : Cond) | and (p q : Cond) | or (p q : Cond) | implies (p q : Cond)
  /-- `\ceil{s,_}(t)`: t has a value -/
  | ceil (s : Srt) (t : Term)
  /-- `\equals{s,_}(t, u)`: both undefined, or both defined with one value -/
  | equals (s : Srt) (t u : Term)
  /-- `\in{s,_}(t, u)`: both defined with one value -/
  | mem (s : Srt) (t u : Term)
  /-- `\exists ȳ. \in{s,_}(t, p) ∧ body`: t's value matches the pattern p under some values of
  the variables `ys`, and body holds there -/
  | exMatch (ys : List Srt) (s : Srt) (p t : Term) (body : Cond)
  /-- `\exists y:s. body` -/
  | ex (s : Srt) (body : Cond)
  /-- `\forall y:s. body` -/
  | all (s : Srt) (body : Cond)
  deriving Repr, Inhabited

/-- The condition is `\top`. -/
def Cond.isTop : Cond → Bool
  | .top => true
  | _ => false

/-- A clause `f(p₁, …, pₙ) = rhs requires req ensures ens`, with its priority (smaller first; 50
by default, 200 for `[owise]`); `none` for a `requires` or an `ensures` that is `\top`. The
`ensures` is part of the right side, `f(p̄) = rhs ∧ (ens = true)`: it is not read by whether the
clause applies, and where the clause decides and `ens` is not `true` the function has no value
there. A clause applies where no clause of a smaller priority does; clauses of one priority are
unordered. -/
structure Clause where
  vars : List Srt
  pats : List Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat := 50
  /-- an equation no `[owise]` premise negates (`non-executable`): it blocks no clause -/
  aside : Bool := false
  /-- the variables the right side binds by `\exists`, indices of `vars` -/
  exs : List Nat := []
  /-- a predicate of the premise: the clause applies where it holds -/
  pre : Cond := .top
  /-- a predicate of the right side: the clause gives its value where it holds -/
  post : Cond := .top
  deriving Repr

/-- A function of the definition. `total`: declared `[total]` (kompile writes `functional` and
`total` on the symbol and the axiom `∃y. f(x̄) = y`); `wf` does not refuse one `totalOK` does not
confirm: it is in `totalObligations` (KCORE-SPEC.md §2.5). Without it the function may be partial: where no
clause applies, it has its rest (`Eval.rest`, the interpretation's value, `Semantics.fnRest`). The
order of `clauses` carries no meaning: the reader keeps the file's, so that printing is stable. -/
structure Fn where
  label : Sym
  args : List Srt
  result : Srt
  clauses : List Clause
  total : Bool := false
  deriving Repr

/-- A rewrite rule `lhs => rhs requires req ensures ens` between configurations (`none` for a
`requires` or an `ensures` that is `\top`), with its priority (smaller first; 50 by default, 200
for `[owise]`). -/
structure Rule where
  vars : List Srt
  lhs : Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat
  /-- the variables the right side binds by `\exists` (`?X`), in the text's order: indices of `vars` -/
  exs : List Nat := []
  /-- a predicate of the left side: the rule applies where it holds -/
  pre : Cond := .top
  /-- a predicate of the right side, under the binder of `exs`: the rule gives its step where it holds -/
  post : Cond := .top
  deriving Repr

/-- The library's collection sorts: `Map` from KItem to KItem, `Set` and `List` of KItem, and
`RangeMap` from Range to KItem. -/
def builtinColls : List CollSig :=
  [⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩,
   ⟨Srt.set, .set, Srt.kitem, none, setUnit, setElem, setConcat⟩,
   ⟨Srt.list, .list, Srt.kitem, none, listUnit, listElem, listConcat⟩,
   ⟨Srt.rangeMap, .rangeMap, Srt.range, some Srt.kitem, rmUnit, rmElem, rmConcat⟩]

/-- An overloading symbol: a symbol of K's overload sets declared `anywhere` and not a constructor
(`f(lift ā) = lift (g(ā))` for each symbol g it overloads). Its signature, and the symbols it
overloads (`over`: constructors, overloading symbols listed before it in `Semantics.ovls`, or
functions of the definition).
A term `f(v̄)` denotes the value `Semantics.norm f v̄` (Value.lean): the raw application where no
overload covers v̄, otherwise the overloaded symbol's value, injected into f's result sort; at
arguments a function it overloads covers, it denotes that function's value, injected likewise. -/
structure OvlSig where
  sig : CtorSig
  over : List Sym
  deriving Repr, DecidableEq, Inhabited

/-- A parameter symbol (ARCHITECTURE.md §3.3): a hooked symbol of the definition.
`impl = some g`: its hook is the registry's hook g, whose meaning it has (`Hooks.lean`);
`impl = none`: no registry interprets its hook, so its meaning is a parameter of the semantics
(`Semantics.hooks`), and every theorem stated for all `hooks` holds whatever it is. -/
structure ParamSig where
  sig : CtorSig
  impl : Option Sym := none
  /-- an open generator: a symbol the text declares total, lists among its result sort's
  generators and gives no constructor axiom -/
  raw : Bool := false
  /-- the text holds the associativity axiom of this symbol -/
  assoc : Bool := false
  /-- the text holds the idempotence axiom of this symbol -/
  idem : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- An interpretation of the parameter symbols: for symbol f and argument values, a value or
undefined (`none`). Evaluation reads it only through `Semantics.paramVal`, which keeps a value
only when it has the symbol's declared result sort: a matching-logic model of a symbol
`f : s₁ … sₙ → s` takes values in the carrier of s, so every model is such an H, and an ill-sorted
answer of an arbitrary H is read as undefined rather than assumed away by a hypothesis. -/
structure HookParams where
  app : Sym → List GroundTerm → Option GroundTerm

/-- No parameter symbol is defined anywhere: the interpretation the parsed data carries. -/
def HookParams.none : HookParams := ⟨fun _ _ => Option.none⟩

instance : Inhabited HookParams := ⟨HookParams.none⟩

/-- The data printed of a `Semantics` (its `Repr`, which the ties compare and the literals are
printed with) does not include the interpretation of its parameters: a literal elaborates with the
default, `HookParams.none`. -/
instance : Repr HookParams := ⟨fun _ _ => "KCore.HookParams.none"⟩

structure Semantics where
  /-- the builtin library: the union of the imported modules' sorts, subsorts and constructors
  (Builtins.lean) -/
  lib : Lib
  /-- the names of the definition's own sorts (numbered from `nRegSorts`), without `Sort` -/
  sortNames : List String
  /-- the names of the definition's own symbols (numbered from `nRegSyms`) -/
  symNames : List String
  /-- the definition's sorts below KItem besides the library's: its own (numbered from
  `nRegSorts`) and the registry's generated configuration sorts it has (`genSorts`) -/
  userSorts : List Srt
  /-- the definition's constructors besides the fixed text's and the library's: its own and the
  registry's generated configuration constructors it has (`genSyms`), each with its argument and
  result sorts -/
  ctors : List CtorSig
  fns : List Fn
  /-- the declared subsorts besides the library's -/
  userSubsorts : List (Srt × Srt)
  /-- the sort of `$PGM` (a user sort, `K` or `KItem`) -/
  pgmSort : Srt
  rules : List Rule
  /-- the parameter symbols: the imported modules' symbols no hook interprets (registry numbers),
  then the definition's own hooked symbols (numbered after its functions) -/
  params : List ParamSig := []
  /-- the definition's own collection sorts (cell collections), besides the library's `Map`,
  `Set`, `List` and `RangeMap` (`builtinColls`) -/
  colls : List CollSig := []
  /-- the overloading symbols (`OvlSig`), each overloaded symbol that is itself one listed before
  it -/
  ovls : List OvlSig := []
  /-- the meaning of the parameter symbols that no registry hook interprets. Theorems about
  a definition with parameters are stated for every `hooks` (`withHooks`); no decided condition
  reads this field, so a condition decided on the parsed data holds for every interpretation by
  `rfl` (`*_withHooks` lemmas, Exec.lean and Determinism.lean). -/
  hooks : HookParams := HookParams.none
  deriving Repr

/-- The same definition with its parameter symbols interpreted by H. -/
def Semantics.withHooks (c : Semantics) (H : HookParams) : Semantics := { c with hooks := H }

/-! ## The signature the core induces -/

def insertBy {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if key a < key b then a :: b :: bs else b :: insertBy key a bs

def sortBy {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (l : List α) : List α :=
  l.foldr (insertBy key) []

/-- One round of the subsort closure: the pairs found, then each composed with the declared pairs
`base`, less those already found. Successors and membership go through tries of the pairs grouped by
their first sort (`NatMap.group`), so a round costs about the number of pairs found times their
successors, not the product of the two lists. -/
def closureStep (base acc : List (Srt × Srt)) : List (Srt × Srt) :=
  let succ := NatMap.group base
  let seen := NatMap.group acc
  acc ++ acc.flatMap fun (a, b) => (NatMap.succs succ b).filterMap fun d =>
    if (NatMap.succs seen a).contains d then none else some (a, d)

/-- At most k rounds, stopping at the first that adds nothing. -/
def closeRounds (base : List (Srt × Srt)) : Nat → List (Srt × Srt) → List (Srt × Srt)
  | 0, acc => acc
  | k + 1, acc =>
    let acc' := closureStep base acc
    if acc'.length == acc.length then acc else closeRounds base k acc'

/-- The predicate `isX` of a sort below KItem: the registry's (`none` for a registry sort that has
none), or, for the definition's own sort numbered `nRegSorts + i`, its symbol `nRegSyms + i`. -/
def predOf (X : Srt) : Option Sym := if X < nRegSorts then regPred X else some (X - nRegSorts + nRegSyms)

/-- The registry's sorts of the generated configuration: the top cell's, its fragment's, the
counter cell's and its `Opt` sort. A definition's sorts are its own or these (`idsOK`). -/
def genSorts : List Srt := [Srt.top, Srt.topFrag, Srt.counter, Srt.counterOpt]

/-- The registry's constructors of the generated configuration: `<generatedTop>`, its fragment,
`<generatedCounter>` and `noGeneratedCounterCell`. A definition's constructors are its own or
these (`idsOK`). -/
def genSyms : List Sym := [topLabel, topFragLabel, counterLabel, noCounter]

namespace Semantics
variable (c : Semantics)

def sortsBelowKItem : List Srt := c.lib.sortsBelowKItem ++ c.userSorts

/-- The definition's own sorts in their numbering: those of `userSorts` numbered from
`nRegSorts`. -/
def ownSorts : List Srt := c.userSorts.filter fun s => decide (nRegSorts ≤ s)

/-- The first number of the definition's own symbols after its sort predicates. -/
def symBase : Nat := nRegSyms + c.sortNames.length

/-- The definition's own symbols but the sort predicates, in their numbering (the imported
modules' parameter symbols are the registry's): its constructors, functions, parameters and
overloading symbols. -/
def ownSyms : List Sym :=
  (c.ctors.map (·.name)).filter (fun f => decide (nRegSyms ≤ f)) ++ c.fns.map (·.label) ++
    (c.params.filter fun k => decide (nRegSyms ≤ k.sig.name)).map (·.sig.name) ++ c.ovls.map (·.sig.name)

/-- The declared subsorts between the user's and the library's sorts (the KORE's `[subsort]`
axioms: kompile writes the declared pairs only, `Int < Value`, `Value < Expr`), closed under
transitivity (`Int < Expr`, which the rules use as `inj{Int,Expr}`): rounds of composition with the
declared pairs, until a round adds nothing; one round per declared pair suffices (`closureStep`,
`closeRounds`; NamesApart.lean proves the result transitive). -/
def declaredClosure : List (Srt × Srt) :=
  let base := c.userSubsorts ++ c.lib.subsorts
  closeRounds base base.length base

def subsorts : List (Srt × Srt) :=
  c.declaredClosure ++ c.sortsBelowKItem.map (·, Srt.kitem)

def le (a b : Srt) : Bool := a == b || c.subsorts.contains (a, b)

/-- The generated sort predicates: `isK(K) = true`; `isKItem(kseq(I, dotk)) = true`, otherwise
`false`; for each sort X below KItem with a predicate (`predOf`), `isX(kseq(inj{X,KItem}(V), dotk))
= true`, otherwise `false`. "Otherwise" is a clause of priority 200 over a variable of sort K.
These are the equations kompile writes for every definition (Emit.lean writes those of
`userSorts`; the fixed text holds the library's), read as functions. -/
def sortPreds : List Fn :=
  let tt := Term.dv Srt.bool (.bool true)
  let ff := Term.dv Srt.bool (.bool false)
  let dk := Term.app dotk []
  let otherwise : Clause := { vars := [Srt.k], pats := [.var 0], req := none, rhs := ff, ens := none, prio := 200 }
  [⟨isK, [Srt.k], Srt.bool, [{ vars := [Srt.k], pats := [.var 0], req := none, rhs := tt, ens := none }], true⟩,
   ⟨isKItem, [Srt.k], Srt.bool,
    [{ vars := [Srt.kitem], pats := [.app kseq [.var 0, dk]], req := none, rhs := tt, ens := none }, otherwise], true⟩] ++
  c.sortsBelowKItem.filterMap fun X => (predOf X).map fun p =>
    ⟨p, [Srt.k], Srt.bool,
      [{ vars := [X], pats := [.app kseq [.inj X Srt.kitem (.var 0), dk]], req := none, rhs := tt, ens := none },
        otherwise], true⟩

/-- The functions evaluation reads: the user's, then the sort predicates. -/
def allFns : List Fn := c.fns ++ c.sortPreds

/-- All constructors: the fixed text's, the library's, then the definition's. -/
def ctorSigs : List CtorSig := fixedCtors ++ c.lib.ctors ++ c.ctors

/-- The overloading symbols' signatures. -/
def ovlSigs : List CtorSig := c.ovls.map (·.sig)

/-- The overloading symbol f's declaration (the first of that number). -/
def lookupOvl (f : Sym) : Option OvlSig := c.ovls.find? (·.sig.name == f)

/-- The collection sorts: the library's `Map`, `Set` and `List` (of `KItem`) and `RangeMap` (from
`Range` to `KItem`), then the definition's own (`colls`). -/
def allColls : List CollSig := builtinColls ++ c.colls

/-- The collection sort `s`, if it is one. -/
def collOf (s : Srt) : Option CollSig := c.allColls.find? (·.sort == s)

/-! ## Names (read by `emit` and the translation only) -/

def sortName (s : Srt) : String :=
  if s < nRegSorts then regSortNames.getD s "" else c.sortNames.getD (s - nRegSorts) ""

def symName (f : Sym) : String :=
  if f < nRegSyms then regSymNames.getD f "" else c.symNames.getD (f - nRegSyms) ""

end Semantics

/-- The signature of f among `heads` (the first of that number), by the trie of their numbers
(NatMap.lean): about log₂ of the number of symbols steps, not one comparison per entry. -/
def lookupSig (heads : List CtorSig) (f : Sym) : Option CtorSig :=
  (NatMap.ofList (heads.map fun k => (k.name, k))).find f

/-- `lookupSig` is the list's first entry of the number. -/
theorem lookupSig_eq (heads : List CtorSig) (f : Sym) : lookupSig heads f = heads.find? (·.name == f) := by
  rw [lookupSig, NatMap.find_ofList, List.find?_map]
  simp only [Function.comp_def]
  cases heads.find? (·.name == f) <;> rfl

/-- The function-overloaded symbols: the overloading symbols one of whose own overloads (`over`)
is the label of a function of `c.fns`. -/
def Semantics.fnOvlSyms (c : Semantics) : List Sym :=
  (c.ovls.filter fun o => o.over.any fun f => c.fns.any (·.label == f)).map (·.sig.name)

end KCore
