/-
  Hand-built semantics with open generators (`ParamSig.raw`), one per text, for the checks of
  CN-4 §4.7 (the reader refuses an open generator, `RefusalReason.openGenerator`, so these are
  built by hand). No expectation is stated here; each namespace checks only that its numbering is
  the one `idsOK` asks and that `lookupOpen` finds each open generator and no constructor. Run from
  the package root: `lake env lean -j1 test/OpenGenSems.lean`. Kernel-checked.

  Each semantics has the configuration `<k> K </k>` with the generated counter (as
  `Faithful.UndefRhsWitness`), its own sorts numbered `KCell`, `KCellOpt`, then the text's; its own
  symbols the sorts' predicates, then `<k>`, `noKCell`, the text's constructors, its functions,
  its open generators (the order `idsOK` checks). A sort's `project:X` function, which no sentence
  read here uses, is left out; its `isX` is `Semantics.sortPreds`'.

  Texts (lane P's fixtures, `test/constructs/fixtures/<name>/kore.txt`, K 7.1.337):
  - `CommCtor`, e2-comm-ctor: `syntax Exp ::= "x" | Exp "&" Exp [symbol(and), comm] |
    Exp "|" Exp [symbol(or), assoc]`. `and` raw, no law; `or` raw, `assoc`.
  - `OpenRule`, e2-open-rule: the K text of CN-2 §5 (`Exp ::= "x" | "y" | Exp "&" Exp [comm]`,
    `syntax Bool ::= same(Exp, Exp) [function]`, `rule same(A, B) => A ==K B`,
    `rule <k> go => x & y </k>`). PROVISIONAL: no kompiled text of it exists (no fixture
    directory). Not backed by a sentence: `go`'s production (taken as `syntax KItem ::= "go"`,
    a constructor of KItem), `same`'s clause shape (`==K` of the one-item sequences
    `kseq(inj{Exp,KItem}(A), dotk)`, the form kompile writes for `==K` at a sort below KItem), the
    rule's cell form (the top cell with the counter cell as a variable, the form of e2-open-mixed's
    `kore.txt:61`), and `and`'s declaration (taken as e2-comm-ctor's `and`: `functional`, no
    `constructor`, no `comm` attribute, no axiom of commutativity).
  - `IdemCtor`, e2-idem-ctor: `syntax Exp ::= "x" | "y" | Exp "|" Exp [idem, symbol(or)]`. `or` raw,
    `idem` (V7 case 2: the symbol is no constructor and the idempotence axiom is written).
  - `OpenMixed`, e2-open-mixed: `syntax A ::= "x" | "y"`, `syntax B ::= A "&" A [comm, symbol(and)]`,
    `syntax KItem ::= c(B) | d(A)`. `and : A A → B` raw, no law. The text's rule
    `<k> c(X & Y) => d(X) </k>` binds variables under the open generator (the shape
    `openGeneratorPattern`): it is `ruleCD`, not among the semantics' rules.
  The band text e2-band-ctor is `test/BandSem.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.OpenGenSems

open KCore

/-- The configuration's sorts: the top cell's, its fragment's, `KCell`, `KCellOpt` and the
counter's. -/
def ogCellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
/-- The configuration's constructors, with `<k>` numbered `b` and `noKCell` `b + 1`. -/
def ogCellCtors (b : Sym) : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨b, [Srt.k], nRegSorts⟩, ⟨b + 1, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def ogCellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-! ## e2-comm-ctor

What the text states of its two open generators (`kore.txt`; line numbers of that file):
- `and`: declared `symbol Lbland{}(SortExp{}, SortExp{}) : SortExp{} [functional{}(), …]` (:6), no
  `constructor`, `injective`, `function` or `comm`; its `functional` axiom (:18); no axiom of
  commutativity.
- `or`: declared likewise (:10), no `assoc` attribute; its `functional` axiom (:24); the
  associativity axiom `or(or(K1,K2),K3) = or(K1,or(K2,K3))` (:22, `[assoc{}()]`).
- Exp's no-junk axiom (:28): `∃X0 X1. and(X0,X1) ∨ ∃X0 X1. or(X0,X1) ∨ x() ∨ ⊥`: both open
  generators are listed beside the constructor `x`.
- No no-confusion axiom is written for Exp at all (x is its one constructor): no axiom separates
  an `and` or `or` application from `x()`, from each other, or states either injective.
-/
namespace CommCtor

def exp : Srt := nRegSorts + 2
def kS : Sym := nRegSyms + 3
def xS : Sym := nRegSyms + 5
def andS : Sym := nRegSyms + 6
def orS : Sym := nRegSyms + 7

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }
def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, assoc := true }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Exp"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisExp", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx",
      "Lbland", "Lblor"]
    userSorts := ogCellSorts ++ [exp]
    ctors := ogCellCtors kS ++ [⟨xS, [], exp⟩]
    fns := []
    userSubsorts := ogCellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [andP, orP] }

theorem idsOK : c.idsOK = true := by decide +kernel
theorem lookupOpen_ok : c.lookupOpen andS = some andP ∧ c.lookupOpen orS = some orP ∧
    c.lookupOpen xS = none := by decide +kernel

end CommCtor

/-! ## e2-open-rule (provisional: no kompiled text)

What CN-2 §5 states of the text, read at e2-comm-ctor's `and` (the same production): `and` total
(`functional`), listed in Exp's no-junk axiom beside `x` and `y`; no law; the no-confusion axiom
`¬(x() ∧ y())` (as e2-idem-ctor's :26, the two nullary constructors) names no open generator. -/
namespace OpenRule

def exp : Srt := nRegSorts + 2
def kS : Sym := nRegSyms + 3
def xS : Sym := nRegSyms + 5
def yS : Sym := nRegSyms + 6
def goS : Sym := nRegSyms + 7
def sameS : Sym := nRegSyms + 8
def andS : Sym := nRegSyms + 9

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }

/-- The one-item sequence `kseq(inj{Exp,KItem}(t), dotk)`. -/
def item (t : Term) : Term := .app kseq [.inj exp Srt.kitem t, .app dotk []]

/-- `same(A, B) => A ==K B`. -/
def clSame : Clause := ⟨[exp, exp], [.var 0, .var 1], none, .app kEq [item (.var 0), item (.var 1)], none, 50,
  false, [], .top, .top⟩
def fnSame : Fn := ⟨sameS, [exp, exp], Srt.bool, [clSame], false⟩

/-- `<k> go => x & y </k>`: the top cell with the counter cell a variable. -/
def ruleGo : Rule :=
  { vars := [Srt.counter]
    lhs := .app topLabel [.app kS [.app kseq [.app goS [], .app dotk []]], .var 0]
    req := none
    rhs := .app topLabel [.app kS [item (.app andS [.app xS [], .app yS []])], .var 0]
    ens := none
    prio := 50 }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Exp"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisExp", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx", "Lbly",
      "Lblgo", "Lblsame", "Lbland"]
    userSorts := ogCellSorts ++ [exp]
    ctors := ogCellCtors kS ++ [⟨xS, [], exp⟩, ⟨yS, [], exp⟩, ⟨goS, [], Srt.kitem⟩]
    fns := [fnSame]
    userSubsorts := ogCellSubsorts
    pgmSort := Srt.k
    rules := [ruleGo]
    params := [andP] }

theorem idsOK : c.idsOK = true := by decide +kernel
theorem lookupOpen_ok : c.lookupOpen andS = some andP ∧ c.lookupOpen xS = none ∧
    c.lookupOpen sameS = none := by decide +kernel

end OpenRule

/-! ## e2-idem-ctor

What the text states of its open generator (`kore.txt`):
- `or`: declared `symbol Lblor{}(SortExp{}, SortExp{}) : SortExp{} [functional{}(), idem{}(), …]`
  (:8): no `constructor`, `injective` or `function`, the attribute `idem` kept on the declaration;
  its `functional` axiom (:22); the idempotence axiom `or(K,K) = K` (:20, `[idem{}()]`).
- Exp's no-junk axiom (:30): `∃X0 X1. or(X0,X1) ∨ x() ∨ y() ∨ ⊥`.
- The one no-confusion axiom (:26) is `¬(x() ∧ y())`: it names no `or` application. No axiom
  separates `or(…)` from `x()` or `y()`, or states `or` injective.
-/
namespace IdemCtor

def exp : Srt := nRegSorts + 2
def kS : Sym := nRegSyms + 3
def xS : Sym := nRegSyms + 5
def yS : Sym := nRegSyms + 6
def orS : Sym := nRegSyms + 7

def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, idem := true }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Exp"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisExp", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx", "Lbly",
      "Lblor"]
    userSorts := ogCellSorts ++ [exp]
    ctors := ogCellCtors kS ++ [⟨xS, [], exp⟩, ⟨yS, [], exp⟩]
    fns := []
    userSubsorts := ogCellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [orP] }

theorem idsOK : c.idsOK = true := by decide +kernel
theorem lookupOpen_ok : c.lookupOpen orS = some orP ∧ c.lookupOpen xS = none ∧ c.lookupOpen yS = none := by
  decide +kernel

end IdemCtor

/-! ## e2-open-mixed

What the text states of its open generator (`kore.txt`):
- `and`: declared `symbol Lbland{}(SortA{}, SortA{}) : SortB{} [functional{}(), …]` (:8), no
  `constructor`, `injective`, `function` or `comm`; its `functional` axiom (:30); no law axiom.
- B's no-junk axiom (:54) is `∃X0 X1. and(X0,X1) ∨ ⊥`: `and` is B's only generator, B has no
  constructor. A's (:52) is `x() ∨ y() ∨ ⊥`.
- No no-confusion axiom names `and`: A's (:48) is `¬(x() ∧ y())`; KItem's are `c` injective (:34),
  `d` injective (:40) and `¬(c(X0) ∧ d(Y0))` (:36). `c`'s injectivity is stated at every element
  of B, so at `and` applications through `c` only: `c(and(a,b)) = c(and(a',b'))` gives
  `and(a,b) = and(a',b')`, nothing about `a, b` and `a', b'`.
- The rule (:59-61) has `c(and(VarX:SortA, VarY:SortA))` in its left side.
-/
namespace OpenMixed

def sA : Srt := nRegSorts + 2
def sB : Srt := nRegSorts + 3
def kS : Sym := nRegSyms + 4
def xS : Sym := nRegSyms + 6
def yS : Sym := nRegSyms + 7
def cS : Sym := nRegSyms + 8
def dS : Sym := nRegSyms + 9
def andS : Sym := nRegSyms + 10

def andP : ParamSig := { sig := ⟨andS, [sA, sA], sB⟩, raw := true }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "A", "B"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisA", "LblisB", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx",
      "Lbly", "Lblc", "Lbld", "Lbland"]
    userSorts := ogCellSorts ++ [sA, sB]
    ctors := ogCellCtors kS ++ [⟨xS, [], sA⟩, ⟨yS, [], sA⟩, ⟨cS, [sB], Srt.kitem⟩, ⟨dS, [sA], Srt.kitem⟩]
    fns := []
    userSubsorts := ogCellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [andP] }

/-- The text's rule `<k> c(X & Y) => d(X) </k>` (`kore.txt:59-61`), the shape `openGeneratorPattern`:
not among `c`'s rules. -/
def ruleCD : Rule :=
  { vars := [sA, sA, Srt.counter]
    lhs := .app topLabel [.app kS [.app kseq [.app cS [.app andS [.var 0, .var 1]], .app dotk []]], .var 2]
    req := none
    rhs := .app topLabel [.app kS [.app kseq [.app dS [.var 0], .app dotk []]], .var 2]
    ens := none
    prio := 50 }

theorem idsOK : c.idsOK = true := by decide +kernel
theorem lookupOpen_ok : c.lookupOpen andS = some andP ∧ c.lookupOpen xS = none ∧ c.lookupOpen cS = none := by
  decide +kernel

end OpenMixed

/-! ## `genWf`, and the two values `values_apart` separates

`Faithful.genWf` holds of each semantics (each open generator's sort is flat). At
`HookParams.none`, which leaves every application raw, an open generator's application at values
and a nullary constructor of its sort are two values of that sort that `cmp` tells apart: the
two values `Faithful.values_apart` is applied to in `ctor_back`'s open case. OpenMixed's open
generator `and` has the sort B, which has no constructor, so there is no such pair there. -/

theorem genWf_ok : Faithful.genWf CommCtor.c = true ∧ Faithful.genWf OpenRule.c = true ∧
    Faithful.genWf IdemCtor.c = true ∧ Faithful.genWf OpenMixed.c = true := by decide +kernel

/-- An open generator's result sort is a constructor sort, and no sort of `shapeSorts ++
litShapeSorts`. -/
example : CommCtor.exp ∈ Faithful.consSorts CommCtor.c :=
  Faithful.genWf_raw_cons genWf_ok.1 (k := CommCtor.andP) (by decide +kernel) rfl
example : (shapeSorts ++ litShapeSorts).contains CommCtor.andP.sig.result = false :=
  shapes_open' (c := CommCtor.c) (by decide +kernel) (by decide +kernel) rfl

theorem apart_comm :
    (CommCtor.c.withHooks HookParams.none).sortOf (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) =
      some CommCtor.exp ∧
    (CommCtor.c.withHooks HookParams.none).sortOf (.ctor CommCtor.xS []) = some CommCtor.exp ∧
    GroundTerm.cmp (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) (.ctor CommCtor.xS []) != .eq := by
  decide +kernel

theorem apart_rule :
    (OpenRule.c.withHooks HookParams.none).sortOf (.ctor OpenRule.andS [.ctor OpenRule.xS [], .ctor OpenRule.yS []]) =
      some OpenRule.exp ∧
    (OpenRule.c.withHooks HookParams.none).sortOf (.ctor OpenRule.xS []) = some OpenRule.exp ∧
    GroundTerm.cmp (.ctor OpenRule.andS [.ctor OpenRule.xS [], .ctor OpenRule.yS []]) (.ctor OpenRule.xS []) != .eq := by
  decide +kernel

theorem apart_idem :
    (IdemCtor.c.withHooks HookParams.none).sortOf (.ctor IdemCtor.orS [.ctor IdemCtor.xS [], .ctor IdemCtor.xS []]) =
      some IdemCtor.exp ∧
    (IdemCtor.c.withHooks HookParams.none).sortOf (.ctor IdemCtor.xS []) = some IdemCtor.exp ∧
    GroundTerm.cmp (.ctor IdemCtor.orS [.ctor IdemCtor.xS [], .ctor IdemCtor.xS []]) (.ctor IdemCtor.xS []) != .eq := by
  decide +kernel


/-! ### The values of an open generator (`Semantics.sortOf_open_iff`, `paramVal_raw_sorted`,
`paramVal_raw_keep`)

At CommCtor's `and`: under `HookParams.none` the application `and(x, x)` is a value of Exp and
`and`'s value there is that application; under `Hx`, which answers `x` at every application of
`and`, the interpretation does not leave `and(x, x)` raw, so it is no value, and `and`'s value there
is `x`, which has `and`'s result sort. -/

/-- The interpretation answering `x` at every application of CommCtor's `and`. -/
def Hx : HookParams := ⟨fun f _ => if f == CommCtor.andS then some (.ctor CommCtor.xS []) else none⟩

theorem open_value_none :
    (CommCtor.c.withHooks HookParams.none).sortOf (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) =
      some CommCtor.exp :=
  (Semantics.sortOf_open_iff (c := CommCtor.c.withHooks HookParams.none) (k := CommCtor.andP)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr ⟨by decide +kernel, by decide +kernel, rfl⟩

theorem open_value_Hx :
    (CommCtor.c.withHooks Hx).sortOf (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) = none := by
  cases h : (CommCtor.c.withHooks Hx).sortOf (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) with
  | none => rfl
  | some s =>
    have := ((Semantics.sortOf_open_iff (c := CommCtor.c.withHooks Hx) (k := CommCtor.andP)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).mp h).2.1
    exact absurd this (by decide +kernel)

theorem open_paramVal_none :
    (CommCtor.c.withHooks HookParams.none).paramVal CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []] =
      some (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) :=
  paramVal_raw_keep (c := CommCtor.c.withHooks HookParams.none) (k := CommCtor.andP) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)

theorem open_paramVal_Hx :
    (CommCtor.c.withHooks Hx).paramVal CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []] =
      some (.ctor CommCtor.xS []) :=
  (paramVal_raw_sorted (c := CommCtor.c.withHooks Hx) (k := CommCtor.andP) (by decide +kernel) rfl rfl).mpr
    ⟨rfl, by decide +kernel⟩


/-! ### `lawHooks` is admitted where H is (`libAdmitted_lawHooks_of`)

CommCtor has two open generators. Its open generators bear no registry number, and every value of a
sort the library's sentences read applies none (`shapesOK`, `floatShapeOK`), so `lawHooks c H` is
admitted wherever H is; at `HookParams.lib`, admitted in every semantics with `floatShapeOK`
(`libAdmitted_lib`), so is `lawHooks c HookParams.lib`, which differs from it at `and` and `or`. -/

theorem comm_reg : ∀ k ∈ CommCtor.c.params, k.raw = true → nRegSyms ≤ k.sig.name := by decide +kernel

theorem comm_lawLibRawFree : CommCtor.c.lawLibRawFree :=
  lawLibRawFree_of_shapes (by decide +kernel) (by decide +kernel) comm_reg

theorem comm_lawHooks_lib : (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)).libAdmitted :=
  libAdmitted_lawHooks_of comm_reg comm_lawLibRawFree HookParams.lib
    (libAdmitted_lib CommCtor.c (by decide +kernel))

example : (lawHooks CommCtor.c HookParams.lib).app CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []] =
      some (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) ∧
    HookParams.lib.app CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []] = none := by
  decide +kernel

/-! ### Where the reason fails: an open generator of Endianness

`genWf` admits an open generator whose result sort is the library's Endianness (a constructor sort:
BYTES' `LE` and `BE`, both nullary). Bytes2Int takes an Endianness argument, and its `functional`
sentence (domains.md 2082) is read at every argument list of its sorts (`silentTotal`). Under
`HookParams.none` the raw application `myE(1)` is a value of Endianness, so a value of a sort the
library's sentences read applies a raw parameter: `lawLibRawFree` is false, and `enumShapesOK`
refuses the semantics. -/
namespace EndRaw

def myE : Sym := nRegSyms + 20

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool, Srt.bytes, Srt.endianness, Srt.signedness]
             ctors := [⟨littleEndianBytes, [], Srt.endianness⟩, ⟨bigEndianBytes, [], Srt.endianness⟩,
               ⟨signedBytes, [], Srt.signedness⟩, ⟨unsignedBytes, [], Srt.signedness⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := ogCellSorts
    ctors := ogCellCtors (nRegSyms + 2)
    fns := []
    userSubsorts := ogCellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [{ sig := ⟨myE, [Srt.int], Srt.endianness⟩, raw := true }] }

theorem genWf_admits : Faithful.genWf c = true ∧ Srt.endianness ∈ Faithful.consSorts c ∧
    c.enumShapesOK = false ∧
    (c.withHooks HookParams.none).sortOf (.ctor myE [int 1]) = some Srt.endianness ∧
    c.rawFree (.ctor myE [int 1]) = false := by
  decide +kernel

theorem not_lawLibRawFree : ¬ c.lawLibRawFree := fun h => by
  have := h HookParams.none (.ctor myE [int 1]) Srt.endianness (by decide) genWf_admits.2.2.2.1
  rw [genWf_admits.2.2.2.2] at this
  cases this

/-- The same semantics with the open generator numbered in order (`idsOK`; `c` numbers it
`nRegSyms + 20`, which `idsOK` refuses by itself). -/
def c2 : Semantics :=
  { c with symNames := c.symNames ++ ["LblmyE"]
           params := [{ sig := ⟨nRegSyms + 4, [Srt.int], Srt.endianness⟩, raw := true }] }

/-- `coreOK` refuses it (V2.d1-flip), by `paramsPlain`'s raw branch alone, which asks `shapesOK`
(false by `enumShapesOK`): every other conjunct of `coreOK` holds, `genWf` among them, and the
other conjuncts of the raw branch (no hook, no law, a number outside the registry, no ite name,
`floatShapeOK`). -/
theorem coreOK_refuses : c2.coreOK = false ∧ c2.paramsPlain = false ∧ c2.shapesOK = false ∧
    c2.enumShapesOK = false ∧ c2.floatShapeOK = true ∧ Faithful.genWf c2 = true ∧
    c2.params.all (fun k => k.raw && k.impl.isNone && !k.assoc && !k.idem &&
      decide (nRegSyms ≤ k.sig.name) && (iteSort? (c2.symName k.sig.name)).isNone) = true ∧
    (c2.subsortsOK && c2.fns.all (fun f => f.clauses.all (c2.clauseSorted f (c2.fns.map Fn.sig))) &&
      c2.rules.all c2.ruleSorted && c2.rulesPlain && c2.clausesPlain && c2.carriersOK &&
      c2.faithCoreOK && c2.hooksApart && c2.predsApart && c2.idsOK && c2.overloadsOK) = true := by
  decide +kernel

/-- `c` itself is refused as well. -/
theorem coreOK_refuses_c : c.coreOK = false ∧ c.paramsPlain = false := by decide +kernel

end EndRaw


/-! ### The constructors' items at an open generator (`consItemsK`)

At CommCtor: the constructor `x` has its functionality item and the open generators `and` and
`or` none; Exp's no-junk item lists all three; `or`'s associativity sentence is an item, and it
is the translation of the text's sentence 186 (`commctor.kompile.kore`, kompiled from
e2-comm-ctor.k: `axiom{R} \equals{SortExp{}, R}(Lblor{}(Lblor{}(K1,K2),K3), Lblor{}(K1,Lblor{}(K2,K3)))
[assoc{}()]`), read with the text's declarations. -/

kore_term commKore from "f2-examples/commctor.kompile.kore"

/-- `or`'s associativity item. -/
def orAssocItem : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.assocAxK CommCtor.c CommCtor.orP⟩

theorem comm_lawItems : (Faithful.lawItemsK CommCtor.c).map (·.pat) = [orAssocItem.pat] := by decide +kernel

theorem comm_items :
    (Faithful.consItemsK CommCtor.c).any (·.pat == orAssocItem.pat) = true ∧
    (Faithful.consItemsK CommCtor.c).any (·.pat ==
      (KoreAML.Cons.funItem "Exp" (Gen.toK CommCtor.c (.ctor ⟨CommCtor.xS, [], CommCtor.exp⟩))).pat) = true ∧
    (Faithful.consItemsK CommCtor.c).any (·.pat ==
      (KoreAML.Cons.funItem "Exp" (Gen.toK CommCtor.c (.ctor CommCtor.andP.sig))).pat) = false ∧
    (Faithful.consItemsK CommCtor.c).any (·.pat ==
      (KoreAML.Cons.funItem "Exp" (Gen.toK CommCtor.c (.ctor CommCtor.orP.sig))).pat) = false ∧
    (Faithful.consItemsK CommCtor.c).any (·.pat ==
      (KoreAML.Cons.noJunkItem "Exp" ((CommCtor.c.gens CommCtor.exp).map (Gen.toK CommCtor.c))).pat) = true ∧
    (CommCtor.c.gens CommCtor.exp).length = 3 := by
  decide +kernel

/-- The item is the text's sentence 186 (its axiom 76, `AxiomDecl.index`), translated with the text's
declarations. -/
theorem comm_assoc_is_text :
    (commKore.axiomDecls.find? (·.index == 76)).map (fun ad => (KoreAML.trAxiom commKore.symbolDecls
      commKore.aliasNames ad).pat) = some orAssocItem.pat := by
  decide +kernel


/-! ### An open generator in a left side is refused (`openGeneratorPattern`, decided)

`patCtxAll`, the heads a left side may apply, holds no open generator: a pattern that applies one
has no sort there, so `ruleSorted` is false of OpenMixed's `ruleCD` (`<k> c(X & Y) => d(X) </k>`).
The same rule with a variable of B in place of `X & Y` is sorted, and the open generator may stand
in a right side (`rhsCtx` holds the parameters). -/

/-- `<k> c(Z) => d(x) </k>`, Z a variable of B. -/
def ruleCZ : Rule :=
  { vars := [OpenMixed.sB, Srt.counter]
    lhs := .app topLabel [.app OpenMixed.kS [.app kseq [.app OpenMixed.cS [.var 0], .app dotk []]], .var 1]
    req := none
    rhs := .app topLabel [.app OpenMixed.kS [.app kseq [.app OpenMixed.dS [.app OpenMixed.xS []], .app dotk []]],
      .var 1]
    ens := none
    prio := 50 }

/-- `<k> c(Z) => c(x & y) </k>`: the open generator in the right side. -/
def ruleCAnd : Rule :=
  { ruleCZ with
    rhs := .app topLabel [.app OpenMixed.kS [.app kseq [.app OpenMixed.cS
      [.app OpenMixed.andS [.app OpenMixed.xS [], .app OpenMixed.yS []]], .app dotk []]], .var 1] }

theorem openGeneratorPattern_decided :
    (OpenMixed.c.patCtxAll.heads.all fun k => !OpenMixed.c.params.any fun p => p.raw && p.sig.name == k.name) = true ∧
    sortOfTerm OpenMixed.c.patCtxAll OpenMixed.ruleCD.vars OpenMixed.ruleCD.lhs = none ∧
    OpenMixed.c.ruleSorted OpenMixed.ruleCD = false ∧
    OpenMixed.c.ruleSorted ruleCZ = true ∧ OpenMixed.c.ruleSorted ruleCAnd = true := by
  decide +kernel

/-! ## `OpenTotal` at `HookParams.none` (V2.OpenTotal-none)

At CommCtor, where `and` and `or` are open generators, `openTotal_of_noAnswer` holds with its
hypotheses met (not vacuously): each raw parameter is the one its name finds, an open generator,
with no hook, its name no constructor's and no overloading symbol's. -/
theorem commCtor_openTotal_none : OpenTotal (CommCtor.c.withHooks HookParams.none) :=
  openTotal_of_noAnswer (fun _ _ => rfl) fun k hk _ => by
    have hk' : k = CommCtor.andP ∨ k = CommCtor.orP := by
      simpa [CommCtor.c, Semantics.withHooks] using hk
    rcases hk' with rfl | rfl
    · exact ⟨CommCtor.andP, by decide +kernel, by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel⟩
    · exact ⟨CommCtor.orP, by decide +kernel, by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel⟩

/-! ## `lawHooks` satisfies the laws (V2.d3-openLaws)

At CommCtor (`and` with no law, `or` associative) and IdemCtor (`or` idempotent),
`openLaws_of_lawShape` holds with its hypotheses met (not vacuously): every raw parameter has
`LawShape`; so `OpenLaws` holds at `lawHooks c H` for every H. -/
theorem commCtor_lawShape : ∀ k ∈ CommCtor.c.params, k.raw = true → LawShape CommCtor.c k := by decide +kernel
theorem idemCtor_lawShape : ∀ k ∈ IdemCtor.c.params, k.raw = true → LawShape IdemCtor.c k := by decide +kernel

theorem commCtor_openLaws_lawHooks (H : HookParams) : OpenLaws (CommCtor.c.withHooks (lawHooks CommCtor.c H)) :=
  openLaws_of_lawShape commCtor_lawShape H
theorem idemCtor_openLaws_lawHooks (H : HookParams) : OpenLaws (IdemCtor.c.withHooks (lawHooks IdemCtor.c H)) :=
  openLaws_of_lawShape idemCtor_lawShape H

/-! ## `lawHooks` gives the open generators values (V2.d3-openTotal)

At CommCtor (the no-law and the associative branch) and IdemCtor (the idempotent branch). -/
theorem commCtor_openTotal_lawHooks (H : HookParams) : OpenTotal (CommCtor.c.withHooks (lawHooks CommCtor.c H)) :=
  openTotal_of_lawShape commCtor_lawShape H
theorem idemCtor_openTotal_lawHooks (H : HookParams) : OpenTotal (IdemCtor.c.withHooks (lawHooks IdemCtor.c H)) :=
  openTotal_of_lawShape idemCtor_lawShape H

/-! ## The three together at `lawHooks c HookParams.lib` (V2.d3-example)

CN-4 §4.7 item 2's example, at its statement less the hypothesis `hl` (CN-4b §12): in a semantics
meeting `coreOK` and `floatShapeOK`, `lawHooks c HookParams.lib`
satisfies the laws (`openLaws_lawHooks`), gives every open generator a value at every argument
list of its sorts (`openTotal_lawHooks`) and is admitted by the library's sentences
(`libAdmitted_lawHooks` from `libAdmitted_lib`). `coreOK` admits open generators of
`paramsPlain`'s raw shape (V2.d1-flip); the instances below state the same three at CommCtor
and IdemCtor, which have open generators, from the `_of` forms whose hypotheses they meet
(`commCtor_lawShape`, `idemCtor_lawShape`, `comm_reg`, `comm_lawLibRawFree`, `idemCtor_reg`). -/
theorem lawHooks_lib (c : Semantics) (h : c.coreOK = true) (hf : c.floatShapeOK = true) :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted :=
  ⟨openLaws_lawHooks c h HookParams.lib, openTotal_lawHooks c h HookParams.lib,
    libAdmitted_lawHooks c h HookParams.lib (libAdmitted_lib c hf)⟩

theorem commCtor_lawHooks_lib :
    OpenLaws (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)) ∧
    OpenTotal (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)) ∧
    (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)).libAdmitted :=
  ⟨commCtor_openLaws_lawHooks HookParams.lib, commCtor_openTotal_lawHooks HookParams.lib, comm_lawHooks_lib⟩

theorem idemCtor_reg : ∀ k ∈ IdemCtor.c.params, k.raw = true → nRegSyms ≤ k.sig.name := by decide +kernel

theorem idemCtor_lawHooks_lib :
    OpenLaws (IdemCtor.c.withHooks (lawHooks IdemCtor.c HookParams.lib)) ∧
    OpenTotal (IdemCtor.c.withHooks (lawHooks IdemCtor.c HookParams.lib)) ∧
    (IdemCtor.c.withHooks (lawHooks IdemCtor.c HookParams.lib)).libAdmitted :=
  ⟨idemCtor_openLaws_lawHooks HookParams.lib, idemCtor_openTotal_lawHooks HookParams.lib,
    libAdmitted_lawHooks_of idemCtor_reg
      (lawLibRawFree_of_shapes (by decide +kernel) (by decide +kernel) idemCtor_reg) HookParams.lib
      (libAdmitted_lib IdemCtor.c (by decide +kernel))⟩

end KCore.OpenGenSems
