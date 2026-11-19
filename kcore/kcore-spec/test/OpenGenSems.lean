/-
  Hand-built semantics with open generators (`ParamSig.raw`), one per text, for the checks of
  CN-4 §4.7. The reader reads an open generator the text declares `functional` as a `raw`
  parameter where its result sort is a constructor sort whose constructors are nullary
  (`Parse.openGenFault`); `OpenRule.textCheck` reads e2-open-rule's text. No expectation is stated here; each namespace checks only that its numbering is
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
    `syntax KItem ::= "go"`, `syntax Bool ::= same(Exp, Exp) [function]`, `rule same(A, B) => A ==K B`,
    `rule <k> go => x & y </k>`). `and` raw, no law. The declarations, the rule and `same`'s
    equation are compared with the kompiled text's sentences (`OpenRule.textCheck`).
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

/-! ## e2-open-rule

What the text states (`kore.txt`; line numbers of that file):
- `and`: declared `symbol Lbland{}(SortExp{}, SortExp{}) : SortExp{} [functional{}(), …]` (:6), no
  `constructor`, `injective`, `function` or `comm`; its `functional` axiom (:42); no law axiom.
- Exp's no-junk axiom (:58): `∃X0 X1. and(X0,X1) ∨ x() ∨ y() ∨ ⊥`. The one no-confusion axiom of
  Exp (:54) is `¬(x() ∧ y())`: it names no `and` application.
- `go`: `symbol Lblgo{}() : SortKItem{} [constructor{}(), functional{}(), injective{}(), …]` (:8), a
  constructor of KItem, in the rule's left side with no injection.
- The rule (:63-68): `\rewrites(\and(<generatedTop>(<k>(kseq(go(), dotk())), _DotVar0), \top),
  \and(<generatedTop>(<k>(kseq(inj{Exp,KItem}(and(x(), y())), dotk())), _DotVar0), \top))`, the
  counter cell a variable.
- `same`'s equation (:143-161): `same(X0, X1) = _==K_(kseq(inj{Exp,KItem}(A), dotk()),
  kseq(inj{Exp,KItem}(B), dotk()))` under the premise `X0 ∈ A ∧ X1 ∈ B`, no `requires` or
  `ensures`.
-/
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

/-! ### The semantics against the kompiled text

`c` is written by hand (the reader refuses the text at `and`'s declaration, `openGenerator`). Each
part of it that reads a sentence of the user module is compared with that sentence
(`f2-examples/openrule.kompile.kore`, the fixture's kompiled text; line numbers of the fixture's
`kore.txt`). -/

/-- A symbol's declaration in the sentences `ss`: its argument sorts, its result sort and its
attributes but `Location`, `Source` and `symbol'Kywd'`. -/
def declOf (ss : List Kore.Sentence) (n : String) : Option (List Kore.KSort × Kore.KSort × List String) :=
  ss.findSome? fun
    | .symbol d => if d.symbol.ident.ident.name == n then
        some (d.sorts, d.sort, (d.attributes.map (·.head.ident.name)).filter fun a =>
          !(a.startsWith "org'Stop'kframework" || a == "symbol'Kywd'"))
      else none
    | _ => none

/-- `c` against the text: the reader's open generators (`and : Exp Exp → Exp`), `coreOK` of the
semantics read and the inert constructor axioms it does not induce (none: Exp's no-junk axiom
lists `and`, as `Γ` does); `and`,
`go`, `same`, `x` and `y` declared with `c`'s signatures and kinds (an open generator: `functional`
alone; constructors; a function); the text's one rewrite axiom is `ruleGo`'s two sides as
`Term.kore` writes them at `c`'s names, with the text's variable name; `same`'s one equation has
`clSame`'s premise (`premise`, no `requires`) and right side. -/
def textCheck : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/openrule.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    let ss := (k.modules.getLast?.map (·.sentences)).getD []
    let E := KoreAML.srt "Exp"
    -- the reader's verdict: `and` an open generator
    match Parse.parse k with
    | .error r => IO.println s!"parse: refused {r.reason.name} {r.detail}"
    | .ok d =>
      let cr := d.sem
      IO.println s!"parse: read; open generators {(cr.params.filter (·.raw)).map fun p =>
        (cr.symName p.sig.name, p.sig.args.map cr.sortName, cr.sortName p.sig.result)}; coreOK {cr.coreOK}; uninduced {(Parse.uninduced k d).length}"
    -- the declarations (:6, :8, :14, :16, :18)
    IO.println s!"and: {declOf ss (c.symName andS) == some ([E, E], E, ["functional"])}"
    IO.println s!"go: {declOf ss (c.symName goS) == some ([], KoreAML.srt "KItem", ["constructor", "functional", "injective"])}"
    IO.println s!"same: {declOf ss (c.symName sameS) == some ([E, E], KoreAML.srt "Bool", ["function"])}"
    IO.println s!"x, y: {[xS, yS].map fun f => declOf ss (c.symName f) == some ([], E, ["constructor", "functional", "injective"])}"
    -- the one rewrite axiom (:63-68): `\rewrites(\and(lhs, \top), \and(rhs, \top))`
    let vr := KoreAML.varList [c.sortName Srt.counter] ["'Unds'DotVar0"]
    let rws := ss.filterMap fun
      | .axiom a => match a.pattern with
        | .rewrites _ l r => some (l, r)
        | _ => none
      | _ => none
    let T := Kore.Pattern.top (KoreAML.srt (c.sortName Srt.top))
    IO.println s!"rule: {rws == [(.and (KoreAML.srt (c.sortName Srt.top)) [Term.kore c vr ruleGo.lhs, T], .and (KoreAML.srt (c.sortName Srt.top)) [Term.kore c vr ruleGo.rhs, T])]}"
    -- `same`'s equation (:143-161): `\implies(premise, \equals(same(X0, X1), \and(rhs, \top)))`
    let vc := KoreAML.varList [c.sortName exp, c.sortName exp] ["A", "B"]
    let eqs := ss.filterMap fun
      | .axiom a => match a.pattern with
        | .implies _ p (.equals _ _ (.app h _ _) r) => if h.ident.name == c.symName sameS then some (p, r) else none
        | _ => none
      | _ => none
    IO.println s!"same's equation: {eqs.map fun (p, r) => (p == KCore.premise [c.sortName exp, c.sortName exp] none (Term.koreList c vc clSame.pats), r == Kore.Pattern.and (KoreAML.srt "Bool") [Term.kore c vc clSame.rhs, .top (KoreAML.srt "Bool")])}"

/--
info: parse: read; open generators [(Lbland, ([Exp, Exp], Exp))]; coreOK true; uninduced 0
and: true
go: true
same: true
x, y: [true, true]
rule: true
same's equation: [(true, true)]
-/
#guard_msgs in
#eval textCheck

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
sort the library's sentences other than `_RangeMap_`'s associativity read applies none (`shapesOK`,
`floatShapeOK`), so `lawHooks c H` is admitted wherever H is and gives `_RangeMap_` no value; at
`HookParams.lib`, admitted in every semantics with `floatShapeOK`
(`libAdmitted_lib`), so is `lawHooks c HookParams.lib`, which differs from it at `and` and `or`. -/

theorem comm_reg : ∀ k ∈ CommCtor.c.params, k.raw = true → nRegSyms ≤ k.sig.name := by decide +kernel

theorem comm_lawLibRawFree : CommCtor.c.lawLibRawFree :=
  lawLibRawFree_of_shapes (by decide +kernel) (by decide +kernel) comm_reg

theorem comm_lawHooks_lib : (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)).libAdmitted :=
  libAdmitted_lawHooks_of comm_reg comm_lawLibRawFree HookParams.lib
    (libAdmitted_lib CommCtor.c (by decide +kernel)) lib_app_rmConcat_none

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

/-- `coreOK` refuses it, by `paramsPlain`'s raw branch alone, which asks `shapesOK`
(false by `enumShapesOK`): every other conjunct of `coreOK` holds, `genWf` among them, and the
other conjuncts of the raw branch (no hook, no law, a number outside the registry, no ite name);
`floatShapeOK` holds too. -/
theorem coreOK_refuses : c2.coreOK = false ∧ c2.paramsPlain = false ∧ c2.shapesOK = false ∧
    c2.enumShapesOK = false ∧ c2.floatShapeOK = true ∧ Faithful.genWf c2 = true ∧
    c2.params.all (fun k => k.raw && k.impl.isNone && !k.assoc && !k.idem &&
      decide (nRegSyms ≤ k.sig.name) && (iteSort? (c2.symName k.sig.name)).isNone) = true ∧
    (c2.subsortsOK && c2.fns.all (fun f => f.clauses.all (c2.clauseSorted f (c2.fns.map Fn.sig))) &&
      c2.rules.all c2.ruleSorted && c2.rulesPlain && c2.clausesPlain && c2.carriersOK &&
      c2.faithCoreOK && c2.predsApart && c2.idsOK && c2.overloadsOK) = true := by
  decide_cheap

/-- `c` itself is refused as well. -/
theorem coreOK_refuses_c : c.coreOK = false ∧ c.paramsPlain = false := by decide +kernel

/-- `c2` with its parameter not raw. -/
def c2n : Semantics :=
  { c2 with params := [{ sig := ⟨nRegSyms + 4, [Srt.int], Srt.endianness⟩, raw := false }] }

/-- The raw parameter is the cause of the refusal: the same semantics with the parameter not raw
meets `coreOK` and `shapesOK`. -/
theorem coreOK_c2n : c2n.coreOK = true ∧ c2n.shapesOK = true := by decide_cheap

/-- The reason holds at `c2`: a value of Endianness applies its raw parameter, so the hypothesis
of `libAdmitted_lawHooks_of` is false there. -/
theorem not_lawLibRawFree_c2 : ¬ c2.lawLibRawFree := fun h => by
  have hv : (c2.withHooks HookParams.none).sortOf (.ctor (nRegSyms + 4) [int 1]) = some Srt.endianness := by
    decide +kernel
  have := h HookParams.none (.ctor (nRegSyms + 4) [int 1]) Srt.endianness (by decide) hv
  have hf : c2.rawFree (.ctor (nRegSyms + 4) [int 1]) = false := by decide +kernel
  rw [hf] at this; cases this

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

CN-4 §4.7 item 2's example, at its statement less the hypotheses `hl` (CN-4b §12) and `hf`
(`coreOK` gives `floatShapeOK`, `floatShapeOK_of_coreOK`): in a semantics
meeting `coreOK`, `lawHooks c HookParams.lib`
satisfies the laws (`openLaws_lawHooks`), gives every open generator a value at every argument
list of its sorts (`openTotal_lawHooks`) and is admitted by the library's sentences
(`libAdmitted_lawHooks` from `libAdmitted_lib_of_coreOK`). The instances below state the same
three at CommCtor and IdemCtor, which have open generators, from the `_of` forms whose hypotheses
they meet (`commCtor_lawShape`, `idemCtor_lawShape`, `comm_reg`, `comm_lawLibRawFree`,
`idemCtor_reg`); the instances from `coreOK` are in the next section. -/
theorem lawHooks_lib (c : Semantics) (h : c.coreOK = true) :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted :=
  ⟨openLaws_lawHooks c h HookParams.lib, openTotal_lawHooks c h HookParams.lib,
    libAdmitted_lawHooks c h HookParams.lib (libAdmitted_lib_of_coreOK h) lib_app_rmConcat_none⟩

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
      (libAdmitted_lib IdemCtor.c (by decide +kernel)) lib_app_rmConcat_none⟩

/-! ## `coreOK` admits the four semantics

Each of the four meets `coreOK`. At CommCtor, whose `or` is raw with a law, the library's
statements for a semantics meeting `coreOK` are read with a raw parameter at hand (not vacuously):
`paramsPlain`'s raw branch (`raw_of_core`), `raw_open_core`, `lawShape_core`, `openTotal_none`,
`libAdmitted_lawHooks`, and the three of `lawHooks_lib` (also at IdemCtor). -/

theorem commCtor_coreOK : CommCtor.c.coreOK = true := by decide_cheap
theorem idemCtor_coreOK : IdemCtor.c.coreOK = true := by decide_cheap
theorem openMixed_coreOK : OpenMixed.c.coreOK = true := by decide_cheap
theorem openRule_coreOK : OpenRule.c.coreOK = true := by decide_cheap

theorem commCtor_raw_or : CommCtor.orP.impl = none ∧
    ((CommCtor.orP.assoc || CommCtor.orP.idem) = true →
      CommCtor.orP.sig.args = [CommCtor.orP.sig.result, CommCtor.orP.sig.result]) ∧
    nRegSyms ≤ CommCtor.orP.sig.name ∧ iteSort? (CommCtor.c.symName CommCtor.orP.sig.name) = none ∧
    CommCtor.c.shapesOK = true :=
  Semantics.raw_of_core commCtor_coreOK (k := CommCtor.orP) (by decide +kernel) rfl

theorem commCtor_raw_open : ∀ k ∈ CommCtor.c.params, k.raw = true → ∃ kp, CommCtor.c.lookupParam k.sig.name = some kp ∧
    CommCtor.c.lookupOpen k.sig.name = some kp ∧ kp.sig = k.sig ∧ kp.impl = none ∧
    lookupSig CommCtor.c.ctorSigs k.sig.name = none ∧ CommCtor.c.lookupOvl k.sig.name = none :=
  Semantics.raw_open_core commCtor_coreOK

theorem commCtor_lawShape_core : ∀ k ∈ CommCtor.c.params, k.raw = true → LawShape CommCtor.c k :=
  Semantics.lawShape_core commCtor_coreOK

theorem commCtor_openTotal_none_core : OpenTotal (CommCtor.c.withHooks HookParams.none) :=
  openTotal_none _ commCtor_coreOK

theorem commCtor_libAdmitted_lawHooks (H : HookParams) (ha : (CommCtor.c.withHooks H).libAdmitted)
    (hrm : ∀ vs, H.app rmConcat vs = none) :
    (CommCtor.c.withHooks (lawHooks CommCtor.c H)).libAdmitted :=
  libAdmitted_lawHooks _ commCtor_coreOK H ha hrm

theorem commCtor_lawHooks_lib_core :
    OpenLaws (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)) ∧
    OpenTotal (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)) ∧
    (CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.lib)).libAdmitted :=
  lawHooks_lib CommCtor.c commCtor_coreOK

theorem idemCtor_lawHooks_lib_core :
    OpenLaws (IdemCtor.c.withHooks (lawHooks IdemCtor.c HookParams.lib)) ∧
    OpenTotal (IdemCtor.c.withHooks (lawHooks IdemCtor.c HookParams.lib)) ∧
    (IdemCtor.c.withHooks (lawHooks IdemCtor.c HookParams.lib)).libAdmitted :=
  lawHooks_lib IdemCtor.c idemCtor_coreOK

/-! ## The headlines at a semantics with an open generator

`FnHyp` of a semantics none of whose lists names a fact and whose clauses' predicates are `\top`,
under an interpretation H that satisfies its open generators' laws: the deciders' lists are those of the data (they do not read H), and
`OpenLaws` is the hypothesis. With it `consistent_of`, `sound_hyp`, `complete_hyp` and `exact_hyp`
apply, every hypothesis discharged: at CommCtor (two open generators, one with a law; no rule, no
function) and at OpenRule (an open generator, a rule and a function), each at `lawHooks c
HookParams.none`, whose laws `openLaws_lawHooks` gives. -/

theorem fnHyp_of_laws {c : Semantics} (hc : c.coreOK = true) (hv : c.rightValued = true)
    (h1 : c.rankObligations [] ++ c.decObligationsL = []) (h2 : c.totalObligationsRP [] [] = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = [])
    (h5 : c.owedRules = []) (h6 : c.owedClauses = []) (hpreTop : c.clausesPreTop = true)
    (H : HookParams) (hl : OpenLaws (c.withHooks H))
    (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact Semantics.fnsNoExs_of_all rfl) :
    FnHyp (c.withHooks H) :=
  fnHyp_of_fnObligations (ord := []) (tp := []) (hpreTop := (Semantics.clausesPreTop_withHooks c H).trans hpreTop)
    (hnoEx := (Semantics.fnsNoExs_withHooks c H).mpr hnoEx) ((Semantics.coreOK_withHooks c H).trans hc)
    (Semantics.rightHeld_withHooks_of_valued hv H) ParamsTotal.nil
    ((FnFacts.of_nil_laws
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact h1)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans h2)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans h3)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans h4) hl).obligations
     ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, h5]; intro i hi; cases hi),
      openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, h6]; intro p hp; cases hp)⟩)

theorem commCtor_fnHyp (H : HookParams) (hl : OpenLaws (CommCtor.c.withHooks H)) :
    FnHyp (CommCtor.c.withHooks H) :=
  fnHyp_of_laws commCtor_coreOK (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H hl

theorem openRule_fnHyp (H : HookParams) (hl : OpenLaws (OpenRule.c.withHooks H)) :
    FnHyp (OpenRule.c.withHooks H) :=
  fnHyp_of_laws openRule_coreOK (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H hl

/-- CommCtor at `lawHooks c HookParams.none`. -/
abbrev cL : Semantics := CommCtor.c.withHooks (lawHooks CommCtor.c HookParams.none)
/-- OpenRule at `lawHooks c HookParams.none`. -/
abbrev cR : Semantics := OpenRule.c.withHooks (lawHooks OpenRule.c HookParams.none)

theorem cL_coreOK : cL.coreOK = true := (Semantics.coreOK_withHooks CommCtor.c _).trans commCtor_coreOK
theorem cL_laws : OpenLaws cL := openLaws_lawHooks CommCtor.c commCtor_coreOK HookParams.none
theorem cL_total : OpenTotal cL := openTotal_lawHooks CommCtor.c commCtor_coreOK HookParams.none
theorem cL_fnHyp : FnHyp cL := commCtor_fnHyp _ cL_laws
theorem cL_consistent : Consistent cL :=
  consistent_of cL cL_coreOK (fnModel_of_fnHyp cL_coreOK cL_fnHyp).1 (fnModel_of_fnHyp cL_coreOK cL_fnHyp).2
    (clausePreDecided_of_fnHyp cL_coreOK cL_fnHyp)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp cL_coreOK) cL_fnHyp) cL_laws
theorem cL_sound : SoundC cL := sound_hyp cL cL_coreOK cL_fnHyp
theorem cL_complete (ref : OutFn) : CompleteC cL ref := complete_hyp cL ref cL_coreOK cL_fnHyp
theorem cL_exact : ExactC cL := exact_hyp cL cL_coreOK cL_fnHyp

/-- A value of `cL` applies the open generator `and`: its values are not all `rawFree`. -/
theorem cL_value : cL.sortOf (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) = some CommCtor.exp ∧
    cL.rawFree (.ctor CommCtor.andS [.ctor CommCtor.xS [], .ctor CommCtor.xS []]) = false := by decide +kernel

theorem cR_coreOK : cR.coreOK = true := (Semantics.coreOK_withHooks OpenRule.c _).trans openRule_coreOK
theorem cR_laws : OpenLaws cR := openLaws_lawHooks OpenRule.c openRule_coreOK HookParams.none
theorem cR_total : OpenTotal cR := openTotal_lawHooks OpenRule.c openRule_coreOK HookParams.none
theorem cR_fnHyp : FnHyp cR := openRule_fnHyp _ cR_laws
theorem cR_consistent : Consistent cR :=
  consistent_of cR cR_coreOK (fnModel_of_fnHyp cR_coreOK cR_fnHyp).1 (fnModel_of_fnHyp cR_coreOK cR_fnHyp).2
    (clausePreDecided_of_fnHyp cR_coreOK cR_fnHyp)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp cR_coreOK) cR_fnHyp) cR_laws
theorem cR_sound : SoundC cR := sound_hyp cR cR_coreOK cR_fnHyp
theorem cR_complete (ref : OutFn) : CompleteC cR ref := complete_hyp cR ref cR_coreOK cR_fnHyp
theorem cR_exact : ExactC cR := exact_hyp cR cR_coreOK cR_fnHyp

/-- `cR` has a rule and a function, and a value that applies its open generator. -/
theorem cR_parts : cR.rules.length = 1 ∧ cR.fns.length = 1 ∧
    cR.sortOf (.ctor OpenRule.andS [.ctor OpenRule.xS [], .ctor OpenRule.yS []]) = some OpenRule.exp ∧
    cR.rawFree (.ctor OpenRule.andS [.ctor OpenRule.xS [], .ctor OpenRule.yS []]) = false := by decide +kernel

/-- **A confined sort has a value** (`confined_has_value`) at a semantics with open generators:
a confined sort of CommCtor has a value under every interpretation that gives the open generators
values (`OpenTotal`). -/
theorem commCtor_confined_value (H : HookParams) (ht : OpenTotal (CommCtor.c.withHooks H)) {s : Srt}
    (hs : (CommCtor.c.withHooks H).confined s = true) : ∃ v, (CommCtor.c.withHooks H).sortOf v = some s :=
  confined_has_value ((Semantics.coreOK_withHooks CommCtor.c H).trans commCtor_coreOK) hs ht

#print axioms cL_consistent
#print axioms cL_sound
#print axioms cL_complete
#print axioms cL_exact
#print axioms cR_consistent
#print axioms cR_sound
#print axioms cR_complete
#print axioms cR_exact
#print axioms commCtor_confined_value
#print axioms EndRaw.not_lawLibRawFree_c2

/-! ## e2-idem-ctor: the expectations (CN-4 §3.4 V7)

- For every H with `OpenLaws`: `x | x` is `x` (the idempotence axiom at `x`).
- At `lawHooks c HookParams.none`: `(x | y) | y` is a value of Exp distinct from `x | y` (the text
  leaves it open; `lawHooks` merges equal arguments only).
- At `HookParams.none`: `OpenIdem` fails at `x` (`or(x, x)` is the raw application, a value other
  than `x`), so `OpenLaws` fails. -/
namespace IdemCtor

def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []

theorem sort_x (H : HookParams) : (c.withHooks H).sortOf xV = some exp :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

theorem or_mem (H : HookParams) : orP ∈ (c.withHooks H).params := List.mem_singleton_self _

theorem idem_x (H : HookParams) (hl : OpenLaws (c.withHooks H)) :
    (c.withHooks H).paramVal orS [xV, xV] = some xV :=
  (hl orP (or_mem H) rfl).2 rfl xV (sort_x H)

theorem lawHooks_values :
    (c.withHooks (lawHooks c HookParams.none)).paramVal orS [.ctor orS [xV, yV], yV] =
      some (.ctor orS [.ctor orS [xV, yV], yV]) ∧
    (c.withHooks (lawHooks c HookParams.none)).sortOf (.ctor orS [.ctor orS [xV, yV], yV]) = some exp ∧
    (c.withHooks (lawHooks c HookParams.none)).sortOf (.ctor orS [xV, yV]) = some exp ∧
    GroundTerm.ctor orS [.ctor orS [xV, yV], yV] ≠ .ctor orS [xV, yV] := by
  decide +kernel

theorem none_raw : (c.withHooks HookParams.none).paramVal orS [xV, xV] = some (.ctor orS [xV, xV]) := by
  decide +kernel
theorem not_openIdem_none : ¬ OpenIdem (c.withHooks HookParams.none) orS exp := fun h =>
  absurd ((h xV (sort_x _)).symm.trans none_raw) (by decide +kernel)
theorem not_openLaws_none : ¬ OpenLaws (c.withHooks HookParams.none) := fun h =>
  not_openIdem_none ((h orP (or_mem _) rfl).2 rfl)

end IdemCtor

#print axioms IdemCtor.idem_x
#print axioms IdemCtor.lawHooks_values
#print axioms IdemCtor.not_openLaws_none

/-! ## e2-comm-ctor: the expectations (CN-4 §4.7)

- `coreOK` (`commCtor_coreOK`).
- For every H with `OpenLaws` and `OpenTotal`: `Consistent`, `SoundC`, `CompleteC` and `ExactC`
  (`OpenTotal` is a named obligation no proof reads: it keeps the interpretations to those under
  which the text's `functional` sentences hold).
- At `lawHooks c H`, for every H: the same, both obligations discharged.
- At `HookParams.none`: `OpenTotal` holds and `OpenLaws` fails: `or(or(x,x),x)` and `or(x,or(x,x))`
  are two raw values, so associativity fails at `x, x, x`. -/
namespace CommCtor

def xV : GroundTerm := .ctor xS []

theorem headlines (H : HookParams) (hl : OpenLaws (c.withHooks H)) (_ht : OpenTotal (c.withHooks H)) :
    Consistent (c.withHooks H) ∧ SoundC (c.withHooks H) ∧ (∀ ref, CompleteC (c.withHooks H) ref) ∧
      ExactC (c.withHooks H) :=
  have hc := (Semantics.coreOK_withHooks c H).trans commCtor_coreOK
  have hf := commCtor_fnHyp H hl
  ⟨consistent_of _ hc (fnModel_of_fnHyp hc hf).1 (fnModel_of_fnHyp hc hf).2 (clausePreDecided_of_fnHyp hc hf)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp hc) hf) hl, sound_hyp _ hc hf,
    fun ref => complete_hyp _ ref hc hf, exact_hyp _ hc hf⟩

theorem headlines_lawHooks (H : HookParams) :
    Consistent (c.withHooks (lawHooks c H)) ∧ SoundC (c.withHooks (lawHooks c H)) ∧
      (∀ ref, CompleteC (c.withHooks (lawHooks c H)) ref) ∧ ExactC (c.withHooks (lawHooks c H)) :=
  headlines (lawHooks c H) (openLaws_lawHooks c commCtor_coreOK H) (openTotal_lawHooks c commCtor_coreOK H)

/-- At `HookParams.none` the two nestings of `x, x, x` under `or` are two raw values of Exp. -/
theorem none_values :
    ((c.withHooks HookParams.none).paramVal orS [xV, xV]).bind
        (fun ab => (c.withHooks HookParams.none).paramVal orS [ab, xV]) =
      some (.ctor orS [.ctor orS [xV, xV], xV]) ∧
    ((c.withHooks HookParams.none).paramVal orS [xV, xV]).bind
        (fun bd => (c.withHooks HookParams.none).paramVal orS [xV, bd]) =
      some (.ctor orS [xV, .ctor orS [xV, xV]]) ∧
    (c.withHooks HookParams.none).sortOf (.ctor orS [.ctor orS [xV, xV], xV]) = some exp ∧
    (c.withHooks HookParams.none).sortOf (.ctor orS [xV, .ctor orS [xV, xV]]) = some exp ∧
    GroundTerm.ctor orS [.ctor orS [xV, xV], xV] ≠ .ctor orS [xV, .ctor orS [xV, xV]] := by
  decide +kernel

theorem not_openLaws_none : ¬ OpenLaws (c.withHooks HookParams.none) := fun h => by
  have ha := (h orP (by decide +kernel) rfl).1 rfl xV xV xV (by decide +kernel)
  exact absurd (Option.some.inj ((none_values.1.symm.trans ha).trans none_values.2.1)) none_values.2.2.2.2

theorem openTotal_none : OpenTotal (c.withHooks HookParams.none) := commCtor_openTotal_none_core

end CommCtor

#print axioms CommCtor.headlines
#print axioms CommCtor.headlines_lawHooks
#print axioms CommCtor.not_openLaws_none

/-! ## e2-open-rule: the expectations (CN-4 §4.7)

`and` has no law, so `OpenLaws` holds under every interpretation.

- For every H with `OpenTotal`: `<k> go </k>` (counter 0) has one successor, `<k> v </k>` with v
  the value H gives `x & y`.
- `same(x & y, y & x)` is `false` at `HookParams.none` (two raw values) and `true` at `Hswap`,
  which answers `and(x, y)` at `and [y, x]`.
- At `Hbad`, which answers `go` (of KItem, not Exp) at every application of `and`, `and [x, y]` has
  no value and `OpenTotal` fails.
- The configuration named, `<k> go </k>`, applies no open generator (`rawFree`): it is a
  configuration under every interpretation. -/
namespace OpenRule

def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []
/-- The counter cell at 0. -/
def cnt : GroundTerm := .ctor counterLabel [int 0]
/-- `<k> go </k>`. -/
def goV : GroundTerm := .ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]
/-- `<k> v </k>`, v a value of Exp. -/
def afterV (v : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]], cnt]

theorem go_rawFree : c.rawFree goV = true ∧ c.sortOf goV = some topCellSort ∧
    c.rawFree cnt = true ∧ c.sortOf cnt = some Srt.counter ∧
    c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree yV = true ∧ c.sortOf yV = some exp := by
  decide +kernel

/-- `<k> go </k>` as a configuration under H. -/
def goCfg (H : HookParams) : Config (c.withHooks H) :=
  ⟨goV, (Semantics.sortOf_withHooks_rawFree c H go_rawFree.1).trans go_rawFree.2.1⟩

theorem and_mem (H : HookParams) : andP ∈ (c.withHooks H).params := List.mem_singleton_self _

theorem openLaws_any (H : HookParams) : OpenLaws (c.withHooks H) := fun k hk _ => by
  have hk' : k = andP := List.mem_singleton.mp hk
  subst hk'
  exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem sorts_xy (H : HookParams) : (c.withHooks H).sortsOf [xV, yV] = some [exp, exp] :=
  OvlLaws.sortsOf_cons_iff.mpr
    ⟨(Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.2.2.1).trans go_rawFree.2.2.2.2.2.1,
     OvlLaws.sortsOf_cons_iff.mpr
      ⟨(Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.2.2.2.2.1).trans go_rawFree.2.2.2.2.2.2.2, rfl⟩⟩

/-- The rule's right side under a σ that gives the counter cell: `<k> v </k>`, v the value of
`x & y`. -/
theorem go_rhs (H : HookParams) {v : GroundTerm} (hv : (c.withHooks H).paramVal andS [xV, yV] = some v)
    {σ : Subst} (h0 : σ.lookup 0 = some cnt) :
    EvalTerm (c.withHooks H) σ ruleGo.rhs (some (afterV v)) := by
  have hx : EvalTerm (c.withHooks H) σ (.app xS []) (some xV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor xS = true by decide +kernel) .nil
  have hy : EvalTerm (c.withHooks H) σ (.app yS []) (some yV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor yS = true by decide +kernel) .nil
  have hand : EvalTerm (c.withHooks H) σ (.app andS [.app xS [], .app yS []]) (some v) :=
    EvalTerm.param (rs := [some xV, some yV]) (show c.isCtor andS = false by decide +kernel)
      (by decide +kernel) (show c.isParam andS = true by decide +kernel) (.cons hx (.cons hy .nil)) hv.symm
  have hinj : EvalTerm (c.withHooks H) σ (.inj exp Srt.kitem (.app andS [.app xS [], .app yS []]))
      (some (injNormal exp Srt.kitem v)) := EvalTerm.inj hand
  have hdot : EvalTerm (c.withHooks H) σ (.app dotk []) (some (.ctor dotk [])) :=
    EvalTerm.ctor (rs := []) (show c.isCtor dotk = true by decide +kernel) .nil
  have hseq : EvalTerm (c.withHooks H) σ (item (.app andS [.app xS [], .app yS []]))
      (some (.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []])) :=
    EvalTerm.ctor (rs := [some (injNormal exp Srt.kitem v), some (.ctor dotk [])])
      (show c.isCtor kseq = true by decide +kernel) (.cons hinj (.cons hdot .nil))
  have hk : EvalTerm (c.withHooks H) σ (.app kS [item (.app andS [.app xS [], .app yS []])])
      (some (.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]])) :=
    EvalTerm.ctor (rs := [some (.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []])])
      (show c.isCtor kS = true by decide +kernel) (.cons hseq .nil)
  have hvar : EvalTerm (c.withHooks H) σ (.var 0) (some cnt) := h0 ▸ EvalTerm.var
  exact EvalTerm.ctor (rs := [some (.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]]), some cnt])
    (show c.isCtor topLabel = true by decide +kernel) (.cons hk (.cons hvar .nil))

/-- A match of the rule's left side at `<k> go </k>` gives the counter cell to its variable. -/
theorem go_match (H : HookParams) {σ : Subst} (hm : PatVal (c.withHooks H) σ ruleGo.lhs goV) :
    σ.lookup 0 = some cnt := by
  have hm' : PatVal (c.withHooks H) σ
      (.app topLabel [.app kS [.app kseq [.app goS [], .app dotk []]], .var 0])
      (.ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]) := hm
  have hct : (c.withHooks H).isCtor topLabel = true := show c.isCtor topLabel = true by decide +kernel
  cases hm' with
  | ctor _ hs =>
    cases hs with
    | cons _ hs2 =>
      cases hs2 with
      | cons h2 _ =>
        cases h2 with
        | var h => exact h
  | hook hp _ _ => exact absurd hp (by decide +kernel)
  | coll hc _ _ _ => rw [hct] at hc; cases hc
  | ovl hc _ _ _ => rw [hct] at hc; cases hc

/-- **For every H with `OpenTotal`, `<k> go </k>` has one successor.** -/
theorem go_one (H : HookParams) (ht : OpenTotal (c.withHooks H)) :
    ∃ y : Config (c.withHooks H), ∀ y', Step (c.withHooks H) (goCfg H) y' ↔ y' = y := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht andP (and_mem H) rfl [xV, yV] (sorts_xy H))
  have hc : (c.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c H).trans openRule_coreOK
  have hd := (fnModel_of_fnHyp hc (openRule_fnHyp H (openLaws_any H))).1
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core hc
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hcnt : (c.withHooks H).sortOf cnt = some Srt.counter :=
    (Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.1).trans go_rawFree.2.2.2.1
  have hσ : (c.withHooks H).WellSorted ruleGo.vars [(0, cnt)] := fun i s hs => by
    match i, hs with
    | 0, hs => exact ⟨cnt, rfl, by cases hs; exact hcnt⟩
    | i + 1, hs => simp [ruleGo] at hs
  have he := go_rhs H hv (σ := [(0, cnt)]) rfl
  have hsort : (c.withHooks H).sortOf (afterV v) = some topCellSort :=
    EvalTerm.sorted hsc he (L := (c.withHooks H).fns.map Fn.sig) (headsOK_fns _) hσ
      (show sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) ruleGo.vars ruleGo.rhs = some topCellSort by
        decide +kernel) rfl
  refine ⟨⟨afterV v, hsort⟩, fun y' => ⟨fun hs => ?_, fun e => ?_⟩⟩
  · cases hs with
    | rule r mem σ _ hmatch _ _ heval _ _ _ =>
      have hr : r = ruleGo := List.mem_singleton.mp mem
      subst hr
      exact Subtype.ext (Option.some.inj
        (EvalTerm.functional_of_fnDet hd heval (go_rhs H hv (go_match H hmatch))))
  · subst e
    have hct : ∀ f, c.isCtor f = true → (c.withHooks H).isCtor f = true := fun _ h => h
    refine Step.rule ruleGo (List.mem_singleton_self _) [(0, cnt)] hσ ?_ (fun _ h => by cases h) .top he
      (fun _ h => by cases h) .top (fun r' hr' hlt => ?_)
    · exact PatVal.ctor (hct _ (by decide +kernel))
        (.cons (PatVal.ctor (hct _ (by decide +kernel))
          (.cons (PatVal.ctor (hct _ (by decide +kernel))
            (.cons (PatVal.ctor (hct _ (by decide +kernel)) .nil)
              (.cons (PatVal.ctor (hct _ (by decide +kernel)) .nil) .nil))) .nil))
          (.cons (PatVal.var rfl) .nil))
    · have hr : r' = ruleGo := List.mem_singleton.mp hr'
      subst hr
      exact absurd hlt (Nat.lt_irrefl _)

/-- `same(x & y, y & x)`. -/
def sameT : Term := .app sameS [.app andS [.app xS [], .app yS []], .app andS [.app yS [], .app xS []]]

/-- The interpretation answering `and(x, y)` at `and [y, x]`, and nothing elsewhere. -/
def Hswap : HookParams :=
  ⟨fun f vs => if f == andS && decide (vs = [yV, xV]) then some (.ctor andS [xV, yV]) else none⟩

/-- The interpretation answering `go`, of sort KItem, at every application of `and`. -/
def Hbad : HookParams := ⟨fun f _ => if f == andS then some (.ctor goS []) else none⟩

/-- A closed term's computed result is its result (`CExec.evalT_sound`). -/
theorem evalTerm_of_exec {c : Semantics} (hr : CExec.execReady c = true) {t : Term}
    {r : Option GroundTerm} {s : Srt} (n : Nat) (he : CExec.evalT c n [] t = some r)
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] t = some s) : EvalTerm c [] t r := by
  obtain ⟨-, hsc, hcc, hcm, -⟩ := CExec.execReady_parts hr
  exact CExec.evalT_sound hsc hcc hcm n he (headsOK_fns _) (fun i s hs => by simp at hs) ht

/-- At `HookParams.none`, `x & y` and `y & x` are two raw values and `same` of them is `false`. -/
theorem same_none : EvalTerm (c.withHooks HookParams.none) [] sameT (some (bool false)) :=
  evalTerm_of_exec (by decide +kernel) 50 (by decide +kernel) (s := Srt.bool) (by decide +kernel)

/-- At `Hswap`, `y & x` is `and(x, y)`, the value of `x & y`, and `same` of them is `true`. -/
theorem same_swap : EvalTerm (c.withHooks Hswap) [] sameT (some (bool true)) :=
  evalTerm_of_exec (by decide +kernel) 50 (by decide +kernel) (s := Srt.bool) (by decide +kernel)

theorem swap_values :
    (c.withHooks Hswap).paramVal andS [xV, yV] = some (.ctor andS [xV, yV]) ∧
    (c.withHooks Hswap).paramVal andS [yV, xV] = some (.ctor andS [xV, yV]) ∧
    (c.withHooks HookParams.none).paramVal andS [xV, yV] = some (.ctor andS [xV, yV]) ∧
    (c.withHooks HookParams.none).paramVal andS [yV, xV] = some (.ctor andS [yV, xV]) := by
  decide +kernel

/-- At `Hbad` the answer at `and [x, y]` is no value of Exp: `and` has no value there, and
`OpenTotal` fails. -/
theorem bad_none : (c.withHooks Hbad).paramVal andS [xV, yV] = none := by decide +kernel
theorem not_openTotal_bad : ¬ OpenTotal (c.withHooks Hbad) := fun h => by
  have : ((c.withHooks Hbad).paramVal andS [xV, yV]).isSome = true :=
    h andP (and_mem Hbad) rfl [xV, yV] (sorts_xy Hbad)
  rw [bad_none] at this
  cases this

end OpenRule

#print axioms OpenRule.go_one
#print axioms OpenRule.same_none
#print axioms OpenRule.same_swap
#print axioms OpenRule.not_openTotal_bad

end KCore.OpenGenSems
