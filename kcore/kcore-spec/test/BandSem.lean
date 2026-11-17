/-
  A hand-built semantics for e2-band-ctor, an open generator with `assoc` and `idem` (CN-4b §7,
  BAND). No expectation is stated here; the file checks only that its numbering is the one `idsOK`
  asks and that `lookupOpen` finds the open generator and no constructor. Run from the package
  root: `lake env lean -j1 test/BandSem.lean`. Kernel-checked.

  Text (lane P's fixture `test/constructs/fixtures/e2-band-ctor`, K 7.1.337):
  `syntax Exp ::= "x" [symbol(x)] | "y" [symbol(y)] | Exp "|" Exp [assoc, idem, symbol(or)]`.
  Built as `test/OpenGenSems.lean`'s semantics: the configuration `<k> K </k>` with the generated
  counter, own sorts `KCell`, `KCellOpt`, `Exp`; own symbols the predicates, `<k>`, `noKCell`, `x`,
  `y`, then `or`. `project:Exp` is left out.

  What the text states of `or` (`kore.txt`; line numbers of that file):
  - declared `symbol Lblor{}(SortExp{}, SortExp{}) : SortExp{} [functional{}(), idem{}(), …]` (:8):
    no `constructor`, `injective` or `function`; `idem` is kept on the declaration, `assoc` is not;
  - its `functional` axiom (:24);
  - the associativity axiom `or(or(K1,K2),K3) = or(K1,or(K2,K3))` (:20, `[assoc{}()]`) and the
    idempotence axiom `or(K,K) = K` (:22, `[idem{}()]`): kompile writes both axioms and no
    `constructor`, the first case of CN-4b §7's fixture table;
  - Exp's no-junk axiom (:32): `∃X0 X1. or(X0,X1) ∨ x() ∨ y() ∨ ⊥`;
  - the one no-confusion axiom (:28) is `¬(x() ∧ y())`: no axiom separates an `or` application from
    `x()` or `y()`, or states `or` injective.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.BandSem

open KCore

def exp : Srt := nRegSorts + 2
def kS : Sym := nRegSyms + 3
def xS : Sym := nRegSyms + 5
def yS : Sym := nRegSyms + 6
def orS : Sym := nRegSyms + 7

def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, assoc := true, idem := true }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Exp"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisExp", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx", "Lbly",
      "Lblor"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt, exp]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨kS, [Srt.k], nRegSorts⟩, ⟨kS + 1, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩,
      ⟨xS, [], exp⟩, ⟨yS, [], exp⟩]
    fns := []
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := []
    params := [orP] }

theorem idsOK : c.idsOK = true := by decide +kernel
theorem lookupOpen_ok : c.lookupOpen orS = some orP ∧ c.lookupOpen xS = none ∧ c.lookupOpen yS = none := by
  decide +kernel

/-- `Faithful.genWf` holds (Exp is flat); at `HookParams.none` the raw `or(x, y)` and `x` are two
values of Exp that `cmp` tells apart. -/
theorem genWf_apart : Faithful.genWf c = true ∧
    (c.withHooks HookParams.none).sortOf (.ctor orS [.ctor xS [], .ctor yS []]) = some exp ∧
    (c.withHooks HookParams.none).sortOf (.ctor xS []) = some exp ∧
    GroundTerm.cmp (.ctor orS [.ctor xS [], .ctor yS []]) (.ctor xS []) != .eq := by
  decide +kernel

end KCore.BandSem
