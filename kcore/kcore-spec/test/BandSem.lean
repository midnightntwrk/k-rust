/-
  A hand-built semantics for e2-band-ctor, an open generator with `assoc` and `idem` (CN-4b §7,
  BAND). The file checks that its numbering is the one `idsOK` asks, that `lookupOpen` finds the
  open generator and no constructor, that `OpenLaws` and `OpenTotal` hold at `lawHooks`
  (V13.band-lemmas), and that `coreOK` admits it, `consItemsK` writes both law sentences for `or`
  and `consistent_of` applies at `lawHooks` (V13.band-flip); the fixture's expectations are
  V13.band-test's. Run from the package
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

/-! ## The laws at `lawHooks` (V13.band-lemmas)

`or` has both laws and `LawShape`, so `openLaws_of_lawShape` and `openTotal_of_lawShape` hold here
through their branch for a generator with both laws (not vacuously): at `lawHooks c H`, for every
H, the interpretation satisfies associativity and idempotence at the values of Exp and gives `or` a
value at every two of them. `coreOK` is not read here. -/
theorem lawShape : ∀ k ∈ c.params, k.raw = true → LawShape c k := by decide +kernel
theorem both_laws : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = true := by decide +kernel
theorem openLaws_lawHooks (H : HookParams) : OpenLaws (c.withHooks (lawHooks c H)) :=
  openLaws_of_lawShape lawShape H
theorem openTotal_lawHooks (H : HookParams) : OpenTotal (c.withHooks (lawHooks c H)) :=
  openTotal_of_lawShape lawShape H

/-- The instances read: `or` is associative at every three values of Exp, idempotent at every one,
and has a value at every two, under `lawHooks c H`. -/
theorem or_laws (H : HookParams) :
    OpenAssoc (c.withHooks (lawHooks c H)) orS exp ∧ OpenIdem (c.withHooks (lawHooks c H)) orS exp ∧
    ∀ vs, (c.withHooks (lawHooks c H)).sortsOf vs = some [exp, exp] →
      ((c.withHooks (lawHooks c H)).paramVal orS vs).isSome = true :=
  have hk : orP ∈ (c.withHooks (lawHooks c H)).params := List.mem_singleton_self _
  ⟨(openLaws_lawHooks H orP hk rfl).1 rfl, (openLaws_lawHooks H orP hk rfl).2 rfl,
    openTotal_lawHooks H orP hk rfl⟩

/-- At `lawHooks`: `(x | y) | (x | y)` is `x | y`, the case that merging equal neighbours fails;
`x | y` is a value of Exp. -/
theorem or_compound :
    (c.withHooks (lawHooks c HookParams.none)).paramVal orS
      [.ctor orS [.ctor xS [], .ctor yS []], .ctor orS [.ctor xS [], .ctor yS []]] =
      some (.ctor orS [.ctor xS [], .ctor yS []]) :=
  (or_laws HookParams.none).2.1 _ (by decide +kernel)

/-! ## `coreOK` admits the band (V13.band-flip)

`paramsPlain`'s raw branch no longer refuses a parameter with both laws: `c`, whose one parameter
`or` is raw with `assoc` and `idem`, meets `coreOK`. -/
theorem coreOK : c.coreOK = true := by decide +kernel

/-- `paramsPlain` at `c` with what its raw branch reads, and that the branch is read at a parameter
with both laws. -/
theorem paramsPlain_band : c.paramsPlain = true ∧ c.shapesOK = true ∧ c.floatShapeOK = true ∧
    c.carriersOK = true ∧ c.params.all (fun k => k.raw && k.assoc && k.idem && k.impl.isNone &&
      k.sig.args == [k.sig.result, k.sig.result] && decide (nRegSyms ≤ k.sig.name) &&
      (iteSort? (c.symName k.sig.name)).isNone) = true := by
  decide +kernel

/-- `or`'s associativity and idempotence items. -/
def orAssocItem : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.assocAxK c orP⟩
def orIdemItem : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.idemAxK c orP⟩

/-- `lawItemsK` writes both sentences for `or`, and they are two. -/
theorem lawItems : (Faithful.lawItemsK c).map (·.pat) = [orAssocItem.pat, orIdemItem.pat] ∧
    (orAssocItem.pat == orIdemItem.pat) = false := by
  decide +kernel

/-- Both are items of `consItemsK`; `or` has no functionality item (the constructor `x` has one);
Exp's no-junk item lists `x`, `y` and `or`. -/
theorem items :
    (Faithful.consItemsK c).any (·.pat == orAssocItem.pat) = true ∧
    (Faithful.consItemsK c).any (·.pat == orIdemItem.pat) = true ∧
    (Faithful.consItemsK c).any (·.pat ==
      (KoreAML.Cons.funItem "Exp" (Gen.toK c (.ctor ⟨xS, [], exp⟩))).pat) = true ∧
    (Faithful.consItemsK c).any (·.pat ==
      (KoreAML.Cons.funItem "Exp" (Gen.toK c (.ctor orP.sig))).pat) = false ∧
    (Faithful.consItemsK c).any (·.pat ==
      (KoreAML.Cons.noJunkItem "Exp" ((c.gens exp).map (Gen.toK c))).pat) = true ∧
    (c.gens exp).length = 3 := by
  decide +kernel

/-- The library's theorems for a semantics meeting `coreOK`, at `c` (not the `_of_lawShape` forms
above): the laws, a value at every argument list, and the library's sentences, at
`lawHooks c HookParams.lib` (CN-4 §4.7's example at the band). -/
theorem lawHooks_lib :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted :=
  ⟨KCore.openLaws_lawHooks c coreOK HookParams.lib, KCore.openTotal_lawHooks c coreOK HookParams.lib,
    libAdmitted_lawHooks c coreOK HookParams.lib (libAdmitted_lib c (by decide +kernel))⟩

/-- **`consistent_of` at the band**: for every H, the theory of `c` at `lawHooks c H` has a model,
`OpenLaws` being `openLaws_lawHooks H`. `c` has no function, so `FnSolves` holds of it; `FnDet`
(of the sort predicates' clauses) is taken as a hypothesis. -/
theorem consistent (H : HookParams) (hd : FnDet (c.withHooks (lawHooks c H))) :
    Consistent (c.withHooks (lawHooks c H)) :=
  consistent_of _ ((Semantics.coreOK_withHooks c (lawHooks c H)).trans coreOK) hd
    (fun _ (hfn : _ ∈ ([] : List Fn)) => nomatch hfn) (openLaws_lawHooks H)

#print axioms coreOK
#print axioms lawItems
#print axioms items
#print axioms lawHooks_lib
#print axioms consistent
#print axioms openLaws_lawHooks
#print axioms openTotal_lawHooks
#print axioms or_compound

end KCore.BandSem
