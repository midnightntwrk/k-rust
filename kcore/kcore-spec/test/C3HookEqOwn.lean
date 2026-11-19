/-
  C3 `hook x equation`, the case of the text's own hooked symbol: a user's equation of a symbol the
  text declares with a hook the registry interprets, so that the reading has it as a parameter symbol
  with `impl`, whose value Γ states by the registry's hook (`ΓDomains`, `Semantics.paramVal`). Run
  from the package root: `lake env lean -j1 test/C3HookEqOwn.lean`. Every statement is on the literal
  texts (`f2-examples/FIXTURE.kompile.kore`, the kompiled text that
  `test/constructs/fixtures/FIXTURE/kompile.txt` records, with its paths restored), for every
  interpretation H; nothing reads `Parse.parse` or `emit`.

  The reader leaves each such equation out of Γ (`Parse.regLemmaEqn`), and the account lists it owed
  at values (`user lemma at values`). Each namespace below states, of one fixture:
  - `text`: the sentence is the pattern of an equation in the function form over terms applying the
    parameter symbol (`LibEv.FnEqn`, `LibEv.koreP`), typed over the text's sorts
    (`LibEv.FnEqn.typedPT`), and translated without the text's declarations;
  - `regLemma`: the reader takes it for a user's equation of a symbol whose value the registry gives;
  - `ev`: **it holds at values, for every H** (`EntailsAtValues`, the direction of the class
    `user lemma at values`): its two sides have the same value under Γ's value of the parameter, the
    hook's (`LibEv.FnEqn.entailedPT`, `LibEv.FnEqn.entailedPT_owise`).

  - `Eq` (c3-hook-eq, `plus [hook(INT.add)]`): `plus(X, 0) => X`; at an integer x, x + 0 = x.
  - `Req` (c3-hook-eq-req): `plus(X, Y) => X requires Y ==Int 0`; where y = 0, x + y = x.
  - `Ground` (c3-hook-eq-ground): `plus(1, 2) => 3`; 1 + 2 = 3.
  - `Owise` (c3-hook-eq-owise): `plus(X, 0) => X` (`ev240`) and `plus(X, Y) => X +Int Y [owise]`
    (`ev239`, its premise the `[owise]` conjunct of `LibEvFnOwise`'s form, `LibEv.FnOwise.owiseP`, then
    the equation's own): `plus` is `+Int` at every pair of integers, so the sentence holds whatever the
    other equation's premise says.
  - `Ite` (rdr-ite-own-hook-eq, `pick [symbol(ite), hook(KEQUAL.ite)]` read as K's ite at Foo, the
    parameter `ite{Foo}` implemented by `kIte`): `pick(true, X:Foo, _:Foo) => X`; `kIte` at `true` is
    its second argument (`paramVal_ite`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore ML Faithful KoreAML LibEv

/-! ## `plus(X, 0) => X` -/

namespace KCore.C3HookEqOwn.Eq

kore_term kore from "f2-examples/c3-hook-eq.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq.kompile.kore" module "C3-HOOK-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The parameter symbol `plus`, implemented by `_+Int_`. -/
abbrev plus : Sym := 384

kernel_rfl lookupPlus : ∀ H : HookParams,
  ((cH H).lookupParam plus).map (fun k => (k.sig.name, k.impl, k.sig.result)) = some (plus, some intAdd, Srt.int)

theorem plus_name : c.symName plus = "Lblplus" := by decide +kernel

kernel_rfl appValPlus : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) plus ws = (cH H).paramVal plus ws

-- Γ's value of `plus` at two integers is their sum, for every H.
kernel_rfl pvPlus : ∀ (H : HookParams) (x y : Int), (cH H).paramVal plus [int x, int y] = some (int (x + y))

/-- The user's equation. -/
noncomputable abbrev lemAx : AxiomDecl := U.ax239

/-- `plus(X, 0) => X` in the function form: `plus` at the argument variables `X0`, `X1`, matched
by the patterns `VarX` and `0`, has the value of `VarX`. -/
def E : FnEqn := ⟨[("VarX", Srt.int)], plus, [(Srt.int, .var 0, none), (Srt.int, intT 0, none)], Srt.int, none, .var 0⟩

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

/-- **The sentence is `E`'s pattern**, over the one sort variable `R`, and translated without the
text's declarations. -/
theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] lemAx.ax.pattern) := by
  decide +kernel

/-- The reader takes the sentence for a user's equation of a symbol whose value the registry gives:
it leaves it out of Γ, owed. -/
theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

theorem holds (H : HookParams) : E.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarX", Srt.int) rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h1 : σ.lookup 1 = some (int x) := hm1.symm.trans (by rw [fq_valP_var, h0])
  have h2 : σ.lookup 2 = some (int 0) := hm2.symm
  show valP (cH H) σ (.app plus [.var 1, .var 2]) = valP (cH H) σ (.var 0)
  simp only [valP, valPList, allSome, h1, h2, h0, Option.bind_some, Option.map_some, appValPlus, pvPlus,
    Int.add_zero]

/-- **`plus(X, 0) = X` holds at values, for every H**: in every model of Γ, at every valuation that
sends `X`, `X0`, `X1` to values. -/
theorem ev (H : HookParams) : EntailsAtValues (cH H) lemAx (trS lemAx).pat := by
  rw [text.2.2.2.1]
  exact FnEqn.entailedPT (coreOKH H) E ((typed H).trans text.2.2.1) (holds H) lemAx (pattern H) text.2.1
    (fun i hi => by rw [vkey_wh]; exact text.2.2.2.2 i hi)

end KCore.C3HookEqOwn.Eq

/-! ## `plus(X, Y) => X requires Y ==Int 0` -/

namespace KCore.C3HookEqOwn.Req

kore_term kore from "f2-examples/c3-hook-eq-req.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq-req.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq-req.kompile.kore" module "C3-HOOK-EQ-REQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

abbrev plus : Sym := 384

theorem plus_name : c.symName plus = "Lblplus" := by decide +kernel

kernel_rfl appValPlus : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) plus ws = (cH H).paramVal plus ws
kernel_rfl appValEq : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) intEq ws = (cH H).hv intEq ws
kernel_rfl pvPlus : ∀ (H : HookParams) (x y : Int), (cH H).paramVal plus [int x, int y] = some (int (x + y))

noncomputable abbrev lemAx : AxiomDecl := U.ax239

/-- `plus(X, Y) => X requires Y ==Int 0` in the function form. -/
def E : FnEqn :=
  ⟨[("VarX", Srt.int), ("VarY", Srt.int)], plus, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.int,
    some (.app intEq [.var 1, intT 0]), .var 0⟩

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] lemAx.ax.pattern) := by
  decide +kernel

theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

theorem holds (H : HookParams) : E.HoldsP (cH H) := by
  intro σ hσ hq hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarX", Srt.int) rfl
  obtain ⟨v1, h1, hs1⟩ := hσ 1 ("VarY", Srt.int) rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨y, rfl⟩ := shape_int (shapesOKH H) hs1
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h2 : σ.lookup 2 = some (int x) := hm1.symm.trans (by rw [fq_valP_var, h0])
  have h3 : σ.lookup 3 = some (int y) := hm2.symm.trans (by rw [fq_valP_var, h1])
  have hy := hq _ rfl
  simp only [valP, valPList, allSome, h1, intT, Option.bind_some, Option.map_some] at hy
  rw [appValEq, show (GroundTerm.dv Srt.int (.int 0)) = int 0 from rfl, fhv_intEq] at hy
  have hy0 : y = 0 := by simpa [bool] using hy
  subst hy0
  show valP (cH H) σ (.app plus [.var 2, .var 3]) = valP (cH H) σ (.var 0)
  simp only [valP, valPList, allSome, h2, h3, h0, Option.bind_some, Option.map_some, appValPlus, pvPlus,
    Int.add_zero]

/-- **`plus(X, Y) = X` where `Y ==Int 0` holds at values, for every H.** -/
theorem ev (H : HookParams) : EntailsAtValues (cH H) lemAx (trS lemAx).pat := by
  rw [text.2.2.2.1]
  exact FnEqn.entailedPT (coreOKH H) E ((typed H).trans text.2.2.1) (holds H) lemAx (pattern H) text.2.1
    (fun i hi => by rw [vkey_wh]; exact text.2.2.2.2 i hi)

end KCore.C3HookEqOwn.Req

/-! ## `plus(1, 2) => 3` -/

namespace KCore.C3HookEqOwn.Ground

kore_term kore from "f2-examples/c3-hook-eq-ground.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq-ground.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq-ground.kompile.kore" module "C3-HOOK-EQ-GROUND"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

abbrev plus : Sym := 384

theorem plus_name : c.symName plus = "Lblplus" := by decide +kernel

kernel_rfl appValPlus : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) plus ws = (cH H).paramVal plus ws
kernel_rfl pvPlus : ∀ (H : HookParams) (x y : Int), (cH H).paramVal plus [int x, int y] = some (int (x + y))

noncomputable abbrev lemAx : AxiomDecl := U.ax239

/-- `plus(1, 2) => 3` in the function form. -/
def E : FnEqn := ⟨[], plus, [(Srt.int, intT 1, none), (Srt.int, intT 2, none)], Srt.int, none, intT 3⟩

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] lemAx.ax.pattern) := by
  decide +kernel

theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

theorem holds (H : HookParams) : E.HoldsP (cH H) := by
  intro σ _ _ hm
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h0 : σ.lookup 0 = some (int 1) := hm1.symm
  have h1 : σ.lookup 1 = some (int 2) := hm2.symm
  show valP (cH H) σ (.app plus [.var 0, .var 1]) = valP (cH H) σ (intT 3)
  simp only [valP, valPList, allSome, h0, h1, Option.bind_some, Option.map_some, appValPlus, pvPlus]
  rfl

/-- **`plus(1, 2) = 3` holds at values, for every H.** -/
theorem ev (H : HookParams) : EntailsAtValues (cH H) lemAx (trS lemAx).pat := by
  rw [text.2.2.2.1]
  exact FnEqn.entailedPT (coreOKH H) E ((typed H).trans text.2.2.1) (holds H) lemAx (pattern H) text.2.1
    (fun i hi => by rw [vkey_wh]; exact text.2.2.2.2 i hi)

end KCore.C3HookEqOwn.Ground

/-! ## `plus(X, 0) => X` and `plus(X, Y) => X +Int Y [owise]` -/

namespace KCore.C3HookEqOwn.Owise

kore_term kore from "f2-examples/c3-hook-eq-owise.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq-owise.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq-owise.kompile.kore" module "C3-HOOK-EQ-OWISE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

abbrev plus : Sym := 384

theorem plus_name : c.symName plus = "Lblplus" := by decide +kernel

kernel_rfl appValPlus : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) plus ws = (cH H).paramVal plus ws
kernel_rfl appValAdd : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) intAdd ws = (cH H).hv intAdd ws
kernel_rfl pvPlus : ∀ (H : HookParams) (x y : Int), (cH H).paramVal plus [int x, int y] = some (int (x + y))
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

/-- `plus(X, 0) => X` in the function form. -/
def E0 : FnEqn := ⟨[("VarX", Srt.int)], plus, [(Srt.int, .var 0, none), (Srt.int, intT 0, none)], Srt.int, none, .var 0⟩

/-- `plus(X, Y) => X +Int Y` in the function form. -/
def Ew : FnEqn :=
  ⟨[("VarX", Srt.int), ("VarY", Srt.int)], plus, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.int, none,
    .app intAdd [.var 0, .var 1]⟩

/-- The other equation as the `[owise]` premise names it: `plus(_Gen2, 0)`, its variable `_Gen2`
after `Ew`'s four. -/
def O0 : FnOther := ⟨[("Var'Unds'Gen2", Srt.int)], [(Srt.int, .var 4, none), (Srt.int, intT 0, none)], none⟩

/-- The `[owise]` equation with the other equation of `plus` (`LibEvFnOwise`'s form). -/
def W : FnOwise := ⟨Ew, [O0]⟩

kernel_rfl pattern240 : ∀ H : HookParams, U.ax240.ax.pattern = E0.patternP (cH H)
kernel_rfl pattern239 : ∀ H : HookParams, U.ax239.ax.pattern =
  .implies KoreAML.R (.and KoreAML.R [W.owiseP (cH H), Ew.premP (cH H)]) (Ew.conclP (cH H))
kernel_rfl typed0 : ∀ H : HookParams, E0.typedPT (cH H) = E0.typedPT c
kernel_rfl typedw : ∀ H : HookParams, Ew.typedPT (cH H) = Ew.typedPT c

theorem text240 : U.ax240.ax.pattern = E0.patternP c ∧ U.ax240.ax.sortVars = [KoreAML.Rv] ∧
    E0.typedPT c = true ∧ (trS U.ax240).pat = (trAxiom [] [] U.ax240).pat ∧
    (∀ i, i < E0.av.length → vkey c E0.av i ∈ KoreAML.freeOf [] U.ax240.ax.pattern) := by
  decide +kernel

/-- **The `[owise]` sentence is `Ew`'s conclusion under the premise `\and{R}(owise, \and{R}(req,
ins))`**, its `owise` conjunct the negation of `O0`'s premise (`FnOwise.owiseP`). -/
theorem text239 : U.ax239.ax.pattern =
      .implies KoreAML.R (.and KoreAML.R [W.owiseP c, Ew.premP c]) (Ew.conclP c) ∧
    U.ax239.ax.sortVars = [KoreAML.Rv] ∧ Ew.typedPT c = true ∧ (trS U.ax239).pat = (trAxiom [] [] U.ax239).pat ∧
    (∀ i, i < Ew.av.length → vkey c Ew.av i ∈ KoreAML.freeOf [] U.ax239.ax.pattern) := by
  decide +kernel

theorem regLemma : [U.ax239, U.ax240].all (fun ad => (Parse.rawEqn? ad.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD [])))) = true := by
  decide +kernel

theorem holds0 (H : HookParams) : E0.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarX", Srt.int) rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h1 : σ.lookup 1 = some (int x) := hm1.symm.trans (by rw [fq_valP_var, h0])
  have h2 : σ.lookup 2 = some (int 0) := hm2.symm
  show valP (cH H) σ (.app plus [.var 1, .var 2]) = valP (cH H) σ (.var 0)
  simp only [valP, valPList, allSome, h1, h2, h0, Option.bind_some, Option.map_some, appValPlus, pvPlus,
    Int.add_zero]

theorem holdsw (H : HookParams) : Ew.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarX", Srt.int) rfl
  obtain ⟨v1, h1, hs1⟩ := hσ 1 ("VarY", Srt.int) rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨y, rfl⟩ := shape_int (shapesOKH H) hs1
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h2 : σ.lookup 2 = some (int x) := hm1.symm.trans (by rw [fq_valP_var, h0])
  have h3 : σ.lookup 3 = some (int y) := hm2.symm.trans (by rw [fq_valP_var, h1])
  show valP (cH H) σ (.app plus [.var 2, .var 3]) = valP (cH H) σ (.app intAdd [.var 0, .var 1])
  simp only [valP, valPList, allSome, h0, h1, h2, h3, Option.bind_some, Option.map_some, appValPlus, pvPlus,
    appValAdd, hv_intAdd]

/-- **`plus(X, 0) = X` holds at values, for every H.** -/
theorem ev240 (H : HookParams) : EntailsAtValues (cH H) U.ax240 (trS U.ax240).pat := by
  rw [text240.2.2.2.1]
  exact FnEqn.entailedPT (coreOKH H) E0 ((typed0 H).trans text240.2.2.1) (holds0 H) U.ax240 (pattern240 H)
    text240.2.1 (fun i hi => by rw [vkey_wh]; exact text240.2.2.2.2 i hi)

/-- **`plus(X, Y) = X +Int Y` under the `[owise]` premise holds at values, for every H.** -/
theorem ev239 (H : HookParams) : EntailsAtValues (cH H) U.ax239 (trS U.ax239).pat := by
  rw [text239.2.2.2.1]
  exact FnEqn.entailedPT_owise (coreOKH H) Ew ((typedw H).trans text239.2.2.1) (holdsw H) _ U.ax239
    (pattern239 H) text239.2.1 (fun i hi => by rw [vkey_wh]; exact text239.2.2.2.2 i hi)

end KCore.C3HookEqOwn.Owise

/-! ## `pick(true, X:Foo, _:Foo) => X`, `pick` K's ite at Foo -/

namespace KCore.C3HookEqOwn.Ite

kore_term kore from "f2-examples/rdr-ite-own-hook-eq.kompile.kore"
definition_of defn from "f2-examples/rdr-ite-own-hook-eq.kompile.kore"
user_axioms U from "f2-examples/rdr-ite-own-hook-eq.kompile.kore" module "RDR-ITE-OWN-HOOK-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort Foo, a sort of the text. -/
abbrev foo : Srt := 32

/-- The parameter symbol `ite{Foo}`, implemented by `kIte`. -/
abbrev iteFoo : Sym := 388

theorem names : c.sortName foo = "Foo" ∧ c.symName iteFoo = Parse.iteName "Foo" := by decide +kernel

kernel_rfl lookupIte : ∀ H : HookParams,
  ((cH H).lookupParam iteFoo).map (fun k => (k.impl, k.sig.result)) = some (some kIte, foo)
kernel_rfl appValIte : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) iteFoo ws = (cH H).paramVal iteFoo ws

noncomputable abbrev lemAx : AxiomDecl := U.ax171

/-- `ite{Foo}(true, X, _Gen0) => X` in the function form. -/
def E : FnEqn :=
  ⟨[("VarX", foo), ("Var'Unds'Gen0", foo)], iteFoo,
    [(Srt.bool, .dv Srt.bool (.bool true), none), (foo, .var 0, none), (foo, .var 1, none)], foo, none, .var 0⟩

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] lemAx.ax.pattern) := by
  decide +kernel

theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

theorem holds (H : HookParams) : E.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarX", foo) rfl
  obtain ⟨v1, h1, -⟩ := hσ 1 ("Var'Unds'Gen0", foo) rfl
  obtain ⟨hm1, -, hm2, -, hm3, -, -⟩ := hm
  have h2 : σ.lookup 2 = some (bool true) := hm1.symm
  have h3 : σ.lookup 3 = some v0 := hm2.symm.trans (by rw [fq_valP_var, h0])
  have h4 : σ.lookup 4 = some v1 := hm3.symm.trans (by rw [fq_valP_var, h1])
  show valP (cH H) σ (.app iteFoo [.var 2, .var 3, .var 4]) = valP (cH H) σ (.var 0)
  simp only [valP, valPList, allSome, h0, h2, h3, h4, Option.bind_some, Option.map_some, appValIte]
  have hl := lookupIte H
  cases hk : (cH H).lookupParam iteFoo with
  | none => rw [hk] at hl; cases hl
  | some k =>
    rw [hk] at hl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    have hz : (cH H).sortOf (if true then v0 else v1) = some k.sig.result := by rw [hl.2]; exact hs0
    simpa using paramVal_ite (c := cH H) hk hl.1 true hz

/-- **`ite{Foo}(true, X, _) = X` holds at values, for every H.** -/
theorem ev (H : HookParams) : EntailsAtValues (cH H) lemAx (trS lemAx).pat := by
  rw [text.2.2.2.1]
  exact FnEqn.entailedPT (coreOKH H) E ((typed H).trans text.2.2.1) (holds H) lemAx (pattern H) text.2.1
    (fun i hi => by rw [vkey_wh]; exact text.2.2.2.2 i hi)

end KCore.C3HookEqOwn.Ite

/-- info: 'KCore.C3HookEqOwn.Eq.ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqOwn.Eq.ev
/-- info: 'KCore.C3HookEqOwn.Req.ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqOwn.Req.ev
/-- info: 'KCore.C3HookEqOwn.Ground.ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqOwn.Ground.ev
/-- info: 'KCore.C3HookEqOwn.Owise.ev240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqOwn.Owise.ev240
/-- info: 'KCore.C3HookEqOwn.Owise.ev239' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqOwn.Owise.ev239
/-- info: 'KCore.C3HookEqOwn.Ite.ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqOwn.Ite.ev
#print axioms KCore.C3HookEqOwn.Eq.regLemma
#print axioms KCore.C3HookEqOwn.Req.regLemma
#print axioms KCore.C3HookEqOwn.Ground.regLemma
#print axioms KCore.C3HookEqOwn.Owise.regLemma
#print axioms KCore.C3HookEqOwn.Ite.regLemma
