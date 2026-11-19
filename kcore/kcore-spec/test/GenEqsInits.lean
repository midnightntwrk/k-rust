/-
  Instances of `KcoreSpec/GenEqsInit.lean` on kompiled texts: the equations of the cell tree's
  initializers and of the counter's getter hold together in one model of the theory whose steps
  are the semantics'. Run from the package root: `lake env lean -j1 test/GenEqsInits.lean`.

  ## Nested cells (`Cells`, `f2-examples/cellsplain.kompile.kore`)

  The construct fixture e2-cells-plain, `configuration <t> <k> $PGM:Exp </k> <one> 0 </one>
  <ec> 0 </ec> </t>`, by K 7.1.337's kompile. Its initializers: the constants `initOneCell()`,
  `initEcCell()` and `initGeneratedCounterCell()`; `initKCell(Init)`, whose right side applies
  `project:Exp` to `Map:lookup(Init, $PGM)`; `initTCell(Init) = <t>(initKCell(Init),
  initOneCell(), initEcCell())` and `initGeneratedTopCell(Init) = <generatedTop>(initTCell(Init),
  initGeneratedCounterCell())`, each applying the initializers of the cells below it. None of
  them, nor `project:Exp` nor the getter, is a symbol the semantics numbers (`unnumbered`). With
  `G` each right side's value, the initializers below read through `G` (`gK`, `gT`, `gTop`), one
  model of the theory whose steps are `Step`'s (`GenEqs.model_with_inits_step`) holds:
  - the constants' equations (`initOneCell() = <one>(0)` and the like);
  - at the map `$PGM ↦ a()` (`w1`), each initializer's equation with the right side as the text
    writes it (`rhsK`, `rhsT`, `rhsTop`), and the initial configuration
    `<generatedTop>(<t>(<k>(a()), <one>(0), <ec>(0)), <generatedCounter>(0))`, whose counter the
    getter gives;
  - at the empty map (`w0`), where `Map:lookup(Init, $PGM)` has no value, each equation with both
    sides denoting nothing, and `initGeneratedTopCell(.Map) = ⊥`.

  ## Initializers of two arguments (`Fresh`, `f2-examples/freshcfg.kompile.kore`)

  The construct fixture e7-freshconfig, `configuration <k> $PGM:Exp </k> <id> !N:Int </id>`: the
  fresh variable gives `initIdCell` and `initGeneratedTopCell` the arguments `(Init,
  #Configuration)`, and the counter the initial value 1. At `w1` and a configuration `t`,
  `initIdCell(w1, t) = <id>(0)` and `initGeneratedTopCell(w1, t) = <generatedTop>(initKCell(w1),
  initIdCell(w1, t), initGeneratedCounterCell())`, whose value is
  `<generatedTop>(<k>(a()), <id>(0), <generatedCounter>(1))`; at the empty map the configuration has
  none.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsInits

/-- The symbol named `f` applied to `ps`, as the translation writes an application. -/
def app (f : String) (ps : List KoreAML.P) : KoreAML.P := KoreAML.appList (symP f) ps

/-- `inj{a, b}(p)`, as the translation writes it. -/
def injA (a b : String) (p : KoreAML.P) : KoreAML.P :=
  KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP a, KoreAML.Cons.sortP b, p]

theorem srt {o : Option Srt} (h : o.isSome = true) : o = some (o.get h) := (Option.some_get h).symm

def key : GroundTerm := .inj Srt.kconfigVar Srt.kitem (.dv Srt.kconfigVar (.tok "$PGM"))
def w0 : GroundTerm := .map Srt.map []
def zero : GroundTerm := .dv Srt.int (.int 0)
def one : GroundTerm := .dv Srt.int (.int 1)
def dotK : GroundTerm := .ctor dotk []

/-- `Map:lookup`'s signature. -/
def lookupSig : CtorSig := ⟨mapLookup, [Srt.map, Srt.kitem], Srt.kitem⟩

theorem lookupSig_mem : lookupSig ∈ hookSigs := by decide +kernel

/-- `Map:lookup(w, $PGM)` on values. -/
def lookupV (w : GroundTerm) : Option GroundTerm :=
  match hook mapLookup [w, key] with
  | some (some v) => some v
  | _ => none

def initK : String := "LblinitKCell"
def initT : String := "LblinitTCell"
def initTop : String := "LblinitGeneratedTopCell"
def initCtr : String := "LblinitGeneratedCounterCell"
def initOne : String := "LblinitOneCell"
def initEc : String := "LblinitEcCell"
def initId : String := "LblinitIdCell"
def getter : String := "LblgetGeneratedCounterCell"
def projExp : String := "Lblproject'Coln'Exp"

namespace Cells

definition_of defn from "f2-examples/cellsplain.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

def names : List String := [initK, initT, initTop, initCtr, initOne, initEc, getter, projExp]

/-- **None of the names is a symbol of the semantics**, nor `inj` or `Lblite`. -/
theorem unnumbered : ∀ n ∈ names, (regSymNames ++ c.symNames).contains n = false ∧ n ≠ "" ∧ n ≠ "inj" ∧
    n ≠ "Lblite" ∧ c.instHeadFree n = true := by decide +kernel

/-- The arities the text declares. -/
def ar : String → Nat := fun n => if n = initCtr ∨ n = initOne ∨ n = initEc then 0 else 1

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def exp : Srt := nRegSorts + c.sortNames.idxOf "Exp"
noncomputable def kL : Sym := symN "Lbl'-LT-'k'-GT-'"
noncomputable def tL : Sym := symN "Lbl'-LT-'t'-GT-'"
noncomputable def oneL : Sym := symN "Lbl'-LT-'one'-GT-'"
noncomputable def ecL : Sym := symN "Lbl'-LT-'ec'-GT-'"
noncomputable def oneS : Srt := nRegSorts + c.sortNames.idxOf "OneCell"
noncomputable def ecS : Srt := nRegSorts + c.sortNames.idxOf "EcCell"

/-- The names of the symbols the right sides apply are the text's. -/
theorem text_names : c.symName kL = "Lbl'-LT-'k'-GT-'" ∧ c.symName tL = "Lbl'-LT-'t'-GT-'" ∧
    c.symName oneL = "Lbl'-LT-'one'-GT-'" ∧ c.symName ecL = "Lbl'-LT-'ec'-GT-'" ∧
    c.symName topLabel = "Lbl'-LT-'generatedTop'-GT-'" ∧ c.symName counterLabel = "Lbl'-LT-'generatedCounter'-GT-'" ∧
    c.symName kseq = "kseq" ∧ c.symName dotk = "dotk" ∧ c.symName mapLookup = "LblMap'Coln'lookup" ∧
    c.sortName exp = "Exp" ∧ c.sortName Srt.kitem = "KItem" ∧ c.sortName oneS = "OneCell" ∧
    c.sortName ecS = "EcCell" := by decide +kernel

noncomputable def aV : GroundTerm := .ctor (symN "Lbla") []
noncomputable def pgm : GroundTerm := .inj exp Srt.kitem aV
/-- The map `$PGM ↦ a()`. -/
noncomputable def w1 : GroundTerm := .map Srt.map [(key, pgm)]
noncomputable def oneV : GroundTerm := .ctor oneL [zero]
noncomputable def ecV : GroundTerm := .ctor ecL [zero]
def ctrV : GroundTerm := .ctor counterLabel [zero]

/-- The initializers' right sides at values, those below read through the ones above: `initKCell`'s
from `Map:lookup` and `project:Exp`, `initTCell`'s from `initKCell`'s, `initGeneratedTopCell`'s
from `initTCell`'s. -/
noncomputable def gK (w : GroundTerm) : Option GroundTerm := do
  let v ← lookupV w
  let e ← projFn c exp (.ctor kseq [v, dotK])
  pure (.ctor kL [.ctor kseq [.inj exp Srt.kitem e, dotK]])
noncomputable def gT (w : GroundTerm) : Option GroundTerm := (gK w).map fun k => .ctor tL [k, oneV, ecV]
noncomputable def gTop (w : GroundTerm) : Option GroundTerm := (gT w).map fun t => .ctor topLabel [t, ctrV]

noncomputable def G : String → List GroundTerm → Option GroundTerm
  | n, [] => if n = initOne then some oneV else if n = initEc then some ecV else if n = initCtr then some ctrV else none
  | n, [w] => if n = initK then gK w else if n = initT then gT w else if n = initTop then gTop w
      else if n = getter then argFn topLabel 1 w else if n = projExp then projFn c exp w else none
  | _, _ => none

def inits : String → Prop := fun n => n ∈ names

/-- `initKCell`'s right side at `x`: `<k>(kseq(inj{Exp,KItem}(project:Exp(kseq(Map:lookup(x, $PGM), dotk))), dotk))`. -/
noncomputable def rhsK (x : KoreAML.P) : KoreAML.P :=
  app (c.symName kL) [app (c.symName kseq) [injA (c.sortName exp) (c.sortName Srt.kitem)
    (app projExp [app (c.symName kseq) [app (c.symName mapLookup) [x, den c key], app (c.symName dotk) []]]),
    app (c.symName dotk) []]]
/-- `initTCell`'s right side at `x`: `<t>(initKCell(x), initOneCell(), initEcCell())`. -/
noncomputable def rhsT (x : KoreAML.P) : KoreAML.P := app (c.symName tL) [app initK [x], app initOne [], app initEc []]
/-- `initGeneratedTopCell`'s right side at `x`: `<generatedTop>(initTCell(x), initGeneratedCounterCell())`. -/
noncomputable def rhsTop (x : KoreAML.P) : KoreAML.P := app (c.symName topLabel) [app initT [x], app initCtr []]

noncomputable def item : GroundTerm := .ctor kseq [pgm, dotK]
noncomputable def kV : GroundTerm := .ctor kL [.ctor kseq [pgm, dotK]]
noncomputable def tV : GroundTerm := .ctor tL [kV, oneV, ecV]
/-- The initial configuration at `w1`. -/
noncomputable def topV : GroundTerm := .ctor topLabel [tV, ctrV]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf w0).isSome ∧ (c.sortOf key).isSome ∧ (c.sortOf pgm).isSome ∧
    (c.sortOf aV).isSome ∧ (c.sortOf dotK).isSome ∧ (c.sortOf item).isSome ∧ (c.sortOf kV).isSome ∧
    (c.sortOf oneV).isSome ∧ (c.sortOf ecV).isSome ∧ (c.sortOf ctrV).isSome ∧ (c.sortOf tV).isSome ∧
    (c.sortOf topV).isSome ∧ c.sortsOf [w1, key] = some lookupSig.args ∧ c.sortsOf [w0, key] = some lookupSig.args := by
  decide +kernel

/-- What `G` gives: the values at `w1`, none at `w0`. -/
theorem gvals : lookupV w1 = some pgm ∧ hook mapLookup [w1, key] = some (some pgm) ∧
    hook mapLookup [w0, key] = some none ∧ silent mapLookup [w0, key] = false ∧
    projFn c exp item = some aV ∧ gK w1 = some kV ∧ gT w1 = some tV ∧ gTop w1 = some topV ∧
    gK w0 = none ∧ gT w0 = none ∧ gTop w0 = none := by
  decide +kernel

theorem iteNone : instDecode? (c.symName mapLookup) = none := by decide +kernel

theorem constSorts : c.sortOf oneV = some oneS ∧ c.sortOf ecV = some ecS := by decide +kernel

open InitModel in
/-- **One model of the theory, whose steps are the semantics' steps, holds the initializers'
equations down the cell tree**: the constants' with their `functional` axioms, each equation at `w1` with its value, at `w0`
with neither side a value, and the getter at the initial configuration. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (app initOne [] ≡ den c oneV)) ∧ (I ⊧ᴵ (app initEc [] ≡ den c ecV)) ∧
      (I ⊧ᴵ (app initCtr [] ≡ den c ctrV)) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (KoreAML.Cons.sortP "OneCell") (.evar ⟨1⟩ ≡ app initOne [])) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (KoreAML.Cons.sortP "EcCell") (.evar ⟨1⟩ ≡ app initEc [])) ∧
      (I ⊧ᴵ (app initK [den c w1] ≡ rhsK (den c w1))) ∧ (I ⊧ᴵ (app initT [den c w1] ≡ rhsT (den c w1))) ∧
      (I ⊧ᴵ (app initTop [den c w1] ≡ rhsTop (den c w1))) ∧ (I ⊧ᴵ (app initTop [den c w1] ≡ den c topV)) ∧
      (I ⊧ᴵ (app getter [app initTop [den c w1]] ≡ den c ctrV)) ∧
      (I ⊧ᴵ (app initK [den c w0] ≡ rhsK (den c w0))) ∧ (I ⊧ᴵ (app initT [den c w0] ≡ rhsT (den c w0))) ∧
      (I ⊧ᴵ (app initTop [den c w0] ≡ rhsTop (den c w0))) ∧ (I ⊧ᴵ (app initTop [den c w0] ≡ ⊥)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_with_inits_step c coreOK fnHyp inits ar G unnumbered
  obtain ⟨hw1, hw0, hkey, hpgm, haV, hdot, hitem, hkV, hone, hec, hctr, htV, htop, hs1, hs0⟩ := sorts
  obtain ⟨-, hl1, hl0, hsil0, hpr, hgK1, hgT1, hgTop1, hgK0, hgT0, hgTop0⟩ := gvals
  have mem : ∀ {n}, n ∈ names → inits n := fun h => h
  have vw1 := hM.val (srt hw1)
  have vw0 := hM.val (srt hw0)
  have vkey := hM.val (srt hkey)
  -- the constants
  have dOne : DenV c I (app initOne []) oneV := hM.name (mem (by decide)) .nil rfl (by simp [G]) (srt hone)
  have dEc : DenV c I (app initEc []) ecV := hM.name (mem (by decide)) .nil rfl (by simp [G, initEc, initOne]) (srt hec)
  have dCtr : DenV c I (app initCtr []) ctrV :=
    hM.name (mem (by decide)) .nil rfl (by simp [G, initEc, initOne, initCtr]) (srt hctr)
  have dDot : DenV c I (app (c.symName dotk) []) dotK := hM.ctor .nil (srt hdot)
  -- `initKCell` at w1, its right side bottom up
  have dLk : DenV c I (app (c.symName mapLookup) [den c w1, den c key]) pgm :=
    hM.hookV lookupSig_mem iteNone (.cons vw1 (.cons vkey .nil)) hs1 hl1 (srt hpgm)
  have dItem : DenV c I (app (c.symName kseq) [app (c.symName mapLookup) [den c w1, den c key], app (c.symName dotk) []]) item :=
    hM.ctor (.cons dLk (.cons dDot .nil)) (srt hitem)
  have dPr := hM.name (mem (by decide)) (.cons dItem .nil) rfl (n := projExp) (by simpa [G, initK, initT, initTop, getter, projExp] using hpr)
    (srt haV)
  have dInj := hM.inj exp Srt.kitem dPr (srt hpgm)
  have dSeq := hM.ctor (f := kseq) (.cons dInj (.cons dDot .nil)) (srt hitem)
  have dRK1 : DenV c I (rhsK (den c w1)) kV := hM.ctor (.cons dSeq .nil) (srt hkV)
  have dK1 : DenV c I (app initK [den c w1]) kV := hM.name (mem (by decide)) (.cons vw1 .nil) rfl (by simpa [G] using hgK1)
    (srt hkV)
  -- `initTCell` and `initGeneratedTopCell` at w1, through the initializers below
  have dRT1 : DenV c I (rhsT (den c w1)) tV := hM.ctor (.cons dK1 (.cons dOne (.cons dEc .nil))) (srt htV)
  have dT1 : DenV c I (app initT [den c w1]) tV := hM.name (mem (by decide)) (.cons vw1 .nil) rfl
    (by simpa [G, initK, initT] using hgT1) (srt htV)
  have dRTop1 : DenV c I (rhsTop (den c w1)) topV := hM.ctor (.cons dT1 (.cons dCtr .nil)) (srt htop)
  have dTop1 : DenV c I (app initTop [den c w1]) topV := hM.name (mem (by decide)) (.cons vw1 .nil) rfl
    (by simpa [G, initK, initT, initTop] using hgTop1) (srt htop)
  have dGet : DenV c I (app getter [app initTop [den c w1]]) ctrV := hM.name (mem (by decide)) (.cons dTop1 .nil) rfl
    (by simp [G, initK, initT, initTop, getter, topV, argFn_ctor]) (srt hctr)
  -- at w0: `Map:lookup(.Map, $PGM)` has no value, nor has any right side above it
  have eLk : DenE I (app (c.symName mapLookup) [den c w0, den c key]) :=
    hM.hookE lookupSig_mem iteNone (.cons vw0 (.cons vkey .nil)) hs0 hl0 hsil0
  have eItem0 : DenE I (app (c.symName kseq) [app (c.symName mapLookup) [den c w0, den c key], app (c.symName dotk) []]) :=
    DenE.app _ ⟨_, List.mem_cons_self .., eLk⟩
  have ePr0 : DenE I (app projExp [app (c.symName kseq) [app (c.symName mapLookup) [den c w0, den c key],
      app (c.symName dotk) []]]) := DenE.app _ ⟨_, List.mem_cons_self .., eItem0⟩
  have eInj0 : DenE I (injA (c.sortName exp) (c.sortName Srt.kitem) (app projExp [app (c.symName kseq)
      [app (c.symName mapLookup) [den c w0, den c key], app (c.symName dotk) []]])) :=
    DenE.app _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ePr0⟩
  have eRK0 : DenE I (rhsK (den c w0)) :=
    DenE.app _ ⟨_, List.mem_cons_self .., DenE.app _ ⟨_, List.mem_cons_self .., eInj0⟩⟩
  have eK0 : DenE I (app initK [den c w0]) := hM.name_none (mem (by decide)) (.cons vw0 .nil) rfl (by simpa [G] using hgK0)
  have eRT0 : DenE I (rhsT (den c w0)) := DenE.app _ ⟨_, List.mem_cons_self .., eK0⟩
  have eT0 : DenE I (app initT [den c w0]) := hM.name_none (mem (by decide)) (.cons vw0 .nil) rfl
    (by simpa [G, initK, initT] using hgT0)
  have eRTop0 : DenE I (rhsTop (den c w0)) := DenE.app _ ⟨_, List.mem_cons_self .., eT0⟩
  have eTop0 : DenE I (app initTop [den c w0]) := hM.name_none (mem (by decide)) (.cons vw0 .nil) rfl
    (by simpa [G, initK, initT, initTop] using hgTop0)
  exact ⟨I, hM.sat, hM.eqn dOne (hM.val (srt hone)), hM.eqn dEc (hM.val (srt hec)),
    hM.eqn dCtr (hM.val (srt hctr)),
    text_names.2.2.2.2.2.2.2.2.2.2.2.1 ▸ hM.functional dOne constSorts.1 ⟨1⟩,
    text_names.2.2.2.2.2.2.2.2.2.2.2.2 ▸ hM.functional dEc constSorts.2 ⟨1⟩, hM.eqn dK1 dRK1, hM.eqn dT1 dRT1, hM.eqn dTop1 dRTop1,
    hM.eqn dTop1 (hM.val (srt htop)), hM.eqn dGet (hM.val (srt hctr)),
    hM.eqn_none eK0 eRK0, hM.eqn_none eT0 eRT0, hM.eqn_none eTop0 eRTop0, hM.eqn_none eTop0 (fun _ _ h => h),
    hstep⟩

end Cells

namespace Fresh

definition_of defn from "f2-examples/freshcfg.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

def names : List String := [initK, initId, initTop, initCtr, getter, projExp]

theorem unnumbered : ∀ n ∈ names, (regSymNames ++ c.symNames).contains n = false ∧ n ≠ "" ∧ n ≠ "inj" ∧
    n ≠ "Lblite" ∧ c.instHeadFree n = true := by decide +kernel

/-- The arities the text declares: `initIdCell` and `initGeneratedTopCell` take `(Init, #Configuration)`. -/
def ar : String → Nat := fun n => if n = initCtr then 0 else if n = initId ∨ n = initTop then 2 else 1

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def exp : Srt := nRegSorts + c.sortNames.idxOf "Exp"
noncomputable def kL : Sym := symN "Lbl'-LT-'k'-GT-'"
noncomputable def idL : Sym := symN "Lbl'-LT-'id'-GT-'"

theorem text_names : c.symName kL = "Lbl'-LT-'k'-GT-'" ∧ c.symName idL = "Lbl'-LT-'id'-GT-'" ∧
    c.symName topLabel = "Lbl'-LT-'generatedTop'-GT-'" ∧ c.symName counterLabel = "Lbl'-LT-'generatedCounter'-GT-'" ∧
    c.symName kseq = "kseq" ∧ c.symName dotk = "dotk" ∧ c.symName mapLookup = "LblMap'Coln'lookup" ∧
    c.sortName exp = "Exp" ∧ c.sortName Srt.kitem = "KItem" := by decide +kernel

noncomputable def aV : GroundTerm := .ctor (symN "Lbla") []
noncomputable def pgm : GroundTerm := .inj exp Srt.kitem aV
noncomputable def w1 : GroundTerm := .map Srt.map [(key, pgm)]
noncomputable def idV : GroundTerm := .ctor idL [zero]
/-- The counter's initial value is 1: the configuration holds a fresh variable. -/
def ctrV : GroundTerm := .ctor counterLabel [one]
noncomputable def item : GroundTerm := .ctor kseq [pgm, dotK]
noncomputable def kV : GroundTerm := .ctor kL [.ctor kseq [pgm, dotK]]
/-- The initial configuration at `w1`. -/
noncomputable def topV : GroundTerm := .ctor topLabel [kV, idV, ctrV]

noncomputable def gK (w : GroundTerm) : Option GroundTerm := do
  let v ← lookupV w
  let e ← projFn c exp (.ctor kseq [v, dotK])
  pure (.ctor kL [.ctor kseq [.inj exp Srt.kitem e, dotK]])
noncomputable def gTop (w : GroundTerm) : Option GroundTerm := (gK w).map fun k => .ctor topLabel [k, idV, ctrV]

noncomputable def G : String → List GroundTerm → Option GroundTerm
  | n, [] => if n = initCtr then some ctrV else none
  | n, [w] => if n = initK then gK w else if n = getter then argFn topLabel 2 w
      else if n = projExp then projFn c exp w else none
  | n, [w, _] => if n = initId then some idV else if n = initTop then gTop w else none
  | _, _ => none

def inits : String → Prop := fun n => n ∈ names

/-- `initGeneratedTopCell`'s right side at `(x, y)`:
`<generatedTop>(initKCell(x), initIdCell(x, y), initGeneratedCounterCell())`. -/
noncomputable def rhsTop (x y : KoreAML.P) : KoreAML.P :=
  app (c.symName topLabel) [app initK [x], app initId [x, y], app initCtr []]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf w0).isSome ∧ (c.sortOf key).isSome ∧ (c.sortOf pgm).isSome ∧
    (c.sortOf aV).isSome ∧ (c.sortOf dotK).isSome ∧ (c.sortOf item).isSome ∧ (c.sortOf kV).isSome ∧
    (c.sortOf idV).isSome ∧ (c.sortOf ctrV).isSome ∧ c.sortOf topV = some topCellSort ∧
    c.sortsOf [w1, key] = some lookupSig.args ∧ c.sortsOf [w0, key] = some lookupSig.args := by
  decide +kernel

theorem gvals : hook mapLookup [w1, key] = some (some pgm) ∧ hook mapLookup [w0, key] = some none ∧
    silent mapLookup [w0, key] = false ∧ projFn c exp item = some aV ∧ gK w1 = some kV ∧ gTop w1 = some topV ∧
    gK w0 = none ∧ gTop w0 = none := by
  decide +kernel

theorem iteNone : instDecode? (c.symName mapLookup) = none := by decide +kernel

open InitModel in
/-- **One model of the theory, whose steps are the semantics' steps, holds the initializers'
equations at two arguments**: `initIdCell(w1, t) = <id>(0)`, `initGeneratedTopCell(w1, t)` its right
side and the initial configuration, at the initial configuration `t`, and at the empty map both
sides of `initGeneratedTopCell`'s equation denoting nothing. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (app initCtr [] ≡ den c ctrV)) ∧ (I ⊧ᴵ (app initId [den c w1, den c topV] ≡ den c idV)) ∧
      (I ⊧ᴵ (app initTop [den c w1, den c topV] ≡ rhsTop (den c w1) (den c topV))) ∧
      (I ⊧ᴵ (app initTop [den c w1, den c topV] ≡ den c topV)) ∧
      (I ⊧ᴵ (app initTop [den c w0, den c topV] ≡ rhsTop (den c w0) (den c topV))) ∧
      (I ⊧ᴵ (app initTop [den c w0, den c topV] ≡ ⊥)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_with_inits_step c coreOK fnHyp inits ar G unnumbered
  obtain ⟨hw1, hw0, hkey, -, -, -, -, hkV, hid, hctr, htop, -, hs0⟩ := sorts
  obtain ⟨-, hl0, hsil0, -, hgK1, hgTop1, hgK0, hgTop0⟩ := gvals
  have mem : ∀ {n}, n ∈ names → inits n := fun h => h
  have vw1 := hM.val (srt hw1)
  have vw0 := hM.val (srt hw0)
  have vkey := hM.val (srt hkey)
  have vtop := hM.val htop
  have dCtr : DenV c I (app initCtr []) ctrV := hM.name (mem (by decide)) .nil rfl (by simp [G]) (srt hctr)
  have dId : DenV c I (app initId [den c w1, den c topV]) idV :=
    hM.name (mem (by decide)) (.cons vw1 (.cons vtop .nil)) rfl (by simp [G]) (srt hid)
  have dK1 : DenV c I (app initK [den c w1]) kV := hM.name (mem (by decide)) (.cons vw1 .nil) rfl (by simpa [G] using hgK1)
    (srt hkV)
  have dRTop1 : DenV c I (rhsTop (den c w1) (den c topV)) topV := hM.ctor (.cons dK1 (.cons dId (.cons dCtr .nil))) htop
  have dTop1 : DenV c I (app initTop [den c w1, den c topV]) topV := hM.name (mem (by decide)) (.cons vw1 (.cons vtop .nil)) rfl
    (by simpa [G, initId, initTop] using hgTop1) htop
  have eLk : DenE I (app (c.symName mapLookup) [den c w0, den c key]) :=
    hM.hookE lookupSig_mem iteNone (.cons vw0 (.cons vkey .nil)) hs0 hl0 hsil0
  have eK0 : DenE I (app initK [den c w0]) := hM.name_none (mem (by decide)) (.cons vw0 .nil) rfl (by simpa [G] using hgK0)
  have eRTop0 : DenE I (rhsTop (den c w0) (den c topV)) := DenE.app _ ⟨_, List.mem_cons_self .., eK0⟩
  have eTop0 : DenE I (app initTop [den c w0, den c topV]) := hM.name_none (mem (by decide)) (.cons vw0 (.cons vtop .nil)) rfl
    (by simpa [G, initId, initTop] using hgTop0)
  exact ⟨I, hM.sat, hM.eqn dCtr (hM.val (srt hctr)), hM.eqn dId (hM.val (srt hid)), hM.eqn dTop1 dRTop1,
    hM.eqn dTop1 vtop, hM.eqn_none eTop0 eRTop0, hM.eqn_none eTop0 (fun _ _ h => h), hstep⟩

end Fresh

/-- info: 'GenEqsInits.Cells.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cells.eqns
/-- info: 'GenEqsInits.Fresh.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fresh.eqns
/-- info: 'KCore.GenEqs.model_with_inits_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_with_inits_step

end GenEqsInits
