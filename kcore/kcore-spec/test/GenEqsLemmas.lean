/-
  Instances of `KcoreSpec/GenEqsConservative.lean` on corpus-shaped texts. Run from the package
  root: `lake env lean -j1 test/GenEqsLemmas.lean`.

  ## Sort predicates (`Hand`, as `test/PredContent.lean`'s)

  One own sort Foo with `pair(Foo, Foo) : Foo`, and the two equations kompile writes for its
  predicate: `std`, `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true`, and `ow [dStd]`,
  `isFoo(K) = false [owise]` whose one disjunct excludes `std`. `predProjOK?` accepts both
  (`decide +kernel`), so by `GenEqs.sortPredEqn_in_Γ` each is read as a clause of `isFoo`'s
  `sortPreds` function whose equation is a premise of `Γ` (`std_in_Γ`, `ow_in_Γ`), and the `[owise]`
  one's disjunct pairs with the clause it negates, `std`'s, read back as that clause
  (`ow_excl`, by `GenEqs.predEqnOK_clause`).

  ## Registry projections (`Nx`, `f2-examples/owisenx.kompile.kore`)

  The text declares the projections of the registry sorts it holds (`project:Int`, `project:K`,
  `project:KItem`, ...) and holds their generated equations; no sentence it reads applies one. The
  registry's `projectSym X` of every registry sort X whose number names `project:X` (`regProjs`) is
  free of the theory (`free`, `GenEqs.freeB`, a kernel decision), so no premise of `Γc c ∪ Γstep c`
  applies `project:Int`, `project:K` or `project:KItem` (`int_free`, `k_free`, `kitem_free`).

  The model half: every premise of the theory is rooted (`rooted`, a kernel decision), so the value
  model at any transition with `project:Int`, `project:K` and `project:KItem` applied by any `F`
  is a model of the theory wherever the value model is (`proj_patch`), and under the functions'
  obligations the theory has a model in which the three projections' equations at the item of
  `0` hold together (`proj_eqns`, `GenEqs.model_with_eqns`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsLemmas

namespace Hand

open KoreAML (ev evar ap srt asK uidAttr attr R)

def Foo : Srt := nRegSorts
def isFoo : Sym := nRegSyms
def pairS : Sym := nRegSyms + 1

def N : Names := { sorts := ["Foo"], syms := ["LblisFoo", "Lblpair"] }

def c : Semantics :=
  { lib := libOf [], sortNames := N.sorts, symNames := N.syms, userSorts := [Foo]
    ctors := [⟨pairS, [Foo, Foo], Foo⟩], fns := [], userSubsorts := [], pgmSort := Srt.k, rules := [] }

def tt : Kore.Pattern := .dv (srt "Bool") "true"
def ff : Kore.Pattern := .dv (srt "Bool") "false"
def item (p : Kore.Pattern) : Kore.Pattern := asK "Foo" p

def std : RawEqn := ⟨"LblisFoo", [item (ev "VarV" (srt "Foo"))], none, none, tt, [uidAttr "std"], none, false⟩

def disjunct (xs : List Kore.EVar) (req p : Kore.Pattern) : Kore.Pattern :=
  KoreAML.existsAll R xs (.and R [req, .and R [.in (srt "K") R (ev "X0" (srt "K")) p, .top R]])

def dStd : Kore.Pattern :=
  disjunct [evar "Var'Unds'Gen2" (srt "Foo")] (.top R) (item (ev "Var'Unds'Gen2" (srt "Foo")))

def ow (ds : List Kore.Pattern) : RawEqn :=
  ⟨"LblisFoo", [ev "VarK" (srt "K")], none, some ds, ff, [uidAttr "ow", attr "owise"], none, false⟩

def eqs : List RawEqn := [ow [dStd], std]

theorem std_ok : predProjOK? N "" eqs c std = some true := by decide +kernel
theorem ow_ok : predProjOK? N "" eqs c (ow [dStd]) = some true := by decide +kernel

/-- **The standard equation is a clause of `isFoo` that `Γ` states.** -/
theorem std_in_Γ : ∃ fn ∈ c.sortPreds, c.symName fn.label = "LblisFoo" ∧ ∃ cl cp, clause? N "" std none = .ok (cl, cp) ∧
    cl ∈ fn.clauses ∧ ∀ it ∈ Faithful.kernelItems [Faithful.prioEquation c fn cl], Faithful.Γ c it.pat :=
  sortPredEqn_in_Γ std_ok (by decide)

/-- **The `[owise]` equation is a clause of `isFoo` that `Γ` states.** -/
theorem ow_in_Γ : ∃ fn ∈ c.sortPreds, c.symName fn.label = "LblisFoo" ∧ ∃ cl cp, clause? N "" (ow [dStd]) none = .ok (cl, cp) ∧
    cl ∈ fn.clauses ∧ ∀ it ∈ Faithful.kernelItems [Faithful.prioEquation c fn cl], Faithful.Γ c it.pat :=
  sortPredEqn_in_Γ ow_ok (by decide)

/-- **The `[owise]` equation's one disjunct pairs with the clause it negates**, read back as it. -/
theorem ow_excl : ∃ fn ∈ c.sortPreds, ∃ cl cp, clause? N "" (ow [dStd]) none = .ok (cl, cp) ∧ cl ∈ fn.clauses ∧
    ∃ es : List (RawEqn × Clause), es.map (·.2) = Faithful.lowerClauses fn cl ∧ es.length = 1 ∧
      ∀ q ∈ (pairExcl (es.map (·.1)) [dStd]).zip es, ∃ cp', clause? N "" q.1.1 q.1.2 = .ok (q.2.2, cp') := by
  obtain ⟨fn, hfn, -, hok⟩ := predProjOK_sortPred ow_ok (by decide)
  obtain ⟨cl, cp, hc, hcl, hex⟩ := predEqnOK_clause hok
  obtain ⟨es, h1, h2, h3⟩ := hex [dStd] rfl
  exact ⟨fn, hfn, cl, cp, hc, hcl, es, h1, h2.symm, h3⟩

end Hand

namespace Nx

definition_of defn from "f2-examples/owisenx.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The registry's projections whose number names `project:X`. -/
noncomputable def regProjs : List Sym :=
  ((List.range nRegSorts).filter fun X => c.symName (projectSym X) == "Lblproject'Coln'" ++ c.sortName X).map projectSym

theorem names : c.symName (projectSym Srt.int) = "Lblproject'Coln'Int" ∧
    c.symName (projectSym Srt.k) = "Lblproject'Coln'K" ∧ c.symName (projectSym Srt.kitem) = "Lblproject'Coln'KItem" := by
  decide +kernel

theorem mems : projectSym Srt.int ∈ regProjs ∧ projectSym Srt.k ∈ regProjs ∧ projectSym Srt.kitem ∈ regProjs := by
  decide +kernel

/-- **No premise of the theory applies a registry projection** (decided). -/
theorem free : freeB c regProjs = true := by
  rw [freeB, DetachedB.listsB, DetachedB.valuesB, DetachedB.graphsB]; decide_cheap 40

theorem int_free : ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol "Lblproject'Coln'Int" ∉ psyms φ := by
  have := sym_free c regProjs coreOK free mems.1
  rwa [names.1] at this

theorem k_free : ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol "Lblproject'Coln'K" ∉ psyms φ := by
  have := sym_free c regProjs coreOK free mems.2.1
  rwa [names.2.1] at this

theorem kitem_free : ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol "Lblproject'Coln'KItem" ∉ psyms φ := by
  have := sym_free c regProjs coreOK free mems.2.2
  rwa [names.2.2] at this

/-! The model half (`KcoreSpec/GenEqsModel.lean`) at `project:Int`, `project:K` and
`project:KItem` together. -/

/-- Every premise of the theory is rooted (decided on its lists). -/
theorem rooted : rootedListsB c = true := by rw [rootedListsB]; decide_cheap 40

def projNames : String → Prop := fun n => n ∈ ["Lblproject'Coln'Int", "Lblproject'Coln'K", "Lblproject'Coln'KItem"]

/-- The three projections on values: Int's through the item, K's the identity, KItem's the item. -/
noncomputable def projG : String → GroundTerm → Option GroundTerm := fun n =>
  if n = "Lblproject'Coln'Int" then projFn c Srt.int
  else if n = "Lblproject'Coln'K" then some
  else if n = "Lblproject'Coln'KItem" then itemFn
  else fun _ => none

theorem proj_free : ∀ n, projNames n → ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ := by
  intro n hn
  simp only [projNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact int_free
  · exact k_free
  · exact kitem_free

/-- Each resolves to no constant: the symbol holds of its head only. -/
theorem proj_spare : ∀ n, projNames n → spareSymB c n = true := by
  intro n hn
  simp only [projNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;> decide +kernel

def zero : GroundTerm := .dv Srt.int (.int 0)
def zeroKItem : GroundTerm := .inj Srt.int Srt.kitem zero
def zeroItem : GroundTerm := .ctor kseq [zeroKItem, .ctor dotk []]

theorem zero_sort : c.sortOf zero = some Srt.int := by decide +kernel
theorem zeroKItem_sort : c.sortOf zeroKItem = some Srt.kitem := by decide +kernel
theorem zeroItem_sort : c.sortOf zeroItem = some Srt.k := by decide +kernel

/-- **The value model with the three projections applied by any `F` is a model of the theory**
wherever the value model is, at every transition. -/
theorem proj_patch (T : GroundTerm → GroundTerm → Prop)
    (F : Faithful.Model.Elem → Faithful.Model.Elem → Set Faithful.Model.Elem)
    (hI : Faithful.Model.stdI_T c T ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) :
    stdPatch c T projNames F ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c) :=
  stdPatch_model c T _ F rooted proj_free hI

/-- **The theory with the three projections' equations at `0` has a model**, under the functions'
obligations: in one model of the theory, `project:Int(kseq(inj{Int,KItem}(0), dotk)) = 0`,
`project:K` of that sequence is the sequence, and `project:KItem` of it is `inj{Int,KItem}(0)`. -/
theorem proj_eqns (hf : FnHyp c) :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (symP "Lblproject'Coln'Int" ⬝ den c zeroItem ≡ den c zero)) ∧
      (I ⊧ᴵ (symP "Lblproject'Coln'K" ⬝ den c zeroItem ≡ den c zeroItem)) ∧
      (I ⊧ᴵ (symP "Lblproject'Coln'KItem" ⬝ den c zeroItem ≡ den c zeroKItem)) := by
  obtain ⟨I, h1, h2, -⟩ := model_with_eqns c coreOK hf projNames projG rooted proj_free proj_spare
  refine ⟨I, h1, h2 _ (by simp [projNames]) _ _ _ _ zeroItem_sort zero_sort ?_,
    h2 _ (by simp [projNames]) _ _ _ _ zeroItem_sort zeroItem_sort ?_,
    h2 _ (by simp [projNames]) _ _ _ _ zeroItem_sort zeroKItem_sort ?_⟩
  · simp only [projG, ↓reduceIte]
    exact projFn_item c Srt.int (by decide +kernel) zero_sort
  · simp [projG]
  · simp [projG]
    exact itemFn_item _

end Nx

/-! ## Names the semantics does not number, and the kconfig equation, at the semantics' steps

`f2-examples/prio.kore`, krust's text of `prio.k` (three rules, no function, no parameter). The
semantics numbers neither `project:B`, `project:KCell` nor `getGeneratedCounterCell`
(`unnumbered`: none is a registry name or one of the definition's), and no premise of the theory
holds one (`free`, `GenEqs.nameFreeB`); no premise applies `#unboxKConfigValue`, a registry symbol
(`unbox_free`, `GenEqs.freeB`). With `FnHyp` (no function, no rule needing a witness, no raw
parameter: `fnHyp`), one model of the theory whose steps at configurations are `Step`'s holds the
four equations together (`eqns`, `GenEqs.model_with_eqns_step`): `project:B` at the item of the B
value `d`, `project:KCell` at the item of `<k>(.K)`, the getter at
`<generatedTop>(<k>(.K), <generatedCounter>(0))`, which is `<generatedCounter>(0)`, and
`#unboxKConfigValue(#KConfigValue(.K)) = .K`, the text's kconfig equation at `.K`. -/

namespace Prio

definition_of defn from "f2-examples/prio.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem rooted : rootedListsB c = true := by rw [rootedListsB]; decide_cheap 40

def projB : String := "Lblproject'Coln'B"
def projKCell : String := "Lblproject'Coln'KCell"
def getter : String := "LblgetGeneratedCounterCell"
def unbox : String := "Lbl'Hash'unboxKConfigValue"

def names : List String := [projB, projKCell, getter]

/-- None of the three is a name the semantics numbers. -/
theorem unnumbered : names.all (fun n => !(regSymNames ++ c.symNames).contains n) = true := by decide +kernel

/-- **No premise of the theory holds the three** (decided). -/
theorem free : nameFreeB c names = true := by
  rw [nameFreeB, NameFree.listsN, NameFree.valuesN, NameFree.graphsN]; decide_cheap 40

theorem unbox_free : freeB c [unboxKConfigValue] = true := by
  rw [freeB, DetachedB.listsB, DetachedB.valuesB, DetachedB.graphsB]; decide_cheap 40

theorem unbox_name : c.symName unboxKConfigValue = unbox := by decide +kernel

def eqNames : String → Prop := fun n => n ∈ names ∨ n = unbox

theorem eq_free : ∀ n, eqNames n → ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ := by
  rintro n (hn | rfl)
  · exact nameFree_of_decided c names coreOK free n hn
  · have := sym_free c [unboxKConfigValue] coreOK unbox_free (List.mem_singleton.mpr rfl)
    rwa [unbox_name] at this

theorem eq_spare : ∀ n, eqNames n → spareSymB c n = true := by
  rintro n (hn | rfl)
  · simp only [names, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> decide +kernel
  · decide +kernel

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def sortN (n : String) : Srt := nRegSorts + c.sortNames.idxOf n
noncomputable def sortB : Srt := sortN "B"
noncomputable def sortD : Srt := sortN "D"
noncomputable def sortKCell : Srt := sortN "KCell"

def dotK : GroundTerm := .ctor dotk []
def zero : GroundTerm := .dv Srt.int (.int 0)
/-- The item of a value `v` of sort `X`. -/
def itemOf (X : Srt) (v : GroundTerm) : GroundTerm := .ctor kseq [injNormal X Srt.kitem v, dotK]
/-- `d` as a value of B. -/
noncomputable def dB : GroundTerm := .inj sortD sortB (.ctor (symN "Lbld") [])
noncomputable def kcellV : GroundTerm := .ctor (symN "Lbl'-LT-'k'-GT-'") [dotK]
noncomputable def counterV : GroundTerm := .ctor counterLabel [zero]
noncomputable def topV : GroundTerm := .ctor topLabel [kcellV, counterV]
def kconfigV : GroundTerm := .ctor kconfigValue [dotK]

/-- The four symbols on values: the two projections through the item, the getter the top cell's
second argument, `#unboxKConfigValue` the argument of `#KConfigValue`. -/
noncomputable def eqG : String → GroundTerm → Option GroundTerm := fun n =>
  if n = projB then projFn c sortB
  else if n = projKCell then projFn c sortKCell
  else if n = getter then argFn topLabel 1
  else if n = unbox then argFn kconfigValue 0
  else fun _ => none

theorem sorts : c.sortOf dB = some sortB ∧ c.sortOf (itemOf sortB dB) = some Srt.k ∧
    c.sortOf kcellV = some sortKCell ∧ c.sortOf (itemOf sortKCell kcellV) = some Srt.k ∧
    c.sortOf topV = some topCellSort ∧ c.sortOf counterV = some Srt.counter ∧
    c.sortOf kconfigV = some Srt.kitem ∧ c.sortOf dotK = some Srt.k := by
  decide +kernel

theorem not_self : (sortB, sortB) ∉ c.subsorts ∧ (sortKCell, sortKCell) ∉ c.subsorts := by decide +kernel

/-- **One model of the theory, whose steps are the semantics' steps, holds the four equations.** -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (symP projB ⬝ den c (itemOf sortB dB) ≡ den c dB)) ∧
      (I ⊧ᴵ (symP projKCell ⬝ den c (itemOf sortKCell kcellV) ≡ den c kcellV)) ∧
      (I ⊧ᴵ (symP getter ⬝ den c topV ≡ den c counterV)) ∧
      (I ⊧ᴵ (symP unbox ⬝ den c kconfigV ≡ den c dotK)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨hdB, hiB, hk, hik, htop, hctr, hkc, hdot⟩ := sorts
  obtain ⟨I, h1, h2, h3⟩ := model_with_eqns_step c coreOK fnHyp eqNames eqG rooted eq_free eq_spare
  refine ⟨I, h1, h2 _ (.inl (by simp [names])) _ _ _ _ hiB hdB ?_,
    h2 _ (.inl (by simp [names])) _ _ _ _ hik hk ?_, h2 _ (.inl (by simp [names])) _ _ _ _ htop hctr ?_,
    h2 _ (.inr rfl) _ _ _ _ hkc hdot ?_, h3⟩
  · simp only [eqG, ↓reduceIte, itemOf]
    exact projFn_item c sortB not_self.1 hdB
  · have h : projKCell ≠ projB := by decide
    simp only [eqG, h, ↓reduceIte, itemOf]
    exact projFn_item c sortKCell not_self.2 hk
  · have h1 : getter ≠ projB := by decide
    have h2 : getter ≠ projKCell := by decide
    simp only [eqG, h1, h2, ↓reduceIte, topV, argFn_ctor]
    rfl
  · have h1 : unbox ≠ projB := by decide
    have h2 : unbox ≠ projKCell := by decide
    have h3 : unbox ≠ getter := by decide
    simp only [eqG, h1, h2, h3, ↓reduceIte, kconfigV, argFn_ctor]
    rfl

end Prio

/-! ## A constructor argument's projection (G8)

A hand-built semantics of kompile's shape: the configuration `<k> K </k>` with the generated
counter, and an own sort `Foo ::= leaf() | pair(left: Foo, right: Foo)`, whose named arguments kompile
gives the projections `project:pair:left` and `project:pair:right` with the equations
`project:pair:left(pair(K0, K1)) = K0` and the like (as it does for K-IO's `#tempFile` and
`#unknownIOError`; the corpus texts that hold such projections are the K-IO ones, 785 KB and up). Neither name is a registry name or one of the
semantics' own, so each resolves to no constant (`GenEqs.spareSymB_of_argProj`), and no premise of
the theory holds one (`free`, `GenEqs.nameFreeB`). Under `FnHyp` (no function), one model of the
theory whose steps are `Step`'s holds both projections' equations at `pair(leaf, pair(leaf, leaf))`
(`eqns`, `GenEqs.model_with_eqns_step` with `GenEqs.argFn`). -/

namespace HandArg

open KCore.Faithful.SortsWitness (cellSorts cellCtors cellSubsorts)

/-- The own sort Foo, after the `k` cell's two sorts; its predicate beside theirs, `leaf` and `pair` after the
four cell symbols. -/
def Foo : Srt := nRegSorts + 2
def leafS : Sym := nRegSyms + 5
def pairS : Sym := nRegSyms + 6

/-- The configuration `<k> K </k>` with the generated counter, and the own sort
`Foo ::= leaf() | pair(left: Foo, right: Foo)`. -/
def c : Semantics :=
  { lib := {}, sortNames := ["KCell", "KCellOpt", "Foo"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisFoo", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblleaf", "Lblpair"]
    userSorts := cellSorts ++ [Foo]
    ctors := cellCtors ++ [⟨leafS, [], Foo⟩, ⟨pairS, [Foo, Foo], Foo⟩], fns := []
    userSubsorts := cellSubsorts, pgmSort := Srt.k, rules := [] }

theorem coreOK : c.coreOK = true := by decide_coreOK

theorem rooted : rootedListsB c = true := by decide +kernel

def left : String := "Lblproject'Coln'pair'Coln'left"
def right : String := "Lblproject'Coln'pair'Coln'right"
def names : List String := [left, right]

theorem free : nameFreeB c names = true := by decide +kernel

def argNames : String → Prop := fun n => n ∈ names

theorem arg_free : ∀ n, argNames n → ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ :=
  nameFree_of_decided c names coreOK free

theorem arg_spare : ∀ n, argNames n → spareSymB c n = true := by
  intro n hn
  simp only [argNames, names, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl <;>
    exact spareSymB_of_argProj c (by decide) (by decide +kernel) (by decide +kernel)

def argG : String → GroundTerm → Option GroundTerm := fun n =>
  if n = left then argFn pairS 0 else if n = right then argFn pairS 1 else fun _ => none

def leafV : GroundTerm := .ctor leafS []
def pairV : GroundTerm := .ctor pairS [leafV, .ctor pairS [leafV, leafV]]

theorem sorts : c.sortOf leafV = some Foo ∧ c.sortOf pairV = some Foo ∧
    c.sortOf (.ctor pairS [leafV, leafV]) = some Foo := by decide +kernel

theorem fns_nil : c.fns = [] := rfl
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-- **One model of the theory, whose steps are the semantics' steps, holds both projections'
equations** at `pair(leaf, pair(leaf, leaf))`. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (symP left ⬝ den c pairV ≡ den c leafV)) ∧
      (I ⊧ᴵ (symP right ⬝ den c pairV ≡ den c (.ctor pairS [leafV, leafV]))) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨hl, hp, hp2⟩ := sorts
  obtain ⟨I, h1, h2, h3⟩ := model_with_eqns_step c coreOK fnHyp argNames argG rooted arg_free arg_spare
  refine ⟨I, h1, h2 _ (by simp [argNames, names]) _ _ _ _ hp hl ?_,
    h2 _ (by simp [argNames, names]) _ _ _ _ hp hp2 ?_, h3⟩
  · simp only [argG, ↓reduceIte, pairV, argFn_ctor]
    rfl
  · have h : right ≠ left := by decide
    simp only [argG, h, ↓reduceIte, pairV, argFn_ctor]
    rfl

end HandArg

/-! ## Without kernel decisions of the theory's lists

`GenEqs.rootedListsB_holds` gives rootedness of every semantics, and `GenEqs.nameFree_of_argProj`
freeness of a constructor argument's projection from the conditions the account's arm checks of its
name; `GenEqs.model_with_eqns_argProj` puts them together with `spareSymB_of_argProj`. -/

namespace General

/-- Every semantics' lists are rooted. -/
example (c : Semantics) : rootedListsB c = true := rootedListsB_holds c

/-- The symbols a premise holds are the semantics' own, `inj` or `Lblite`. -/
example (c : Semantics) (h : c.coreOK = true) :
    ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → ∀ n, KoreAML.Sym.symbol n ∈ psyms φ →
      n ∈ regSymNames ++ c.symNames ∨ n = "" ∨ n = "inj" ∨ n = "Lblite" :=
  premise_symbols c h

/-- `HandArg`'s model, from the arm's conditions on the two names alone. -/
theorem handArg_eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem,
      (I ⊧ᴵP (Faithful.Γc HandArg.c ∪ Faithful.Γstep HandArg.c)) ∧
      (I ⊧ᴵ (symP HandArg.left ⬝ den HandArg.c HandArg.pairV ≡ den HandArg.c HandArg.leafV)) ∧
      ∀ x y : Config HandArg.c, Step HandArg.c x y ↔
        ¬ (I ⊧ᴵ (den HandArg.c x.val ⇒ ∼ KoreAML.sNext (den HandArg.c y.val))) := by
  obtain ⟨hl, hp, -⟩ := HandArg.sorts
  obtain ⟨I, h1, h2, h3⟩ := model_with_eqns_argProj HandArg.c HandArg.coreOK HandArg.fnHyp HandArg.argNames
    HandArg.argG (fun n hn => by
      simp only [HandArg.argNames, HandArg.names, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> exact ⟨by decide, by decide +kernel, by decide +kernel⟩)
  refine ⟨I, h1, h2 _ (by simp [HandArg.argNames, HandArg.names]) _ _ _ _ hp hl ?_, h3⟩
  simp only [HandArg.argG, ↓reduceIte, HandArg.pairV, argFn_ctor]
  rfl

end General

/-! ## A named argument's projections on a kompiled text (`NamedArg`, `f2-examples/namedarg.kompile.kore`)

`pair(fst: Foo, snd: Foo)`: kompile declares `project:pair:fst` and `project:pair:snd` and writes their
equations, which the account accepts as constructor arguments' projections (`kcore account`: nothing
refused). The names meet the conditions `genEqClassOK` checks of them (`arm`), so one model of the
theory whose steps are the semantics' holds both equations at `pair(leaf, leaf)`
(`GenEqs.model_with_eqns_argProj`): the kernel decides `coreOK`, the functions' facts and the names'
conditions, and nothing of the theory's lists. -/

namespace NamedArg

kore_term kore from "f2-examples/namedarg.kompile.kore"
definition_of defn from "f2-examples/namedarg.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

def fst : String := "Lblproject'Coln'pair'Coln'fst"
def snd : String := "Lblproject'Coln'pair'Coln'snd"
def names : List String := [fst, snd]

/-- The text declares both projections. -/
theorem declared : names.all (fun n => kore.symbolDecls.any (·.name == n)) = true := by decide +kernel

/-- **The arm's conditions on the two names**: the prefix, no registry symbol's, none of the
semantics' own. -/
theorem arm : ∀ n ∈ names, (KoreAML.Parse.dropPrefix? "Lblproject'Coln" n).isSome = true ∧
    regSymNames.contains n = false ∧ c.symNames.contains n = false := by decide +kernel

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def leafV : GroundTerm := .ctor (symN "Lblleaf") []
noncomputable def pairV : GroundTerm := .ctor (symN "Lblpair") [leafV, leafV]

theorem sorts : (c.sortOf leafV).isSome = true ∧ (c.sortOf pairV).isSome = true := by decide +kernel

def argNames : String → Prop := fun n => n ∈ names

noncomputable def argG : String → GroundTerm → Option GroundTerm := fun n =>
  if n = fst then argFn (symN "Lblpair") 0 else if n = snd then argFn (symN "Lblpair") 1 else fun _ => none

/-- **One model of the theory, whose steps are the semantics' steps, holds both projections'
equations** at `pair(leaf, leaf)`. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (symP fst ⬝ den c pairV ≡ den c leafV)) ∧ (I ⊧ᴵ (symP snd ⬝ den c pairV ≡ den c leafV)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨s, hl⟩ := Option.isSome_iff_exists.mp sorts.1
  obtain ⟨s', hp⟩ := Option.isSome_iff_exists.mp sorts.2
  obtain ⟨I, h1, h2, h3⟩ := model_with_eqns_argProj c coreOK fnHyp argNames argG (fun n hn => arm n hn)
  refine ⟨I, h1, h2 _ (by simp [argNames, names]) _ _ _ _ hp hl ?_, h2 _ (by simp [argNames, names]) _ _ _ _ hp hl ?_, h3⟩
  · simp only [argG, ↓reduceIte, pairV, argFn_ctor]
    rfl
  · have h : snd ≠ fst := by decide
    simp only [argG, h, ↓reduceIte, pairV, argFn_ctor]
    rfl

end NamedArg

/-! ## A registry-numbered projection the arm refuses (`RegProj`)

`HandArg`'s shape without `pair`, with a parameter symbol numbered as the registry's `project:Int`.
`coreOK` holds and the name is none of the semantics' own, so `predProjOK?` accepts the selector-domain
axiom of `project:Int`; but the parameter's arity item, a premise of the theory, names it
(`GenEqs.kernelSym_named`), so the equation's symbol is not free. The arm's decided check refuses it
(`Parse.predProjAcc`, `Parse.regProjFree`). -/

namespace RegProj

open KCore.Faithful.SortsWitness (cellSorts cellCtors cellSubsorts)

def Foo : Srt := nRegSorts + 2
def leafS : Sym := nRegSyms + 5
def projK : CtorSig := ⟨projectSym Srt.int, [Srt.k], Srt.int⟩

def c : Semantics :=
  { lib := {}, sortNames := ["KCell", "KCellOpt", "Foo"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisFoo", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblleaf"]
    userSorts := cellSorts ++ [Foo]
    ctors := cellCtors ++ [⟨leafS, [], Foo⟩], fns := []
    params := [{ sig := projK }]
    userSubsorts := cellSubsorts, pgmSort := Srt.k, rules := [] }

theorem coreOK : c.coreOK = true := by decide_coreOK

def projInt : String := "Lblproject'Coln'Int"

theorem name : c.symName projK.name = projInt := by decide +kernel

/-- `project:Int`'s selector-domain axiom, as the reader reads it. -/
def e : Parse.RawEqn :=
  { fn := projInt, pats := [], req := none, competitors := none, rhs := .top KoreAML.R, attrs := [], ens := none,
    dom := true }

def N : Parse.Names := { sorts := [], syms := [] }

/-- `predProjOK?` accepts it: Int is a registry sort and the name is none of the semantics' own. -/
theorem pred_ok : Parse.predProjOK? N "" [e] c e = some true := by decide +kernel

/-- **A premise of the theory names `project:Int`**: the parameter's arity item. -/
theorem named : ∃ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ ∧ KoreAML.Sym.symbol projInt ∈ psyms φ := by
  have := kernelSym_named (c := c) (k := projK) (by decide +kernel) (by decide +kernel)
  rwa [name] at this

/-- **The arm refuses it**: `freeB c [projectSym Int]` is false. -/
theorem refused : Parse.predProjAcc N "" [e] c e = false := by decide +kernel

end RegProj

/-- info: 'GenEqsLemmas.Hand.std_in_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.std_in_Γ
/-- info: 'GenEqsLemmas.Hand.ow_in_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ow_in_Γ
/-- info: 'GenEqsLemmas.Hand.ow_excl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ow_excl
/-- info: 'GenEqsLemmas.Nx.int_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.int_free
/-- info: 'GenEqsLemmas.Nx.k_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.k_free
/-- info: 'GenEqsLemmas.Nx.kitem_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.kitem_free
/-- info: 'GenEqsLemmas.Nx.proj_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.proj_patch
/-- info: 'GenEqsLemmas.Nx.proj_eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.proj_eqns
/-- info: 'GenEqsLemmas.Prio.eq_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Prio.eq_free
/-- info: 'GenEqsLemmas.Prio.fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Prio.fnHyp
/-- info: 'GenEqsLemmas.Prio.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Prio.eqns

/-- info: 'GenEqsLemmas.HandArg.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandArg.eqns

/-- info: 'KCore.GenEqs.rootedListsB_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rootedListsB_holds
/-- info: 'KCore.GenEqs.premise_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms premise_symbols
/-- info: 'KCore.GenEqs.argProj_free_of_genEqClassOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms argProj_free_of_genEqClassOK
/-- info: 'KCore.GenEqs.sortProj_free_of_predProjOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortProj_free_of_predProjOK
/-- info: 'KCore.GenEqs.sortProj_free_of_predProjAcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortProj_free_of_predProjAcc
/-- info: 'GenEqsLemmas.RegProj.named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RegProj.named
/-- info: 'GenEqsLemmas.General.handArg_eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms General.handArg_eqns
/-- info: 'GenEqsLemmas.NamedArg.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NamedArg.eqns

end GenEqsLemmas
