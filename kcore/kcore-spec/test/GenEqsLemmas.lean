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

end GenEqsLemmas
