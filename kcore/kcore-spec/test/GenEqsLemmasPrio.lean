/-
  Instances of `KcoreSpec/GenEqsModel.lean` on `f2-examples/prio.kore`. Run from the package root:
  `lake env lean -j1 test/GenEqsLemmasPrio.lean`. Beside test/GenEqsLemmas.lean.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsLemmas

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

/-- info: 'GenEqsLemmas.Prio.eq_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Prio.eq_free
/-- info: 'GenEqsLemmas.Prio.fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Prio.fnHyp
/-- info: 'GenEqsLemmas.Prio.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Prio.eqns

end GenEqsLemmas
