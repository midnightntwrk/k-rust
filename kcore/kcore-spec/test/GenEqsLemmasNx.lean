/-
  Instances of `KcoreSpec/GenEqsConservative.lean` and `KcoreSpec/GenEqsModel.lean` on
  `f2-examples/owisenx.kompile.kore`. Run from the package root:
  `lake env lean -j1 test/GenEqsLemmasNx.lean`. Beside test/GenEqsLemmas.lean.

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

end GenEqsLemmas
