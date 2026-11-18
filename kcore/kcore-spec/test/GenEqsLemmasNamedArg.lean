/-
  Instances of `KcoreSpec/GenEqsModel.lean` on `f2-examples/namedarg.kompile.kore`. Run from the
  package root: `lake env lean -j1 test/GenEqsLemmasNamedArg.lean`. Beside test/GenEqsLemmas.lean.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsLemmas

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

/-- info: 'GenEqsLemmas.NamedArg.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NamedArg.eqns

end GenEqsLemmas
