/-
  KCore, checked layer: the executable step of CollExec.lean is complete.

  - `patEval_complete`, `patEvals_complete`: a pattern that denotes v under σ (`PatVal`) reads as v
    under σ (`patEval`), the map pattern symbols being no constructors (`MatchCtxO.patHooks`) and
    an overloading symbol's normal form being computed by `patEval` (`norm`);
  - `patEval_congr`, `patEvals_congr`: `patEval` reads σ on the pattern's variables only;
  - the sorts of what patterns denote over the collection pattern symbols are `Det.patVal_sortedAll`
    (Uniq.lean): a pattern of sort s in a left-hand side's context (`patCtxAll`) denotes, under a
    well-sorted σ, a value of sort s.
-/
import KcoreSpec.CollExecSound
import KcoreSpec.Uniq

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec GroundTerm

variable {c : Semantics}

/-! ## The check accepts every match -/

/-- A collection pattern symbol is not a map pattern symbol. -/
theorem notPatternHook_of_collPat {f : Sym} (h : c.isCollPat f = true) :
    patternHooks.contains f = false := by
  cases hph : patternHooks.contains f with
  | false => rfl
  | true => rw [c.isCollPat_of_hook hph] at h; cases h

mutual
  /-- A pattern that denotes v under σ reads as v under σ. -/
  theorem patEval_complete (hc : MatchCtxO c) {σ : Subst} : ∀ {p : Term} {v : GroundTerm},
      PatVal c σ p v → patEval c σ p = some v
    | _, _, .var h => by simpa [patEval] using h
    | _, _, .dv => rfl
    | _, _, .ctor hk hs => by
      simp only [patEval, patEvals_complete hc hs, hk, ↓reduceIte]
    | _, _, .hook (f := f) hp hs hv => by
      have hnc : c.isCtor f = false := hc.patHooks f (List.contains_iff_mem.mp hp)
      simp only [patEval, patEvals_complete hc hs, hnc, hp, hv, Bool.false_eq_true, ↓reduceIte,
        Option.join_some]
    | _, _, .coll (f := f) hct hp hs hv => by
      have hnp := notPatternHook_of_collPat hp
      simp only [patEval, patEvals_complete hc hs, hct, hnp, hp, hv, Bool.false_eq_true, ↓reduceIte]
    | _, _, .inj h => by simp only [patEval, patEval_complete hc h, Option.map_some]
    | _, _, .as h hi => by
      simp only [patEval, patEval_complete hc h, hi, same_iff.mpr rfl, ↓reduceIte]
    | _, _, .ovl (f := f) hct ho hs hv => by
      have hph : patternHooks.contains f = false := by
        cases h : patternHooks.contains f with
        | false => rfl
        | true => rw [c.isOvl_of_patternHook h] at ho; cases ho
      have hcp : c.isCollPat f = false := by
        cases h : c.isCollPat f with
        | false => rfl
        | true => rw [c.isOvl_of_collPat h] at ho; cases ho
      simp only [patEval, patEvals_complete hc hs, hct, hph, hcp, ho, hv, Bool.false_eq_true, ↓reduceIte]
  theorem patEvals_complete (hc : MatchCtxO c) {σ : Subst} : ∀ {ps : List Term} {vs : List GroundTerm},
      PatVals c σ ps vs → patEvals c σ ps = some vs
    | _, _, .nil => rfl
    | _, _, .cons h hs => by simp only [patEvals, patEval_complete hc h, patEvals_complete hc hs]
end

mutual
  /-- `patEval` reads σ on the pattern's variables only. -/
  theorem patEval_congr {σ σ' : Subst} : ∀ (p : Term), (∀ i ∈ varOccs p, σ.lookup i = σ'.lookup i) →
      patEval c σ p = patEval c σ' p
    | .var i, h => by simp only [patEval]; exact h i (by simp [varOccs])
    | .dv _ _, _ => rfl
    | .inj a b p, h => by
      simp only [patEval]
      rw [patEval_congr p (fun i hi => h i (by simpa [varOccs] using hi))]
    | .as p i, h => by
      simp only [patEval]
      rw [patEval_congr p (fun j hj => h j (by simp [varOccs, hj])), h i (by simp [varOccs])]
    | .app f ps, h => by
      simp only [patEval]
      rw [patEvals_congr ps (fun i hi => h i (by simpa [varOccs] using hi))]
    termination_by structural p => p
  theorem patEvals_congr {σ σ' : Subst} : ∀ (ps : List Term),
      (∀ i ∈ varOccsList ps, σ.lookup i = σ'.lookup i) → patEvals c σ ps = patEvals c σ' ps
    | [], _ => rfl
    | p :: ps, h => by
      simp only [patEvals]
      rw [patEval_congr p (fun i hi => h i (by simp [varOccsList, hi])),
        patEvals_congr ps (fun i hi => h i (by simp [varOccsList, hi]))]
    termination_by structural ps => ps
end

end KCore.CExec
