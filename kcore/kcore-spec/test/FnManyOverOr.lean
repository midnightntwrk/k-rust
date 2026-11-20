/-
  `Faithful.Model.consistent_of_fnMany_agree` on the fixture e3-ml-eq-rhs-or, at its function h,
  for every interpretation of the hooks. Run from the package root:
  `lake env lean -j1 test/FnManyOverOr.lean`.

  The text is `f2-examples/e3-ml-eq-rhs-or.kompile.kore` (`rule h(X) => f(X) #Or g(X)` with
  `rule f(X) => X` and `rule g(X) => 0 -Int X`, none `total`, over Int). The reader gives h the one
  clause `clH`: `[X:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`, `post := #Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`
  (`read`). Decided on the text (`decide +kernel`, `decide_cheap`):
  - h's name `Lblh` is read as no instance (`plain_h`) and is no constant (`spare_h`);
  - the theory's lists hold `Lblh` in h's own items only (`lists_h`), the values are built from
    symbols of other names (`values_h`), and the heads applied at values but h's are not `Lblh`
    (`hooks_h`, `params_h`, `fns_h`);
  - h's clause's premise and right side apply no symbol named `Lblh` (`kok_h`);
  - `coreOKEx`, no raw parameter, every clause's predicate `\top`.
  For every H: every premise of the theory but h's own items avoids `Lblh` (`avoidsOffH`; h's
  clause applies at every argument of Int, so the theory states no rest of h), and two matches of
  h's clause at one argument agree on X, its only variable off `exsFree` (`agreeH`). So the
  theory has a model for every H where evaluation has one result at most, `f` and `g` solve their
  equations and the right-side predicates have truth values (`consistent_of_rest`).
-/
import KcoreSpec
import KcoreSpec.ModelFnMany
import KcoreSpec.ModelFnOverHooks

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs KCore.Faithful KCore.Faithful.Model

namespace FnManyOverOr

definition_of defn from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def fG : Sym := 385
def fH : Sym := 386
def nH : String := "Lblh"

/-- `f(X) => X`. -/
def clF : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }

/-- `g(X) => 0 -Int X`. -/
def clG : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intSub [.dv Srt.int (.int 0), .var 0],
    ens := none }

/-- `#Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`. -/
def postH : Cond :=
  .or (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app fG [.var 0]))

/-- `h(X) => #Or0` with `exs = [#Or0]` and `post := postH`. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postH }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clF] }
def fnG : Fn := { label := fG, args := [Srt.int], result := Srt.int, clauses := [clG] }
def fnH : Fn := { label := fH, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, `h` with the one clause `clH`. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem name_h : c.symName fH = nH := by decide +kernel

/-! ## The checks on the text -/

theorem plain_h : instDecode? nH = none := by decide +kernel
theorem spare_h : spareSymB c nH = true := by decide +kernel
theorem values_h : NameFree.valuesN c [nH] = true := by rw [NameFree.valuesN]; decide_cheap 40
theorem hooks_h : hookSigs.all (fun k => NameFree.appOKN c [nH] k.name) = true := by decide_cheap 40
theorem params_h : c.params.all (fun k => NameFree.appOKN c [nH] k.sig.name) = true := by decide_cheap 40
theorem fns_h : c.allFns.all (fun g => decide (g.label = fH) || NameFree.appOKN c [nH] g.label) = true := by
  decide_cheap 40
theorem lists_h : listsOffB c fH nH = true := by rw [listsOffB]; decide_cheap 40
theorem kok_h : ownKokB c fnH clH = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem fH_one : (c.allFns.filter (fun g => decide (g.label = fH))).length = 1 := by decide +kernel
theorem exsFree_h : clH.exsFree = [1] := by decide

/-! ## For every H -/

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) ((coreOKEx_withHooks_fm c H).trans coreEx)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- h's clause applies at every argument of Int. -/
theorem not_fails_h (H : HookParams) {x : GroundTerm} (hx : (cH H).sortOf x = some Srt.int) :
    ¬ Fails (cH H) [x] clH := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : (cH H).WellSorted clH.vars [(1, x), (0, x)] := by
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨x, rfl, hx⟩
      | 1, hs => cases hs; exact ⟨x, rfl, hx⟩
      | i + 2, hs => simp [clH] at hs
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **Every premise but h's own items avoids `Lblh`, for every H.** -/
theorem avoidsOffH (H : HookParams) : AvoidsOff (cH H) fH ((cH H).symName fH) := by
  have hn : (cH H).symName fH = nH := name_h
  rw [hn]
  refine avoidsOff_of_lists (rangeBelowH H) (listsOff_withHooks H lists_h) values_h
    (List.all_eq_true.mp hooks_h) (List.all_eq_true.mp params_h)
    (fun g hg hl => by
      have h1 : NameFree.appOKN c [nH] g.label = true := by
        have := List.all_eq_true.mp fns_h g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fH)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hH : fnH ∈ c.allFns.filter (fun g => decide (g.label = fH)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp), by simp [fnH]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp fH_one
  rw [hx, List.mem_singleton] at hfn' hH
  obtain rfl : fn = fnH := hfn'.trans hH.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.int := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails_h H hx (hall clH (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnH])

/-- **Two matches of h's clause at one argument agree on X, for every H.** -/
theorem agreeH (H : HookParams) : ∀ ws σ₁ σ₂, clH.AppliesAt (cH H) σ₁ ws → clH.AppliesAt (cH H) σ₂ ws →
    ∀ i < clH.vars.length, i ∉ clH.exsFree → σ₁.lookup i = σ₂.lookup i := by
  intro ws σ₁ σ₂ h1 h2 i hi hx
  rw [exsFree_h] at hx
  have hi0 : i = 0 := by
    have hl : clH.vars.length = 2 := rfl
    simp only [List.mem_singleton] at hx
    omega
  subst hi0
  obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₁ [.var 0] ws from h1.2.1)
  obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₂ [.var 0] (v :: vs') from h2.2.1)
  cases hvs
  rw [PatVal.var_inv hv, PatVal.var_inv hv']

/-- **The theory has a model for every H** where evaluation has one result at most, `f` and `g`
solve their equations and the right-side predicates have truth values. -/
theorem consistent_of_rest (H : HookParams) (hd : FnDet (cH H)) (hf : FnSolvesAt (cH H) fnF)
    (hg : FnSolvesAt (cH H) fnG) (hq : ClausePostDecided (cH H)) : Consistent (cH H) := by
  have hfns : (cH H).fns = [fnF, fnG, fnH] := read
  refine consistent_of_fnMany_agree (f := fH) (fn := fnH) (cl := clH) (a := Srt.int)
    ((coreOKEx_withHooks_fm c H).trans coreEx) (by rw [hfns]; simp) rfl rfl rfl (by decide)
    (by rw [show (cH H).symName fH = nH from name_h]; exact plain_h)
    (by rw [show (cH H).symName fH = nH from name_h, spareSymB_withHooks_fm]; exact spare_h)
    (avoidsOffH H) (by rw [ownKokB_withHooks]; exact kok_h) hd (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) hq (openLaws_of_plain noRaw)
  rw [hfns] at hg'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl
  · exact hf
  · exact hg
  · exact absurd rfl hl

end FnManyOverOr

/-- info: 'FnManyOverOr.lists_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.lists_h
/-- info: 'FnManyOverOr.avoidsOffH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.avoidsOffH
/-- info: 'FnManyOverOr.consistent_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.consistent_of_rest
