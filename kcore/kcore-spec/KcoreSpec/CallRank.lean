/-
  KCore, checked layer: termination and totality by a rank of the functions, a list of their labels
  given with the semantics (`ord`; a function's rank is its position, `List.idxOf`).

  Declaration order (`orderObligations`, Terminates.lean) is one rank: the order the text happens to
  declare the functions in. A function whose callees are all declared before it terminates; one
  that calls a function declared after it is named, whether or not the call can come back to it.
  Any order of the functions in which each one's callees, itself aside, come before it is as good:
  the call graph restricted to the functions is then acyclic up to self calls, and evaluation
  terminates by induction on the rank, the self calls decreasing (`terminates_of_decreasing`).
  The rank is data: a generator computes one from the call graph (callees first) and the kernel
  checks it here, so a wrong rank only names more functions.

  - `rankedCallees ord labels f`: each callee of f that is a function of `c`, f aside, comes
    before it in `ord`. `rankObligations` (CallGroups.lean) names the functions it refuses, unless
    they are in a cycle whose calls decrease in a shared weight; `terminates_of_rankL` there gives
    every function's termination.
  - `totalOKR c ord f`: `totalOK` with the total functions ranked before f in place of those
    declared before it; `totalObligationsR c ord`: the `[total]` functions it does not confirm.
    `totals_of_rank`: every `[total]` function is total, given the named ones.

  Neither is a condition of `coreOK`: they decide facts of `FnHyp` (FnObligations.lean).
-/
import KcoreSpec.Totals

set_option autoImplicit false

namespace KCore

namespace Semantics
variable (c : Semantics)

/-- A function's callees are ranked below it by `ord`: each callee that is a function of `c` and
not the function itself comes before it in `ord`. -/
def _root_.KCore.rankedCallees (ord : List Sym) (labels : List Sym) (f : Fn) : Bool :=
  f.callees.all fun g => g == f.label || !labels.contains g || decide (ord.idxOf g < ord.idxOf f.label)

/-- The functions declared `[total]` ranked before f by `ord`. -/
def totalBeforeR (ord : List Sym) (f : Fn) : List Sym :=
  (c.fns.filter fun g => g.total && decide (ord.idxOf g.label < ord.idxOf f.label)).map (·.label)

/-- `totalOK` with the total functions ranked before f (`totalBeforeR`) in place of those declared
before it. -/
def totalOKR (ord : List Sym) (f : Fn) : Bool :=
  let tot := c.totalBeforeR ord f ++ c.sortPreds.map (·.label) ++ [f.label]
  c.shapesOK && decreasingOK c f (c.decArg f) &&
  c.covers (coverFuel f) f.args (coverRows f) &&
  f.clauses.all (fun cl => c.totalTerm tot cl.rhs) && f.clauses.all (·.ens.isNone)

/-- The functions declared `[total]` that `totalOKR` does not confirm. -/
def totalObligationsR (ord : List Sym) : List Sym :=
  (c.fns.filter fun f => f.total && !c.totalOKR ord f).map (·.label)

end Semantics

variable {c : Semantics}

/-- A callee of a function of `c` is the function itself, a function of `c` before it in `ord`, or
no function of `c`. -/
theorem rankedCallees_spec {ord labels : List Sym} {f : Fn} (h : rankedCallees ord labels f = true)
    {g : Sym} (hg : g ∈ f.callees) : g = f.label ∨ g ∉ labels ∨ ord.idxOf g < ord.idxOf f.label := by
  have := List.all_eq_true.mp h g hg
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this with (h | h) | h
  · exact .inl h
  · exact .inr (.inl fun hm => by rw [List.contains_iff_mem.mpr hm] at h; cases h)
  · exact .inr (.inr h)

/-- A function `lookupFn` finds under a label no function of `c` bears is a sort predicate, which
terminates. -/
theorem terminates_of_not_labelN (hc : EvalCtxN c) {g : Sym} (hg : g ∉ c.fns.map (·.label)) :
    Terminates c g := by
  intro gfn hgfn
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hgfn
  rcases List.mem_append.mp hgm with hu | hp
  · exact absurd (hlab ▸ List.mem_map_of_mem hu) hg
  · exact hlab ▸ sortPreds_terminateN hc hp gfn (hlab ▸ hgfn)

theorem terminates_of_not_label (hc : EvalCtx c) {g : Sym} (hg : g ∉ c.fns.map (·.label)) :
    Terminates c g :=
  terminates_of_not_labelN hc.toN hg

/-- **A function `totalOKR` confirms is total**, in a core that `sortedOK` and `srReady` accept,
every function terminating and the total functions ranked before it total. -/
theorem total_of_totalOKR (hpreTop : c.clausesPreTop = true) (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld) (hterm : ∀ g, Terminates c g) {ord : List Sym} {fn : Fn} (hfn : fn ∈ c.fns)
    (hT : c.totalOKR ord fn = true) (htot : ∀ g ∈ c.totalBeforeR ord fn, Total c g) :
    Total c fn.label := by
  have hc := evalCtx_of_all (hpreTop := hpreTop) hok hsr hov hrh
  simp only [Semantics.totalOKR, Bool.and_eq_true, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨hs, hdec⟩, hcov⟩, hrhs⟩, hne⟩ := hT
  have hfok : ∀ cl ∈ fn.clauses, c.clauseSorted fn (c.fns.map Fn.sig) cl = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.2 fn hfn
  refine total_of_parts hc hs hterm (List.mem_append_left _ hfn) (fun cl hcl => ?_) hdec
    (n := Semantics.coverFuel fn) hcov hrhs (fun cl hcl => by simpa using hne cl hcl) (fun g hg hgl => ?_)
  · have := hfok cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    replace this := this.1
    exact ⟨sortsOfTerms_all_of_nf this.1.1.1.1.1, Semantics.clausesPreTop_spec hpreTop hfn hcl⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨p, hp, rfl⟩) | hg
    · exact htot g hg
    · exact sortPreds_total hc hp
    · exact absurd hg hgl

/-- **Every function declared `[total]` is total**, in a core that `sortedOK` and `srReady` accept,
every function terminating, given those `totalObligationsR` names: by induction on the rank, a
function `totalOKR` confirms is total where the total functions ranked before it are; the sort
predicates are total. -/
theorem totals_of_rank (hpreTop : c.clausesPreTop = true) (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase) (hrh : c.RightHeld) (hterm : ∀ g, Terminates c g)
    (ord : List Sym) (hnamed : ∀ g ∈ c.totalObligationsR ord, Total c g) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f := by
  have hc := evalCtx_of_all (hpreTop := hpreTop) hok hsr hov hrh
  have pos : ∀ (n : Nat) (fn : Fn), fn ∈ c.fns → ord.idxOf fn.label = n → fn.total = true →
      Total c fn.label := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro fn hmem hn htot
      by_cases hN : fn.label ∈ c.totalObligationsR ord
      · exact hnamed _ hN
      have hT : c.totalOKR ord fn = true := by
        cases h : c.totalOKR ord fn
        · exact absurd (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨hmem, by simp [htot, h]⟩, rfl⟩) hN
        · rfl
      refine total_of_totalOKR (hpreTop := hpreTop) hok hsr hov hrh hterm hmem hT fun g hg => ?_
      simp only [Semantics.totalBeforeR, List.mem_map, List.mem_filter, Bool.and_eq_true,
        decide_eq_true_eq] at hg
      obtain ⟨gfn, ⟨hgm, hgt, hlt⟩, rfl⟩ := hg
      exact ih _ (hn ▸ hlt) gfn hgm rfl hgt
  intro f fn hfn htot
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  rcases List.mem_append.mp hgm with hu | hp
  · exact pos _ fn hu rfl htot
  · exact sortPreds_total hc hp

kernel_rfl Semantics.totalObligationsR_withHooks :
  ∀ (c : Semantics) (H : HookParams) (ord : List Sym),
    (c.withHooks H).totalObligationsR ord = c.totalObligationsR ord

end KCore
