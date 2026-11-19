/-
  A sort predicate held as a function of `c.fns` (`Semantics.sortPreds`, `Semantics.ownSyms`,
  `Semantics.idsOK`). Run from the package root: `lake env lean -j1 test/PredFnCone.lean`.

  Kernel-checked here:
  - `idsOK_of_before`: every semantics that `idsOK` accepted while `ownSyms` listed every function
    and `idsOK` had no conjunct on the functions' labels (`idsOKBefore`) is accepted now. Then
    `ownSyms` numbered every function from `symBase`, so the filter keeps all of them, and
    `symBase = nRegSyms + sortNames.length` gives the new conjunct.
  - `One.c`: a function of `c.fns` labelled as the predicate of the own sort KCell: `sortPreds`
    builds no function of that label, and `coreOK` holds.
  - `Twice.c`: two functions of `c.fns` under that label, one giving true and one false: every leaf
    of `coreOK` holds but `predsApart` (test/witnesses.toml, predsApart.1); it is the semantics of
    KcoreSpec/ModelPredTwiceWitness.lean, whose `Γ` has no model.
  - `IsK.c`: a function of `c.fns` labelled `isK`, which `sortPreds` builds whatever `c.fns` holds:
    `predsApart` refuses it (two functions of one label), and `idsOK` too (a registry symbol).
  - `Reg.c`: a function of `c.fns` labelled as the registry's predicate of Int: every leaf of
    `coreOK` holds but the conjunct of `idsOK` on the functions' labels (test/witnesses.toml,
    idsOK.4).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.PredFnCone

/-- `ownSyms` listing every function. -/
def ownSymsBefore (c : Semantics) : List Sym :=
  (c.ctors.map (·.name)).filter (fun f => decide (nRegSyms ≤ f)) ++ c.fns.map (·.label) ++
    (c.params.filter fun k => decide (nRegSyms ≤ k.sig.name)).map (·.sig.name) ++ c.ovls.map (·.sig.name)

/-- `idsOK` over `ownSymsBefore`, without the conjunct on the functions' labels. -/
def idsOKBefore (c : Semantics) : Bool :=
  c.ownSorts == List.range' nRegSorts c.sortNames.length &&
  ownSymsBefore c == List.range' c.symBase (c.symNames.length - c.sortNames.length) &&
  decide (c.sortNames.length ≤ c.symNames.length) &&
  ((let reg := c.userSorts.filter fun s => decide (s < nRegSorts)
    nodup reg && reg.all genSorts.contains &&
    c.ctors.all fun k => decide (nRegSyms ≤ k.name) || genSyms.contains k.name) && c.lib.ok)

/-- **Every semantics `idsOKBefore` accepts, `idsOK` accepts.** -/
theorem idsOK_of_before {c : Semantics} (h : idsOKBefore c = true) : c.idsOK = true := by
  unfold idsOKBefore at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hge : ∀ f ∈ c.fns, c.symBase ≤ f.label := by
    intro f hf
    have hm : f.label ∈ ownSymsBefore c := by
      simp only [ownSymsBefore, List.mem_append]
      exact .inl (.inl (.inr (List.mem_map_of_mem hf)))
    rw [h2, List.mem_range'_1] at hm
    exact hm.1
  have hfil : (c.fns.map (·.label)).filter (fun f => decide (c.symBase ≤ f)) = c.fns.map (·.label) := by
    rw [List.filter_eq_self]
    intro l hl
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
    exact decide_eq_true (hge f hf)
  have hown : c.ownSyms = ownSymsBefore c := by
    simp only [Semantics.ownSyms, ownSymsBefore, hfil]
  unfold Semantics.idsOK
  simp only [Bool.and_eq_true, beq_iff_eq, hown]
  refine ⟨⟨⟨h1, h2⟩, h3, ?_⟩, h4⟩
  rw [List.all_eq_true]
  intro f hf
  exact decide_eq_true (Nat.le_trans (Nat.le_add_right _ _) (hge f hf))

/-- A function of `K` to `Bool` under the label `l`, of one clause giving `b`. -/
def predFn (l : Sym) (b : Bool) : Fn :=
  { label := l, args := [Srt.k], result := Srt.bool
    clauses := [{ vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool b), ens := none }]
    total := true }

/-- The configuration `<k> K </k>` with the generated counter, with the functions `fs`. -/
def withFns (fs : List Fn) : Semantics :=
  { PrioTextWitness.c with fns := fs, symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"] }

namespace One

def c : Semantics := withFns [predFn nRegSyms true]

theorem pred_label : predOf nRegSorts = some nRegSyms := by decide +kernel
theorem no_sortPred : (c.sortPreds.map (·.label)).contains nRegSyms = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_coreOK

end One

namespace Twice

def c : Semantics := withFns [predFn nRegSyms true, predFn nRegSyms false]

theorem not_predsApart : c.predsApart = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true :=
  ⟨by decide_sortedOK, by decide_faithCoreOK, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The semantics of the witness module KcoreSpec/ModelPredTwiceWitness.lean. -/
theorem eq_witness : c = PredTwiceWitness.c := rfl

end Twice

namespace IsK

def c : Semantics := withFns [predFn isK true]

theorem sortPred_kept : (c.sortPreds.map (·.label)).contains isK = true := by decide +kernel
theorem not_predsApart : c.predsApart = false := by decide +kernel
theorem not_idsOK : c.idsOK = false := by decide +kernel
theorem not_coreOK : c.coreOK = false := by decide_cheap

end IsK

namespace Reg

def c : Semantics := withFns [predFn 54 true]

theorem int_pred : predOf Srt.int = some 54 := by decide +kernel
/-- The conjunct of `idsOK` on the functions' labels. -/
theorem not_fns_reg : (c.fns.all fun f => decide (nRegSyms ≤ f.label)) = false := by decide +kernel
theorem not_idsOK : c.idsOK = false := by decide +kernel
/-- `idsOK`'s other leaves. -/
theorem ids_others : (c.ownSorts == List.range' nRegSorts c.sortNames.length) = true ∧
    (c.ownSyms == List.range' c.symBase (c.symNames.length - c.sortNames.length)) = true ∧
    decide (c.sortNames.length ≤ c.symNames.length) = true ∧
    ((let reg := c.userSorts.filter fun s => decide (s < nRegSorts)
      nodup reg && reg.all genSorts.contains &&
      c.ctors.all fun k => decide (nRegSyms ≤ k.name) || genSyms.contains k.name) && c.lib.ok) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxHeartbeats 1000000 in
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧
    c.overloadsOK = true :=
  ⟨by decide_sortedOK, by decide_faithCoreOK, by decide +kernel, by decide +kernel, by decide +kernel⟩

end Reg

/-- info: 'KCore.Faithful.PredFnCone.idsOK_of_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idsOK_of_before

/-- info: 'KCore.Faithful.PredFnCone.One.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms One.coreOK

end KCore.Faithful.PredFnCone
