/-
  A hooked symbol of the registry in a rule's left side, read through the cut (`Parse.ovlCut`,
  `Parse.regCutSyms`), on K 7.1.337 kompile's text of fixture e6-list-set-lhs-bound
  (`f2-examples/e6-list-set-lhs-bound.kompile.kore`, the kompiled text that
  `test/constructs/fixtures/e6-list-set-lhs-bound/kompile.txt` records, with its paths restored):
  `rule <k> m(L, I, J) => .K ... </k> <list> L [ I <- J ] </list>`, `L [ I <- J ]` the library's
  `List:set` (hook LIST.update). Run from the package root: `lake env lean -j1 test/HookedCutStep.lean`.

  The rule's sentence says: at a configuration whose k cell begins with `m(l, i, j)`, the rule
  applies exactly where the list cell holds the list the update gives at l, i and j. Every argument
  of `List:set` is bound by `m`'s arguments in the k cell, so the cut `C[List:set(L, I, J)]` =
  `∃V. C[V] ∧ V ∈ List:set(L, I, J)` leaves no variable open: the reader reads the list cell's
  content as a fresh variable `Hooked0` with `Hooked0 ∈ List:set(L, I, inj(J))` a conjunct of
  `Rule.pre`, whose term is evaluated through the registry's graph of LIST.update.

  - `reading`, `wf_defn`, `coreOK`: one rule, no function, no parameter; the rule's `pre` printed
    (`Hooked0 ∈ List:set(L, I, inj(J))`).
  - `fnDet`: the reading has no function, so at every H one result at most, and the executable
    step, which here reads no interpretation, lists exactly the `Step` successors where it does not
    run out of fuel (`CExec.noStep_at`).
  - `steps_same` (every H): with the list `0 1 2` in the list cell, `m(0 1 2, 1, 1)` steps to `.K`,
    the list unchanged (the update of `0 1 2` at 1 by 1 is `0 1 2`).
  - `steps_set` (every H): with `0 5 2` in the list cell, `m(0 1 2, 1, 5)` steps (the update at 1 by
    5 is `0 5 2`).
  - `stuck_other` (every H): with `0 1 2` in the list cell, `m(0 1 2, 1, 5)` has no successor: the
    update is `0 5 2`, not the list the cell holds.
  The index is in each case an index of the list; what the update gives at another index is not
  stated here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HookedCutStep

open KCore GroundTerm Faithful

definition_of defn from "f2-examples/e6-list-set-lhs-bound.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def kCell : Sym := 384
def listCell : Sym := 386
def symM : Sym := 388

theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName listCell = "Lbl'-LT-'list'-GT-'" ∧
    c.symName symM = "Lblm" ∧ c.symName listSet = "LblList'Coln'set" := by
  decide +kernel

/-- The list of the Ints `xs`, each injected into KItem. -/
def lst (xs : List Int) : GroundTerm := .list Srt.list (xs.map fun n => .inj Srt.int Srt.kitem (int n))

/-- The configuration with `m(l, i, j)` in the k cell and `L` in the list cell. -/
def cfg (l : List Int) (i j : Int) (L : List Int) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.ctor symM [lst l, int i, int j], .ctor dotk []]],
    .ctor listCell [lst L], .ctor counterLabel [int 0]]

/-- The configuration with an empty k cell and `L` in the list cell. -/
def done (L : List Int) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor listCell [lst L], .ctor counterLabel [int 0]]

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap

/-- **The reading**: one rule, no function, no parameter. -/
theorem reading : c.rules.length = 1 ∧ c.fns.isEmpty = true ∧ c.params.isEmpty = true := by
  decide +kernel

/-- The rule's `pre`, printed: `Hooked0 ∈ List:set(L, I, inj(J))`, the variables by index. -/
def condStr : Cond → String
  | .mem s (.var v) (.app f [.var a, .var b, .inj x y (.var j)]) =>
    s!"in[{s}](var {v}, app {f}(var {a}, var {b}, inj[{x},{y}](var {j})))"
  | _ => "other"

/--
info: [in[5](var 6, app 199(var 0, var 1, inj[3,1](var 2)))]
-/
#guard_msgs in
#eval show IO Unit from do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/e6-list-set-lhs-bound.kompile.kore") | IO.println "read error"
  match Parse.parse k with
  | .ok d => IO.println s!"{d.sem.rules.map fun r => condStr r.pre}"
  | .error r => IO.println r.reason.name

private theorem ready : CExec.execReady c = true := by decide +kernel

theorem noFns : c.fns = [] := List.isEmpty_iff.mp reading.2.1

kernel_rfl fns_withHooks : ∀ H : HookParams, (c.withHooks H).fns = c.fns

/-- No function, so one result at most, at every H. -/
theorem fnDet (H : HookParams) : FnDet (c.withHooks H) :=
  fnDet_of_agree (fun _ h => by rw [fns_withHooks, noFns] at h; cases h)
    (fun _ h => by rw [fns_withHooks, noFns] at h; cases h)

/-- A configuration of the reading is one under every interpretation (no open generator). -/
def cfgH (x : Config c) (H : HookParams) : Config (c.withHooks H) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact x.property⟩

def Same : Config c := ⟨cfg [0, 1, 2] 1 1 [0, 1, 2], by decide +kernel⟩
def DoneSame : Config c := ⟨done [0, 1, 2], by decide +kernel⟩
def Set5 : Config c := ⟨cfg [0, 1, 2] 1 5 [0, 5, 2], by decide +kernel⟩
def Done5 : Config c := ⟨done [0, 5, 2], by decide +kernel⟩
def Other : Config c := ⟨cfg [0, 1, 2] 1 5 [0, 1, 2], by decide +kernel⟩

-- The executable step at these configurations reads no interpretation: the cut's membership is
-- decided by LIST.update's graph at values, and the rest of the rule is constructors.
kernel_rfl same_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 20 Same.val = CExec.successorsN c 20 Same.val
kernel_rfl set5_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 20 Set5.val = CExec.successorsN c 20 Set5.val
kernel_rfl other_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 20 Other.val = CExec.successorsN c 20 Other.val
kernel_rfl other_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c.withHooks H) 20 Other.val = CExec.outOfFuel c 20 Other.val

theorem listed :
    CExec.successorsN c 20 Same.val = [DoneSame.val] ∧
    CExec.successorsN c 20 Set5.val = [Done5.val] ∧
    CExec.successorsN c 20 Other.val = [] ∧
    CExec.outOfFuel c 20 Other.val = false := by
  decide +kernel

/-- **`m(0 1 2, 1, 1)` steps to `.K`, the list `0 1 2` unchanged, for every H.** -/
theorem steps_same (H : HookParams) : Step (c.withHooks H) (cfgH Same H) (cfgH DoneSame H) := by
  have hy : DoneSame.val ∈ CExec.successorsN (c.withHooks H) 20 Same.val := by
    rw [same_withHooks, listed.1]; exact List.mem_singleton_self _
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready ((CExec.execReady_withHooks c H).trans ready)
    (x := cfgH Same H) hy
  exact h

/-- **With `0 5 2` in the list cell, `m(0 1 2, 1, 5)` steps to `.K`, for every H.** -/
theorem steps_set (H : HookParams) : Step (c.withHooks H) (cfgH Set5 H) (cfgH Done5 H) := by
  have hy : Done5.val ∈ CExec.successorsN (c.withHooks H) 20 Set5.val := by
    rw [set5_withHooks, listed.2.1]; exact List.mem_singleton_self _
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready ((CExec.execReady_withHooks c H).trans ready)
    (x := cfgH Set5 H) hy
  exact h

/-- **With `0 1 2` in the list cell, `m(0 1 2, 1, 5)` has no successor, for every H**: the update
of `0 1 2` at 1 by 5 is `0 5 2`. -/
theorem stuck_other (H : HookParams) (y : Config (c.withHooks H)) : ¬ Step (c.withHooks H) (cfgH Other H) y :=
  have hf : CExec.outOfFuel (c.withHooks H) 20 (cfgH Other H).val = false :=
    (other_fuel_withHooks H).trans listed.2.2.2
  have he : CExec.successorsN (c.withHooks H) 20 (cfgH Other H).val = [] :=
    (other_withHooks H).trans listed.2.2.1
  CExec.noStep_at (n := 20) (x := cfgH Other H) ((CExec.execReady_withHooks c H).trans ready) (fnDet H) hf he y

end KCore.HookedCutStep

#print axioms KCore.HookedCutStep.reading
#print axioms KCore.HookedCutStep.fnDet
#print axioms KCore.HookedCutStep.steps_same
#print axioms KCore.HookedCutStep.steps_set
#print axioms KCore.HookedCutStep.stuck_other
