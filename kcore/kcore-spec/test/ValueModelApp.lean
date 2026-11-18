/-
  KCore test. A function's application to values, read in the value model (`KcoreSpec/ValueModelApp.lean`).

  - The statements, and that they rest on the three standard axioms only.
  - The reading with `HypModelCore` from `consistent_ofCl`'s hypotheses (`hypModel_ofCl`), at the
    model `consistent_ofCl` builds.
  - `f2-examples/clgenless.kompile.kore` (`rule f(_) => 1 requires isC(H:S)` beside
    `rule f(_) => 0 [owise]`): what `consistent_ofCl` asks of c beside the functions' facts is
    decided, and from `FnDet c`, `FnSolves c` and `Eval c f [0] (some 0)` the theory with the step's
    closure does not entail `f(0) = 1`. The three hypotheses are not shown here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful KCore.Faithful.Model

namespace ValueModelAppTest

#check @vmSymE_fn_iff
#check @vmApp_fn_iff
#check @vmApp_fn_eq
#check @vmApp_fn_empty
#check @vmModelCl
#check @vmApp_fn_not_entailed
#check @vmApp_fn_not_bot

/-- The reading at the model `consistent_ofCl` builds, from its hypotheses. -/
example (c : Semantics) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hids : c.idsOK = true)
    (hd : FnDet c) (hs : FnSolves c) {fn : Fn} (hfn : fn ∈ c.fns) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some fn.args) (e : ML.Valuation Elem) (m : Elem) :
    (TiePair.app c fn.label vs).interpret (stdI_T c (StepV c)) e m ↔ ∃ v, m = .val v ∧ Eval c fn.label vs (some v) :=
  vmApp_fn_iff (hypModel_ofCl hok hsr hov hfa hph hids hd hs) _ (List.mem_append_left _ hfn) hvs (KCore.sortsOf_length hvs) e m

/-! ## clgenless -/

definition_of defn from "f2-examples/clgenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

example : c.symName 389 = "Lblf" := by decide +kernel

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)

theorem fF_mem : fF ∈ c.allFns := List.mem_append_left _ (List.getElem_mem _)

theorem fF_shape : fF.label = 389 ∧ fF.args = [Srt.int] := by decide +kernel

/-- What `consistent_ofCl` asks of c beside the functions' facts, decided. -/
theorem decided : c.sortedOKCl = true ∧ c.srReady = true ∧ c.faithCoreOK = true ∧
    patHooksApart c = true ∧ c.idsOK = true ∧ c.ovls = [] ∧ c.subsorts.all (fun p => p.1 != p.2) = true := by
  decide_cheap

instance ovl : OvlOK c := OvlOK.of_nil decided.2.2.2.2.2.1 decided.2.2.2.2.2.2

def i0 : GroundTerm := .dv Srt.int (.int 0)
def i1 : GroundTerm := .dv Srt.int (.int 1)

/-- **`f(0) = 1` is not entailed** where c's functions have one result, its evaluation solves the
equations and `Eval` gives `f(0)` the value 0: in the value model `f(0)` is 0. -/
theorem f0_not_1 (hd : FnDet c) (hs : FnSolves c) (hE : Eval c 389 [i0] (some i0)) :
    ¬ ((Γc c ∪ Γstep c) ⊧ (TiePair.app c 389 [i0] ≡ den c i1)) :=
  vmApp_fn_not_entailed c decided.1 decided.2.1 decided.2.2.1 decided.2.2.2.1 decided.2.2.2.2.1 hd hs
    (clausePreDecided_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))
    fF_mem (vs := [i0]) (ss := [Srt.int]) (by decide +kernel) (by rw [fF_shape.2]; rfl)
    (by rw [fF_shape.1]; exact hE) (s := Srt.int) (by decide +kernel) (by decide)

end ValueModelAppTest

/-- info: 'KCore.vmSymE_fn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmSymE_fn_iff
/-- info: 'KCore.vmApp_fn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmApp_fn_iff
/-- info: 'KCore.vmApp_fn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmApp_fn_eq
/-- info: 'KCore.vmApp_fn_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmApp_fn_empty
/-- info: 'KCore.vmModelCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmModelCl
/-- info: 'KCore.vmApp_fn_not_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmApp_fn_not_entailed
/-- info: 'KCore.vmApp_fn_not_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.vmApp_fn_not_bot
/-- info: 'ValueModelAppTest.f0_not_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ValueModelAppTest.f0_not_1
