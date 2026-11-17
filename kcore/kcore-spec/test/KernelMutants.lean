/-
  An instance for a kernel mutant of `test/constructs/mutants.toml` (`[kernel.*]`) that changes a
  premise of `Step.rule`: a step and a configuration without a successor under every interpretation,
  on K 7.1.337 kompile's KORE. Run from the package root: `lake env lean -j1 test/KernelMutants.lean`.

  - `f2-examples/ensrule.kompile.kore` (`ensrule.k`): `assume(B) => ok() ensures B`. For every
    interpretation `assume(true)` steps to `ok()` and `assume(false)` has no successor
    (`EnsRule.ens_everyH`): a `Step` that does not read a rule's `ensures` steps `assume(false)` to
    `ok()`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KernelMutants

open KCore KCore.Exec KCore.Cert

section EveryH
variable {c : Semantics}

/-- A configuration of the data is one under every interpretation, where no parameter is an open
generator. -/
def cfgH (hr : ∀ k ∈ c.params, k.raw = false) (x : Config c) (H : HookParams) : Config (c.withHooks H) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks _ _ hr]; exact x.property⟩

/-- A step some rule's check accepts on the data, which reads no interpretation, is a step under
every interpretation. -/
theorem step_everyH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) {x y : Config c} {n : Nat}
    (hc : c.rules.any (fun r => checkStep c n r x.val y.val) = true) (H : HookParams) :
    Step (c.withHooks H) (cfgH hr x H) (cfgH hr y H) := by
  obtain ⟨r, hmem, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨_, hstep⟩ := step_of_listed ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    (x := cfgH hr x H)
    (listed_of_checkStep (c := c.withHooks H) (r := r) hmem ((checkStep_withHooks c H hr n r _ _).trans hc))
  exact hstep

/-- A configuration `stuckCheck` accepts on the data has no successor under any interpretation. -/
theorem stuck_everyH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) (hcf : c.clausesFixed = true) (hag : c.agreeObligations = [])
    (hna : c.asideFree = true) {x : Config c} {n : Nat} (h : stuckCheck c n x.val = true) (H : HookParams) :
    ∀ y, ¬ Step (c.withHooks H) (cfgH hr x H) y :=
  stuckCheck_sound hok hsr hmr H
    (Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
      ((Semantics.matchReady_withHooks c H).trans hmr) ((Semantics.clausesFixed_withHooks c H).trans hcf)
      ((Semantics.agreeObligations_withHooks c H).trans hag))
    (x := cfgH hr x H) h hna hr

end EveryH

def cfgOf (kCell : Sym) (cmdS : Srt) (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

namespace EnsRule

definition_of defn from "f2-examples/ensrule.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

def assume : Sym := 385
def ok_ : Sym := 386
theorem names_ok : c.symName 383 = "Lbl'-LT-'k'-GT-'" ∧ c.symName assume = "Lblassume" ∧
    c.symName ok_ = "Lblok" ∧ c.sortName 32 = "Cmd" := by decide +kernel
/-- The rule `assume`: no `requires`, its `ensures` B (variable 0). -/
theorem assume_rule : c.rules.map (·.prio) = [50, 200] ∧ c.rules.map (·.req.isSome) = [false, false] ∧
    c.rules.map (fun r => r.ens.map (Term.beq (.var 0))) = [some true, none] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel

def AssumeT : Config c := ⟨cfgOf 383 32 (.ctor assume [.dv Srt.bool (.bool true)]), by decide +kernel⟩
def AssumeF : Config c := ⟨cfgOf 383 32 (.ctor assume [.dv Srt.bool (.bool false)]), by decide +kernel⟩
def Ok : Config c := ⟨cfgOf 383 32 (.ctor ok_ []), by decide +kernel⟩

/-- **A rule's `ensures` is read, for every interpretation**: where it is true the rule steps, where
it is false the configuration has no successor. -/
theorem ens_everyH (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw AssumeT H) (cfgH noRaw Ok H) ∧
    ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw AssumeF H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 100) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 100)
    (by decide +kernel) H⟩

end EnsRule

end KCore.KernelMutants

#print axioms KCore.KernelMutants.EnsRule.ens_everyH
