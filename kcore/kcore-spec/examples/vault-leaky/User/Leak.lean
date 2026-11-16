/-
  The decided condition is not vacuous. vault-leaky (f2-examples/vault-leaky.k) adds the rule
  `leak`, which copies the secret `<sec>` into the public `<pub>`; the condition rejects it, so
  the generated theorem `noninterference` has one obligation, rule 5's unwinding. Two runs of
  `leak` from configurations equal outside `<sec>` (the secret 1, then 0) stop with `<pub>` 1
  and `<pub>` 0 (both followed by the kernel, `NI.runFirst`, compared by `same`; both stuck, `stuckCheck`). So the
  statement is false (`not_noninterference`), and so is the obligation (`leak_not_unwinds`):
  it is a real premise, not a gap in the decision.
-/
import VaultLeaky
import KcoreSpec.Cert

set_option autoImplicit false
set_option maxRecDepth 100000

namespace VaultLeaky

open KCore KCore.Cert KCore.Exec

/- The observed keys: vault has no keyed position, so every statement holds for any. -/
variable (lo : GroundTerm → Prop)

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)

/-- A configuration: `<k>` holds K, `<pub>` p, `<sec>` s, the counter 0. -/
def cfgOf (K : GroundTerm) (p s : Int) : GroundTerm :=
  .ctor topLabel [.ctor Sym.«<k>» [K], .ctor Sym.«<pub>» [int p], .ctor Sym.«<sec>» [int s],
    .ctor counterLabel [int 0]]

def leakK : GroundTerm := .ctor kseq [.inj Srt.«Op» Srt.kitem (.ctor Sym.«leak» []), .ctor dotk []]
def doneK : GroundTerm := .ctor dotk []

theorem start₁ : c.sortOf (cfgOf leakK 0 1) = some topCellSort := by decide +kernel
theorem start₂ : c.sortOf (cfgOf leakK 0 0) = some topCellSort := by decide +kernel

/-- The two starts are equal outside `<sec>`. -/
theorem start_lowEq : NI.LowEq c lo high ⟨_, start₁⟩ ⟨_, start₂⟩ := by
  show NI.EqOut c lo high (cfgOf leakK 0 1) (cfgOf leakK 0 0)
  rw [high_eq]
  refine .ctor rfl fun i a b ha hb => ?_
  rcases i with _ | _ | _ | _ | i <;> simp [cfgOf] at ha hb <;> subst ha <;> subst hb
  · exact .same
  · exact .same
  · refine .ctor rfl fun j a b ha hb => ?_
    rcases j with _ | j <;> simp at ha hb
    subst ha; subst hb
    exact .high (by decide) (by decide +kernel)
  · exact .same

/-- Both runs of `leak` stop after one step: the public cell holds the secret. -/
theorem run₁ : NI.runFirst c 100 3 (cfgOf leakK 0 1) = cfgOf doneK 1 1 := same_iff.mp (by decide +kernel)
theorem run₂ : NI.runFirst c 100 3 (cfgOf leakK 0 0) = cfgOf doneK 0 0 := same_iff.mp (by decide +kernel)
theorem stuck₁ : stuckCheck c 100 (cfgOf doneK 1 1) = true := by decide +kernel
theorem stuck₂ : stuckCheck c 100 (cfgOf doneK 0 0) = true := by decide +kernel

/-- The two final configurations differ at `<pub>`, which is not secret. -/
theorem final_not_lowEq : ¬ NI.EqOut c lo high (cfgOf doneK 1 1) (cfgOf doneK 0 0) := by
  rw [high_eq]
  intro h
  obtain ⟨vs₂, he, _, hr⟩ := h.ctor_inv (by decide)
  simp only [cfgOf, GroundTerm.ctor.injEq, true_and] at he
  subst he
  have h1 := hr 1 _ _ rfl rfl
  have := h1.eq_of_nil (by decide)
  simp [int] at this

/-- **vault-leaky is not noninterfering** for `<sec>`. -/
theorem not_noninterference : ¬ NI.TINI c (NI.LowEq c lo high) (NI.Stuck c) (NI.LowEq c lo high) := by
  intro h
  obtain ⟨z₁, hz₁, hr₁⟩ := NI.runFirst_reach ok srReady matchReady 100 3 ⟨_, start₁⟩
  obtain ⟨z₂, hz₂, hr₂⟩ := NI.runFirst_reach ok srReady matchReady 100 3 ⟨_, start₂⟩
  rw [run₁] at hz₁; rw [run₂] at hz₂
  have hs₁ : NI.Stuck c z₁ := fun y => by
    obtain ⟨v, hv⟩ := z₁; simp only at hz₁; subst hz₁
    exact (stuckCheck_sound ok srReady matchReady c.hooks (coherent_withHooks c.hooks) (x := ⟨_, hv⟩) stuck₁) y
  have hs₂ : NI.Stuck c z₂ := fun y => by
    obtain ⟨v, hv⟩ := z₂; simp only at hz₂; subst hz₂
    exact (stuckCheck_sound ok srReady matchReady c.hooks (coherent_withHooks c.hooks) (x := ⟨_, hv⟩) stuck₂) y
  have := h _ _ z₁ z₂ (start_lowEq lo) hr₁ hr₂ hs₁ hs₂
  unfold NI.LowEq at this
  rw [← hz₁, ← hz₂] at this
  exact final_not_lowEq lo this

/-- **The obligation is false**: rule 5 (`leak`) does not unwind. -/
theorem leak_not_unwinds :
    ¬ ∀ r, c.rules[5]? = some r → NI.RuleUnwinds c (NI.LowEq c lo high) r :=
  fun h => not_noninterference lo (noninterference c.hooks lo h)

end VaultLeaky
