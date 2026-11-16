/-
  kimp under the keyed policy (`kcore gen … --keyed env`, Kimp/Kinds/NI.lean): the store `<env>` is
  secret except at the identifiers the observer is given (`lo`), and the rest of the configuration,
  the program included, is public. The decided condition covers every rule of kimp but `CALC.var`,
  which reads the store at the identifier the program names; `CALC.assign`'s update of the store is
  covered (`updOK`). So `Kimp.noninterference` has that one obligation.

  The obligation is false, not undischarged (kernel facts): from the stores `h ↦ 1, l ↦ 0` and
  `h ↦ 0, l ↦ 0`, which agree at `l`, kimp's two runs of `l = h;` end with `l ↦ 1` and `l ↦ 0`
  (`not_noninterference`, `var_not_unwinds`). Without a checker kimp leaks, so a relation in which
  the program is public cannot give kimp's statement `KimpNI` (Spec.lean): reading a high
  identifier is safe only where the checker's typing puts the value it reads in a high context.
  That typing of runtime k cells is the relation still missing.
-/
import NI.Examples
import Kimp.Kinds.NI

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NI.Keyed

open KCore KCore.Cert KCore.Exec NI

/-- The observer is given `l`. -/
def loL (k : GroundTerm) : Prop := k = key l

/-- A store's Int value (`inj{Int,KItem}`). -/
def iv (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int n))

def S₁ : Entries := [(key h, iv 1), (key l, iv 0)]
def S₂ : Entries := [(key h, iv 0), (key l, iv 0)]
/-- The first run's final store: `l` holds what `h` held. -/
def S₁' : Entries := [(key h, iv 1), (key l, iv 1)]

def n0 : GroundTerm := .dv Srt.int (.int 0)

theorem cfg_eq (K E n : GroundTerm) :
    cfg K E n = .ctor topLabel [.ctor Kimp.Sym.«<k>» [K], .ctor Kimp.Sym.«<env>» [E], .ctor counterLabel [n]] :=
  rfl

/-- The two stores are related at the keyed position: canonical, the same keys, the same entry at
`l`, well-sorted entries at the same keys. -/
theorem keyRel_start : KCore.NI.KeyRel Kimp.c loL S₁ S₂ := by
  refine ⟨show keysSorted S₁ = true by decide +kernel, show keysSorted S₂ = true by decide +kernel,
    fun k => ⟨fun hk => ?_, ?_⟩⟩
  · subst hk; decide +kernel
  · simp only [S₁, S₂, Map.find_cons, Map.find_nil]
    by_cases h1 : k = key h
    · subst h1; rw [if_pos rfl, if_pos rfl]
      show Kimp.c.entryOK KCore.Srt.kitem KCore.Srt.kitem (key h, iv 1) = Kimp.c.entryOK KCore.Srt.kitem KCore.Srt.kitem (key h, iv 0)
      decide +kernel
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : k = key l
      · rw [if_pos h2]; exact rfl
      · rw [if_neg h2]; trivial

theorem start₁ : Kimp.c.sortOf (init explicitFlow (.map KCore.Srt.map S₁)) = some topCellSort := by decide +kernel
theorem start₂ : Kimp.c.sortOf (init explicitFlow (.map KCore.Srt.map S₂)) = some topCellSort := by decide +kernel

/-- The two starts are equal outside the store, and their stores are related. -/
theorem start_lowEq : KCore.NI.LowEq Kimp.c loL Kimp.high ⟨_, start₁⟩ ⟨_, start₂⟩ := by
  show KCore.NI.EqOut Kimp.c loL Kimp.high (init explicitFlow (.map KCore.Srt.map S₁)) (init explicitFlow (.map KCore.Srt.map S₂))
  rw [Kimp.high_eq, init, init, cfg_eq, cfg_eq]
  refine .ctor rfl fun i a b ha hb => ?_
  rcases i with _ | _ | _ | i <;> simp at ha hb <;> subst ha <;> subst hb
  · exact .same
  · refine .ctor rfl fun j a b ha hb => ?_
    rcases j with _ | j <;> simp at ha hb
    subst ha; subst hb
    exact .keyed (by decide) keyRel_start
  · exact .same

/-- Both runs of `l = h;` stop with `<k>` empty. -/
theorem run₁ : KCore.NI.runFirst Kimp.c 100 40 (init explicitFlow (.map KCore.Srt.map S₁)) = cfg dotK (.map KCore.Srt.map S₁') n0 :=
  same_iff.mp (by decide +kernel)
theorem run₂ : KCore.NI.runFirst Kimp.c 100 40 (init explicitFlow (.map KCore.Srt.map S₂)) = cfg dotK (.map KCore.Srt.map S₂) n0 :=
  same_iff.mp (by decide +kernel)
theorem stuck₁ : stuckCheck Kimp.c 100 (cfg dotK (.map KCore.Srt.map S₁') n0) = true := by decide +kernel
theorem stuck₂ : stuckCheck Kimp.c 100 (cfg dotK (.map KCore.Srt.map S₂) n0) = true := by decide +kernel

theorem stores_not_related :
    ∀ A B, KCore.NI.EqOut Kimp.c loL [[KCore.NI.keyTag]] A B → A = .map KCore.Srt.map S₁' → B = .map KCore.Srt.map S₂ → False := by
  intro A B h
  cases h with
  | high h _ => intro _ _; exact absurd h (by decide)
  | same => intro h1 h2; rw [h1] at h2; exact absurd h2 (by decide +kernel)
  | ctor _ _ => intro h1; cases h1
  | keyed _ hk =>
    intro h1 h2; cases h1; cases h2
    exact absurd ((hk.2.2 (key l)).1 rfl) (by decide +kernel)

/-- The final configurations' stores differ at the observed `l`. -/
theorem final_not_lowEq : ¬ KCore.NI.EqOut Kimp.c loL Kimp.high (cfg dotK (.map KCore.Srt.map S₁') n0) (cfg dotK (.map KCore.Srt.map S₂) n0) := by
  rw [Kimp.high_eq, cfg_eq, cfg_eq]
  intro he
  obtain ⟨vs₂, hv, _, hr⟩ := he.ctor_inv (by decide)
  simp only [GroundTerm.ctor.injEq, true_and] at hv
  subst hv
  obtain ⟨ws, hw, _, hr'⟩ := (hr 1 _ _ rfl rfl).ctor_inv (by decide)
  simp only [GroundTerm.ctor.injEq, true_and] at hw
  subst hw
  exact stores_not_related _ _ (hr' 0 _ _ rfl rfl) rfl rfl

/-- **kimp without a checker is not noninterfering** for the store, `l` observed. -/
theorem not_noninterference :
    ¬ KCore.NI.TINI Kimp.c (KCore.NI.LowEq Kimp.c loL Kimp.high) (KCore.NI.Stuck Kimp.c) (KCore.NI.LowEq Kimp.c loL Kimp.high) := by
  intro hT
  obtain ⟨z₁, hz₁, hr₁⟩ := KCore.NI.runFirst_reach Kimp.ok Kimp.srReady Kimp.matchReady 100 40 ⟨_, start₁⟩
  obtain ⟨z₂, hz₂, hr₂⟩ := KCore.NI.runFirst_reach Kimp.ok Kimp.srReady Kimp.matchReady 100 40 ⟨_, start₂⟩
  rw [run₁] at hz₁; rw [run₂] at hz₂
  have hs₁ : KCore.NI.Stuck Kimp.c z₁ := fun y => by
    obtain ⟨v, hv⟩ := z₁; simp only at hz₁; subst hz₁
    exact (stuckCheck_sound Kimp.ok Kimp.srReady Kimp.matchReady Kimp.c.hooks (Kimp.coherent_withHooks Kimp.c.hooks) (x := ⟨_, hv⟩) stuck₁) y
  have hs₂ : KCore.NI.Stuck Kimp.c z₂ := fun y => by
    obtain ⟨v, hv⟩ := z₂; simp only at hz₂; subst hz₂
    exact (stuckCheck_sound Kimp.ok Kimp.srReady Kimp.matchReady Kimp.c.hooks (Kimp.coherent_withHooks Kimp.c.hooks) (x := ⟨_, hv⟩) stuck₂) y
  have := hT _ _ z₁ z₂ start_lowEq hr₁ hr₂ hs₁ hs₂
  unfold KCore.NI.LowEq at this
  rw [← hz₁, ← hz₂] at this
  exact final_not_lowEq this

/-- **The one obligation is false**: `CALC.var` does not unwind when the program is public. -/
theorem var_not_unwinds :
    ¬ ∀ r, Kimp.c.rules[19]? = some r → KCore.NI.RuleUnwinds Kimp.c (KCore.NI.LowEq Kimp.c loL Kimp.high) r :=
  fun h => not_noninterference (Kimp.noninterference Kimp.c.hooks loL h)

/-- info: 'NI.Keyed.var_not_unwinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms var_not_unwinds

end NI.Keyed
