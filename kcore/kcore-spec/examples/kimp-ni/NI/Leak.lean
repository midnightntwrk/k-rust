/-
  Kernel facts (examples/run.sh): the statement does not hold for every checker. The weakened
  checker `ImpSecLeaky` (f2-examples/imp-sec-leaky.k, written by findings/work/p3/leaky-kore.sh)
  is kimp's checker with one restriction removed: `conf` accepts an assignment to any identifier,
  so a branch on a high condition may write a low identifier. It accepts `if (h > 0) l = 1;` at
  the labelling G0 (`h` high, `l` low). From the stores `h ↦ 1, l ↦ 0` and `h ↦ 0, l ↦ 0`, which
  agree at `l`, kimp's two runs of that program end with `l ↦ 1` and `l ↦ 0`. Both runs are
  followed by the kernel (`NI.runFirst`) and are chains of `Step` (`NI.runFirst_reach`). So
  `NIFor ImpSecLeaky.c` is false (`leaky_not_ni`), while kimp's checker rejects the program
  (`not_secure_ifFlow`, Examples.lean): the statement tells the two checkers apart.
-/
import NI.Examples
import NI.Kind
import ImpSecLeaky

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NI

open KCore KCore.Cert KCore.Exec

/-- A store's Int value (`inj{Int,KItem}`). -/
def intV (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int n))

/-- The two initial stores: they agree at `l`. -/
def E₁ : GroundTerm := .map KCore.Srt.map [(key h, intV 1), (key l, intV 0)]
def E₂ : GroundTerm := .map KCore.Srt.map [(key h, intV 0), (key l, intV 0)]
/-- The first run's final store: the high branch wrote `l`. -/
def E₁' : GroundTerm := .map KCore.Srt.map [(key h, intV 1), (key l, intV 1)]

/-! ## The weakened checker's verdicts -/

theorem leaky_G0 : ImpSecLeaky.c.sortOf G0 = some Srt.map := by decide +kernel

theorem leaky_secure : SecureIn ImpSecLeaky.c G0 ifFlow :=
  eval_of_checkIn ImpSecLeaky.ok ImpSecLeaky.srReady ImpSecLeaky.matchReady 200 (by decide +kernel)

theorem leaky_low_l : LowIn ImpSecLeaky.c G0 l :=
  eval_of_checkIn ImpSecLeaky.ok ImpSecLeaky.srReady ImpSecLeaky.matchReady 200 (by decide +kernel)

theorem leaky_not_low_h : ¬ LowIn ImpSecLeaky.c G0 h := fun hl => by
  have := eval_unique_of_checkIn ImpSecLeaky.ok ImpSecLeaky.srReady ImpSecLeaky.matchReady
    ImpSecLeaky.coherent 200 (w := hi) (by decide +kernel) hl
  simp [lo, hi, S.lo, S.hi] at this
  exact absurd this (by decide)

/-! ## The stores -/

theorem lookup_two {k a b va vb v : GroundTerm} (hv : lookup (.map KCore.Srt.map [(a, va), (b, vb)]) k = some v) :
    v = va ∨ v = vb := by
  simp only [lookup, findK] at hv
  split at hv
  · exact Option.some.inj hv ▸ Or.inl rfl
  · split at hv
    · exact Option.some.inj hv ▸ Or.inr rfl
    · cases hv

theorem isValue_int (n : Int) (hn : checkIn Kimp.c 50 K.isValue [.ctor kseq [intV n, dotK]] (bool true) = true) :
    Eval Kimp.c K.isValue [.ctor kseq [intV n, dotK]] (some (bool true)) :=
  eval_of_checkIn Kimp.ok Kimp.srReady Kimp.matchReady 50 hn

theorem good_E₁ : Good E₁ := ⟨by decide +kernel, fun _ v hv => by
  rcases lookup_two hv with rfl | rfl
  · exact isValue_int 1 (by decide +kernel)
  · exact isValue_int 0 (by decide +kernel)⟩

theorem good_E₂ : Good E₂ := ⟨by decide +kernel, fun _ v hv => by
  rcases lookup_two hv with rfl | rfl <;> exact isValue_int 0 (by decide +kernel)⟩

/-- The two stores differ only at `h`, which is not low. -/
theorem lowEq_E : LowEqIn ImpSecLeaky.c G0 E₁ E₂ := fun X hX => by
  simp only [E₁, E₂, lookup, findK]
  by_cases hk : GroundTerm.cmp (key X) (key h) = .eq
  · have : X = h := by
      have := GroundTerm.cmp_eq _ _ hk
      simp only [key, GroundTerm.inj.injEq] at this
      exact this.2.2
    subst this
    exact absurd hX leaky_not_low_h
  · simp [hk]

/-! ## The two runs -/

/-- The first run's last configuration: `<k>` empty, `l ↦ 1`. -/
theorem run₁ : NI.runFirst Kimp.c 100 40 (init ifFlow E₁) = cfg dotK E₁' (.dv Srt.int (.int 0)) :=
  same_iff.mp (by decide +kernel)

/-- The second run's last configuration: `<k>` empty, `l ↦ 0`. -/
theorem run₂ : NI.runFirst Kimp.c 100 40 (init ifFlow E₂) = cfg dotK E₂ (.dv Srt.int (.int 0)) :=
  same_iff.mp (by decide +kernel)

theorem init_sorted (E : GroundTerm) (hE : Kimp.c.sortOf (init ifFlow E) = some topCellSort) :
    ∀ y, NI.runFirst Kimp.c 100 40 (init ifFlow E) = y →
      ∃ _ : Kimp.c.sortOf y = some topCellSort, Run (init ifFlow E) y := by
  intro y hy
  obtain ⟨z, hz, hr⟩ := NI.runFirst_reach Kimp.ok Kimp.srReady Kimp.matchReady 100 40 ⟨_, hE⟩
  rw [hy] at hz
  subst hz
  exact ⟨z.property, hE, z.property, star_of_reach hr⟩

/-- **B6.** The weakened checker's noninterference is false: it accepts `if (h > 0) l = 1;`, and
two runs from stores that agree at the low `l` end with stores that do not. -/
theorem leaky_not_ni : ¬ NIFor ImpSecLeaky.c := fun hni => by
  have hs₁ : Kimp.c.sortOf (init ifFlow E₁) = some topCellSort := by decide +kernel
  have hs₂ : Kimp.c.sortOf (init ifFlow E₂) = some topCellSort := by decide +kernel
  have hP : Kimp.c.sortOf ifFlow = some K.stmt := by decide +kernel
  obtain ⟨_, r₁⟩ := init_sorted E₁ hs₁ _ run₁
  obtain ⟨_, r₂⟩ := init_sorted E₂ hs₂ _ run₂
  have hlo := hni leaky_G0 hP leaky_secure good_E₁ good_E₂ lowEq_E r₁ r₂ l leaky_low_l
  -- the stores bind `l` to 1 and to 0
  have hd : (match lookup E₁' (key l), lookup E₂ (key l) with
      | some a, some b => same a b
      | _, _ => true) = false := by decide +kernel
  rw [hlo] at hd
  cases hv : lookup E₂ (key l) with
  | none => rw [hv] at hd; cases hd
  | some v => rw [hv] at hd; simp [same, GroundTerm.cmp_refl] at hd

/-- The weakened checker accepts the program kimp's checker rejects. -/
theorem checkers_differ : SecureIn ImpSecLeaky.c G0 ifFlow ∧ ¬ Secure G0 ifFlow :=
  ⟨leaky_secure, not_secure_ifFlow⟩

/-- info: 'NI.leaky_not_ni' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaky_not_ni

end NI
