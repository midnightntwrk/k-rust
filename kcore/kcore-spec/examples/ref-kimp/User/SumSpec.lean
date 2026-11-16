/-
  K's claim `sum-spec` (imp-semantics, `examples/specs/imp-sum-spec.k`) on kimp read from
  kompile's own KORE:

      claim <k> while (!($n <= 0)) { $s = $s + $n; $n = $n + -1; } => .K ... </k>
            <env> $n |-> (N => 0)  $s |-> (S => S +Int ((N +Int 1) *Int N /Int 2)) </env>
        requires N >=Int 0

  The program and configurations are written with the package's constructors (`RefKimp.Syntax`).
  Each step is `fire i`: rule i of the package's `Step`, its substitution, successor, match,
  `requires` and right-hand side found and checked by the kernel (KcoreSpec/FireTac.lean). One
  pass of the loop's condition, one iteration, and the exit make the run; `loop_runs` is the
  induction on `$n`, the claim's circularity, with the rest of the k cell growing by the block's
  `{}` each pass. `sum_spec` is the claim all-path (the package's determinism makes the run the
  only one), `sum_spec_entailed` what it means in matching logic through `star_entails`.
-/
import RefKimp.Syntax
import RefKimp.Surface
import RefKimp.Kinds.Det
import RefKimp.FnHyp
import KcoreSpec.RunsSound

set_option autoImplicit false

namespace RefKimp.SumSpec

open KCore RefKimp.Syntax

/-! ## The program and the configurations -/

def body : Tm Srt.«Stmt» :=
  «{_}» («__» («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
    («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))
def loop : Tm Srt.«Stmt» := «while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0))) body

/-- A configuration: the k cell k, `$n ↦ n` and `$s ↦ s` in the env cell, any counter cell C. -/
def cfg (k : Tm KCore.Srt.k) (n s : Int) (C : GroundTerm) : GroundTerm :=
  («<generatedTop>» («<k>» k) («<env>» (Tm.map [(Tm.ident "$n", Tm.int n), (Tm.ident "$s", Tm.int s)]))
    ⟨C⟩).val

/-- The claim's left-hand side: the loop before any rest K of the k cell. -/
def init (N S : Int) (K C : GroundTerm) : GroundTerm := cfg (Tm.kseq loop ⟨K⟩) N S C

/-- The claim's right-hand side: the rest K alone, `$n ↦ 0`, `$s ↦ S +Int (N +Int 1) *Int N /Int 2`
(`/Int` truncates). -/
def final (N S : Int) (K C : GroundTerm) : GroundTerm :=
  cfg ⟨K⟩ 0 (S + ((N + 1) * N).tdiv 2) C

/-! ## The arithmetic -/

theorem tri_step (n : Nat) (b : Int) :
    b + ((n + 1 : Nat) : Int) + ((n * (n + 1) / 2 : Nat) : Int) = b + (((n + 1) * (n + 1 + 1) / 2 : Nat) : Int) := by
  have h : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_comm (n + 1) n, Nat.mul_comm (n + 1) 2]
  rw [show n + 1 + 1 = n + 2 from rfl, h, Nat.add_mul_div_left _ _ (by decide)]
  push_cast; omega

theorem tri_tdiv (n : Nat) : ((n * (n + 1) / 2 : Nat) : Int) = (((n : Int) + 1) * n).tdiv 2 := by
  rw [show ((n : Int) + 1) * n = (((n + 1) * n : Nat) : Int) by push_cast; rfl,
    show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.ofNat_tdiv, Nat.mul_comm]

/-! ## The loop, by induction on `$n` -/

/-- From the loop with `$n ↦ n` and `$s ↦ b` before any rest K of the k cell, a run reaches K
alone, with `$n ↦ 0` and `$s ↦ b + n(n+1)/2`. The induction hypothesis is used with the rest
`{} ~> K` the iteration leaves. -/
theorem loop_runs : ∀ (n : Nat) (b : Int) (K C : GroundTerm), c.sortOf K = some KCore.Srt.k →
    c.sortOf C = some KCore.Srt.counter →
    Runs c (init n b K C) (cfg ⟨K⟩ 0 (b + ((n * (n + 1) / 2 : Nat) : Int)) C)
  | 0, b, K, C, hK, hC => by
    fire 69 73 74 26 49 68 13 51 0 27 25  -- the condition, false
    fire 75 78  -- the exit
    rw [show b + ((0 * (0 + 1) / 2 : Nat) : Int) = b by simp]
    run_end
  | n + 1, b, K, C, hK, hC => by
    fire 69 73 74 26 49 68 13 51 0 27 25  -- the condition
    rw [show (!decide (((n + 1 : Nat) : Int) ≤ 0)) = true by simp]
    fire 76 77 72 77 72 70 40 68 7 41 68 8 42 19 71 70 40 68 7 42 19 71 78  -- one iteration
    rw [show ((n + 1 : Nat) : Int) + -1 = n by omega]
    run_by loop_runs n (b + (n + 1 : Nat)) (Tm.kseq «{}» ⟨K⟩).val C (by ksort) hC
    fire 78  -- the outer block's `{}`
    rw [tri_step]
    run_end

/-! ## The claim -/

/-- **The claim, one path**: from every configuration of the left-hand side with `N ≥ 0`, a run of
`Step` reaches the configuration of the right-hand side. -/
theorem sum_spec_run (N S : Int) (hN : 0 ≤ N) (K C : GroundTerm) (x : Config c)
    (hx : x.val = init N S K C) : ∃ y : Config c, y.val = final N S K C ∧ Star (Step c) x y := by
  config_sorts hx
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hN
  refine (loop_runs n S K C hK hC).of_eq ?_ x hx
  rw [final, tri_tdiv]

/-- The step of the package is deterministic. -/
theorem step_det : ∀ x y y' : Config c, Step c x y → Step c x y' → y = y' :=
  fun _ _ _ h h' => deterministic c.hooks h h'

/-- **The claim `sum-spec`** (imp-semantics, `examples/specs/imp-sum-spec.k`), all-path, as K
proves it: for every `N ≥ 0`, S, rest K of the k cell and counter cell C, every complete run of
`Step` from the left-hand side passes through the right-hand side. -/
theorem sum_spec (N S : Int) (hN : 0 ≤ N) (K C : GroundTerm) :
    Reachability.AllPath (Step c) (fun x => x.val = init N S K C) (fun y => y.val = final N S K C) :=
  Reachability.allPath_of_star step_det fun x hx => sum_spec_run N S hN K C x hx

/-- **The claim in matching logic**: by soundness at each step (`KCore.star_entails`, from
`RefKimp.coreOK_defn` and `RefKimp.plain_defn`), the theory `Γ` of the definition
entails, for every instance of the claim's variables, that the left-hand side's configuration
reaches the right-hand side's, `⟦init⟧ → μX. ⟦final⟧ ∨ •X`. -/
theorem sum_spec_entailed (N S : Int) (hN : 0 ≤ N) (K C : GroundTerm) (x : Config c)
    (hx : x.val = init N S K C) :
    ∃ y : Config c, y.val = final N S K C ∧
      (Faithful.Γ c ⊧ (den c x.val ⇒ eventually (den c y.val))) :=
  let ⟨y, hy, hs⟩ := sum_spec_run N S hN K C x hx
  ⟨y, hy, star_entails coreOK_defn (Semantics.readsConfined_of_plain plain_defn) hs⟩

/-- The same run in a number of steps: `⟦init⟧ → •ⁿ⟦final⟧` for some n. -/
theorem sum_spec_entailed_nextN (N S : Int) (hN : 0 ≤ N) (K C : GroundTerm) (x : Config c)
    (hx : x.val = init N S K C) :
    ∃ y : Config c, y.val = final N S K C ∧ ∃ n, (Faithful.Γ c ⊧ (den c x.val ⇒ nextN n (den c y.val))) :=
  let ⟨y, hy, hs⟩ := sum_spec_run N S hN K C x hx
  ⟨y, hy, star_entails_nextN coreOK_defn (Semantics.readsConfined_of_plain plain_defn) hs⟩

#eval show Lean.CoreM Unit from do
  for n in [``sum_spec, ``sum_spec_run, ``sum_spec_entailed, ``loop_runs] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end RefKimp.SumSpec
