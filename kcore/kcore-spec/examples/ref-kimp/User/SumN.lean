/-
  K's claim `sum-N` (imp-semantics, `examples/specs/imp-simple-spec.k`) on kimp read from
  kompile's own KORE:

      claim <k> $s = 0; $n = N; while (0 < $n) { $s = $s + $n ; $n = $n - 1 ; } => .K ... </k>
            <env> .Map => $s |-> (N *Int (N +Int 1)) /Int 2 $n |-> 0 </env>
        requires 0 <=Int N

  The whole program from the empty store: the two assignments, then the loop by induction on `$n`.
-/
import RefKimp.Syntax
import RefKimp.Surface
import RefKimp.Kinds.Det

set_option autoImplicit false

namespace RefKimp.SumN

open KCore RefKimp.Syntax

def body : Tm Srt.«Stmt» :=
  «{_}» («__» («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
    («_=_;» (Tm.ident "$n") («_-_» (Tm.ident "$n") (Tm.int 1))))
def loop : Tm Srt.«Stmt» := «while(_)_» («_<_» (Tm.int 0) (Tm.ident "$n")) body
def prog (N : Int) : Tm Srt.«Stmt» :=
  «__» («_=_;» (Tm.ident "$s") (Tm.int 0)) («__» («_=_;» (Tm.ident "$n") (Tm.int N)) loop)

/-- A configuration: the k cell k, `$n ↦ n` and `$s ↦ s` in the env cell, any counter cell C. -/
def cfg (k : Tm KCore.Srt.k) (n s : Int) (C : GroundTerm) : GroundTerm :=
  («<generatedTop>» («<k>» k) («<env>» (Tm.map [(Tm.ident "$n", Tm.int n), (Tm.ident "$s", Tm.int s)]))
    ⟨C⟩).val

/-- The claim's left-hand side: the program before any rest K of the k cell, the empty store. -/
def init (N : Int) (K C : GroundTerm) : GroundTerm :=
  («<generatedTop>» («<k>» (Tm.kseq (prog N) ⟨K⟩)) («<env>» (Tm.map [])) ⟨C⟩).val

/-- The claim's right-hand side: K alone, `$s ↦ (N *Int (N +Int 1)) /Int 2`, `$n ↦ 0`. -/
def final (N : Int) (K C : GroundTerm) : GroundTerm := cfg ⟨K⟩ 0 ((N * (N + 1)).tdiv 2) C

theorem tri_step (n : Nat) (b : Int) :
    b + ((n + 1 : Nat) : Int) + ((n * (n + 1) / 2 : Nat) : Int) = b + (((n + 1) * (n + 1 + 1) / 2 : Nat) : Int) := by
  have h : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_comm (n + 1) n, Nat.mul_comm (n + 1) 2]
  rw [show n + 1 + 1 = n + 2 from rfl, h, Nat.add_mul_div_left _ _ (by decide)]
  push_cast; omega

theorem tri_tdiv (n : Nat) : ((n * (n + 1) / 2 : Nat) : Int) = ((n : Int) * (n + 1)).tdiv 2 := by
  rw [show (n : Int) * (n + 1) = ((n * (n + 1) : Nat) : Int) by push_cast; rfl,
    show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.ofNat_tdiv]

/-- The loop, by induction on `$n`: from `$n ↦ n`, `$s ↦ b`, to `$n ↦ 0`, `$s ↦ b + n(n+1)/2`. -/
theorem loop_runs : ∀ (n : Nat) (b : Int) (K C : GroundTerm), c.sortOf K = some KCore.Srt.k →
    c.sortOf C = some KCore.Srt.counter →
    Runs c (cfg (Tm.kseq loop ⟨K⟩) n b C) (cfg ⟨K⟩ 0 (b + ((n * (n + 1) / 2 : Nat) : Int)) C)
  | 0, b, K, C, hK, hC => by
    fire 69 73 74 53 68 16 54 25  -- the condition, false
    fire 75 78  -- the exit
    rw [show b + ((0 * (0 + 1) / 2 : Nat) : Int) = b by simp]
    run_end
  | n + 1, b, K, C, hK, hC => by
    fire 69 73 74 53 68 16 54 25  -- the condition
    rw [show decide ((0 : Int) < ((n + 1 : Nat) : Int)) = true by simp]
    fire 76 77 72 77 72 70 40 68 7 41 68 8 42 19 71 70 43 68 9 45 19 71 78  -- one iteration
    rw [show ((n + 1 : Nat) : Int) - 1 = n by omega]
    run_by loop_runs n (b + (n + 1 : Nat)) (Tm.kseq «{}» ⟨K⟩).val C (by ksort) hC
    fire 78  -- the outer block's `{}`
    rw [tri_step]
    run_end

/-- **The claim `sum-N`, one path.** -/
theorem sum_N_run (N : Int) (hN : 0 ≤ N) (K C : GroundTerm) (x : Config c)
    (hx : x.val = init N K C) : ∃ y : Config c, y.val = final N K C ∧ Star (Step c) x y := by
  config_sorts hx
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hN
  have h : Runs c (init n K C) (final n K C) := by
    fire 72 71 72 71  -- `$s = 0;`, `$n = N;`
    run_by loop_runs n 0 K C hK hC
    rw [Int.zero_add, tri_tdiv]
    run_end
  exact h x hx

theorem step_det : ∀ x y y' : Config c, Step c x y → Step c x y' → y = y' :=
  fun _ _ _ h h' => deterministic c.hooks h h'

/-- **The claim `sum-N`**, all-path (the package's determinism). -/
theorem sum_N (N : Int) (hN : 0 ≤ N) (K C : GroundTerm) :
    Reachability.AllPath (Step c) (fun x => x.val = init N K C) (fun y => y.val = final N K C) :=
  Reachability.allPath_of_star step_det fun x hx => sum_N_run N hN K C x hx

#eval show Lean.CoreM Unit from do
  for n in [``sum_N, ``sum_N_run, ``loop_runs] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end RefKimp.SumN
