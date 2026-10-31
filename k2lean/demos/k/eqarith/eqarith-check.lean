import KPrelude.Tactic

/-! The checks of the hooks' arithmetic in the generic equation proofs (`k2l_eq`, EQ-22): a
comparison of an arithmetic hook (`IntHook.lt M (IntHook.add N 1)`) reads, after `simp`, as Lean's
comparison of Lean's arithmetic, in a hypothesis and in the goal, under `KEqHook.ne` and inside an
`if`, so that `omega` decides it; the generic proofs prove such laws of an author (KEVM's
`A +Int B <=Int C` against `A <=Int C -Int B`) and still fail on a false one. The gate runs this
file (`lake env lean` in the prelude) and fails on any unexpected message. -/

namespace EqArithCheck

open KPrelude

abbrev SortInt := Int

-- `k2l_arith_omega` (the discharger of `k2l_ite_neg`/`k2l_ite_pos`, the last arm of the row proofs)
example (M N : Int) (h : IntHook.lt M (IntHook.add N 1) = true) : M ≤ N := by k2l_arith_omega
example (M N : Int) (h : M ≤ N) : IntHook.lt M (IntHook.add N 1) = true := by k2l_arith_omega
example (M N : Int) (h : IntHook.le (IntHook.mul 2 M) (IntHook.sub N 1) = true) : 2 * M < N := by
  k2l_arith_omega
example (M N : Int) (h : IntHook.gt (IntHook.add N 1) M = false) : M ≥ N + 1 := by k2l_arith_omega
example (M N : Int) (h : KEqHook.ne M (IntHook.add N 1) = true) (h2 : M ≤ N + 1)
    (h3 : IntHook.ge M (IntHook.add N 1) = true) : False := by k2l_arith_omega
example (M N : Int) (h : BoolHook.and (IntHook.lt 0 M) (IntHook.le M (IntHook.add N 1)) = true) :
    0 ≤ N := by k2l_arith_omega
example (X Y : Int) (h : IntHook.le (IntHook.max X Y) 3 = true) : Y ≤ 3 := by k2l_arith_omega

-- `simp_all [k2l_eq]` (the generic proofs `k2l_eqn_a`, `k2l_eqn_b`)
example (M N : Int) (h : IntHook.lt M (IntHook.add N 1) = true) : M ≤ N := by
  simp_all [k2l_eq]; omega
example (M N : Int) (h : M ≤ N) :
    (if IntHook.lt M (IntHook.add N 1) = true then 1 else 0) = 1 := by simp_all [k2l_eq]; omega

-- an author's laws, as the generator states them (`Simp.s_…`), by the generic proof
example : ∀ (A B C : SortInt),
    IntHook.le (IntHook.add A B) C = IntHook.le A (IntHook.sub C B) := by intros; k2l_eqn_a []
example : ∀ (A B C : SortInt),
    IntHook.lt A (IntHook.add B C) = IntHook.lt (IntHook.sub A C) B := by intros; k2l_eqn_a []
example : ∀ (A B C D : SortInt),
    IntHook.lt (IntHook.add A B) (IntHook.add C D) = IntHook.lt (IntHook.sub A C) (IntHook.sub D B) := by
  intros; k2l_eqn_a []

-- a false law is not proved
/-- error: k2l_eqn_a failed -/
#guard_msgs (substring := true, error, drop warning) in
example : ∀ (A B C : SortInt),
    IntHook.lt A (IntHook.add B C) = IntHook.lt (IntHook.sub A C) (IntHook.add B 1) := by
  intros; first | k2l_eqn_a [] | fail "k2l_eqn_a failed"
/-- error: k2l_arith_omega failed -/
#guard_msgs (substring := true, error, drop warning) in
example (M N : Int) (h : IntHook.lt M (IntHook.add N 1) = true) : M < N := by
  first | k2l_arith_omega | fail "k2l_arith_omega failed"

end EqArithCheck
