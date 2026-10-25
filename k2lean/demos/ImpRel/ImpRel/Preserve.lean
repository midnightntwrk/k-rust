import ImpRel.Bisim
import KPrelude.InvTactic
import KPrelude.InvSteps
import KPrelude.InvColl

/-! Hand-written. `inv_step` of the generated `Bisim.lean` (the invariant `relate` generated:
store keys are `Id`s, store values are `Value`s), re-proved over `KImp` with the invariant core
(`KPrelude.Invariant`) and `k2l_preserve` only. The unfolding set names the definitions `Inv` is made
of; no tactic is specific to this case. -/

namespace ImpRelInv

open KPrelude ImpRel

theorem inv_preserved : Preserved KImp.Step Inv := by
  k2l_preserve [cell0, InvCell0, KeysOK, ValsOK, keyOK, valOK]

/-- The statement of `ImpRel.inv_step`. -/
theorem inv_step {c c' : KImp.SortGeneratedTopCell} (hi : Inv c) (h : KImp.Step c c') : Inv c' :=
  inv_preserved c c' hi h

/-- Every configuration reachable from one satisfying `Inv` satisfies it. -/
theorem inv_stepsN {n : Nat} {c c' : KImp.SortGeneratedTopCell} (h : StepsN KImp.Step n c c')
    (hi : Inv c) : Inv c' :=
  inv_preserved.stepsN h hi

#k2l_assert_axioms inv_preserved inv_step inv_stepsN

end ImpRelInv
