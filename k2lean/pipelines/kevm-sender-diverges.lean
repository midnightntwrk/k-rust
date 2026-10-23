import KEvm.Functions
import KPrelude.Tactic

/-! KEVM's `senderTxData` is the least fixed point of its equations (`kevm-termination.toml`):
at chain id -4 its two rules cycle (0 → 27 → 0), K's rewriting does not terminate, and the
function has no value there. `kevm.sh check` elaborates this file against the generated library. -/

namespace KEvm
open KPrelude

theorem senderTxData_diverges [Hooks] (t : SortTxData) (r s : SortBytes) : K.senderTxData t 0 r s (-4) = none := by
  have adm := fun (n : Int) => Lean.Order.admissible_apply (fun (_ : Int) (v : Option SortAccount) => v = none) n
    (Lean.Order.admissible_flatOrder _ rfl)
  have := K.senderTxData.fixpoint_induct t r s (-4) (fun f => f 0 = none ∧ f 27 = none)
    (Lean.Order.admissible_and _ _ (adm 0) (adm 27))
    (fun f ⟨h0, h27⟩ => by
      refine ⟨?_, ?_⟩ <;> simp [KPrelude.BoolHook.or, KPrelude.IntHook.eq, KPrelude.IntHook.add, KPrelude.IntHook.mul,
        KPrelude.IntHook.sub, KPrelude.IntHook.emod, h0, h27, show (-8 : Int).emod 2 = 0 by decide])
  exact this.1

#k2l_assert_axioms KEvm.senderTxData_diverges

end KEvm
