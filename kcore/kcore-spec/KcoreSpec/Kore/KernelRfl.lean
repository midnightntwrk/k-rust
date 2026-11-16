/-
  `kernel_rfl`: close a closed equation by `Eq.refl`, checked by the kernel's definitional equality
  alone. Kept from F0Route when F0 was removed (P1.4).
-/
import Lean

open Lean Elab Tactic Meta in
/-- `kernel_rfl`: close a closed goal `a = b` by `Eq.refl a`, checked by the kernel's
definitional equality only (as `decide +kernel` leaves its decision to the kernel); the
elaborator unfolds nothing. -/
elab "kernel_rfl" : tactic => liftMetaFinishingTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  let some (α, a, _) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  if t.hasFVar || t.hasMVar then throwError "kernel_rfl: the goal must be closed"
  let u ← getLevel α
  let pf := mkApp2 (mkConst ``Eq.refl [u]) α a
  let lvls := (collectLevelParams {} t).params.toList
  let name ← mkAuxLemma lvls t pf
  g.assign (mkConst name (lvls.map mkLevelParam))
