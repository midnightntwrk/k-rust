import OpenComm
/-
  A user module of the package of `f2-examples/commctor.kompile.kore` (e2-comm-ctor: `and` an open
  generator without a law, `or` one with `assoc`), built against it by test/open-gen.sh: for every H
  with `OpenLaws` and `OpenTotal`, the semantics is exact (`ExactC`, by `exact_hyp` from the
  package's `fnHyp_defn`), and its instance at `lawHooks defn.sem H`, both obligations discharged.
-/
set_option autoImplicit false

namespace OpenComm.User
open KCore

/-- The text declares no parameter total that no registry hook implements: `HooksTotal` holds at
every H. -/
theorem totalParams_nil : defn.totalParams = [] := by kernel_rfl

theorem hooksTotal (H : HookParams) : HooksTotal H := by
  unfold HooksTotal; rw [totalParams_nil]; exact ParamsTotal.nil

/-- **Exactness for every H with `OpenLaws` and `OpenTotal`.** -/
theorem exact_defn (H : HookParams) (hop : OpenLaws (defn.sem.withHooks H))
    (_hot : OpenTotal (defn.sem.withHooks H)) : ExactC (defn.sem.withHooks H) :=
  exact_hyp _ (coreOK_withHooks_defn H) (fnHyp_defn H hop _hot (hooksTotal H))

/-- `exact_defn` at `lawHooks defn.sem H`, the two obligations discharged. -/
theorem exact_defn_lawHooks (H : HookParams) : ExactC (defn.sem.withHooks (lawHooks defn.sem H)) :=
  exact_defn (lawHooks defn.sem H) (openLaws_lawHooks_defn H) (openTotal_lawHooks_defn H)

end OpenComm.User

#print axioms OpenComm.User.exact_defn
#print axioms OpenComm.User.exact_defn_lawHooks
