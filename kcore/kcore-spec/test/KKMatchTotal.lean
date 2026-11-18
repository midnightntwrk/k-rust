/-
  `match` has a value, and finds every substitution a denotation gives
  (`KcoreSpec/KKMatchTotal.lean`). Run from the package root: `lake env lean test/KKMatchTotal.lean`.
-/
import KcoreSpec.KKMatchTotal

set_option autoImplicit false

namespace KCore.KK.TestMatchTotal

open KCore KCore.KK

#check @ArT
#check @matchF_isSome_kct
#check @matchTsF_isSome_kct
#check @matchColF_isSome_kct
#check @patArity
#check @valArity
#check @arity_agree_kct
#check @arT_enc_kct
#check @patAr_kct
#check @matchF_total
#check @matchTsF_total
#check @matchF_of_den
#check @bindOfSubst
#check @bindAgree_iff_ext
#check @varsIn_kct
#check @matchF_complete_of_den

/-- The one source of no value, `matchTs` at two lengths, is outside `matchF_isSome_kct`: no two
arity tables that agree allow `ap 7` at one argument in the pattern and at none in the subject. -/
example {Ap Av : Int → Nat → Prop} (hA : ∀ f n m, Ap f n → Av f m → n = m) :
    ¬ (ArT Ap (.ap 7 [.vr 0]) ∧ ArT Av (.ap 7 [])) := by
  rintro ⟨hp, ha⟩
  cases hp with
  | ap hf _ => cases ha with
    | ap hg _ => exact absurd (hA _ _ _ hf hg) (by decide)

example : matchF [] (.ap 7 [.vr 0]) (.ap 7 []) [] = none := by
  rw [matchF_ap_ap]; simp only [↓reduceIte]; exact matchTsF_cons_nil [] _ _ _

/-- A set pattern with an element whose key is unbound matches each element: two substitutions. -/
example : matchF [] (.cb .set 3 [.el (.vr 0), .vr 1]) (.co .set 3 [.el (.iv 1), .el (.iv 2)]) [] =
    some [[(1, .co .set 3 [.el (.iv 2)]), (0, .iv 1)], [(1, .co .set 3 [.el (.iv 1)]), (0, .iv 2)]] := by
  simp [matchF_cb_co, matchColF.eq_def, chooseF_cons, chooseF_nil, matchF_el_el, matchF_vr,
    restF_cons, restF_nil, bindVarF, lookF, isElemT]

#print axioms matchF_isSome_kct
#print axioms matchColF_isSome_kct
#print axioms arT_enc_kct
#print axioms patAr_kct
#print axioms matchF_total
#print axioms matchTsF_total
#print axioms matchF_of_den
#print axioms matchColF_of_den_kct
#print axioms bindAgree_iff_ext
#print axioms varsIn_kct
#print axioms matchF_complete_of_den

end KCore.KK.TestMatchTotal
