import ImpNI.Proof

/-! Hand-written. `kimp_noninterference` is not vacuous: at a labelling with one high and one low
identifier the checker accepts a program whose high branch writes only the high identifier,
rejects an explicit flow, an implicit flow through `if` and one through `while`, and the empty
stores are low-equal. The checker's functions are defined by well-founded recursion, which the
kernel does not reduce, so its verdicts are computed through the inversion lemmas of
`Levels.lean`. -/

namespace ImpNI.Examples

open KPrelude

def h : KImp.SortId := ⟨"h"⟩
def l : KImp.SortId := ⟨"l"⟩

/-- `h` is high, `l` is low. -/
def G0 : Lab :=
  MapHook.update (MapHook.update MapHook.unit (KImpSec.SortKItem.inj_Id (tr_SortId h))
    (KImpSec.SortKItem.inj_Level .hi)) (KImpSec.SortKItem.inj_Id (tr_SortId l))
    (KImpSec.SortKItem.inj_Level .lo)

def var (X : KImp.SortId) : KImp.SortExpr := .inj_Id X
def num (n : Int) : KImp.SortExpr := .inj_Int n

/-- `l = 1; h = l + 1; if (h > 0) h = 2;` -/
def ok : KImp.SortStmt :=
  .__ (.«_=_;» l (num 1)) (.__ (.«_=_;» h (.inj_Expr (.«_+_» (var l) (num 1))))
    (.«if(_)_» (.inj_Expr (.«_>_» (var h) (num 0))) (.«_=_;» h (num 2))))

/-- `l = h;` -/
def explicitFlow : KImp.SortStmt := .«_=_;» l (var h)

/-- `if (h > 0) l = 1;` -/
def ifFlow : KImp.SortStmt := .«if(_)_» (.inj_Expr (.«_>_» (var h) (num 0))) (.«_=_;» l (num 1))

/-- `while (h > 0) { l = 1; h = 0; }` -/
def whileFlow : KImp.SortStmt := .«while(_)_» (.inj_Expr (.«_>_» (var h) (num 0)))
  (.«{_}» (.__ (.«_=_;» l (num 1)) (.«_=_;» h (num 0))))

theorem levId_h : levId G0 h = some .hi := by decide
theorem levId_l : levId G0 l = some .lo := by decide

/-- Compute the checker's verdict on a closed program by its inversion lemmas. -/
macro "k2l_sec_eval" : tactic => `(tactic| (
  simp only [ok, explicitFlow, ifFlow, whileFlow, var, num, sec_seq, sec_assign, sec_if, sec_while,
    sec_block, conf_seq, conf_assign, conf_block, conf_if, lev_id, lev_int, lev_bin_0, lev_bin_1,
    lev_bin_2, lev_bin_3, lev_bin_4, lev_bin_5, lev_bin_6, lev_bin_7, lev_bin_8, lev_bin_9,
    lev_bin_10, lev_bin_11, join, levId_h, levId_l] <;> decide))

set_option linter.unusedSimpArgs false in
theorem secure_ok : secure G0 ok := by change sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_explicitFlow : ¬ secure G0 explicitFlow := by
  change ¬ sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_ifFlow : ¬ secure G0 ifFlow := by change ¬ sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_whileFlow : ¬ secure G0 whileFlow := by
  change ¬ sec G0 _ = some true; k2l_sec_eval

theorem good_unit : Good (MapHook.unit : KImp.SortMap) := by
  refine ⟨MapHook.wf_unit, fun X v hv => ?_⟩
  rw [MapHook.lookup, MapRepr.lookupR_eq, MapHook.unit, ListIso.toList_ofList] at hv
  cases hv

/-- The hypotheses of `kimp_noninterference` hold of some programs and stores, and `secure` rejects
the three classic leaks. -/
theorem nonvacuous : secure G0 ok ∧ ¬ secure G0 explicitFlow ∧ ¬ secure G0 ifFlow ∧
    ¬ secure G0 whileFlow ∧ lowEq G0 MapHook.unit MapHook.unit :=
  ⟨secure_ok, not_secure_explicitFlow, not_secure_ifFlow, not_secure_whileFlow,
    good_unit, good_unit, fun _ _ => rfl⟩

#k2l_assert_axioms nonvacuous

end ImpNI.Examples
