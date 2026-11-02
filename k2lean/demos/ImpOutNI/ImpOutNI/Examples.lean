import ImpOutNI.Proof

/-! Hand-written. `kimpoutni_noninterference` is not vacuous, and its observation of the output is
not either: at a labelling with one high and one low identifier the checker accepts a program that
prints a low value and branches on the high identifier writing only it, and rejects an explicit
flow to the output (`print(h);`) and an implicit one (`if (h > 0) print(1);`), which the store's
low-equality alone would not see; the empty stores are low-equal. The checker's verdicts are
computed through the inversion lemmas of `Levels.lean` (generated, `lev_id` among them),
as in `demos/ImpNI`. -/

namespace ImpOutNI.Examples

open KPrelude

def h : KImpOutNI.SortId := ⟨"h"⟩
def l : KImpOutNI.SortId := ⟨"l"⟩

/-- `h` is high, `l` is low. -/
def G0 : Lab :=
  MapHook.update (MapHook.update MapHook.unit (KImpSecP.SortKItem.inj_Id (tr_SortId h))
    (KImpSecP.SortKItem.inj_Level .hi)) (KImpSecP.SortKItem.inj_Id (tr_SortId l))
    (KImpSecP.SortKItem.inj_Level .lo)

def var (X : KImpOutNI.SortId) : KImpOutNI.SortExpr := .inj_Id X
def num (n : Int) : KImpOutNI.SortExpr := .inj_Int n

/-- `l = 1; print(l + 1); if (h > 0) h = 2;` -/
def ok : KImpOutNI.SortStmt :=
  .__ (.«_=_;» l (num 1)) (.__ (.«print(_);» (.inj_Expr (.«_+_» (var l) (num 1))))
    (.«if(_)_» (.inj_Expr (.«_>_» (var h) (num 0))) (.«_=_;» h (num 2))))

/-- `print(h);` -/
def explicitFlow : KImpOutNI.SortStmt := .«print(_);» (var h)

/-- `if (h > 0) print(1);` -/
def ifFlow : KImpOutNI.SortStmt :=
  .«if(_)_» (.inj_Expr (.«_>_» (var h) (num 0))) (.«print(_);» (num 1))

theorem levId_h : levId G0 h = some .hi := by decide
theorem levId_l : levId G0 l = some .lo := by decide

/-- Compute the checker's verdict on a closed program by its inversion lemmas. -/
local macro "k2l_sec_eval" : tactic => `(tactic| (
  simp only [ok, explicitFlow, ifFlow, var, num, sec.__, sec.«_=_;», sec.«if(_)_», sec.«print(_);»,
    conf.«_=_;», conf.«print(_);», lev_id, lev.inj_Int, lev.«_+_», lev.«_>_»,
    KImpSecP.K.«join(_,_)_IMP-SEC_Level_Level_Level»,
    KImpSecP.K.«join(_,_)_IMP-SEC_Level_Level_Level».rule1,
    KImpSecP.K.«join(_,_)_IMP-SEC_Level_Level_Level».rule2, levId_h, levId_l] <;> decide))

set_option linter.unusedSimpArgs false in
theorem secure_ok : secure G0 ok := by change sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_explicitFlow : ¬ secure G0 explicitFlow := by
  change ¬ sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_ifFlow : ¬ secure G0 ifFlow := by change ¬ sec G0 _ = some true; k2l_sec_eval

/-- The hypotheses of `kimpoutni_noninterference` hold of some programs and stores, and `secure`
rejects the two flows to the output. -/
theorem nonvacuous : secure G0 ok ∧ ¬ secure G0 explicitFlow ∧ ¬ secure G0 ifFlow ∧
    lowEq G0 MapHook.unit MapHook.unit :=
  ⟨secure_ok, not_secure_explicitFlow, not_secure_ifFlow, good_unit, good_unit, fun _ _ => rfl⟩

#k2l_assert_axioms nonvacuous

end ImpOutNI.Examples
