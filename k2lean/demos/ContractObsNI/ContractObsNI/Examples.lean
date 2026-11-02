import ContractObsNI.Proof

/-! Hand-written. `contract_noninterference` here is plain noninterference, the disclosed values
observed with the ledger and the transcript, and it is not vacuous: at a labelling with one high
local `h` and one low local `l`, the checker that releases nothing accepts a contract that branches
on a private value writing only `h` and discloses a public one, and rejects `demos/ContractNI`'s
accepted contract, whose branch on a disclosed condition on a private value is a release, and the
disclosure of a private value. The checker's verdicts are computed through the inversion lemmas of
`Levels.lean`, as in `demos/ContractNI`. -/

namespace ContractObsNI.Examples

open KPrelude

def h : Contract.SortId := ⟨"h"⟩
def l : Contract.SortId := ⟨"l"⟩
def x : Contract.SortId := ⟨"x"⟩

/-- `h` is high, `l` is low. -/
def G0 : Lab :=
  MapHook.update (MapHook.update MapHook.unit (ContractSecNR.SortKItem.inj_Id (tr_SortId h))
    (ContractSecNR.SortKItem.inj_Level .hi)) (ContractSecNR.SortKItem.inj_Id (tr_SortId l))
    (ContractSecNR.SortKItem.inj_Level .lo)

def var (X : Contract.SortId) : Contract.SortExpr := .inj_Id X
def num (n : Int) : Contract.SortExpr := .inj_Int n
def wit : Contract.SortExpr := .inj_Expr .«witness()»
def rd (X : Contract.SortId) : Contract.SortExpr := .inj_Expr (.«read(_)» X)
def disc (e : Contract.SortExpr) : Contract.SortExpr := .inj_Expr (.«disclose(_)» e)
def lt (a b : Contract.SortExpr) : Contract.SortExpr := .inj_Expr (.«_<_» a b)
def plus (a b : Contract.SortExpr) : Contract.SortExpr := .inj_Expr (.«_+_» a b)

/-- `h = witness(); if (h < 5) { h = 1; } else { } emit(disclose(1));` -/
def ok : Contract.SortStmt :=
  .__ (.«_=_;» h wit) (.__ (.«if(_)_else_» (lt (var h) (num 5)) (.«{_}» (.«_=_;» h (num 1))) .«{}»)
    (.«emit(_);» (disc (num 1))))

/-- `demos/ContractNI`'s accepted contract:
`h = witness(); if (disclose(h < 5)) { write(x, read(x) + 1); } else { } emit(1);` -/
def released : Contract.SortStmt :=
  .__ (.«_=_;» h wit) (.__ (.«if(_)_else_» (disc (lt (var h) (num 5)))
    (.«{_}» (.«write(_,_);» x (plus (rd x) (num 1)))) .«{}») (.«emit(_);» (num 1)))

/-- `emit(disclose(witness()));` -/
def discloseFlow : Contract.SortStmt := .«emit(_);» (disc wit)

theorem levId_h : levId G0 h = some .hi := by decide
theorem levId_l : levId G0 l = some .lo := by decide

/-- Compute the checker's verdict on a closed program by its inversion lemmas. -/
local macro "k2l_sec_eval" : tactic => `(tactic| (
  simp only [ok, released, discloseFlow, var, num, wit, rd, disc, lt, plus,
    sec.__, sec.«_=_;», sec.«write(_,_);», sec.«emit(_);», sec.«if(_)_else_», sec.«{_}», sec.«{}»,
    conf.__, conf.«_=_;», conf.«{_}», conf.«{}», conf.«emit(_);», conf.«write(_,_);»,
    lev_id, lev.inj_Int, lev.«witness()», lev.«read(_)», lev.«disclose(_)», lev.«_+_», lev.«_<_»,
    quiet.inj_Int, quiet.inj_Id, quiet.«witness()», quiet.«read(_)», quiet.«disclose(_)»,
    quiet.«_+_», quiet.«_<_»,
    ContractSecNR.K.«join(_,_)_CONTRACTSEC_Level_Level_Level»,
    ContractSecNR.K.«join(_,_)_CONTRACTSEC_Level_Level_Level».rule1,
    ContractSecNR.K.«join(_,_)_CONTRACTSEC_Level_Level_Level».rule2, levId_h, levId_l] <;> decide))

set_option linter.unusedSimpArgs false in
theorem secure_ok : secure G0 ok := by change sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_released : ¬ secure G0 released := by
  change ¬ sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_discloseFlow : ¬ secure G0 discloseFlow := by
  change ¬ sec G0 _ = some true; k2l_sec_eval

/-- The hypotheses of `contract_noninterference` hold of some program, and `secure` rejects the
two releases. -/
theorem nonvacuous : secure G0 ok ∧ ¬ secure G0 released ∧ ¬ secure G0 discloseFlow :=
  ⟨secure_ok, not_secure_released, not_secure_discloseFlow⟩

#k2l_assert_axioms nonvacuous

end ContractObsNI.Examples
