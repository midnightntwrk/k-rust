import ContractValsNI.Proof
import KPrelude.TwoRuns
import ContractVals.Adequacy

/-! Hand-written. `contractvals_noninterference` is not vacuous, and the checker's rejections are not
either. At a labelling with one high local `h` and one low local `l`, the checker accepts a
contract that branches on a disclosed condition on a private value, and rejects three leaks: an
explicit flow to the ledger, an implicit flow through `emit` under a private branch, and a ledger
read under a private branch. The explicit flow is refuted by two runs: from one ledger and two
private inputs, both runs end, disclose nothing, and leave different ledgers and transcripts. The
checker's verdicts are computed through the inversion lemmas of `Levels.lean`, since its functions
are defined by well-founded recursion, which the kernel does not reduce. -/

namespace ContractValsNI.Examples

open KPrelude KPrelude.TwoRuns

def h : ContractVals.SortId := ⟨"h"⟩
def l : ContractVals.SortId := ⟨"l"⟩
def x : ContractVals.SortId := ⟨"x"⟩

/-- `h` is high, `l` is low. -/
def G0 : Lab :=
  MapHook.update (MapHook.update MapHook.unit (ContractSec.SortKItem.inj_Id (tr_SortId h))
    (ContractSec.SortKItem.inj_Level .hi)) (ContractSec.SortKItem.inj_Id (tr_SortId l))
    (ContractSec.SortKItem.inj_Level .lo)

def var (X : ContractVals.SortId) : ContractVals.SortExpr := .inj_Id X
def num (n : Int) : ContractVals.SortExpr := .inj_Int n
def wit : ContractVals.SortExpr := .inj_Expr .«witness()»
def rd (X : ContractVals.SortId) : ContractVals.SortExpr := .inj_Expr (.«read(_)» X)
def disc (e : ContractVals.SortExpr) : ContractVals.SortExpr := .inj_Expr (.«disclose(_)» e)
def lt (a b : ContractVals.SortExpr) : ContractVals.SortExpr := .inj_Expr (.«_<_» a b)
def plus (a b : ContractVals.SortExpr) : ContractVals.SortExpr := .inj_Expr (.«_+_» a b)

/-- `h = witness(); if (disclose(h < 5)) { write(x, read(x) + 1); } else { } emit(1);` -/
def ok : ContractVals.SortStmt :=
  .__ (.«_=_;» h wit) (.__ (.«if(_)_else_» (disc (lt (var h) (num 5)))
    (.«{_}» (.«write(_,_);» x (plus (rd x) (num 1)))) .«{}») (.«emit(_);» (num 1)))

/-- `write(x, witness());` -/
def explicitFlow : ContractVals.SortStmt := .«write(_,_);» x wit

/-- `h = witness(); if (h < 5) { emit(1); } else { }` -/
def implicitFlow : ContractVals.SortStmt :=
  .__ (.«_=_;» h wit) (.«if(_)_else_» (lt (var h) (num 5)) (.«{_}» (.«emit(_);» (num 1))) .«{}»)

/-- `h = witness(); if (h < 5) { h = read(x); } else { }` -/
def loudBranch : ContractVals.SortStmt :=
  .__ (.«_=_;» h wit) (.«if(_)_else_» (lt (var h) (num 5)) (.«{_}» (.«_=_;» h (rd x))) .«{}»)

theorem levId_h : levId G0 h = some .hi := by decide
theorem levId_l : levId G0 l = some .lo := by decide

/-- Compute the checker's verdict on a closed program by its inversion lemmas. -/
local macro "k2l_sec_eval" : tactic => `(tactic| (
  simp only [ok, explicitFlow, implicitFlow, loudBranch, var, num, wit, rd, disc, lt, plus,
    sec.__, sec.«_=_;», sec.«write(_,_);», sec.«emit(_);», sec.«if(_)_else_», sec.«{_}», sec.«{}»,
    conf.__, conf.«_=_;», conf.«{_}», conf.«{}», conf.«emit(_);», conf.«write(_,_);»,
    lev_id, lev.inj_Int, lev.«witness()», lev.«read(_)», lev.«disclose(_)», lev.«_+_», lev.«_<_»,
    quiet.inj_Int, quiet.inj_Id, quiet.«witness()», quiet.«read(_)», quiet.«disclose(_)»,
    quiet.«_+_», quiet.«_<_»,
    ContractSec.K.«join(_,_)_CONTRACTSEC_Level_Level_Level»,
    ContractSec.K.«join(_,_)_CONTRACTSEC_Level_Level_Level».rule1,
    ContractSec.K.«join(_,_)_CONTRACTSEC_Level_Level_Level».rule2, levId_h, levId_l] <;> decide))

set_option linter.unusedSimpArgs false in
theorem secure_ok : secure G0 ok := by change sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_explicitFlow : ¬ secure G0 explicitFlow := by
  change ¬ sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_implicitFlow : ¬ secure G0 implicitFlow := by
  change ¬ sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_loudBranch : ¬ secure G0 loudBranch := by
  change ¬ sec G0 _ = some true; k2l_sec_eval

/-- The final configurations, as a test. -/
def fin (c : ContractVals.SortGeneratedTopCell) : Bool := decide (kOf c = .dotk)

/-- The theorem, for the accepted contract, in the form two runs refute. -/
theorem ok_agrees (L : ContractVals.SortMap) (W₁ W₂ : ContractVals.SortList) :
    AgreeFrom ContractVals.Step fin discOf pubOf (ContractVals.init ok L W₁) (ContractVals.init ok L W₂) :=
  fun h₁ hf₁ h₂ hf₂ hd =>
    contractvals_noninterference (G := G0) secure_ok h₁ (of_decide_eq_true hf₁ : kOf _ = .dotk) h₂
      (of_decide_eq_true hf₂ : kOf _ = .dotk) hd

/-- One private answer. -/
def answer (n : Int) : ContractVals.SortList := ListHook.element (ContractVals.SortKItem.inj_Int n)

/-- The explicit flow leaks: from the empty ledger and the private answers `1` and `2`, both runs
end, disclose nothing, and write different values. -/
theorem explicitFlow_leaks :
    ¬ AgreeFrom ContractVals.Step fin discOf pubOf (ContractVals.init explicitFlow MapHook.unit (answer 1))
      (ContractVals.init explicitFlow MapHook.unit (answer 2)) :=
  refute_from_runs (next := KPrelude.successors ContractVals.rules)
    (fun _ _ h => ContractVals.successors_iff.mp h) (List.replicate 4 0) (List.replicate 4 0)
    (by decide +kernel)

/-- The hypotheses of `contractvals_noninterference` hold of a contract that uses private data, and
`secure` rejects three leaks, one of which two runs refute. -/
theorem nonvacuous : secure G0 ok ∧ ¬ secure G0 explicitFlow ∧ ¬ secure G0 implicitFlow ∧
    ¬ secure G0 loudBranch ∧
    ¬ AgreeFrom ContractVals.Step fin discOf pubOf (ContractVals.init explicitFlow MapHook.unit (answer 1))
      (ContractVals.init explicitFlow MapHook.unit (answer 2)) :=
  ⟨secure_ok, not_secure_explicitFlow, not_secure_implicitFlow, not_secure_loudBranch,
    explicitFlow_leaks⟩

#k2l_assert_axioms ok_agrees nonvacuous

end ContractValsNI.Examples
