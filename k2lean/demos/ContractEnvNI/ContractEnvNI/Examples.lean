import ContractEnvNI.Proof
import KPrelude.TwoRuns
import ContractEnv.Adequacy

/-! Hand-written. `contractenv_noninterference` is not vacuous, and the checker's rejections are not
either. At a labelling with one high local `h` and one low local `l`, the checker accepts a
contract that branches on a disclosed condition on a private value and one that emits `l` from the
initial store, and rejects four leaks: an explicit flow to the ledger, an implicit flow through
`emit` under a private branch, a ledger read under a private branch, and the emission of `h` from
the initial store. Two are refuted by two runs: the explicit flow from one ledger and two private
inputs, and the emission of `h` from two initial stores that differ at `h` only (low-equal, the
statement's premise); both runs end, disclose nothing, and leave different transcripts. The
checker's verdicts are computed through the inversion lemmas of `Levels.lean`, since its functions
are defined by well-founded recursion, which the kernel does not reduce. -/

namespace ContractEnvNI.Examples

open KPrelude KPrelude.TwoRuns

def h : ContractEnv.SortId := ⟨"h"⟩
def l : ContractEnv.SortId := ⟨"l"⟩
def x : ContractEnv.SortId := ⟨"x"⟩

/-- `h` is high, `l` is low. -/
def G0 : Lab :=
  MapHook.update (MapHook.update MapHook.unit (ContractSec.SortKItem.inj_Id (tr_SortId h))
    (ContractSec.SortKItem.inj_Level .hi)) (ContractSec.SortKItem.inj_Id (tr_SortId l))
    (ContractSec.SortKItem.inj_Level .lo)

def var (X : ContractEnv.SortId) : ContractEnv.SortExpr := .inj_Id X
def num (n : Int) : ContractEnv.SortExpr := .inj_Int n
def wit : ContractEnv.SortExpr := .inj_Expr .«witness()»
def rd (X : ContractEnv.SortId) : ContractEnv.SortExpr := .inj_Expr (.«read(_)» X)
def disc (e : ContractEnv.SortExpr) : ContractEnv.SortExpr := .inj_Expr (.«disclose(_)» e)
def lt (a b : ContractEnv.SortExpr) : ContractEnv.SortExpr := .inj_Expr (.«_<_» a b)
def plus (a b : ContractEnv.SortExpr) : ContractEnv.SortExpr := .inj_Expr (.«_+_» a b)

/-- `h = witness(); if (disclose(h < 5)) { write(x, read(x) + 1); } else { } emit(1);` -/
def ok : ContractEnv.SortStmt :=
  .__ (.«_=_;» h wit) (.__ (.«if(_)_else_» (disc (lt (var h) (num 5)))
    (.«{_}» (.«write(_,_);» x (plus (rd x) (num 1)))) .«{}») (.«emit(_);» (num 1)))

/-- `emit(l);` -/
def emitL : ContractEnv.SortStmt := .«emit(_);» (var l)

/-- `emit(h);` -/
def emitH : ContractEnv.SortStmt := .«emit(_);» (var h)

/-- `write(x, witness());` -/
def explicitFlow : ContractEnv.SortStmt := .«write(_,_);» x wit

/-- `h = witness(); if (h < 5) { emit(1); } else { }` -/
def implicitFlow : ContractEnv.SortStmt :=
  .__ (.«_=_;» h wit) (.«if(_)_else_» (lt (var h) (num 5)) (.«{_}» (.«emit(_);» (num 1))) .«{}»)

/-- `h = witness(); if (h < 5) { h = read(x); } else { }` -/
def loudBranch : ContractEnv.SortStmt :=
  .__ (.«_=_;» h wit) (.«if(_)_else_» (lt (var h) (num 5)) (.«{_}» (.«_=_;» h (rd x))) .«{}»)

theorem levId_h : levId G0 h = some .hi := by decide
theorem levId_l : levId G0 l = some .lo := by decide

/-- Compute the checker's verdict on a closed program by its inversion lemmas. -/
local macro "k2l_sec_eval" : tactic => `(tactic| (
  simp only [ok, emitL, emitH, explicitFlow, implicitFlow, loudBranch, var, num, wit, rd, disc, lt, plus,
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
theorem secure_emitL : secure G0 emitL := by change sec G0 _ = some true; k2l_sec_eval
set_option linter.unusedSimpArgs false in
theorem not_secure_emitH : ¬ secure G0 emitH := by change ¬ sec G0 _ = some true; k2l_sec_eval
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
def fin (c : ContractEnv.SortGeneratedTopCell) : Bool := decide (kOf c = .dotk)

/-- The theorem, for the accepted contracts, in the form two runs refute: from low-equal initial
stores, one ledger and any private inputs. -/
theorem agrees {P : ContractEnv.SortStmt} (hP : secure G0 P) {E₁ E₂ : ContractEnv.SortMap}
    (hE : lowEq G0 E₁ E₂) (L : ContractEnv.SortMap) (W₁ W₂ : ContractEnv.SortList) :
    AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init P E₁ L W₁) (ContractEnv.init P E₂ L W₂) :=
  fun h₁ hf₁ h₂ hf₂ hd =>
    (contractenv_noninterference (G := G0) hP hE h₁ (of_decide_eq_true hf₁ : kOf _ = .dotk) h₂
      (of_decide_eq_true hf₂ : kOf _ = .dotk) hd).2

theorem ok_agrees {E₁ E₂ : ContractEnv.SortMap} (hE : lowEq G0 E₁ E₂) (L : ContractEnv.SortMap)
    (W₁ W₂ : ContractEnv.SortList) :
    AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init ok E₁ L W₁) (ContractEnv.init ok E₂ L W₂) :=
  agrees secure_ok hE L W₁ W₂

theorem emitL_agrees {E₁ E₂ : ContractEnv.SortMap} (hE : lowEq G0 E₁ E₂) (L : ContractEnv.SortMap)
    (W₁ W₂ : ContractEnv.SortList) :
    AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init emitL E₁ L W₁)
      (ContractEnv.init emitL E₂ L W₂) :=
  agrees secure_emitL hE L W₁ W₂

/-- One private answer. -/
def answer (n : Int) : ContractEnv.SortList := ListHook.element (ContractEnv.SortKItem.inj_Int n)

/-- The explicit flow leaks: from the empty ledger and the private answers `1` and `2`, both runs
end, disclose nothing, and write different values. -/
theorem explicitFlow_leaks :
    ¬ AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init explicitFlow MapHook.unit MapHook.unit (answer 1))
      (ContractEnv.init explicitFlow MapHook.unit MapHook.unit (answer 2)) :=
  refute_from_runs (next := KPrelude.successors ContractEnv.rules)
    (fun _ _ h => ContractEnv.successors_iff.mp h) (List.replicate 4 0) (List.replicate 4 0)
    (by decide +kernel)

/-- An initial store binding `h` to `n` and `l` to `0`: two of them, at different `n`, are low-equal. -/
def envAt (n : Int) : ContractEnv.SortMap :=
  MapHook.update (MapHook.update MapHook.unit (ContractEnv.SortKItem.inj_Id h)
    (ContractEnv.inj_Value_KItem (.inj_Int n))) (ContractEnv.SortKItem.inj_Id l)
    (ContractEnv.inj_Value_KItem (.inj_Int 0))

/-- The two initial stores are low-equal: each is a store, and they agree at every low identifier,
`h` being high. -/
theorem envAt_lowEq : lowEq G0 (envAt 1) (envAt 2) := by
  have good (n : Int) : Good (envAt n) :=
    (good_unit.update (test_inj_Value h _)).update (test_inj_Value l _)
  refine ⟨good 1, good 2, fun X hX => ?_⟩
  by_cases hh : X = h
  · subst hh; exact absurd hX (not_low_of_lev (by rw [lev_id]; exact levId_h))
  by_cases hl : X = l
  · subst hl; simp only [envAt, MapHook.lookup_update_self]
  have ne : ∀ {Y : ContractEnv.SortId}, X ≠ Y →
      ContractEnv.SortKItem.inj_Id X ≠ ContractEnv.SortKItem.inj_Id Y := fun hne e =>
    hne (Option.some.inj (congrArg ContractEnv.proj_KItem_Id e))
  simp only [envAt, MapHook.lookup_update_ne _ _ (ne hl), MapHook.lookup_update_ne _ _ (ne hh)]

/-- The emission of `h` leaks: from initial stores that differ at `h` only, one ledger and one
private answer, both runs end, disclose nothing, and emit different values. -/
theorem emitH_leaks :
    ¬ AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init emitH (envAt 1) MapHook.unit (answer 1))
      (ContractEnv.init emitH (envAt 2) MapHook.unit (answer 1)) :=
  refute_from_runs (next := KPrelude.successors ContractEnv.rules)
    (fun _ _ h => ContractEnv.successors_iff.mp h) (List.replicate 4 0) (List.replicate 4 0)
    (by decide +kernel)

/-- The hypotheses of `contractenv_noninterference` hold of a contract that uses private data and
of one that reads the initial store, and `secure` rejects four leaks, two of which two runs
refute. -/
theorem nonvacuous : secure G0 ok ∧ secure G0 emitL ∧ ¬ secure G0 explicitFlow ∧
    ¬ secure G0 implicitFlow ∧ ¬ secure G0 loudBranch ∧ ¬ secure G0 emitH ∧
    lowEq G0 (envAt 1) (envAt 2) ∧
    ¬ AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init emitH (envAt 1) MapHook.unit (answer 1))
      (ContractEnv.init emitH (envAt 2) MapHook.unit (answer 1)) ∧
    ¬ AgreeFrom ContractEnv.Step fin discOf pubOf (ContractEnv.init explicitFlow MapHook.unit MapHook.unit (answer 1))
      (ContractEnv.init explicitFlow MapHook.unit MapHook.unit (answer 2)) :=
  ⟨secure_ok, secure_emitL, not_secure_explicitFlow, not_secure_implicitFlow, not_secure_loudBranch,
    not_secure_emitH, envAt_lowEq, emitH_leaks, explicitFlow_leaks⟩

#k2l_assert_axioms ok_agrees emitL_agrees nonvacuous

end ContractEnvNI.Examples
