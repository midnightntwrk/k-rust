import ImpNI.Hand
import KPrelude.Soundness
import KPrelude.Tactic

/-! Hand-written. The security checker's functions `lev`, `sec`, `conf` (`k/imp-sec.k`) at kimp's
terms, through the translation `tr` (`Tr.lean`), and one inversion lemma per checker equation:
what the checker computes on each constructor, in terms of the components. -/

namespace ImpNI

open KPrelude

abbrev Lvl := KImpSec.SortLevel
abbrev Lab := KImpSec.SortMap

/-- The level of an expression. -/
def lev (G : Lab) (x : KImp.SortExpr) : Option Lvl :=
  KImpSec.K.«lev(_,_)_IMP-SEC_Level_Expr_Map» (tr_SortExpr x) G
/-- The checker accepts a statement at a low program counter. -/
def sec (G : Lab) (x : KImp.SortStmt) : Option Bool :=
  KImpSec.K.«sec(_,_)_IMP-SEC_Bool_Stmt_Map» (tr_SortStmt x) G
/-- A statement is confined: it assigns only high identifiers. -/
def conf (G : Lab) (x : KImp.SortStmt) : Option Bool :=
  KImpSec.K.«conf(_,_)_IMP-SEC_Bool_Stmt_Map» (tr_SortStmt x) G

/-- The join of two levels (the checker's `join`, which is total). -/
def join : Lvl → Lvl → Lvl
  | .lo, l => l
  | .hi, _ => .hi

/-- Unfold the checker's function once at the left-hand side, case on the values of the calls, and
compute. -/
macro "k2l_lev_inv" : tactic => `(tactic| (
  simp only [lev, sec, conf, tr_SortExpr, tr_SortExpr_Own, tr_SortStmt]
  first
    | (conv => lhs; rw [KImpSec.K.«lev(_,_)_IMP-SEC_Level_Expr_Map».eq_def])
    | (conv => lhs; rw [KImpSec.K.«sec(_,_)_IMP-SEC_Bool_Stmt_Map».eq_def])
    | (conv => lhs; rw [KImpSec.K.«conf(_,_)_IMP-SEC_Bool_Stmt_Map».eq_def])
  try simp only []
  try k2l_cases_apps [KImpSec.K.«lev(_,_)_IMP-SEC_Level_Expr_Map», KImpSec.K.«sec(_,_)_IMP-SEC_Bool_Stmt_Map», KImpSec.K.«conf(_,_)_IMP-SEC_Bool_Stmt_Map»]
  all_goals simp_all [KEqHook.eq, BoolHook.and, BoolHook.or, join, KImpSec.K.«join(_,_)_IMP-SEC_Level_Level_Level», KImpSec.K.«join(_,_)_IMP-SEC_Level_Level_Level».rule1, KImpSec.K.«join(_,_)_IMP-SEC_Level_Level_Level».rule2]))

/-- The level of an identifier: its label. -/
def levId (G : Lab) (X : KImp.SortId) : Option Lvl :=
  if MapHook.wfb G = true then
    match MapHook.lookup G (KImpSec.SortKItem.inj_Id (tr_SortId X)) with
    | some (KImpSec.SortKItem.inj_Level L) => some L
    | _ => none
  else none

theorem lev_int (G : Lab) (n : KImp.SortInt) : lev G (.inj_Int n) = some .lo := by k2l_lev_inv
theorem lev_bool (G : Lab) (b : KImp.SortBool) : lev G (.inj_Bool b) = some .lo := by k2l_lev_inv
theorem lev_id (G : Lab) (X : KImp.SortId) : lev G (.inj_Id X) = levId G X := by
  simp only [lev, levId, tr_SortExpr]
  rw [KImpSec.K.«lev(_,_)_IMP-SEC_Level_Expr_Map».eq_def]
  simp only []
  by_cases hw : MapHook.wfb G = true
  · simp only [hw, dite_true, ite_true]
    split <;> rename_i hl <;> split at hl <;> rename_i hlk <;> (try split at hl) <;> simp_all
  · simp [hw]
theorem lev_neg (G : Lab) (E : KImp.SortExpr) :
    lev G (.inj_Expr (.«-_» E)) = lev G E := by k2l_lev_inv
theorem lev_not (G : Lab) (E : KImp.SortExpr) :
    lev G (.inj_Expr (.«!_» E)) = lev G E := by k2l_lev_inv

theorem lev_bin_0 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_+_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_1 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_-_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_2 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_*_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_3 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_/_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_4 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_>=_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_5 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_>_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_6 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_<=_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_7 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_<_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_8 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_==_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_9 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_!=_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_10 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_&&_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem lev_bin_11 (G : Lab) (E1 E2 : KImp.SortExpr) :
    lev G (.inj_Expr (.«_||_» E1 E2)) =
      match lev G E1, lev G E2 with
      | some a, some b => some (join a b)
      | _, _ => none := by k2l_lev_inv
theorem sec_empty (G : Lab) : sec G .«{}» = some true := by k2l_lev_inv
theorem sec_block (G : Lab) (S : KImp.SortStmt) : sec G (.«{_}» S) = sec G S := by k2l_lev_inv
theorem sec_seq (G : Lab) (S1 S2 : KImp.SortStmt) :
    sec G (.__ S1 S2) =
      match sec G S1, sec G S2 with
      | some a, some b => some (a && b)
      | _, _ => none := by k2l_lev_inv
theorem sec_assign (G : Lab) (X : KImp.SortId) (E : KImp.SortExpr) :
    sec G (.«_=_;» X E) =
      match lev G (.inj_Id X), lev G E with
      | some a, some b => if a = .hi ∨ b = .lo then some true else some false
      | _, _ => some false := by k2l_lev_inv
theorem sec_ifelse (G : Lab) (C : KImp.SortExpr) (S1 S2 : KImp.SortStmt) :
    sec G (.«if(_)_else_» C S1 S2) =
      match lev G C with
      | some .lo => (match sec G S1, sec G S2 with
          | some a, some b => some (a && b)
          | _, _ => none)
      | some .hi => (match conf G S1, conf G S2 with
          | some a, some b => some (a && b)
          | _, _ => none)
      | none => some false := by k2l_lev_inv
theorem sec_if (G : Lab) (C : KImp.SortExpr) (S : KImp.SortStmt) :
    sec G (.«if(_)_» C S) =
      match lev G C with
      | some .lo => sec G S
      | some .hi => conf G S
      | none => some false := by k2l_lev_inv
theorem sec_while (G : Lab) (C : KImp.SortExpr) (S : KImp.SortStmt) :
    sec G (.«while(_)_» C S) =
      match lev G C with
      | some .lo => sec G S
      | some .hi => conf G S
      | none => some false := by k2l_lev_inv
theorem conf_empty (G : Lab) : conf G .«{}» = some true := by k2l_lev_inv
theorem conf_block (G : Lab) (S : KImp.SortStmt) : conf G (.«{_}» S) = conf G S := by k2l_lev_inv
theorem conf_seq (G : Lab) (S1 S2 : KImp.SortStmt) :
    conf G (.__ S1 S2) =
      match conf G S1, conf G S2 with
      | some a, some b => some (a && b)
      | _, _ => none := by k2l_lev_inv
theorem conf_assign (G : Lab) (X : KImp.SortId) (E : KImp.SortExpr) :
    conf G (.«_=_;» X E) =
      match lev G (.inj_Id X) with
      | some l => some (l == .hi)
      | none => none := by k2l_lev_inv
theorem conf_ifelse (G : Lab) (C : KImp.SortExpr) (S1 S2 : KImp.SortStmt) :
    conf G (.«if(_)_else_» C S1 S2) =
      match conf G S1, conf G S2 with
      | some a, some b => some (a && b)
      | _, _ => none := by k2l_lev_inv
theorem conf_if (G : Lab) (C : KImp.SortExpr) (S : KImp.SortStmt) :
    conf G (.«if(_)_» C S) = conf G S := by k2l_lev_inv
theorem conf_while (G : Lab) (C : KImp.SortExpr) (S : KImp.SortStmt) :
    conf G (.«while(_)_» C S) = conf G S := by k2l_lev_inv

end ImpNI
