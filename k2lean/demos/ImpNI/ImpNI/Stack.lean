import ImpNI.Levels
import KImp.Rules

/-! Hand-written. The two stack typings of kimp's `<k>` that the noninterference relation is
built from, in the style of the runtime typing of `k2lean soundness` (`kty` in
`demos/ImpTypes`): an item leaves `some true` (a pending value), `some false` (nothing: a statement
done) or `none` (rejected), and a freezer is typed by plugging a low value into it (`plug`).
- the low typing `lk`: the items both runs execute in lockstep: low expressions, statements the
  checker accepts at a low program counter (`sec`);
- the confined typing `CK G K`: a stack of items over the common continuation `K` that assign only
  high identifiers (`conf`), with any expression; a run executes it alone. -/

namespace ImpNI

open KPrelude

/-- A low value, plugged into a freezer to type it. -/
def dflt : KImp.SortExpr := .inj_Int 0

open KImp in
/-- The item that cooling makes of `e ~> f`: each case is the right-hand side of `f`'s cooling
rule, with the hole `e`. -/
def plug : KImp.SortKItem.Own → KImp.SortExpr → Option KImp.SortKItem
  | SortKItem.Own.«#freezer!__EXPR-SYNTAX_Expr_Expr0_», HOLE => some (SortKItem.inj_Expr (SortExpr.Own.«!_» HOLE))
  | SortKItem.Own.«#freezer-__EXPR-SYNTAX_Expr_Expr0_», HOLE => some (SortKItem.inj_Expr (SortExpr.Own.«-_» HOLE))
  | SortKItem.Own.«#freezer_!=__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_!=_» HOLE K1))
  | SortKItem.Own.«#freezer_!=__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_!=_» K0 HOLE))
  | SortKItem.Own.«#freezer_&&__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_&&_» HOLE K1))
  | SortKItem.Own.«#freezer_*__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_*_» HOLE K1))
  | SortKItem.Own.«#freezer_*__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_*_» K0 HOLE))
  | SortKItem.Own.«#freezer_+__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_+_» HOLE K1))
  | SortKItem.Own.«#freezer_+__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_+_» K0 HOLE))
  | SortKItem.Own.«#freezer_-__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_-_» HOLE K1))
  | SortKItem.Own.«#freezer_-__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_-_» K0 HOLE))
  | SortKItem.Own.«#freezer_/__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_/_» HOLE K1))
  | SortKItem.Own.«#freezer_/__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_/_» K0 HOLE))
  | SortKItem.Own.«#freezer_<=__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_<=_» HOLE K1))
  | SortKItem.Own.«#freezer_<=__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_<=_» K0 HOLE))
  | SortKItem.Own.«#freezer_<__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_<_» HOLE K1))
  | SortKItem.Own.«#freezer_<__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_<_» K0 HOLE))
  | SortKItem.Own.«#freezer_==__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_==_» HOLE K1))
  | SortKItem.Own.«#freezer_==__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_==_» K0 HOLE))
  | SortKItem.Own.«#freezer_=_;_CALC-SYNTAX_Stmt_Id_Expr1_» (SortK.kseq y1 SortK.dotk), HOLE => (proj_KItem_Id y1).bind fun K0 => some (SortKItem.inj_Stmt (SortStmt.«_=_;» K0 HOLE))
  | SortKItem.Own.«#freezer_>=__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_>=_» HOLE K1))
  | SortKItem.Own.«#freezer_>=__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_>=_» K0 HOLE))
  | SortKItem.Own.«#freezer_>__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_>_» HOLE K1))
  | SortKItem.Own.«#freezer_>__EXPR-SYNTAX_Expr_Expr_Expr1_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K0 => some (SortKItem.inj_Expr (SortExpr.Own.«_>_» K0 HOLE))
  | SortKItem.Own.«#freezer_||__EXPR-SYNTAX_Expr_Expr_Expr0_» (SortK.kseq y_2 SortK.dotk), HOLE => (proj_KItem_Expr y_2).bind fun K1 => some (SortKItem.inj_Expr (SortExpr.Own.«_||_» HOLE K1))
  | SortKItem.Own.«#freezerif(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt0_» (SortK.kseq y1 SortK.dotk) (SortK.kseq y2 SortK.dotk), HOLE => (proj_KItem_Stmt y1).bind fun K1 => (proj_KItem_Stmt y2).bind fun K2 => some (SortKItem.inj_Stmt (SortStmt.«if(_)_else_» HOLE K1 K2))
  | _, _ => none

/-- What an item leaves on the low stack. -/
def litem0 (G : Lab) : KImp.SortKItem → Option Bool
  | .inj_Bool x => if lev G (.inj_Bool x) = some .lo then some true else none
  | .inj_Expr x => if lev G (.inj_Expr x) = some .lo then some true else none
  | .inj_Id x => if lev G (.inj_Id x) = some .lo then some true else none
  | .inj_Int x => if lev G (.inj_Int x) = some .lo then some true else none
  | .inj_Stmt x => if sec G x = some true then some false else none
  | _ => none

/-- What an item leaves on a confined stack. -/
def citem0 (G : Lab) : KImp.SortKItem → Option Bool
  | .inj_Bool _ => some true
  | .inj_Expr _ => some true
  | .inj_Id _ => some true
  | .inj_Int _ => some true
  | .inj_Stmt x => if conf G x = some true then some false else none
  | _ => none

/-- An item that receives what the previous item leaves: a freezer receives a value. -/
def litem (G : Lab) : Bool → KImp.SortKItem → Option Bool
  | false, it => litem0 G it
  | true, .inj_KItem f => (plug f dflt).bind (litem0 G)
  | true, _ => none

def citem (G : Lab) : Bool → KImp.SortKItem → Option Bool
  | false, it => citem0 G it
  | true, .inj_KItem f => (plug f dflt).bind (citem0 G)
  | true, _ => none

/-- A low stack: each item consumes what the previous one leaves, and nothing is left. -/
def lk (G : Lab) : Bool → KImp.SortK → Bool
  | b, .dotk => !b
  | b, .kseq it k => match litem G b it with
    | some o => lk G o k
    | none => false

/-- A confined stack over the continuation `K`: `k` is `K` with nothing pending, or its first
item consumes `b` and the rest is a confined stack over `K`. -/
def CK (G : Lab) (K : KImp.SortK) : Bool → KImp.SortK → Prop
  | b, .dotk => b = false ∧ KImp.SortK.dotk = K
  | b, .kseq it k => (b = false ∧ KImp.SortK.kseq it k = K) ∨
      (match citem G b it with
       | some o => CK G K o k
       | none => False)

theorem CK_kseq (G : Lab) (K : KImp.SortK) (b : Bool) (it : KImp.SortKItem) (k : KImp.SortK) :
    CK G K b (.kseq it k) = ((b = false ∧ KImp.SortK.kseq it k = K) ∨
      (match citem G b it with
       | some o => CK G K o k
       | none => False)) := rfl

theorem CK_dotk (G : Lab) (K : KImp.SortK) (b : Bool) :
    CK G K b .dotk = (b = false ∧ KImp.SortK.dotk = K) := rfl

theorem CK_base (G : Lab) (K : KImp.SortK) : CK G K false K := by
  cases K <;> simp [CK]

/-! ## Stores -/

/-- `X` is labelled `lo`. -/
def Low (G : Lab) (X : KImp.SortId) : Prop :=
  MapHook.lookup G (KImpSec.SortKItem.inj_Id (tr_SortId X)) = some (KImpSec.SortKItem.inj_Level .lo)

theorem low_of_lev {G : Lab} {X : KImp.SortId} (h : lev G (.inj_Id X) = some .lo) : Low G X := by
  rw [lev_id, levId] at h
  unfold Low
  split at h
  · split at h <;> simp_all
  · simp at h

theorem not_low_of_lev {G : Lab} {X : KImp.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  rw [lev_id, levId] at h
  unfold Low
  intro hl
  split at h
  · simp [hl] at h
  · simp at h

/-- The store changes only at high identifiers, and stays a store. -/
def HiOnly (G : Lab) (E E' : KImp.SortMap) : Prop :=
  Good E' ∧ ∀ X, Low G X → MapHook.lookup E (KImp.SortKItem.inj_Id X) = MapHook.lookup E' (KImp.SortKItem.inj_Id X)

/-! ## Computing the typings -/

theorem litem0_Expr (G : Lab) (x : KImp.SortExpr) :
    litem0 G (KImp.inj_Expr_KItem x) = if lev G x = some .lo then some true else none := by
  cases x <;> rfl
theorem citem0_Expr (G : Lab) (x : KImp.SortExpr) : citem0 G (KImp.inj_Expr_KItem x) = some true := by
  cases x <;> rfl
theorem litem_false (G : Lab) (it : KImp.SortKItem) : litem G false it = litem0 G it := rfl
theorem citem_false (G : Lab) (it : KImp.SortKItem) : citem G false it = citem0 G it := rfl

@[simp] theorem litem0_inj_Bool (G : Lab) (x : KImp.SortBool) : litem0 G (.inj_Bool x) = if lev G (.inj_Bool x) = some .lo then some true else none := rfl
@[simp] theorem litem0_inj_Expr (G : Lab) (x : KImp.SortExpr.Own) : litem0 G (.inj_Expr x) = if lev G (.inj_Expr x) = some .lo then some true else none := rfl
@[simp] theorem litem0_inj_Id (G : Lab) (x : KImp.SortId) : litem0 G (.inj_Id x) = if lev G (.inj_Id x) = some .lo then some true else none := rfl
@[simp] theorem litem0_inj_Int (G : Lab) (x : KImp.SortInt) : litem0 G (.inj_Int x) = if lev G (.inj_Int x) = some .lo then some true else none := rfl
@[simp] theorem litem0_inj_Stmt (G : Lab) (x : KImp.SortStmt) : litem0 G (.inj_Stmt x) = if sec G x = some true then some false else none := rfl
@[simp] theorem litem0_inj_KItem (G : Lab) (x : KImp.SortKItem.Own) : litem0 G (.inj_KItem x) = none := rfl
@[simp] theorem citem0_inj_Bool (G : Lab) (x : KImp.SortBool) : citem0 G (.inj_Bool x) = some true := rfl
@[simp] theorem citem0_inj_Expr (G : Lab) (x : KImp.SortExpr.Own) : citem0 G (.inj_Expr x) = some true := rfl
@[simp] theorem citem0_inj_Id (G : Lab) (x : KImp.SortId) : citem0 G (.inj_Id x) = some true := rfl
@[simp] theorem citem0_inj_Int (G : Lab) (x : KImp.SortInt) : citem0 G (.inj_Int x) = some true := rfl
@[simp] theorem citem0_inj_Stmt (G : Lab) (x : KImp.SortStmt) : citem0 G (.inj_Stmt x) = if conf G x = some true then some false else none := rfl
@[simp] theorem citem0_inj_KItem (G : Lab) (x : KImp.SortKItem.Own) : citem0 G (.inj_KItem x) = none := rfl
@[simp] theorem litem_true_frz (G : Lab) (f : KImp.SortKItem.Own) : litem G true (.inj_KItem f) = (plug f dflt).bind (litem0 G) := rfl
@[simp] theorem citem_true_frz (G : Lab) (f : KImp.SortKItem.Own) : citem G true (.inj_KItem f) = (plug f dflt).bind (citem0 G) := rfl
@[simp] theorem litem_true_Expr (G : Lab) (x : KImp.SortExpr) : litem G true (KImp.inj_Expr_KItem x) = none := by cases x <;> rfl
@[simp] theorem citem_true_Expr (G : Lab) (x : KImp.SortExpr) : citem G true (KImp.inj_Expr_KItem x) = none := by cases x <;> rfl
@[simp] theorem litem_true_Stmt (G : Lab) (x : KImp.SortStmt) : litem G true (.inj_Stmt x) = none := rfl
@[simp] theorem citem_true_Stmt (G : Lab) (x : KImp.SortStmt) : citem G true (.inj_Stmt x) = none := rfl
@[simp] theorem lk_dotk (G : Lab) (b : Bool) : lk G b .dotk = !b := rfl
@[simp] theorem lk_kseq (G : Lab) (b : Bool) (it : KImp.SortKItem) (k : KImp.SortK) :
    lk G b (.kseq it k) = (match litem G b it with | some o => lk G o k | none => false) := rfl
attribute [simp] litem0_Expr citem0_Expr litem_false citem_false

/-! ## Stores and values -/

theorem isVal_inj_Value (V : KImp.SortValue) : isVal (KImp.inj_Value_KItem V) = true := by
  cases V <;> rfl

theorem citem0_of_isVal (G : Lab) {v : KImp.SortKItem} (h : isVal v = true) : citem0 G v = some true := by
  cases v <;> simp_all [isVal]

theorem litem0_of_isVal (G : Lab) {v : KImp.SortKItem} (h : isVal v = true) : litem0 G v = some true := by
  cases v <;> simp_all [isVal, lev_int, lev_bool]

theorem Good.lookup {E : KImp.SortMap} (hE : Good E) {X : KImp.SortId} {v : KImp.SortKItem}
    (h : MapHook.lookup E (KImp.SortKItem.inj_Id X) = some v) : isVal v = true := hE.2 X v h

theorem Good.update {E : KImp.SortMap} (hE : Good E) (X : KImp.SortId) (V : KImp.SortValue) :
    Good (MapHook.update E (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V)) := by
  refine ⟨MapHook.wf_update hE.1, fun X' v h => ?_⟩
  by_cases hx : X' = X
  · subst hx
    rw [MapHook.lookup_update_self] at h
    cases h; exact isVal_inj_Value V
  · rw [MapHook.lookup_update_ne _ _ (fun h => hx (by cases h; rfl))] at h
    exact hE.2 X' v h

theorem hiOnly_refl {G : Lab} {E : KImp.SortMap} (hE : Good E) : HiOnly G E E := ⟨hE, fun _ _ => rfl⟩

theorem hiOnly_update {G : Lab} {E : KImp.SortMap} (hE : Good E) {X : KImp.SortId} (V : KImp.SortValue)
    (hX : lev G (.inj_Id X) = some .hi) :
    HiOnly G E (MapHook.update E (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V)) := by
  refine ⟨hE.update X V, fun X' hl => ?_⟩
  have hne : X' ≠ X := fun h => not_low_of_lev hX (h ▸ hl)
  rw [MapHook.lookup_update_ne _ _ (fun h => hne (by cases h; rfl))]

theorem lev_hi_of_conf_assign {G : Lab} {X : KImp.SortId} {y : KImp.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf_assign] at h
  split at h
  · rename_i l hl
    cases l <;> simp_all
  · simp at h

theorem lowEq_update {G : Lab} {E₁ E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) (X : KImp.SortId) (V : KImp.SortValue) :
    lowEq G (MapHook.update E₁ (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V))
      (MapHook.update E₂ (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V)) := by
  refine ⟨h.1.update X V, h.2.1.update X V, fun X' hl => ?_⟩
  by_cases hx : X' = X
  · subst hx; rw [MapHook.lookup_update_self, MapHook.lookup_update_self]
  · have hne : KImp.SortKItem.inj_Id X' ≠ KImp.SortKItem.inj_Id X := fun h => hx (by cases h; rfl)
    rw [MapHook.lookup_update_ne _ _ hne, MapHook.lookup_update_ne _ _ hne]
    exact h.2.2 X' hl

theorem lowEq_lookup {G : Lab} {E₁ E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) {X : KImp.SortId}
    (hX : lev G (.inj_Id X) = some .lo) :
    MapHook.lookup E₁ (KImp.SortKItem.inj_Id X) = MapHook.lookup E₂ (KImp.SortKItem.inj_Id X) :=
  h.2.2 X (low_of_lev hX)

/-! ## The closers of the per-rule cases

`k2l_ni_comp` computes the typings of both sides of a rule (`k2l_ni_simp`), cases on the values of
the checker's functions that the computation stops at (`k2l_ni_split`), and computes again. -/

open Lean Meta Elab Tactic in
/-- Case every variable of the store cell's sort into `<env> E`. -/
elab "k2l_cases_env" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let some d ← g.withContext do
        (← getLCtx).findDeclM? fun d => do
          if d.isImplementationDetail then return none
          let t ← whnfR d.type
          return if t.isConstOf ``KImp.SortEnvCell then some d else none
      | return
    let gs ← g.cases d.fvarId
    replaceMainGoal (gs.map (·.mvarId)).toList
    go (fuel - 1)
  go 8

open Lean Meta Elab Tactic in
/-- Case on the value of an application of one of `fs` in a hypothesis or the goal that no
equation hypothesis has as its left-hand side yet, and recurse. -/
partial def niSplitLoop (fs : Array Name) (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let found ← g.withContext do
    let lctx ← getLCtx
    let mut done : Array Expr := #[]
    let mut cands : Array Expr := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if let some (_, l, _) := t.eq? then done := done.push l
      cands := cands.push t
    cands := cands.push (← instantiateMVars (← g.getType))
    for t in cands do
      if let some e := t.find? (fun e => !e.hasLooseBVars && fs.any e.isAppOf && e.getAppNumArgs == 2 && !done.contains e) then
        return some e
    return none
  let some e := found | return
  let x ← g.withContext (Term.exprToSyntax e)
  evalTactic (← `(tactic| ((rcases _h : $x:term with _ | v) <;> (try cases v))))
  KPrelude.Soundness.eachGoal (niSplitLoop fs (fuel - 1))

elab "k2l_ni_split" : tactic => niSplitLoop #[``ImpNI.conf, ``ImpNI.sec, ``ImpNI.lev] 6

macro "k2l_ni_simp" : tactic => `(tactic| simp_all [plug, dflt, citem0_Expr, litem0_Expr, KImp.proj_inj_KItem_Expr,
    lev_int, lev_bool, lev_neg, lev_not, lev_bin_0, lev_bin_1, lev_bin_2, lev_bin_3, lev_bin_4, lev_bin_5,
    lev_bin_6, lev_bin_7, lev_bin_8, lev_bin_9, lev_bin_10, lev_bin_11,
    join, conf_empty, conf_block, conf_seq, conf_assign, conf_ifelse, conf_if, conf_while,
    sec_empty, sec_block, sec_seq, sec_assign, sec_ifelse, sec_if, sec_while, CK_base])

macro "k2l_ni_comp" : tactic => `(tactic|
  (try k2l_ni_simp) <;> (try (k2l_ni_split; all_goals (try k2l_ni_simp))))

end ImpNI
