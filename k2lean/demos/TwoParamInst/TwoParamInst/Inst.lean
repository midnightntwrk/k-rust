import TwoParamConf
import Corout.Determinism
import Corout.Equations
import TwoParamInst.Tr
import TwoParamInst.Back
import KPrelude.Paths

/-!
# The parameterized form's segments, run by the coroutine language (`docs/direction.md` §8 step 4)

The fixture `twoparam` leaves a segment's register and code (`segReg`, `segCode`) as parameters,
the fields of `TwoParam.Hooks`, and `TwoParamConf.terminal_unique` holds for every instance. The
fixture `corout` is the coroutine language on its own. Nothing steps at a `yield` or at the code's
end, and its steps are deterministic (`Corout.Step.deterministic`, generated with no overlapping
pair). So a run from a segment's start has at most one first configuration that does not step
(`Paths.FirstReach.unique`), and the instance below takes the hooks from it: the segment from
register `R` and code `C` is corout's run from `<k> C </k> <reg> R </reg>` to that configuration.
Its register is the segment's output, and the code after its `yield` is what the process keeps. A
segment that never ends has no value (`none`), so its resume does not step. Each segment's
termination (B's segment measure) would rule that case out.
-/

namespace TwoParamInst

open KPrelude

/-- Corout's configuration at the start of a segment. -/
def start (R : Int) (C : Corout.SortStmts) : Corout.SortGeneratedTopCell :=
  .«<generatedTop>» (.«<T>» (.«<k>» (.kseq (.inj_Stmts C) .dotk)) (.«<reg>» R)) (.«<generatedCounter>» 0)

/-- `e` is where corout's run of the segment from `R` and `C` ends: the first configuration that
does not step. -/
def Ends (R : Int) (C : Corout.SortStmts) (e : Corout.SortGeneratedTopCell) : Prop :=
  Paths.FirstReach Corout.Step (Terminal Corout.Step) (start R C) e

/-- A segment ends at one configuration at most. -/
theorem ends_unique {R : Int} {C : Corout.SortStmts} {e e' : Corout.SortGeneratedTopCell}
    (h : Ends R C e) (h' : Ends R C e') : e = e' :=
  Paths.FirstReach.unique (R := Corout.Step) (fun h₁ h₂ => Corout.Step.deterministic h₁ h₂) h h'

/-- The register where a segment ends. -/
def regOf : Corout.SortGeneratedTopCell → Int
  | .«<generatedTop>» (.«<T>» _ (.«<reg>» r)) _ => r

/-- The code a process keeps: what follows the `yield` the segment ends at. -/
def after : Corout.SortStmts → Corout.SortStmts
  | .«_;_» .yield C => C
  | C => C

/-- The code where a segment ends. -/
def codeOf : Corout.SortGeneratedTopCell → Option Corout.SortStmts
  | .«<generatedTop>» (.«<T>» (.«<k>» (.kseq (.inj_Stmts C) .dotk)) _) _ => some (after C)
  | _ => none

open Classical

/-- The segments of `twoparam` as corout runs them. -/
noncomputable instance hooks : TwoParam.Hooks where
  «fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» R C :=
    if h : ∃ e, Ends R (Tr.tr_SortStmts C) e then some (regOf (choose h)) else none
  «fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» R C :=
    if h : ∃ e, Ends R (Tr.tr_SortStmts C) e then (codeOf (choose h)).map Back.tr_SortStmts else none

/-- A run of corout to a segment's end gives the hooks' values. -/
theorem seg_of_ends {R : Int} {C : TwoParam.SortStmts} {e : Corout.SortGeneratedTopCell}
    (h : Ends R (Tr.tr_SortStmts C) e) :
    TwoParam.Hooks.«fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» R C = some (regOf e) ∧
      TwoParam.Hooks.«fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» R C =
        (codeOf e).map Back.tr_SortStmts := by
  refine ⟨?_, ?_⟩ <;> show (if h : _ then _ else _) = _ <;> split
  all_goals first
    | (rename_i ex; rw [ends_unique (choose_spec ex) h])
    | (rename_i n; exact absurd ⟨e, h⟩ n)

/-- A segment that never ends has no value. -/
theorem seg_of_not_ends {R : Int} {C : TwoParam.SortStmts}
    (h : ¬ ∃ e, Ends R (Tr.tr_SortStmts C) e) :
    TwoParam.Hooks.«fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» R C = none ∧
      TwoParam.Hooks.«fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» R C = none := by
  refine ⟨?_, ?_⟩ <;> show (if h : _ then _ else _) = _ <;> split
  all_goals first
    | rfl
    | (rename_i ex; exact absurd ex h)

/-- One segment: from register 1, `add(2) ; yield ; dbl` yields 3 and keeps `dbl`. -/
example :
    TwoParam.Hooks.«fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» 1
        (.«_;_» (.«add(_)» 2) (.«_;_» .yield (.«_;_» .dbl .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»))) =
      some 3 ∧
    TwoParam.Hooks.«fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» 1
        (.«_;_» (.«add(_)» 2) (.«_;_» .yield (.«_;_» .dbl .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»))) =
      some (.«_;_» .dbl .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») := by
  have stuck : Terminal Corout.Step
      (.«<generatedTop>» (.«<T>» (.«<k>» (.kseq (.inj_Stmts (.«_;_» .yield (.«_;_» .dbl
        .«.List{"_;__COROUT-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»))) .dotk)) (.«<reg>» 3))
        (.«<generatedCounter>» 0)) := by
    intro c' h
    cases h
  have st : Corout.Step (start 1 (Tr.tr_SortStmts
      (.«_;_» (.«add(_)» 2) (.«_;_» .yield (.«_;_» .dbl .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)))))
      (.«<generatedTop>» (.«<T>» (.«<k>» (.kseq (.inj_Stmts (.«_;_» .yield (.«_;_» .dbl
        .«.List{"_;__COROUT-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»))) .dotk)) (.«<reg>» 3))
        (.«<generatedCounter>» 0)) :=
    Corout.Step.add 2 _ 1 _
  have e := (seg_of_ends (Paths.FirstReach.step (fun t => t _ st) st (Paths.FirstReach.here stuck)))
  exact ⟨e.1, e.2⟩

/-- `loop(2, {dbl}) ; yield`, the code a process keeps after the first segment of `prog`. -/
def rest : TwoParam.SortStmts :=
  .«_;_» (.«loop(_,_)» 2 (.«{_}» (.«_;_» .dbl .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)))
    (.«_;_» .yield .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)

/-- `add(1) ; yield ; loop(2, {dbl}) ; yield`. -/
def prog : TwoParam.SortStmts := .«_;_» (.«add(_)» 1) (.«_;_» .yield rest)

/-- `app` of a one-statement body, by corout's equations (`app` recurs on its first argument, so it
does not reduce by `rfl`). -/
theorem app_one {S : Corout.SortStmt} {T : Corout.SortStmts} :
    Corout.K.«app(_,_)_COROUT_Stmts_Stmts_Stmts»
      (.«_;_» S .«.List{"_;__COROUT-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») T = some (.«_;_» S T) := by
  simp [Corout.Eqn.«app(_,_)_COROUT_Stmts_Stmts_Stmts_1», Corout.Eqn.«app(_,_)_COROUT_Stmts_Stmts_Stmts_2»]

/-- A run of corout to a segment's end, step by step: each step is corout's `step` computed
(`Corout.step_sound`), or a `loop` whose body is one statement (`app_one`), and the end is a
configuration no rule matches. -/
local macro "k2l_seg_run" : tactic => `(tactic| (simp only [Ends, start, prog, rest, k2l_tr]; repeat (first
  | (refine Paths.FirstReach.here ?_; intro _ h; cases h <;> done)
  | (refine Paths.FirstReach.step ?_ (Corout.step_sound rfl) ?_
     · intro t; exact t _ (Corout.step_sound rfl))
  | (refine Paths.FirstReach.step ?_ (Corout.Step.loop _ _ _ _ _ _ (by rfl) app_one) ?_
     · intro t; exact t _ (Corout.Step.loop _ _ _ _ _ _ (by rfl) app_one)))))

/-- Two segments of one process: resumed with 1 from register 0, `prog` yields 2 and keeps `rest`,
the code after the `yield`; resumed again with 1, from register 3, `rest` runs its loop and yields
12, keeping nothing. -/
example :
    TwoParam.Hooks.«fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» 1 prog = some 2 ∧
    TwoParam.Hooks.«fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» 1 prog = some rest ∧
    TwoParam.Hooks.«fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» 3 rest = some 12 ∧
    TwoParam.Hooks.«fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» 3 rest =
      some .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts» :=
  -- the first segment stops at the `yield` with register 2, the second at the last `yield` with 12
  have s₁ := seg_of_ends (show Ends 1 (Tr.tr_SortStmts prog)
    (start 2 (.«_;_» .yield (Tr.tr_SortStmts rest))) by k2l_seg_run)
  have s₂ := seg_of_ends (show Ends 3 (Tr.tr_SortStmts rest)
    (start 12 (.«_;_» .yield .«.List{"_;__COROUT-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)) by k2l_seg_run)
  ⟨s₁.1, s₁.2.trans (by simp [codeOf, after, start, rest, k2l_tr]), s₂.1,
    s₂.2.trans (by simp [codeOf, after, start, k2l_tr])⟩

end TwoParamInst

namespace TwoParamInst

open KPrelude

/-- The parameterized form at corout's segments: from a configuration where the script is
well formed (`wf`), every two runs to a terminal configuration end at the same one. -/
theorem terminal_unique {c n₁ n₂ : TwoParam.SortGeneratedTopCell} (hinv : TwoParam.Invariant c)
    (h₁ : Star TwoParam.Step c n₁) (t₁ : Terminal TwoParam.Step n₁) (h₂ : Star TwoParam.Step c n₂)
    (t₂ : Terminal TwoParam.Step n₂) : n₁ = n₂ :=
  TwoParamConf.terminal_unique hinv h₁ t₁ h₂ t₂

#k2l_assert_axioms ends_unique seg_of_ends seg_of_not_ends terminal_unique

end TwoParamInst
