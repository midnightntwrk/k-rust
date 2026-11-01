import TwoParamInst.Inst
import Corout.Measure
import Corout.Progress
import KPrelude.Measure

/-!
# Every segment ends (`docs/direction.md` §8 step 4, the termination of each segment)

`TwoParamInst` takes the hooks of `twoparam` from corout's run of a segment to the first
configuration that does not step, and gives `none` where no such configuration exists. The fixture
`corout` states its measure in K (`measure`, the steps left, with two lemmas about it as
simplification rules), and `gen --measure measure@T` proves that every rule lowers it
(`Corout.Measure.lower`, every case by `k2l_measure`), so no run of corout is infinite from a
configuration where the measure is defined (`Corout.Measure.terminates`), as it is at a segment's
start (`defined`, by the lemma). A run from a segment's start therefore reaches a first configuration
that does not step (`ends`), which holds code, as every configuration a corout rule builds does
(`shape_of`), so both hooks have a value at every register and code (`hooks_some`).

The fixture also states where a segment may end, `segEnd` (a `yield` or the code's end), and that
`<k>` holds code, `kOk`. `gen --progress` proves that a configuration holding code is a segment end
or has a rule that applies (`Corout.progress`). Where a rule applies, a step exists: `loop`'s also
needs `app` defined, which it is everywhere (`app_some`). So a segment ends only at a segment end
(`ends_segEnd`): the code the instance keeps (`after`, what follows the `yield`) is never what is left
of a segment that stopped early.
-/

namespace TwoParamEnds

open KPrelude TwoParamInst

/-- A configuration whose `<k>` holds code: what corout's rules take and build. -/
def Shape (c : Corout.SortGeneratedTopCell) : Prop :=
  ∃ C r n, c = .«<generatedTop>» (.«<T>» (.«<k>» (.kseq (.inj_Stmts C) .dotk)) r) n

/-- Every configuration a run reaches from one holding code holds code. -/
theorem shape_of {a e : Corout.SortGeneratedTopCell}
    (h : Paths.FirstReach Corout.Step (Terminal Corout.Step) a e) (ha : Shape a) : Shape e := by
  induction h with
  | here _ => exact ha
  | step _ hs _ ih => apply ih; cases hs <;> exact ⟨_, _, _, rfl⟩

/-- The measure is defined at a segment's start: it is `mu` of the code, which has a value by the
fixture's lemma `mu(C) >=Int 0` (`Corout.Simp.s_635e8b9640b8`, which states the value nonnegative
and so defined). -/
theorem defined (R : Int) (C : Corout.SortStmts) : (Corout.Measure.value (start R C)).isSome := by
  have h := Corout.Simp.s_635e8b9640b8 C
  simp only [Corout.Measure.value, Corout.Measure.cell_T, start,
    Corout.Eqn.«measure(_)_COROUT_Int_TCell_1», Option.bind_fun_some]
  cases hm : Corout.K.«mu(_)_COROUT_Int_Stmts» C <;> simp_all

/-- Every segment ends: corout's run from its start reaches a first configuration that does not
step. -/
theorem ends (R : Int) (C : Corout.SortStmts) : ∃ e, Ends R C e :=
  KPrelude.Measure.exists_firstReach_terminal (Corout.Measure.terminates (start R C) (defined R C))

/-- The hooks of `twoparam` that corout gives have a value at every register and code: a resume
always has its segment's output and the code its process keeps. -/
theorem hooks_some (R : Int) (C : TwoParam.SortStmts) :
    (∃ r, TwoParam.Hooks.«fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» R C = some r) ∧
      ∃ C', TwoParam.Hooks.«fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» R C = some C' := by
  obtain ⟨e, he⟩ := ends R (Tr.tr_SortStmts C)
  obtain ⟨hr, hc⟩ := seg_of_ends he
  obtain ⟨C', r, n, rfl⟩ := shape_of he ⟨_, _, _, rfl⟩
  exact ⟨⟨_, hr⟩, _, hc⟩

/-- `app` has a value at every two lists of statements, by its two equations. -/
theorem app_some : ∀ (A T : Corout.SortStmts), ∃ r, Corout.K.«app(_,_)_COROUT_Stmts_Stmts_Stmts» A T = some r
  | .«_;_» S A, T => by
    obtain ⟨r, h⟩ := app_some A T
    exact ⟨_, by rw [Corout.Eqn.«app(_,_)_COROUT_Stmts_Stmts_Stmts_2», h, Option.bind_some]⟩
  | .«.List{"_;__COROUT-SYNTAX_Stmts_Stmt_Stmts"}_Stmts», T =>
    ⟨T, Corout.Eqn.«app(_,_)_COROUT_Stmts_Stmts_Stmts_1» T⟩

/-- Where a rule of corout applies, a step exists. -/
theorem step_of_app {c : Corout.SortGeneratedTopCell} (h : Corout.App c) : ∃ c', Corout.Step c c' := by
  cases h with
  | add => exact ⟨_, Corout.Step.add ..⟩
  | dbl => exact ⟨_, Corout.Step.dbl ..⟩
  | loop M C r n B hreq =>
    obtain ⟨_, ha⟩ := app_some B (.«_;_» (.«loop(_,_)» (IntHook.sub M 1) (.«{_}» B)) C)
    exact ⟨_, Corout.Step.loop _ _ _ _ _ _ hreq ha⟩
  | «loop-done» M G C r n hreq => exact ⟨_, Corout.Step.«loop-done» M G C r n hreq⟩

/-- Where a segment ends, nothing steps. -/
theorem terminal_of_ends {R : Int} {C : Corout.SortStmts} {e : Corout.SortGeneratedTopCell}
    (h : Ends R C e) : Terminal Corout.Step e := by
  unfold Ends at h
  generalize start R C = a at h
  induction h with
  | here hy => exact hy
  | step _ _ _ ih => exact ih

/-- **A segment ends only at a segment end:** the configuration corout's run of a segment stops at
is a `yield` or the code's end (`segEnd`). -/
theorem ends_segEnd {R : Int} {C : Corout.SortStmts} {e : Corout.SortGeneratedTopCell}
    (h : Ends R C e) : Corout.Ending e := by
  have ht := terminal_of_ends h
  obtain ⟨C', r, n, rfl⟩ := shape_of h ⟨_, _, _, rfl⟩
  have hI : Corout.Invariant (.«<generatedTop>» (.«<T>» (.«<k>» (.kseq (.inj_Stmts C') .dotk)) r) n) :=
    Corout.Eqn.«kOk(_)_COROUT_Bool_K_1» C'
  rcases Corout.progress _ hI with he | ha
  · exact he
  · obtain ⟨_, hs⟩ := step_of_app ha
    exact absurd hs (ht _)

#k2l_assert_axioms defined ends hooks_some app_some step_of_app terminal_of_ends ends_segEnd

end TwoParamEnds
