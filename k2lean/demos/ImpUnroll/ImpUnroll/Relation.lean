import ImpUnroll.Tr
import KPrelude.Scaffold

/-! The hand-written part of the stuttering bisimulation between kimp (`KImp`) and its variant
whose `while` unrolls straight to the two-armed `if` (`KUnroll`, `tests/kimp-unroll.py`):
the non-local part `X` of the relation, the measures, and the six cases `k2lean refine` does not
generate (`demos/ImpUnroll/open-cases.txt`). `ImpUnroll.Refine` (generated) proves the rest.

kimp takes two steps where the variant takes one: `while (C) S` becomes `if (C) {S while (C) S}`,
which `if-else` completes to `if (C) {…} else {}`. Between the two, kimp is at a one-armed `if`
and the variant already at the two-armed one: that is `X`. A step of kimp from such a state is
`if-else`, which the variant does not match: kimp stutters, and `μ` (1 at a one-armed `if`, 0
elsewhere) decreases. A step of the variant from such a state is matched by `if-else` and the
same rule in kimp. -/

set_option linter.unusedVariables false

namespace ImpUnroll

open KPrelude

/-- kimp at a one-armed `if`, the variant at its completion with `else {}`. The variant's side is
a pattern of its constructors over variables, each the translation of kimp's (`hC` … `hg`), so
that `cases` on `X` against a rule's left-hand side clashes on constructors where they differ
and never has to invert a translation. -/
inductive X : KImp.SortGeneratedTopCell → KUnroll.SortGeneratedTopCell → Prop where
  | unroll (C : KImp.SortExpr) (S : KImp.SortStmt) (K : KImp.SortK) (E : KImp.SortEnvCell)
      (g : KImp.SortGeneratedCounterCell) (C' : KUnroll.SortExpr) (S' : KUnroll.SortStmt)
      (K' : KUnroll.SortK) (E' : KUnroll.SortEnvCell) (g' : KUnroll.SortGeneratedCounterCell)
      (hC : C' = tr_SortExpr C) (hS : S' = tr_SortStmt S) (hK : K' = tr_SortK K)
      (hE : E' = tr_SortEnvCell E) (hg : g' = tr_SortGeneratedCounterCell g) :
      X (.«<generatedTop>» (.«<k>» (.kseq (.inj_Stmt (.«if(_)_» C S)) K)) E g)
        (.«<generatedTop>» (.«<k>» (.kseq (.inj_Stmt (.«if(_)_else_» C' S' .«{}»)) K')) E' g')

theorem X_inv {c : KImp.SortGeneratedTopCell} {d : KUnroll.SortGeneratedTopCell} (h : X c d) :
    ∃ C S K E g, c = .«<generatedTop>» (.«<k>» (.kseq (.inj_Stmt (.«if(_)_» C S)) K)) E g ∧
      d = .«<generatedTop>» (.«<k>» (.kseq (.inj_Stmt (.«if(_)_else_» (tr_SortExpr C) (tr_SortStmt S) .«{}»))
        (tr_SortK K))) (tr_SortEnvCell E) (tr_SortGeneratedCounterCell g) := by
  cases h; subst_vars; exact ⟨_, _, _, _, _, rfl, rfl⟩

/-- kimp's measure: 1 at a one-armed `if`, where it stutters. -/
def μ : KImp.SortGeneratedTopCell → Nat
  | .«<generatedTop>» (.«<k>» (.kseq (.inj_Stmt (.«if(_)_» _ _)) _)) _ _ => 1
  | _ => 0

/-- The variant never stutters. -/
def ν (_ : KUnroll.SortGeneratedTopCell) : Nat := 0

abbrev R := Stutter.Rel tr_SortGeneratedTopCell X

/-- kimp's `while`: the variant's `while` leads to the completed `if`, which `X` relates to kimp's
one-armed one. -/
theorem hand.fwd_tr.«IMP.while» :
    KImp.Step.Rel.«IMP.while» (Stutter.FwdTr tr_SortGeneratedTopCell KUnroll.Step X μ) := by
  intro K E g C S
  exact Or.inl ⟨_, .single (KUnroll.Step.«IMP.while» (tr_SortK K) (tr_SortEnvCell E)
    (tr_SortGeneratedCounterCell g) (tr_SortExpr C) (tr_SortStmt S)), Or.inr (X.unroll _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl)⟩

/-- kimp's `if-else` at a state `X` relates: kimp catches up with the variant, which stays. -/
theorem hand.fwd_x.«IMP.if-else» :
    KImp.Step.Rel.«IMP.if-else» (Stutter.FwdX tr_SortGeneratedTopCell KUnroll.Step X μ) := by
  intro C S K E g d hX
  cases hX
  subst_vars
  exact Or.inr ⟨Or.inl rfl, by simp [μ]⟩

/-- The variant's `while`: kimp takes `while` and `if-else`. -/
theorem hand.bwd_tr.«IMP.while» :
    KUnroll.Step.Rel.«IMP.while» (Stutter.BwdTr tr_SortGeneratedTopCell KImp.Step X ν) := by
  intro K E g C S c hd
  have hd := hd.symm
  k2l_inv
  exact Or.inl ⟨_, .tail (.single (KImp.Step.«IMP.while» _ _ _ _ _)) (KImp.Step.«IMP.if-else» _ _ _ _ _),
    Or.inl rfl⟩

/-- At a state `X` relates, a step of the variant from the completed `if` is `if-else` and the
same step in kimp. -/
theorem hand.bwd_x.«IMP.if-true» :
    KUnroll.Step.Rel.«IMP.if-true» (Stutter.BwdX tr_SortGeneratedTopCell KImp.Step X ν) := by
  intro S1 S2 K E g c hX
  obtain ⟨C, S, K', E', g', rfl, hd⟩ := X_inv hX
  k2l_injections
  k2l_inv
  exact Or.inl ⟨_, .tail (.single (KImp.Step.«IMP.if-else» _ _ _ _ _)) (KImp.Step.«IMP.if-true» _ _ _ _ _),
    Or.inl rfl⟩

theorem hand.bwd_x.«IMP.if-false» :
    KUnroll.Step.Rel.«IMP.if-false» (Stutter.BwdX tr_SortGeneratedTopCell KImp.Step X ν) := by
  intro S1 S2 K E g c hX
  obtain ⟨C, S, K', E', g', rfl, hd⟩ := X_inv hX
  k2l_injections
  k2l_inv
  exact Or.inl ⟨_, .tail (.single (KImp.Step.«IMP.if-else» _ _ _ _ _)) (KImp.Step.«IMP.if-false» _ _ _ _ _),
    Or.inl rfl⟩

/-- Heating the condition of the completed `if`: kimp completes its `if` first. -/
theorem hand.bwd_x.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» :
    KUnroll.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»
      (Stutter.BwdX tr_SortGeneratedTopCell KImp.Step X ν) := by
  intro H S1 S2 K E g hreq c hX
  obtain ⟨C, S, K', E', g', rfl, hd⟩ := X_inv hX
  k2l_injections
  k2l_inv
  refine Or.inl ⟨_, .tail (.single (KImp.Step.«IMP.if-else» _ _ _ _ _))
    (KImp.Step.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» _ _ _ _ _ _ ?_), Or.inl ?_⟩
  · simpa only [k2l_rel] using hreq
  · simp only [k2l_rel]

#k2l_assert_axioms X_inv hand.fwd_tr.«IMP.while» hand.fwd_x.«IMP.if-else» hand.bwd_tr.«IMP.while»
  hand.bwd_x.«IMP.if-true» hand.bwd_x.«IMP.if-false»
  hand.bwd_x.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»

end ImpUnroll
