import ImpNI.Same

/-! Hand-written. kimp's noninterference for the security checker `k/imp-sec.k`: the relation on
pairs of runs and its three modes, and the 240 obligations of `NI.lean` discharged.

- `Rel`: the two `<k>` cells are confined stacks (`CK`) over a common low stack `K` (`lk`), and the
  stores are low-equal. A run inside its confined part executes alone; the common part is executed in
  lockstep.
- `Left`: the left run is inside its confined part; `Right`: the left run has reached `K` and the
  right one has not; `Sync`: both are at `K`.

Each per-rule obligation follows from one of three per-rule lemmas, proved for every step: `cq_step`
(`Confine.lean`: a step inside a confined stack stays confined and writes only high identifiers),
`sq_step` (`Sync.lean`: a step from a low stack leads to a confined stack over a low stack) and
`same_step` (`Same.lean`: from the same low stack and low-equal stores, both runs step to the same
stack and low-equal stores). -/

namespace ImpNI

open KPrelude

variable (G : Lab)

def Rel (c₁ c₂ : KImp.SortGeneratedTopCell) : Prop :=
  ∃ K, CK G K false (kOf c₁) ∧ CK G K false (kOf c₂) ∧ lk G false K = true ∧
    lowEq G (storeOf c₁) (storeOf c₂)

def Left (c₁ c₂ : KImp.SortGeneratedTopCell) : Prop :=
  ∃ K, CK G K false (kOf c₁) ∧ kOf c₁ ≠ K ∧ CK G K false (kOf c₂) ∧ lk G false K = true ∧
    lowEq G (storeOf c₁) (storeOf c₂)

def Right (c₁ c₂ : KImp.SortGeneratedTopCell) : Prop :=
  ∃ K, kOf c₁ = K ∧ CK G K false (kOf c₂) ∧ kOf c₂ ≠ K ∧ lk G false K = true ∧
    lowEq G (storeOf c₁) (storeOf c₂)

variable {G}

theorem lowEq_symm {E₁ E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) : lowEq G E₂ E₁ :=
  ⟨h.2.1, h.1, fun X hX => (h.2.2 X hX).symm⟩

theorem lowEq_hiOnly {E₁ E₁' E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) (h' : HiOnly G E₁ E₁') :
    lowEq G E₁' E₂ :=
  ⟨h'.1, h.2.1, fun X hX => (h'.2 X hX).symm.trans (h.2.2 X hX)⟩

theorem ne_dotk_of_CK {K k : KImp.SortK} (h : CK G K false k) (hne : k ≠ K) : k ≠ .dotk := by
  rintro rfl
  exact hne (h.2)

theorem sync_all {c₁ c₁' : KImp.SortGeneratedTopCell} (h : KImp.Step c₁ c₁') :
    ∀ c₂ c₂', Sync G c₁ c₂ → KImp.Step c₂ c₂' → Rel G c₁' c₂' := by
  intro c₂ c₂' hs h₂
  obtain ⟨hk, hlow⟩ := same_step G h c₂ c₂' hs h₂
  obtain ⟨K, hck, hlk⟩ := sq_step G h hs.2.1 hs.2.2.1
  exact ⟨K, hck, hk ▸ hck, hlk, hlow⟩

theorem left_all {c₁ c₁' : KImp.SortGeneratedTopCell} (h : KImp.Step c₁ c₁') :
    ∀ c₂, Left G c₁ c₂ → Rel G c₁' c₂ := by
  rintro c₂ ⟨K, hc₁, hne, hc₂, hlk, hlow⟩
  obtain ⟨hc₁', hhi⟩ := cq_step G h K hc₁ hne hlow.1
  exact ⟨K, hc₁', hc₂, hlk, lowEq_hiOnly hlow hhi⟩

theorem right_all {c₂ c₂' : KImp.SortGeneratedTopCell} (h : KImp.Step c₂ c₂') :
    ∀ c₁, Right G c₁ c₂ → Rel G c₁ c₂' := by
  rintro c₁ ⟨K, hc₁, hc₂, hne, hlk, hlow⟩
  obtain ⟨hc₂', hhi⟩ := cq_step G h K hc₂ hne hlow.2.1
  exact ⟨K, hc₁ ▸ CK_base G K, hc₂', hlk, lowEq_symm (lowEq_hiOnly (lowEq_symm hlow) hhi)⟩

theorem rel.«- X» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«- X» Q := by
  unfold KImp.Step.Rel.«- X»
  intros
  apply h
  apply KImp.Step.«- X» <;> assumption
theorem rel.«! B» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«! B» Q := by
  unfold KImp.Step.Rel.«! B»
  intros
  apply h
  apply KImp.Step.«! B» <;> assumption
theorem rel.«X + Y» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«X + Y» Q := by
  unfold KImp.Step.Rel.«X + Y»
  intros
  apply h
  apply KImp.Step.«X + Y» <;> assumption
theorem rel.«X - Y» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«X - Y» Q := by
  unfold KImp.Step.Rel.«X - Y»
  intros
  apply h
  apply KImp.Step.«X - Y» <;> assumption
theorem rel.«X * Y» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«X * Y» Q := by
  unfold KImp.Step.Rel.«X * Y»
  intros
  apply h
  apply KImp.Step.«X * Y» <;> assumption
theorem rel.«X / Y» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«X / Y» Q := by
  unfold KImp.Step.Rel.«X / Y»
  intros
  apply h
  apply KImp.Step.«X / Y» <;> assumption
theorem rel.«I1 >= I2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«I1 >= I2» Q := by
  unfold KImp.Step.Rel.«I1 >= I2»
  intros
  apply h
  apply KImp.Step.«I1 >= I2» <;> assumption
theorem rel.«I1 > I2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«I1 > I2» Q := by
  unfold KImp.Step.Rel.«I1 > I2»
  intros
  apply h
  apply KImp.Step.«I1 > I2» <;> assumption
theorem rel.«I1 <= I2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«I1 <= I2» Q := by
  unfold KImp.Step.Rel.«I1 <= I2»
  intros
  apply h
  apply KImp.Step.«I1 <= I2» <;> assumption
theorem rel.«I1 < I2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«I1 < I2» Q := by
  unfold KImp.Step.Rel.«I1 < I2»
  intros
  apply h
  apply KImp.Step.«I1 < I2» <;> assumption
theorem rel.«B1 == B2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«B1 == B2» Q := by
  unfold KImp.Step.Rel.«B1 == B2»
  intros
  apply h
  apply KImp.Step.«B1 == B2» <;> assumption
theorem rel.«I1 == I2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«I1 == I2» Q := by
  unfold KImp.Step.Rel.«I1 == I2»
  intros
  apply h
  apply KImp.Step.«I1 == I2» <;> assumption
theorem rel.«B1 != B2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«B1 != B2» Q := by
  unfold KImp.Step.Rel.«B1 != B2»
  intros
  apply h
  apply KImp.Step.«B1 != B2» <;> assumption
theorem rel.«I1 != I2» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«I1 != I2» Q := by
  unfold KImp.Step.Rel.«I1 != I2»
  intros
  apply h
  apply KImp.Step.«I1 != I2» <;> assumption
theorem rel.«true && B» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«true && B» Q := by
  unfold KImp.Step.Rel.«true && B»
  intros
  apply h
  apply KImp.Step.«true && B» <;> assumption
theorem rel.«false && _» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«false && _» Q := by
  unfold KImp.Step.Rel.«false && _»
  intros
  apply h
  apply KImp.Step.«false && _» <;> assumption
theorem rel.«true || _» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«true || _» Q := by
  unfold KImp.Step.Rel.«true || _»
  intros
  apply h
  apply KImp.Step.«true || _» <;> assumption
theorem rel.«false || B» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«false || B» Q := by
  unfold KImp.Step.Rel.«false || B»
  intros
  apply h
  apply KImp.Step.«false || B» <;> assumption
theorem rel.«CALC.step» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«CALC.step» Q := by
  unfold KImp.Step.Rel.«CALC.step»
  intros
  apply h
  apply KImp.Step.«CALC.step» <;> assumption
theorem rel.«CALC.var» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«CALC.var» Q := by
  unfold KImp.Step.Rel.«CALC.var»
  intros
  apply h
  apply KImp.Step.«CALC.var» <;> assumption
theorem rel.«CALC.assign» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«CALC.assign» Q := by
  unfold KImp.Step.Rel.«CALC.assign»
  intros
  apply h
  apply KImp.Step.«CALC.assign» <;> assumption
theorem rel.«IMP.if-true» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP.if-true» Q := by
  unfold KImp.Step.Rel.«IMP.if-true»
  intros
  apply h
  apply KImp.Step.«IMP.if-true» <;> assumption
theorem rel.«IMP.if-false» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP.if-false» Q := by
  unfold KImp.Step.Rel.«IMP.if-false»
  intros
  apply h
  apply KImp.Step.«IMP.if-false» <;> assumption
theorem rel.«IMP.if-else» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP.if-else» Q := by
  unfold KImp.Step.Rel.«IMP.if-else»
  intros
  apply h
  apply KImp.Step.«IMP.if-else» <;> assumption
theorem rel.«IMP.while» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP.while» Q := by
  unfold KImp.Step.Rel.«IMP.while»
  intros
  apply h
  apply KImp.Step.«IMP.while» <;> assumption
theorem rel.«IMP.block» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP.block» Q := by
  unfold KImp.Step.Rel.«IMP.block»
  intros
  apply h
  apply KImp.Step.«IMP.block» <;> assumption
theorem rel.«IMP.done» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP.done» Q := by
  unfold KImp.Step.Rel.«IMP.done»
  intros
  apply h
  apply KImp.Step.«IMP.done» <;> assumption
theorem rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» <;> assumption
theorem rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» Q := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  intros
  apply h
  apply KImp.Step.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» <;> assumption
theorem rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» Q := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat»
  intros
  apply h
  apply KImp.Step.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» <;> assumption
theorem rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» Q := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool»
  intros
  apply h
  apply KImp.Step.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» <;> assumption
theorem rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» Q := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»
  intros
  apply h
  apply KImp.Step.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» <;> assumption
theorem rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» {Q : KImp.SortGeneratedTopCell → KImp.SortGeneratedTopCell → Prop}
    (h : ∀ {c c'}, KImp.Step c c' → Q c c') : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» Q := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool»
  intros
  apply h
  apply KImp.Step.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» <;> assumption

/-- The relation satisfies the 240 obligations. -/
theorem obligations : Obligations G (Rel G) (Sync G) (Left G) (Right G) where
  init P E₁ E₂ hP hE := by
    refine ⟨_, CK_base G _, ?_, ?_, hE⟩
    · simp only [KImp.init, kOf]; exact CK_base G _
    · simp only [KImp.init, kOf, lk_kseq, litem_false, litem0_inj_Stmt]
      simp [show sec G P = some true from hP]
  final := fun ⟨_, _, _, _, hlow⟩ _ _ => hlow
  cover := by
    rintro c₁ c₂ ⟨K, hc₁, hc₂, hlk, hlow⟩ hnf
    by_cases h₁ : kOf c₁ = K
    · by_cases h₂ : kOf c₂ = K
      · refine Or.inr (Or.inr ⟨⟨h₁.trans h₂.symm, by rw [h₁]; exact hlk, hlow⟩,
          fun hf => hnf ⟨hf, ?_⟩, fun hf => hnf ⟨?_, hf⟩⟩)
        · simp only [Final] at hf ⊢; rw [h₂, ← h₁, hf]
        · simp only [Final] at hf ⊢; rw [h₁, ← h₂, hf]
      · exact Or.inr (Or.inl ⟨⟨K, h₁, hc₂, h₂, hlk, hlow⟩, ne_dotk_of_CK hc₂ h₂⟩)
    · exact Or.inl ⟨⟨K, hc₁, h₁, hc₂, hlk, hlow⟩, ne_dotk_of_CK hc₁ h₁⟩
  «sync:- X» := rel.«- X» sync_all
  «left:- X» := rel.«- X» left_all
  «right:- X» := rel.«- X» right_all
  «sync:! B» := rel.«! B» sync_all
  «left:! B» := rel.«! B» left_all
  «right:! B» := rel.«! B» right_all
  «sync:X + Y» := rel.«X + Y» sync_all
  «left:X + Y» := rel.«X + Y» left_all
  «right:X + Y» := rel.«X + Y» right_all
  «sync:X - Y» := rel.«X - Y» sync_all
  «left:X - Y» := rel.«X - Y» left_all
  «right:X - Y» := rel.«X - Y» right_all
  «sync:X * Y» := rel.«X * Y» sync_all
  «left:X * Y» := rel.«X * Y» left_all
  «right:X * Y» := rel.«X * Y» right_all
  «sync:X / Y» := rel.«X / Y» sync_all
  «left:X / Y» := rel.«X / Y» left_all
  «right:X / Y» := rel.«X / Y» right_all
  «sync:I1 >= I2» := rel.«I1 >= I2» sync_all
  «left:I1 >= I2» := rel.«I1 >= I2» left_all
  «right:I1 >= I2» := rel.«I1 >= I2» right_all
  «sync:I1 > I2» := rel.«I1 > I2» sync_all
  «left:I1 > I2» := rel.«I1 > I2» left_all
  «right:I1 > I2» := rel.«I1 > I2» right_all
  «sync:I1 <= I2» := rel.«I1 <= I2» sync_all
  «left:I1 <= I2» := rel.«I1 <= I2» left_all
  «right:I1 <= I2» := rel.«I1 <= I2» right_all
  «sync:I1 < I2» := rel.«I1 < I2» sync_all
  «left:I1 < I2» := rel.«I1 < I2» left_all
  «right:I1 < I2» := rel.«I1 < I2» right_all
  «sync:B1 == B2» := rel.«B1 == B2» sync_all
  «left:B1 == B2» := rel.«B1 == B2» left_all
  «right:B1 == B2» := rel.«B1 == B2» right_all
  «sync:I1 == I2» := rel.«I1 == I2» sync_all
  «left:I1 == I2» := rel.«I1 == I2» left_all
  «right:I1 == I2» := rel.«I1 == I2» right_all
  «sync:B1 != B2» := rel.«B1 != B2» sync_all
  «left:B1 != B2» := rel.«B1 != B2» left_all
  «right:B1 != B2» := rel.«B1 != B2» right_all
  «sync:I1 != I2» := rel.«I1 != I2» sync_all
  «left:I1 != I2» := rel.«I1 != I2» left_all
  «right:I1 != I2» := rel.«I1 != I2» right_all
  «sync:true && B» := rel.«true && B» sync_all
  «left:true && B» := rel.«true && B» left_all
  «right:true && B» := rel.«true && B» right_all
  «sync:false && _» := rel.«false && _» sync_all
  «left:false && _» := rel.«false && _» left_all
  «right:false && _» := rel.«false && _» right_all
  «sync:true || _» := rel.«true || _» sync_all
  «left:true || _» := rel.«true || _» left_all
  «right:true || _» := rel.«true || _» right_all
  «sync:false || B» := rel.«false || B» sync_all
  «left:false || B» := rel.«false || B» left_all
  «right:false || B» := rel.«false || B» right_all
  «sync:CALC.step» := rel.«CALC.step» sync_all
  «left:CALC.step» := rel.«CALC.step» left_all
  «right:CALC.step» := rel.«CALC.step» right_all
  «sync:CALC.var» := rel.«CALC.var» sync_all
  «left:CALC.var» := rel.«CALC.var» left_all
  «right:CALC.var» := rel.«CALC.var» right_all
  «sync:CALC.assign» := rel.«CALC.assign» sync_all
  «left:CALC.assign» := rel.«CALC.assign» left_all
  «right:CALC.assign» := rel.«CALC.assign» right_all
  «sync:IMP.if-true» := rel.«IMP.if-true» sync_all
  «left:IMP.if-true» := rel.«IMP.if-true» left_all
  «right:IMP.if-true» := rel.«IMP.if-true» right_all
  «sync:IMP.if-false» := rel.«IMP.if-false» sync_all
  «left:IMP.if-false» := rel.«IMP.if-false» left_all
  «right:IMP.if-false» := rel.«IMP.if-false» right_all
  «sync:IMP.if-else» := rel.«IMP.if-else» sync_all
  «left:IMP.if-else» := rel.«IMP.if-else» left_all
  «right:IMP.if-else» := rel.«IMP.if-else» right_all
  «sync:IMP.while» := rel.«IMP.while» sync_all
  «left:IMP.while» := rel.«IMP.while» left_all
  «right:IMP.while» := rel.«IMP.while» right_all
  «sync:IMP.block» := rel.«IMP.block» sync_all
  «left:IMP.block» := rel.«IMP.block» left_all
  «right:IMP.block» := rel.«IMP.block» right_all
  «sync:IMP.done» := rel.«IMP.done» sync_all
  «left:IMP.done» := rel.«IMP.done» left_all
  «right:IMP.done» := rel.«IMP.done» right_all
  «sync:EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» := rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» := rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» := rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» := rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» := rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» := rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» := rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» := rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» := rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» := rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» := rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» := rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» sync_all
  «left:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» left_all
  «right:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» right_all
  «sync:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» sync_all
  «left:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» left_all
  «right:EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» := rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» right_all
  «sync:EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» sync_all
  «left:EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» left_all
  «right:EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» := rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» right_all
  «sync:EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» sync_all
  «left:EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» left_all
  «right:EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» := rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» right_all
  «sync:CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» := rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» sync_all
  «left:CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» := rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» left_all
  «right:CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» := rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» right_all
  «sync:CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» := rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» sync_all
  «left:CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» := rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» left_all
  «right:CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» := rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» right_all
  «sync:IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» := rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» sync_all
  «left:IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» := rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» left_all
  «right:IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» := rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» right_all
  «sync:IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» := rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» sync_all
  «left:IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» := rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» left_all
  «right:IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» := rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» right_all

/-- Termination-insensitive noninterference for kimp and the checker `k/imp-sec.k`. -/
theorem kimp_noninterference {P : KImp.SortStmt} {E₁ E₂ : KImp.SortMap}
    (hP : secure G P) (hE : lowEq G E₁ E₂) {f₁ f₂ : KImp.SortGeneratedTopCell}
    (h₁ : Star KImp.Step (KImp.init P E₁) f₁) (hf₁ : Final f₁)
    (h₂ : Star KImp.Step (KImp.init P E₂) f₂) (hf₂ : Final f₂) :
    lowEq G (storeOf f₁) (storeOf f₂) :=
  noninterference G obligations hP hE h₁ hf₁ h₂ hf₂

#k2l_assert_axioms cq_step sq_step same_step obligations kimp_noninterference

end ImpNI
