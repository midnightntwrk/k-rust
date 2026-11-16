/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Pattern
import MatchingLogic.Proof



namespace ML

set_option autoImplicit false

/--
  Typeclass for signatures `𝕊` containing the definedness symbol,
  we name it `defined`.
-/
class HasDefined (𝕊 : Type) where
  defined : 𝕊

/--
  The canonical signature having `definedness` as its only symbol.
-/
inductive Definedness where
| defined

instance : HasDefined Definedness := ⟨Definedness.defined⟩

/-- Notation for `Pattern.symbol HasDefined.defined` -/
notation "⌈" φ "⌉" => (Pattern.symbol HasDefined.defined) ⬝ φ

/--
  The definedness axiom, named simply `definedness`:
  `∀ x. ⌈x⌉`
-/
def definedness {𝕊} [HasDefined 𝕊] {x : EVar} : Pattern 𝕊 := ∀∀ x ⌈.evar x⌉

section variable {𝕊 : Type} [HasDefined 𝕊]

  def total (φ : Pattern 𝕊) : Pattern 𝕊 := ∼⌈∼φ⌉
  notation "⌊" φ "⌋" => total φ

  def equal (φ ψ : Pattern 𝕊) : Pattern 𝕊 := ⌊φ ⇔ ψ⌋
  infix:50 " ≡ "  => equal

  def member (x : EVar) (φ : Pattern 𝕊) : Pattern 𝕊 := ⌈.evar x ⋀ φ⌉
  infix:50 " ∈∈ " => member

  def included (φ ψ : Pattern 𝕊) : Pattern 𝕊 := ⌊φ ⇒ ψ⌋
  infix:50 " ⊆⊆ " => included

end

/--
  A set of premises `Γ` over a signature `𝕊` that contains the
  `defined` symbol satisfies `HasDefinedness` if the definedness axioms belogns to `Γ`.
-/
class HasDefinedness {𝕊} [HasDefined 𝕊] (Γ : Premises 𝕊) where
  hasDefinedness : ∀ {x}, @definedness _ _ x ∈ Γ

/--
  Application context of the form `⌈□⌉`.
-/
def AppContext.CtxDefined {𝕊} [HasDefined 𝕊]: AppContext 𝕊 := .left (Pattern.symbol HasDefined.defined) .empty


section PrettyPrinting
  open Lean PrettyPrinter Delaborator SubExpr

  /-
    There has to be a sane way to do this so that it handles namespaces
  -/
  def isApplicationOfDefinedSymbolToPattern : TSyntax `term → Bool
  | `(ML.Pattern.symbol HasDefined.defined)
  | `(ML.Pattern.symbol bdefined)
  | `(Pattern.symbol ML.HasDefined.defined)
  | `(Pattern.symbol HasDefined.defined)
  | `(Pattern.symbol Mdefined)
  | `(symbol ML.HasDefined.defined)
  | `(symbol HasDefined.defined)
  | `(symbol defined) => true
  | _ => false

  /--
    Forces the pretty printing of `(symbol defined) ; φ` as `⌈φ⌉`.
  -/
  @[delab app.ML.Pattern.application] def delabDefined : Delab := do
    let e ← getExpr
    guard $ e.getAppNumArgs == 3
    let signature ← withAppFn $ withAppFn $ withAppArg $ Delaborator.delab
    let first ← withAppFn $ withAppArg Delaborator.delab
    let second ← withAppArg Delaborator.delab
    if isApplicationOfDefinedSymbolToPattern first then
      `(⌈$second⌉)
    else
      `($first ⬝ $second)

end PrettyPrinting


section Equality
  open Proof
  variable {𝕊 : Type} [HasDefined 𝕊] {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {C : AppContext 𝕊}

  def equivImplEqual :
    Γ ⊢ φ ⇔ ψ →
    Γ ⊢ (φ ≡ ψ)
    :=
    fun l₁ : Γ ⊢ φ ⇔ ψ =>
    let l₂ : Γ ⊢ ∼⌈∼(φ ⇔ ψ)⌉ := (doubleNegCtx (C := .left _ .empty)) l₁
    let l₃ : Γ ⊢ φ ≡ ψ := l₂
    l₃

  def equalSelf :
    Γ ⊢ φ ≡ φ :=
    let l₁ : Γ ⊢ φ ⇔ φ := equivSelf
    let l₂ : Γ ⊢ φ ≡ φ := (equivImplEqual) l₁
    l₂

  variable [HasDefinedness Γ]

  def definedness' {x : EVar} : Γ ⊢ ⌈.evar x⌉ :=
    let l₁ : Γ ⊢ ∀∀ x ⌈.evar x⌉ := premise (by autopos) HasDefinedness.hasDefinedness
    let l₂ : Γ ⊢ ∀∀ x ⌈.evar x⌉ ⇒ ⌈.evar x⌉.substEvar x (.evar x) := @univQuan _ _ (⌈.evar x⌉) x x (Pattern.substitutable_evar_same _ _)
    let l₃ : Γ ⊢ ∀∀ x ⌈.evar x⌉ ⇒ ⌈.evar x⌉ := by rw [Pattern.subst_var_var_eq_self_evar] at l₂ ; exact l₂
    modusPonens l₁ l₃

end Equality

section Membership
  open Proof
  variable {𝕊 : Type} [HasDefined 𝕊] {Γ : Premises 𝕊}  [HasDefinedness Γ] {φ ψ χ : Pattern 𝕊} {C : AppContext 𝕊}

  def memberIntro {x : EVar} :
    Γ ⊢ φ →
    Γ ⊢ ∀∀ x (x ∈∈ φ)
    :=
    fun l₁ : Γ ⊢ φ =>
    let l₂ : Γ ⊢ .evar x ⇒ φ := (extraPremise) l₁
    let l₃ : Γ ⊢ .evar x ⇒ .evar x := implSelf
    let l₄ : Γ ⊢ .evar x ⇒ .evar x ⋀ φ := toRule (toRule conjIntro l₃) l₂
    let l₅ : Γ ⊢ ⌈.evar x⌉ ⇒ ⌈.evar x ⋀ φ⌉ := (framing (C := .left _ .empty)) l₄
    let l₆ : Γ ⊢ ⌈.evar x⌉ := definedness'
    let l₇ : Γ ⊢ ⌈.evar x ⋀ φ⌉ := modusPonens l₆ l₅
    let l₈ : Γ ⊢ x ∈∈ φ := l₇
    let l₈ : Γ ⊢ ∀∀ x (x ∈∈ φ) := (univGeneralization) l₈
    l₈

  -- def memberElim {x : EVar} {φ : Pattern 𝕊} : Γ ⊢ ∀∀ x (x ∈∈ φ) → Γ ⊢ φ :=
  --   fun l₁ =>
  --   let l₂ : Γ ⊢ (∀∀ x (x ∈∈ φ)) ⇒ (x ∈∈ φ) := univImplSelf
  --   let l₃ : Γ ⊢ x ∈∈ φ := modusPonens l₁ l₂
  --   let l₄ : Γ ⊢ ⌈x ⋀ φ⌉ := l₃
  --   let l₅ : Γ ⊢ ∼(⌈x ⋀ φ⌉ ⋀ (x ⋀ ∼φ)) := singleton (C₁ := .CtxDefined) (C₂ := .empty)
  --   let l₆ : Γ ⊢ ⌈x ⋀ φ⌉ ⇒ (x ⇒ φ) :=
  --     have : ∀ {p q r : Pattern 𝕊}, Γ ⊢ ∼(p ⋀ (q ⋀ ∼r)) ⇒ (p ⇒ (q ⇒ r)) := @fun p q r => tautology <| by
  --       intros _ _ _ _ _
  --       simp_all
  --     toRule this l₅
  --   let l₇ : Γ ⊢ x ⇒ φ := modusPonens l₄ l₆
  --   let l₈ : Γ ⊢ ∀∀ x (x ⇒ φ) := univGeneralization l₇
  --   let l₉ : Γ ⊢ ∃∃ x x ⇒ φ := sorry --fol
  --   modusPonens existence l₉

  def memberVarLeft {x y : EVar} : Γ ⊢ (x ≡ y) ⇒ (x ∈∈ y) :=
    let l₁ : Γ ⊢ ⌈x⌉ := definedness'
    let l₂ : Γ ⊢ ⌈x⌉ ⋁ ⌈y⌉ := toRule disjIntroLeft l₁
    let l₃ : Γ ⊢ ⌈x ⋁ y⌉ := toRule (propagationDisjR (C := .CtxDefined)) l₂
    let l₄ : ∀ {p q : Pattern 𝕊}, Γ ⊢ p ⋁ q ⇒ ∼(p ⇔ q) ⋁ (p ⋀ q) := tautology <| by
      intros _ _ _ _ _
      taut_morphism
    let l₅ : Γ ⊢ x ⋁ y ⇒ ∼(x ⇔ y) ⋁ (x ⋀ y) := l₄
    let l₆ : Γ ⊢ ⌈x ⋁ y⌉ ⇒ ⌈∼(x ⇔ y) ⋁ (x ⋀ y)⌉ := framing (C := .CtxDefined) l₅
    let l₇ : Γ ⊢ ⌈∼(x ⇔ y) ⋁ (x ⋀ y)⌉ := modusPonens l₃ l₆
    let l₈ : Γ ⊢ ⌈∼(x ⇔ y)⌉ ⋁ ⌈(x ⋀ y)⌉ := toRule (propagationDisj (C := .CtxDefined)) l₇
    l₈
    -- works definitionally; I leave the proof for reference
    -- by
    --   have : ⌈x ⋀ y⌉ = (x ∈∈ y : Pattern 𝕊) := rfl
    --   rw [this] at l₈
    --   have : ∼⌈∼(x ⇔ y)⌉ = (x ≡ y : Pattern 𝕊) := rfl
    --   rw [this] at l₈

  -- def memberVarRight {x y : EVar} : Γ ⊢ (x ∈∈ y) ⇒ (x ≡ y) :=
  --   let l₁ : Γ ⊢ ∼(⌈x ⋀ y⌉ ⋀ ⌈x ⋀ ∼y⌉) := singleton (C₁ := .CtxDefined) (C₂ := .CtxDefined)
  --   let l₂ : Γ ⊢ ∼(⌈y ⋀ x⌉ ⋀ ⌈y ⋀ ∼x⌉) := singleton (C₁ := .CtxDefined) (C₂ := .CtxDefined)
  --   let l₃ : Γ ⊢ ⌈x ⋀ y⌉ ⇒ ∼⌈x ⋀ ∼y⌉ := toRule negConjAsImpl l₂
  --   _


  -- def memberVar {x y : EVar} : Γ ⊢ (x ∈∈ y) ≡ (x ≡ y) := sorry

  -- def memberNegLeft {x y : EVar} : Γ ⊢ (x ∈∈ ∼φ) ⇒ ∼(x ∈∈ φ) :=
  --   let l₁ : Γ ⊢ ∼(⌈x ⋀ φ⌉ ⋀ ⌈x ⋀ ∼φ⌉) := singleton (C₁ := .CtxDefined) (C₂ := .CtxDefined)
  --   let l₂ : Γ ⊢ ∼(⌈x ⋀ ∼φ⌉ ⋀ ⌈x ⋀ φ⌉) := sorry --prop
  --   let l₃ : Γ ⊢ ⌈x ⋀ ∼φ⌉ ⇒ ∼⌈x ⋀ φ⌉ := toRule negConjAsImpl l₂
  --   l₃

  def memberNegRight {x y : EVar} : Γ ⊢ ∼(x ∈∈ φ) ⇒ (x ∈∈ ∼φ) :=
    let l₁ : Γ ⊢ ⌈x⌉ := definedness'
    let l₂ : ∀ p q : Pattern 𝕊, Γ ⊢ p ⇒ ((p ⋀ q) ⋁ (p ⋀ ∼q)) := fun p q => tautology <| by
      intros _ _ _ _ _
      simp_all
    let l₃ : Γ ⊢ ⌈x⌉ ⇒ ⌈(x ⋀ φ) ⋁ (x ⋀ ∼φ)⌉ := framingRight (l₂ _ _)
    let l₄ : Γ ⊢ ⌈(x ⋀ φ) ⋁ (x ⋀ ∼φ)⌉ := toRule l₃ l₁
    let l₅ : Γ ⊢ ⌈(x ⋀ φ)⌉ ⋁ ⌈(x ⋀ ∼φ)⌉ := toRule (propagationDisj (C := .CtxDefined)) l₄
    let l₆ : Γ ⊢ ∼⌈(x ⋀ φ)⌉ ⇒ ⌈(x ⋀ ∼φ)⌉ := l₅ --by the definition of disjunction
    l₆

  def memberDistribCDisjLeft {x : EVar} {φ ψ : EVar} : Γ ⊢ (x ∈∈ φ ⋁ ψ) ⇒ (x ∈∈ φ) ⋁ (x ∈∈ ψ) :=
    let l₁ : Γ ⊢ x ⋀ (φ ⋁ ψ) ⇒ (x ⋀ φ) ⋁ (x ⋀ ψ) := tautology <| by intros _ _ _ _ _ ; simp_all
    let l₂ : Γ ⊢ ⌈x ⋀ (φ ⋁ ψ)⌉ ⇒ ⌈(x ⋀ φ) ⋁ (x ⋀ ψ)⌉ := framingRight l₁
    let l₃ : Γ ⊢ ⌈(x ⋀ φ) ⋁ (x ⋀ ψ)⌉ ⇒ ⌈(x ⋀ φ)⌉ ⋁ ⌈(x ⋀ ψ)⌉ := (propagationDisj (C := .CtxDefined))
    let l₄ : Γ ⊢ ⌈x ⋀ (φ ⋁ ψ)⌉ ⇒ ⌈(x ⋀ φ)⌉ ⋁ ⌈(x ⋀ ψ)⌉ := syllogism l₂ l₃
    l₄

  -- def memberDistribCDisjRight {x : EVar} {φ ψ : EVar} : Γ ⊢ (x ∈∈ φ) ⋁ (x ∈∈ ψ) ⇒ (x ∈∈ φ ⋁ ψ) := sorry


  -- def memberExist {x y : EVar} {φ : Pattern 𝕊} (h : x ≠ y) : Γ ⊢ (x ∈∈ ∃∃ y φ) ≡ (∃∃ y (x ∈∈ φ)) := sorry

end Membership




section ContextReasoning
  open Proof
  variable {𝕊 : Type} [HasDefined 𝕊] {Γ : Premises 𝕊} [HasDefinedness Γ] {φ ψ χ : Pattern 𝕊} {C : AppContext 𝕊}

  def auxTauto {δ θ} : Γ ⊢ δ ⋁ θ ⇒ δ ⋀ ∼θ ⋁ θ := tautology <| by
        intros M _ f _ m
        simp only [Morphism.morphism_impl, Morphism.morphism_disj, Morphism.morphism_conj, Morphism.morphism_neg]
        intros h
        have := Classical.em <| f θ m
        cases this
        . apply Or.inr
          assumption
        . apply Or.inl
          cases h
          . trivial
          . contradiction

  theorem AppContext.not_in_free_evars_insert {x : EVar} : x ∉ φ.evars ++ C.evars → ¬φ.isFreeEvar x ∧ ¬C.isFreeEvar x := by
    intros h
    apply And.intro
    .
      have : x ∉ φ.evars ++ C.evars := h
      rw [←Pattern.free_evar_equiv_def]
      rw [List.mem_append] at this
      revert this
      rw [←contraposition]
      intros h
      rw [Pattern.free_evar_equiv_def] at h
      rw [Pattern.evar_equiv_def]
      exact Or.inl (Pattern.evar_of_free_evar h)
    .
      have : x ∉ φ.evars ++ C.evars := h
      rw [List.mem_append] at this
      revert this
      rw [←contraposition]
      intros h
      rw [AppContext.evar_equiv_def]
      exact Or.inr (AppContext.evar_of_free_evar h)

  -- #exit

  def ctxImplDefinedAux1 (x : EVar) : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉ :=
    let l₁ : Γ ⊢ ⌈x⌉ := definedness'
    let l₂ : Γ ⊢ ⌈x⌉ ⋁ ⌈φ⌉ := modusPonens l₁ (disjIntroLeft)
    let l₃ : Γ ⊢ ⌈x ⋁ φ⌉ := toRule (propagationDisjR (C := .CtxDefined)) l₂
    let l₄ : Γ ⊢ ⌈(x ⋀ ∼φ) ⋁ φ⌉ :=
      let l₁' : Γ ⊢ x ⋁ φ ⇒ (x ⋀ ∼φ) ⋁ φ := auxTauto
      let l₂' : Γ ⊢ ⌈x ⋁ φ⌉ ⇒ ⌈(x ⋀ ∼φ) ⋁ φ⌉ := (framingRight) l₁'
      toRule l₂' l₃
    let l₅ : Γ ⊢ ⌈x ⋀ ∼φ⌉ ⋁ ⌈φ⌉ := toRule (propagationDisj (C := .CtxDefined)) l₄
    let l₆ : Γ ⊢ C[x ⋀ φ] ⇒ ∼⌈x ⋀ ∼φ⌉ :=
      let l₁' : Γ ⊢ ∼(C[x ⋀ φ] ⋀ ⌈x ⋀ ∼φ⌉) := (singleton (C₁ := C) (C₂ := .CtxDefined))
      let l₂' : Γ ⊢ C[x ⋀ φ] ⇒ ∼⌈x ⋀ ∼φ⌉ := toRule (negConjAsImpl) l₁'
      l₂'
    let l₇ : Γ ⊢ ∼⌈x ⋀ ∼φ⌉ ⇒ ⌈φ⌉ := l₅
    let l₈ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉ := (syllogism) l₆ l₇
    let l₉ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉ := l₈
    l₉


  def ctxImplDefined : Γ ⊢ C[φ] ⇒ ⌈φ⌉ :=
    let x : EVar := EVar.getFresh (φ.evars ++ C.evars)
    have not_fv_φ : ¬φ.isFreeEvar x := And.left <| AppContext.not_in_free_evars_insert (EVar.get_fresh_is_fresh _)
    have not_fv_C : ¬C.isFreeEvar x := And.right <| AppContext.not_in_free_evars_insert (EVar.get_fresh_is_fresh _)
    let l₉ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉ := (ctxImplDefinedAux1) x
    let l₁₀ : Γ ⊢ ∃∃ x (C[x ⋀ φ]) ⇒ ⌈φ⌉ := existGen (by simp_all) l₉
    let l₁₁ : Γ ⊢ φ ⇒ (∃∃ x (x)) ⋀ φ :=
      let l₁' : Γ ⊢ φ ⇒ φ := (implSelf)
      let l₂' : Γ ⊢ ∃∃ x (x) := existence
      let l₃' : Γ ⊢ φ ⇒ ∃∃ x x := (extraPremise) l₂'
      let l₄' : Γ ⊢ φ ⇒ (∃∃ x x) ⋀ φ := (conjIntroRule) l₃' l₁'
      l₄'
    let l₁₂ : Γ ⊢ φ ⇒ ∃∃ x (x ⋀ φ) := (syllogism) l₁₁ ((pushConjInExist) not_fv_φ)
    let l₁₃ : Γ ⊢ C[φ] ⇒ C[(∃∃ x (x ⋀ φ))] := (framing) l₁₂
    let l₁₄ : Γ ⊢ C[(∃∃ x (x ⋀ φ))] ⇒ ⌈φ⌉ :=
      let l₁' : Γ ⊢ C[(∃∃ x (x ⋀ φ))] ⇒ ∃∃ x (C[x ⋀ φ]) := (propagationExist) not_fv_C
      (syllogism) l₁' l₁₀
    let l₁₅ : Γ ⊢ C[φ] ⇒ ⌈φ⌉ := (syllogism) l₁₃ l₁₄
    l₁₅

  def implDefined : Γ ⊢ φ ⇒ ⌈φ⌉ := ctxImplDefined (C := .empty)

  def totalImpl : Γ ⊢ ⌊φ⌋ ⇒ φ :=
    let l₁ : Γ ⊢ ∼φ ⇒ ⌈∼φ⌉ := implDefined
    let l₂ : Γ ⊢ ∼⌈∼φ⌉ ⇒ ∼∼φ := (negImplIntro) l₁
    let l₃ : Γ ⊢ ⌊φ⌋ ⇒ ∼∼φ := l₂
    (syllogism) l₃ (doubleNegElim)

end ContextReasoning
