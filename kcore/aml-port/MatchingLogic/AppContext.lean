/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Pattern 
import MatchingLogic.Substitution
import MatchingLogic.Positivity

set_option autoImplicit false 

namespace ML 

/--
  The type of application contexts.
  Application contexts are inductively constructed starting with `□`
  and applying patterns to the left or to the right. 
  For example, `φ ⬝ (ψ ⬝ (□ ⬝ χ))` represents an application context.
  The intention is to then substiute `□` by a pattern, transforming the application context 
  into a concrete pattern of its respective shape.
-/
inductive AppContext (𝕊 : Type) where 
| empty : AppContext 𝕊
| left : Pattern 𝕊 → AppContext 𝕊 → AppContext 𝕊
| right : Pattern 𝕊 → AppContext 𝕊 → AppContext 𝕊 
deriving Inhabited, DecidableEq, Repr 

namespace AppContext 

variable {𝕊 : Type}

/--
  Substitutes the `□` in an application context by a pattern,
  thus realizing the application context into a concrete pattern.
-/
@[simp]
def insert (φ : Pattern 𝕊) : AppContext 𝕊 → Pattern 𝕊
| empty => φ
| left ψ C'=> ψ ⬝ (C'.insert φ)
| right ψ C' => (C'.insert φ) ⬝ ψ

/-- Notation for `AppContext.insert`-/
notation C "[" φ "]" => insert φ C
/-- Notation for `AppContext.empty` -/
notation "□" => empty
/-- Notation for `C.right φ` -/
notation C "<⬝" φ => AppContext.right φ C
/-- Notation for `C.left φ` -/
notation φ "⬝>" C => AppContext.left φ C

@[simp]
def insertLeftAtBox (φ : Pattern 𝕊) : AppContext 𝕊 → AppContext 𝕊 
| empty => left φ empty 
| left ψ C => left ψ (C.insertLeftAtBox φ)
| right ψ C => right ψ (C.insertLeftAtBox φ)

variable {C : AppContext 𝕊} {φ ψ : Pattern 𝕊}

@[simp]
theorem insert_left_at_box : (C.insertLeftAtBox φ).insert ψ = C.insert (φ ⬝ ψ) := by 
  induction C 
  all_goals simp [*]

/--
  Lifts a self-mapping of patterns to a self-mapping of application contexts.
-/
@[simp]
def map (f : Pattern 𝕊 → Pattern 𝕊) : AppContext 𝕊 → AppContext 𝕊
| empty => empty 
| left ψ C => left (f ψ) (map f C)
| right ψ C => right (f ψ) (map f C)



/--
  Return all patterns that compose an application context, as a list.
-/
def toList : AppContext 𝕊 → List (Pattern 𝕊) 
| empty => []
| left χ C | right χ C => χ :: C.toList 

@[simp]
def evars (C : AppContext 𝕊) : List EVar :=
match C with 
| □ => []
| left φ C | right φ C => φ.evars ++ C.evars

@[simp]
def isEvar (C : AppContext 𝕊) (x : EVar) : Bool := 
match C with 
| □ => false 
| left φ C | right φ C => φ.isEvar x ∨ C.isEvar x

theorem evar_equiv_def (C : AppContext 𝕊) (x : EVar) : x ∈ C.evars ↔ C.isEvar x := by 
  induction C <;> simp [*, Pattern.evar_equiv_def] at * 

@[simp]
def isFreeEvar (C : AppContext 𝕊) (x : EVar) : Bool :=
match C with 
| □ => false 
| left φ C | right φ C => φ.isFreeEvar x ∨ C.isFreeEvar x

theorem evar_of_free_evar {C : AppContext 𝕊} {x : EVar} : C.isFreeEvar x → C.isEvar x := by 
  intros h 
  induction C with 
  | empty => simp [*] at *
  | left φ C' ih | right φ C' ih => 
    simp at h 
    cases h 
    . simp [*, Pattern.evar_of_free_evar] at *
    . specialize ih (by assumption)
      simp [*] at *

@[simp]
theorem no_free_occ_left {C : AppContext 𝕊} {χ : Pattern 𝕊} {x : EVar} : ¬(C.left χ).isFreeEvar x ↔ ¬χ.isFreeEvar x ∧ ¬C.isFreeEvar x := by 
  apply Iff.intro 
  . intros h 
    simp_all
  . intros h 
    simp [*]

@[simp]
theorem no_free_occ_right {C : AppContext 𝕊} {χ : Pattern 𝕊} {x : EVar} : ¬(C.right χ).isFreeEvar x ↔ ¬χ.isFreeEvar x ∧ ¬C.isFreeEvar x := by 
  apply Iff.intro 
  . intros h 
    simp_all
  . intros h 
    simp [*]

@[simp]
theorem no_free_occ_evar_insert {C : AppContext 𝕊} {φ : Pattern 𝕊} {x : EVar} : ¬C[φ].isFreeEvar x ↔ ¬φ.isFreeEvar x ∧ ¬C.isFreeEvar x := by 
  apply Iff.intro 
  . intros h 
    induction C with 
    | empty => simp [*] at * ; assumption 
    | left χ C' ih  => 
      apply And.intro 
      . simp at * 
        specialize ih h.2 
        exact ih.1 
      . simp at * 
        specialize ih h.2
        exact ⟨h.1, ih.2⟩
    | right χ C' ih  => 
      apply And.intro 
      . simp at * 
        specialize ih h.1
        exact ih.1 
      . simp at * 
        specialize ih h.1
        exact ⟨h.2, ih.2⟩
  . intros h 
    induction C with 
    | empty => simp [*] at * 
    | left χ C' ih => 
      cases h with | intro h₁ h₂ =>
      rw [no_free_occ_left] at h₂
      specialize ih ⟨h₁, h₂.2⟩
      simp [*]
     | right χ C' ih => 
      cases h with | intro h₁ h₂ =>
      rw [no_free_occ_right] at h₂
      specialize ih ⟨h₁, h₂.2⟩
      simp [*]
    
      



      




@[simp]
def substEvar (C : AppContext 𝕊) (x : EVar) (ψ : Pattern 𝕊) : AppContext 𝕊 := 
match C with 
| empty => empty  
| left χ C' => left (χ.substEvar x ψ) (C'.substEvar x ψ)
| right χ C' => right (χ.substEvar x ψ) (C'.substEvar x ψ)

notation C "[" x "⇐ᵉ" ψ "]ᶜ" => substEvar C x ψ


theorem subst_evar_insert {C : AppContext 𝕊} {x : EVar} {φ : Pattern 𝕊} {ψ : Pattern 𝕊} : C[φ][x ⇐ ψ]ᵉ = C[x ⇐ᵉ ψ]ᶜ[φ[x ⇐ ψ]ᵉ] := by 
  induction C <;> simp [*]

@[simp]
theorem subst_var_var_eq_self_evar {C : AppContext 𝕊} {x : EVar} : C[x ⇐ᵉ x]ᶜ = C := by 
  induction C with 
  | _ => simp [*]

section ContextPositivity

  inductive Positive : AppContext 𝕊 → Prop where 
  | empty : Positive empty 
  | left (φ : Pattern 𝕊) (C) : φ.Positive → Positive C → Positive (left φ C)
  | right (φ : Pattern 𝕊) (C) : φ.Positive → Positive C → Positive (right φ C)

  theorem wf_insert {C : AppContext 𝕊} {φ} :
    C.Positive → φ.Positive → C[φ].Positive := by 
    intros wfC wfφ 
    induction C with 
    | empty => simp [*]
    | left χ C ih | right χ C ih => 
      cases wfC 
      specialize ih (by assumption)      
      constructor <;> assumption

end ContextPositivity

macro_rules 
| `(tactic| autopos) => `(tactic| (try apply AppContext.wf_insert <;> autopos) ; done)
