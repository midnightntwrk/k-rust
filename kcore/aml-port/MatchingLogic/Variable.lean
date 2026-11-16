/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Util

set_option autoImplicit false

namespace ML

@[simp]
def getFresh : List ℕ → ℕ
| [] => 0 
| .cons x xs => (max x (getFresh xs)) + 1 

theorem lt_get_fresh {xs : List ℕ} {x : ℕ} (h : x ∈ xs) : x < getFresh xs := by 
  induction xs with 
  | nil => simp at h 
  | cons hd tl ih => 
    cases h with 
    | head => 
      dsimp
      have : x ≤ max x (getFresh tl) := Nat.le_max_left x (getFresh tl)
      exact Nat.lt_succ_of_le this
    | tail _ hmem => 
      dsimp 
      specialize ih hmem
      have : getFresh tl ≤ max hd (getFresh tl) := Nat.le_max_right hd (getFresh tl)
      have := Nat.le_trans (Nat.le_of_lt ih) this 
      exact Nat.lt_succ_of_le this
      



theorem get_fresh_is_fresh (xs : List ℕ) : getFresh xs ∉ xs := 
  fun h => Nat.lt_irrefl _ $ lt_get_fresh h 

theorem get_fresh_is_fresh' (xs : List ℕ) : ∀ x ∈ xs, getFresh xs ≠ x := by 
  intros x hmem h
  have := get_fresh_is_fresh xs 
  subst h
  contradiction

@[ext]
structure EVar where 
  val : ℕ 
deriving DecidableEq, Inhabited, Repr

namespace EVar 

  instance : ToString EVar where 
    toString x := s!"x{x.val}"

  theorem evar_eq_def (x y : EVar) : x = y ↔ x.val = y.val := by 
    apply Iff.intro <;> intros h 
    . cases h ; rfl
    . ext ; assumption

  @[simp]
  def getFresh : List EVar → EVar 
  | xs => ⟨ML.getFresh <| xs.map EVar.val⟩

  theorem get_fresh_is_fresh' (xs : List EVar) : ∀ x ∈ xs, getFresh xs ≠ x := by 
    intros x hmem h 
    rw [evar_eq_def] at h 
    have := List.mem_map_of_mem (f := EVar.val) hmem    
    exact ML.get_fresh_is_fresh' (xs.map EVar.val) x.val this h

  
  theorem get_fresh_is_fresh (xs : List EVar) : getFresh xs ∉ xs := by 
    intros hmem
    exact get_fresh_is_fresh' xs (getFresh xs) hmem rfl 

end EVar 












@[ext]
structure SVar where 
  val : ℕ
deriving DecidableEq, Inhabited, Repr

namespace SVar 

  instance : ToString SVar where 
    toString X := s!"X{X.val}"

  theorem svar_eq_def (x y : SVar) : x = y ↔ x.val = y.val := by 
    apply Iff.intro <;> intros h 
    . cases h ; rfl
    . ext ; assumption

  @[simp]
  def getFresh : List SVar → SVar 
  | xs => ⟨ML.getFresh $ xs.map SVar.val⟩

  theorem get_fresh_is_fresh' (xs : List SVar) : ∀ x ∈ xs, getFresh xs ≠ x := by 
    intros x hmem h 
    rw [svar_eq_def] at h 
    have := List.mem_map_of_mem (f := SVar.val) hmem    
    exact ML.get_fresh_is_fresh' (xs.map SVar.val) x.val this h

  
  theorem get_fresh_is_fresh (xs : List SVar) : getFresh xs ∉ xs := by 
    intros hmem
    exact get_fresh_is_fresh' xs (getFresh xs) hmem rfl 


end SVar 

