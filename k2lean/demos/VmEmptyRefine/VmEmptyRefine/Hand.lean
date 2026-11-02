import VmEmptyRefine.RefineDefs

/-! The parts that read the cache (`open.txt`): the underflow rules on an empty stack, which read
the stack in `KVmEmpty` and the cache in `KVmEmptyOpt`, and `add`'s priority lemma (`KVmEmptyOpt`'s
`add-underflow0` reads the cache). Each holds under the invariant that the cache is right
(`KVmEmpty.Invariant`, `emptyOk`). -/

set_option maxHeartbeats 0

namespace VmEmptyRefine

open KPrelude

section
open KVmEmpty

/-- The configuration of `KVmEmpty` with these cells. -/
abbrev cfg (k : SortK) (S : SortStack) (e : Bool) (G : SortGeneratedCounterCell) : SortGeneratedTopCell :=
  .«<generatedTop>» (.«<T>» (.«<k>» k) (.«<stack>» S) (.«<empty>» e)) G

/-- The invariant at a configuration: the cache against what the stack's emptiness is. -/
theorem inv_cfg {k S e G} (h : Invariant (cfg k S e G)) :
    (KVmEmpty.K.«isEmpty(_)_VMPRI_Bool_Stack» S).bind (fun r => some (BoolHook.eq e r)) = some true := by
  simpa only [Invariant, Invariant.emptyOk, Invariant.cell_T, Invariant.cell_stack,
    Invariant.content_stack, Invariant.cell_empty, Invariant.content_empty,
    Invariant.emptyOk_cells] using h

/-- On an empty stack the cache says empty. -/
theorem cache_nil {k e G} (h : Invariant (cfg k SortStack.«.Stack» e G)) : e = true := by
  have h := inv_cfg h
  simp only [Eqn.«isEmpty(_)_VMPRI_Bool_Stack_1»] at h
  cases e <;> simp_all [BoolHook.eq]

/-- On a nonempty stack the cache says nonempty. -/
theorem cache_cons {k A S e G} (h : Invariant (cfg k (SortStack.«_:_» A S) e G)) : e = false := by
  have h := inv_cfg h
  simp only [Eqn.«isEmpty(_)_VMPRI_Bool_Stack_2»] at h
  cases e <;> simp_all [BoolHook.eq]

/-- Where the cache says empty, the stack is empty. -/
theorem stack_of_cache {k S G} (h : Invariant (cfg k S true G)) : S = SortStack.«.Stack» := by
  have h := inv_cfg h
  k2l_cases S <;> simp_all [Eqn.«isEmpty(_)_VMPRI_Bool_Stack_1», Eqn.«isEmpty(_)_VMPRI_Bool_Stack_2», BoolHook.eq]

end

theorem fwd_tr.«add-underflow0» : fwd_tr.«add-underflow0».statement := by
  intro K E G hinv
  k2l_cases E with ⟨e⟩
  obtain rfl := cache_nil hinv
  exact Or.inl ⟨_, .single (KVmEmptyOpt.Step.«add-underflow0» _ _ _), Or.inl rfl⟩

theorem fwd_tr.«div-underflow0» : fwd_tr.«div-underflow0».statement := by
  intro K E G hpri hinv
  k2l_cases E with ⟨e⟩
  obtain rfl := cache_nil hinv
  exact Or.inl ⟨_, .single (KVmEmptyOpt.Step.«div-underflow0» _ _ _
    (fun j hj hb => by cases hb <;> omega)), Or.inl rfl⟩

/-- `pop` underflows where neither `pop` nor `pop-last` applies: on an empty stack, where the
cache says empty, and so does the translation's. -/
theorem fwd_tr.«pop-underflow» : fwd_tr.«pop-underflow».statement := by
  intro K Sc E G hpri hinv
  k2l_cases Sc with ⟨S⟩
  k2l_cases E with ⟨e⟩
  k2l_cases S
  · obtain rfl := cache_nil hinv
    exact Or.inl ⟨_, .single (KVmEmptyOpt.Step.«pop-underflow» _ _ _
      (fun j hj hb => by cases hb <;> omega)), Or.inl rfl⟩
  · rename_i rest _
    k2l_cases rest <;>
      exact (hpri 1 (by decide) (by
        first | exact KVmEmpty.App.«pop-last» _ _ _ _ | exact KVmEmpty.App.pop _ _ _ _ _ _)).elim

theorem bwd_tr.«add-underflow0» : bwd_tr.«add-underflow0».statement := by
  intro K Sc G c hinv hd
  k2l_inv
  rename_i G' Sc' K' _ _ _
  k2l_cases Sc' with ⟨S⟩
  obtain rfl := stack_of_cache hinv
  exact Or.inl ⟨_, .single (KVmEmpty.Step.«add-underflow0» _ _ _), Or.inl rfl⟩

theorem bwd_tr.«div-underflow0» : bwd_tr.«div-underflow0».statement := by
  intro K Sc G hpri c hinv hd
  k2l_inv
  rename_i G' Sc' K' _ _ _
  k2l_cases Sc' with ⟨S⟩
  obtain rfl := stack_of_cache hinv
  exact Or.inl ⟨_, .single (KVmEmpty.Step.«div-underflow0» _ _ _
    (fun j hj ha => by cases ha <;> omega)), Or.inl rfl⟩

/-- Where the cache says empty, so is the stack, so neither `pop` nor `pop-last` applies. -/
theorem bwd_tr.«pop-underflow» : bwd_tr.«pop-underflow».statement := by
  intro K Sc G hpri c hinv hd
  k2l_inv
  rename_i G' Sc' K' _ _ _
  k2l_cases Sc' with ⟨S⟩
  obtain rfl := stack_of_cache hinv
  exact Or.inl ⟨_, .single (KVmEmpty.Step.«pop-underflow» _ _ _ _
    (fun j hj ha => by cases ha <;> omega)), Or.inl rfl⟩

/-- `add` applies on a stack of two, where the cache says nonempty: `KVmEmptyOpt`'s
`add-underflow0`, which reads the cache, does not apply at the translation, nor does
`add-underflow1`. -/
theorem pri_fwd.add : pri_fwd.add.statement := by
  intro K A B S E G hpri hinv j hj d hd hb
  k2l_cases E with ⟨e⟩
  obtain rfl := cache_cons hinv
  subst hd
  cases hb <;> omega

end VmEmptyRefine
