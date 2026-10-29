import Handoff.Invariants
import KPrelude.Scaffold

/-! The script's well-formedness, read at the level of the script's claims. The specification is
`wf` in K (`tests/fixtures/handoff/handoff.k`: no claim is named twice), a kind 1 invariant whose
preservation by every rule is generated (`Handoff.Invariant.preserved`). This module states what it
means for the proofs that read it: two pending tasks claim nothing in common (`Wf`,
`wf_of_invariant`), and the initial configuration of a script whose claims are distinct satisfies it
(`invariant_init`). A claim is the `N`-th resume of a process `Q` or the creation of `Q`; K writes
them as the id of the resume's output, `o(Q, N)`, and as `Q` (`claimK`). -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffConf

variable [Handoff.Hooks]

open KPrelude

/-- A claim: the `N`-th resume of the process `Q` (`inl (Q, N)`), or the creation of `Q` (`inr Q`). -/
abbrev Claim := (Int × Int) ⊕ Int

/-- The claim of one instruction. -/
def iclaims : Handoff.SortInstr → List Claim
  | .«new(_,_)» Q _ => [.inr Q]
  | .«resume(_,_,_)» Q N _ => [.inl (Q, N)]
  | _ => []

/-- The claims of the instructions of a program. -/
def pclaims : Handoff.SortPgm → List Claim
  | .«_;_» I P => iclaims I ++ pclaims P
  | _ => []

/-- The claims of a task: those of the instruction or program its `<k>` holds. -/
def claims : Handoff.SortTaskCell → List Claim
  | .«<task>» _ _ (.«<k>» (.kseq (.inj_Instr I) .dotk)) => iclaims I
  | .«<task>» _ _ (.«<k>» (.kseq (.inj_Pgm P) .dotk)) => pclaims P
  | _ => []

/-- The tasks of a configuration. -/
def tasks : Handoff.SortGeneratedTopCell → Handoff.SortTaskCellMap
  | .«<generatedTop>» (.«<T>» (.«<tasks>» m) _ _) _ => m

/-- No claim occurs twice in a map of tasks: not within one task, not in two tasks. -/
def WfM (m : Handoff.SortTaskCellMap) : Prop :=
  (∀ k t, MapHook.lookup m k = some t → (claims t).Nodup) ∧
  (∀ k₁ k₂ t₁ t₂, k₁ ≠ k₂ → MapHook.lookup m k₁ = some t₁ → MapHook.lookup m k₂ = some t₂ →
    ∀ x ∈ claims t₁, x ∉ claims t₂)

/-- The invariant: the tasks' claims are pairwise distinct. -/
def Wf (c : Handoff.SortGeneratedTopCell) : Prop := WfM (tasks c)

/-- A claim as K's `iclaims` writes it: the id of the resume's output, or the process created. -/
def claimK : Claim → Handoff.SortKItem
  | .inl (Q, N) => .inj_Oid (.«o(_,_)» Q N)
  | .inr Q => .inj_Int Q

theorem claimK_inj : Function.Injective claimK := by
  intro a b h
  rcases a with ⟨Q, N⟩ | Q <;> rcases b with ⟨Q', N'⟩ | Q' <;> simp [claimK] at h ⊢ <;>
    (try cases h) <;> (try simp_all) <;> (try rfl)

/-- K's `iclaims` is `iclaims`, written as K writes claims. -/
theorem iclaims_K (I : Handoff.SortInstr) :
    (Handoff.K.«iclaims(_)_HANDOFF_List_Instr» I).map ListIso.toList = some ((iclaims I).map claimK) := by
  k2l_cases I
  all_goals simp [Handoff.Eqn.«iclaims(_)_HANDOFF_List_Instr_1», Handoff.Eqn.«iclaims(_)_HANDOFF_List_Instr_2»,
    iclaims, claimK, ListHook.element, ListIso.toList_ofList]

/-- K's `pclaims` is `pclaims`, written as K writes claims. -/
theorem pclaims_K (P : Handoff.SortPgm) :
    (Handoff.K.«pclaims(_)_HANDOFF_List_Pgm» P).map ListIso.toList = some ((pclaims P).map claimK) := by
  induction P using pclaims.induct with
  | case1 I P ih =>
    rw [Handoff.Eqn.«pclaims(_)_HANDOFF_List_Pgm_1»]
    have hi := iclaims_K I
    cases hI : Handoff.K.«iclaims(_)_HANDOFF_List_Instr» I <;> rw [hI] at hi <;> simp at hi
    cases hP : Handoff.K.«pclaims(_)_HANDOFF_List_Pgm» P <;> rw [hP] at ih <;> simp at ih
    simp [pclaims, ListHook.concat, ListIso.toList_ofList, hi, ih]
  | case2 P h =>
    k2l_cases P
    all_goals first
      | exact (h _ _ rfl).elim
      | (rw [Handoff.Eqn.«pclaims(_)_HANDOFF_List_Pgm_2»]; simp [pclaims, ListHook.unit, ListIso.toList_ofList])

theorem nodup_map {f : Claim → Handoff.SortKItem} (hf : Function.Injective f) :
    ∀ {l : List Claim}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.1 h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_map hf ht⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    exact ha (hf e ▸ hb)

theorem nodup_of_map {f : Claim → Handoff.SortKItem} : ∀ {l : List Claim}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.1 h
    exact List.nodup_cons.2 ⟨fun hm => ha (List.mem_map.2 ⟨a, hm, rfl⟩), nodup_of_map ht⟩

/-- K's `kclaims` where none of its first two equations applies. -/
theorem kclaims_owise {K : Handoff.SortK}
    (h₁ : ∀ I, K = Handoff.SortK.kseq (Handoff.SortKItem.inj_Instr I) Handoff.SortK.dotk → False)
    (h₂ : ∀ P, K = Handoff.SortK.kseq (Handoff.SortKItem.inj_Pgm P) Handoff.SortK.dotk → False) :
    (Handoff.K.«kclaims(_)_HANDOFF_List_K» K).map ListIso.toList = some [] := by
  rw [Handoff.Eqn.«kclaims(_)_HANDOFF_List_K_3» K h₁ h₂]
  simp [ListHook.unit, ListIso.toList_ofList]

/-- A task's claims as the generated invariant reads them (`mclaims_g`) are its claims. -/
theorem g_eq (k : Handoff.SortTidCell) (t : Handoff.SortTaskCell) :
    (Handoff.Invariant.mclaims_g k t).map ListIso.toList = some ((claims t).map claimK) := by
  k2l_cases t with ⟨⟨_⟩, ⟨_⟩, ⟨_⟩⟩
  simp only [Handoff.Invariant.mclaims_g, Handoff.Invariant.cell_k, Handoff.Invariant.content_k]
  rename_i K
  k2l_cases K
  all_goals first
    | (exact kclaims_owise (fun _ e => by simp at e) (fun _ e => by simp at e))
    | skip
  rename_i x r
  k2l_cases r
  · k2l_cases x
    all_goals first
      | (simp only [claims, Handoff.Eqn.«kclaims(_)_HANDOFF_List_K_1», Option.bind_fun_some]; exact iclaims_K _)
      | (simp only [claims, Handoff.Eqn.«kclaims(_)_HANDOFF_List_K_2», Option.bind_fun_some]; exact pclaims_K _)
      | (simp only [claims, List.map_nil]; exact kclaims_owise (fun _ e => by simp at e) (fun _ e => by simp at e))
  · simp only [claims, List.map_nil]
    exact kclaims_owise (fun _ e => by simp at e) (fun _ e => by simp at e)

theorem tasks_eq (c : Handoff.SortGeneratedTopCell) :
    Handoff.Invariant.cell_tasks (Handoff.Invariant.cell_T c) = Handoff.SortTasksCell.«<tasks>» (tasks c) := by
  k2l_cases c with ⟨⟨⟨_⟩, _, _⟩, _⟩
  rfl

/-- The generated invariant, read order-free: the tasks' claims are pairwise distinct. -/
theorem wf_of_invariant {c : Handoff.SortGeneratedTopCell} (h : Handoff.Invariant c) : Wf c := by
  simp only [Handoff.Invariant, Handoff.Invariant.wf, Handoff.Invariant.wf_cells, Option.bind_fun_some,
    tasks_eq] at h
  obtain ⟨hw, -, -, hn⟩ := (Handoff.Invariant.mclaims_noDup _).1 h
  simp only [ListHook.unit, ListIso.toList_ofList, Option.map_some, Option.getD_some, List.append_nil] at hn
  obtain ⟨h₁, h₂⟩ := (MapHook.nodup_claimsOf_iff hw).1 hn
  have mem : ∀ {k t}, MapHook.lookup (tasks c) k = some t → (k, t) ∈ ListIso.toList (tasks c) := by
    intro k t hk; rw [MapHook.lookup_def] at hk; exact SAL.lookup_mem hk
  refine ⟨fun k t hk => ?_, fun k₁ k₂ t₁ t₂ hne e₁ e₂ x hx hx' => ?_⟩
  · have := h₁ _ (mem hk)
    rw [g_eq] at this
    exact nodup_of_map this
  · have := h₂ _ (mem e₁) _ (mem e₂) (fun e => hne (Prod.ext_iff.1 e).1) (claimK x)
    simp only [g_eq, Option.getD_some, List.mem_map] at this
    exact this ⟨x, hx, rfl⟩ ⟨x, hx', rfl⟩

/-- The initial configuration of a script whose claims are distinct satisfies the generated
invariant. -/
theorem invariant_init {P : Handoff.SortPgm} (h : (pclaims P).Nodup) : Handoff.Invariant (Handoff.init P) := by
  refine Handoff.Invariant.init_holds P ?_
  simp only [Handoff.init, Handoff.Invariant.cell_T, Handoff.Invariant.cell_tasks, Option.bind_fun_some]
  refine (Handoff.Invariant.mclaims_noDup _).2 ⟨MapHook.wf_element, ?_, rfl, ?_⟩
  · refine MapHook.entriesOn_element ⟨rfl, ?_⟩
    have := pclaims_K P
    simp only [Handoff.Invariant.mclaims_g, Handoff.Invariant.cell_k, Handoff.Invariant.content_k,
      Handoff.Eqn.«kclaims(_)_HANDOFF_List_K_2», Option.bind_fun_some]
    cases hP : Handoff.K.«pclaims(_)_HANDOFF_List_Pgm» P <;> simp_all
  · rw [MapHook.claimsOf_element]
    have := g_eq (Handoff.SortTidCell.«<tid>» 0)
      (Handoff.SortTaskCell.«<task>» (Handoff.SortTidCell.«<tid>» 0) (Handoff.SortNCell.«<n>» 0)
        (Handoff.SortKCell.«<k>» (Handoff.SortK.kseq (Handoff.SortKItem.inj_Pgm P) Handoff.SortK.dotk)))
    rw [this]
    simp only [Option.getD_some, ListHook.unit, ListIso.toList_ofList, Option.map_some, List.append_nil, claims]
    exact nodup_map claimK_inj h

end HandoffConf
