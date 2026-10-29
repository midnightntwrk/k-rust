import HandoffConf.Claims
import KPrelude.InvColl
import KPrelude.Progress

/-! The script's closure: every pending instruction's inputs and earlier turns are done or
claimed by a pending instruction, along an acyclic order (`Closed`). With the script's
well-formedness (`wf` in K, the generated `Handoff.Invariant`, read order-free by
`HandoffConf.Claims`) and the shapes of the configurations K builds (`Live`), every configuration that is not an ending has a rule that applies
(its left-hand side matches, `App`): what `progress` states. It does not say that a step exists:
that would also need `fork`'s new key and the output `o(Q, N)` unbound where they are written, and
the lower layer's `next` and `out` defined. -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffConf

variable [Handoff.Hooks]

open KPrelude Handoff

/-- The instructions of a program. -/
def iinstrs : SortPgm → List SortInstr
  | .«_;_» I P => I :: iinstrs P
  | _ => []

/-- The instructions a task has yet to run: those of the instruction or program its `<k>` holds. -/
def instrs : SortTaskCell → List SortInstr
  | .«<task>» _ _ (.«<k>» (.kseq (.inj_Instr I) .dotk)) => [I]
  | .«<task>» _ _ (.«<k>» (.kseq (.inj_Pgm P) .dotk)) => iinstrs P
  | _ => []

theorem mem_pclaims : ∀ {P : SortPgm} {i : SortInstr} {x : Claim}, i ∈ iinstrs P → x ∈ iclaims i →
    x ∈ pclaims P
  | .«_;_» I P, i, x, hi, hx => by
    simp only [iinstrs, List.mem_cons] at hi
    simp only [pclaims, List.mem_append]
    rcases hi with rfl | hi
    · exact Or.inl hx
    · exact Or.inr (mem_pclaims hi hx)
  | .«.List{"_;__HANDOFF-SYNTAX_Pgm_Instr_Pgm"}_Pgm», i, x, hi, hx => by simp [iinstrs] at hi

/-- What an instruction a task has yet to run claims, the task claims. -/
theorem mem_claims {t : SortTaskCell} {i : SortInstr} {x : Claim} (hi : i ∈ instrs t)
    (hx : x ∈ iclaims i) : x ∈ claims t := by
  unfold instrs at hi
  split at hi
  · simp only [List.mem_singleton] at hi; subst hi; simpa [claims] using hx
  · simpa [claims] using mem_pclaims hi hx
  · simp at hi

/-- The cells of a configuration. -/
def procsMap : SortProcsCell → SortMap
  | .«<procs>» p => p

def valsMap : SortValsCell → SortMap
  | .«<vals>» v => v

def procs : SortGeneratedTopCell → SortMap
  | .«<generatedTop>» (.«<T>» _ p _) _ => procsMap p

def vals : SortGeneratedTopCell → SortMap
  | .«<generatedTop>» (.«<T>» _ _ v) _ => valsMap v

/-- A process's state: its count of segments taken, and the lower layer's state. -/
abbrev st (M S : Int) : SortKItem := .inj_KItem (.«st(_,_)» M S)

/-- The `N`-th resume of `Q` is done: `Q` has taken more than `N` segments, `N` a turn. -/
def doneP (p : SortMap) (Q N : Int) : Prop :=
  ∃ M S, MapHook.lookup p (.inj_Int Q) = some (st M S) ∧ 0 ≤ N ∧ N < M

/-- A claim is satisfied: the process exists, or its turn is done. -/
def sat (p : SortMap) : Claim → Prop
  | .inr Q => ∃ v, MapHook.lookup p (.inj_Int Q) = some v
  | .inl (Q, N) => doneP p Q N

/-- What an instruction waits for: the process's previous turn (its creation for turn `0`), and the
turn that writes its input. -/
def deps : SortInstr → List Claim
  | .«resume(_,_,_)» Q N I =>
    (if N = 0 then .inr Q else .inl (Q, N - 1)) ::
      (match I with
       | .inj_Oid (.«o(_,_)» P M) => [.inl (P, M)]
       | _ => [])
  | _ => []

/-- An instruction some task has yet to run. -/
def PendI (m : SortTaskCellMap) (i : SortInstr) : Prop :=
  ∃ k t, MapHook.lookup m k = some t ∧ i ∈ instrs t

/-- A claim of an instruction some task has yet to run. -/
def Pend (m : SortTaskCellMap) (x : Claim) : Prop :=
  ∃ i, PendI m i ∧ x ∈ iclaims i

/-- `h` orders the pending claims: what an instruction waits for is above what it claims. -/
def Acyc (m : SortTaskCellMap) (h : Claim → Nat) : Prop :=
  ∀ i, PendI m i → ∀ x ∈ iclaims i, ∀ d ∈ deps i, Pend m d → h x < h d

/-- The script's closure: nothing pending is done already, what a pending instruction waits for is
done or pending, and the waits are acyclic. -/
structure Closed (m : SortTaskCellMap) (p : SortMap) : Prop where
  fresh : ∀ i, PendI m i → ∀ x ∈ iclaims i, ¬ sat p x
  ready : ∀ i, PendI m i → ∀ d ∈ deps i, sat p d ∨ Pend m d
  acyc : ∃ h, Acyc m h

/-- A task holds nothing, one instruction, or (the root, at tid `0`) a program. -/
def TaskOk : SortTaskCell → Prop
  | .«<task>» j _ (.«<k>» K) => K = .dotk ∨ (∃ i, K = .kseq (.inj_Instr i) .dotk) ∨
      (∃ P, K = .kseq (.inj_Pgm P) .dotk ∧ j = .«<tid>» 0)

/-- The invariant: the script's well-formedness (`wf` in K, `Handoff.Invariant`), the shapes K's
configurations have, the ledger of outputs, and `Closed`. -/
structure Live (c : SortGeneratedTopCell) : Prop where
  inv : Handoff.Invariant c
  tasks_ok : ∀ k t, MapHook.lookup (tasks c) k = some t → TaskOk t
  procs_wf : MapHook.WF (procs c)
  procs_ok : ∀ k v, MapHook.lookup (procs c) k = some v → ∃ M S, v = st M S ∧ 0 ≤ M
  vals_wf : MapHook.WF (vals c)
  ledger : ∀ Q N, doneP (procs c) Q N →
    ∃ V, MapHook.lookup (vals c) (.inj_Oid (.«o(_,_)» Q N)) = some (.inj_Int V)
  closed : Closed (tasks c) (procs c)

/-- What `Live` says of each element of the cell map of tasks (`gen --progress --element-fact`). -/
theorem Live.taskOk {c : SortGeneratedTopCell} {k : SortTidCell} {e : SortTaskCell} {r : SortTaskCellMap}
    (h : Live c) (hm : MapHook.concat (MapHook.element k e) r = some (tasks c)) : TaskOk e :=
  h.tasks_ok _ _ (MapHook.lookup_of_concat_element hm)

/-! ## `Closed` across a step -/

/-- A step keeps `Closed` when it adds no pending instruction, keeps every satisfied claim, newly
satisfies only claims no longer pending, and satisfies every claim it stops pending. -/
theorem Closed.step {m m' : SortTaskCellMap} {p p' : SortMap}
    (H1 : ∀ i, PendI m' i → PendI m i) (H2 : ∀ x, sat p x → sat p' x)
    (H3 : ∀ x, Pend m' x → sat p' x → sat p x) (H4 : ∀ x, Pend m x → Pend m' x ∨ sat p' x)
    (w : Closed m p) : Closed m' p' := by
  refine ⟨fun i hi x hx hs => ?_, fun i hi d hd => ?_, ?_⟩
  · exact w.fresh i (H1 i hi) x hx (H3 x ⟨i, hi, hx⟩ hs)
  · rcases w.ready i (H1 i hi) d hd with s | pd
    · exact Or.inl (H2 d s)
    · rcases H4 d pd with pd' | s
      · exact Or.inr pd'
      · exact Or.inl s
  · obtain ⟨h, ac⟩ := w.acyc
    exact ⟨h, fun i hi x hx d hd ⟨j, hj, hdj⟩ => ac i (H1 i hi) x hx d hd ⟨j, H1 j hj, hdj⟩⟩

/-! ## The tasks across a step -/

/-- Replacing a task by one with nothing to run. -/
theorem pendI_replace {k : SortTidCell} {t t' : SortTaskCell} {D m m' : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m)
    (hr : MapHook.concat (MapHook.element k t') D = some m') (e : instrs t' = []) :
    (∀ i, PendI m' i → PendI m i) ∧ (∀ i, PendI m i → PendI m' i ∨ i ∈ instrs t) := by
  constructor
  · rintro i ⟨j, u, hu, hi⟩
    by_cases hj : j = k
    · subst hj
      rw [MapHook.lookup_of_concat_element hr] at hu
      cases hu; rw [e] at hi; cases hi
    · refine ⟨j, u, ?_, hi⟩
      rw [MapHook.lookup_concat_right hr (MapHook.lookup_element_ne hj)] at hu
      rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]
      exact hu
  · rintro i ⟨j, u, hu, hi⟩
    by_cases hj : j = k
    · subst hj
      rw [MapHook.lookup_of_concat_element hm] at hu
      cases hu; exact Or.inr hi
    · refine Or.inl ⟨j, u, ?_, hi⟩
      rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)] at hu
      rw [MapHook.lookup_concat_right hr (MapHook.lookup_element_ne hj)]
      exact hu

/-- Removing a task with nothing to run. -/
theorem pendI_remove {k : SortTidCell} {t : SortTaskCell} {D m : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m) (e : instrs t = []) :
    ∀ i, PendI D i ↔ PendI m i := by
  intro i
  constructor
  · rintro ⟨j, u, hu, hi⟩
    by_cases hj : j = k
    · subst hj; rw [(MapHook.concat_element_iff.1 hm).2.1] at hu; cases hu
    · exact ⟨j, u, by rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]; exact hu, hi⟩
  · rintro ⟨j, u, hu, hi⟩
    by_cases hj : j = k
    · subst hj; rw [MapHook.lookup_of_concat_element hm] at hu; cases hu; rw [e] at hi; cases hi
    · exact ⟨j, u, by rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)] at hu; exact hu, hi⟩


/-- A lookup in a map whose one task was replaced. -/
theorem lookup_replace {k : SortTidCell} {t t' : SortTaskCell} {D m m' : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m)
    (hr : MapHook.concat (MapHook.element k t') D = some m') {j : SortTidCell} {u : SortTaskCell}
    (hu : MapHook.lookup m' j = some u) : (j = k ∧ u = t') ∨ MapHook.lookup m j = some u := by
  by_cases hj : j = k
  · subst hj; rw [MapHook.lookup_of_concat_element hr] at hu; cases hu; exact Or.inl ⟨rfl, rfl⟩
  · right
    rw [MapHook.lookup_concat_right hr (MapHook.lookup_element_ne hj)] at hu
    rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]; exact hu

/-- A lookup in a map with one task removed. -/
theorem lookup_remove {k : SortTidCell} {t : SortTaskCell} {D m : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m) {j : SortTidCell} {u : SortTaskCell}
    (hu : MapHook.lookup D j = some u) : MapHook.lookup m j = some u :=
  MapHook.lookup_of_concat_right hm hu

/-- A lookup after `fork`: the root, the new task, or a task of the rest. -/
theorem lookup_fork {k₀ kN : SortTidCell} {root root' task : SortTaskCell}
    {D m r r₂ : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k₀ root) D = some m)
    (hr : MapHook.concat (MapHook.element k₀ root') (MapHook.element kN task) = some r)
    (hr₂ : MapHook.concat r D = some r₂) {j : SortTidCell} {u : SortTaskCell}
    (hu : MapHook.lookup r₂ j = some u) :
    (j = k₀ ∧ u = root') ∨ (j = kN ∧ u = task) ∨ (MapHook.lookup m j = some u ∧ j ≠ k₀) := by
  rw [MapHook.lookup_concat hr₂] at hu
  cases e : MapHook.lookup r j with
  | none =>
    rw [e] at hu
    right; right
    by_cases hj : j = k₀
    · subst hj; rw [(MapHook.concat_element_iff.1 hm).2.1] at hu; cases hu
    · exact ⟨by rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]; exact hu, hj⟩
  | some v =>
    rw [e] at hu; cases hu
    have := ((MapHook.binds_pair hr) j _).1 e
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- `fork` moves the root's first instruction to a new task: the same instructions are pending. -/
theorem pendI_fork {k₀ kN : SortTidCell} {root root' task : SortTaskCell}
    {D m r r₂ : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k₀ root) D = some m)
    (hr : MapHook.concat (MapHook.element k₀ root') (MapHook.element kN task) = some r)
    (hr₂ : MapHook.concat r D = some r₂)
    (hsplit : ∀ i, i ∈ instrs root ↔ i ∈ instrs task ∨ i ∈ instrs root') :
    ∀ i, PendI r₂ i ↔ PendI m i := by
  intro i
  constructor
  · rintro ⟨j, u, hu, hi⟩
    rcases lookup_fork hm hr hr₂ hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e, -⟩
    · exact ⟨_, _, MapHook.lookup_of_concat_element hm, (hsplit i).2 (Or.inr hi)⟩
    · exact ⟨_, _, MapHook.lookup_of_concat_element hm, (hsplit i).2 (Or.inl hi)⟩
    · exact ⟨_, _, e, hi⟩
  · rintro ⟨j, u, hu, hi⟩
    by_cases hj : j = k₀
    · subst hj
      rw [MapHook.lookup_of_concat_element hm] at hu; cases hu
      rcases (hsplit i).1 hi with h | h
      · exact ⟨_, _, MapHook.lookup_of_concat hr₂ (MapHook.lookup_of_concat_element_right hr), h⟩
      · exact ⟨_, _, MapHook.lookup_of_concat hr₂ (MapHook.lookup_of_concat_element hr), h⟩
    · rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)] at hu
      exact ⟨_, _, MapHook.lookup_of_concat_right hr₂ hu, hi⟩

/-- After a task's instruction ran (the task now has nothing to run), no task claims what it
claimed (`WfM`, `HandoffConf.Claims`). -/
theorem not_pend_of_ran {k : SortTidCell} {t t' : SortTaskCell} {D m m' : SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m)
    (hr : MapHook.concat (MapHook.element k t') D = some m') (e : instrs t' = []) (w : WfM m)
    {x : Claim} (hx : x ∈ claims t) : ¬ Pend m' x := by
  rintro ⟨i, ⟨j, u, hu, hi⟩, hxi⟩
  by_cases hj : j = k
  · subst hj; rw [MapHook.lookup_of_concat_element hr] at hu; cases hu; rw [e] at hi; cases hi
  · rw [MapHook.lookup_concat_right hr (MapHook.lookup_element_ne hj)] at hu
    rw [← MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)] at hu
    exact w.2 _ _ _ _ (Ne.symm hj) (MapHook.lookup_of_concat_element hm) hu x hx (mem_claims hi hxi)

/-! ## `<procs>` across a step -/

theorem inj_Int_ne {Q Q' : Int} (h : Q' ≠ Q) : (SortKItem.inj_Int Q' : SortKItem) ≠ .inj_Int Q := by
  intro e; cases e; exact h rfl

/-- `new(Q, S)` adds `Q` at turn `0`: every claim satisfied before still is, and only `Q`'s creation
is newly satisfied. -/
theorem sat_new {Q S : Int} {p p' : SortMap}
    (h : MapHook.concat (MapHook.element (.inj_Int Q) (st 0 S)) p = some p') :
    (∀ x, sat p x → sat p' x) ∧ (∀ x, sat p' x → x ≠ .inr Q → sat p x) := by
  constructor
  · rintro (⟨Q', N⟩ | Q') hs
    · obtain ⟨M, S', hl, h0, hN⟩ := hs
      exact ⟨M, S', MapHook.lookup_of_concat_right h hl, h0, hN⟩
    · obtain ⟨v, hl⟩ := hs
      exact ⟨v, MapHook.lookup_of_concat_right h hl⟩
  · rintro (⟨Q', N⟩ | Q') hs hne
    · obtain ⟨M, S', hl, h0, hN⟩ := hs
      by_cases hq : Q' = Q
      · subst hq
        rw [MapHook.lookup_of_concat_element h] at hl
        simp only [Option.some.injEq] at hl; cases hl; omega
      · rw [MapHook.lookup_concat_right h (MapHook.lookup_element_ne (inj_Int_ne hq))] at hl
        exact ⟨M, S', hl, h0, hN⟩
    · obtain ⟨v, hl⟩ := hs
      have hq : Q' ≠ Q := fun e => hne (by rw [e])
      rw [MapHook.lookup_concat_right h (MapHook.lookup_element_ne (inj_Int_ne hq))] at hl
      exact ⟨v, hl⟩

/-- The `N`-th resume of `Q` moves `Q` from turn `N` to `N + 1`: every claim satisfied before still is,
and only that turn is newly satisfied. -/
theorem sat_resume {Q N S S' : Int} {D p p' : SortMap}
    (hp : MapHook.concat (MapHook.element (.inj_Int Q) (st N S)) D = some p)
    (hp' : MapHook.concat (MapHook.element (.inj_Int Q) (st (N + 1) S')) D = some p') :
    (∀ x, sat p x → sat p' x) ∧ (∀ x, sat p' x → x ≠ .inl (Q, N) → sat p x) := by
  have same : ∀ {Q'}, Q' ≠ Q → MapHook.lookup p' (.inj_Int Q') = MapHook.lookup p (.inj_Int Q') :=
    fun hq => by
      rw [MapHook.lookup_concat_right hp' (MapHook.lookup_element_ne (inj_Int_ne hq)),
        MapHook.lookup_concat_right hp (MapHook.lookup_element_ne (inj_Int_ne hq))]
  have lp := MapHook.lookup_of_concat_element hp
  have lp' := MapHook.lookup_of_concat_element hp'
  constructor
  · rintro (⟨Q', j⟩ | Q') hs
    · obtain ⟨M, S₀, hl, h0, hN⟩ := hs
      by_cases hq : Q' = Q
      · subst hq; rw [lp] at hl; simp only [Option.some.injEq] at hl; cases hl
        exact ⟨N + 1, S', lp', h0, by omega⟩
      · exact ⟨M, S₀, by rw [same hq]; exact hl, h0, hN⟩
    · obtain ⟨v, hl⟩ := hs
      by_cases hq : Q' = Q
      · subst hq; exact ⟨_, lp'⟩
      · exact ⟨v, by rw [same hq]; exact hl⟩
  · rintro (⟨Q', j⟩ | Q') hs hne
    · obtain ⟨M, S₀, hl, h0, hN⟩ := hs
      by_cases hq : Q' = Q
      · subst hq; rw [lp'] at hl; simp only [Option.some.injEq] at hl; cases hl
        have : j ≠ N := fun e => hne (by rw [e])
        exact ⟨N, S, lp, h0, by omega⟩
      · exact ⟨M, S₀, by rw [← same hq]; exact hl, h0, hN⟩
    · obtain ⟨v, hl⟩ := hs
      by_cases hq : Q' = Q
      · subst hq; exact ⟨_, lp⟩
      · exact ⟨v, by rw [← same hq]; exact hl⟩

/-! ## `<vals>` across a step -/

/-- `resume` with an input keeps every binding of `<vals>` and adds its output. -/
theorem vals_oid {I : SortOid} {V W : Int} {o : SortOid} {D a r₁ b : SortMap}
    (ha : MapHook.concat (MapHook.element (.inj_Oid I) (.inj_Int V)) D = some a)
    (h₁ : MapHook.concat (MapHook.element (.inj_Oid I) (.inj_Int V))
      (MapHook.element (.inj_Oid o) (.inj_Int W)) = some r₁)
    (hb : MapHook.concat r₁ D = some b) :
    (∀ j v, MapHook.lookup a j = some v → MapHook.lookup b j = some v) ∧
      MapHook.lookup b (.inj_Oid o) = some (.inj_Int W) := by
  refine ⟨fun j v hv => ?_, MapHook.lookup_of_concat hb (MapHook.lookup_of_concat_element_right h₁)⟩
  by_cases hj : j = .inj_Oid I
  · subst hj; rw [MapHook.lookup_of_concat_element ha] at hv; cases hv
    exact MapHook.lookup_of_concat hb (MapHook.lookup_of_concat_element h₁)
  · rw [MapHook.lookup_concat_right ha (MapHook.lookup_element_ne hj)] at hv
    exact MapHook.lookup_of_concat_right hb hv

/-! ## `Live` is preserved -/

theorem st_inj {M S M' S' : Int} (h : st M S = st M' S') : M = M' ∧ S = S' := by
  cases h; exact ⟨rfl, rfl⟩

/-- The new state of `<procs>` after a step that binds `Q` to `v`, `0 ≤` its turn. -/
theorem procs_ok_bind {Q M S : Int} {D p' : SortMap} (h0 : 0 ≤ M)
    (hp' : MapHook.concat (MapHook.element (.inj_Int Q) (st M S)) D = some p')
    (old : ∀ j v, MapHook.lookup D j = some v → ∃ M S, v = st M S ∧ 0 ≤ M) :
    ∀ j v, MapHook.lookup p' j = some v → ∃ M S, v = st M S ∧ 0 ≤ M := by
  intro j v hv
  by_cases hj : j = .inj_Int Q
  · subst hj; rw [MapHook.lookup_of_concat_element hp'] at hv; cases hv; exact ⟨M, S, rfl, h0⟩
  · rw [MapHook.lookup_concat_right hp' (MapHook.lookup_element_ne hj)] at hv; exact old j v hv

/-- The rest of `<procs>` without `Q`'s binding has the same values. -/
theorem procs_ok_rest {Q : Int} {w : SortKItem} {D p : SortMap}
    (hp : MapHook.concat (MapHook.element (.inj_Int Q) w) D = some p)
    (old : ∀ j v, MapHook.lookup p j = some v → ∃ M S, v = st M S ∧ 0 ≤ M) :
    ∀ j v, MapHook.lookup D j = some v → ∃ M S, v = st M S ∧ 0 ≤ M :=
  fun j v hv => old j v (MapHook.lookup_of_concat_right hp hv)

theorem Live.preserved : Preserved Handoff.Step Live := by
  apply Handoff.Step.preserves_of
  · -- fork
    intro m G3 G4 D0 D2 y N I P r r2 hm hlit hr hr3 w
    subst hlit
    have hsplit : ∀ i, i ∈ instrs (.«<task>» (.«<tid>» 0) (.«<n>» N) (.«<k>» (.kseq (.inj_Pgm (.«_;_» I P)) .dotk))) ↔
        i ∈ instrs (.«<task>» (.«<tid>» (KPrelude.IntHook.add N 1)) (.«<n>» 0) (.«<k>» (.kseq (.inj_Instr I) .dotk))) ∨
        i ∈ instrs (.«<task>» (.«<tid>» 0) (.«<n>» (KPrelude.IntHook.add N 1)) (.«<k>» (.kseq (.inj_Pgm P) .dotk))) := by
      intro i; simp [instrs, iinstrs]
    have pf := pendI_fork hm hr hr3 hsplit
    refine ⟨(Handoff.Invariant.case.fork m G3 G4 D0 D2 0 N I P r r2 hm rfl hr hr3 w.inv), fun j u hu => ?_, w.procs_wf, w.procs_ok,
      w.vals_wf, w.ledger, Closed.step (fun i h => (pf i).1 h) (fun _ h => h) (fun _ _ h => h)
        (fun x ⟨i, hi, hx⟩ => Or.inl ⟨i, (pf i).2 hi, hx⟩) w.closed⟩
    rcases lookup_fork hm hr hr3 hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨e, -⟩
    · simp [TaskOk]
    · simp [TaskOk]
    · exact w.tasks_ok j u e
  · -- nil
    intro m G4 G5 D0 k D2 G6 r hm hr w
    have pr := pendI_replace hm hr rfl
    refine ⟨(Handoff.Invariant.case.nil m G4 G5 D0 k D2 G6 r hm hr w.inv), fun j u hu => ?_, w.procs_wf, w.procs_ok,
      w.vals_wf, w.ledger, Closed.step pr.1 (fun _ h => h) (fun _ _ h => h)
        (fun x ⟨i, hi, hx⟩ => (pr.2 i hi).elim (fun h => Or.inl ⟨i, h, hx⟩)
          (fun h => by simp [instrs, iinstrs] at h)) w.closed⟩
    rcases lookup_replace hm hr hu with ⟨-, rfl⟩ | e
    · simp [TaskOk]
    · exact w.tasks_ok j u e
  · -- new
    intro m D2 D1 D0 k D3 G5 Q S r r2 hm hr hr3 w
    have pr := pendI_replace hm hr rfl
    have sn := sat_new hr3
    refine ⟨(Handoff.Invariant.case.new m D2 D1 D0 k D3 G5 Q S r r2 hm hr hr3 w.inv), fun j u hu => ?_, MapHook.wf_of_concat hr3,
      procs_ok_bind (Int.le_refl 0) hr3 w.procs_ok, w.vals_wf,
      fun Q' N hd => w.ledger Q' N (sn.2 (.inl (Q', N)) hd (by simp)), Closed.step pr.1 sn.1 ?_ ?_ w.closed⟩
    · rcases lookup_replace hm hr hu with ⟨-, rfl⟩ | e
      · simp [TaskOk]
      · exact w.tasks_ok j u e
    · intro x hp hs
      by_cases hx : x = .inr Q
      · subst hx; exact absurd hp (not_pend_of_ran hm hr rfl (wf_of_invariant w.inv) (by simp [claims, iclaims]))
      · exact sn.2 x hs hx
    · rintro x ⟨i, hi, hx⟩
      rcases pr.2 i hi with h | h
      · exact Or.inl ⟨i, h, hx⟩
      · simp only [instrs, List.mem_singleton] at h; subst h
        simp only [iclaims, List.mem_singleton] at hx; subst hx
        exact Or.inr ⟨_, MapHook.lookup_of_concat_element hr3⟩
  · -- resume-lit
    intro m m2 D3 D0 k D4 G6 Q N V D2 S r x9 r9 y13 r11 hm hm5 hr fn10 hr10 fo14 hr12 w
    have pr := pendI_replace hm hr rfl
    obtain ⟨M, S₀, e, h0⟩ := w.procs_ok _ _ (MapHook.lookup_of_concat_element hm5)
    obtain ⟨rfl, -⟩ := st_inj e
    have sr := sat_resume hm5 hr10
    refine ⟨(Handoff.Invariant.case.«resume-lit» m m2 D3 D0 k D4 G6 Q N V D2 S r x9 r9 y13 r11 hm hm5 hr fn10 hr10 fo14 hr12 w.inv), fun j u hu => ?_, MapHook.wf_of_concat hr10,
      procs_ok_bind (by simp only [IntHook.add]; omega) hr10 (procs_ok_rest hm5 w.procs_ok), MapHook.wf_of_concat hr12, ?_,
      Closed.step pr.1 sr.1 ?_ ?_ w.closed⟩
    · rcases lookup_replace hm hr hu with ⟨-, rfl⟩ | e
      · simp [TaskOk]
      · exact w.tasks_ok j u e
    · intro Q' j hd
      by_cases hx : (Q', j) = (Q, N)
      · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
        exact ⟨_, MapHook.lookup_of_concat_element hr12⟩
      · obtain ⟨W, hW⟩ := w.ledger Q' j (sr.2 (.inl (Q', j)) hd (by simpa using hx))
        exact ⟨W, MapHook.lookup_of_concat_right hr12 hW⟩
    · intro x hp hs
      by_cases hx : x = .inl (Q, N)
      · subst hx; exact absurd hp (not_pend_of_ran hm hr rfl (wf_of_invariant w.inv) (by simp [claims, iclaims]))
      · exact sr.2 x hs hx
    · rintro x ⟨i, hi, hx⟩
      rcases pr.2 i hi with h | h
      · exact Or.inl ⟨i, h, hx⟩
      · simp only [instrs, List.mem_singleton] at h; subst h
        simp only [iclaims, List.mem_singleton] at hx; subst hx
        exact Or.inr ⟨N + 1, x9, MapHook.lookup_of_concat_element hr10, h0, by omega⟩
  · -- resume-oid
    intro m m2 m3 D0 k D4 G6 Q N I D2 S D3 V r x15 r15 y19 r17 r19 hm hm6 hm13 hr fn16 hr16 fo20 hr18 hr20 w
    have pr := pendI_replace hm hr rfl
    obtain ⟨M, S₀, e, h0⟩ := w.procs_ok _ _ (MapHook.lookup_of_concat_element hm6)
    obtain ⟨rfl, -⟩ := st_inj e
    have sr := sat_resume hm6 hr16
    have vo := vals_oid hm13 hr18 hr20
    refine ⟨(Handoff.Invariant.case.«resume-oid» m m2 m3 D0 k D4 G6 Q N I D2 S D3 V r x15 r15 y19 r17 r19 hm hm6 hm13 hr fn16 hr16 fo20 hr18 hr20 w.inv), fun j u hu => ?_, MapHook.wf_of_concat hr16,
      procs_ok_bind (by simp only [IntHook.add]; omega) hr16 (procs_ok_rest hm6 w.procs_ok), MapHook.wf_of_concat hr20, ?_,
      Closed.step pr.1 sr.1 ?_ ?_ w.closed⟩
    · rcases lookup_replace hm hr hu with ⟨-, rfl⟩ | e
      · simp [TaskOk]
      · exact w.tasks_ok j u e
    · intro Q' j hd
      by_cases hx : (Q', j) = (Q, N)
      · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
        exact ⟨_, vo.2⟩
      · obtain ⟨W, hW⟩ := w.ledger Q' j (sr.2 (.inl (Q', j)) hd (by simpa using hx))
        exact ⟨W, vo.1 _ _ hW⟩
    · intro x hp hs
      by_cases hx : x = .inl (Q, N)
      · subst hx; exact absurd hp (not_pend_of_ran hm hr rfl (wf_of_invariant w.inv) (by simp [claims, iclaims]))
      · exact sr.2 x hs hx
    · rintro x ⟨i, hi, hx⟩
      rcases pr.2 i hi with h | h
      · exact Or.inl ⟨i, h, hx⟩
      · simp only [instrs, List.mem_singleton] at h; subst h
        simp only [iclaims, List.mem_singleton] at hx; subst hx
        exact Or.inr ⟨N + 1, x15, MapHook.lookup_of_concat_element hr16, h0, by omega⟩
  · -- done
    intro m G4 G5 D0 D2 G0 D3 hm w
    have pr := pendI_remove hm rfl
    refine ⟨(Handoff.Invariant.case.done m G4 G5 D0 D2 G0 D3 hm w.inv), fun j u hu => w.tasks_ok j u (lookup_remove hm hu),
      w.procs_wf, w.procs_ok, w.vals_wf, w.ledger,
      Closed.step (fun i h => (pr i).1 h) (fun _ h => h) (fun _ _ h => h)
        (fun x ⟨i, hi, hx⟩ => Or.inl ⟨i, (pr i).2 hi, hx⟩) w.closed⟩

/-! ## The rank -/

open Classical in
/-- An order of the pending claims that `Closed` gives (any, when there is none). -/
noncomputable def H (m : SortTaskCellMap) : Claim → Nat :=
  if h : ∃ h, Acyc m h then Classical.choose h else fun _ => 0

theorem acyc_H {m : SortTaskCellMap} (h : ∃ h, Acyc m h) : Acyc m (H m) := by
  unfold H
  split
  · next h' => exact Classical.choose_spec h'
  · contradiction

/-- The rank of a task in the proof of `progress`: the highest of its claims in `H`. A task waits on
claims above its own, so on tasks of a higher rank. -/
noncomputable def taskRank (m : SortTaskCellMap) (_ : SortTidCell) (t : SortTaskCell) : Nat :=
  ((instrs t).flatMap iclaims).foldr (fun x b => max (H m x) b) 0

theorem le_taskRank {m : SortTaskCellMap} {k : SortTidCell} {t : SortTaskCell} {i : SortInstr} {x : Claim}
    (hi : i ∈ instrs t) (hx : x ∈ iclaims i) : H m x ≤ taskRank m k t :=
  KPrelude.MapHook.le_foldr_max (H m) (List.mem_flatMap.2 ⟨i, hi, hx⟩)

end HandoffConf
