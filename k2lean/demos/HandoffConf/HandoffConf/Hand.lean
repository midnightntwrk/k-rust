import HandoffConf.Views

/-! The slots of `HandoffConf.Slots` that the generic attempts leave, proved by hand: the races at
one binding of `<procs>` or `<vals>` (`KeyJoins`). Steps of one task are one step; steps of two
tasks would both claim one creation or one resume, which the script's well-formedness `Wf`
(`HandoffConf.Inv`) excludes (`eff_compat`). -/

set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffConf

variable [Handoff.Hooks]

open KPrelude

section MChFacts

open MapHook

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [Std.TransOrd K]
  [Std.LawfulEqOrd K]

/-- A change of a map that changes only the binding at `k` reads or leaves alone every other key. -/
theorem mch_shape {c : MCh M} {L L' : M} {k : K} (pre : c.pre L) (ap : c.apply L = L')
    (hk : lookup L' k ≠ lookup L k) (ho : ∀ j, j ≠ k → lookup L' j = lookup L j) :
    ∃ a b, c = some (a, b) ∧ ∀ j, j ≠ k →
      (lookup a j = none ∧ lookup b j = none) ∨ (lookup a j = lookup b j ∧ lookup L j ≠ none) := by
  cases c with
  | none => exact absurd (by rw [← ap]; rfl) hk
  | some p =>
    obtain ⟨a, b⟩ := p
    refine ⟨a, b, rfl, fun j hj => ?_⟩
    obtain ⟨R, r, h, h'⟩ := pre _ rfl
    have e := ho j hj
    rw [← ap, MCh.lookup_apply pre] at e
    by_cases u : lookup a j = none ∧ lookup b j = none
    · exact Or.inl u
    · rw [ite_eq_right u] at e
      right
      cases ha : lookup a j with
      | some v =>
        have hl := lookup_of_concat h ha
        exact ⟨(e.trans hl).symm, by rw [hl]; simp⟩
      | none =>
        exfalso
        have hb : lookup b j ≠ none := fun hb => u ⟨ha, hb⟩
        rcases concat_disj_lookup h' j with x | x
        · exact hb x
        · rw [← lookup_concat_right h ha, ← e] at x; exact hb x

/-- A rule's change (`MCh.Small`) that changes only the binding at `k`, to a binding, matches and
puts back no other key. -/
theorem mch_keys {c : MCh M} {L L' : M} {k : K} (sm : c.Small) (pre : c.pre L) (ap : c.apply L = L')
    (hk : lookup L' k ≠ lookup L k) (ho : ∀ j, j ≠ k → lookup L' j = lookup L j)
    (hb : lookup L' k ≠ none) :
    ∃ a b, c = some (a, b) ∧ ∀ j, j ≠ k → lookup a j = none ∧ lookup b j = none := by
  obtain ⟨a, b, rfl, hs⟩ := mch_shape pre ap hk ho
  refine ⟨a, b, rfl, fun j hj => ?_⟩
  have hbk : lookup b k ≠ none := by
    have e := MCh.lookup_apply pre k
    rw [ap] at e
    by_cases u : lookup a k = none ∧ lookup b k = none
    · rw [ite_eq_left u] at e; exact absurd e hk
    · rw [ite_eq_right u] at e; rw [← e]; exact hb
  have hbj : lookup b j = none := by
    rcases (sm _ rfl).2 with ⟨k', w, e⟩ | e
    · change b = _ at e
      subst e
      by_cases e : k = k'
      · subst e; exact lookup_element_ne hj
      · exact absurd (lookup_element_ne e) hbk
    · change b = _ at e
      subst e; exact lookup_unit
  rcases hs j hj with u | ⟨e, -⟩
  · exact u
  · exact ⟨e.trans hbj, hbj⟩

omit [Std.TransOrd K] [Std.LawfulEqOrd K] in
/-- Two changes at two different keys, each matching and putting back no other key, commute. -/
theorem keys_compat {c₁ c₂ : MCh M} {k₁ k₂ : K} (hne : k₁ ≠ k₂)
    (h₁ : ∃ a b, c₁ = some (a, b) ∧ ∀ j, j ≠ k₁ → lookup a j = none ∧ lookup b j = none)
    (h₂ : ∃ a b, c₂ = some (a, b) ∧ ∀ j, j ≠ k₂ → lookup a j = none ∧ lookup b j = none) :
    MCh.Compat c₁ c₂ := by
  obtain ⟨a₁, b₁, rfl, h₁⟩ := h₁
  obtain ⟨a₂, b₂, rfl, h₂⟩ := h₂
  have key : ∀ j, (lookup a₁ j = none ∧ lookup b₁ j = none) ∨
      (lookup a₂ j = none ∧ lookup b₂ j = none) := by
    intro j
    by_cases hj : j = k₁
    · rw [hj]; exact Or.inr (h₂ _ hne)
    · exact Or.inl (h₁ _ hj)
  exact Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, Or.inl ⟨fun j => (key j).imp And.left And.left,
    fun j => (key j).imp And.right And.right⟩⟩)

omit [Std.TransOrd K] [Std.LawfulEqOrd K] in
/-- Two changes that each add a binding at a key the map does not bind, two different keys, and
read or leave alone every other key, commute (`MCh.Shared`). -/
theorem adds_compat {c₁ c₂ : MCh M} {L : M} {o₁ o₂ : K} (hne : o₁ ≠ o₂)
    (n₁ : lookup L o₁ = none) (n₂ : lookup L o₂ = none)
    (h₁ : ∃ a b, c₁ = some (a, b) ∧ ∀ j, j ≠ o₁ →
      (lookup a j = none ∧ lookup b j = none) ∨ (lookup a j = lookup b j ∧ lookup L j ≠ none))
    (h₂ : ∃ a b, c₂ = some (a, b) ∧ ∀ j, j ≠ o₂ →
      (lookup a j = none ∧ lookup b j = none) ∨ (lookup a j = lookup b j ∧ lookup L j ≠ none)) :
    MCh.Compat c₁ c₂ := by
  obtain ⟨a₁, b₁, rfl, h₁⟩ := h₁
  obtain ⟨a₂, b₂, rfl, h₂⟩ := h₂
  refine Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, Or.inr (Or.inr fun j => ?_)⟩)
  by_cases j₁ : j = o₁
  · rw [j₁]
    rcases h₂ _ hne with u | ⟨-, x⟩
    · exact Or.inr (Or.inl u)
    · exact absurd n₁ x
  by_cases j₂ : j = o₂
  · rw [j₂]
    rcases h₁ _ (Ne.symm hne) with u | ⟨-, x⟩
    · exact Or.inl u
    · exact absurd n₂ x
  rcases h₁ _ j₁ with u | ⟨e₁, -⟩
  · exact Or.inl u
  rcases h₂ _ j₂ with u | ⟨e₂, -⟩
  · exact Or.inr (Or.inl u)
  exact Or.inr (Or.inr ⟨e₁, e₂⟩)

/-- An insertion `(k ↦ v) L = L'`. -/
theorem ins_facts {k : K} {v : V} {L L' : M} (h : concat (element k v) L = some L') :
    lookup L' k = some v ∧ lookup L k = none ∧ ∀ j, j ≠ k → lookup L' j = lookup L j :=
  ⟨lookup_of_concat_element h, (concat_element_iff.1 h).2.1,
    fun j hj => lookup_concat_right h (lookup_element_ne hj)⟩

/-- A replacement of the binding at `k` (`(k ↦ v) D = L`, `(k ↦ w) D = L'`). -/
theorem repl_facts {k : K} {v w : V} {D L L' : M} (h : concat (element k v) D = some L)
    (h' : concat (element k w) D = some L') :
    lookup L' k = some w ∧ lookup L k = some v ∧ ∀ j, j ≠ k → lookup L' j = lookup L j :=
  ⟨lookup_of_concat_element h', lookup_of_concat_element h, fun j hj =>
    (lookup_concat_right h' (lookup_element_ne hj)).trans (lookup_concat_right h (lookup_element_ne hj)).symm⟩

/-- A read of `i ↦ v` and an insertion of `o ↦ x` beside it (`(i ↦ v) D = L`, `(i ↦ v) (o ↦ x) = r`,
`r D = L'`). -/
theorem ext_facts {i o : K} {v x : V} {D L r L' : M} (h : concat (element i v) D = some L)
    (hp : concat (element i v) (element o x) = some r) (h' : concat r D = some L') :
    lookup L' o = some x ∧ lookup L o = none ∧ ∀ j, j ≠ o → lookup L' j = lookup L j := by
  have bp := binds_pair hp
  have ro : lookup r o = some x := (bp o x).2 (by simp)
  have ri : lookup r i = some v := (bp i v).2 (by simp)
  have hio : i ≠ o := fun e => by
    have := (concat_element_iff.1 hp).2.1
    rw [e, lookup_element_self] at this; cases this
  have nDo : lookup D o = none := by
    rcases concat_disj_lookup h' o with x' | x'
    · rw [ro] at x'; cases x'
    · exact x'
  refine ⟨lookup_of_concat h' ro, ?_, fun j hj => ?_⟩
  · rw [lookup_concat_right h (lookup_element_ne (Ne.symm hio))]; exact nDo
  · by_cases ji : j = i
    · rw [ji, lookup_of_concat h' ri, lookup_of_concat_element h]
    · have rj : lookup r j = none := by
        cases e : lookup r j with
        | none => rfl
        | some w =>
          have := (bp j w).1 e
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
          rcases this with ⟨e', -⟩ | ⟨e', -⟩
          · exact absurd e' ji
          · exact absurd e' hj
      rw [lookup_concat_right h' rj, lookup_concat_right h (lookup_element_ne ji)]

end MChFacts

/-- The `<procs>` of a configuration. -/
def procsOf : Handoff.SortGeneratedTopCell → Handoff.SortMap
  | .«<generatedTop>» (.«<T>» _ (.«<procs>» L) _) _ => L

/-- The `<vals>` of a configuration. -/
def valsOf : Handoff.SortGeneratedTopCell → Handoff.SortMap
  | .«<generatedTop>» (.«<T>» _ _ (.«<vals>» V)) _ => V

/-- What a view's change (`ChOf`) does to `<procs>` and `<vals>`. -/
theorem cells_step {ch : Change} {c c₁ : Handoff.SortGeneratedTopCell}
    (o : (∃ a b, MStep a b ch c c₁) ∨ SStep ch c c₁) :
    ch.procs.pre (procsOf c) ∧ ch.procs.apply (procsOf c) = procsOf c₁ ∧
      ch.vals.pre (valsOf c) ∧ ch.vals.apply (valsOf c) = valsOf c₁ := by
  rcases o with ⟨a, b, m, R, r, s, rfl, -, -, hp, rfl⟩ | ⟨tc, s, rfl, hp, rfl⟩
  all_goals exact ⟨hp.1, rfl, hp.2.1, rfl⟩

/-- A change of a map that matches and puts back only the key `k`. -/
def Keys (c : MCh Handoff.SortMap) (k : Handoff.SortKItem) : Prop :=
  ∃ a b, c = some (a, b) ∧ ∀ j, j ≠ k → MapHook.lookup a j = none ∧ MapHook.lookup b j = none

/-- A change of the map `L` that changes only the key `k`, and reads or leaves alone the others. -/
def Shape (c : MCh Handoff.SortMap) (L : Handoff.SortMap) (k : Handoff.SortKItem) : Prop :=
  ∃ a b, c = some (a, b) ∧ ∀ j, j ≠ k → (MapHook.lookup a j = none ∧ MapHook.lookup b j = none) ∨
    (MapHook.lookup a j = MapHook.lookup b j ∧ MapHook.lookup L j ≠ none)

/-- What the step of the task at `k` that creates a process (`new`) or resumes one (`resume-lit`,
`resume-oid`) from `c` does: the task's claim, and its changes of `<procs>` and `<vals>`. -/
inductive Eff (c : Handoff.SortGeneratedTopCell) (ch : Change) (k : Handoff.SortTidCell) : Prop where
  | new (t : Handoff.SortTaskCell) (Q : Int) (ht : MapHook.lookup (tasks c) k = some t)
      (hc : claims t = [.inr Q]) (hL : MapHook.lookup (procsOf c) (Handoff.SortKItem.inj_Int Q) = none)
      (hp : Keys ch.procs (Handoff.SortKItem.inj_Int Q)) (hv : ch.vals = none)
  | res (t : Handoff.SortTaskCell) (Q N S : Int) (ht : MapHook.lookup (tasks c) k = some t)
      (hc : claims t = [.inl (Q, N)])
      (hL : MapHook.lookup (procsOf c) (Handoff.SortKItem.inj_Int Q) =
        some (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» N S)))
      (hp : Keys ch.procs (Handoff.SortKItem.inj_Int Q))
      (hV : MapHook.lookup (valsOf c) (Handoff.SortKItem.inj_Oid (Handoff.SortOid.«o(_,_)» Q N)) = none)
      (hv : Shape ch.vals (valsOf c) (Handoff.SortKItem.inj_Oid (Handoff.SortOid.«o(_,_)» Q N)))

/-- The steps of two different tasks that create or resume processes have keyed changes that
commute: two claims of one creation or of one resume are excluded by `Wf`, and a creation of a
process that a resume reads cannot be. -/
theorem eff_compat {c ch₁ ch₂ k₁ k₂} (w : Wf c) (hk : k₁ ≠ k₂) (e₁ : Eff c ch₁ k₁) (e₂ : Eff c ch₂ k₂) :
    ch₁.KCompat ch₂ := by
  rcases e₁ with ⟨t₁, Q₁, ht₁, hc₁, hL₁, hp₁, hv₁⟩ | ⟨t₁, Q₁, N₁, S₁, ht₁, hc₁, hL₁, hp₁, hV₁, hv₁⟩ <;>
  rcases e₂ with ⟨t₂, Q₂, ht₂, hc₂, hL₂, hp₂, hv₂⟩ | ⟨t₂, Q₂, N₂, S₂, ht₂, hc₂, hL₂, hp₂, hV₂, hv₂⟩
  · refine ⟨keys_compat ?_ hp₁ hp₂, Or.inl hv₁⟩
    intro e; cases e
    exact w.2 _ _ _ _ hk ht₁ ht₂ (.inr Q₁) (by rw [hc₁]; simp) (by rw [hc₂]; simp)
  · refine ⟨keys_compat ?_ hp₁ hp₂, Or.inl hv₁⟩
    intro e; cases e
    rw [hL₁] at hL₂; cases hL₂
  · refine ⟨keys_compat ?_ hp₁ hp₂, Or.inr (Or.inl hv₂)⟩
    intro e; cases e
    rw [hL₁] at hL₂; cases hL₂
  · have same : ∀ {Q N : Int}, claims t₁ = [.inl (Q, N)] → claims t₂ = [.inl (Q, N)] → False :=
      fun {Q N} e₁ e₂ => w.2 _ _ _ _ hk ht₁ ht₂ (.inl (Q, N)) (by rw [e₁]; simp) (by rw [e₂]; simp)
    refine ⟨keys_compat ?_ hp₁ hp₂, adds_compat ?_ hV₁ hV₂ hv₁ hv₂⟩
    · intro e; cases e
      cases hL₁.symm.trans hL₂
      exact same hc₁ hc₂
    · intro e; cases e
      exact same hc₁ hc₂

/-- The integer a binding of `<procs>` counts the segments of its process by. -/
noncomputable def stN : Option Handoff.SortKItem → Int
  | some (.inj_KItem (.«st(_,_)» n _)) => n
  | _ => 0

/-- The step `st(N, S) => st(N +Int 1, _)` changes the binding. -/
theorem st_ne {N S S' : Int} :
    (some (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» (IntHook.add N 1) S')) : Option Handoff.SortKItem) ≠
      some (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» N S)) := by
  intro h
  have := congrArg stN h
  simp only [stN, IntHook.add] at this
  omega

/-- The task map, `<procs>` and `<vals>` of a configuration. -/
abbrev cfg (m : Handoff.SortTaskCellMap) (p : Handoff.SortProcsCell) (v : Handoff.SortValsCell)
    (g : Handoff.SortGeneratedCounterCell) : Handoff.SortGeneratedTopCell :=
  Handoff.SortGeneratedTopCell.«<generatedTop>» (Handoff.SortTCell.«<T>» (Handoff.SortTasksCell.«<tasks>» m) p v) g

theorem eff_new {m D3 r : Handoff.SortTaskCellMap} {k : Handoff.SortTidCell} {G : Handoff.SortNCell}
    {Q S : Int} {D L' : Handoff.SortMap} {Vc : Handoff.SortValsCell} {g : Handoff.SortGeneratedCounterCell}
    {ch : Change}
    (hm : MapHook.concat (MapHook.element k (Handoff.SortTaskCell.«<task>» k G (Handoff.SortKCell.«<k>»
      (Handoff.SortK.kseq (Handoff.SortKItem.inj_Instr (Handoff.SortInstr.«new(_,_)» Q S)) Handoff.SortK.dotk)))) D3 = some m)
    (hr : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Int Q)
      (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» 0 S))) D = some L')
    (o : (∃ a b, MStep a b ch (cfg m (.«<procs>» D) Vc g) (cfg r (.«<procs>» L') Vc g)) ∨
      SStep ch (cfg m (.«<procs>» D) Vc g) (cfg r (.«<procs>» L') Vc g))
    (sm : ch.Small) (i : ch.vals = none ∧ ch.generatedCounter = none) :
    Eff (cfg m (.«<procs>» D) Vc g) ch k := by
  obtain ⟨pp, pa, -, -⟩ := cells_step o
  have pp : ch.procs.pre D := pp
  have pa : ch.procs.apply D = L' := pa
  have f := ins_facts hr
  exact .new _ Q (MapHook.lookup_of_concat_element hm) rfl f.2.1
    (mch_keys sm.1 pp pa (by rw [f.1, f.2.1]; simp) f.2.2 (by rw [f.1]; simp)) i.1

theorem eff_lit {m D4 r : Handoff.SortTaskCellMap} {k : Handoff.SortTidCell} {G : Handoff.SortNCell}
    {Q N V S x y : Int} {m2 D2 r9 D3 r11 : Handoff.SortMap} {g : Handoff.SortGeneratedCounterCell} {ch : Change}
    (hm : MapHook.concat (MapHook.element k (Handoff.SortTaskCell.«<task>» k G (Handoff.SortKCell.«<k>»
      (Handoff.SortK.kseq (Handoff.SortKItem.inj_Instr (Handoff.SortInstr.«resume(_,_,_)» Q N (Handoff.SortInp.inj_Int V)))
        Handoff.SortK.dotk)))) D4 = some m)
    (hm5 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Int Q)
      (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» N S))) D2 = some m2)
    (hr10 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Int Q)
      (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» (IntHook.add N 1) x))) D2 = some r9)
    (hr12 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Oid (Handoff.SortOid.«o(_,_)» Q N))
      (Handoff.SortKItem.inj_Int y)) D3 = some r11)
    (o : (∃ a b, MStep a b ch (cfg m (.«<procs>» m2) (.«<vals>» D3) g) (cfg r (.«<procs>» r9) (.«<vals>» r11) g)) ∨
      SStep ch (cfg m (.«<procs>» m2) (.«<vals>» D3) g) (cfg r (.«<procs>» r9) (.«<vals>» r11) g))
    (sm : ch.Small) :
    Eff (cfg m (.«<procs>» m2) (.«<vals>» D3) g) ch k := by
  obtain ⟨pp, pa, vp, va⟩ := cells_step o
  have pp : ch.procs.pre m2 := pp
  have pa : ch.procs.apply m2 = r9 := pa
  have vp : ch.vals.pre D3 := vp
  have va : ch.vals.apply D3 = r11 := va
  have f := repl_facts hm5 hr10
  have h := ins_facts hr12
  exact .res _ Q N S (MapHook.lookup_of_concat_element hm) rfl f.2.1
    (mch_keys sm.1 pp pa (by rw [f.1, f.2.1]; exact st_ne) f.2.2 (by rw [f.1]; simp)) h.2.1
    (mch_shape (L := D3) vp va (by rw [h.1, h.2.1]; simp) h.2.2)

theorem eff_oid {m D4 r : Handoff.SortTaskCellMap} {k : Handoff.SortTidCell} {G : Handoff.SortNCell}
    {Q N V S x y : Int} {I : Handoff.SortOid} {m2 D2 r15 m3 D3 r17 r19 : Handoff.SortMap}
    {g : Handoff.SortGeneratedCounterCell} {ch : Change}
    (hm : MapHook.concat (MapHook.element k (Handoff.SortTaskCell.«<task>» k G (Handoff.SortKCell.«<k>»
      (Handoff.SortK.kseq (Handoff.SortKItem.inj_Instr (Handoff.SortInstr.«resume(_,_,_)» Q N (Handoff.SortInp.inj_Oid I)))
        Handoff.SortK.dotk)))) D4 = some m)
    (hm6 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Int Q)
      (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» N S))) D2 = some m2)
    (hr16 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Int Q)
      (Handoff.SortKItem.inj_KItem (Handoff.SortKItem.Own.«st(_,_)» (IntHook.add N 1) x))) D2 = some r15)
    (hm13 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Oid I) (Handoff.SortKItem.inj_Int V)) D3 = some m3)
    (hr18 : MapHook.concat (MapHook.element (Handoff.SortKItem.inj_Oid I) (Handoff.SortKItem.inj_Int V))
      (MapHook.element (Handoff.SortKItem.inj_Oid (Handoff.SortOid.«o(_,_)» Q N))
        (Handoff.SortKItem.inj_Int y)) = some r17)
    (hr20 : MapHook.concat r17 D3 = some r19)
    (o : (∃ a b, MStep a b ch (cfg m (.«<procs>» m2) (.«<vals>» m3) g) (cfg r (.«<procs>» r15) (.«<vals>» r19) g)) ∨
      SStep ch (cfg m (.«<procs>» m2) (.«<vals>» m3) g) (cfg r (.«<procs>» r15) (.«<vals>» r19) g))
    (sm : ch.Small) :
    Eff (cfg m (.«<procs>» m2) (.«<vals>» m3) g) ch k := by
  obtain ⟨pp, pa, vp, va⟩ := cells_step o
  have pp : ch.procs.pre m2 := pp
  have pa : ch.procs.apply m2 = r15 := pa
  have vp : ch.vals.pre m3 := vp
  have va : ch.vals.apply m3 = r19 := va
  have f := repl_facts hm6 hr16
  have h := ext_facts hm13 hr18 hr20
  exact .res _ Q N S (MapHook.lookup_of_concat_element hm) rfl f.2.1
    (mch_keys sm.1 pp pa (by rw [f.1, f.2.1]; exact st_ne) f.2.2 (by rw [f.1]; simp)) h.2.1
    (mch_shape (L := m3) vp va (by rw [h.1, h.2.1]; simp) h.2.2)

theorem hand.join.key.new.new : join.key.new.new.statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, D2, D1, D0, kk, D3, G5, Q, S, r, r2, hm, hr, hr3, e, e'⟩ := Inst.of s₁
  obtain ⟨m', D2', D1', D0', kk', D3', G5', Q', S', r', r2', hm', hr', hr3', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  · exact (hk (eff_compat hinv hkk (eff_new hm hr3 o₁ k₁ i₁) (eff_new hm' hr3' o₂ k₂ i₂))).elim

theorem hand.join.key.new.«resume-lit» : join.key.new.«resume-lit».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, D2, D1, D0, kk, D3, G5, Q, S, r, r2, hm, hr, hr3, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', D3', D0', kk', D4', G6', Q', N', V', D2', S', r', x9', r9', y13', r11', hm', hm5', hr', fn10', hr10', fo14', hr12', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
  · exact (hk (eff_compat hinv hkk (eff_new hm hr3 o₁ k₁ i₁) (eff_lit hm' hm5' hr10' hr12' o₂ k₂))).elim

theorem hand.join.key.new.«resume-oid» : join.key.new.«resume-oid».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, D2, D1, D0, kk, D3, G5, Q, S, r, r2, hm, hr, hr3, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', m3', D0', kk', D4', G6', Q', N', I', D2', S', D3', V', r', x15', r15', y19', r17', r19', hm', hm6', hm13', hr', fn16', hr16', fo20', hr18', hr20', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
  · exact (hk (eff_compat hinv hkk (eff_new hm hr3 o₁ k₁ i₁) (eff_oid hm' hm6' hr16' hm13' hr18' hr20' o₂ k₂))).elim

theorem hand.join.key.«resume-lit».new : join.key.«resume-lit».new.statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, D3, D0, kk, D4, G6, Q, N, V, D2, S, r, x9, r9, y13, r11, hm, hm5, hr, fn10, hr10, fo14, hr12, e, e'⟩ := Inst.of s₁
  obtain ⟨m', D2', D1', D0', kk', D3', G5', Q', S', r', r2', hm', hr', hr3', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
  · exact (hk (eff_compat hinv hkk (eff_lit hm hm5 hr10 hr12 o₁ k₁) (eff_new hm' hr3' o₂ k₂ i₂))).elim

theorem hand.join.key.«resume-oid».new : join.key.«resume-oid».new.statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, m3, D0, kk, D4, G6, Q, N, I, D2, S, D3, V, r, x15, r15, y19, r17, r19, hm, hm6, hm13, hr, fn16, hr16, fo20, hr18, hr20, e, e'⟩ := Inst.of s₁
  obtain ⟨m', D2', D1', D0', kk', D3', G5', Q', S', r', r2', hm', hr', hr3', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
  · exact (hk (eff_compat hinv hkk (eff_oid hm hm6 hr16 hm13 hr18 hr20 o₁ k₁) (eff_new hm' hr3' o₂ k₂ i₂))).elim

theorem hand.join.key.«resume-lit».«resume-lit» : join.key.«resume-lit».«resume-lit».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, D3, D0, kk, D4, G6, Q, N, V, D2, S, r, x9, r9, y13, r11, hm, hm5, hr, fn10, hr10, fo14, hr12, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', D3', D0', kk', D4', G6', Q', N', V', D2', S', r', x9', r9', y13', r11', hm', hm5', hr', fn10', hr10', fo14', hr12', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  · exact (hk (eff_compat hinv hkk (eff_lit hm hm5 hr10 hr12 o₁ k₁) (eff_lit hm' hm5' hr10' hr12' o₂ k₂))).elim

theorem hand.join.key.«resume-lit».«resume-oid» : join.key.«resume-lit».«resume-oid».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, D3, D0, kk, D4, G6, Q, N, V, D2, S, r, x9, r9, y13, r11, hm, hm5, hr, fn10, hr10, fo14, hr12, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', m3', D0', kk', D4', G6', Q', N', I', D2', S', D3', V', r', x15', r15', y19', r17', r19', hm', hm6', hm13', hr', fn16', hr16', fo20', hr18', hr20', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
  · exact (hk (eff_compat hinv hkk (eff_lit hm hm5 hr10 hr12 o₁ k₁) (eff_oid hm' hm6' hr16' hm13' hr18' hr20' o₂ k₂))).elim

theorem hand.join.key.«resume-oid».«resume-lit» : join.key.«resume-oid».«resume-lit».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, m3, D0, kk, D4, G6, Q, N, I, D2, S, D3, V, r, x15, r15, y19, r17, r19, hm, hm6, hm13, hr, fn16, hr16, fo20, hr18, hr20, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', D3', D0', kk', D4', G6', Q', N', V', D2', S', r', x9', r9', y13', r11', hm', hm5', hr', fn10', hr10', fo14', hr12', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
  · exact (hk (eff_compat hinv hkk (eff_oid hm hm6 hr16 hm13 hr18 hr20 o₁ k₁) (eff_lit hm' hm5' hr10' hr12' o₂ k₂))).elim

theorem hand.join.key.«resume-oid».«resume-oid» : join.key.«resume-oid».«resume-oid».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, m3, D0, kk, D4, G6, Q, N, I, D2, S, D3, V, r, x15, r15, y19, r17, r19, hm, hm6, hm13, hr, fn16, hr16, fo20, hr18, hr20, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', m3', D0', kk', D4', G6', Q', N', I', D2', S', D3', V', r', x15', r15', y19', r17', r19', hm', hm6', hm13', hr', fn16', hr16', fo20', hr18', hr20', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases hkk : kk = kk'
  · subst hkk
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  · exact (hk (eff_compat hinv hkk (eff_oid hm hm6 hr16 hm13 hr18 hr20 o₁ k₁) (eff_oid hm' hm6' hr16' hm13' hr18' hr20' o₂ k₂))).elim

end HandoffConf
