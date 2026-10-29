import KPrelude.MapRep
import HandoffSeq.Rules
import Handoff.Rules

/-! Every step of `handoffseq` is matched by steps of `handoff`. The script's next instruction
`I ; P` is, in `handoff`, the root task's next fork: the fork puts `I` in a task of its own, the task
takes `I`'s step on the same bindings, and `done` removes it, which leaves the root with `P`. The
end of the script, `.Pgm`, is the root's `nil` and `done`, which leave no task.

The two definitions' `<procs>` and `<vals>` hold the same bindings (`Rep`, one function each, of
`Q` to `st(N, S)` and of `o(Q, N)` to an `Int`), and `handoffseq` runs `handoff`'s lower layer
(`seqHooks`). -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffSeqRel

open KPrelude MapHook MapRep

variable [Handoff.Hooks]

/-- `handoffseq`'s lower layer is `handoff`'s. -/
instance seqHooks : HandoffSeq.Hooks :=
  ⟨Handoff.Hooks.«fn.next(_,_)_HANDOFF_Int_Int_Int», Handoff.Hooks.«fn.out(_,_)_HANDOFF_Int_Int_Int»⟩

/-! ## Programs -/

def trOid : HandoffSeq.SortOid → Handoff.SortOid
  | .«o(_,_)» Q N => .«o(_,_)» Q N

def trInp : HandoffSeq.SortInp → Handoff.SortInp
  | .inj_Int V => .inj_Int V
  | .inj_Oid I => .inj_Oid (trOid I)

def trInstr : HandoffSeq.SortInstr → Handoff.SortInstr
  | .«new(_,_)» Q S => .«new(_,_)» Q S
  | .«resume(_,_,_)» Q N I => .«resume(_,_,_)» Q N (trInp I)

/-- A script of `handoffseq` as a script of `handoff`: the same instructions in the same order. -/
def trPgm : HandoffSeq.SortPgm → Handoff.SortPgm
  | .«_;_» I P => .«_;_» (trInstr I) (trPgm P)
  | .«.List{"_;__HANDOFFSEQ-SYNTAX_Pgm_Instr_Pgm"}_Pgm» =>
    .«.List{"_;__HANDOFF-SYNTAX_Pgm_Instr_Pgm"}_Pgm»

@[simp] theorem trPgm_cons (I : HandoffSeq.SortInstr) (P : HandoffSeq.SortPgm) :
    trPgm (.«_;_» I P) = .«_;_» (trInstr I) (trPgm P) := by simp [trPgm]

@[simp] theorem trPgm_nil : trPgm .«.List{"_;__HANDOFFSEQ-SYNTAX_Pgm_Instr_Pgm"}_Pgm» =
    .«.List{"_;__HANDOFF-SYNTAX_Pgm_Instr_Pgm"}_Pgm» := by simp [trPgm]

/-! ## The bindings, in each definition's constructors -/

/-- `Q` in `<procs>`. -/
abbrev pkS (Q : Int) : HandoffSeq.SortKItem := .inj_Int Q
/-- `st(N, S)` in `<procs>`. -/
abbrev pvS (p : Int × Int) : HandoffSeq.SortKItem := .inj_KItem (.«st(_,_)» p.1 p.2)
/-- `o(Q, N)` in `<vals>`. -/
abbrev vkS (p : Int × Int) : HandoffSeq.SortKItem := .inj_Oid (.«o(_,_)» p.1 p.2)
/-- A value in `<vals>`. -/
abbrev vvS (V : Int) : HandoffSeq.SortKItem := .inj_Int V
abbrev pkR (Q : Int) : Handoff.SortKItem := .inj_Int Q
abbrev pvR (p : Int × Int) : Handoff.SortKItem := .inj_KItem (.«st(_,_)» p.1 p.2)
abbrev vkR (p : Int × Int) : Handoff.SortKItem := .inj_Oid (.«o(_,_)» p.1 p.2)
abbrev vvR (V : Int) : Handoff.SortKItem := .inj_Int V

theorem pkS_inj : Function.Injective pkS := fun a b h => by simpa using h
theorem pvS_inj : Function.Injective pvS := fun a b h => by simp at h; exact Prod.ext h.1 h.2
theorem vkS_inj : Function.Injective vkS := fun a b h => by simp at h; exact Prod.ext h.1 h.2
theorem vvS_inj : Function.Injective vvS := fun a b h => by simpa using h
theorem pkR_inj : Function.Injective pkR := fun a b h => by simpa using h
theorem pvR_inj : Function.Injective pvR := fun a b h => by simp at h; exact Prod.ext h.1 h.2
theorem vkR_inj : Function.Injective vkR := fun a b h => by simp at h; exact Prod.ext h.1 h.2
theorem vvR_inj : Function.Injective vvR := fun a b h => by simpa using h

/-- The processes: `Q` at turn `N` in state `S`. -/
abbrev Procs := Int → Option (Int × Int)
/-- The values: the output of the `N`-th segment of `Q`. -/
abbrev Vals := Int × Int → Option Int

/-! ## The relation -/

/-- A configuration of `handoffseq`. -/
abbrev scfg (k : HandoffSeq.SortK) (sp sv : HandoffSeq.SortMap) (c : HandoffSeq.SortGeneratedCounterCell) :
    HandoffSeq.SortGeneratedTopCell :=
  .«<generatedTop>» (.«<T>» (.«<k>» k) (.«<procs>» sp) (.«<vals>» sv)) c

/-- A configuration of `handoff`. -/
abbrev rcfg (tm : Handoff.SortTaskCellMap) (pc : Handoff.SortProcsCell) (vc : Handoff.SortValsCell)
    (c : Handoff.SortGeneratedCounterCell) : Handoff.SortGeneratedTopCell :=
  .«<generatedTop>» (.«<T>» (.«<tasks>» tm) pc vc) c

abbrev t0 : Handoff.SortTidCell := .«<tid>» 0

/-- The root task, at its `n`-th fork, with the script `P` left. -/
abbrev root (n : Int) (P : Handoff.SortPgm) : Handoff.SortTaskCell :=
  .«<task>» t0 (.«<n>» n) (.«<k>» (.kseq (.inj_Pgm P) .dotk))

/-- `handoffseq` with `P` left, over `f` and `g`. -/
def SAt (s : HandoffSeq.SortGeneratedTopCell) (P : HandoffSeq.SortPgm) (f : Procs) (g : Vals) : Prop :=
  ∃ sp sv c, s = scfg (.kseq (.inj_Pgm P) .dotk) sp sv c ∧ Rep pkS pvS sp f ∧ Rep vkS vvS sv g

/-- `handoff` with only the root task, `P` left, over `f` and `g`. -/
def RAt (r : Handoff.SortGeneratedTopCell) (P : Handoff.SortPgm) (f : Procs) (g : Vals) : Prop :=
  ∃ n rp rv c, 0 ≤ n ∧ r = rcfg (update unit t0 (root n P)) (.«<procs>» rp) (.«<vals>» rv) c ∧
    Rep pkR pvR rp f ∧ Rep vkR vvR rv g

/-- The script is done in `handoffseq`. -/
def SDone (s : HandoffSeq.SortGeneratedTopCell) (f : Procs) (g : Vals) : Prop :=
  ∃ sp sv c, s = scfg .dotk sp sv c ∧ Rep pkS pvS sp f ∧ Rep vkS vvS sv g

/-- No task is left in `handoff`. -/
def RDone (r : Handoff.SortGeneratedTopCell) (f : Procs) (g : Vals) : Prop :=
  ∃ rp rv c, r = rcfg unit (.«<procs>» rp) (.«<vals>» rv) c ∧ Rep pkR pvR rp f ∧ Rep vkR vvR rv g

/-- Both sides at the same point of the script. -/
def Sim (s : HandoffSeq.SortGeneratedTopCell) (r : Handoff.SortGeneratedTopCell) : Prop :=
  ∃ P f g, SAt s P f g ∧ RAt r (trPgm P) f g

/-- Both sides done, with the same bindings. -/
def Fin (s : HandoffSeq.SortGeneratedTopCell) (r : Handoff.SortGeneratedTopCell) : Prop :=
  ∃ f g, SDone s f g ∧ RDone r f g

/-! ## A task's run in `handoff` -/

/-- A task that takes its step keeps its key, with nothing left to run. -/
theorem done_some {k : Handoff.SortTidCell} {t t' : Handoff.SortTaskCell} {D m : Handoff.SortTaskCellMap}
    (h : concat (element k t) D = some m) : concat (element k t') D = some (update D k t') :=
  let ⟨hw, hn, _⟩ := concat_element_iff.1 h
  ins_some hw hn

theorem t0_ne {n : Int} (hn : 0 ≤ n) :
    (.«<tid>» (IntHook.add n 1) : Handoff.SortTidCell) ≠ .«<tid>» 0 := by
  intro h
  have e : n + 1 = (0 : Int) := by simpa [IntHook.add] using h
  omega

/-- The root's fork of `I`, `I`'s step (`hI`, at any key and rest of the map), and `done`. -/
theorem run_instr {n : Int} {I : Handoff.SortInstr} {P : Handoff.SortPgm}
    {pc pc' : Handoff.SortProcsCell} {vc vc' : Handoff.SortValsCell} {c : Handoff.SortGeneratedCounterCell}
    (hn : 0 ≤ n)
    (hI : ∀ (k : Handoff.SortTidCell) (G : Handoff.SortNCell) (D m : Handoff.SortTaskCellMap),
      concat (element k (.«<task>» k G (.«<k>» (.kseq (.inj_Instr I) .dotk)))) D = some m →
      Handoff.Step (rcfg m pc vc c) (rcfg (update D k (.«<task>» k G (.«<k>» .dotk))) pc' vc' c)) :
    Star Handoff.Step (rcfg (update unit t0 (root n (.«_;_» I P))) pc vc c)
      (rcfg (update unit t0 (root (IntHook.add n 1) P)) pc' vc' c) := by
  let tN : Handoff.SortTidCell := .«<tid>» (IntHook.add n 1)
  let tI : Handoff.SortTaskCell := .«<task>» tN (.«<n>» 0) (.«<k>» (.kseq (.inj_Instr I) .dotk))
  have ne := t0_ne hn
  obtain ⟨x, hx⟩ := concat_exists (wf_element (M := Handoff.SortTaskCellMap) (k := t0)
    (v := root (IntHook.add n 1) P)) (wf_element (M := Handoff.SortTaskCellMap) (k := tN) (v := tI))
    fun j => by
      by_cases hj : j = t0
      · subst hj; exact Or.inr (lookup_element_ne (Ne.symm ne))
      · exact Or.inl (lookup_element_ne hj)
  obtain ⟨r₂, hr₂⟩ := concat_exists (wf_of_concat hx) (wf_unit (M := Handoff.SortTaskCellMap))
    fun j => Or.inr (lookup_unit' (M := Handoff.SortTaskCellMap) j)
  have w₂ := wf_of_concat hr₂
  have fork : Handoff.Step (rcfg (update unit t0 (root n (.«_;_» I P))) pc vc c) (rcfg r₂ pc vc c) :=
    Handoff.Step.fork (hm := ins_some wf_unit (lookup_unit' _)) (hlit := rfl) (hr := hx) (hr_3 := hr₂) ..
  have lI : lookup r₂ tN = some tI := lookup_of_concat hr₂ (lookup_of_concat_element_right hx)
  have step := hI tN (.«<n>» 0) (remove r₂ tN) r₂ (concat_element_remove w₂ lI)
  have done : Handoff.Step
      (rcfg (update (remove r₂ tN) tN (.«<task>» tN (.«<n>» 0) (.«<k>» .dotk))) pc' vc' c)
      (rcfg (remove r₂ tN) pc' vc' c) :=
    Handoff.Step.done (hm := ins_some (wf_remove w₂) (lookup_remove_self _ w₂)) ..
  have e : remove r₂ tN = update unit t0 (root (IntHook.add n 1) P) := by
    refine ext (wf_remove w₂) (wf_update wf_unit) fun j => ?_
    by_cases hj : j = tN
    · subst hj; rw [lookup_remove_self _ w₂, lookup_update_ne _ _ ne, lookup_unit']
    · rw [lookup_remove_ne hj w₂, lookup_concat hr₂, lookup_concat hx, lookup_unit',
        lookup_element_ne (v := tI) hj]
      by_cases h0 : j = t0
      · subst h0; rw [lookup_element_self, lookup_update_self]; rfl
      · rw [lookup_element_ne h0, lookup_update_ne _ _ h0, lookup_unit']; rfl
  rw [← e]
  exact .step fork (.step step (.step done (.refl _)))

/-- The root's `nil` and `done`. -/
theorem run_nil {n : Int} {pc : Handoff.SortProcsCell} {vc : Handoff.SortValsCell}
    {c : Handoff.SortGeneratedCounterCell} :
    Star Handoff.Step
      (rcfg (update unit t0 (root n .«.List{"_;__HANDOFF-SYNTAX_Pgm_Instr_Pgm"}_Pgm»)) pc vc c)
      (rcfg unit pc vc c) :=
  .step (Handoff.Step.nil (hm := ins_some wf_unit (lookup_unit' _))
      (hr := ins_some wf_unit (lookup_unit' _)) ..)
    (.step (Handoff.Step.done (hm := ins_some wf_unit (lookup_unit' _)) ..) (.refl _))

/-- With no task left, `handoff` is terminal. -/
theorem terminal_rdone {pc : Handoff.SortProcsCell} {vc : Handoff.SortValsCell}
    {c : Handoff.SortGeneratedCounterCell} : Terminal Handoff.Step (rcfg unit pc vc c) := by
  have key : ∀ {k : Handoff.SortTidCell} {t : Handoff.SortTaskCell} {D : Handoff.SortTaskCellMap},
      concat (element k t) D ≠ some unit := fun h => by
    have := lookup_of_concat_element h
    rw [lookup_unit'] at this; cases this
  intro c' h
  cases h <;> exact key ‹_›

/-! ## The simulation -/

theorem step_sim {s s' : HandoffSeq.SortGeneratedTopCell} {r : Handoff.SortGeneratedTopCell}
    (h : Sim s r) (st : HandoffSeq.Step s s') :
    ∃ r', Star Handoff.Step r r' ∧ (Sim s' r' ∨ Fin s' r') := by
  obtain ⟨P, f, g, ⟨sp, sv, c, rfl, hp, hv⟩, ⟨n, rp, rv, c', hn, rfl, hp', hv'⟩⟩ := h
  have hn1 : 0 ≤ IntHook.add n 1 := by simp [IntHook.add]; omega
  cases st with
  | new Q S P₁ _ _ _ sp' hr =>
    simp only [trPgm_cons, trInstr]
    have l₀ : f Q = none := rep_none pkS_inj hp (concat_element_iff.1 hr).2.1
    have l₁ : lookup rp (pkR Q) = none := by rw [rep_lookup pkR_inj hp', l₀]; rfl
    refine ⟨_, run_instr (I := .«new(_,_)» Q S) hn fun k G D m hm =>
      Handoff.Step.new (hm := hm) (hr := done_some hm) (hr_3 := ins_some hp'.1 l₁) .., Or.inl ?_⟩
    exact ⟨P₁, upd f Q (0, S), g, ⟨sp', sv, c, rfl, rep_insert pkS_inj hp hr, hv⟩,
      ⟨_, _, rv, c', hn1, rfl, rep_insert pkR_inj hp' (ins_some hp'.1 l₁), hv'⟩⟩
  | «resume-lit» Q N V P₁ _ D3 _ D2 S r9 sp' r4 sv' hm hr hr_3 hr_5 hr_7 =>
    simp only [trPgm_cons, trInstr, trInp]
    have l₀ : f Q = some (N, S) := rep_some pkS_inj pvS_inj hp (lookup_of_concat_element hm)
    have l₁ : lookup rp (pkR Q) = some (pvR (N, S)) := by rw [rep_lookup pkR_inj hp', l₀]; rfl
    have v₀ : g (Q, N) = none := rep_none vkS_inj hv (concat_element_iff.1 hr_7).2.1
    have v₁ : lookup rv (vkR (Q, N)) = none := by rw [rep_lookup vkR_inj hv', v₀]; rfl
    have hm₅ := concat_element_remove hp'.1 l₁
    have hr₁₂ := rebind_some (v := pvR (IntHook.add N 1, r9)) hp'.1 (k := pkR Q)
    have hr₁₆ := ins_some (v := vvR r4) hv'.1 v₁
    refine ⟨_, run_instr (I := .«resume(_,_,_)» Q N (.inj_Int V)) hn fun k G D m hmT =>
      Handoff.Step.«resume-lit» (hm := hmT) (hm_5 := hm₅) (hr := done_some hmT) (hr_10 := hr)
        (hr_12 := hr₁₂) (hr_14 := hr_5) (hr_16 := hr₁₆) .., Or.inl ?_⟩
    exact ⟨P₁, upd f Q (IntHook.add N 1, r9), upd g (Q, N) r4,
      ⟨sp', sv', c, rfl, rep_rebind pkS_inj hp hm hr_3, rep_insert vkS_inj hv hr_7⟩,
      ⟨_, _, _, c', hn1, rfl, rep_rebind pkR_inj hp' hm₅ hr₁₂, rep_insert vkR_inj hv' hr₁₆⟩⟩
  | «resume-oid» Q N I P₁ _ _ _ D2 S D3 V r9 sp' r10 x sv' hm hm_6 hr hr_9 hr_11 hr_13 hr_15 =>
    -- the input is a binding `o(P, M) ↦ V` of `<vals>`
    obtain ⟨⟨P', M'⟩, V', eI, eV, gI⟩ := (hv.2 _ _).1 (lookup_of_concat_element hm_6)
    have eV' : V = V' := by simpa using eV
    subst eV'
    have eI' : I = .«o(_,_)» P' M' := by simpa using eI
    subst eI'
    simp only [trPgm_cons, trInstr, trInp, trOid]
    have l₀ : f Q = some (N, S) := rep_some pkS_inj pvS_inj hp (lookup_of_concat_element hm)
    have l₁ : lookup rp (pkR Q) = some (pvR (N, S)) := by rw [rep_lookup pkR_inj hp', l₀]; rfl
    have i₁ : lookup rv (vkR (P', M')) = some (vvR V) := by rw [rep_lookup vkR_inj hv', gI]; rfl
    -- `o(Q, N)` is unbound, and not the input
    have ne : vkS (P', M') ≠ vkS (Q, N) := by
      intro e
      have := concat_disj_lookup hr_13 (vkS (P', M'))
      rw [lookup_element_self] at this
      rw [e, lookup_element_self] at this
      simp at this
    have neR : vkR (P', M') ≠ vkR (Q, N) := fun e => ne (by rw [vkR_inj e])
    have o₀ : lookup sv (vkS (Q, N)) = none := by
      rw [lookup_concat hm_6, lookup_element_ne (Ne.symm ne)]
      rcases concat_disj_lookup hr_15 (vkS (Q, N)) with e | e
      · rw [lookup_of_concat_element_right hr_13] at e; cases e
      · rw [e]; rfl
    have v₀ : g (Q, N) = none := rep_none vkS_inj hv o₀
    have v₁ : lookup rv (vkR (Q, N)) = none := by rw [rep_lookup vkR_inj hv', v₀]; rfl
    obtain ⟨x', hx⟩ := concat_exists (wf_element (M := Handoff.SortMap) (k := vkR (P', M')) (v := vvR V))
      (wf_element (M := Handoff.SortMap) (k := vkR (Q, N)) (v := vvR r10)) fun j => by
        by_cases hj : j = vkR (P', M')
        · subst hj; exact Or.inr (lookup_element_ne neR)
        · exact Or.inl (lookup_element_ne hj)
    obtain ⟨y, hy⟩ := concat_exists (wf_of_concat hx) (wf_remove (k := vkR (P', M')) hv'.1) fun j => by
      by_cases hj : j = vkR (P', M')
      · subst hj; exact Or.inr (lookup_remove_self _ hv'.1)
      · by_cases hj' : j = vkR (Q, N)
        · subst hj'; exact Or.inr (by rw [lookup_remove_ne hj hv'.1]; exact v₁)
        · exact Or.inl (by rw [lookup_concat hx, lookup_element_ne hj, lookup_element_ne hj']; rfl)
    have hm₆ := concat_element_remove hp'.1 l₁
    have hm₁₃ := concat_element_remove hv'.1 i₁
    have hr₁₈ := rebind_some (v := pvR (IntHook.add N 1, r9)) hp'.1 (k := pkR Q)
    refine ⟨_, run_instr (I := .«resume(_,_,_)» Q N (.inj_Oid (.«o(_,_)» P' M'))) hn
      fun k G D m hmT =>
      Handoff.Step.«resume-oid» (hm := hmT) (hm_6 := hm₆) (hm_13 := hm₁₃) (hr := done_some hmT)
        (hr_16 := hr) (hr_18 := hr₁₈) (hr_20 := hr_11) (hr_22 := hx) (hr_24 := hy) .., Or.inl ?_⟩
    exact ⟨P₁, upd f Q (IntHook.add N 1, r9), upd g (Q, N) r10,
      ⟨sp', sv', c, rfl, rep_rebind pkS_inj hp hm hr_9, rep_insert2 vkS_inj hv hm_6 hr_13 hr_15⟩,
      ⟨_, _, _, c', hn1, rfl, rep_rebind pkR_inj hp' hm₆ hr₁₈, rep_insert2 vkR_inj hv' hm₁₃ hx hy⟩⟩
  | nil =>
    simp only [trPgm_nil]
    exact ⟨_, run_nil, Or.inr ⟨f, g, ⟨sp, sv, c, rfl, hp, hv⟩, ⟨rp, rv, c', rfl, hp', hv'⟩⟩⟩

end HandoffSeqRel
