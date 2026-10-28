import UtxoConf.Views

namespace UtxoConf

open KPrelude

/-- The proof of an inversion lemma: a step of the rule is an instance of it. -/
local macro "k2l_elim_tac" r:ident : tactic =>
  `(tactic| (unfold $r:ident; intros; dsimp only; intro G' k'; apply k' <;> first | rfl | assumption))

/-- Invert a step by rule `seq`. -/
theorem elim_seq {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .seq c c₁) {G : Prop}
    (k : Utxo.Step.Rel.seq (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.seq (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.seq) G k

/-- Invert a step by rule `nil`. -/
theorem elim_nil {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .nil c c₁) {G : Prop}
    (k : Utxo.Step.Rel.nil (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.nil (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.nil) G k

/-- Invert a step by rule `create`. -/
theorem elim_create {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .create c c₁) {G : Prop}
    (k : Utxo.Step.Rel.create (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.create (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.create) G k

/-- Invert a step by rule `spend`. -/
theorem elim_spend {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .spend c c₁) {G : Prop}
    (k : Utxo.Step.Rel.spend (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.spend (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.spend) G k

/-- Invert a step by rule `spawn`. -/
theorem elim_spawn {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .spawn c c₁) {G : Prop}
    (k : Utxo.Step.Rel.spawn (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.spawn (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.spawn) G k

/-- Invert a step by rule `yield`. -/
theorem elim_yield {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .yield c c₁) {G : Prop}
    (k : Utxo.Step.Rel.yield (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.yield (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.yield) G k

/-- Invert a step by rule `resume`. -/
theorem elim_resume {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .resume c c₁) {G : Prop}
    (k : Utxo.Step.Rel.resume (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.resume (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.resume) G k

/-- Invert a step by rule `done`. -/
theorem elim_done {c c₁ : Utxo.SortGeneratedTopCell} (h : StepBy .done c c₁) {G : Prop}
    (k : Utxo.Step.Rel.done (fun d d₁ => d = c → d₁ = c₁ → G)) : G :=
  h (fun d d₁ => ∀ G : Prop, Utxo.Step.Rel.done (fun e e₁ => e = d → e₁ = d₁ → G) → G)
    (by k2l_elim_tac Utxo.Step.Rel.done) G k

/-- A key pattern list of one key fits one binding. -/
theorem fits1 {T K : Type} {view : T → KeyView} {x : KeyPat} :
    ∀ {bs : List (K × T)}, KeyPat.Fits view [x] bs → ∃ p, bs = [p]
  | [], f => f.elim
  | [p], _ => ⟨p, rfl⟩
  | _ :: _ :: _, f => f.2.elim

/-- A key pattern list of two keys fits two bindings. -/
theorem fits2 {T K : Type} {view : T → KeyView} {x y : KeyPat} :
    ∀ {bs : List (K × T)}, KeyPat.Fits view [x, y] bs → ∃ p q, bs = [p, q]
  | [], f => f.elim
  | [_], f => f.2.elim
  | [p, q], _ => ⟨p, q, rfl⟩
  | _ :: _ :: _ :: _, f => f.2.2.elim

/-- A part of the thread map binding two keys, two different keys of which are `x` and `y`, binds
no other. -/
theorem pair_keys {a : Utxo.SortProcCellMap} {p q} (d : MapHook.Binds a [p, q]) {x y k}
    (hx : MapHook.lookup a x ≠ none) (hy : MapHook.lookup a y ≠ none) (hxy : x ≠ y)
    (hk : MapHook.lookup a k ≠ none) : k = x ∨ k = y := by
  have key : ∀ z, MapHook.lookup a z ≠ none → z = p.1 ∨ z = q.1 := fun z hz => by
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hz
    have := (d z w).1 hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with e | e <;> rw [← e]
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases key x hx with ex | ex <;> rcases key y hy with ey | ey <;> rcases key k hk with ek | ek
  all_goals first
    | exact Or.inl (ek.trans ex.symm)
    | exact Or.inr (ek.trans ey.symm)
    | exact absurd (ex.trans ey.symm) hxy

/-- A part of the thread map binding one key binds no other. -/
theorem one_key {a : Utxo.SortProcCellMap} {p} (d : MapHook.Binds a [p]) {k}
    (h : MapHook.lookup a k ≠ none) : k = p.1 := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
  have := (d k w).1 hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rw [← this]

/-- The key a one-binding view of a step matches is the one whose binding the step changes. -/
theorem key_of_view {a b R m m' : Utxo.SortProcCellMap} {p} (h : MapHook.concat a R = some m)
    (h' : MapHook.concat b R = some m') (d : MapHook.Binds a [p]) {k v} {v'}
    (hv : MapHook.lookup m k = some v) (hv' : MapHook.lookup m' k = v') (hne : some v ≠ v') :
    k = p.1 :=
  one_key d (MapHook.matched_of_ne h h' (by rw [hv]; simp) (by rw [hv, hv']; exact hne))

/-- The thread maps of two equal configurations are equal. -/
theorem procs_eq {x x' : Utxo.SortProcCellMap} {y y' : Utxo.SortLedgerCell}
    {z z' : Utxo.SortGeneratedCounterCell}
    (h : Utxo.SortGeneratedTopCell.«<generatedTop>» (Utxo.SortTCell.«<T>» (Utxo.SortProcsCell.«<procs>» x) y) z =
      Utxo.SortGeneratedTopCell.«<generatedTop>» (Utxo.SortTCell.«<T>» (Utxo.SortProcsCell.«<procs>» x') y') z') :
    x = x' := by
  cases h; rfl

/-- Two values that differ: by constructors, or by a term inside itself. -/
local macro "k2l_ne" : tactic => `(tactic| first
  | (simp; done)
  | (intro h; cases h)
  | (simp; intro h; cases h)
  | (simp; intro _ h; cases h)
  | (intro h; have := congrArg sizeOf h; simp at this; omega))

set_option hygiene false in
/-- The views of two steps at one binding of a thread whose binding each step changes: both steps
are at that thread (`key_of_view`), match one value and one rest, so they are one step. -/
local macro "k2l_one_thread" hm:ident hm':ident hv:term:max hv':term:max : tactic => `(tactic| (
  obtain ⟨p₁, rfl⟩ := fits1 f₁
  obtain ⟨p₂, rfl⟩ := fits1 f₂
  obtain ⟨M, R, rr, s, e1, hA, hB, -, e2⟩ := t₁
  obtain ⟨M', R', rr', s', e1', hA', hB', -, e2'⟩ := t₂
  obtain ⟨sl, sg⟩ := s
  obtain ⟨sl', sg'⟩ := s'
  simp only [mk, mkc] at e1 e2 e1' e2'
  cases e1; cases e1'
  cases procs_eq e2; cases procs_eq e2'
  have q₁ := key_of_view hA hB d₁ (MapHook.lookup_of_concat_element $hm) $hv (by k2l_ne)
  have q₂ := key_of_view hA' hB' d₂ (MapHook.lookup_of_concat_element $hm') $hv' (by k2l_ne)
  cases q₁.trans ((one_key d₁ l₁).symm.trans ((one_key d₂ l₂).trans q₂.symm))
  cases (MapHook.lookup_of_concat_element $hm).symm.trans (MapHook.lookup_of_concat_element $hm')
  cases MapHook.concat_rest_unique $hm $hm'))

theorem sameThreadJoins : SameThreadJoins := by
  intro r₁ r₂ k₁ k₂ hr hd c c₁ c₂ a₁ b₁ ch₁ bs₁ a₂ b₂ ch₂ bs₂ k s₁ s₂ t₁ t₂ d₁ d₂ f₁ f₂ l₁ l₂
  cases r₁ <;> cases r₂ <;> (try (exfalso; revert hd; decide))
  case seq.seq =>
    apply elim_seq s₁; intro m L0 G0 kk D2 Gn I P D4 r hm hr e e'
    apply elim_seq s₂; intro m' L0' G0' kk' D2' Gn' I' P' D4' r' hm' hr' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.lookup_of_concat_element hr) (MapHook.lookup_of_concat_element hr')
    cases Option.some.inj (hr.symm.trans hr')
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case nil.nil =>
    apply elim_nil s₁; intro m L0 G0 kk D2 Gn D4 r hm hr e e'
    apply elim_nil s₂; intro m' L0' G0' kk' D2' Gn' D4' r' hm' hr' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.lookup_of_concat_element hr) (MapHook.lookup_of_concat_element hr')
    cases Option.some.inj (hr.symm.trans hr')
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case yield.yield =>
    apply elim_yield s₁; intro m L0 G0 kk D2 Gn D4 r hm hr e e'
    apply elim_yield s₂; intro m' L0' G0' kk' D2' Gn' D4' r' hm' hr' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.lookup_of_concat_element hr) (MapHook.lookup_of_concat_element hr')
    cases Option.some.inj (hr.symm.trans hr')
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case create.create =>
    apply elim_create s₁; intro m L G0 D2 P N Q V D3 r r3 hm hr hr4 e e'
    apply elim_create s₂; intro m' L' G0' D2' P' N' Q' V' D3' r' r3' hm' hr' hr4' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.lookup_of_concat_element hr) (MapHook.lookup_of_concat_element hr')
    cases Option.some.inj (hr.symm.trans hr')
    cases Option.some.inj (hr4.symm.trans hr4')
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case spend.spend =>
    apply elim_spend s₁; intro m m2 G0 D2 P D3 I D4 D5 g0 r hm hm6 hr e e'
    apply elim_spend s₂; intro m' m2' G0' D2' P' D3' I' D4' D5' g0' r' hm' hm6' hr' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.lookup_of_concat_element hr) (MapHook.lookup_of_concat_element hr')
    cases (MapHook.lookup_of_concat_element hm6).symm.trans (MapHook.lookup_of_concat_element hm6')
    cases MapHook.concat_rest_unique hm6 hm6'
    cases Option.some.inj (hr.symm.trans hr')
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case spawn.spawn =>
    apply elim_spawn s₁; intro m L0 G0 D2 P N Gp D3 r r3 hm hr hr4 e e'
    apply elim_spawn s₂; intro m' L0' G0' D2' P' N' Gp' D3' r' r3' hm' hr' hr4' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.lookup_of_concat hr4 (MapHook.lookup_of_concat_element hr)) (MapHook.lookup_of_concat hr4' (MapHook.lookup_of_concat_element hr'))
    cases Option.some.inj (hr.symm.trans hr')
    cases Option.some.inj (hr4.symm.trans hr4')
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case done.done =>
    apply elim_done s₁; intro m L0 G0 D2 g0 D3 hm e e'
    apply elim_done s₂; intro m' L0' G0' D2' g0' D3' hm' f f'
    subst e e'; cases f; subst f'
    k2l_one_thread hm hm' (MapHook.concat_element_iff.1 hm).2.1 (MapHook.concat_element_iff.1 hm').2.1
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  case resume.resume =>
    apply elim_resume s₁; intro m L0 G0 rest P D3 M D4 D2 D5 D6 r r13 hm hm7 hr hr14 e e'
    apply elim_resume s₂; intro m' L0' G0' rest' P' D3' M' D4' D2' D5' D6' r' r13' hm' hm7' hr' hr14' f f'
    subst e e'; cases f; subst f'
    obtain ⟨p₁, q₁, rfl⟩ := fits2 f₁
    obtain ⟨p₂, q₂, rfl⟩ := fits2 f₂
    obtain ⟨M₀, R, rr, s, e1, hA, hB, -, e2⟩ := t₁
    obtain ⟨M₀', R', rr', s', e1', hA', hB', -, e2'⟩ := t₂
    obtain ⟨sl, sg⟩ := s
    obtain ⟨sl', sg'⟩ := s'
    simp only [mk, mkc] at e1 e2 e1' e2'
    cases e1; cases e1'
    cases procs_eq e2; cases procs_eq e2'
    -- each step changes its process and its child, the two keys its view matches
    have hP := MapHook.lookup_of_concat_element hm
    have hC := (MapHook.lookup_concat_right hm (MapHook.lookup_left_none_of_concat hm
      (by rw [MapHook.lookup_of_concat_element hm7]; simp))).trans (MapHook.lookup_of_concat_element hm7)
    have hP' := MapHook.lookup_of_concat_element hm'
    have hC' := (MapHook.lookup_concat_right hm' (MapHook.lookup_left_none_of_concat hm'
      (by rw [MapHook.lookup_of_concat_element hm7']; simp))).trans (MapHook.lookup_of_concat_element hm7')
    have aP := MapHook.matched_of_ne hA hB (by rw [hP]; simp)
      (by rw [hP, MapHook.lookup_of_concat hr14 (MapHook.lookup_of_concat_element hr)]; k2l_ne)
    have aC := MapHook.matched_of_ne hA hB (by rw [hC]; simp)
      (by rw [hC, MapHook.lookup_of_concat hr14 (((MapHook.binds_pair hr) _ _).2 (List.mem_cons_of_mem _ List.mem_cons_self))]; k2l_ne)
    have aP' := MapHook.matched_of_ne hA' hB' (by rw [hP']; simp)
      (by rw [hP', MapHook.lookup_of_concat hr14' (MapHook.lookup_of_concat_element hr')]; k2l_ne)
    have aC' := MapHook.matched_of_ne hA' hB' (by rw [hC']; simp)
      (by rw [hC', MapHook.lookup_of_concat hr14' (((MapHook.binds_pair hr') _ _).2 (List.mem_cons_of_mem _ List.mem_cons_self))]; k2l_ne)
    have k₁ := pair_keys d₁ aP aC (by k2l_ne) l₁
    have k₂ := pair_keys d₂ aP' aC' (by k2l_ne) l₂
    -- one process: the same parent, or the same child, whose parent is its key's; a process
    -- that resumes is not a suspended one
    rcases k₁ with rfl | rfl <;> rcases k₂ with e | e <;> cases e
    all_goals first
      | (cases hP.symm.trans hC'; done)
      | (cases hC.symm.trans hP'; done)
      | skip
    all_goals
      cases hP.symm.trans hP'
      cases MapHook.concat_rest_unique hm hm'
      cases (MapHook.lookup_of_concat_element hm7).symm.trans (MapHook.lookup_of_concat_element hm7')
      cases MapHook.concat_rest_unique hm7 hm7'
      cases Option.some.inj (hr.symm.trans hr')
      cases Option.some.inj (hr14.symm.trans hr14')
      exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩

/-- What a step does to the ledger, read off a view's change (`ChOf`): the change applies at the
ledger before and gives the ledger after. -/
theorem ledger_step {ch : Change} {c c₁ : Utxo.SortGeneratedTopCell}
    (o : (∃ a b, MStep a b ch c c₁) ∨ SStep ch c c₁) {p p' : Utxo.SortProcsCell} {L L' : Utxo.SortMap}
    {g g' : Utxo.SortGeneratedCounterCell}
    (e : c = Utxo.SortGeneratedTopCell.«<generatedTop>» (Utxo.SortTCell.«<T>» p (Utxo.SortLedgerCell.«<ledger>» L)) g)
    (e' : c₁ = Utxo.SortGeneratedTopCell.«<generatedTop>» (Utxo.SortTCell.«<T>» p' (Utxo.SortLedgerCell.«<ledger>» L')) g') :
    ch.ledger.pre L ∧ ch.ledger.apply L = L' := by
  subst e e'
  rcases o with ⟨a, b, m, R, r, ⟨sl, sg⟩, e1, -, -, hp, e2⟩ | ⟨tc, ⟨sl, sg⟩, e1, hp, e2⟩
  all_goals
    simp only [mk, mkc] at e1 e2
    cases e1
    refine ⟨hp.1, ?_⟩
    cases e2
    rfl

/-- The pairs whose changes of the ledger do not commute: two creates of one output, or two spends
of one output, are steps of one process, so they are one step. -/
theorem keyJoins : KeyJoins := by
  intro r₁ r₂ hr c c₁ c₂ ch₁ ch₂ s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Change.KCompat] at hk
  cases r₁ <;> cases r₂ <;> simp only [Rule.cls, InClass] at i₁ i₂
  all_goals first
    | exact (hk (Or.inl i₁.1)).elim
    | exact (hk (Or.inr (Or.inl i₂.1))).elim
    | skip
  case create.create =>
    apply elim_create s₁; intro m L G0 D2 P N Q V D3 r r3 hm hr hr4 e e'
    apply elim_create s₂; intro m' L' G0' D2' P' N' Q' V' D3' r' r3' hm' hr' hr4' f f'
    subst e e'; cases f; subst f'
    obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
    obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
    rw [MCh.insert_of p₁ a₁ k₁ hr4, MCh.insert_of p₂ a₂ k₂ hr4'] at hk
    by_cases eo : Utxo.SortKItem.inj_Oid (Utxo.SortOid.«oid(_,_)» P N) =
        Utxo.SortKItem.inj_Oid (Utxo.SortOid.«oid(_,_)» P' N')
    · cases eo
      cases (MapHook.lookup_of_concat_element hm).symm.trans (MapHook.lookup_of_concat_element hm')
      cases MapHook.concat_rest_unique hm hm'
      cases Option.some.inj (hr.symm.trans hr')
      cases Option.some.inj (hr4.symm.trans hr4')
      exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
    · refine (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
        Or.inl ⟨fun _ => Or.inl MapHook.lookup_unit, fun j => ?_⟩⟩))).elim
      by_cases ej : j = Utxo.SortKItem.inj_Oid (Utxo.SortOid.«oid(_,_)» P N)
      · subst ej; exact Or.inr (MapHook.lookup_element_ne eo)
      · exact Or.inl (MapHook.lookup_element_ne ej)
  case spend.spend =>
    apply elim_spend s₁; intro m m2 G0 D2 P D3 I D4 D5 g0 r hm hm6 hr e e'
    apply elim_spend s₂; intro m' m2' G0' D2' P' D3' I' D4' D5' g0' r' hm' hm6' hr' f f'
    subst e e'; cases f; subst f'
    obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
    obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
    rw [MCh.remove_of p₁ a₁ k₁ hm6, MCh.remove_of p₂ a₂ k₂ hm6'] at hk
    by_cases eo : Utxo.SortKItem.inj_Oid I = Utxo.SortKItem.inj_Oid I'
    · cases eo
      cases (MapHook.lookup_of_concat_element hm6).symm.trans (MapHook.lookup_of_concat_element hm6')
      cases MapHook.concat_rest_unique hm6 hm6'
      cases (MapHook.lookup_of_concat_element hm).symm.trans (MapHook.lookup_of_concat_element hm')
      cases MapHook.concat_rest_unique hm hm'
      cases Option.some.inj (hr.symm.trans hr')
      exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
    · refine (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
        Or.inl ⟨fun j => ?_, fun _ => Or.inl MapHook.lookup_unit⟩⟩))).elim
      by_cases ej : j = Utxo.SortKItem.inj_Oid I
      · subst ej; exact Or.inr (MapHook.lookup_element_ne eo)
      · exact Or.inl (MapHook.lookup_element_ne ej)
  case create.spend =>
    apply elim_create s₁; intro m L G0 D2 P N Q V D3 r r3 hm hr hr4 e e'
    apply elim_spend s₂; intro m' m2' G0' D2' P' D3' I' D4' D5' g0' r' hm' hm6' hr' f f'
    subst e e'; cases f; subst f'
    obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
    obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
    rw [MCh.insert_of p₁ a₁ k₁ hr4, MCh.remove_of p₂ a₂ k₂ hm6'] at hk
    exact (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
      Or.inl ⟨fun _ => Or.inl MapHook.lookup_unit, fun _ => Or.inr MapHook.lookup_unit⟩⟩))).elim
  case spend.create =>
    apply elim_spend s₁; intro m m2 G0 D2 P D3 I D4 D5 g0 r hm hm6 hr e e'
    apply elim_create s₂; intro m' L' G0' D2' P' N' Q' V' D3' r' r3' hm' hr' hr4' f f'
    subst e e'; cases f; subst f'
    obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
    obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
    rw [MCh.remove_of p₁ a₁ k₁ hm6, MCh.insert_of p₂ a₂ k₂ hr4'] at hk
    exact (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
      Or.inl ⟨fun _ => Or.inr MapHook.lookup_unit, fun _ => Or.inl MapHook.lookup_unit⟩⟩))).elim

/-- A key bound by what `concat` puts beside the rest is not the rest's. -/
theorem right_none {b R m : Utxo.SortProcCellMap} (h : MapHook.concat b R = some m) {k}
    (hb : MapHook.lookup b k ≠ none) : MapHook.lookup R k = none := by
  cases e : MapHook.lookup R k with
  | none => rfl
  | some w => exact absurd (MapHook.lookup_left_none_of_concat h (by rw [e]; simp)) hb

/-- The keys of a map of two bindings. -/
theorem pair_key {r : Utxo.SortProcCellMap} {x y v w k}
    (h : MapHook.concat (MapHook.element x v) (MapHook.element y w) = some r)
    (hk : MapHook.lookup r k ≠ none) : k = x ∨ k = y := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hk
  have := ((MapHook.binds_pair h) k u).1 hu
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
  rcases this with ⟨e, -⟩ | ⟨e, -⟩
  · exact Or.inl e
  · exact Or.inr e

/-- The pairs the generic arguments leave: two spawns, of one process (one step) or of two, whose
children are new keys, different since a child's id names its parent, so they commute. -/
theorem openJoins : OpenJoins := by
  intro r₁ r₂ hs c c₁ c₂ s₁ s₂
  cases r₁ <;> cases r₂ <;> (try (exfalso; revert hs; decide))
  case spawn.spawn =>
    apply elim_spawn s₁; intro m L0 G0 D2 P N Gp D3 r r3 hm hr hr4 e e'
    apply elim_spawn s₂; intro m' L0' G0' D2' P' N' Gp' D3' r' r3' hm' hr' hr4' f f'
    subst e e'; cases f; subst f'
    by_cases eP : Utxo.SortPidCell.«<pid>» P = Utxo.SortPidCell.«<pid>» P'
    · cases eP
      cases (MapHook.lookup_of_concat_element hm).symm.trans (MapHook.lookup_of_concat_element hm')
      cases MapHook.concat_rest_unique hm hm'
      cases Option.some.inj (hr.symm.trans hr')
      cases Option.some.inj (hr4.symm.trans hr4')
      exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
    · -- each parent is a key of the map, each child is not
      have old₁ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» P) ≠ none := by
        rw [MapHook.lookup_of_concat_element hm]; simp
      have old₂ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» P') ≠ none := by
        rw [MapHook.lookup_of_concat_element hm']; simp
      have new₁ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» (Utxo.SortPid.«child(_,_)» P N)) = none := by
        rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne (by k2l_ne))]
        exact right_none hr4 (by
          rw [((MapHook.binds_pair hr) _ _).2 (List.mem_cons_of_mem _ List.mem_cons_self)]; simp)
      have new₂ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» (Utxo.SortPid.«child(_,_)» P' N')) = none := by
        rw [MapHook.lookup_concat_right hm' (MapHook.lookup_element_ne (by k2l_ne))]
        exact right_none hr4' (by
          rw [((MapHook.binds_pair hr') _ _).2 (List.mem_cons_of_mem _ List.mem_cons_self)]; simp)
      obtain ⟨R₁₂, R₂₁, m₀, e₁, e₂, e₃, e₄⟩ := MapHook.concat_frame_b hm hr4 hm' hr4'
        (fun k => by
          by_cases ek : k = Utxo.SortPidCell.«<pid>» P
          · subst ek; exact Or.inr (MapHook.lookup_element_ne eP)
          · exact Or.inl (MapHook.lookup_element_ne ek))
        (fun k => by
          by_cases h₁ : MapHook.lookup r k = none
          · exact Or.inl h₁
          refine Or.inr (Classical.byContradiction fun h₂ => ?_)
          rcases pair_key hr h₁ with rfl | rfl <;> rcases pair_key hr' h₂ with e | e
          · exact eP e
          · rw [e] at old₁; exact old₁ new₂
          · rw [e] at new₁; exact old₂ new₁
          · cases e; exact eP rfl)
      exact ⟨_, _, Or.inr (Utxo.Step.spawn _ _ _ _ _ _ _ _ _ _ e₁ hr' e₂),
        Or.inr (Utxo.Step.spawn _ _ _ _ _ _ _ _ _ _ e₃ hr e₄), rfl⟩

/-- The fixture `utxo` is confluent: two runs from one configuration that both end, end in one
configuration, with no premise left. -/
theorem terminal_unique {c n₁ n₂ : Utxo.SortGeneratedTopCell} (h₁ : Star Utxo.Step c n₁)
    (t₁ : Terminal Utxo.Step n₁) (h₂ : Star Utxo.Step c n₂) (t₂ : Terminal Utxo.Step n₂) : n₁ = n₂ :=
  terminal_unique_of openJoins sameThreadJoins keyJoins h₁ t₁ h₂ t₂

#k2l_assert_axioms sameThreadJoins keyJoins openJoins terminal_unique

end UtxoConf
