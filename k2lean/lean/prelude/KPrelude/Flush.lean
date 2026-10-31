import KPrelude.Scaffold
import KPrelude.Determinism

/-!
# Confluence up to the flush of the higher ranks

A definition whose rules have priorities can have rules of a high rank that a rule of the
language enables: K's stream rules (priority 25) run after every `print` that puts an item on
`<output>` (the language's rules have the default priority, 50), and the language's rules do not
apply until they are done. A step of the language and a step of another thread then do not join in
one step each: the second thread cannot step until the first one's output is flushed.

The steps of such a definition are compressed here. `N c` says that no rule of a high rank applies
at `c`. A step from a configuration where one does is a step of the flush (`FlushStep`); the flush
is deterministic (`hdet`) and stops (`FlushNF`) where `N` holds or nothing steps (`Settled`). A
compressed step (`FStep`) is a step from a configuration where `N` holds, then the flush to where it
stops.

- `decomp`: a run that ends is a flush to where it stops, then compressed steps.
- `unique_of_flush`: if two compressed steps from one configuration join in at most one compressed
  step each, modulo `E`, the terminal configurations of two runs from any configuration are related
  by `E`. No termination is assumed.
- `fdiamond_of_diamond`: a join of two steps in at most one step each is one of the compressed steps,
  when every flush stops (`hend`).
- `ObsEq`: equal, or both terminal with one observation, a `StepEquiv` of the compressed steps. Two
  runs whose flush stops where nothing steps (an undefined I/O hook) end apart, with one observation.
- `flushNF_frame`, `fdiamond_of_frame`: a step `M` that the flush commutes with in both directions
  (another thread's step, which leaves the flushed cells alone) carries where the flush stops; so a
  step that enables the flush and such a step join, compressed.
- `flush_ends`: every flush stops when a measure decreases along it.
- `k2l_list_det`: two matches of one list at its first element agree (the flush's determinism).

`k2lean confluence --threads` states a definition's theorem this way when a rule of some rank `R`
may enable the rules of the ranks before `R`, and those step the shared cells alone (design.md
§3.6, "Priorities and the flush").
-/

set_option autoImplicit false

namespace KPrelude

universe u v

section Flush

variable {α : Type u} {β : Type v} {S : α → α → Prop} {N : α → Prop}

/-- A step from a configuration where a rule of a high rank applies. -/
def FlushStep (S : α → α → Prop) (N : α → Prop) (c c' : α) : Prop := ¬ N c ∧ S c c'

/-- No rule of a high rank applies, or nothing steps. -/
def Settled (S : α → α → Prop) (N : α → Prop) (c : α) : Prop := N c ∨ Terminal S c

/-- The flush from `c` stops at `n`. -/
def FlushNF (S : α → α → Prop) (N : α → Prop) (c n : α) : Prop :=
  Star (FlushStep S N) c n ∧ Settled S N n

/-- A compressed step: a step from a configuration where no rule of a high rank applies, then the
flush to where it stops. -/
def FStep (S : α → α → Prop) (N : α → Prop) (c c' : α) : Prop :=
  N c ∧ ∃ x, S c x ∧ FlushNF S N x c'

theorem not_settled_of_flush {c c' : α} (h : FlushStep S N c c') : ¬ Settled S N c :=
  fun hs => hs.elim h.1 (fun ht => ht _ h.2)

theorem flushNF_self {c : α} (h : Settled S N c) : FlushNF S N c c := ⟨.refl _, h⟩

theorem FlushNF.of_flush {c c' n : α} (h : FlushStep S N c c') (hn : FlushNF S N c' n) :
    FlushNF S N c n :=
  ⟨.step h hn.1, hn.2⟩

/-- Where the flush stops is unique, as the flush is deterministic. -/
theorem FlushNF.unique (hdet : ∀ {c a b : α}, ¬ N c → S c a → S c b → a = b) :
    ∀ {c n₁ n₂ : α}, FlushNF S N c n₁ → FlushNF S N c n₂ → n₁ = n₂ := by
  intro c n₁ n₂ ⟨h₁, s₁⟩ ⟨h₂, s₂⟩
  induction h₁ generalizing n₂ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step f _ => exact absurd s₁ (not_settled_of_flush f)
  | step f rest ih =>
    cases h₂ with
    | refl => exact absurd s₂ (not_settled_of_flush f)
    | step f' rest' =>
      have e := hdet f.1 f.2 f'.2
      subst e
      exact ih s₁ rest' s₂

theorem FlushNF.eq_self (hdet : ∀ {c a b : α}, ¬ N c → S c a → S c b → a = b) {c n : α}
    (hc : N c) (h : FlushNF S N c n) : n = c :=
  h.unique hdet (flushNF_self (.inl hc))

theorem Terminal.fstep {c : α} (h : Terminal S c) : Terminal (FStep S N) c :=
  fun _ ⟨_, _, hs, _⟩ => h _ hs

theorem FStep.settled : Preserved (FStep S N) (Settled S N) :=
  fun _ _ _ ⟨_, _, _, hf⟩ => hf.2

/-- A run that ends is the flush to where it stops, then compressed steps. -/
theorem decomp {c n : α} (h : Star S c n) (ht : Terminal S n) :
    ∃ y, FlushNF S N c y ∧ Star (FStep S N) y n := by
  induction h with
  | refl => exact ⟨_, flushNF_self (.inr ht), .refl _⟩
  | @step c c' _ hs _ ih =>
    obtain ⟨y, hy, hr⟩ := ih ht
    by_cases hc : N c
    · exact ⟨c, flushNF_self (.inl hc), .step ⟨hc, c', hs, hy⟩ hr⟩
    · exact ⟨y, hy.of_flush ⟨hc, hs⟩, hr⟩

/-- Confluence up to the flush: if two compressed steps from one configuration join modulo `E` in at
most one compressed step each, two runs that end from one configuration end related by `E`. -/
theorem unique_of_flush {E : α → α → Prop} (hE : StepEquiv (FStep S N) E)
    (hdet : ∀ {c a b : α}, ¬ N c → S c a → S c b → a = b)
    (hd : ∀ {c c₁ c₂ n₁ n₂ : α}, N c → S c c₁ → S c c₂ → FlushNF S N c₁ n₁ → FlushNF S N c₂ n₂ →
      DiamondMod (FStep S N) E n₁ n₂) :
    ∀ {c n₁ n₂ : α}, Star S c n₁ → Terminal S n₁ → Star S c n₂ → Terminal S n₂ → E n₁ n₂ := by
  intro c n₁ n₂ h₁ t₁ h₂ t₂
  obtain ⟨y₁, f₁, r₁⟩ := decomp (N := N) h₁ t₁
  obtain ⟨y₂, f₂, r₂⟩ := decomp (N := N) h₂ t₂
  have e := f₁.unique hdet f₂
  subst e
  exact terminal_unique_of_diamond hE FStep.settled
    (fun _ ⟨hc, _, s₁, g₁⟩ ⟨_, _, s₂, g₂⟩ => hd hc s₁ s₂ g₁ g₂) f₁.2 r₁ t₁.fstep r₂ t₂.fstep

/-- One step, or none, then the flush, is at most one compressed step from where the flush stops. -/
theorem opt_fstep (hdet : ∀ {c a b : α}, ¬ N c → S c a → S c b → a = b) {x d n e : α}
    (o : Opt S x d) (fx : FlushNF S N x n) (fd : FlushNF S N d e) : Opt (FStep S N) n e := by
  rcases o with rfl | hs
  · exact .inl (fd.unique hdet fx)
  · by_cases hx : N x
    · have e := FlushNF.eq_self (S := S) (N := N) hdet hx fx
      subst e
      exact .inr ⟨hx, d, hs, fd⟩
    · exact .inl ((fd.of_flush ⟨hx, hs⟩).unique hdet fx)

/-- A join in at most one step each is a join in at most one compressed step each, when every flush
stops. -/
theorem fdiamond_of_diamond {E : α → α → Prop} (hE : StepEquiv (FStep S N) E)
    (hdet : ∀ {c a b : α}, ¬ N c → S c a → S c b → a = b) (hend : ∀ c, ∃ n, FlushNF S N c n)
    {c₁ c₂ n₁ n₂ : α} (f₁ : FlushNF S N c₁ n₁) (f₂ : FlushNF S N c₂ n₂)
    (h : DiamondMod S Eq c₁ c₂) : DiamondMod (FStep S N) E n₁ n₂ := by
  obtain ⟨d, _, o₁, o₂, rfl⟩ := h
  obtain ⟨e, fe⟩ := hend d
  exact ⟨e, e, opt_fstep hdet o₁ f₁ fe, opt_fstep hdet o₂ f₂ fe, hE.refl _⟩

/-- Every flush stops when a measure decreases along it. -/
theorem flush_ends (μ : α → Nat) (hμ : ∀ {c c'}, FlushStep S N c c' → μ c' < μ c) :
    ∀ c, ∃ n, FlushNF S N c n := by
  intro c
  induction c using measure_ind μ with
  | h c ih =>
    by_cases hs : Settled S N c
    · exact ⟨c, flushNF_self hs⟩
    · have hn : ¬ N c := fun h => hs (.inl h)
      have : ¬ Terminal S c := fun h => hs (.inr h)
      simp only [Terminal, Classical.not_forall, Classical.not_not] at this
      obtain ⟨c', hc'⟩ := this
      obtain ⟨n, hn'⟩ := ih c' (hμ ⟨hn, hc'⟩)
      exact ⟨n, hn'.of_flush ⟨hn, hc'⟩⟩

theorem DiamondMod.symm {E : α → α → Prop} (hE : StepEquiv (FStep S N) E) {a b : α}
    (h : DiamondMod (FStep S N) E a b) : DiamondMod (FStep S N) E b a :=
  let ⟨a', b', o₁, o₂, e⟩ := h
  ⟨b', a', o₂, o₁, hE.symm e⟩

/-- Equal, or both terminal with one observation. -/
def ObsEq (S : α → α → Prop) (obs : α → β) (a b : α) : Prop :=
  a = b ∨ (Terminal S a ∧ Terminal S b ∧ obs a = obs b)

theorem ObsEq.obs {obs : α → β} {a b : α} (h : ObsEq S obs a b) : obs a = obs b :=
  h.elim (congrArg obs) (fun h => h.2.2)

/-- `ObsEq` relates states with related successors: terminal states have none. -/
theorem ObsEq.stepEquiv (obs : α → β) : StepEquiv (FStep S N) (ObsEq S obs) where
  refl _ := .inl rfl
  symm h := h.elim (fun h => .inl h.symm) (fun ⟨a, b, o⟩ => .inr ⟨b, a, o.symm⟩)
  trans h₁ h₂ := by
    rcases h₁ with rfl | ⟨a, b, o⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨_, c, o'⟩
      · exact .inr ⟨a, b, o⟩
      · exact .inr ⟨a, c, o.trans o'⟩
  sim h hs := by
    rcases h with rfl | ⟨a, _, _⟩
    · exact ⟨_, hs, .inl rfl⟩
    · exact absurd hs (Terminal.fstep a _)

/-- A step `M` that the flush commutes with in both directions carries where the flush stops. -/
theorem flushNF_frame {M : α → α → Prop}
    (fw : ∀ {y z y'}, FlushStep S N y z → M y y' → ∃ z', FlushStep S N y' z' ∧ M z z')
    (bw : ∀ {y y' z'}, FlushStep S N y' z' → M y y' → ∃ z, FlushStep S N y z ∧ M z z') :
    ∀ {y n y'}, FlushNF S N y n → M y y' → ∃ n', FlushNF S N y' n' ∧ M n n' := by
  intro y n y' ⟨h, hs⟩ hm
  induction h generalizing y' with
  | @refl y =>
    refine ⟨y', flushNF_self ?_, hm⟩
    by_cases hy : N y'
    · exact .inl hy
    · refine .inr fun z' hz' => ?_
      obtain ⟨z, hz, _⟩ := bw ⟨hy, hz'⟩ hm
      exact not_settled_of_flush hz hs
  | step f _ ih =>
    obtain ⟨z', f', hz'⟩ := fw f hm
    obtain ⟨n', hn', hm'⟩ := ih hs hz'
    exact ⟨n', hn'.of_flush f', hm'⟩

/-- A step to `a` that may enable the flush, and a step `M` to `b` that the flush commutes with,
leaves the observation alone, and is a step wherever no rule of a high rank applies, join
compressed modulo `ObsEq`, given that after the step `M` the first step is a step (`hab`). -/
theorem fdiamond_of_frame {obs : α → β} {M : α → α → Prop}
    (hdet : ∀ {c a b : α}, ¬ N c → S c a → S c b → a = b)
    (fw : ∀ {y z y'}, FlushStep S N y z → M y y' → ∃ z', FlushStep S N y' z' ∧ M z z')
    (bw : ∀ {y y' z'}, FlushStep S N y' z' → M y y' → ∃ z, FlushStep S N y z ∧ M z z')
    (hN : ∀ {y y'}, M y y' → (N y ↔ N y'))
    (hobs : ∀ {y y'}, M y y' → obs y = obs y')
    (hS : ∀ {y y'}, N y → M y y' → S y y')
    {c a b c₁₂ n₁ n₂ : α} (hc : N c) (hb : M c b) (ha₁₂ : M a c₁₂) (hab : S b c₁₂)
    (f₁ : FlushNF S N a n₁) (f₂ : FlushNF S N b n₂) :
    DiamondMod (FStep S N) (ObsEq S obs) n₁ n₂ := by
  have nb : N b := (hN hb).1 hc
  have e := FlushNF.eq_self (S := S) (N := N) hdet nb f₂
  subst e
  obtain ⟨n', f', hm⟩ := flushNF_frame fw bw f₁ ha₁₂
  have t : FStep S N n₂ n' := ⟨nb, c₁₂, hab, f'⟩
  by_cases hn : N n₁
  · have nn' : N n' := (hN hm).1 hn
    exact ⟨n', n', .inr ⟨hn, n', hS hn hm, flushNF_self (.inl nn')⟩, .inr t, .inl rfl⟩
  · have tn : Terminal S n₁ := f₁.2.resolve_left hn
    have tn' : Terminal S n' := f'.2.resolve_left fun h => hn ((hN hm).2 h)
    exact ⟨n₁, n', .inl rfl, .inr t, .inr ⟨tn, tn', hobs hm⟩⟩

end Flush

/-- A change that applies after another it is compatible with applied before it. -/
theorem Ch.pre_unapply {α : Type} {a b : Ch α} {x : α} (h : Ch.Compat a b) (ha : a.pre x)
    (hb : b.pre (a.apply x)) : b.pre x := by
  rcases h with rfl | rfl | ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  · exact hb
  · exact Ch.pre_none
  · have := ha (u, u) rfl
    subst this
    exact hb

end KPrelude

namespace KPrelude.ListHook

open Lean Meta Elab Tactic

private def isSplit (l : Expr) : Bool :=
  l.isAppOfArity ``ListHook.concat 5 && (l.getArg! 3).isAppOfArity ``ListHook.element 4

/-- A proof of `x = x' ∧ t = t'` from a hypothesis `concat (element x) t = concat (element x') t'`,
or from two `concat (element x) t = l` and `concat (element x') t' = l`, and the hypothesis it
makes redundant. -/
private def splitPair? : MetaM (Option (Expr × Expr)) := do
  let mut seen : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
    unless isSplit l do continue
    if isSplit r then
      return some (← mkAppM ``ListHook.concat_element_inj #[d.toExpr], d.toExpr)
    for (h, r') in seen do
      if ← withReducible (isDefEq r r') then
        return some (← mkAppM ``ListHook.concat_element_inj #[← mkEqTrans h (← mkEqSymm d.toExpr)],
          d.toExpr)
    seen := seen.push (d.toExpr, r)
  return none

/-- `k2l_list_det`: two matches of one list at its first element (`concat (element x) t = l` twice,
or `concat (element x) t = concat (element x') t'`) give `x = x'` and `t = t'`
(`concat_element_inj`), each unified by `cases` (a clash of constructors closes the goal). -/
elab "k2l_list_det" : tactic => do
  for _ in [0:256] do
    let g ← getMainGoal
    let some gs ← g.withContext do
        let some (pf, used) ← splitPair? | return none
        let (h, g) ← (← (← g.clear used.fvarId!).assert `k2l_e (← inferType pf) pf).intro1P
        let #[sg] ← g.cases h | return none
        let #[e₁, e₂] := sg.fields | return none
        let mut out := #[]
        let firsts : Array (MVarId × Expr) ← (do
            let ss ← sg.mvarId.cases e₁.fvarId!
            pure (ss.map fun s => (s.mvarId, s.subst.get e₂.fvarId!))) <|> pure #[(sg.mvarId, e₂)]
        for (g₁, e₂') in firsts do
          try out := out ++ (← g₁.cases e₂'.fvarId!).map (·.mvarId)
          catch _ => out := out.push g₁
        return some out
      | return
    replaceMainGoal gs.toList
    if gs.isEmpty then return

end KPrelude.ListHook
