/-!
# Pending calls: divergence of a least fixed point (TERM-1)

A least fixed point (`partial_fixpoint`) is `none` where some model of K's equations has `⊥`:
where the evaluation is undefined (no equation applies, or a right-hand side is `⊥`), and where
it diverges. Which one is a property of the order of the evaluation's binds, not of the
function: a divergent group and an undefined one can have the same least fixed point. The
generator therefore states divergence over the group's pending-call function `p : Call → Option
Call` (`F.pending`): the group's cascade, read so that a call of the group whose value is `none`
is where the evaluation waits (`pendCall`), and `none` where it ends without one.

* `Chain p a`: the pending calls from `a` go on forever; the obligation `F.diverges.statement` is
  `∃ c, Chain F.pending c`, which no termination measure of the group survives.
* `Ends p a`: they stop; with `F.pending_sound`, `none` there is undefinedness.
* `not_ends_and_chain`, `ends_or_chain`: never both, always one. -/

namespace KPrelude

/-- A call of the group in a right-hand side's binds, in the pending-call function: a value
continues the evaluation; `none` makes `c` the call the evaluation waits for. -/
@[inline] def pendCall {α γ : Type} (o : Option α) (c : γ) (k : α → Option γ) : Option γ :=
  match o with
  | some v => k v
  | none => some c

@[simp] theorem pendCall_some {α γ : Type} (v : α) (c : γ) (k : α → Option γ) :
    pendCall (some v) c k = k v := rfl

@[simp] theorem pendCall_none {α γ : Type} (c : γ) (k : α → Option γ) :
    pendCall none c k = some c := rfl

theorem pendCall_eq_some {α γ : Type} (o : Option α) (c c' : γ) (k : α → Option γ) :
    pendCall o c k = some c' ↔ (o = none ∧ c = c') ∨ ∃ v, o = some v ∧ k v = some c' := by
  cases o <;> simp [pendCall, eq_comm]

namespace Pending

/-- The pending calls from `a` stop: the last one's evaluation ends without a pending call. -/
inductive Ends {α : Type} (p : α → Option α) : α → Prop where
  | stop {a} : p a = none → Ends p a
  | next {a b} : p a = some b → Ends p b → Ends p a

/-- The pending calls from `a` go on forever. -/
def Chain {α : Type} (p : α → Option α) (a : α) : Prop :=
  ∃ s : Nat → α, s 0 = a ∧ ∀ n, p (s n) = some (s (n + 1))

/-- A call that is its own pending call. -/
theorem chain_of_fixed {α : Type} (p : α → Option α) (c : α) (h : p c = some c) : Chain p c :=
  ⟨fun _ => c, rfl, fun _ => h⟩

/-- A cycle of pending calls, `l[i]` waiting for `l[i+1]` and the last for the first. -/
theorem chain_of_cycle {α : Type} (p : α → Option α) (l : List α) (hl : 0 < l.length)
    (h : ∀ i (hi : i < l.length),
      p (l.get ⟨i, hi⟩) = some (l.get ⟨(i + 1) % l.length, Nat.mod_lt _ hl⟩)) :
    Chain p (l.get ⟨0, hl⟩) := by
  refine ⟨fun n => l.get ⟨n % l.length, Nat.mod_lt _ hl⟩, by simp [Nat.zero_mod], fun n => ?_⟩
  have e : (n + 1) % l.length = (n % l.length + 1) % l.length := by simp [Nat.add_mod]
  simp only [e]
  exact h _ (Nat.mod_lt _ hl)

/-- Never both. -/
theorem not_ends_and_chain {α : Type} (p : α → Option α) (a : α) : Ends p a → ¬ Chain p a := by
  intro h
  induction h with
  | stop hp =>
    rintro ⟨s, h0, hs⟩
    have := hs 0; rw [h0, hp] at this; cases this
  | @next a b hab _ ih =>
    rintro ⟨s, h0, hs⟩
    have h1 : s 1 = b := by
      have := hs 0; rw [h0, hab] at this; exact (Option.some.inj this).symm
    exact ih ⟨fun n => s (n + 1), h1, fun n => hs (n + 1)⟩

/-- Always one (classical: the chain is chosen through the calls that do not end). -/
theorem ends_or_chain {α : Type} (p : α → Option α) (a : α) : Ends p a ∨ Chain p a := by
  classical
  by_cases h : Ends p a
  · exact Or.inl h
  · right
    have step : ∀ x, ¬ Ends p x → ∃ y, p x = some y ∧ ¬ Ends p y := by
      intro x hx
      cases hpx : p x with
      | none => exact absurd (Ends.stop hpx) hx
      | some y => exact ⟨y, rfl, fun hy => hx (Ends.next hpx hy)⟩
    let T := {x // ¬ Ends p x}
    let nx : T → T := fun x => ⟨(step x.1 x.2).choose, (step x.1 x.2).choose_spec.2⟩
    let s : Nat → T := fun n => Nat.rec (motive := fun _ => T) ⟨a, h⟩ (fun _ x => nx x) n
    refine ⟨fun n => (s n).1, rfl, fun n => ?_⟩
    exact (step (s n).1 (s n).2).choose_spec.1

end Pending

end KPrelude
