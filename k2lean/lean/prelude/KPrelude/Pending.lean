import KPrelude.Paths

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
* `not_ends_and_chain`, `ends_or_chain`: never both, always one.

`Chain p` is `Paths.Inf` of `p`'s graph, and `Ends p` is `Paths.Terminates` of it
(`ends_iff_terminates`). -/

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

/-- The pending calls from `a` go on forever: an infinite path of `p`'s graph,
`∃ s : Nat → α, s 0 = a ∧ ∀ n, p (s n) = some (s (n + 1))`. -/
def Chain {α : Type} (p : α → Option α) (a : α) : Prop :=
  Paths.Inf (fun x y => p x = some y) a

/-- `Ends` is termination of `p`'s graph. -/
theorem ends_iff_terminates {α : Type} (p : α → Option α) (a : α) :
    Ends p a ↔ Paths.Terminates (fun x y => p x = some y) a := by
  constructor
  · intro h
    induction h with
    | stop hp => exact Acc.intro _ fun y (hy : p _ = some y) => by rw [hp] at hy; cases hy
    | @next a b hab _ ih =>
      exact Acc.intro _ fun y (hy : p _ = some y) => by rw [hab] at hy; cases hy; exact ih
  · intro h
    induction h with
    | intro x _ ih =>
      cases hp : p x with
      | none => exact Ends.stop hp
      | some y => exact Ends.next hp (ih y hp)

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
theorem not_ends_and_chain {α : Type} (p : α → Option α) (a : α) : Ends p a → ¬ Chain p a :=
  fun h => ((ends_iff_terminates p a).1 h).not_inf

/-- Always one (classical: the chain is chosen through the calls that do not end). -/
theorem ends_or_chain {α : Type} (p : α → Option α) (a : α) : Ends p a ∨ Chain p a :=
  (Paths.terminates_or_inf a).imp_left (ends_iff_terminates p a).2

/-- `p` is sound for `undef` (a group's `F.pending_sound`, with `undef` "the function's value is
`none`"): a call waits only where it and the call it waits for are undefined. -/
def Sound {α : Type} (p : α → Option α) (undef : α → Prop) : Prop :=
  ∀ c c', p c = some c' → undef c ∧ undef c'

/-- Under a sound `p`, a call whose pending calls go on forever has no value. -/
theorem Sound.undef_of_chain {α : Type} {p : α → Option α} {undef : α → Prop}
    (hs : Sound p undef) {a : α} (h : Chain p a) : undef a := by
  obtain ⟨s, h0, hsn⟩ := h
  exact h0 ▸ (hs _ _ (hsn 0)).1

/-- Under a sound `p`, a call with a value has pending calls that stop. -/
theorem Sound.ends_of_defined {α : Type} {p : α → Option α} {undef : α → Prop}
    (hs : Sound p undef) {a : α} (hd : ¬ undef a) : Ends p a :=
  (ends_or_chain p a).resolve_right fun h => hd (hs.undef_of_chain h)

end Pending

end KPrelude
