import KPrelude.TwoRuns
import KPrelude.LowEq

/-!
# Refutations by two runs from two starting configurations

Noninterference compares two runs from two starting configurations (the private inputs differ):
every run from `c₁` and every run from `c₂` that end are related by `Q` (`RelatedFrom`), where
`Q` is the statement's conclusion, under its premise on the final configurations (the disclosed
values agree). It is refuted by one run from each that end and are not related. As for one start
(`TwoRuns`), the runs are paths of indices into a function `next` that lists steps (sound); the
end is a Boolean `fin`, and that the two final configurations are not related is a Boolean
`apart` with `apart a b = true → ¬ Q a b`, so that the kernel checks one Boolean
(`runsApartBy`, `refute_by_runs`) and never searches. The search (`searchFrom`) runs in the
elaborator over the compiled functions (`k2l_two_starts`).

For the stores of two runs, which noninterference compares at the keys the observer sees
(`MapHook.AgreeOn`), with concrete maps:
- `AgreeOn.of_removeKeys`: two maps agree at the low keys when they are equal once some keys are
  removed and none of those keys is low;
- `lowApart`, `not_agreeOn_of_lowApart`: a key of either map, low by a Boolean test, at which the
  lookups differ, refutes agreement.
- `not_imp_of`, `not_and_of`, `not_of_decide`: `apart` for a conclusion under a premise, for a
  conjunction, and for a decidable proposition.

Not in the `KPrelude` root: a noninterference demo's generated `Witnesses.lean` imports it.
-/

namespace KPrelude.TwoRuns

universe u v

variable {α : Type u}

/-- Every run from `c₁` and every run from `c₂` that end in configurations `fin` accepts are
related by `Q`. -/
def RelatedFrom (S : α → α → Prop) (fin : α → Bool) (Q : α → α → Prop) (c₁ c₂ : α) : Prop :=
  ∀ {f₁ f₂ : α}, Star S c₁ f₁ → fin f₁ = true → Star S c₂ f₂ → fin f₂ = true → Q f₁ f₂

/-- A run from `c₁` along `p₁` and one from `c₂` along `p₂` end in configurations `fin` accepts
that `apart` separates. -/
def runsApartBy (next : α → List α) (fin : α → Bool) (apart : α → α → Bool) (c₁ c₂ : α)
    (p₁ p₂ : List Nat) : Bool :=
  match follow next c₁ p₁, follow next c₂ p₂ with
  | some n₁, some n₂ => fin n₁ && fin n₂ && apart n₁ n₂
  | _, _ => false

/-- Two such runs refute that the runs from `c₁` and `c₂` are related. -/
theorem refute_by_runs {S : α → α → Prop} {next : α → List α}
    (hs : ∀ c c' : α, c' ∈ next c → S c c') {fin : α → Bool} {apart : α → α → Bool}
    {Q : α → α → Prop} (happ : ∀ a b, apart a b = true → ¬ Q a b) {c₁ c₂ : α} (p₁ p₂ : List Nat)
    (h : runsApartBy next fin apart c₁ c₂ p₁ p₂ = true) : ¬ RelatedFrom S fin Q c₁ c₂ :=
  fun u => by
    unfold runsApartBy at h
    split at h
    · rename_i n₁ n₂ e₁ e₂
      simp only [Bool.and_eq_true] at h
      exact happ _ _ h.2 (u (star_of_follow hs p₁ e₁) h.1.1 (star_of_follow hs p₂ e₂) h.1.2)
    · cases h

/-- `apart` for a conclusion `Q` under a decidable premise `P`: `P` holds and `Q` does not. -/
theorem not_imp_of {P Q : Prop} [Decidable P] {q : Bool} (hq : q = true → ¬ Q) :
    (decide P && q) = true → ¬ (P → Q) := fun h hpq => by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact hq h.2 (hpq h.1)

/-- `apart` for a conjunction: one of its parts does not hold. -/
theorem not_and_of {A B : Prop} {a b : Bool} (ha : a = true → ¬ A) (hb : b = true → ¬ B) :
    (a || b) = true → ¬ (A ∧ B) := fun h hab => by
  simp only [Bool.or_eq_true] at h
  exact h.elim (fun h => ha h hab.1) (fun h => hb h hab.2)

/-- `apart` for a decidable proposition: it does not hold. -/
theorem not_of_decide {Q : Prop} [Decidable Q] : (!decide Q) = true → ¬ Q := fun h hq => by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h hq

/-! ## The search, run by the elaborator -/

section Search

variable {α : Type}

/-- Depth first from `c` (`path` reversed): the configurations `fin` accepts, with their paths.
Each configuration is visited once; past `budget` configurations, `throw`, keeping what was found. -/
partial def finals [BEq α] (next : α → List α) (fin : α → Bool) (budget : Nat) (c : α)
    (path : List Nat) : ExceptT Unit (StateM (Array α × Array (α × List Nat))) Unit := do
  let (seen, out) ← get
  if seen.contains c then return
  if seen.size ≥ budget then throw ()
  set (seen.push c, out)
  if fin c then
    modify fun (s, o) => (s, o.push (c, path.reverse))
    return
  for (c', i) in (next c).zipIdx do
    finals next fin budget c' (i :: path)

/-- The configurations `fin` accepts that are reached from `c` within `budget` configurations,
and the number visited. -/
def finalsFrom [BEq α] (next : α → List α) (fin : α → Bool) (c : α) (budget : Nat) :
    Array (α × List Nat) × Nat :=
  let (_, (seen, out)) := (finals next fin budget c []).run.run (#[], #[])
  (out, seen.size)

/-- A path from `c₁` and one from `c₂` to configurations `fin` accepts that `apart` separates, or
`none` among the first `budget` configurations from each; and the number visited. -/
def searchFrom [BEq α] (next : α → List α) (fin : α → Bool) (apart : α → α → Bool) (c₁ c₂ : α)
    (budget : Nat) : Option (List Nat × List Nat) × Nat := Id.run do
  let (f₁, n₁) := finalsFrom next fin c₁ budget
  let (f₂, n₂) := finalsFrom next fin c₂ budget
  for (a, p) in f₁ do
    for (b, q) in f₂ do
      if apart a b then return (some (p, q), n₁ + n₂)
  return (none, n₁ + n₂)

end Search

open Lean Elab Tactic Meta

unsafe def evalSearchFromUnsafe (e : Expr) : MetaM (Option (List Nat × List Nat) × Nat) :=
  evalExpr (Option (List Nat × List Nat) × Nat) (toTypeExpr (Option (List Nat × List Nat) × Nat)) e

@[implemented_by evalSearchFromUnsafe]
opaque evalSearchFrom (e : Expr) : MetaM (Option (List Nat × List Nat) × Nat)

/-- `k2l_two_starts next, hs, apart, happ` closes `¬ RelatedFrom S fin Q c₁ c₂`, where
`hs : ∀ {c c'}, c' ∈ next c → S c c'` and `happ : ∀ a b, apart a b = true → ¬ Q a b`: it searches
the configurations reachable from `c₁` and from `c₂` by `next` for two that `fin` accepts and
`apart` separates, then has the kernel check the two paths it found (`refute_by_runs`). A
trailing `, N` bounds the configurations visited from each (default 100000). The paths are
logged; `c₁`, `c₂`, `fin`, `apart` and `next` must be closed terms. -/
syntax (name := k2lTwoStarts) "k2l_two_starts " term ", " term ", " term ", " term (", " num)? :
  tactic

@[tactic k2lTwoStarts] def evalK2lTwoStarts : Tactic := fun stx => withMainContext do
  let nextStx : Term := ⟨stx[1]⟩
  let hsStx : Term := ⟨stx[3]⟩
  let apartStx : Term := ⟨stx[5]⟩
  let happStx : Term := ⟨stx[7]⟩
  let budget := if stx[8].isNone then 100000 else stx[8][1].isNatLit?.getD 100000
  let tgt ← instantiateMVars (← getMainTarget)
  let some u := tgt.app1? ``Not
    | throwError "k2l_two_starts: the goal is not `¬ RelatedFrom S fin Q c₁ c₂`"
  let u ← whnfR u
  unless u.isAppOfArity ``RelatedFrom 6 do
    throwError "k2l_two_starts: the goal is not `¬ RelatedFrom S fin Q c₁ c₂`: {u}"
  let args := u.getAppArgs
  let (fin, c₁, c₂) := (args[2]!, args[4]!, args[5]!)
  let next ← instantiateMVars (← Term.elabTerm nextStx none)
  let apart ← instantiateMVars (← Term.elabTerm apartStx none)
  let e ← instantiateMVars (← mkAppM ``searchFrom #[next, fin, apart, c₁, c₂, mkNatLit budget])
  let t₀ ← IO.monoMsNow
  let (r, n) ← evalSearchFrom e
  let t₁ ← IO.monoMsNow
  let some (p₁, p₂) := r
    | throwError "k2l_two_starts: no two final configurations, one from each start, that are \
        apart, among the {n} reachable configurations visited (budget {budget} from each)"
  evalTactic (← `(tactic| exact KPrelude.TwoRuns.refute_by_runs (next := $nextStx)
    (fun _ _ h => $hsStx h) (apart := $apartStx) $happStx $(quote p₁) $(quote p₂)
    (by decide +kernel)))
  let t₂ ← IO.monoMsNow
  logInfo m!"k2l_two_starts: {n} configurations visited ({t₁ - t₀} ms); two runs of {p₁.length} \
    and {p₂.length} steps checked by the kernel ({t₂ - t₁} ms): {p₁} and {p₂}"

end KPrelude.TwoRuns

namespace KPrelude.MapHook

open ListIso

variable {M K V X : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]

/-- `E` with the keys `ks` removed, in order. -/
def removeKeys (E : M) : List K → M
  | [] => E
  | k :: ks => removeKeys (remove E k) ks

variable {Low : X → Prop} {ι : X → K} {E₁ E₂ : M}

/-- A key of either map that `low` accepts, at which the lookups differ. -/
def lowApart [DecidableEq V] (low : K → Bool) (E₁ E₂ : M) : Bool :=
  ((toList E₁).map (·.1) ++ (toList E₂).map (·.1)).any fun k =>
    low k && !decide (lookup E₁ k = lookup E₂ k)

/-- Such a key refutes agreement at the low keys, when every key `low` accepts is a low one. -/
theorem not_agreeOn_of_lowApart [DecidableEq V] {low : K → Bool}
    (hlow : ∀ k, low k = true → ∃ x, ι x = k ∧ Low x) (h : lowApart low E₁ E₂ = true) :
    ¬ AgreeOn Low ι E₁ E₂ := fun ha => by
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hk
  obtain ⟨x, rfl, hx⟩ := hlow k hk.1
  exact hk.2 (ha x hx)

variable [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem lookup_removeKeys {k : K} : ∀ (ks : List K) {E : M}, WF E → k ∉ ks →
    lookup (removeKeys E ks) k = lookup E k
  | [], _, _, _ => rfl
  | k' :: ks, E, hw, hk => by
    simp only [List.mem_cons, not_or] at hk
    exact (lookup_removeKeys ks (wf_remove hw) hk.2).trans (lookup_remove_ne hk.1 hw)

/-- Two maps agree at the low keys when they are equal once the keys of `xs` are removed and no
`x` of `xs` is low. -/
theorem AgreeOn.of_removeKeys (hι : Function.Injective ι) (xs : List X) (hw₁ : WF E₁)
    (hw₂ : WF E₂) (h : removeKeys E₁ (xs.map ι) = removeKeys E₂ (xs.map ι))
    (hx : ∀ x ∈ xs, ¬ Low x) : AgreeOn Low ι E₁ E₂ := fun x hl => by
  have hk : ι x ∉ xs.map ι := fun hm => by
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    exact hx y hy (hι he ▸ hl)
  rw [← lookup_removeKeys _ hw₁ hk, ← lookup_removeKeys _ hw₂ hk, h]

end KPrelude.MapHook
