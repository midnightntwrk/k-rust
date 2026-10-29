import KPrelude.Scaffold
import Lean

/-!
# Refutations by two concrete runs

A theorem that compares runs says that from one starting configuration every run that ends ends
with the same observation (`UniqueFrom S obs c`). It is refuted by two runs from `c` that end in
terminal configurations whose observations differ. The runs are paths of indices into a function
`next` that lists steps of `S` (sound), and terminality is read off a function `all` that lists
every step of `S` (complete), so a configuration with an empty `all` has no step. A library's
`successors` is both (`successors_iff`); a library whose functions recurse well-founded has a
sound `successorsF n` with fuel, which the kernel reduces.

The kernel checks the two paths (`runsApart`, one Boolean, `refute_of_runs`) and never searches.
The search (`search`) runs in the elaborator over the compiled functions and hands the kernel only
the two paths it found (`k2l_two_runs`).

- `follow`, `star_of_follow`: where a path leads, and that it is a run of `S`.
- `terminal_of_isEmpty`: an empty `all` is terminal.
- `refute_of_runs`: two runs apart refute `UniqueFrom`.
- `UniqueFrom.of_eq`: uniqueness of the terminal configurations gives `UniqueFrom` for every
  observation.
-/

namespace KPrelude.TwoRuns

universe u v

variable {α : Type u} {β : Type v}

/-- The `i`th element of a list. -/
def nth : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

theorem mem_of_nth : ∀ {l : List α} {i : Nat} {x : α}, nth l i = some x → x ∈ l
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by cases h; exact List.mem_cons_self
  | _ :: ys, i + 1, _, h => List.mem_cons_of_mem _ (mem_of_nth (l := ys) (i := i) h)

/-- Where a path of indices into `next` leads from `c`, if every index is in range. -/
def follow (next : α → List α) : α → List Nat → Option α
  | c, [] => some c
  | c, i :: p => match nth (next c) i with
    | some c' => follow next c' p
    | none => none

theorem star_of_follow {S : α → α → Prop} {next : α → List α}
    (hs : ∀ c c' : α, c' ∈ next c → S c c') :
    ∀ (p : List Nat) {c c' : α}, follow next c p = some c' → Star S c c'
  | [], c, _, h => by cases h; exact .refl c
  | _ :: p, _, _, h => by
    unfold follow at h
    split at h
    · rename_i h₁; exact .step (hs _ _ (mem_of_nth h₁)) (star_of_follow hs p h)
    · cases h

/-- Every terminal configuration reached from `c` has the same observation. -/
def UniqueFrom (S : α → α → Prop) (obs : α → β) (c : α) : Prop :=
  ∀ {n₁ n₂ : α}, Star S c n₁ → Terminal S n₁ → Star S c n₂ → Terminal S n₂ → obs n₁ = obs n₂

/-- Uniqueness of the terminal configurations reached from `c` gives uniqueness of every
observation of them. -/
theorem UniqueFrom.of_eq {S : α → α → Prop} {c : α} (obs : α → β)
    (u : ∀ {n₁ n₂ : α}, Star S c n₁ → Terminal S n₁ → Star S c n₂ → Terminal S n₂ → n₁ = n₂) :
    UniqueFrom S obs c :=
  fun h₁ t₁ h₂ t₂ => congrArg obs (u h₁ t₁ h₂ t₂)

/-- Two runs from `c` along `p₁` and `p₂` (indices into `next`) end in configurations with no
successor in `all`, whose observations differ. -/
def runsApart [DecidableEq β] (next all : α → List α) (obs : α → β) (c : α) (p₁ p₂ : List Nat) :
    Bool :=
  match follow next c p₁, follow next c p₂ with
  | some n₁, some n₂ => (all n₁).isEmpty && (all n₂).isEmpty && !decide (obs n₁ = obs n₂)
  | _, _ => false

theorem terminal_of_isEmpty {S : α → α → Prop} {all : α → List α}
    (hc : ∀ c c' : α, S c c' → c' ∈ all c) {c : α} (h : (all c).isEmpty = true) : Terminal S c :=
  fun _ s => by
    have := hc _ _ s
    rw [List.isEmpty_iff.mp h] at this
    cases this

/-- Two runs apart refute uniqueness from their starting configuration. -/
theorem refute_of_runs [DecidableEq β] {S : α → α → Prop} {next all : α → List α}
    (hs : ∀ c c' : α, c' ∈ next c → S c c') (hc : ∀ c c' : α, S c c' → c' ∈ all c)
    {obs : α → β} {c : α} (p₁ p₂ : List Nat)
    (h : runsApart next all obs c p₁ p₂ = true) : ¬ UniqueFrom S obs c := fun u => by
  unfold runsApart at h
  split at h
  · rename_i n₁ n₂ e₁ e₂
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact h.2 (u (star_of_follow hs p₁ e₁) (terminal_of_isEmpty hc h.1.1)
      (star_of_follow hs p₂ e₂) (terminal_of_isEmpty hc h.1.2))
  · cases h

/-! ## The search, run by the elaborator -/

section Search

variable {α β : Type}

structure SearchState (α β : Type) where
  seen : Array α := #[]
  first : Option (β × List Nat) := none

/-- Depth first from `c` (`path` reversed): the paths to two configurations with no successor in
`all` whose observations differ. Each configuration is visited once: the terminal ones reachable
from a configuration seen before were found from it. Past `budget` configurations, `throw`. -/
partial def dfs [BEq α] [BEq β] (next all : α → List α) (obs : α → β) (budget : Nat) (c : α)
    (path : List Nat) : ExceptT Unit (StateM (SearchState α β)) (Option (List Nat × List Nat)) := do
  let s ← get
  if s.seen.contains c then return none
  if s.seen.size ≥ budget then throw ()
  set { s with seen := s.seen.push c }
  if (all c).isEmpty then
    match s.first with
    | none => modify fun s => { s with first := some (obs c, path.reverse) }; return none
    | some (o, p) => return if o != obs c then some (p, path.reverse) else none
  for (c', i) in (next c).zipIdx do
    if let some r ← dfs next all obs budget c' (i :: path) then return some r
  return none

/-- The two paths, or `none` when there are no two such runs or the budget ran out; and the
number of configurations visited. -/
def search [BEq α] [BEq β] (next all : α → List α) (obs : α → β) (c : α) (budget : Nat) :
    Option (List Nat × List Nat) × Nat :=
  match (dfs next all obs budget c []).run.run {} with
  | (.ok r, s) => (r, s.seen.size)
  | (.error (), s) => (none, s.seen.size)

end Search

open Lean Elab Tactic Meta

unsafe def evalSearchUnsafe (e : Expr) : MetaM (Option (List Nat × List Nat) × Nat) :=
  evalExpr (Option (List Nat × List Nat) × Nat) (toTypeExpr (Option (List Nat × List Nat) × Nat)) e

@[implemented_by evalSearchUnsafe]
opaque evalSearch (e : Expr) : MetaM (Option (List Nat × List Nat) × Nat)

/-- `k2l_two_runs next, hs, all, hc` closes `¬ UniqueFrom S obs c`, where
`hs : ∀ {c c'}, c' ∈ next c → S c c'` and `hc : ∀ {c c'}, S c c' → c' ∈ all c`: it searches the
configurations reachable from `c` by `next` for two with no successor in `all` whose observations
differ, then has the kernel check the two paths it found (`refute_of_runs`). `k2l_two_runs succ, h`
takes `h : c' ∈ succ c ↔ S c c'` for both. A trailing `, N` bounds the configurations visited
(default 100000). The paths are logged; `c`, `obs` and the functions must be closed terms. -/
syntax (name := k2lTwoRuns) "k2l_two_runs " term ", " term (", " term ", " term)? (", " num)? :
  tactic

@[tactic k2lTwoRuns] def evalK2lTwoRuns : Tactic := fun stx => withMainContext do
  let nextStx : Term := ⟨stx[1]⟩
  let hStx : Term := ⟨stx[3]⟩
  let (allStx, hsStx, hcStx) : Term × Term × Term ←
    if stx[4].isNone then pure (nextStx, ← `(($hStx).mp), ← `(($hStx).mpr))
    else pure (⟨stx[4][1]⟩, hStx, ⟨stx[4][3]⟩)
  let budget := if stx[5].isNone then 100000 else stx[5][1].isNatLit?.getD 100000
  let tgt ← instantiateMVars (← getMainTarget)
  let some u := tgt.app1? ``Not | throwError "k2l_two_runs: the goal is not `¬ UniqueFrom S obs c`"
  unless u.isAppOfArity ``UniqueFrom 5 do
    throwError "k2l_two_runs: the goal is not `¬ UniqueFrom S obs c`: {u}"
  let args := u.getAppArgs
  let (obs, c) := (args[3]!, args[4]!)
  let next ← instantiateMVars (← Term.elabTerm nextStx none)
  let all ← instantiateMVars (← Term.elabTerm allStx none)
  let e ← instantiateMVars (← mkAppM ``search #[next, all, obs, c, mkNatLit budget])
  let t₀ ← IO.monoMsNow
  let (r, n) ← evalSearch e
  let t₁ ← IO.monoMsNow
  let some (p₁, p₂) := r
    | throwError "k2l_two_runs: no two terminal configurations with different observations among \
        the {n} reachable configurations visited (budget {budget})"
  evalTactic (← `(tactic| exact KPrelude.TwoRuns.refute_of_runs (next := $nextStx) (all := $allStx)
    (fun _ _ h => $hsStx h) (fun _ _ h => $hcStx h) $(quote p₁) $(quote p₂) (by decide +kernel)))
  let t₂ ← IO.monoMsNow
  logInfo m!"k2l_two_runs: {n} configurations visited ({t₁ - t₀} ms); two runs of {p₁.length} \
    and {p₂.length} steps checked by the kernel ({t₂ - t₁} ms): {p₁} and {p₂}"

end KPrelude.TwoRuns
