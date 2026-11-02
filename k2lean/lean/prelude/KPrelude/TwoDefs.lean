import KPrelude.TwoStarts

/-!
# Refutations by two runs of two definitions

A refinement between two definitions `A` and `B` along a translation `tr` says that from a
configuration `a` of `A`, every run of `A` to a terminal configuration is matched by a run of `B`
from `tr a` to the translation of its end, and every run of `B` from `tr a` to a terminal
configuration by a run of `A` from `a` to a configuration it is the translation of (`EndsMatch`).
It is refuted by a program on which the two definitions disagree: one run of one side to a
terminal configuration, and every terminal configuration that the other side reaches apart from
it (`¬ Matched`).

The run is a path of indices into a function `all` that lists exactly the steps (a library's
`successors`, `successors_iff`), so its end is terminal when `all` is empty there. What the other
side reaches is a list `L` that the kernel computes (`explore`, whose result is not trusted) and
checks: it contains the start and is closed under `all` (`closedB`), so every run from the start
stays in it (`mem_of_star`). For a deterministic side `L` is its one run. The kernel checks one
Boolean (`matchedApart`, `not_matched`); the elaborator finds the direction, the path and the
fuel over the compiled functions (`k2l_ends_apart`).

Not in the `KPrelude` root: a refine demo's generated `Witnesses.lean` imports it.
-/

namespace KPrelude.TwoRuns

universe u v

variable {α : Type u} {β : Type v}

/-- Every run of `S` from `a` to a terminal configuration is matched by a run of `S'` from `b` to
a terminal configuration that `R` relates to its end. -/
def Matched (S : α → α → Prop) (S' : β → β → Prop) (R : α → β → Prop) (a : α) (b : β) : Prop :=
  ∀ {a'}, Star S a a' → Terminal S a' → ∃ b', Star S' b b' ∧ Terminal S' b' ∧ R a' b'

/-- The runs from `a` and from `tr a` that end, end in translations of each other, in both
directions: what a refinement along `tr` transfers (`run_terminal`, `run_terminal_back`). -/
def EndsMatch (S : α → α → Prop) (S' : β → β → Prop) (tr : α → β) (a : α) : Prop :=
  Matched S S' (fun x y => y = tr x) a (tr a) ∧ Matched S' S (fun y x => y = tr x) (tr a) a

/-- Membership by a decidable equality, which the kernel reduces. -/
def memB [DecidableEq β] (y : β) (L : List β) : Bool := L.any fun z => decide (y = z)

theorem mem_of_memB [DecidableEq β] {y : β} {L : List β} (h : memB y L = true) : y ∈ L := by
  obtain ⟨z, hz, e⟩ := List.any_eq_true.mp h
  exact (of_decide_eq_true e) ▸ hz

/-- The configurations reachable from the worklist by `all`, after `seen`, within `fuel` visits;
`none` when the fuel runs out. Its result is checked (`closedB`), not trusted. -/
def explore [DecidableEq β] (all : β → List β) : Nat → List β → List β → Option (List β)
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | n + 1, y :: ys, seen =>
    if memB y seen then explore all n ys seen else explore all n (all y ++ ys) (y :: seen)

/-- Every successor by `all` of a member of `L` is a member. -/
def closedB [DecidableEq β] (all : β → List β) (L : List β) : Bool :=
  L.all fun y => (all y).all fun z => memB z L

theorem mem_of_star [DecidableEq β] {S' : β → β → Prop} {all : β → List β}
    (hc : ∀ x y, S' x y → y ∈ all x) {L : List β} (hL : closedB all L = true) :
    ∀ {b b' : β}, Star S' b b' → b ∈ L → b' ∈ L
  | _, _, .refl _, hb => hb
  | _, _, .step s r, hb => by
    refine mem_of_star (S' := S') hc hL r (mem_of_memB ?_)
    exact List.all_eq_true.mp (List.all_eq_true.mp hL _ hb) _ (hc _ _ s)

/-- A run of `all` from `a` along `p` to a configuration with no successor, and the configurations
`all'` reaches from `b` (within `fuel`), none of them without a successor and related to it by
`rel`. -/
def matchedApart [DecidableEq β] (all : α → List α) (all' : β → List β) (rel : α → β → Bool)
    (a : α) (b : β) (p : List Nat) (fuel : Nat) : Bool :=
  match follow all a p, explore all' fuel [b] [] with
  | some a', some L =>
    (all a').isEmpty && memB b L && closedB all' L &&
      L.all fun y => !((all' y).isEmpty && rel a' y)
  | _, _ => false

/-- Such a run refutes that the runs of `S` from `a` that end are matched from `b`. -/
theorem not_matched [DecidableEq β] {S : α → α → Prop} {S' : β → β → Prop} {all : α → List α}
    {all' : β → List β} (h₁ : ∀ x y, y ∈ all x ↔ S x y) (h₂ : ∀ x y, y ∈ all' x ↔ S' x y)
    {R : α → β → Prop} {rel : α → β → Bool} (hrel : ∀ x y, R x y → rel x y = true) {a : α}
    {b : β} (p : List Nat) (fuel : Nat) (h : matchedApart all all' rel a b p fuel = true) :
    ¬ Matched S S' R a b := fun m => by
  unfold matchedApart at h
  split at h
  · rename_i a' L e₁ _
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨ht, hb⟩, hL⟩, hall⟩ := h
    obtain ⟨b', hr, hb', hR⟩ :=
      m (star_of_follow (fun x y s => (h₁ x y).mp s) p e₁)
        (terminal_of_isEmpty (fun x y s => (h₁ x y).mpr s) ht)
    have hm := mem_of_star (fun x y s => (h₂ x y).mpr s) hL hr (mem_of_memB hb)
    have hy := List.all_eq_true.mp hall b' hm
    have he : (all' b').isEmpty = true := by
      cases hq : all' b' with
      | nil => rfl
      | cons z _ => exact absurd ((h₂ _ _).mp (hq ▸ List.mem_cons_self)) (hb' z)
    simp [he, hrel _ _ hR] at hy
  · cases h

/-- `A`'s run from `a` ends where no run of `B` from `tr a` ends in its translation. -/
theorem ends_apart_fwd [DecidableEq β] {S : α → α → Prop} {S' : β → β → Prop}
    {all : α → List α} {all' : β → List β} (h₁ : ∀ x y, y ∈ all x ↔ S x y)
    (h₂ : ∀ x y, y ∈ all' x ↔ S' x y) {tr : α → β} {a : α} (p : List Nat) (fuel : Nat)
    (h : matchedApart all all' (fun x y => decide (y = tr x)) a (tr a) p fuel = true) :
    ¬ EndsMatch S S' tr a :=
  fun e => not_matched h₁ h₂ (fun _ _ r => decide_eq_true r) p fuel h e.1

/-- `B`'s run from `tr a` ends where no run of `A` from `a` ends in a configuration it translates. -/
theorem ends_apart_bwd {S : α → α → Prop} {S' : β → β → Prop} [DecidableEq α] [DecidableEq β]
    {all : α → List α} {all' : β → List β} (h₁ : ∀ x y, y ∈ all x ↔ S x y)
    (h₂ : ∀ x y, y ∈ all' x ↔ S' x y) {tr : α → β} {a : α} (p : List Nat) (fuel : Nat)
    (h : matchedApart all' all (fun y x => decide (y = tr x)) (tr a) a p fuel = true) :
    ¬ EndsMatch S S' tr a :=
  fun e => not_matched h₂ h₁ (fun _ _ r => decide_eq_true r) p fuel h e.2

/-! ## The search, run by the elaborator -/

section Search

variable {α β : Type}

/-- The fuel `explore` takes over `L`, the configurations it reached: one visit per item of the
worklist, the start and every successor of each. -/
def fuelOf (all : β → List β) (L : List β) : Nat :=
  L.foldl (fun n y => n + (all y).length) 1

/-- A path from `a` along `all` to a configuration with no successor, `fin` a test of it, apart
by `rel` from every configuration with no successor that `all'` reaches from `b`, with the fuel
of that exploration; `none` if there is none within `budget`. -/
def matchedSearch [DecidableEq α] [DecidableEq β] (all : α → List α) (all' : β → List β)
    (rel : α → β → Bool) (a : α) (b : β) (budget : Nat) : Option (List Nat × Nat) × Nat :=
  match explore all' budget [b] [] with
  | none => (none, budget)
  | some L =>
    let (fs, n) := finalsFrom all (fun x => (all x).isEmpty) a budget
    let ends := L.filter fun y => (all' y).isEmpty
    match fs.find? fun (x, _) => ends.all fun y => !rel x y with
    | some (_, p) => (some (p, fuelOf all' L), n + L.length)
    | none => (none, n + L.length)

/-- Either direction: `true` with a path of `A` from `a` (`ends_apart_fwd`), `false` with one of
`B` from `tr a` (`ends_apart_bwd`), and the fuel; and the number of configurations visited. -/
def endsSearch [DecidableEq α] [DecidableEq β] (all : α → List α) (all' : β → List β)
    (tr : α → β) (a : α) (budget : Nat) : Option (Bool × List Nat × Nat) × Nat :=
  match matchedSearch all all' (fun x y => decide (y = tr x)) a (tr a) budget with
  | (some (p, f), n) => (some (true, p, f), n)
  | (none, n) =>
    match matchedSearch all' all (fun y x => decide (y = tr x)) (tr a) a budget with
    | (some (p, f), m) => (some (false, p, f), n + m)
    | (none, m) => (none, n + m)

end Search

open Lean Elab Tactic Meta

unsafe def evalEndsSearchUnsafe (e : Expr) : MetaM (Option (Bool × List Nat × Nat) × Nat) :=
  evalExpr (Option (Bool × List Nat × Nat) × Nat) (toTypeExpr (Option (Bool × List Nat × Nat) × Nat)) e

@[implemented_by evalEndsSearchUnsafe]
opaque evalEndsSearch (e : Expr) : MetaM (Option (Bool × List Nat × Nat) × Nat)

/-- `k2l_ends_apart allA, hA, allB, hB` closes `¬ EndsMatch S S' tr a`, where
`hA : c' ∈ allA c ↔ S c c'` and `hB : d' ∈ allB d ↔ S' d d'` (a library's `successors` and
`successors_iff`): it searches, first from `a` then from `tr a`, for a run to a terminal
configuration apart from every terminal configuration that the other side reaches, then has the
kernel check that run and the other side's reachable configurations (`ends_apart_fwd`,
`ends_apart_bwd`). A trailing `, N` bounds the configurations visited from each (default 100000).
`a`, `tr` and the functions must be closed terms. -/
syntax (name := k2lEndsApart) "k2l_ends_apart " term ", " term ", " term ", " term (", " num)? :
  tactic

@[tactic k2lEndsApart] def evalK2lEndsApart : Tactic := fun stx => withMainContext do
  let allAStx : Term := ⟨stx[1]⟩
  let hAStx : Term := ⟨stx[3]⟩
  let allBStx : Term := ⟨stx[5]⟩
  let hBStx : Term := ⟨stx[7]⟩
  let budget := if stx[8].isNone then 100000 else stx[8][1].isNatLit?.getD 100000
  let tgt ← instantiateMVars (← getMainTarget)
  let some u := tgt.app1? ``Not
    | throwError "k2l_ends_apart: the goal is not `¬ EndsMatch S S' tr a`"
  let u ← whnfR u
  unless u.isAppOfArity ``EndsMatch 6 do
    throwError "k2l_ends_apart: the goal is not `¬ EndsMatch S S' tr a`: {u}"
  let args := u.getAppArgs
  let (tr, a) := (args[4]!, args[5]!)
  let allA ← instantiateMVars (← Term.elabTerm allAStx none)
  let allB ← instantiateMVars (← Term.elabTerm allBStx none)
  let e ← instantiateMVars (← mkAppM ``endsSearch #[allA, allB, tr, a, mkNatLit budget])
  let t₀ ← IO.monoMsNow
  let (r, n) ← evalEndsSearch e
  let t₁ ← IO.monoMsNow
  let some (fwd, p, fuel) := r
    | throwError "k2l_ends_apart: no run of either side to a terminal configuration apart from \
        every one the other side reaches, among the {n} configurations visited (budget {budget} \
        from each)"
  if fwd then
    evalTactic (← `(tactic| exact KPrelude.TwoRuns.ends_apart_fwd (all := $allAStx)
      (all' := $allBStx) (fun _ _ => $hAStx) (fun _ _ => $hBStx) $(quote p) $(quote fuel) (by decide +kernel)))
  else
    evalTactic (← `(tactic| exact KPrelude.TwoRuns.ends_apart_bwd (all := $allAStx)
      (all' := $allBStx) (fun _ _ => $hAStx) (fun _ _ => $hBStx) $(quote p) $(quote fuel) (by decide +kernel)))
  let t₂ ← IO.monoMsNow
  logInfo m!"k2l_ends_apart: {n} configurations visited ({t₁ - t₀} ms); a run of \
    {if fwd then "the first" else "the second"} definition of {p.length} steps and the other's \
    configurations ({fuel} visits) checked by the kernel ({t₂ - t₁} ms): {p}"

end KPrelude.TwoRuns
