/-
  Symbolic states and claims over `Step` (design SY-0). A symbolic state is a presentation of a
  set of configurations; every statement is about that set, so a tool may compute symbolic states
  however it likes and Lean checks what they denote.
-/
import KcoreSpec.Cert
import KcoreSpec.Reachability

set_option autoImplicit false

namespace KCore

open KCore.Reachability

/-- A symbolic state: variables with sorts, a pattern over them, and a constraint on their
values. The constraint is a Lean proposition: a `requires` or `ensures` term is the instance
`fun σ => EvalTerm c σ t (some (bool true))`. -/
structure SymState where
  vars : List Srt
  term : Term
  cond : Subst → Prop

/-- σ is a well-sorted valuation, equal to ρ on the first `n` variables. -/
def Extends (n : Nat) (ρ σ : Subst) : Prop := ∀ i, i < n → σ.lookup i = ρ.lookup i

namespace SymState

/-- `x` is the instance of φ at σ. -/
def At (c : Semantics) (φ : SymState) (σ : Subst) (x : Config c) : Prop :=
  c.WellSorted φ.vars σ ∧ PatVal c σ φ.term x.val ∧ φ.cond σ

/-- The configurations φ denotes, its first `n` variables fixed by ρ and the rest existential. -/
def DenFrom (c : Semantics) (n : Nat) (ρ : Subst) (φ : SymState) (x : Config c) : Prop :=
  ∃ σ, Extends n ρ σ ∧ φ.At c σ x

/-- The configurations φ denotes. -/
def Den (c : Semantics) (φ : SymState) (x : Config c) : Prop := ∃ σ, φ.At c σ x

end SymState

/-- A reachability claim `∀ x̄. pre(x̄) ⇒ ∃ ȳ. post(x̄, ȳ)`: the variables of `pre` are universal
and are the first variables of `post`; the others of `post` are existential (K's `?X`), and
`post.cond` holds an `ensures`. -/
structure Claim where
  pre : SymState
  post : SymState

/-- All-path validity: for each valuation of the universal variables, every complete execution
from the instance of `pre` passes through an instance of `post` at an extension of it. -/
def Claim.AllPathValid (c : Semantics) (k : Claim) : Prop :=
  ∀ ρ, AllPath (Step c) (fun x => k.pre.At c ρ x) (k.post.DenFrom c k.pre.vars.length ρ)

/-- One-path validity: some execution from the instance of `pre` reaches an instance of `post`,
or from it some execution never ends. Stated for the terminating case only: the reaching one. -/
def Claim.OnePathReaches (c : Semantics) (k : Claim) : Prop :=
  ∀ ρ x, k.pre.At c ρ x → ∃ y, Cert.Reach (Step c) x y ∧ k.post.DenFrom c k.pre.vars.length ρ y

/-- Rule `r` takes `x` to `y` under σ. -/
def Fires (c : Semantics) (r : Rule) (σ : Subst) (x y : Config c) : Prop :=
  c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
    EvalTerm c σ r.rhs (some y.val) ∧
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val

theorem step_iff_fires {c : Semantics} {x y : Config c} :
    Step c x y ↔ ∃ r ∈ c.rules, ∃ σ, Fires c r σ x y :=
  ⟨fun h => by cases h with | rule r mem σ h1 h2 h3 h4 h5 => exact ⟨r, mem, σ, h1, h2, h3, h4, h5⟩,
   fun ⟨r, mem, σ, h1, h2, h3, h4, h5⟩ => .rule r mem σ h1 h2 h3 h4 h5⟩

/-- A symbolic step: every configuration of φ has a successor, and every successor is in one of
the states `ψs`, the first `n` variables kept. -/
def SymStep (c : Semantics) (n : Nat) (φ : SymState) (ψs : List SymState) : Prop :=
  ∀ ρ, StepsInto (Step c) (φ.DenFrom c n ρ) (fun y => ∃ ψ ∈ ψs, ψ.DenFrom c n ρ y)

/-- A symbolic step followed by a proof from each resulting state. -/
theorem SymStep.allPath {c : Semantics} {n : Nat} {φ : SymState} {ψs : List SymState}
    (hs : SymStep c n φ ψs) {ρ : Subst} {G : Config c → Prop}
    (h : ∀ ψ ∈ ψs, AllPath (Step c) (ψ.DenFrom c n ρ) G) :
    AllPath (Step c) (φ.DenFrom c n ρ) G :=
  AllPath.step (hs ρ) fun y ⟨ψ, hψ, hy⟩ l hl => h ψ hψ y hy l hl

end KCore

#print axioms KCore.SymStep.allPath
#print axioms KCore.step_iff_fires
