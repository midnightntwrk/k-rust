# SY-0: the symbolic layer

Delivers ticket SY-0 of `TICKETS-2026-11-11.toml` (finding F8).
Two Lean files beside this one are kernel-checked against the library at `938ddde1`:

- `Reachability.lean`: claims over any relation; depends on propext and Quot.sound only.
- `Symbolic.lean`: symbolic states and claims over `Step`.

SY-1 adds both to `KcoreSpec/` unchanged and builds §4 on them.

## 1. The principle

A symbolic state is a presentation of a set of configurations, and every statement is about that set.
A tool (k2lean, a tactic, a backend's proof) computes symbolic states however it likes; Lean checks what they denote.
So the layer needs no unification algorithm, no simplifier and no embedded constraint logic in the kernel: constraints are Lean propositions.

## 2. Claims (`Reachability.lean`)

`CPath r x l`: `l` is a complete path from `x`, ending where `r` has no successor.
`AllPath r P Q`: every complete path from a state of `P` passes through a state of `Q`.
This is all-path reachability with partial correctness: an execution that never ends is not constrained.

Proved, for any relation:

| theorem | use |
|---|---|
| `AllPath.refl`, `AllPath.mono` | consequence |
| `AllPath.trans` | sequencing two claims |
| `AllPath.cases` | case split |
| `AllPath.step` | one step: `StepsInto r P P'` (every state of `P` has a successor, and all successors are in `P'`) |
| `circularity` | a set of claims `(P i, Q i)`, each derived by `Derives` from steps and from the claims themselves, a claim usable only after a first step |
| `Derives.allPath` | a derivation from claims already valid |
| `allPath_of_invariant` | a set closed under steps until the goal |

`circularity` is the rule that makes loops and recursion provable; it is proved by induction on the length of the path, with no coinduction.

## 3. Symbolic states over `Step` (`Symbolic.lean`)

```lean
structure SymState where
  vars : List Srt
  term : Term              -- a pattern, read by PatVal
  cond : Subst → Prop      -- a requires or ensures t is  fun σ => EvalTerm c σ t (some (bool true))

def SymState.At c φ σ x      := c.WellSorted φ.vars σ ∧ PatVal c σ φ.term x.val ∧ φ.cond σ
def SymState.DenFrom c n ρ φ x := ∃ σ, Extends n ρ σ ∧ φ.At c σ x     -- first n variables fixed by ρ
structure Claim where pre post : SymState
def Claim.AllPathValid c k   := ∀ ρ, AllPath (Step c) (k.pre.At c ρ) (k.post.DenFrom c k.pre.vars.length ρ)
```

- **Universal and existential variables.** The variables of `pre` are universal and are the first variables of `post`; the rest of `post`'s are existential. That is K's `?X`.
- **`ensures`** is `post.cond`.
- **One-path** claims are stated for the reaching case (`Claim.OnePathReaches`); the diverging alternative needs infinite paths and is left until something asks for it.
- **`Fires c r σ x y`** names what `Step.rule` requires of one rule, and `step_iff_fires : Step c x y ↔ ∃ r ∈ c.rules, ∃ σ, Fires c r σ x y`.
- **`SymStep c n φ ψs`**: every configuration of φ has a successor and every successor is in one of `ψs`, with the first `n` variables kept. `SymStep.allPath` chains it with proofs from each resulting state.

## 4. What SY-1 builds: proving a `SymStep`

A `SymStep` has two halves, and each needs one kind of lemma.

- **Progress**: exhibit a rule and a valuation. `Step.rule` with the rule's data lemma (`rule_i`, which `Surface.lean` has today) is enough.
- **Coverage**: every successor is in the cover. By `step_iff_fires` this is one case per rule. For each rule the facts are `PatVal c σ r.lhs v` and `PatVal c σ' φ.term v` for the same `v`, and the goal follows by inverting both.

So SY-1 is three library pieces and no new per-rule output:

1. **Inversion lemmas for `PatVal`, `PatVals` and `EvalTerm`** by head (`ctor`, `inj`, `dv`, `var`, `as`, a hook, a parameter, a call), as `iff` statements usable by `simp`. Some exist under other names (`EvalTerm.var_inv`, `inj_inv`).
2. **A decided candidate filter**: `candidates c t : List Nat`, the rules whose left-hand side `overlap`s `t`, with
   `Step c x y → PatVal c σ t x.val → ∃ i ∈ candidates c t, ∃ r, c.rules[i]? = some r ∧ ∃ σ', Fires c r σ' x y`.
   Its proof is TH-1's `overlap_sound`, which gains a second caller here. Without it a step in KEVM is a case split over every rule.
3. **Function lemmas**: for a clause, `Eval c f vs r` from a match and the right-hand side's result (the introduction form), and `Eval.functional` to turn it into an equation. These let a `cond` be simplified.

**What `Surface.lean` must generate**: the rule and clause data lemmas it generates now, each under a stable name. Nothing per rule beyond them: the per-state work (which rules, which cover) is the symbolic executor's output, checked against the library's theorems. This keeps the generator's size linear in the definition and independent of the proofs done over it.

Typed surface terms (a Lean inductive per sort, so that states print as K terms) are a presentation over `GroundTerm` and do not change any statement here; they are not part of SY-1.

## 5. Priorities

`Fires` carries `NotApplies` for the rules of smaller priority. A symbolic step by a rule that has such competitors must show they do not apply on φ: by the candidate filter when their left-hand sides cannot match, and as a side condition otherwise. A cover may split φ by a competitor's `requires`.

## 6. Found by SY-1a and SY-1b

- **A state's `term` is a pattern, not a right-hand side.** `PatVal` gives a function call no value, so a rule's right-hand side that calls a function denotes nothing as a `term`. The state after such a rule has a fresh variable in the call's place and `cond` saying the call evaluates to it. A symbolic executor must produce states in that form.
- **A constructor pattern matches exactly its instance** (`PatVal.iff_inst`): this, not head-by-head inversion, is what makes a match against an unknown value usable by `simp`.
- **Inverting a function call** needs `Eval.functional` for clauses with a `requires`; until TH-3 lands only clauses without one invert.
