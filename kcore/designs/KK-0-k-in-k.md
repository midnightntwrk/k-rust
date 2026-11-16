# KK-0: K in K, and the fixed point

State: design item, written 2026-11-12 by Fable. Nothing here is compiled.
It refines milestone M4 of `ROADMAP.md` and the goals `G-dogfood` and `G-specialization` of `goals.toml`; it does not reopen D4 (the hand-written Lean step is the bridge to matching logic, K-in-K is a candidate proved equal to it).

## 1. What "K in K" is here

A K definition `KK` whose configuration holds an encoded definition and an encoded configuration of that definition, and whose rules take the encoded configuration to its successors.
The reader turns `KK`'s KORE into a `KCore.Definition` like any other definition, so `KK` gets `wf`, its named obligations, `sound` and `complete` from the library with no special case.

kink (`kink/`) is the mutation-testing tool, not this definition. `KK` is the subject kink would be run on.

## 2. The statement

Let `kk : Definition` be the reader's result on `KK`'s KORE, `encDef : Semantics → GroundTerm` and `enc : GroundTerm → GroundTerm` the encodings (Lean functions), and `load D t`, `done D t` the two shapes of `kk`'s configuration: about to take one object step, and having taken it.

```lean
theorem kk_step (d : Definition) (hwf : wf d = true) (hob : Obligations d) (x y : Config d.sem) :
    Step d.sem x y ↔ RunsTo kk.sem (load (encDef d.sem) (enc x.val)) (done (encDef d.sem) (enc y.val))
```

`RunsTo a b`: `b` is reached from `a` by `kk`'s `Step` through configurations that are not of the `done` shape.

This is `StepEquiv` for a candidate that is itself a K definition.
The fixed point is the instance `d := kk`: `KK`, read by the kernel, describes the kernel's reading of `KK`.

What it shows: the kernel's meaning of K can be written in K, and the two agree on every well-formed definition.
What it does not show: that this meaning is the right one. A wrong reading of priorities written consistently on both sides is also a fixed point. That question stays with `sound`, `complete` and the differentials.

## 3. Constraints the kernel puts on how `KK` is written

These follow from statements already proved; they decide the shape of `KK` before any line of it is written.

1. **Object evaluation is done by rules, not by functions.**
   `Obligations kk` asks that every function of `kk` terminates on well-sorted arguments.
   A `KK` function `eval(D, f, args)` does not: an object function may not terminate.
   So function calls of the object definition are evaluated by `KK` rewrite rules on an evaluation stack inside the configuration, and an object evaluation that has no result is a `KK` run that never reaches `done`.
   `KK`'s own functions are the terminating ones: lookup in the encoded definition, substitution, syntactic matching of constructor patterns, sort checks.

2. **Negative premises are run to a result.**
   `Step.rule` asks that no rule of a smaller priority applies (`NotApplies`), and `Eval.clause` that every clause of a smaller priority fails (`Fails`). Both are positive statements: for every match of the competitor there is a derivation of its `requires` whose result is not `true` (`RuleReqFails`, `ReqFails`: `v ≠ some (bool true)`).
   Two outcomes must be kept apart. A `requires` whose result is *undefined* (`none`: a hook off its domain, a function where every clause fails) counts exactly as `false`: the competitor does not apply and does not block. A `requires` with *no derivation* (an evaluation that does not terminate) is neither `true` nor a failure: `NotApplies` cannot be shown, and no rule of a larger priority number steps.
   `KK` therefore evaluates the `requires` of each competitor of a smaller priority to a result before it commits. The result `true` blocks, whether or not that competitor's right side has a value. The result `false` or undefined does not block. A `KK` evaluation of it that does not finish gives no step, as in `Step`.
   Competitors of the same or a larger priority number are not premises of the step: `Step.rule` asks nothing of them, so `KK` must not make a step depend on their evaluation finishing.

3. **`KK` is not deterministic, and must not be made so.**
   `Step` is a relation: several rules of one priority, or several matches of one rule, each give a successor.
   `KK` chooses a rule and a match by overlapping rules of its own; `kk_step` is stated with `RunsTo`, not with a function.
   Within one priority the evaluator may not commit to the first candidate (`KN-0` §7); `KK` has the same obligation. A candidate whose `requires` has the result undefined is skipped, at the same priority and at a smaller one alike. A `requires` with no derivation matters only for a competitor of a smaller priority, where no step is taken (point 2); at the same priority `Step` asks nothing of the other candidates.

4. **Hooks of the object definition are `KK`'s own hooks.**
   An object call of `+Int` is a `KK` rule whose right-hand side calls `+Int`. `KK` covers the hook domains it imports and no others, so `kk_step` is stated for the definitions whose hooks `KK` imports.

5. **Symbols and sorts are numbers.**
   `Semantics` already numbers them; `encDef` writes the numbers as `Int` literals, so `KK` needs equality on `Int` and no string domain.

## 4. Stages

| Stage | Object definitions covered | What `KK` itself uses | Depends on |
|---|---|---|---|
| KK-a | constructors, subsorts, functions with priorities and `requires`, rules with priorities and `requires`, Bool and Int hooks; no collections | constructors (lists as cons/nil), functions with priorities, Int equality | nothing new: k-rust's KORE of this fragment is read and tied today |
| KK-b | Map, Set, List patterns | the same; matching modulo the collection axioms written as rules that choose a split | MX-1 (so `kk` and the executable matcher can be compared by running) |
| KK-c | every hook domain the registry has | — | KN-4 |
| KK-self | `d := kk` | — | `KK` written inside the fragment its own stage covers |

KK-a is the spike `Q-crux-proof-cost` already names. KK-self needs `KK` to stay inside what it interprets, which is why point 3.1 matters: with evaluation by rules, `KK` at stage a uses nothing outside stage a.

## 5. Written in K or in KRS

In KRS, as `ROADMAP.md` M4 says, emitted to K and kompiled by k-rust; the reader takes that KORE.
kink's decision M1 (mutations of a KRS specification are K patches of its emitted K) then applies as is.
The Lean side does not care which source produced the KORE.

## 6. What the project's tools do with it

- **kink on `KK`.** A mutant of `KK` is a wrong K semantics. A corpus of (definition, configuration, expected successors) cases that kills the mutants is a test suite for *K engines*, and k-rust's backend is run against it natively: for each case, the backend's successors of the configuration under the definition must be the expected ones. Expected successors come from the Lean evaluator (`Exec.successorsN`, proved equal to `Step`), not from k-rust running `KK`, so a backend bug is not on both sides (`goals.toml`, the oracle question).
- **k2lean.** `G-specialization`: a per-definition view is the specialization of `KK` to one definition.
- **This formalization.** `KK` is the largest function-heavy definition we would have, with priorities, overlapping rules and deep recursion in one place; it exercises `wf`, the obligation deciders and the generator harder than any example does.

## 7. Cost and risk

- `kk_step`'s proof is a simulation in both directions between an inductive relation and runs of an interpreter with an explicit stack. The backward direction (a `KK` run that reaches `done` corresponds to one `Step`) needs an invariant on every intermediate `KK` configuration. This is the expensive part; KK-a measures it.
- `wf kk` must be decided by the kernel under the memory cap. One `wf` conjunct already reached the cap on kink-imp.
- If `KK` needs a feature `wf` refuses, the choice is to rewrite `KK` or to widen `wf`, and the second is exactly the pressure that should come from a real definition.

## 8. First ticket (KK-1, not dispatched)

Write `KK` for stage a in KRS; emit, read and tie it; record `wf kk` and the obligation lists; run it against `Exec.successorsN` on peano, prio and fprio configurations by evaluation (no proof yet).
Done when the runs agree or each difference is explained, and the size of `kk` and the cost of `wf kk` are recorded.
`kk_step` for stage a is the ticket after it, sized by KK-1's numbers.

## 9. Open

1. Whether `load`/`done` hold the definition as data in the configuration (one `kk` for every `d`) or `KK` is generated per definition. Section 2 assumes the first; the second is `G-specialization` and comes later.
2. Whether `RunsTo` should also bound the object step's *failure*: `Step` having no successor at `x` corresponds to `KK` reaching a `stuck` shape, or to `KK` diverging when a competitor's `requires` has no value. `Complete` suggests a second theorem about the `stuck` shape.
3. Whether the encoding is checked by a decoder with a round-trip lemma (as the k2lean bridge plans) or `enc` alone suffices; `kk_step` as stated needs only injectivity of `enc`.
