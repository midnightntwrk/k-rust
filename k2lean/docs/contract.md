# What a generated library promises, and what an optimization loop may change

This note states the principle every design decision in k2lean is judged by, and how each part of a generated library relates to it.
The principle is Sebastien's (2026-10-22, restated 2026-10-28); the layers and the consequences below are derived from it.
A ticket or design note that weighs options should say which layer each option lives in.
Its companion is `design.md` §3, "What a generator knows": which facts the generator states from K's constructs and which a user writes as K functions; both end up in the specification layer below.

## 1. The goal

k2lean does not promise the most efficient Lean: a construction general enough for every K definition cannot also be the fastest for each one.
It promises a library whose definitions and theorem statements encode the user's K definition faithfully, and whose proofs Lean's kernel checks.
Efficiency is then the job of an optimization loop run after generation ("autoresearch"), in the user's project:
- an agent, unattended, changes a proof, or writes a faster function with a proof that it equals the generated one;
- the build is the evaluator: the kernel accepts the proof of the unchanged statement or rejects it, and the axiom guard rejects `sorry`, `native_decide` and new axioms;
- a cost metric (heartbeats, build time, memory, or an implementation's run time) decides whether the change is kept or reverted.

Lean makes the loop safe in a way few targets are.
Correctness is a yes-or-no answer the agent cannot game while the statements are fixed, so nobody has to review whether an optimized proof is right: an optimization is accepted "without fear".
What the loop cannot do is make the statements faithful: they come from the user's K definition, which is correct by assumption, through the generator.

So k2lean emits two things:
- **the evaluator:** the definitions and the statements, faithful to K and frozen;
- **a baseline:** proofs that build, and open obligations, which are slots where "find any proof" is the goal.

Performance after that is the loop's.

So when a choice trades generality or faithfulness against cost, take the general, faithful construction if the cost lies in a layer that can be optimized later (§2, the checked and derived layers).
Weigh the cost only when it lies in the specification layer, which cannot be optimized after generation.

## 2. The three layers of a generated library

| layer | what it holds | why it can be relied on | who may change it, and how |
|---|---|---|---|
| **Specification** | the term types (`Terms`); the functions (`Functions`); the hook models of `KPrelude` (`Int`, `Bytes`, the `Map`/`Set` carriers and their hooks, …); the parameters `class Hooks`; `Step` and `App` (`Rules`); `init`; and the statement of every generated theorem, its premises included (an open obligation's `def ….statement : Prop` too) | it is what the generator writes from the KORE: faithful to K by the argument of `design.md` §2 and by the differential tests against krust and K's LLVM backend (goldens, traces, case results); no Lean proof can check that it is the user's K | by regenerating from the K definition: a hand edit would make it something other than the user's K; in k2lean, a change to what the generator writes is a design decision recorded in `design.md` |
| **Checked** | every proof: the generated ones, the tactics and lemmas of `KPrelude`, termination proofs and measures, heartbeat budgets, the split of a module into parts | the kernel checks each proof against its statement; the axiom guard (`#k2l_assert_axioms`) admits only `propext`, `Classical.choice` and `Quot.sound`, which rules out `sorry` and `native_decide` | anyone, freely, including a user editing the generated proofs in their own project: the worst outcome is a proof that does not build |
| **Derived** | definitions tied to the specification by a proved theorem: the executable `step`, `successors` and `run` (tied to `Step` by `Adequacy`); a faster function proved equal to a generated one (`@[csimp]`); views over the term family | the tying theorem, checked like any proof | anyone, provided the tying theorem is proved again |

## 3. What follows

1. **A cost in the checked layer is no reason to choose a less general specification.**
   Proofs on the arity universe cost two to four times those on the per-sort one (`design.md` §2.1), and SimpleRel's `comm_fn_4` takes 771 s.
   Both are proof costs, which later work can bring down.
2. **A cost in the specification layer is real.**
   The specification can be replaced only with an equivalence proof: for `Step`, a bisimulation between two relations, which is much harder than the proofs it would speed up.
   Examples of such costs are the elaboration time of `Terms`, and the shape of `Step` (heating and cooling steps that every program proof walks through).
   Another is the choice of term encoding: the per-sort encoding of KEVM does not build at all (`design.md` §2.1).
   So the specification is chosen for four things, all up front: faithfulness, generality (every K definition, up to KEVM's and KMIR's size), proof-friendliness (its shape is fixed once generated), and build cost.
3. **A convenience the specification lacks comes back as a derived view, not as a second specification.**
   Plain `cases` and `injEq` per sort are views over the arity family, proved from it.
   Two encodings would be two specifications to keep faithful and in step.
   The same holds for readable notation, and for a fast interpreter.
4. **A statement is specification.**
   A proof must not change the statement it proves: no dropped or added premise, no specialization, no weaker conclusion.
   An agent that cannot prove a statement reports it as open; it never restates it.
   Changing a statement is a generator decision recorded in `design.md`.
   Collection carriers and the `WF` premise are a worked case (`design.md` §8):
   - a premise is part of what the statement says;
   - a function proved equal to a generated one only at well-formed values can replace it in statements about K values;
   - it cannot replace it in the theorems that quantify over every carrier value.
5. **"Generated code nobody edits" (G1) is a requirement on the generator, not on users.**
   The generator must reach the guarantees alone: for k2lean's own libraries and benchmarks (the gate, KEVM, KMIR), a fix goes into the generator or the prelude, never into a generated file, since those libraries measure the generator.
   A user's library is generated into the user's project, and the loop edits its proofs there: that is where an optimization of one library lives.
   When the K definition changes, the library is regenerated (a new evaluator and baseline) and the loop runs again.
   An optimization general enough to help every library is worth bringing back into the generator or the prelude.
6. **Agents changing a library are assumed fallible, not malicious.**
   The loop has to know mechanically what is frozen, because nobody reads each change; that is about making accept or reject automatic and catching an accidental edit of the evaluator, not about defending against an attacker.
   The checks are designed to catch mistakes:
   - the kernel;
   - the axiom guard;
   - the gate's hashes of generated files, so that a moved statement is noticed and explained;
   - the differential tests.

   Nothing defends against deliberate subversion.
   An `instance : Hooks` that returns a value no K hook would return is accepted.
   `@[implemented_by]` replaces compiled code without a proof, so it is trusted rather than checked, and k2lean uses none.

## 4. Where each concept sits

| concept | layer | consequence |
|---|---|---|
| the term encoding (arity-indexed family) | specification | chosen because it builds at every size; per-sort ergonomics come back as derived views (§3.3) |
| `Map`/`Set` carriers and the `WF` premise | specification | `design.md` §8: the carriers keep their values that are not K values; equality to a generated function at well-formed values only is not a drop-in replacement |
| the hook models in `KPrelude` | specification | checked against K by the differential tests; the laws K states of them are theorems (`HookLaws`) |
| `class Hooks` (hooks with no model, functions with no equations) | specification, unconstrained | an instance is the user's assumption, outside what k2lean checks |
| open obligations | a statement with no proof yet | closing one is checked-layer work; restating it is not closing it |
| tactics, heartbeat budgets, module parts | checked | tune freely; the gate's counts say whether a change loses a proof |
| termination | the function is specification; its measure and proof are checked | a hand proof only where K itself diverges, and then a divergence theorem, which is a statement |
| determinism and its overlap list | the list is part of the statement; the witnesses and disjointness proofs are checked | a witnessed overlap is a fact about K, not a gap |
| `step`, `run`, a fast interpreter | derived | welcome when proved equal; not a goal of the generator |
| goal printing (`KPrelude.Delab`, `#k2l_check_delab`) | presentation of the specification | the check proves that what is printed is the definition, which keeps the specification reviewable |
| differential tests | evidence for the specification | the only check that the specification is the user's K |
| the gate's hashes of generated files | guard on the specification and on the generated proofs | a moved hash is a change to explain |

## 5. The output as a loop target

What makes a generated library a good target for the loop, and where k2lean stands (2026-10-28):

| need | why the loop needs it | today |
|---|---|---|
| the frozen part delimited, with a cheap check that it did not move | accept or reject is automatic, and an edit that changes a statement by accident is rejected | statements sit next to their proofs in the same generated files; only an open obligation has a separate `def ….statement : Prop`. A statements module compared with a fresh regeneration (hash), with proof modules free, would give the check |
| small search units | one experiment should rebuild one theorem or one function, not KEVM's whole `Equations`; iteration speed decides how much the loop explores | `Equations` is split into parts by weight (`gen --equations-part-weight`), and each proof has its own heartbeat budget; other modules (`Determinism`, relate's commutation lemmas) are one unit each |
| a metric that does not depend on the machine's load | wall time on a shared, saturated host varies too much to compare two experiments | heartbeats count allocations and do not depend on load; they are measured per module by hand (`lean -j1 -DElab.async=false`, `design.md` §2.1), not per declaration, and no harness reports them |
| a baseline that builds | the loop improves something that works; an open obligation is a slot to fill | every library builds with its open obligations listed (`open-obligations.txt`) |
| a reference for each derived definition | a faster implementation is accepted by a proof that it equals the generated definition (`fast = spec`, `@[csimp]`) | the generated definitions are the references; `step` is tied to `Step` by `Adequacy` |
