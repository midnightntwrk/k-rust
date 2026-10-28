# k2lean's product: why it exists, for whom, and what it must do

This note holds the product decisions and requirements that steer k2lean's work, with their reasons.
It is not final: the project still learns as it goes, so each item is dated and changed in place, not appended to.
Each item says where it comes from:
- **decided**: Sebastien's decision, with its date;
- **established**: practice the project has kept and measured, with its record;
- **proposed**: written down by core on 2026-10-28 from what the project has learned, awaiting Sebastien's review.

Companions:
- [`contract.md`](contract.md): what a generated library promises, and what an optimization loop may change in it;
- `design.md` §3, "What a generator knows": what each generator states from K, and what a user writes.

The records behind this note are the lab notebook (`draft-personal/matching-logic-vs-dtt/`): its decisions are summarized here, and its history is not imported (decided 2026-10-24).

## 1. Why k2lean exists (proposed)

K is a good place to write and run a language's semantics, and k-rust's engine is where K stays ahead.
What K cannot do is state and prove facts *about* a semantics:
- that it is deterministic, up to its listed overlaps;
- that a property holds after every step of every program;
- that a type system is sound for it;
- that two definitions of a language agree, or that one refines the other;
- that it is confluent modulo scheduling, or noninterferent.

k2lean turns a K definition into a Lean library where those facts are theorems, generated and proved push-button where the proof is generic, and checked by Lean's kernel.
K, or KRS, stays the front end where the semantics is written and run.
Lean is the generated back end for meta-level proofs, and for K claims that need a kernel-checked proof.

Speed is not the argument: compiled Lean already runs a semantics 2 to 4 times faster than K's LLVM backend (2026-10-22), and the generated interpreter is not optimized for it (§5).

## 2. Who it is for (open: §8, question 1)

The work so far implies four users. None of them has been chosen as the primary one:
- **the author of a K semantics** (a language designer, RV, the K community), who wants meta-theorems about their language without writing Lean;
- **a program verifier**, who wants K claims as kernel-checked theorems;
- **a Lean developer**, who imports a generated semantics as a dependency next to Mathlib and the Lean ecosystem;
- **an optimization loop** (`contract.md` §1), which makes a generated library's proofs cheaper without changing what it says.

## 3. Requirements

### 3.1 Faithfulness
1. **The library means what the K definition means.** Definitions and statements come from the KORE, by the argument of `design.md` §2. The differential tests against krust and K's LLVM backend are the evidence: they are the only check that the specification is the user's K (established; `contract.md` §2).
2. **No axioms; hooks are real definitions.** Only Lean's three axioms, checked by the axiom guard. A hook K leaves to the implementation is a parameter (`class Hooks`), and every theorem holds for every instance (established since the first generator, 2026-10-22; an earlier generator's prelude proved `False`).
3. **Refuse rather than approximate.** A construct the generator cannot state faithfully is an error with a message, never an approximation (established; §6).
4. **A Lean value that is no K value is not a K fact.** Collection carriers hold lists that are no K value, so a statement about K values carries the `WF` premise (decided 2026-10-28; `design.md` §8).

### 3.2 Every exception is a checked fact
5. **What a theorem leaves out is listed, and each entry is checked** (proposed; the practice of every area):
   - an overlap of two rules has a witness configuration;
   - a function K declares total but that diverges has a divergence theorem;
   - an equation that is false in the model has a counterexample;
   - a K claim that is false has a refutation.
6. **"Open" means unproved, not false.** An open obligation is never assumed. An obligation refuted by a counterexample is reported as refuted, apart from the open ones (proposed; today refutations are written case by case, as for `countAllOccurrences` equation 2).
7. **A statement weaker than K's original says so.** Examples: soundness excludes stuck states, not undefined ones; a claim under `--assume-invariant`; noninterference that ignores termination; a confluence proof with joins left as hypotheses. Each is listed in `design.md` §8 (proposed; today they are spread through `design.md` §3).
   An option that chooses which theorem is stated is part of the specification (`contract.md` §2). An option that weakens a statement only for testing is internal, not a user option (proposed; §8, question 6).

### 3.3 Generality
8. **Every K definition, up to KEVM's and KMIR's size.** A feature is justified by what a K construct means, and tested on a second definition (decided 2026-10-28, §6). Soundness asks for two validation definitions per feature, and that is the bar for every area (proposed).
9. **One encoding.** The arity-indexed term family is the only specification of terms. A convenience it lacks comes back as a view proved from it (`contract.md` §3.3; retiring the per-sort encoding awaits Sebastien's go, ticket CT-1).

### 3.4 Automation
10. **Push-button where the proof is generic.** Hand-written Lean is for proof cases the tactics do not close, and a hand case proves the generated statement by name (established; §6).
11. **A case that was automatic stays automatic, and no count gets worse.** These are the gate's ratchet: open sets only shrink, and proved counts never drop (established, `rules.md` and the gate).
12. **Hand proofs survive unrelated edits.** Rule names are stable. An edit to one K rule reopens that rule's cases and no other, and `k2lean diff` names the hand references to revisit (established; making it a requirement is proposed).

### 3.5 Cost
13. **The specification's build cost counts. A proof's cost is the optimization loop's** (decided 2026-10-22, restated 2026-10-28; `contract.md` §1 and §3). This supersedes the earlier wording "build cost of the definitions and proofs matters".
14. **Cost is measured so that two runs compare.** Heartbeats, which count allocations and do not depend on load, come with peak memory per module under a cap. Wall time on the shared host does not compare, nor does a whole gate's peak (proposed; ticket CT-4).

## 4. Success criteria

- **G1:** KEVM and KMIR as libraries with every guarantee kimp has:
  - no axiom and no `sorry`;
  - determinism exact both ways (every pair the theorem treats as disjoint is proved disjoint, every listed overlap witnessed);
  - no hand termination proof except where K itself diverges, with a divergence theorem there;
  - generated code nobody edits.

  The original wording also says "no open obligation" (orchestrator's plan, 2026-10-24). Since some of K's own equations are false in its semantics, it should read "every obligation proved, or refuted by a counterexample" (proposed; §8, question 4).
- **Per area:** each meta-theorem kind's exit is on its readiness page. Soundness is done for a feature when two validation definitions prove it with hand Lean only for proof cases.
- **Beyond k2lean:** the EVM goals (KEVM against the Ethereum tests; KEVM against another EVM model) are claims about one semantics, so they belong to an EVM project, which G1 enables (§6).

## 5. Non-goals

- A fast generated interpreter. A faster implementation is derived and proved equal when someone needs it (decided 2026-10-22; `contract.md` §4).
- Replacing k-rust's engine with Lean automation, and selling k2lean on speed (established in the product note of 2026-10-23, from the measurements of 2026-10-22).
- Trust and failure-mode arguments as a pitch: "the TCB is ours to manage", "people assume it works" (decided 2026-10-21).
- Lean projects that only confirm an argument to ourselves (decided 2026-10-21: "low value"); concrete examples for documentation are welcome.
- Mutation testing on the Lean side: a Lean mutant costs about 10 times the time and 12 times the memory of a krust one, so kink stays on K (established, measured 2026-10-22).
- Reading KRS's own representation, and asking KRS for typed collections everywhere: little to win (recommended 2026-10-23, not decided; revisited only if a measured gain appears).
- Reporting a definition's overlaps or bugs upstream as part of this work (decided 2026-10-23 for KEVM's overlaps; the fix belongs to KEVM's KRS port).

## 6. Where work belongs (decided 2026-10-28)

Heuristics, not rules: apply them with judgement, and say on the ticket when a case does not fit.
They decide what gets built where; correctness from first principles (the repository's agent notes) decides how it is justified.

**Which project.**
- k2lean (in k-rust) when K's meaning justifies the feature and a second definition tests it.
- Example material (a demo, a checker, a fixture, a sidecar, an invariant's statement, a divergence proof) when it is a fact of one semantics.
- A project of its own (for KEVM, the EVM work: conformance runs, equivalence with another EVM model) when its purpose is a claim about one semantics.
  A generator feature such a project needs that is general in form but has no consumer outside it is recorded there, and built when a second definition needs it (KEVM's `<wordStack>` statement).

**Inside k2lean: generators know K constructs, not language features.**
A language feature (variables, scopes, functions, exceptions, objects, threads) is a use of K constructs plus facts about how one language uses them.
- The generator handles each K construct from what it means in K: cells, nesting and cell collections, `<k>` with strictness and `KResult`, priorities and `owise`, side conditions, rules that read several cells or several collection elements, hooked sorts (`Map`, `List`, `Set`, `Int`), fresh values, `stream` cells, functions and their partiality.
- The language's facts are written by the user, in K, as functions of a definition: a kind 1 invariant, a type checker, a relation between the checker's typing and the runtime state. The generator proves things about them.
- Hand-written Lean is for proof cases the tactics do not close, not for stating a language's facts.
- To apply it: when a feature's description names a language concept (variable, store, location, frame, scope), find the K constructs under it. They are the generator's; what is left is the user's.
  Example: variables are a typing context the checker threads along `<k>`, `Map` cells, rules that read `<env>` then `<store>`, and fresh locations (K constructs), plus "the environment and the store realize the typing context" (the user's, a K function).
- Warning sign: an option or mechanism named after one definition's shape (`--store-cell`, `--env-item`) or after a language concept is a place where the boundary was crossed. Keep it as a stopgap only until a second definition shows the general form, then replace it.
- Not every K definition fits a generator's input. Say so in `design.md` and refuse with a message rather than stretch a generator. For example, `soundness` reads a checker written as functions, not one written as rewrite rules.

## 7. Learnings that set direction

- **Scale is decided by the specification's encoding, not by proofs.** One Lean type per sort never finished on KEVM (90 min, 17.9 GB), and Lean cannot compile KEVM's 277 injections as constructor fields. The arity family builds both KEVM and KMIR.
- **Stating K's facts finds real bugs.** Among them:
  - in K's own semantics: `countAllOccurrences` equation 2 is false; 6 of KEVM's 22 Set/Map simplifications are false without well-formedness; 11 KMIR functions declared total diverge on a cyclic type table; `senderTxData` diverges at a negative chain id;
  - in the definitions: 79 genuine KEVM overlaps, one of them `DUP(N)`; a difference between kimp and its KRS port;
  - in the tools: a hole in KRS's type check; a krust miscompilation.

  This is part of the product's value (§1), and why every exception is a checked fact (§3.2).
- **Generic machinery keeps replacing hand modules.**
  - ImpTypes' hand Lean went from 674 lines to 100.
  - SimpleEnv, ImpUnroll's relation and the noninterference relation are now generated.
  - Five KEVM termination entries became synthesized measures.

  Language facts written in K as functions are what made this possible (§6).
- **Failing cases cost more than size.**
  - SimpleRel's memory went to failing arms.
  - 19 runaway theorems took 8,174 s of KEVM's equation time.
  - An IMP++ preservation proof took 44 min on the whole configuration and 9.7 s per thread.

  A tactic alternative must close its goal or fail, and a resource limit must leave the case open rather than abort the module (`design.md`).
- **Estimates miss in both directions:** noninterference took under a day against an estimate of two to four. Probe and measure before planning a large change.

## 8. Open questions for Sebastien (2026-10-28)

1. Who is the primary user (§2), and what follows for the feature order?
2. Which of the first product note's ambitions are still goals?
   - certifying krust's proofs by replaying them in Lean (a prototype exists: `claims replay`);
   - the generated semantics as a dependency of other Lean projects;
   - incremental regeneration that keeps hand and loop proofs;
   - notation from the K grammar, so that statements read like the K source.
3. Is specification written in Lean accepted where K cannot express the property, or must every language fact move into K functions (§6)? Cases today: a kind 2 invariant's `P`; noninterference's `lowEq` and `secure`; refine's `X`; confluence's hypothesis `H`.
4. Restate G1's "no open obligation" as "every obligation proved or refuted" (§4)?
5. Should the specification's build cost on KEVM and KMIR have an acceptance bar, now that proof cost is the loop's?
6. Should options that weaken a statement for testing (`--det2-overlap`, `--det2-long-*`) leave the user interface (§3.2, 7)?
7. Should k2lean report what it finds false in a definition upstream, for KMIR's diverging functions and the false `domains.md` equation (KEVM's overlaps: decided no, 2026-10-23)?
