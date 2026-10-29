# k2lean's product: why it exists, for whom, and what it must do

This note holds the product decisions and requirements that steer k2lean's work, with their reasons.
It is not final: the project still learns as it goes, so each item is dated and changed in place, not appended to.
Each item says where it comes from:
- **decided**: Sebastien's decision, with its date;
- **established**: practice the project has kept and measured, with its record;
- **proposed**: written down by core on 2026-10-28 from what the project has learned, awaiting Sebastien's review.

Companions:
- [`contract.md`](contract.md): what a generated library promises, and what an optimization loop may change in it;
- [`direction.md`](direction.md): the map these decisions fit in, and the directions beyond what exists; a direction moves here when Sebastien decides it;
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

## 2. Who it is for (decided 2026-10-28)

- **Primary: the author of a K semantics** (a language designer, RV, the K community), who wants meta-theorems about their language.
  The planned users are mostly languages and virtual machines of blockchains: Starstream is one of many, with the EVM and others to come.
  They need cryptography and proof systems next to their semantics, which makes importing and being imported a requirement (§3.6).
- **Served by an optimization loop** (`contract.md` §1), which makes a generated library's proofs cheaper without changing what it says.
- Also served: a program verifier who wants K claims as kernel-checked theorems, and a Lean developer who imports a generated semantics.

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
7. **A statement weaker than K's original, or than the property's usual form where K states none, says so.** Examples: soundness excludes stuck states, not undefined ones; a claim under `--assume-invariant`; noninterference and confluence, which K does not state, are termination-insensitive, and confluence holds with its open joins as premises. Each is listed in `design.md` §8.1 (established 2026-10-28).
   An option that chooses which theorem is stated is part of the specification (`contract.md` §2).

### 3.3 Generality
8. **Every K definition, up to KEVM's and KMIR's size.** A feature is justified by what a K construct means, and tested on a second definition (decided 2026-10-28, §6). Soundness asks for two validation definitions per feature, and that is the bar for every area (proposed).
9. **One encoding.** The arity-indexed term family is the only specification of terms. A convenience it lacks comes back as a view proved from it (`contract.md` §3.3; the per-sort encoding was retired on 2026-10-28, ticket CT-1).

### 3.4 Automation
10. **Push-button where the proof is generic.** Hand-written proofs are for cases the tactics do not close, and a hand case proves the generated statement by name (established; §6).
11. **A case that was automatic stays automatic, and no count gets worse.** These are the gate's ratchet: open sets only shrink, and proved counts never drop (established, `rules.md` and the gate).
12. **Hand proofs survive unrelated edits.** Rule names are stable. An edit to one K rule reopens that rule's cases and no other, and `k2lean diff` names the hand references to revisit (established; making it a requirement is proposed).

### 3.5 Cost
13. **The specification's build cost counts. A proof's cost is the optimization loop's** (decided 2026-10-22, restated 2026-10-28; `contract.md` §1 and §3). There is no fixed bar: a specification's cost is judged from first principles, case by case (decided 2026-10-28). This supersedes the earlier wording "build cost of the definitions and proofs matters".
14. **Cost is measured so that two runs compare.** Heartbeats count allocations and do not depend on load: `k2l-eval FILE MODULE` reports them per declaration, the loop's metric (`contract.md` §5). Memory is measured per module under a cap (the KEVM and KMIR pipelines record each module's peak). Wall time on the shared host does not compare, nor does a whole gate's peak (established 2026-10-29, CT-4).

### 3.6 Specification in Lean, and other Lean libraries
15. **A user can state in Lean what K cannot express, as a first-class input** (decided 2026-10-28: "K can't do [everything] so we need this for most projects").
    Examples: properties about cryptographic primitives or proof systems, and properties of whole runs.
    Such a statement is specification the user writes (`contract.md` §2): kept in a module of its own, apart from proofs, and frozen for the optimization loop.
    A fact that a K function of the definition can express is still written in K, because generators can then state and prove things from it (§6; noninterference's store predicates are such facts, C's NI-4).
16. **A generated library is a Lean package that other projects import, and that can import Lean libraries itself** (decided 2026-10-28: required "for almost all blockchain constructs as they need to import proof systems or cryptography").
    This is the main use of `class Hooks`: a hash function or a proof system's verifier is a parameter of the semantics, instantiated from a Lean library.
    Gap today: the quick start copies the prelude into the user's tree by relative path, and there is no packaging, versioning or toolchain story for using a library next to others (ticket PKG-1).

## 4. Success criteria

- **G1**, the current goal for large definitions (set 2026-10-24 for the scale work), is KEVM and KMIR as libraries with every guarantee kimp, the small IMP definition, has:
  - no axiom and no `sorry`;
  - determinism exact both ways (every pair the theorem treats as disjoint is proved disjoint, every listed overlap witnessed);
  - no hand termination proof except where K itself diverges, with a divergence theorem there;
  - generated code nobody edits.

  The original wording also says "no open obligation". Some of K's own equations are false in its semantics (§7), so no proof of them can exist; the goal is that every obligation is proved, or refuted by a counterexample (restated 2026-10-28).
- **Per area:** each meta-theorem kind's exit is on its readiness page. Soundness is done for a feature when two validation definitions prove it with hand Lean only for proof cases.
- **UTXO-based smart contracts** (Sebastien, 2026-10-28; a direction, not yet a criterion): proving properties of a UTXO smart-contract system whose semantics is written in K, such as Starstream's coroutines over a UTXO ledger.
  k-rust and k2lean provide the features such systems need; each system's own codebase owns its semantics and its proofs (Sebastien, 2026-10-29). k2lean's fixtures reproduce the shapes those semantics take, not the systems themselves.
  Several of its process-level obligations are k2lean's theorem kinds:
  - a transaction is a finite DAG of UTXO transitions, executed in some order the DAG allows; every such order gives the same ledger effects, under a legality hypothesis: `confluence`, a property of the interleaving;
  - a suspended continuation resumed at most once: an invariant;
  - the properties of one contract over the ways its UTXO can evolve (its invariants and specifications, written by the contract's author): invariants and `claims`, a property of the contract, not of the interleaving. This is K's established use in auditing Solidity contracts.

  The coordination script names as inputs every UTXO a transaction may touch, but which path the execution takes is known only once it runs (a ZK prover follows the trace of a run made beforehand without ZK).
  Proofs are made at several units, depending on how far one zooms in: a folding step, a segment from one yield or raised effect to the next, a transaction, a change to the ledger's UTXO set (Sebastien, 2026-10-29).

  A coroutine against the state machine it compiles to, or Starstream against Wasm, is a certified-compiler question, a separate effort not on this roadmap (Sebastien, 2026-10-29); `relate` and `refine` cover a definition against an optimized variant of itself.

  This is why confluence is in scope: languages that are nondeterministic for their own sake (SIMPLE's threads) matter less for blockchains.
  First result (2026-10-29): the fixture `utxo` (coroutines over a ledger, ids derived from content, outputs spent by their owner) is proved confluent with no premise (`demos/UtxoConf`, design.md §3.6); a legality hypothesis, temporal statements and a fixture with the handoff shape of coroutines (a resume makes the resumer wait until the child yields, so a step of the interleaving is a whole segment) are still ahead.
  It is likely not sufficient: protocol properties (session types) need temporal statements beyond reachability and confluence, and whether Lean is the right tool for those is open (§8).
- **What confluence is for** (direction agreed by Sebastien 2026-10-29; the items below proposed by C the same day):
  - *Its reusable result is which steps commute, not only that final states are unique.* Every confluence theorem rests on generic lemmas that two steps can be swapped: by their footprints, by the bindings of a map cell they change, by their priorities. `terminal_unique` is the first consumer of them.
  - *The second consumer is independence: which steps do not affect each other, so that their proofs can be made in parallel.* A Starstream transaction is a finite DAG, so everything in it runs and there is no fairness question (Sebastien, 2026-10-29); `terminal_unique` already says that every order gives the same result. Proofs made separately need commutation in both directions (neither step changes whether the other is enabled or what it does); the views prove only the forward direction today (CNF-15). A step here is the unit of the layer being stated, and there are two levels, each its own definition:
    - *inside one interleaving:* the segments of different UTXOs (each from one yield or raised effect to the next) that read nothing the others write;
    - *across transactions:* transactions whose input UTXOs are disjoint, at the ledger's level, as a parallel executor relies on (Block-STM, Sui's objects).
  - *Atomicity between yields is part of the model, not a theorem to prove.* From the coordination script's view, a coroutine always runs from one yield or raised effect to the next as one step, so the interleaving layer's step is a whole segment and nothing interleaves inside it. Lipton's and partial-order reduction (proving that fine-grained steps can be grouped or reordered) apply only to a definition written at a finer grain than its atomic unit; a definition whose interleaving step is already a segment, as Starstream's model would be, does not need them.
    An unbounded program is a resume repeated forever; whether such programs go through Starstream's constructs (recursion, interleaving several programs) or through Nightstream's folding directly (RISC-V, Wasm, SM83) is Starstream's design question, not k2lean's.
  - *Boundaries with other approaches.* Ordering and protocol properties (a child is eventually resumed; a spend comes after its create) are temporal statements, not part of confluence. Facts such as "no output is spent twice" are invariants, which confluence takes as its program hypothesis. A session-typed protocol layer may give confluence of well-typed programs from its soundness theorem (the `soundness` kind) instead of from a commutation proof per definition, so confluence should not grow toward protocols.
  - *Secondary use: languages nondeterministic for their own sake* (SIMPLE's threads, strict operators whose arguments have effects). They keep working and test generality (§3.3), but do not drive features: joins of several steps and equality up to a renaming of fresh values wait for a consumer.
  - *One tool.* Confluence has two modes today, one obligation per pair of rules and one view per rule (`--threads`), with options the other lacks. The direction is one pipeline: the views for what is generic, then each remaining pair as an obligation of its own, closed by a generic attempt, by a hand proof, or left open as a premise, as equations are (`open`, `hand`, `refuted`; §3.2).
- **Beyond k2lean:** the EVM goals (KEVM against the Ethereum tests; KEVM against another EVM model) are claims about one semantics, so they belong to an EVM project, which G1 enables (§6).

## 5. Non-goals

- A fast generated interpreter. A faster implementation is derived and proved equal when someone needs it (decided 2026-10-22; `contract.md` §4).
- Replacing k-rust's engine with Lean automation, and selling k2lean on speed (established in the product note of 2026-10-23, from the measurements of 2026-10-22).
- Trust and failure-mode arguments as a pitch: "the TCB is ours to manage", "people assume it works" (decided 2026-10-21).
- Lean projects that only confirm an argument to ourselves (decided 2026-10-21: "low value"); concrete examples for documentation are welcome.
- Mutation testing on the Lean side: a Lean mutant costs about 10 times the time and 12 times the memory of a krust one, so kink stays on K (established, measured 2026-10-22).
- Reading KRS's own representation, and asking KRS for typed collections everywhere: little to win (recommended 2026-10-23, not decided; revisited only if a measured gain appears).
- Fixing definitions we do not own. A finding (an overlap, a false equation, a function declared total that diverges) is noted, and fixed where we own a port of the definition, such as a local KRS port (decided 2026-10-23 for KEVM's overlaps, 2026-10-28 in general).

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
- Hand-written Lean is for proof cases the tactics do not close, and for properties K cannot express (§3.6); a language fact that a K function can express is written in K.
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

## 8. Open questions for Sebastien

Answered 2026-10-28: the primary user (§2), Lean specification (§3.6), importing and being imported (§3.6), the build-cost bar (§3.5: none fixed, judged from first principles), findings in definitions we do not own (§5).
Still open:
1. Are these still goals, and in which order?
   - certifying krust's proofs by replaying them in Lean (a prototype exists: `claims replay`);
   - incremental regeneration that keeps hand and loop proofs;
   - notation from the K grammar, so that statements read like the K source.
2. For UTXO smart contracts (§4): which temporal statements over runs (protocol conformance, session types) k2lean should state, and whether Lean is the right tool for them.
3. For UTXO smart contracts (§4), what "one of them is illegal" means: a predicate on configurations that every step preserves (an invariant, as `claims --assume-invariant` takes one), or a predicate on steps that removes the illegal ones from the relation (which also changes which configurations are terminal). The first is the one confluence can take today; Starstream's requirements decide whether the second is needed.
   It is the same question as soundness's (B): which configurations are acceptable endings, under a well-formedness property the author states. The invariant reading is that hypothesis; the step-restriction reading changes which configurations are terminal, which is what the acceptable endings name. One answer serves both (agreed by B and C, 2026-10-29).
