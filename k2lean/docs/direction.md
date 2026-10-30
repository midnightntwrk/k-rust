# k2lean's direction: one definition's theorems, systems of semantics, protocols

Status: written by B on 2026-10-29 from a discussion with Sebastien, reviewed by core and C; Sebastien gave the go-ahead to flesh out and implement it the same day, with §9's recommendations as the working answers.
[`product.md`](product.md) holds the decisions and requirements; this note holds the map they fit in, and the directions beyond what exists.
A direction moves into `product.md` when Sebastien decides it.

Each item is labeled:
- **today**: exists, with where;
- **direction**: worth pursuing, not built, with the experiment that would make it real;
- **open**: a question for Sebastien, collected in §9.

The note is written to stay true for any K author: Starstream is one customer among several (§7), and its examples are marked as such.
k-rust and k2lean provide the features; each consumer's own codebase owns its semantics and its proofs, and k2lean's fixtures reproduce the shapes those semantics take, not the systems (Sebastien, 2026-10-29; `product.md` §4).

## 1. One object, many theorems

A K definition, read in Lean, is a step relation (which configurations can step to which) and the functions its rules call.
Every theorem k2lean states is about one or the other, and the theorems differ in what they talk about:

| What it talks about | The question | k2lean |
|---|---|---|
| One function | Is each of K's equations true in the model? Does each function terminate, or where does it diverge? | **today**: equations proved or refuted, termination measures, divergence theorems (`design.md` §1, §2.2; TERM-1). Most of G1's work |
| One step | Does each state have one successor? Do two steps commute? | **today**: determinism (`design.md` §3.1). Commutation lemmas exist inside the confluence module (§3.6), not yet as a statement other kinds consume (CNF-15) |
| Every reachable state | Does P hold after every step? Is every reachable state finished or able to step? Do programs the checker accepts never go wrong? | **today**: invariants; no stuck states under the author's invariant (`gen --progress`, §3.9), of which type soundness (§3.3) is an instance under the checker's runtime typing (kimp; IMP++, whose threads are a cell map) |
| Whole runs: safety | Does nothing bad ever happen along a run? (a continuation resumed at most once, a spend after its create, messages in protocol order) | **today** only when the configuration already records the history, as an invariant (§5) |
| One program's runs | Does this program reach this state, on all paths or on one? Does it terminate in a value? | **today**: claims (§3.8): `AF` and `EF`, weak all-path and one-path eventually (partial correctness); `Reach` under `--induction`, total correctness |
| Every program's runs: liveness | Does something good eventually happen, for every program? (every run ends; every request to a server is answered; a long-running program keeps making progress) | **today** only in finite executions: every run ends, by a measure every step decreases, composed with a comparison by `KPrelude.Ends` (`handoff`, CNF-22, `design.md` §3.6); nothing under fairness (§5) |
| Two runs | Do two schedules end alike? Do private inputs change public outputs beyond what the program discloses? | **today**: `terminal_unique` (§3.6), proved with no premise for the fixtures `race` and `utxo`, with open joins as premises for SIMPLE; noninterference (§3.7) |
| Two definitions | Does one definition simulate or refine another? | **today** for two definitions of one language whose constructors correspond, by symbol or by sorts and concrete syntax (§3.2, §3.5); `refine` needs an order-preserving translation and no priority ranks (REL-5). Not across languages (§4) |

The rows split in two (Sebastien, 2026-10-29).
All but the last two are properties of one object: a function, a step, a state, or one run.
The last two compare two runs, of one definition or of two: confluence (the runs differ in the order of steps), noninterference (in private data) and `relate`/`refine` (in the definition that runs).
A comparison has the same shape in each kind (`product.md` §4, "Comparing two runs"): what is observed, what varies, and which starting points are legal; and it ends in a theorem, a refutation by two concrete runs, or obligations left open by name.
Comparisons are termination-insensitive: they relate runs that end.
That every run ends is liveness, a property of one run (§5), and not part of any comparison; a theorem that needs both, such as "every order a transaction allows ends, and in the same state", is composed from the two.

The run vocabulary (**today**, since RUN-1, main 498964bf4; `design.md` §3):
- `KPrelude/Paths.lean`: infinite paths (`Paths.Inf`), termination (`Paths.Terminates`), maximal runs (a halting run repeats its last configuration) with `always_iff` and `always_of_preserved`, and `FirstReach`/`Segment` (one or more steps to the first configuration satisfying a predicate, functional under a deterministic relation);
- `Star` (`KPrelude/Invariant.lean`) and `StepsN` (`KPrelude/Run.lean`), where they were, imported by `Paths.lean`;
- `Pending.Chain` (divergence) is `Paths.Inf` of the pending-call function's graph;
- claims keep their own `Avoids`, `Terminates`, `AF`, `EF`, `Plus` and `Reach` (`KClaims/Reach.lean`), which their tactics match by name, with bridges to the prelude's in `KClaims/Paths.lean` (`Reach.iff_star`, `Terminates.iff_paths`).

## 2. What the author states once

Beyond the K definition, an author knows facts about their language that no K construct says.
Several theorem kinds need the same facts, and each takes them in its own form today:

- **Legality, or well-formedness:** which configurations are meaningful.
  Claims take it as `--assume-invariant`, noninterference as its store predicates, soundness as the part of its well-typedness about cells other than `<k>`.
  No stuck states (`gen --progress`) takes it as its `Invariant`: the library's kind 1 invariant, or a kind 2 one in Lean with the flags of claims (`--assume-invariant`, `--invariant-module`, `--invariant-preserved`; `design.md` §3.9).
  Confluence is planned to take it as its program hypothesis (CNF-10); today `--threads` states the hypothesis `True`, and the per-pair mode takes `--hyp` from a hand module.
- **Acceptable endings:** which configurations that cannot step count as finished (halt, trap, exception), as opposed to gaps in the semantics.
  A configuration has no successor in three ways, which the step relation does not tell apart (a rule whose right-hand side is ⊥ counts like a stuck one):
  - *stuck:* no rule applies;
  - *undefined:* a rule applies and its right-hand side is ⊥ (`Outcome.undefined` in `KPrelude/Run.lean`, such as `X /Int 0`);
  - *blocked on a function* defined as a least fixed point that is `none` there: undefined, or divergent.

  Today soundness excludes stuck configurations, not undefined ones (`product.md` §3.2, item 7).
  A no stuck states theorem has to say which of the three it excludes, and can tell them apart only through the matcher's three-valued outcome and the pending-call function; telling divergence from undefinedness at a step is TERM-1c's `pending_sound` (core).
  Soundness reads them off its `Final` predicate, which today also excuses a thread waiting at `join` (IMP++).
  It is the same question as confluence's "one of the schedules is illegal" (`product.md` §8, question 3).
  Confluence itself never reads endings: its terminal configurations are those with no successor, so the answer reaches confluence only if legality restricts the steps, which changes which configurations are terminal.
- **What is observable:** what two runs or two definitions are compared on: the public outputs (noninterference), the configuration up to a translation (relate).
  Confluence compares whole final configurations today; its `obs_confluent` follows from their equality.
  Confluence up to an observation, such as the ledger's effects, is a direction: it needs an equivalence coarser than equality that is a bisimulation (C's PLAN4 §1).
  Starstream's drafts compare labeled traces, which K has no notion of; a trace cell is how a K definition records them.
- **A type checker,** written as K functions, for type soundness.
- **Properties K cannot express,** in Lean (`product.md` §3.6).

**Direction:** one declaration of each fact, in K where a K function can say it, that every theorem kind reads.
Otherwise each command grows its own version of the same fact, and they drift apart.
The no stuck states theorem (B's next step, §8) would be the first to read the shared legality and endings.

**Open (§9, question 2):** which kinds of waiting may be an acceptable ending?
Recommended (B, after testing the first answer against several definitions): waiting on the environment may be (a `read()` on empty input, a contract waiting for its next transaction, a server between requests); waiting on another part of the same configuration may not (a thread joining a thread that joins it back).
The second is a deadlock, so it is always reported, and "finished" means finished for soundness and confluence alike; a configuration waiting internally is justified by the invariant (no cycle of processes waiting on each other).
Today IMP++'s soundness counts a thread waiting at `join` as finished, which is the case this excludes.

## 3. Theorems feed theorems

A proved theorem should be an input to the next, by name in Lean, not restated:
- a proved invariant is the legality that claims, confluence and soundness assume;
- a determinism theorem of one process discharges confluence's `SameThreadJoins` (one process stepping two ways from one state); `demos/UtxoConf/Joins.lean` proves it by hand today;
- confluence's commutation lemmas are what independence (proving steps in parallel) rests on (`product.md` §4, CNF-15), once they hold in both directions: today they prove that two steps enabled at one state join, and independence also needs that a step taken after another could have been taken before it, which fails exactly at handoffs (a resume enabling a child); Lipton's and partial-order reduction rest on the same facts, but apply only to a definition written finer than its atomic unit;
- soundness plus linearity gives a session-typed language's guarantees (§6).

**Today:** claims consume three kinds of theorem by name: the invariant a library generated with `gen --invariant` proves preserved (`--assume-invariant`, `invariants.md`), relate's and refine's bisimulations (`--transfer`, `AF.of_bisim`, `EF.of_stutter`), and determinism (`--transfer-det`, `AF_iff_EF_of_det`).
The other kinds state and prove their hypotheses themselves.
**Direction:** each kind's hypothesis is a named Lean proposition, discharged by citing the theorem another kind proved.

## 4. Systems of several semantics

Every generator today reads one K definition, and `relate`/`refine` read two definitions of one language.
Real systems have several semantics layered on each other.
Starstream, as one example of the shape (§7 for others):

| Layer | What it is | Written in |
|---|---|---|
| Computation | Wasm, the code a UTXO runs | KWasm exists in K |
| Language | Starstream, compiled to Wasm | Starstream's codebase; not K today (§7) |
| Interleaving | a transaction: a finite DAG of UTXO transitions, executed in an order the DAG allows, with legality rules (Starstream's codebase, not written yet). Its step is a segment: a coroutine's run from a resume to its next yield or raised effect, atomic by Starstream's model. The coordination script names every input UTXO ahead; the path is known only once it runs (a ZK prover follows the trace of a run made without ZK) | not written |
| Ledger | validity of a transaction, the UTXO set | could be K, or a Lean library |

Proofs are made at several units, depending on how far one zooms in: a folding step, a segment, a transaction, a change to the UTXO set (`product.md` §4).
Each unit is the step of its own layer, and a theorem is stated over the layer whose step is its unit.

Adjacent layers connect in three ways, each needing its own mechanism:

1. **Refinement: one definition implements another.** Two scales, of very different size:
   - *A definition against a variant of itself:* an optimization applied to a K definition keeps its behavior (a rule split or merged, a loop unrolled, constructors renamed).
     **Today:** `relate` and `refine` (`design.md` §3.2, §3.5), for definitions whose constructors correspond.
   - *One language compiled to another:* Starstream to Wasm, a coroutine to the state machine it compiles to, RISC-V or SM83 against a reference model.
     This is a certified compiler, a deep topic of its own with long prior work (CompCert; Wasm work in Rocq), not an extension of `refine`.
     It is not ruled out: when every layer is its own K or KRS project, the same techniques would apply (the author states the relation between the two configurations, and the generator states one obligation per rule), but it is a separate effort, not on this roadmap.
     **Today** the agreement between such layers is checked by light formal methods: kink's mutation testing builds a test corpus that tells the layers apart, with the differential tests.
2. **Parameterization: one layer is generic in another.**
   The interleaving says "if a coroutine runs from a resume to its next yield or effect with label l, the configuration steps with label l", whatever the coroutines' language is; it relies on the ledger's validity checks without restating them.
   **Today:** a K definition's hooked functions are parameters (`class Hooks`), instantiated from a Lean library; a whole lower layer's step relation is not.
   **Direction:** the lower layer's step as a parameter, with its contract as a hypothesis, so the upper layer's theorems are proved once for every lower layer that meets the contract.
   The contract is stated at the upper layer's unit: for the interleaving, the lower layer's big step from a resume to the next yield or effect, not its single steps.
   It says that the big step preserves the lower layer's legality and that its labels are of these forms; for confluence and independence it must also state its footprint: a process's step touches only its own binding and the shared cells it names (keyed ones at the bindings it names).
   The footprint is the main risk of this form, since commutation needs it and nothing else in the contract implies it.
   The alternative is one combined K definition per system, which reuses every generator unchanged (confluence's views read footprints off the rules, as today) but gives no modular theorems and Lean proofs at the combined size.
   Which one, or when each, is what the prototype of §8 decides.
3. **Interleaving: many instances of one layer side by side.**
   This is confluence's and independence's home (`product.md` §4), at two levels, each its own statement over its own definition:
   - *inside one interleaving:* the segments of different UTXOs that read nothing the others write;
   - *across transactions:* transactions whose input UTXOs are disjoint, at the ledger's level, as a parallel executor relies on.

   A property of the interleaving (every order the DAG allows gives the same effects) is not a property of one contract over the ways its UTXO can evolve; the second is the contract author's, through invariants and claims (§7).
   In the `utxo` fixture a transaction's DAG is implicit: ids derive from content, so a spend is enabled only once its output exists, and the DAG's edges are the enabling relation.
   Its confluence with no premise (`demos/UtxoConf`) is therefore already "every order the DAG allows gives the same result" for that fixture.
   A DAG explicit in the configuration, with legality "a transition's predecessors have run", is the restriction-of-steps reading of `product.md` §8 question 3.
   As a feature, independent of any consumer, it is confluence under a readiness condition: any segment whose inputs are ready may run.
   The shape that needs it is a coroutine handoff: a resume makes the resumer wait until the child yields, so a step of the interleaving is a whole segment; no fixture has it yet (C).

Some layers are not K: a ledger written in Lean is an imported library (`product.md` §3.6), and a runtime is related by conformance tests rather than proofs.
**Principle (proposed):** one specification per layer.
A second, hand-written model of the same layer (for a model checker, say) is a source of disagreement unless it is generated from the first or proved equal to it.

## 5. Runs, temporal properties, liveness

- **Safety over runs reduces to invariants.**
  Any "nothing bad ever happens" property is an invariant of the configuration extended with enough history.
  When the configuration already records it (a trace cell, a spent set in the ledger), it is an invariant today.
  When it does not, the author needs a monitor: a small machine that steps along with the semantics and records what the property needs.
  **Direction:** one run vocabulary in the prelude (§8, step 3), and each invariant also stated as "P holds always, on every run".
  For safety this adds nothing over `Preserved` and `Star`; its value is one statement type that temporal work builds on instead of restating.
  "Every run" includes the maximal finite runs (`Avoids`' shape), or an "always P" over infinite sequences would say nothing of a program that halts.
  Then monitors, as a second definition stepped in product with the first (§4's parameterization, applied to a property).
- **Liveness depends on whether executions are finite.**
  - *Finite executions.* A Starstream transaction is a finite DAG of UTXO transitions, executed in some order the DAG allows; everything in it runs.
    What there is to prove is that each step terminates (one function, §1), that no execution gets stuck (§2), that every execution ends (here a measure every step decreases: the transitions of the DAG not yet run), and that every order the DAG allows gives the same result (confluence).
    **Today** for the fixture `handoff` (CNF-22): the work left is the measure, written by hand (`HandoffConf.terminates`), and `HandoffSeqRel.transaction` composes it with confluence and the script's own order through `KPrelude.Ends`. A generated form (the author's measure as a K function, one obligation per rule that the step lowers it) is a **direction**: B's, built in §8's step 4, whose termination of each segment is its second definition (Sebastien, 2026-10-30).
    There is no fairness question: the interleaving borrows concurrency's vocabulary (coroutines, schedules) without its starvation problem.
    What plays the part of scheduling is performance: which steps are independent, so that their proofs can be made in parallel (§4, at two levels).
    That is a commutation question (confluence's footprints, `product.md` §4), not a liveness one.
  - *Unbounded executions* (a server, threads that run forever; in Starstream's terms, a resume repeated forever, whether through Starstream's own constructs or Nightstream's folding directly, which is Starstream's design question): progress holds only under an assumption about the scheduler, such as "a process that can step is eventually chosen" (fairness).
    This needs runs, the assumption stated over them, and ranking arguments.
    **Proposed:** a new layer over the same step relation, in Lean, not a separate tool. This answers `product.md` §8 question 2 ("whether Lean is the right tool"), which stays open until Sebastien decides it.
  - *A decreasing measure* (every step decreases a quantity) proves some properties with one obligation per rule, as termination measures do today, but many properties have no such measure; richer disciplines such as session types (§6) are meant to cover more.
  **Open (§9, question 3):** liveness under fairness as its own branch, designed when a customer's property needs it.
- **Exploration is not proof.**
  Finding a bad schedule is a search over runs; k-rust's engine searches K definitions (its fuzzer, §10, searches inputs), and model checkers such as TLA+'s or Quint's search their own models.
  Whether a separate model checker earns its place is open; if it does, the principle of §4 applies: its model is generated from the K definition, or proved equal to it.

## 6. Session types

A session type describes a communication protocol: "send an integer, then receive a boolean, then end".
A session-typed language guarantees, for programs its checker accepts:

| Guarantee | What it is in k2lean's terms | Builds on |
|---|---|---|
| Preservation | typed configurations stay typed | type soundness (§1) |
| Deadlock freedom | a configuration that cannot step is finished, never waiting | soundness with endings that exclude waiting (§2) |
| Linearity | each endpoint of a linear channel is owned by one process | an invariant; it is also what makes two processes' steps commute, so confluence takes it as its program hypothesis (C, 2026-10-29). Shared names that anyone may use (a service, a ledger) bring races back, which legality or ownership must exclude, as the `utxo` fixture's owner checks do |
| Protocol fidelity | the messages on each channel follow its type | safety over runs: an invariant over the recorded trace (§5) |
| Delivery (some systems) | every pending message is eventually received | liveness (§5): in a finite execution, no stuck states plus termination; in an unbounded one, under fairness |

So a session-typed language is not a new theorem kind: it is soundness, an invariant, confluence and, for delivery, liveness, over one checker the author writes in K.

**Why revisit them now.**
Starstream today has no session types, by an explicit decision: the cost in what humans must read, write and reason about looked too high for a concept with little adoption in decades.
That cost was mostly proofs and annotations written by hand.
With the generator stating the obligations and AI proving the cases its tactics leave, the cost that stays with humans is reading the protocol declarations and the checker.
Whether that can be made readable for coroutines over a ledger is the question; the experiment of §8 answers it on a small language, as a k2lean feature, before Starstream decides whether to adopt it.

What is not yet known:
- deadlock freedom is a global property (no cycle of waiting processes), so whether its proof splits per rule as soundness's does;
- whether a protocol notation exists that a human reads at a glance for multiparty, ledger-mediated interactions;
- the cost at a realistic size.

## 7. Customers and what they ask

What each customer would prove with k2lean, in its own codebase, by §1's levels and §4's connections.
Today's coverage is in `product.md` §4; this table is the catalog §8's first step completes.

| Customer | Main asks |
|---|---|
| KEVM | a library at scale (G1); determinism with its overlaps witnessed; no stuck states (an invalid opcode is an exceptional halt, an acceptable ending; a configuration no rule handles is a gap); refinement against another EVM model (an EVM project's claim, `product.md` §6) |
| KMIR | a library at scale (G1); findings such as functions declared total that diverge |
| KWasm | type soundness of validation, if validation is written as K functions (not checked); no stuck states; the computation layer under Starstream |
| RISC-V, SM83 | no stuck states and determinism; claims about programs; agreement with a reference model, possibly not in K (a cross-language question, §4). SM83 is being written by Sebastien in a repository of its own, updated as k2lean's features land: the instruction-set validation, and a test of the end-user experience |
| Starstream language | type soundness with affine continuations (a linearity invariant); one contract's properties over the ways its UTXO can evolve, written by the contract's author as invariants and claims (as K audits Solidity contracts); agreement with the Wasm it compiles to (a certified-compiler question, §4; kink's corpus today) |
| Starstream interleaving | every order a transaction's DAG allows gives the same result, under legality (confluence); independent segments, for proving them in parallel; at-most-once resumption (an invariant); no segment stuck |
| A ledger | value conservation, unique ids, no double spend (invariants); validity of a transaction as legality; independent transactions (disjoint inputs), for proving them in parallel; possibly a Lean library |

**Starstream today and its possible futures.**
- *Today:* Starstream does not use K. It types suspended continuations as affine (storable and movable, never duplicated) and has no session types, by choice.
- *Planning drafts:* `starstream-fv/plan/` holds AI-generated brainstorming from before k-rust existed: directionally accurate, not requirements. Its obligation lists (M-1 to M-7, O-1 to O-12, G-1 to G-7) are used here as examples of the properties such a system needs, and its tool choices (Quint for the process level, among others) predate what k-rust and k2lean now offer, so they are to be re-decided from first principles.
- *Possible futures*, each Starstream's to decide and build: its semantics in K, over KWasm; a session-typed protocol layer if §6's experiment shows a readable form; unbounded programs (a resume repeated forever), where fairness could apply (§5), through Starstream or through Nightstream's folding directly, which Starstream decides.

## 8. Steps that would settle the direction

In order, each small enough to finish and each answering a question above:

1. **The requirements catalog** (read-only): every customer's property list, each property classified by level (§1) and layer (§4), with the theorem kind that would prove it and what is missing. The coverage of the plan then comes from a table, not an impression.
2. **No stuck states, reading the shared legality and endings** (B): the theorem for VM and ISA customers, and the first consumer of §2's declarations. It consumes TERM-1c (core) to tell a divergent function from an undefined one (§2). Validation follows the customers: SM83 (Sebastien's repository, as features land), a KEVM slice and the `utxo` fixture first, then IMP++ and a Wasm fragment.
3. **One run vocabulary.** The prelude part is done (core's RUN-1, §1). What remains is B's: every generated invariant also stated as "always P" on every run (§5), one line per library (`Paths.always_of_preserved`), from `invariants.rs` and the kind 2 template.
4. **A two-layer prototype** (a fixture of the shape, not a consumer's model): a fixture derived from `utxo`, with the handoff shape (§4.3), as a tiny coroutine language and a process-plus-ledger level, built both ways of §4.2 (the lower layer as a parameter, and one combined definition). The interleaving layer's step is a run of the lower layer from a resume to the next yield or effect, so the lower layer's contract is that big step and its footprint. One property per level: soundness, at-most-once resumption, confluence over the orders a DAG allows (under readiness, §4.3), termination of each segment; the coroutine language's determinism is cited for confluence's `SameThreadJoins` (§3), through a lemma of step 3's run vocabulary: a deterministic relation has at most one run to the first yield or effect, so the big step is deterministic too. `utxo` keeps its result (confluent with no premise) as the generality fixture; the prototype's combined form is confluent under readiness; the parameterized form is the experiment. Whatever does not fit is the real gap list for systems of semantics. C owns its confluence part; B its soundness, its invariants and its termination of each segment, with the generated measure (§5).
5. **A session-typed toy** on the same fixture: a protocol checker written in K, run through soundness, the linearity invariant and confluence. Measured by the number of hand cases and by whether Sebastien finds the protocol declarations readable.
6. **Liveness under fairness**, once a property in the catalog needs it (unbounded executions; not Starstream's finite transactions).

## 9. Questions for Sebastien, and the working answers

Each answer is the recommendation Sebastien gave the go-ahead to on 2026-10-29; any of them changes if he decides otherwise.

0. Is "no stuck states under a well-formedness property the author states" the general product, with type soundness one instance of it? **Working answer:** yes.
1. Order: state-level first, with runs defined from the start (§5), or temporal statements first? **Working answer:** state-level first; the runs are defined (RUN-1).
2. Which kinds of waiting may be an acceptable ending (§2)? **Working answer:** waiting on the environment yes, waiting on another process of the configuration no. It answers `product.md` §8 question 3 as well.
3. Liveness under fairness: its own branch, or covered by one example in the first design? **Working answer:** its own branch, designed when a customer needs it.
4. §8's order and owners. **Working answer:** the order as written; step 1 B; step 2 B; step 3 core (done) and B (the "always P" line); step 4 C for confluence, B for soundness, the invariants and termination (the generated measure of §5: Sebastien, 2026-10-30, as a per-rule obligation over the configuration, like an invariant's, not a separate session); step 5 B, with C for confluence; step 6 later.

## 10. Refuting an obligation before proving it, and the testing tools that exist

Status: a **direction**, written by the kink session on 2026-10-30 from a discussion with Sebastien; not decided, and not on §8's order.
The docs site does not present it (Sebastien, 2026-10-30): its fuzzing section is about growing a test corpus, and k2lean's part of the site is still to be written.

**Why.** Much of the time, a proof is stuck because its statement is false: a missing side condition, an empty map, a negative chain id.
k2lean already meets such statements (`product.md` §6: `countAllOccurrences` equation 2, 6 of KEVM's 22 Set/Map simplifications without well-formedness) and wants every refuted obligation reported as refuted (`product.md` §3.2, items 5 and 6), which today is written case by case.
An agent proving open cases gains most: a refutation found in seconds stops it working on a goal that is false.

**What k-rust and kink already have** (read these before building a generator or a counterexample search in k2lean):
- **`krust fuzz`** (`crates/k-rust-fuzz`; guide `docs/fuzzing.md`, reference `crates/k-rust-fuzz/README.md`) searches for values of *holes* so that a run of the K definition reaches a *target*.
  - **Holes:** literal spans of a program the author wrote, configuration variables (`$NAME`), or, in the library API only, free variables of a KORE initial pattern.
  - **Targets:** a rule; a K pattern, at the final configuration or at any state, on one path or all paths; or a differential, which compares two definitions' ends on one input.
  - **Search:** sort-directed generators, a dictionary, a coverage climb, a corpus, a solver-backed proposer (`solve`) and shrinking.
  - **Results:** deterministic and replayable, with a witness file. A witness is a concrete input that a re-run confirmed. "No witness" is never a proof that none exists.
  - It searches the K definition, never the Lean.
- **`kink-flow fuzz`** (`kink/crates/kink-flow`) runs the same search inside a kink flow, and kink confirms the witness. kink itself does mutation testing and builds the corpus that tells two definitions apart (§4).
- **The backend's critical-pair check** (`k_rust_backend::data_term`; `docs/compatibility.md`, and `docs/fuzzing.md`, "Not comparable at setup") searches small ground terms for an input at which two equations give different results, and reports it as a genuine finding.
- **k-rust's prover:** when a claim fails, the configurations it could not finish are where to look for a counterexample.

**Which obligations a search can refute:**

| Obligation (§1) | A refutation is | What exists |
|---|---|---|
| An equation, or two overlapping equations | a ground input where the two sides differ | the critical-pair check, for pairs; an equation against its hook through the check's hook pairs. Extend that search for single equations rather than start another |
| One program's runs (a claim) | a concrete run of the claim's program that misses the target | a pattern target on that program, with its symbolic values as holes |
| Every reachable state, whole-run safety | a program that reaches a bad state | a pattern target at any state, over a template |
| Two definitions (`relate`, `refine`) | one input with different ends | the differential target. It compares only ends that are data in both definitions, with no translation between their constructors |
| Two runs of one definition (`terminal_unique`, noninterference) | one input with two different ends; two inputs that agree on public values and differ in public output | not built. An all-paths run lists every end of one input, but no target asks for two different ones, and no target pairs two inputs |
| One step, per rule (invariant preservation, no stuck states, the per-rule cases of noninterference and `refine`) | a configuration that satisfies the premise, from which the rule's step breaks the conclusion | **not reachable by program search.** The fuzzer visits only states that some program reaches, while a stuck invariant proof is usually about a true invariant that is not inductive: it fails only at states no program reaches. This needs configurations generated under the premise. KORE-pattern holes and the sort-directed generators are reusable for that; a premise over a whole configuration is not built. Generation could equally run in Lean, on the executable `step` that `Adequacy` ties to `Step` |

The per-rule row is where most of k2lean's open cases are, and the one the existing tools do not reach.
The rows above it are mostly recipes over what exists: an agent writes the stuck statement as a target and runs the fuzzer.
Turning a witness, which is a K input, into a Lean refutation stays k2lean's part.

**Experiment that would make it real:** take `countAllOccurrences` equation 2 and one open per-rule case of a fixture, and see what the existing tools find for each: the critical-pair check for the equation, a pattern target or KORE-pattern holes for the case.
The result decides whether this is a recipe in the docs or a feature, and on which side (fuzzer or k2lean) configuration generation belongs.
