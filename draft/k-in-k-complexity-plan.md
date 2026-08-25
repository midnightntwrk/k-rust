# Modern K-in-K: complexity reconnaissance plan

Status: initial reconnaissance plan. This document replaces "the K frontend is
large" with a capability graph, executable oracles, and a complexity measure
calibrated by small probes. The proposed gated implementation sequence now
lives in `draft/k-in-k-execution-roadmap.md`.

Assessment baseline: 18 August 2026.

Progress through 19 August 2026: the initial Gate A census, Gate B differential
harness, and all three bounded probes are complete. See
`draft/k-in-k-oracles.md`, the three `draft/k-in-k-probe-p*.md` reports, and the
executable harnesses under `oracle/`, `p1/`, `p2/`, and `p3/`. The next gate is
independent review; broad implementation has not been authorized by these
probe results.

## 1. Objective

Assess the complexity of building a modern, feature-complete successor to
K-in-K: an explicit, executable semantics of K frontend constructs and their
lowering to Kore/Matching Logic.

K-in-K does **not** mean implementing a K execution backend in K. The target is
the frontend/compiler semantics which turns K definitions into the declarations
and axioms consumed by a Kore backend.

The assessment must answer:

1. What does "feature-complete" mean at a testable boundary?
2. Which behavior can be reused, which can only be used as an oracle, and which
   must be specified anew?
3. What is the dependency structure, especially the serial core and tightly
   coupled clusters that cannot be cheaply parallelized?
4. How strong is the oracle for each capability?
5. How many empirically calibrated, validated agent attempts would a build
   require, with what uncertainty?

Human-hours and source lines are explicitly not the primary estimates. Agentic
development changes the cost of parallel breadth, but does not remove serial
dependencies, semantic ambiguity, weak feedback, or integration rework.

## 2. Reference systems and pin

This assessment uses these names:

| name | location | role |
| --- | --- | --- |
| `K` | `/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k` | production reference implementation and primary behavioral oracle |
| `K_TS` | `/home/sebdev20/Documents/git/workspaces/starstream-fv/k-framework-ts` | reusable TypeScript representations, adapters, comparators, runners, and fixture corpora |
| `OLD_KINK` | `/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/kframework/k-in-k` | conceptual predecessor and source of the fixed-point oracle |

The initial compatibility pin is **K v7.1.337**, commit
`4a46d1231473b599c699160132fd6e76a5c46406`. This is both the checked-out K
source and the release recorded by `K_TS/packages/k-parser/src/version.ts`.

Changing the K pin is a compatibility project, not a transparent dependency
upgrade. Every implemented capability should record the upstream files or
observable contracts from which it was derived, following `K_TS`'s existing
`TRANSCRIBED_FROM` pattern.

## 3. Three meanings of feature-complete

The word "complete" needs three tiers. Combining them into one target would
make the estimate misleading.

### F1: semantic compilation completeness

For valid definitions in the supported K release and option profile, produce
Kore whose execution and proof behavior is equivalent to Kore emitted by
official K.

This includes:

- frontend constructs, generated rules, and generated declarations;
- rule and configuration parsing, unless supplied through a declared parser
  adapter boundary;
- the normal lowering pipeline;
- Kore declarations, attributes, axioms, rules, and claims needed by the
  selected backend profile.

It does not require byte-identical output, identical internal IDs, or identical
wording of every diagnostic.

### F2: normalized artifact parity

In addition to F1, agree with official K at selected intermediate boundaries:

- parsed `KDefinition`/`parsed.json`;
- compiled `KDefinition`/`compiled.json` after named stage prefixes;
- `syntaxDefinition.kore`, `macros.kore`, and the main `definition.kore` after
  documented normalization.

This is primarily an oracle and debugging target. It is stronger than semantic
equivalence in some ways and weaker in others: matching an artifact does not by
itself prove its meaning is correct.

### F3: drop-in frontend parity

In addition to F1 and F2, reproduce the user-visible compiler product:

- accepted CLI options and module-selection behavior;
- caches and generated parser artifacts;
- warnings, errors, source locations, and invalid-definition behavior;
- backend-specific refusals and compatibility flags;
- stable file layout expected by downstream K tools.

F3 is expected to be substantially larger than the metacircular semantics
project. It must be estimated separately and should not be allowed to obscure
the feasibility of F1.

### Initial recommendation

Build and estimate **F1 for the Haskell-backend Kore profile**, use the useful
parts of F2 as its oracle, and inventory F3 without committing to it. Proof
specification compilation is tracked separately until its inclusion in F1 is
decided.

## 4. Architecture and trust boundaries

The intended dataflow is:

```text
K source / literate Markdown / include tree
  -> source selection and outer parsing
  -> KDefinition with rule/configuration bubbles
  -> generated grammars, scanning, inner parsing, disambiguation
  -> parsed KDefinition
  -> generated configuration syntax and sentences
  -> named frontend lowering stages
  -> backend preparation
  -> Kore sorts, symbols, axioms, rules, claims, and attributes
  -> Kore backend execution/proof
```

There are two different trust questions:

1. **What is part of the semantics?** Ideally every meaning-bearing lowering
   step is explicit and executable in K.
2. **What may remain an adapter?** Filesystem access, Markdown extraction,
   byte-level lexing, process launch, artifact normalization, and possibly
   parsing can be supplied by TypeScript without making the semantic lowering
   less explicit.

The inner-parser boundary is the largest unresolved architectural choice:

- **Adapter parser:** official K or a compatible parser produces parsed KAST;
  K-in-K begins at parsed definitions. This makes semantic lowering tractable
  sooner, but is not a complete independent frontend.
- **Specified parser pipeline:** scanner generation, parsing, disambiguation,
  and type inference are included in the project. This is the honest F1 target
  if "frontend" includes the meaning of concrete rule syntax.
- **Two-stage delivery:** establish lowering correctness through the adapter,
  then replace the parser boundary. This is the recommended assessment and
  implementation order; it does not silently redefine the final scope.

`K_TS` may be used as an orchestration and oracle layer in all three cases. It
must not be counted as a K-in-K implementation of a pass merely because it can
perform or inspect that pass in TypeScript.

## 5. Initial capability inventory

This is a first census, not yet the final work-breakdown structure. A leaf is
ready for estimation only after it has a declared input, output, dependencies,
oracle, and corpus slice.

Reuse labels:

- **Direct:** a tested component can be used at the declared adapter boundary.
- **Harness:** useful for driving, comparing, or inspecting the target, but not
  itself an implementation of the K-in-K semantics.
- **Reference:** behavior can be studied or transcribed; meaningful new target
  code is still required.
- **None known:** no reusable implementation has yet been identified.

Risk labels are provisional: `L` low, `M` medium, `H` high, and `X` a likely
critical-path or scope-defining capability.

### 5.1 Source intake and outer definition parsing

| ID | capability | current evidence and reuse | primary oracle | grade | risk |
| --- | --- | --- | --- | --- | --- |
| IN-01 | Literate Markdown fence selection with source locations | Direct adapter in `K_TS/k-parser`; production K and pyk references pinned | Exact source-span and token fixtures | O4 | L |
| IN-02 | `requires` resolution, include paths, cycles, and prelude loading | Direct adapter for DFS slurping in `K_TS/k-parser`; K adds compiler policy around preludes and lookup paths | Parsed module closure against official K | O3 | M |
| IN-03 | Outer lexing and surface parsing | Direct adapter in `K_TS/k-parser`, with 775 tests across its whole package and vendored upstream fixtures | Exact token/surface-AST fixtures plus official outer JSON | O4 | L as adapter; H if reimplemented in K |
| IN-04 | Surface AST to `KDefinition` | Substantial Direct/Harness support in `K_TS/k-parser`, including sentence conversion absent from pyk | Normalized `--outer-parsed-json` / `parsed.json` | O3 | M |
| IN-05 | Generated klabels, user-list productions, sort synonyms, priorities, associativity, lexical syntax | Direct/Harness support in `K_TS/k-parser`, derived partly from `KILtoKORE` | Feature-isolated AST goldens and official K | O4 | M |
| IN-06 | Module/import closure, syntax/main module selection, selectors, excluded module tags | Partial Direct support for parsing; compiler policy remains Reference | Definition/module-set differential | O3 | M |
| IN-07 | Outer and structural validation: duplicates, regexes, attributes, sorts, labels, streams, tokens, rewrite shapes | Explicitly excluded from `K_TS/k-parser`; production checks are spread across `Kompile` and `compile/checks` | Negative corpus with diagnostic class and source location | O3 | H for F3; M for valid-input F1 |

### 5.2 Generated grammars, inner parsing, and disambiguation

`K_TS/k-parser` intentionally stops before this boundary. Production K's
`RuleGrammarGenerator` creates extension, disambiguation, and parsing modules;
`ParseInModule` then runs an Earley parser and a multi-stage ambiguity pipeline.

| ID | capability | current evidence and reuse | primary oracle | grade | risk |
| --- | --- | --- | --- | --- | --- |
| IP-01 | Rule, configuration, and program grammar generation | Some derived facts in `K_TS/k-parser`, but complete behavior is Reference in `RuleGrammarGenerator.java` | Generated grammar modules and focused parse results | O2 | X |
| IP-02 | Scanner construction: regex terminals, token precedence, lexical rejects, and global/module scanners | Reference in K's inner parser | Token streams and negative lexical cases | O3 | H |
| IP-03 | Generalized parsing and ambiguity representation | Reference Earley implementation in K | Raw parse forests before filters, if an observation seam is added | O1 | H |
| IP-04 | Tree cleanup, record collapse, priority and associativity filtering, K application conversion | Reference sequence is explicit in `ParseInModule.parseStringTerm` | Per-filter snapshots plus final parsed KAST | O2 | H |
| IP-05 | Ambiguity movement, `prefer`/`avoid`, top-LHS handling, overload resolution, list completion, bracket removal | Reference sequence is explicit in `ParseInModule` | Adversarial ambiguity corpus and final KAST | O3 | X |
| IP-06 | Sort/type inference, including SimpleSub and Z3 modes | Two production algorithms exist and can cross-check each other in `CHECKED` mode | Result/error parity and production's own cross-check | O4 | X |
| IP-07 | Bubble dispatch for rules, claims, contexts, aliases, and configurations | Reference in `DefinitionParsing`; outer bubbles already represented by `K_TS` | Parsed sentence differential with location preservation | O3 | H |
| IP-08 | Parse caching, invalidation, parallel parsing, and source/warning remapping | Primarily F3 operational behavior; semantic cache invalidation can affect correctness | Cold/warm equivalence and mutation cases | O3 | M for F1; H for F3 |

The production disambiguation order currently observed is:

1. Earley parse;
2. tree cleanup;
3. record-production collapse;
4. priority and associativity filtering;
5. `KApp` conversion;
6. ambiguity movement and `prefer`/`avoid`;
7. SimpleSub or Z3 type inference;
8. overloaded-terminator resolution;
9. overload-aware ambiguity movement;
10. remaining-ambiguity rejection;
11. empty-list insertion;
12. bracket removal.

This sequence must be treated as one coupled cluster until probes show stable
interfaces at which it can be split.

### 5.3 Configuration elaboration

| ID | capability | current evidence and reuse | primary oracle | grade | risk |
| --- | --- | --- | --- | --- | --- |
| CF-01 | Default configuration insertion and configuration grammar construction | Reference in `DefinitionParsing` | Parsed configuration and module-import snapshots | O3 | H |
| CF-02 | Configuration-cell validation and reserved/generated cells | Reference in `DefinitionParsing` and compiler checks | Positive and negative configuration corpus | O3 | M |
| CF-03 | Generation of cell sorts, productions, initializers, and rules from configuration declarations | Reference in `GenerateSentencesFromConfigDecl` | Stage output immediately after config expansion | O3 | X |
| CF-04 | Configuration metadata used by later passes | Reference implementations `ConfigurationInfo`, `ConcretizationInfo`, `LabelInfo`, and `SortInfo` | Query-level fixtures plus consumer-stage parity | O1 | H |

Configuration parsing precedes ordinary rule parsing because generated
configuration syntax changes the rule grammar. This creates a serial dependency:

```text
outer definition
  -> parse configuration bubbles
  -> generate configuration sentences and grammar
  -> parse rule/context/claim bubbles
```

### 5.4 Named semantic lowering stages

For K v7.1.337, `KoreBackend.steps()` exposes the following default order:

1. `resolveComm`
2. `resolveIO`
3. `resolveFun`
4. `resolveFunctionWithConfig`
5. `resolveStrict`
6. `resolveAnonVars`
7. `resolveContexts`
8. `numberSentences1`
9. `resolveHeatCoolAttribute`
10. `resolveSemanticCasts`
11. `subsortKItem1`
12. `constantFolding`
13. `propagateMacroToRules`
14. `guardOrs`
15. `resolveFreshConfigConstants`
16. `generateSortPredicateSyntax1`
17. `generateSortProjections1`
18. `expandMacros`
19. `addImplicitComputationCell`
20. `resolveFreshConstants`
21. `generateSortPredicateSyntax2`
22. `generateSortProjections2`
23. `checkSimplificationRules`
24. `subsortKItem2`
25. `concretizeCells`
26. `genCoverage`
27. `addSemanticsModule`
28. `resolveConfigVar`
29. `addCoolLikeAtt`
30. `removeAnywhereRules`
31. `generateSortPredicateRules`
32. `numberSentences2`

Some names repeat because intervening passes create new syntax that must itself
be lowered. The repetitions are evidence against treating the pipeline as an
unordered bag of independent transformations.

For assessment, the stages are initially grouped by shared semantic state:

| ID | cluster | included behavior | likely dependencies | primary oracle | grade | risk |
| --- | --- | --- | --- | --- | --- | --- |
| LO-01 | Builtin and special-form resolution | commutative simplification, I/O streams, `#fun`, functions with configuration | parsed rules, configuration metadata | Prefix-stage `compiled.json` plus execution | O4 | H |
| LO-02 | Evaluation contexts | `strict`/`seqstrict`, explicit contexts, heat/cool attributes | productions, generated labels, configuration | Prefix-stage differential plus execution traces | O4 | X |
| LO-03 | Variables, casts, and patterns | anonymous variables, semantic casts, guarded or-patterns | sort/type information | Prefix-stage differential | O3 | M |
| LO-04 | Sort infrastructure | subsorting to `KItem`, sort predicates, sort projections | complete sort/production index | Prefix-stage differential and sort-query invariants | O4 | H |
| LO-05 | Macros and constants | propagation, macro expansion, constant folding | functions, side conditions, module visibility | Prefix-stage and execution differential | O4 | H |
| LO-06 | Fresh values and implicit cells | fresh config constants, fresh constants, computation cell, configuration variables | configuration and sort metadata | Prefix-stage differential | O3 | H |
| LO-07 | Cell concretization | parent/child completion, open cells, fragment handling, cell sorting | full configuration metadata and transformed rules | Stage differential plus nontrivial execution | O4 | X |
| LO-08 | Rule identity and backend policy | numbering, coverage, semantics module, cool-like, anywhere policy | nearly all previous stages | Artifact and backend acceptance differential | O3 | M |
| LO-09 | Validation between and after stages | simplification-rule checks, sort checks, overload lattice | pass-specific invariants | Negative corpus and official error class | O3 | H for F3; M for F1 |

The 32 names are observation points, not yet 32 work units. Each cluster must be
decomposed only where inputs and outputs can be independently validated.

### 5.5 Backend preparation and KAST-to-Kore translation

After the named stages, `KoreBackend.getKompiledModule` adds sort injections,
removes unit applications for collections, and may minimize term construction.
`ModuleToKORE` then generates backend text and axioms.

| ID | capability | current evidence and reuse | primary oracle | grade | risk |
| --- | --- | --- | --- | --- | --- |
| KO-01 | Sort-injection insertion and collection-unit normalization | `K_TS/konvert` and `K_TS/kore` provide substantial Harness code; production pass remains Reference | Normalized prepared module/Kore patterns | O2 | H |
| KO-02 | Sort declarations and token/domain-value attributes | Kore reader/writer and definition indexes in `K_TS/kore` | Declaration-set comparison | O3 | M |
| KO-03 | Symbol declarations, sort parameters, hooks, impurity, and semantic/syntax attributes | Harness support for Kore parsing/indexing; production generation is Reference | Declaration/attribute comparison | O3 | H |
| KO-04 | Subsort, associativity, idempotence, unit, functional, and overload axioms | Partial concepts existed in old K-in-K; modern behavior is Reference in `ModuleToKORE` | Canonical axiom comparison plus focused backend checks | O4 | H |
| KO-05 | Constructor no-confusion and sort no-junk axioms | Missing/incomplete in old K-in-K; modern behavior is Reference | Canonical axiom comparison and model/backend acceptance | O4 | X |
| KO-06 | Function/simplification equations, `owise`, side conditions, existentials, and sort parameters | Old K-in-K only covered narrow function shapes; production behavior is Reference | Rule-isolated Kore plus evaluation differential | O4 | X |
| KO-07 | Semantic rewrite rules, aliases, priority groups, one/all-path claims, and attributes | Kore AST support in `K_TS`; generation is Reference | Canonical rule/claim comparison and symbolic execution | O4 | X |
| KO-08 | Collection- and backend-specific generated axioms such as map-ceil behavior | Reference in production backend with option-dependent behavior | Backend-profile corpus and execution | O4 | H |
| KO-09 | Syntax and macro Kore artifacts | Inspectable with `K_TS/kore` and `K_TS/kompiled` | Three-artifact comparison | O3 | M |
| KO-10 | Kore name encoding, builtin connective mapping, and term serialization | Strong Harness support in `K_TS/kore` and `K_TS/konvert` | Exact round trips and official output | O4 | M |

### 5.6 Product surface and proof specifications

| ID | capability | current evidence and reuse | primary oracle | grade | risk |
| --- | --- | --- | --- | --- | --- |
| PR-01 | Compiler option profile and backend feature switches | Reference in `KompileOptions`, `KoreBackend`, and `ModuleToKORE` | Pairwise option matrix | O2 | H if broad; M if one pinned profile |
| PR-02 | Emitted directory layout and metadata | Strong Harness readers in `K_TS/kompiled`; runner support in `K_TS/ktool` | Artifact manifest comparison | O3 | M |
| PR-03 | Deterministic, agent-readable failures | Existing `K_TS` design patterns help, but parity is new work | Negative corpus and stable structured schema | O3 | H |
| SP-01 | Claim/specification parsing and the separate specification lowering pipeline | Production K has a distinct `specificationSteps`; `K_TS/proof` can inspect downstream artifacts | Compiled claims and backend proof behavior | O4 | X; scope decision required |

### 5.7 Initial readout

The first census contains 42 top-level capability units. Ten are provisionally
marked `X`. The initial oracle distribution is:

| grade | capabilities |
| --- | ---: |
| O1 | 2 |
| O2 | 4 |
| O3 | 20 |
| O4 | 16 |

This is encouraging for assessment feasibility: most of the surface can obtain
localized differential feedback. It is not yet evidence that implementation is
small. The critical items concentrate in three places: inner parsing and
inference, configuration/context elaboration, and rule/axiom generation.

The six O1/O2 entries deserve early oracle work because an agent can spend many
iterations implementing the wrong boundary when only an end-to-end diff is
available. The 42 entries must also be split further before they become build
tasks; they are deliberately coarser than validated agent episodes.

## 6. Initial dependency structure

The high-level critical path is:

```text
scope and K pin
  -> canonical IR and adapters
  -> outer/module closure
  -> generated grammar and scanner
  -> configuration parsing and expansion
  -> ordinary bubble parsing and disambiguation
  -> shared module/configuration indexes
  -> semantic lowering clusters
  -> backend preparation
  -> Kore declarations and axioms
  -> backend behavioral validation
```

Likely high-coupling clusters are:

1. **Grammar/parser cluster:** IP-01 through IP-07.
2. **Configuration/context cluster:** CF-01 through CF-04, LO-02, LO-06,
   and LO-07.
3. **Sort/symbol cluster:** LO-03, LO-04, KO-01 through KO-05.
4. **Rule/axiom cluster:** LO-01, LO-05, KO-06 through KO-08.

These clusters matter more than raw feature count. Work inside a cluster may
need one coherent owner or a stabilized shared interface before agent fan-out.

## 7. Reuse map for `k-framework-ts`

The TypeScript workspace changes the assessment significantly, but mostly by
strengthening adapters and oracles:

| package | assessment use |
| --- | --- |
| `k-parser` | Outer source parsing, `requires` slurping, KDefinition conversion, generated-label/list/strictness facts, and a large source corpus |
| `kast` | Canonical typed KAST algebra, traversal, matching, substitution, and JSON shapes |
| `kore` | Kore parsing/writing, symbol demangling, definition indexing, and axiom/rule classification |
| `konvert` | KAST-to-Kore term conversion and sorting/injection reference behavior |
| `kompiled` | Reading and comparing complete `*-kompiled` layouts |
| `ktool` | Reproducible official K command invocation and artifact production |
| `kore-rpc` | Backend execution/proof requests for behavioral comparison |
| `cterm`, `kcfg`, `proof` | Higher-level symbolic execution and proof equivalence tests |
| `wasm-fixtures`, `evm-fixtures`, `mir-fixtures` | Pinned real-semantics corpora and build metadata |

Reuse must be recorded per capability as one of Direct, Harness, Reference, or
None known. A package-wide statement such as "the frontend already exists in
TypeScript" would conceal the critical inner-parser and lowering gaps.

## 8. Oracle strategy

### 8.1 Oracle strength scale

Every capability receives the strongest currently available oracle grade:

| grade | meaning |
| --- | --- |
| O0 | No executable oracle; behavior is still a research or specification decision |
| O1 | End-to-end outcome only, such as backend success or final execution result |
| O2 | Normalized final-artifact differential against official K |
| O3 | Stage-local differential with an isolated feature corpus |
| O4 | O3 plus an independent invariant, metamorphic test, or downstream behavioral check |

An O4 oracle is not a correctness proof. It means an agent gets precise local
feedback and at least one check that does not merely repeat official K's bytes.

### 8.2 Official-K differential harness

For each corpus definition, the harness should capture:

- invocation, environment, K release, and all relevant options;
- outer/parsed definition JSON where available;
- `compiled.json` for the full pipeline;
- `compiled.json` for useful prefixes selected through
  `--kore-backend-steps`;
- `syntaxDefinition.kore`, `macros.kore`, and the primary Kore definition;
- backend validation and selected executions/proofs;
- stdout, stderr, exit class, and structured source locations for negative
  cases.

The named-stage option makes the modern frontend unusually amenable to
stage-local differential testing. The harness must first verify that running a
prefix faithfully exposes that prefix and does not introduce unrelated output
differences.

### 8.3 Normalization policy

Normalization is an allowlist, not a generic pretty-printer. Every rule needs:

- a name;
- the unstable producer field it removes or canonicalizes;
- evidence that the field is non-semantic for the relevant oracle;
- a test that a nearby semantic difference remains visible.

Likely candidates include filesystem roots, source digests, generated unique
IDs, and declaration ordering when the format's semantics make it irrelevant.
Labels, priorities, attributes, sort injections, side conditions, and axiom
contents must not be normalized away merely because they are inconvenient.

### 8.4 Corpus layers

The harness should grow in this order:

1. **Feature isolates:** minimal definitions with exactly one construct or
   interaction under test.
2. **Old K-in-K languages:** `foobar`, `peano`, and `imp-simple`, retaining the
   fixed-point and execution ideas.
3. **Modern IMP:** a small, conventionally structured definition with proofs.
4. **Built-in prelude and parser rarities:** dense syntax, attributes, hooks,
   tokens, and negative cases already present in `K_TS/k-parser`.
5. **KWasm:** the first readable real-language soak test.
6. **KMIR and KEVM:** scale and rare-feature coverage, not the first debugging
   fixtures.

Real-language success alone is not good localization: a large semantics can
miss a rare feature while producing an enormous opaque diff.

### 8.5 Independent invariants

Preserve and extend the old fixed-point oracle:

```text
lower(source) = expected
lower(expected) = expected
```

Additional invariants should include, where applicable:

- alpha-renaming does not change meaning;
- irrelevant declaration/import order does not change canonical output;
- every emitted reference names a declared sort or symbol in a valid order;
- rerunning an idempotent normalization stage reaches a fixed point;
- generated labels and sentence IDs are unique and traceable to source;
- KAST/Kore conversion round trips at declared boundaries;
- official and generated Kore produce the same selected executions or proofs.

## 9. Complexity model for AI-agent development

### 9.1 Static capability vector

Each leaf capability is scored independently from 0 to 4 on:

| dimension | 0 | 4 |
| --- | --- | --- |
| Semantic novelty | Existing tested implementation at the target boundary | Behavior must be newly specified or reconciled from conflicting sources |
| Coupling | Pure local transformation | Participates in a large shared-state or cyclic cluster |
| Serial depth | No unmet prerequisite | Sits behind a long critical dependency chain |
| Oracle deficit | Fast O4 feedback | O0/O1 feedback or expensive manual interpretation |
| Integration radius | Isolated output | Changes most downstream stages/artifacts |
| Scope uncertainty | Boundary and behavior settled | Architectural or compatibility decision still open |

The six-number vector is the primary record. A sum from 0 to 24 may be used to
sort reconnaissance work, but is not treated as a cardinal effort estimate.

Project-level static metrics are:

- count of leaf capabilities by risk band;
- longest dependency path;
- largest tightly coupled cluster;
- count and criticality of O0/O1 capabilities;
- number of distinct shared IR/index contracts;
- evaluation latency at each major boundary.

### 9.2 Validated agent episodes

The empirical unit is a **validated agent episode (VAE)**:

> One fresh, bounded agent attempt, using a versioned task packet, which ends
> in either a replayable artifact passing its declared oracle or a classified
> failure with preserved evidence.

A task packet records:

- model and tool versions;
- target capability and declared non-goals;
- allowed source context and upstream pin;
- starting commit/artifact digest;
- deterministic acceptance command;
- maximum intended scope before the attempt must split or report blockage.

For every probe and later implementation class, record:

- successful and failed VAEs;
- oracle cycles before acceptance;
- regressions outside the target capability;
- context or contract omissions discovered;
- p50 and p90 evaluation latency;
- whether a fresh agent can reproduce the accepted result from the task packet.

Tokens, tool calls, and wall-clock duration are telemetry. They are not the
primary unit because they vary with model generation, infrastructure, caching,
and agent style.

### 9.3 Forecast form

After calibration, report estimates as ranges:

```text
semantic target:  P50–P90 validated episodes
serial core:      P50–P90 validated episodes
parallel leaves:  count and maximum safe concurrency
oracle-building:  P50–P90 validated episodes
unclassified:     capabilities still at O0/O1
```

Do not publish a total before the probes. Do not add VAEs from differently
scoped tasks without normalizing their task packets.

## 10. Three bounded calibration probes

Only these probes should run in parallel, and only after the inventory and
differential harness have stable schemas. Each probe is a feasibility
experiment, not permission to grow into a subsystem implementation.

### P1: simple lowering and Kore emission

Status: completed as a bounded feasibility slice on 19 August 2026. The target
matched official K for one user sort, four symbols, eleven structural/equation
axioms, and one parsed semantic rewrite; its canonical result was a fixed
point. Official Kore executed the representative program. Direct execution of
the P1-produced projection is deferred because a backend-executable semantic
rewrite first requires the configuration-concretization work intentionally
assigned to P3. See `draft/k-in-k-probe-p1.md`.

Question: how effectively can modern K express and execute the staged
metacircular transformations, and how much of the old approach remains useful?

Scope:

- begin from adapter-produced parsed KAST, deliberately bypassing inner parsing;
- support small syntax declarations, constructors, one function, side
  conditions, and one semantic rewrite;
- produce canonical Kore for `foobar` and `peano`-class definitions;
- compare declarations/axioms with official K and execute a program;
- require a fixed point for the target's normalization boundary.

Exit artifact: a minimal modern K project and differential report. It need not
be retained as production architecture if the probe exposes a better design.

Calibration value: baseline VAE cost for local transformations with strong
oracles and little configuration coupling.

### P2: inner parsing and disambiguation decision

Status: completed on 19 August 2026. Seven exact resolved-KAST cases passed for
priority, associativity, `prefer`, `avoid`, overloads, user-list completion,
and checked SimpleSub/Z3 inference. The selected first-delivery architecture is
a replaceable official-K parsed-KAST adapter. A specified independent parser
remains a separate critical-path project because no raw parse-forest oracle is
publicly exposed. See `draft/k-in-k-probe-p2.md`.

Question: is it practical and worthwhile to specify the modern inner parser in
the target, or should it remain a replaceable adapter for the first delivery?

Scope:

- generate a grammar for a deliberately ambiguous expression language;
- include priority, associativity, overload, `prefer`/`avoid`, a user list, and
  one sort-inference case;
- capture official results after meaningful disambiguation filters;
- implement enough of one candidate architecture to match the selected cases;
- document which behavior cannot be observed without adding an oracle seam.

Exit artifact: a decision record comparing adapter, direct transcription, and
declarative-in-K parser approaches, backed by at least one executable slice.

Calibration value: VAE cost and uncertainty for the largest parser cluster.

### P3: configuration, strictness, and cell concretization

Status: completed on 19 August 2026. The K model matched the official cell
graph, six generated context rules, five concretized source rules, one function
configuration injection, and condition-presence facts at the cell-prefix and
full compiled boundaries. All eleven selected rules reached final Kore, the
projection was a fixed point, and execution produced `<k> 1 </k>` with
`<state> 2 </state>`. See `draft/k-in-k-probe-p3.md`.

Question: how severe is the coupling between generated configuration syntax,
evaluation contexts, and final rewrite rules?

Scope:

- use a non-preconcretized configuration;
- include strict or sequentially strict syntax, an explicit context, a function
  reading configuration, and `requires`/`ensures`;
- capture official artifacts after configuration expansion, context/strictness
  lowering, and cell concretization;
- match those boundaries and execute representative programs.

Exit artifact: a vertical slice and dependency report identifying the minimum
stable configuration metadata API.

Calibration value: VAE cost for a tightly coupled, high-integration cluster.

### Probe stop rule

Each probe receives a fixed number of initial VAEs. If it does not reach its
oracle, it must return a classified blocker and narrower follow-up experiment;
it must not silently turn into open-ended implementation. The initial VAE cap
is selected only after the harness task size is calibrated.

## 11. Orchestration and gates

### Gate A: single-owner census

One lead owns the scope contract, capability IDs, upstream pin, and evidence
ledger. Reconnaissance may collect evidence from many sources, but there is one
canonical matrix.

Exit criteria:

- every top-level pipeline boundary has an ID;
- every ID has at least one source reference and candidate oracle;
- unknowns are marked rather than estimated optimistically;
- target tiers and parser boundary are explicit.

### Gate B: oracle harness

Build the official-K runner, artifact schema, normalization allowlist, and
small corpus before target implementation fans out.

Exit criteria:

- the same input is reproducible from a manifest;
- full and prefix-stage output can be captured;
- one deliberate semantic mutation is detected at every comparison boundary;
- failures are replayable without recovering agent conversation history.

### Gate C: at most three concurrent probes

Status: the three probes are complete. They were executed conservatively
without broad implementation fan-out. Each has an executable passing slice,
telemetry, and a report; none yet has an independent fresh-agent replay. Gate D
therefore remains the next required step before project-wide VAE ranges or an
implementation fan-out decision.

Run P1, P2, and P3 with disjoint worktrees or artifact roots and versioned task
packets. The lead integrates results; probe agents do not redefine scope or
shared schemas.

Exit criteria:

- at least one passing artifact or classified blocker per probe;
- static vectors updated from evidence;
- VAE and oracle-cycle telemetry recorded consistently;
- cluster and critical-path assumptions revised.

### Gate D: independent review

One fresh agent audits the feature matrix against the pinned K pipeline and
tries to find omitted behavior, invalid normalization, and unjustified reuse
credit. This is sequential review, not another implementation swarm.

### Gate E: implementation fan-out decision

Only after Gate D decide:

- the initial product tier;
- whether inner parsing is in the first delivery;
- the number of stable parallel workstreams;
- ownership of coupled clusters;
- the P50/P90 VAE range and its uncertainty.

## 12. Deliverables under `draft/`

The reconnaissance should eventually produce:

| artifact | purpose |
| --- | --- |
| `k-in-k-complexity-plan.md` | This scope, orchestration, and measurement plan |
| `k-in-k-capabilities.csv` or `.json` | Machine-readable leaf capability matrix and dependencies |
| `k-in-k-oracles.md` | Artifact schemas, normalization allowlist, and corpus manifest |
| `k-in-k-probe-p1.md` | Simple lowering results and VAE record |
| `k-in-k-probe-p2.md` | Inner-parser architecture decision and evidence |
| `k-in-k-probe-p3.md` | Configuration/context coupling results and VAE record |
| `k-in-k-execution-roadmap.md` | Gated build sequence, concurrency policy, and immediate queue |
| `k-in-k-complexity-report.md` | Calibrated P50/P90 estimate and fan-out recommendation |

Executable harnesses and fixtures should live outside `draft/` once they exist;
the draft documents link to them and record their versioned commands.

## 13. Open decisions and provisional defaults

| decision | provisional default for reconnaissance | why |
| --- | --- | --- |
| Compatibility pin | K v7.1.337 | Exact source and `K_TS` pins are already available |
| First semantic profile | Haskell-backend Kore | It is the modern execution/proof route and bounds option interactions |
| Parser delivery order | Adapter first, specified parser assessed in P2 | Decouples lowering feasibility without deleting parser completeness from scope |
| Comparison | Normalized structural artifacts plus behavior | Byte equality is too brittle; behavior alone localizes poorly |
| Diagnostics | Inventory now, exact parity outside initial F1 | Negative-path product parity is a distinct large surface |
| Proof specs | Inventory and isolate; decide after P1/P3 | Separate production pipeline and claim semantics require explicit scope |
| Historical build | Do not revive it | Old K-in-K is a conceptual and test-pattern source, not a modern base |

## 14. Reconnaissance definition of done

The complexity assessment is complete when:

1. The capability inventory has independently testable leaves and a reviewed
   dependency graph.
2. The official-K oracle harness detects deliberate mutations at the selected
   boundaries.
3. P1, P2, and P3 have produced passing slices or classified blockers.
4. Complexity vectors and VAE data have replaced provisional `L/M/H/X` labels.
5. The report states separate ranges for F1, F2, and F3 rather than one blended
   estimate.
6. The serial core, largest coupled clusters, oracle gaps, and maximum sensible
   concurrency are explicit.
7. A fresh agent can reproduce every material conclusion from files and
   commands without relying on conversation history.

At that point, broad implementation can be accepted, narrowed, or rejected on
evidence rather than on repository size or intuition.

## 15. Sources inspected for this initial census

- `draft/k-in-k-summary.md`.
- `OLD_KINK/README.md`, its source modules, examples, and historical pipeline.
- `K_TS/README.md`, `docs/gap-analysis.md`, and
  `packages/k-parser/README.md`/`src/version.ts`.
- `K/k-frontend/src/main/java/org/kframework/kompile/Kompile.java`.
- `K/k-frontend/src/main/java/org/kframework/kompile/DefinitionParsing.java`.
- `K/k-frontend/src/main/java/org/kframework/parser/inner/ParseInModule.java`.
- `K/k-frontend/src/main/java/org/kframework/parser/inner/RuleGrammarGenerator.java`.
- `K/k-frontend/src/main/java/org/kframework/backend/kore/KoreBackend.java`.
- `K/k-frontend/src/main/java/org/kframework/backend/kore/ModuleToKORE.java`.
- `K/k-frontend/src/main/java/org/kframework/compile/` and compiler check
  classes as a directory-level census.
