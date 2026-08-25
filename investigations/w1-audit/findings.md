# Material omissions, overclaims, and oracle gaps

Source references use the baseline workspace and pinned reference trees named in
`draft/k-in-k-complexity-plan.md`.

## Material omissions

1. **The 42 groups are a compiler census, not the active G1 product census.**
   Stable `SemanticInput`, identity/provenance, structural selection, canonical
   patches, atomic application, G1 ingress/egress, observation instrumentation,
   branch-local monitors, mutation operators, bounded runners, and goal reports
   are required by the roadmap and feature contracts but absent as owned groups
   in section 5 of the complexity plan. The candidate matrix adds these as
   explicit G1 rows rather than assigning them to unrelated frontend groups.
   Sources: `draft/k-in-k-execution-roadmap.md` sections 1, 2, R2-G, R3-G,
   R4-G; both goal contracts.

2. **The 42 rows are not build leaves.** The plan says so, but later wording
   sometimes treats the census as a matrix ready to classify. Rows such as
   IN-05, LO-01, LO-05, LO-08, KO-04, KO-06, and KO-07 combine independently
   testable behaviors. IN-03, IN-07, IP-08, LO-09, KO-07, PR-01, and PR-03
   also cross delivery or product-tier boundaries. The audit splits only the
   cross-track cases and labels the rest `group-proxy`; exact leaf decomposition
   remains future packet work. Sources: complexity plan sections 5.1-5.6 and
   5.7; roadmap R0.

3. **No G1 row has a deterministic leaf acceptance command.** The roadmap and
   feature contracts contain valuable acceptance prose, but no checked-in
   task command exists for any of the 21 G1-classified rows (including the G1
   part of PR-03). This fails the R0 exit statement that every build-ready G1
   leaf has such a command. Source: roadmap R0; machine result from
   `bun investigations/w1-audit/verify.mjs`.

4. **Required observation seams are absent.** Missing seams include generated
   grammar modules, raw parse forests, snapshots after individual ambiguity
   filters, a prepared module after `AddSortInjections`/`RemoveUnit` and before
   `ModuleToKORE`, query-level configuration metadata, and a supported
   transformed-definition egress. Sources: P2 oracle limitation; P3 minimum
   metadata API; `KoreBackend.getKompiledModule`; roadmap section 2.

5. **Negative and interaction coverage is not an implemented corpus.** There
   is no capability-local negative corpus for structural validation, scanner
   rejects, configuration cell errors, cache invalidation, pass-local checks,
   option interactions, or G1 stale/overlap/atomicity failures. P3 explicitly
   excludes multiplicity, fragments, optional/star cells, open-cell sorting,
   nested rewrites, priorities, and general strictness arity. Sources: IN-07,
   IP-02/IP-08, CF-02, LO-09, PR-01 rows in the plan; P3 limitations; goal MVP
   acceptance sections.

## Material overclaims or wording narrower than implied elsewhere

1. **The original O1/O2/O3/O4 distribution is a candidate-oracle inventory,
   not a distribution of demonstrated current oracles.** Most rows cite an
   oracle that could be built; no command or isolated corpus currently realizes
   it. The audit therefore records separate `current_oracle_grade` and
   `candidate_target_oracle_grade`. Sources: complexity plan sections 5.7 and
   8.1; checked-in harness/probe contents.

2. **P2's blanket statement that the final cases have O4 feedback is too
   broad.** The checked inference fixture has an independent SimpleSub/Z3
   cross-check and can be O4 narrowly. Priority, associativity, prefer/avoid,
   overload, and list cases compare final resolved KAST with asserted expected
   trees but lack an independent invariant or downstream behavioral check;
   they are O3 under the plan's own scale. Sources: P2 executable evidence,
   P2 oracle limitation, complexity plan section 8.1.

3. **P1 and P3 establish bounded projections, not production compiler
   completeness.** P1 does not emit a complete backend-executable definition;
   its execution uses official Kore. P3 emits a dependency/fact projection,
   while execution uses official final Kore. Both reports state these limits,
   but their high-grade results cannot be inherited by the full KO/CF/LO
   groups. Sources: P1 exact boundary and complexity implication; P3
   limitations.

4. **The cited 775 K_TS tests are package-wide reuse evidence, not an IN-03
   capability-local acceptance count.** They provide real adapter confidence,
   but do not support assigning the whole outer/compiler ingress surface O4.
   Sources: complexity plan IN-03; K_TS k-parser README and test tree.

5. **Prefix `compiled.json` is an observation artifact from an intentionally
   failed compilation, not successful stage execution through backend
   emission.** The oracle documentation states this correctly; any capability
   conclusion must retain `acceptedNonzeroExit: true` and the exact failure
   contract. Sources: oracle document prefix-stage limitation; replay bundles.

6. **`macros.kore` equality in the smoke mutation is determinism evidence,
   not macro sensitivity.** The fixture declares no macro, so it does not
   demonstrate LO-05 or KO-09 macro behavior. Source: oracle smoke corpus and
   mutation description.

## Hash drift and reproducibility gap

The audit replay passes the relational smoke contract, but the three unique
documented JSON hashes drift. Parsed JSON changes from
`00b570...731f` to `0c69fe...2066`; context-prefix compiled JSON changes from
`62f1dd...82a1` to `a6dd75...3eb1`; full compiled JSON changes from
`fe95fa...3243` to `c78dc2...53a`. All three documented Kore hashes remain
exactly equal. Baseline A and B compare equal at all seven boundaries; the
mutation changes the expected six boundaries and leaves macros equal. Removing
every JSON field named `digest` in an audit-only comparison still leaves all
four JSON boundary pairs structurally different. The cause of the byte-hash
drift is unknown because the earlier raw bundle is not checked in. Exact data:
`hash-drift.json` and `evidence/smoke/smoke-report.json`.

## Unresolved oracle gaps by priority

1. G1 ingress/configuration cut and official egress: blocks all end-to-end G1
   acceptance.
2. G1 identity/provenance and patch atomicity: blocks both feature goals.
3. Raw parser/filter exports: prerequisite for honest C2 implementation.
4. Prepared-module and configuration-metadata snapshots: localize C1
   sort/injection/concretization work.
5. Negative/mutation corpora for validation, cache invalidation, options, and
   product status honesty.
6. A macro-bearing and proof-bearing fixture if those optional scopes are
   activated.
