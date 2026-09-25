# Compatibility decisions

The port follows the combined Booster and Kore backend semantics described in [backend-port.md](backend-port.md).
When the engines, their frontend policies, or their recorded outputs disagree, the contracts below identify the intended Rust behavior and the evidence used to check it.
These contracts do not depend on development notes or local measurement logs.

The K reference is [`runtimeverification/k` at `4a46d1231473b599c699160132fd6e76a5c46406`](https://github.com/runtimeverification/k/tree/4a46d1231473b599c699160132fd6e76a5c46406), version `v7.1.337`, as recorded in [the differential manifest](../scripts/reference-differential.toml).
The backend reference is [`runtimeverification/haskell-backend` at `ad54c7a55085b726c4d3c2728242a7e0695b0439`](https://github.com/runtimeverification/haskell-backend/tree/ad54c7a55085b726c4d3c2728242a7e0695b0439).
Source paths below are relative to these pinned repositories.
Fixture provenance records the commands and pins used for committed outputs; a source explanation alone must not be presented as a live measurement.

## Backend scope

LLVM-specific runtime behavior, the behavior of the external Bison/Flex parser generator, LLVM decision-tree warnings and LLVM coverage instrumentation are outside the Haskell-backend compatibility contract.
The CLI interoperability contract includes rendering parser sources, invoking the system Bison/Flex/C toolchain, installing executable or shared-library parser artifacts, and preserving their parser-output bytes; the Bison implementation itself remains external to Rust.
The conformance expectations retain each affected case or step with its concrete `llvm-only` reason.
An LLVM expected output cannot define the behavior of a hook that neither pinned Kore engine evaluates, or of a definition that `kore-parser --verify` rejects.
The [hook capability inventory](../crates/k-rust/tests/fixtures/hook-capabilities.toml) records implemented and unsupported operations.

Ordinary `kcompile --backend rust` output is directly runnable through `krun --definition DIR`.
The runtime validates the artifact identity, schema version, Rust backend identity, and every payload digest before use.
The CLI and Rust library are the compatibility boundary; individual files and their serialization inside the compiled directory may change between releases.
LLVM compilation does not publish a Rust runnable artifact.
The conformance driver retains LLVM output for its frontend comparison and accounts for one explicit, separate Rust compilation when execution steps need a runnable directory.

A hook without an evaluator or applicable K equation must report an unsupported-hook error when every argument is constructor-like.
Symbolic applications remain unevaluated.
This follows the missing-evaluator checks in `kore/src/Kore/Equation/EvaluationStrategy.hs` and the port's completion contract; an exclusion must not turn the unsupported outcome into a successful execution.

Ordinary committed execution implements the console operations `IO.getc` and `IO.read` on descriptor 0 and `IO.putc` and `IO.write` on descriptors 1 and 2.
Their input cursor and ordered descriptor transcript are branch-local, and rolled-back candidates cannot deliver bytes.
Input is pre-buffered before execution; live output is delivered exactly once from the selected `--strategy any` trace.
Other descriptors and IO hooks remain unsupported, pure simplification receives no console state, search rejects `--io on`, and RPC does not perform host IO.

## Frontend policy

The Rust backend uses K's Haskell policies for existential right-hand-side variables, variables bound through `requires`, and excluded module attributes.
`--backend haskell` is an alias for Rust, `--backend kore` is rejected, and `--backend llvm` uses LLVM frontend policies.
The reference checks are in `kernel/src/main/java/org/kframework/compile/checks/CheckRHSVariables.java` and `kernel/src/main/java/org/kframework/kompile/Kompile.java`.
[Definition checks](../crates/k-rust/tests/definition_checks.rs) exercise these acceptance boundaries.
Anywhere rules have the explicit supported-superset contract below.

## Variable sort annotations

A semantic cast `t:S` requires the sort of `t` to be less than or equal to `S` (K user manual, "Semantic casts"); on a variable this is an upper bound, in both inference engines.
The variable's sort is then inferred like any other variable's: the same sort at every occurrence, maximal among the solutions, so `rule bar(X:Big) => foo(X)` with `foo(Small)` gives `X` the sort `Small` and compiles to a pattern matching `bar` of an injection of a `Small` into `Big`.
To make an annotation exact, so that a narrower occurrence is a sort error, write the strict cast `X::S`.
The pinned K frontend rejects `semcast3` and `semcast4`, whose ambiguous `a(X)` has exactly one well-sorted reading under this bound; Rust accepts them with that reading, and the differential manifest records both as `excluded` with the Rust acceptance as the local gate.

## Compiler-resolved fresh constants

Within one rule or context, each distinct `!` variable receives a distinct consecutive offset from the generated counter and every occurrence of the same full variable name reuses that offset.
Rust assigns offsets in lexicographic order of the full names and advances the counter by the number of distinct names.
This deterministic association is Rust's stable compiler policy; portable programs must not depend on a particular association between names and offsets.
The policy must not depend on source paths or emulate the iteration order of Java's `HashSet`.

Distinct offsets, consistent reuse, and counter advancement are portable frontend properties.
Generated-value freshness additionally relies on the selected sort's `freshGenerator` contract.
Pinned K assigns names to offsets in unspecified `HashSet` iteration order, so its name-to-offset permutation is not a compiler oracle.
Each backend executes the permutation in its compiled definition; differing concrete values in ordered result positions must remain visible and must not be normalized as alpha-equivalent.
The `fresh-variables` compilation differential checks a case where the permutations happen to agree, while the focused Rust pass regression pins lexicographic allocation and repeated-name reuse.

## Anywhere rules

Rust accepts and executes anywhere rules, including inputs K's Haskell frontend rejects or removes.
Kore represents them with an `anywhere` symbol attribute and admits them in `kore/src/Kore/Equation/Validate.hs`; its equation evaluation supplies the semantic reference.
K's frontend restriction originated in the emission defect discussed in [K issue #2909](https://github.com/runtimeverification/k/issues/2909) and [PR #2998](https://github.com/runtimeverification/k/pull/2998), rather than a backend inability to evaluate the equations.

The `supported-superset` exclusion applies to expectations that demand frontend rejection or removal of anywhere rules.
It does not exempt their execution from verification or equation tests.
The differential manifest includes anywhere inference fixtures; compiling the reference with its `kore` frontend policy allows the emitted equations to be evaluated with `kore-exec`.
An LLVM execution result may still differ because LLVM matches a normalized anywhere symbol syntactically while Kore can match it through a simplified function equality; the corresponding conformance case records that separate limitation.

After equation normalization reaches a fixed point, the backend treats a term as concrete when every application head is either a constructor or an anywhere-attributed production without the `function` attribute.
This concrete-after-normalization classification is shared by rewrite instantiation, equation matching, overload lowering, and structural predicate simplification.
The simplifier may cache a closed normalized anywhere or overloaded application as evaluated only after a fresh scan has found every compatible equation inapplicable independently of the current path condition.
A symbolic application, a scan with an indeterminate equation, or an equation refuted under the current path condition must remain unevaluated.
An equality from the path condition that can replace any part of a cached term must be applied before the cache can short-circuit simplification.
Rewrite matching decomposes equal rigid heads and rejects a different rigid head, while matches against variables and ordinary function heads remain symbolic.
Equation matching lowers a concrete overloaded application through `symbol-overload` relations when every argument can lower to the corresponding lesser sort.
The most specific successful lowering supplies sort membership; a concrete application for which every compatible lowering fails refutes membership.
After compatible lowering, equation matching treats different productions in an overload family as distinct rigid heads when the subject is concrete after normalization.
An ambiguous lowering, a variable, or an ordinary function argument remains symbolic.
Structural equality rejects distinct normalized concrete terms only when their rigid heads differ or an injective equal head contains structurally distinct arguments.
This ground-program rule follows LLVM's executable semantics: K's Haskell frontend rejects these definitions, so Kore supplies no execution oracle for them.

## Concrete rewrite instantiation

When the entire initial term is constructor-like, applying a rewrite rule requires a substitution covering every free variable on its left-hand side.
Unification and `requires` simplification may supply those bindings; an unresolved variable must produce an explicit instantiation failure before applying the right-hand side or `ensures`.
An impossible match or false `requires` remains non-applicable.
The reference is `kore/src/Kore/Log/ErrorRewritesInstantiation.hs::checkSubstitutionCoverage`, called after initial-condition filtering in `kore/src/Kore/Rewrite/RewriteStep.hs::finalizeRule`.
Rust reports this unsupported instantiation as typed indeterminacy, so execution and search retain an incomplete outcome instead of inventing existential successors or treating the rule as non-applicable.

The boundary is concreteness of the whole normalized term.
This includes Kore constructor-like terms and extends them for the supported anywhere superset, so a variable-free normalized anywhere or overloaded application does not make a ground configuration symbolic.
A variable below such an application keeps the configuration symbolic.
A ground function-headed term can still narrow, and symbolic configurations retain fresh rule arguments and their existentially quantified complementary conditions.
Anywhere equation evaluation, overload lowering, and covered function-equality matching remain supported before this boundary is applied.
The [rewrite coverage fixture](../crates/k-rust-backend/tests/fixtures/rewrite-coverage.kore) and [rewrite tests](../crates/k-rust-backend/tests/backend/rewrite.rs) exercise this boundary, false and binding requirements, equation normalization, and symbolic complements.

## Trivial rule results

A rule whose left-hand side matches and whose `requires` holds has applied even when `ensures false` or a bottom right-hand side makes its result empty.
Its matched region must be removed from the remainder available to lower-priority and `owise` rules.
The K manual fixes both halves: the `requires` clause decides whether a rule applies, while the `ensures` clause is a post-condition that "may cause the entire term to become undefined, but the backend will not stop itself from applying the rule in this case" (`docs/user_manual.md:1153-1164`, "Rule Structure"); an `owise` rule applies "only if all the other rules have been tried and failed", after they have "been shown not to apply" (`docs/user_manual.md:1711-1722`, "`owise` and `priority` attributes").
A rule with an empty result has not failed, so for the matched region the result of the step is empty: `krun` prints `\bottom` and the RPC `execute` answers `vacuous`, never a successor of a lower-priority rule.

This is a recorded divergence from `kore-rpc-booster`, whose Booster rewriter continues with the next priority group when every applicable rule of a group has an empty result (`OnlyTrivial` in `booster/library/Booster/Pattern/Rewrite.hs::rewriteStep`).
The `trivial-result-rpc` differential case compares both answers with the pinned proxy.
Its `execute-trivial` request is krun's depth-0 state, whose initializer functions Booster does not rewrite, so the proxy answers it through its Kore fallback and both sides answer `vacuous`.
Its `execute-trivial-configuration` request sends the evaluated configuration `<k> a </k>`, which Booster rewrites itself: Booster answers `depth-bound` at depth 1 with the `owise` successor `<k> c </k>`, and k-rust answers `vacuous` at depth 0.
That response is the case's `rpc.oracle-exception` row in the [differential manifest](../scripts/reference-differential.toml): the gate fails when k-rust's answer leaves the committed expectation or when the proxy's answer becomes equal to it, and the proxy's measured answer is kept beside the expectation in the [RPC fixtures](../crates/k-rust/tests/fixtures/reference/rpc).
[Rewrite tests](../crates/k-rust-backend/tests/backend/rewrite.rs), including `a_trivial_rule_shadows_lower_priority_rules`, cover concrete and symbolic remainders.

## Hook specification exceptions

The hook contract is K's [`k-distribution/include/kframework/builtin/domains.md`](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/k-distribution/include/kframework/builtin/domains.md).

- `MAP.inclusion` compares complete entries: each included key must have the same value in the other map. Kore follows this contract; Booster's key-only check does not.
- `STRING.find` reports an index in the original haystack. The pinned Kore `kore/src/Kore/Builtin/String.hs` searches the suffix without rebasing the result.
- `BYTES.replaceAt` requires the entire replacement range to fit in the original bytes. The pinned Kore `kore/src/Kore/Builtin/InternalBytes.hs` checks only the start index.

Rust retains the specified behavior for all three operations.
The [hook fixtures](../crates/k-rust/tests/fixtures/reference/hooks) and `execution.oracle-exception` entries in the differential manifest preserve separate Rust and Kore expectations for the two Kore deviations.
Normalization N18 checks both expectations independently; when a pin fixes the deviation, refresh the reference evidence and remove that exception.

## RPC behavior

A predicate-free `get-model` request returns `Unknown` without a substitution.
Both `booster/library/Booster/JsonRpc.hs` and `kore/src/Kore/JsonRpc.hs` contain this no-predicate outcome.
A proxy response of `sat` must not override this contract without establishing whether the proxy classified the same input as carrying a predicate or definedness obligation.

A `cancel` request inside a batch returns `-32601`, `Cancel not supported`, following the shipped proxy; an empty batch returns `-32600` with data `[]`.
The older server API document is not authoritative for these measured wire details.
Execution retains an explicit `aborted` reason for incomplete indeterminate, simplification-error and breadth-bound outcomes because Rust has no fallback engine to hide the failure.
[RPC tests](../crates/k-rust/src/rpc.rs) cover predicate-free models, batch cancellation, and error classification; [RPC fixtures](../crates/k-rust/tests/fixtures/reference/rpc) preserve shipped-proxy responses.
An `execute` response lists `next-states` in application order with the remainder last; the order is not part of the contract and the differential gate compares the array as a multiset (N27).
Backend error `data` is compared by class: code, message, and the `error` sentence; context lines are the port's own diagnostics (N28).
An `implies` request is the statement `A -> \exists E. C` under the universal closure of the free variables of `A` and `C`, with `E` the consequent's leading existentials.
A free variable of the consequent that the antecedent does not mention is therefore universal, not an error: the match binding `u := s` of any universal is an obligation `u = s` that the antecedent's condition must entail.
The universal ranges over the values of its sort in the models of the definition, so the answer is `valid` when every such value the antecedent allows satisfies the obligation: when the antecedent is unsatisfiable, when nothing constrains the variable, or when the definition's no-junk axiom for the variable's sort (its `constructor` axiom) leaves `s` as the only value, as for a sort whose one constructor is nullary.
The solver treats a user sort as uninterpreted and does not see the no-junk axiom, so in that last case it reports a counterexample; when the solver does not answer `valid`, the check simplifies `A /\ u =/= s`, and if `u =/= s` excludes every constructor the axiom lists, that conjunction is a contradiction and the answer is `valid`.
The answer is `invalid` when the antecedent is satisfiable and neither the solver nor that simplification of `A /\ u =/= s` rules out a value of `u` that violates the obligation; a sort without a no-junk axiom has such values even if the definition declares a single constructor for it.
An antecedent existential that shares the consequent universal's name is a different variable and is renamed apart.
The RPC differential records this as the `bounded-search` `implies-consequent-universal` oracle exception (N19): with the ground start configuration as antecedent and its `<k>` item replaced by `X:SortState` as consequent, k-rust answers `invalid` with the binding `X = start`, and the pinned proxy answers error code 4, `Implication check error`, "The RHS must not have free variables not present in the LHS".

An `implies` response reports its antecedent and consequent after simplification, the patterns the verdict was decided on ([`simplified_implication_response_syntax`](../crates/k-rust/src/rpc.rs)); a simplification failure is reported as a `simplify` fault rather than as an unsimplified pattern beside a verdict computed from the simplified one.
Simplification replaces a pattern by an equal one, so the payload denotes the requested implication.
The pinned Booster proxy echoes the request's patterns instead; for the IMP request that is an unevaluated `initGeneratedTopCell` application where k-rust reports the configuration it evaluates to.
The `rpc.imp` `oracle-exception` records that difference with `equivalence = "simplified-implication"`, and N19 checks the claimed equality rather than asserting it: the two responses must be equal outside the payload, and both payloads' antecedents and consequents, simplified by `krust kore-simplify` against the reference definition, must print identically.
Like C8, that evidence depends on the port's simplifier.

## Definition verification

The acceptance boundary follows `kore-parser --verify` even where Booster is more permissive.
Every axiom pattern must be well formed, including axioms ignored by later classification, and domain values require a sort declared with `hasDomainValues`.
Reflexive subsort axioms are accepted, as Kore accepts them.
The [definition fixture index](../crates/k-rust/tests/fixtures/reference/definition/index.toml) records pinned verification outcomes and diagnostic fragments.

## Search results

Search output uses deterministic structural KORE order; reproducing Kore's internal `MultiOr` ordering is not a compatibility requirement.
The order is `k-rust-kore`'s `Pattern` order (variant declaration rank, then fields in declaration order, byte-wise strings) and may change between releases.
Differential gates compare disjunctions as multisets so ordering is ignored while multiplicity is still checked.
For `--bound N`, selected results must be distinct members of the same query's unbounded solution set, up to the bound; which members are selected is unspecified.
The CLI test `krun_search_bound_returns_a_subset_of_the_unbounded_solutions` checks this property against the port's own unbounded search.
Which successor `--strategy any` follows among equal-priority rules is likewise unspecified; the differential gate checks that the port's any-strategy result is a member of the reference all-strategy set (N26).
The port follows the first applicable rule in priority order, then `definition.kore` declaration order (main module first, imports depth-first in their written order); which rule the reference follows is engine-internal.
Among several collection matches of that rule, the port follows the first candidate in deterministic structural order; which candidate the reference follows is engine-internal.
The RPC `next-states` array is a set of successors and is compared as a multiset (N27).

The port retains every execution leaf when Kore's graph traversal drops `Stop` leaves in the presence of a `Remaining` leaf.
Normalization N17 limits the corresponding differential exception to marked depth-bounded cases and requires the reference leaves to remain a sub-multiset of the Rust leaves.
[Execution fixtures](../crates/k-rust/tests/fixtures/reference/execution) and the symbolic differential cover branch sets and depth cuts.

## CLI scope

`krust` retains its source-plus-flags interface.
For source-driven `krun`, the syntax or configuration parser module supplies the concrete grammar and the selected main module supplies the executable production catalog and visible macro sentences.
Parsed applications must rebase into the main catalog before macro expansion, sort injection, and KORE conversion; an absent source-catalog production index may be discarded only from a self-describing token, whose lexical hook is read from the parser module before falling back to the main module.
Macro expansion uses the frontend's KAST-domain expander after rebasing and before conversion to executable KORE; `kast` retains its separate unparsing-module scope.
A macro- or alias-headed term that survives expansion is invalid executable input and must be rejected before the first rewrite step rather than narrowed as an ordinary function application.
The backend also rejects such a head defensively when a direct caller bypasses the CLI validation.
The project provides its own versioned compiled-directory runtime contract rather than K's file format; it does not implement K-derived module defaults, every K flag alias, or K's pretty-output and proof-verdict framing solely for tool interchangeability; its own verdict words are defined under [Proof verdicts](#proof-verdicts).
K tools and pyk serve as differential oracles; the conformance driver translates recipes into supported Rust operations.
An unknown or untranslatable flag must remain explicitly unsupported rather than being silently ignored.
The `declined-capability` category records steps requiring an interface with no Rust equivalent.
Semantic input selection, warning handling, execution status, and configuration initialization remain testable contracts; this policy does not exclude them.
The source-plus-flags interface includes standalone Bison parser generation and executable or shared-library parser artifacts, while relying on the system Bison, Flex, and C compiler rather than implementing those tools in Rust.

`krun --output captured` is an explicit ordinary-execution mode for definition-computed console output.
It uses buffered `--io off` stream semantics with pre-buffered standard input, requires exactly one complete unconstrained terminal execution leaf and exactly one structurally identified stdout stream buffer, writes that buffer to process stdout once, and suppresses KORE rendering.
Bottom, constrained or multiple leaves, incomplete execution, malformed stream state, search, surface result matching, and an explicit `--io on` are errors.
`krun --io on --output none` is the corresponding committed live mode with pre-buffered input and byte-exact descriptor 1/2 delivery.
Default KORE output remains unchanged.

## Proof verdicts

`krust kprove` prints one verdict word per selected claim: `proven`, `disproved`, `failed`, `indeterminate`, `depth bound` or `breadth bound`.
The Node.js and WebAssembly `status` field uses the same words, with `depth-bound` and `breadth-bound`.
The [README kprove section](../README.md) lists them with the leaf listing each word prints.
A word is a statement about the claim; the process exit status is only a summary of several claims: 0 exactly when every selected claim is `proven`, 1 otherwise with `one or more reachability claims were not proven`.

This differs from the pinned `kprove`, which reports only whether the backend proved every claim.
It prints `backend terminated because the configuration cannot be rewritten further` whenever the backend exits with status 1 (`k-frontend/src/main/java/org/kframework/kprove/KProve.java`), and the pinned `kore-exec` exits with status 1 whenever its result lists any claim it did not prove (`kore/app/exec/Main.hs`, `koreProve`).
The message therefore states that a claim was not proven; it does not state that the claim is false.
k-rust separates the two because a consumer acts on the word: a `disproved` claim cannot be proven by any strategy and needs a changed claim or definition, while a `failed` claim may be true, for example a vacuous claim or a one-path claim whose search took a rule that leads nowhere.
Reporting a true claim as false is a wrong result, not a presentation difference.

A claim `φ => ψ` is refuted, under the manual's [one-path](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md#one-path-interpretation) and [all-path](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md#all-path-interpretation) readings ("there exists a path", "all paths ... will reach"), by a configuration of `φ` that, for an all-path claim, has a path ending in a configuration with no successor without passing through `ψ`, or, for a one-path claim, has no path to `ψ`.
`disproved` requires a leaf that shows this, a certified stuck leaf (`Stuck (certified)` in the listing), which must meet all of the following conditions:

- (a) No successor: the rewrite step on the leaf is stuck.
  A state the search stopped without rewriting, such as a stuck-check stop, is stepped once and is certified only if that step is stuck, because a configuration that can still move may reach `ψ` later.
- (b) Every path followed: the claim is all-path, or its one-path trace kept every successor.
  A one-path claim is false only if no path reaches `ψ`, and a trace that took one of several applicable rules says nothing about the others.
  The sequential rewriter does not report whether a step dropped an applicable alternative, so every one-path rewrite step counts as one that may have, and a one-path leaf is certified only when its trace has no rewrite step.
- (c) No claim step: no circularity or trusted claim on the trace.
  Such a step replaces paths by an assumed claim instead of following them, so the leaf shows at most that the assumption and the claim cannot both hold.
- (d) Non-empty outside the destination: the leaf term applies no function symbol (it may hold constructors, domain values and variables) and is not a conjunction of terms at its top, and the leaf constraints together with the definedness of its term hold syntactically, or are satisfiable by an SMT query that approximates nothing (only `Int` and `Bool` variables, no abstracted subterm, no partial function).
  A leaf denoting the empty set refutes nothing, an unevaluated function application may denote no value or a value the destination accepts, and a satisfiable abstraction may be spurious.
  The leaf constraints carry the complement of every destination condition checked on the trace, including the uncovered part of a state that the destination condition covers only in part; the complement places the leaf outside `ψ` only if every destination check on the trace ran and was decided.

Every other stuck leaf, and every empty leaf the vacuity policy rejects (`Trivial`, `Vacuous`), makes the claim `failed`: the search stopped there without establishing that the claim is false.
When leaves disagree, the first of `disproved`, `failed`, `indeterminate`, `depth bound`, `breadth bound` applies.
The conditions are sufficient, not necessary: a false claim whose refutation k-rust cannot certify is reported `failed`, never `disproved` without evidence.
The conformance driver compares kprove recipes only as proven, not proven or error (`kprove_verdicts` in `scripts/conformance/run.py`), so `disproved` and `failed` are the same outcome there.

[reference-proof-differential.sh](../scripts/reference-proof-differential.sh) runs each `[[proof]]` entry's `failure-claim` through both toolchains.
It requires the reference `kprove` to exit with the message above and k-rust to print `claim <failure-claim>: disproved`; N12 omits the counterexample framing from that comparison.
The reference observation supplies only the fact that the claim is not proven.
The `disproved` expectation is k-rust's own stronger statement: it is valid for an entry only when the failure claim is false and k-rust's leaf for it meets (a)-(d), and the gate passing shows the leaf was certified, not that the reference refuted the claim.
`mini-proof`'s `claim-refuted`, the all-path claim `<k> start => stuck </k>` over a definition whose only rules are `start => middle` and `middle => done`, meets them: its leaf is `<k> done </k>` with no constraint, reached by the only path and without a successor.
A failure claim that is not false cannot carry the `disproved` expectation, and its entry must record its own expectation with the reason.

## Driver scope

The conformance driver translates each upstream `ktest` recipe into krust operations and compares their outcomes.
A plain `krun --output none` recipe with a non-empty expected console output runs under `--io off` and compares the stdout stream buffer of its single unconstrained execution leaf with that output under C9; it does not require host console effects from the backend.
An explicit `--io on` recipe compares the committed console stdout bytes directly with its expected output.
When C9 proves that buffered stdin cannot reproduce an implicit recipe's tokenization, the driver retains the attributed C9 result and re-runs that recipe under pre-buffered `--io on --output none`; only the live bytes decide that step.
A recipe that defines no translatable step supplies no oracle: a `ktest-kdep.mak` or sub-make-only Makefile, a Makefile whose `ktest.mak` include is disabled upstream, a recipe that discards the output it would compare, or an expected kompile failure that leaves no definition for a later step.
The `undriven-recipe` category records such cases with the concrete recipe feature; the skip is not evidence of a Rust pass and must be reconsidered when the driver learns to translate the feature.

Every case whose accepted verdict is not `match` carries exactly one of two dispositions.
A non-empty `exclusion` names the category whose section here justifies leaving the difference, and the inline `reason` states the concrete feature or decision for that case; the justification is complete in this repository.
An empty `exclusion` with a non-empty `reason` records a measured port or driver gap that is pending work; the work itself is tracked outside this repository, and [testing.md](testing.md#manual-conformance-acceptance) describes how a local backlog is audited against the measurements.

## Comparison contract

[reference-normalisations.toml](../scripts/reference-normalisations.toml) is the authority for each permitted equivalence and exclusion.
Normalization identifiers such as N3 are durable names defined in that register, not work-item identifiers.

N3 permits only the counted multi-alias freezer family exclusion.
K's generated suffix assignment depends on unordered Scala context iteration, including `Source` and `Location` attributes; Rust retains deterministic declaration order.
The frontend orders catalogs, emitted sentences, and checks by dependency-first declaration order; no Scala `Ordering` is reproduced.
Sentence identity for deduplication (`sentence_equivalent`) keeps K's `Sentence` equality.
Single-alias identities remain compared.
N23 applies the same limited policy to generated lambda families: `kernel/src/main/java/org/kframework/compile/ResolveFun.java` assigns suffixes in `localSentences` iteration order, whose sentence hashes include the source path.
The pinned `issue-1528`, `let-test` and `record-llvm` cases exhibit different suffix assignments from different checkout paths.
The comparator collapses multi-suffix names consistently in declarations and uses, ignores only the affected UNIQUE_ID attributes, compares the remaining sentence multiset, and prints the collapsed axiom count.
The tradeoff is explicit: a suffix-to-body association is outside this comparison, while signatures and rule bodies remain checked.
Variable numbering inside a generated owise competitor disjunction is the port's own; N4 renames it on both sides.
The conformance driver's surface-text comparison (`scripts/conformance/run.py` `execution_text_diff`) applies the same N4 reading to kprint's `?Name:Sort` tokens as C7: the rule existentials both engines instantiate through a fresh counter are compared modulo a bijective, sort-preserving renaming by first occurrence per disjunct, applied before the C1 sort.
Every other variable, including the search pattern's own variables and any `?` variable the recipe's `--pattern` text names, and every string literal are compared literally, so lost sharing, a changed sort, or a renamed pattern variable remains a mismatch.
When that text comparison fails, C8 (`compare_simplified_kore`) re-runs the reference recipe with `--output kore`, simplifies that result and the krust result with `krust kore-simplify` against the reference kompiled definition and main module, and compares the two simplified patterns with the structural execution comparator without `K_DIFFERENTIAL_DEFINITION`, so N4 renaming applies and N15 does not.
The pinned reference prints a rewrite result before its own simplification is complete: `no-junk-macro` retains a constraint that the definition's own `smt-lemma` makes valid, and `concrete-function` leaves `foo(inc(sym2(?X)))` unevaluated because the argument's definedness is open, while the port discharges the constraint and applies the equation under a `\ceil` obligation that the surrounding constructor context already entails.
Both pairs are equal patterns; simplifying both with one simplifier makes them comparable.
A step that matches only this way records the C8 comparison label and the text difference, never plain match text; the checked-in `.out` stays the oracle, so the re-run's result must still print as the `.out`.
A simplification or comparison that fails or is unavailable leaves the text mismatch in place; a reference re-run that produces no result records `reference-error` with the reference's stderr, which is an oracle change and not evidence for either side.
C8 is supplementary evidence in the sense of [testing.md](testing.md#comparator-evidence): it depends on the port's simplifier, like N15.

C9 compares the bytes a tutorial definition accumulates in its stdout stream buffer under `--io off` with the checked-in output of the corresponding `--output none` recipe.
The comparison requires exactly one execution leaf in total, that leaf to be unconstrained, and exactly one structurally identified `#ostream(1)`, `"off"`, `#buffer(S)` stream.
Any residual leaf, multiple terminal leaves, and malformed stream configurations are mismatches and remain reported.
The tutorial stream rules append the same strings in both IO modes and make the `on` mode's `IO.write` hook only a transport for those bytes; K itself selects `off` for search and debug executions.
For input programs, C9 applies only where krust's buffered stdin is the piped input and K's stream rules tokenize those bytes as they tokenize the recipe's interactive stream.
When krust attributes an undefined result to a `STDIN-STREAM` rule and the input begins with a parse delimiter or contains adjacent parse delimiters, the driver records that C9 precondition failure and drives the implicit recipe under committed pre-buffered `--io on`.
This comparison remains independent of the captured output mode: C9 extracts the KORE result through its own structural helper and does not invoke `krun --output captured`.
C9 also remains independent of live delivery: the normal tutorial measurements continue to use its definition-computed buffer, while only a proved C9 input-precondition failure selects the separate committed transcript path.

A text difference that neither C8 nor N15 can compare stays a mismatch with a measured reason; no prose exclusion category exists for it.
Normalization N15 may prove residual constraints equivalent by checking both implications, subject to the independence limitations in [testing.md](testing.md#comparator-evidence).
Different text or a successful Rust implication check alone must not establish implication correctness.

## Reference evidence

`reference-crash` means the reference supplied no expected behavior; `stale-oracle` means the pinned toolchain did not reproduce an upstream checked-in output.
Both remain visible and must be reconsidered when the reference pin changes.
Neither is evidence of a Rust pass, and locally regenerating an upstream output does not independently establish the contract.
The driver records a reference tool that fails to produce a result as `reference-error` with its stderr, and a reference result that differs from the checked-in output as a stale oracle; the two are never merged.
`both-reject` permits different diagnostic presentation only after both toolchains reject the input; diagnostic classes remain separately recorded to expose rejection for the wrong reason.

The [conformance expectations](../scripts/conformance/expectations.toml) preserve measured revisions, result digests, accepted ranks and stages, and individual case or step reasons.
Historical digests identify measurements; they do not imply that their full temporary logs are distributed with this repository.
A new checkout can seed the versioned floor and measure selected cases using the commands in [testing.md](testing.md#manual-conformance-acceptance).

## Proof gate verdicts

The kprove verdict words are defined in the [README kprove section](../README.md): `disproved` is reserved for a certified refutation, and `failed` covers a failing leaf that does not show the claim false, including an empty leaf that the vacuity policy rejects.
[reference-proof-differential.sh](../scripts/reference-proof-differential.sh) requires every case's failure claim to be rejected by both toolchains, and requires k-rust's verdict word to be the case's `failure-verdict` in [reference-differential.toml](../scripts/reference-differential.toml): `disproved` unless the entry says otherwise, in which case `failure-verdict-reason` states why the claim is not false.

`trivial-proof` expects `failed` for `TRIVIAL-SPEC.ct2`, the all-path claim `<k> t1 => t3 </k>`.
The definition's only rule for `t1` is `t1 => t2 ensures false`; its result is empty, so it states that `t1` has a successor in the empty set, which holds of no configuration.
The claim's left-hand side is therefore empty, and the claim holds vacuously; nothing refutes it.
k-rust reaches a `Trivial` leaf, which the vacuity policy rejects as `failed`, and `--allow-vacuous` proves the claim.
The reference toolchain's rejection of the claim remains checked as the case's oracle observation; k-rust's `failed` verdict records that this rejection is not a refutation.

## Proof oracle incompleteness

A `reference-incomplete-port-proves` exclusion needs a soundness argument for the particular claim: a Rust `proven` result alone cannot justify departing from a reference refutation.
The pinned K cases are under [`k-distribution/tests/regression-new/spec-rule-application`](https://github.com/runtimeverification/k/tree/4a46d1231473b599c699160132fd6e76a5c46406/k-distribution/tests/regression-new/spec-rule-application).
Their `def.k` defines `incPos(X) = X + 1` when `X >= 0`, and the only ordinary transition is `start X => mid X`.

For `def61-spec.k`, after that transition choose trusted-claim variables `Y1 = X1` and `Y2 = X2 - 1`.
The subject requires `X1 >= 0` and `X2 - 1 >= 0`, so `incPos(Y1) - Y1 - 1 = 0` and `incPos(Y2) = X2`.
Both components of the trusted claim's `binop` therefore match the subject, and its right-hand side is exactly the destination `end X1` with the same variable cell.

For `def81-spec.k`, choose `Y1 = X + 1` and `Y2 = X + 2` after the initial transition.
The subject requires `X >= 0`, hence `incPos(Y1) - 1 = X + 1`; also `Y1 - 1 = X`, `Y2 - 1 = X + 1`, and the trusted claim's condition `Y2 = Y1 + 1` holds.
The trusted claim reaches exactly the specified destination without an uncovered remainder.
The upstream test plan's parts 6 and 8 explain evaluation under constraints; the plan also says part 8 passed an older simplification algorithm, so it does not by itself establish the current pinned backend's outcome.
The individual step exclusions retain the observed oracle mismatch separately from these substitution arguments.
