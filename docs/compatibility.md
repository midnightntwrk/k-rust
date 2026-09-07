# Compatibility decisions

The port follows the combined Booster and Kore backend semantics described in [backend-port.md](backend-port.md).
When the engines, their frontend policies, or their recorded outputs disagree, the contracts below identify the intended Rust behavior and the evidence used to check it.
These contracts do not depend on development notes or local measurement logs.

The K reference is [`runtimeverification/k` at `4a46d1231473b599c699160132fd6e76a5c46406`](https://github.com/runtimeverification/k/tree/4a46d1231473b599c699160132fd6e76a5c46406), version `v7.1.337`, as recorded in [the differential manifest](../scripts/reference-differential.toml).
The backend reference is [`runtimeverification/haskell-backend` at `ad54c7a55085b726c4d3c2728242a7e0695b0439`](https://github.com/runtimeverification/haskell-backend/tree/ad54c7a55085b726c4d3c2728242a7e0695b0439).
Source paths below are relative to these pinned repositories.
Fixture provenance records the commands and pins used for committed outputs; a source explanation alone must not be presented as a live measurement.

## Backend scope

LLVM-specific runtime behavior, Bison parser generation, LLVM decision-tree warnings and LLVM coverage instrumentation are outside the Haskell-backend compatibility contract.
The conformance expectations retain each affected case or step with its concrete `llvm-only` reason.
An LLVM expected output cannot define the behavior of a hook that neither pinned Kore engine evaluates, or of a definition that `kore-parser --verify` rejects.
The [hook capability inventory](../crates/k-rust/tests/fixtures/hook-capabilities.toml) records implemented and unsupported operations.

A hook without an evaluator or applicable K equation must report an unsupported-hook error when every argument is constructor-like.
Symbolic applications remain unevaluated.
This follows the missing-evaluator checks in `kore/src/Kore/Equation/EvaluationStrategy.hs` and the port's completion contract; an exclusion must not turn the unsupported outcome into a successful execution.

## Frontend policy

The Rust backend uses K's Haskell policies for existential right-hand-side variables, variables bound through `requires`, and excluded module attributes.
`--backend haskell` is an alias for Rust, `--backend kore` is rejected, and `--backend llvm` uses LLVM frontend policies.
The reference checks are in `kernel/src/main/java/org/kframework/compile/checks/CheckRHSVariables.java` and `kernel/src/main/java/org/kframework/kompile/Kompile.java`.
[Definition checks](../crates/k-rust/tests/definition_checks.rs) exercise these acceptance boundaries.
Anywhere rules have the explicit supported-superset contract below.

## Anywhere rules

Rust accepts and executes anywhere rules, including inputs K's Haskell frontend rejects or removes.
Kore represents them with an `anywhere` symbol attribute and admits them in `kore/src/Kore/Equation/Validate.hs`; its equation evaluation supplies the semantic reference.
K's frontend restriction originated in the emission defect discussed in [K issue #2909](https://github.com/runtimeverification/k/issues/2909) and [PR #2998](https://github.com/runtimeverification/k/pull/2998), rather than a backend inability to evaluate the equations.

The `supported-superset` exclusion applies to expectations that demand frontend rejection or removal of anywhere rules.
It does not exempt their execution from verification or equation tests.
The differential manifest includes anywhere inference fixtures; compiling the reference with its `kore` frontend policy allows the emitted equations to be evaluated with `kore-exec`.
An LLVM execution result may still differ because LLVM matches a normalized anywhere symbol syntactically while Kore can match it through a simplified function equality; the corresponding conformance case records that separate limitation.

## Trivial rule results

A rule whose left-hand side matches and whose `requires` holds has applied even when `ensures false` or a bottom right-hand side makes its result empty.
Its matched region must be removed from the remainder available to lower-priority and `owise` rules.
This follows `kore/src/Kore/Rewrite.hs`, which computes the remainder from unification, and K's documented requirement that `owise` applies only when other rules fail to apply.
Booster's `OnlyTrivial` fall-through is excluded from the RPC differential for that shape.
[Rewrite tests](../crates/k-rust-backend/src/rewrite.rs), including `a_trivial_rule_shadows_lower_priority_rules`, cover concrete and symbolic remainders.

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

## Definition verification

The acceptance boundary follows `kore-parser --verify` even where Booster is more permissive.
Every axiom pattern must be well formed, including axioms ignored by later classification, and domain values require a sort declared with `hasDomainValues`.
Reflexive subsort axioms are accepted, as Kore accepts them.
The [definition fixture index](../crates/k-rust/tests/fixtures/reference/definition/index.toml) records pinned verification outcomes and diagnostic fragments.

## Search results

Search output uses deterministic structural KORE order; reproducing Kore's internal `MultiOr` ordering is not a compatibility requirement.
Differential gates compare disjunctions as multisets so ordering is ignored while multiplicity is still checked.
For `--bound N`, selected results must be distinct members of the same query's unbounded solution set, up to the bound; which members are selected is unspecified.
The CLI test `krun_search_bound_returns_a_subset_of_the_unbounded_solutions` checks this property against the port's own unbounded search.

The port retains every execution leaf when Kore's graph traversal drops `Stop` leaves in the presence of a `Remaining` leaf.
Normalization N17 limits the corresponding differential exception to marked depth-bounded cases and requires the reference leaves to remain a sub-multiset of the Rust leaves.
[Execution fixtures](../crates/k-rust/tests/fixtures/reference/execution) and the symbolic differential cover branch sets and depth cuts.

## CLI scope

`krust` retains its source-plus-flags interface.
The project does not implement K's compiled-directory runtime contract, K-derived module defaults, every K flag alias, or K's pretty-output and proof-verdict framing solely for tool interchangeability.
K tools and pyk serve as differential oracles; the conformance driver translates recipes into supported Rust operations.
An unknown or untranslatable flag must remain explicitly unsupported rather than being silently ignored.
The `declined-capability` category records steps requiring an interface with no Rust equivalent.
Semantic input selection, warning handling, execution status, and configuration initialization remain testable contracts; this policy does not exclude them.

## Comparison contract

[reference-normalisations.toml](../scripts/reference-normalisations.toml) is the authority for each permitted equivalence and exclusion.
Normalization identifiers such as N3 are durable names defined in that register, not work-item identifiers.

N3 permits only the counted multi-alias freezer family exclusion.
K's generated suffix assignment depends on unordered Scala context iteration, including `Source` and `Location` attributes; Rust retains deterministic declaration order.
Single-alias identities remain compared.
N23 applies the same limited policy to generated lambda families: `kernel/src/main/java/org/kframework/compile/ResolveFun.java` assigns suffixes in `localSentences` iteration order, whose sentence hashes include the source path.
The pinned `issue-1528`, `let-test` and `record-llvm` cases exhibit different suffix assignments from different checkout paths.
The comparator collapses multi-suffix names consistently in declarations and uses, ignores only the affected UNIQUE_ID attributes, compares the remaining sentence multiset, and prints the collapsed axiom count.
The tradeoff is explicit: a suffix-to-body association is outside this comparison, while signatures and rule bodies remain checked.

A `presentation-only` conformance exclusion requires an explanation of why the represented patterns are equal.
For example, `no-junk-macro` retains a valid constraint in Kore while Rust discharges it using the definition's own SMT lemma.
Normalization N15 may prove residual constraints equivalent by checking both implications, subject to the independence limitations in [testing.md](testing.md#comparator-evidence).
Different text or a successful Rust implication check alone must not establish implication correctness.

## Reference evidence

`reference-crash` means the reference supplied no expected behavior; `stale-oracle` means the pinned toolchain did not reproduce an upstream checked-in output.
Both remain visible and must be reconsidered when the reference pin changes.
Neither is evidence of a Rust pass, and locally regenerating an upstream output does not independently establish the contract.
`both-reject` permits different diagnostic presentation only after both toolchains reject the input; diagnostic classes remain separately recorded to expose rejection for the wrong reason.

The [conformance expectations](../scripts/conformance/expectations.toml) preserve measured revisions, result digests, accepted ranks and stages, and individual case or step reasons.
Historical digests identify measurements; they do not imply that their full temporary logs are distributed with this repository.
A new checkout can seed the versioned floor and measure selected cases using the commands in [testing.md](testing.md#manual-conformance-acceptance).

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
