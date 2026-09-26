# M3D authored-surface ledger

This ledger compares the pinned M3D oracle with the intended Rust-authored
package. It is a compiler contract, not a claim that the current facade
implements these forms. The always-on declarations live in `surface/src/lib.rs`
and currently fail first at the `term!` subject of `add_one`. The namespaced
`k::equation` attribute is not collected, so it does not intercept that
compiler-owned pattern before the ordinary placeholder macro expands; rustc
therefore reports `this macro call doesn't expand to a pattern`. This is the
observable diagnostic for the missing equation path, not evidence that the
term notation itself is the requested compiler feature.

## Provenance and staging

The green package uses `src/m3c.rs`, a byte-identical copy of
`tests/m3c/rust-definition/src/lib.rs`. At authoring time both files have
SHA-256:

```text
8703da529c7e2049f16cadb262f36d1c5f190064c4fd7346f45009ae327c5b3f
```

The nested package has its own `[workspace]`, so Cargo does not pull its
intentional compile failure into the green root. The M3C source is included as
a module there before the M3D additions; no raw-K, generated descriptor,
feature gate, or `cfg` fallback stands in for an unsupported declaration.

## Adjunct sentence ledger

| Oracle sentence | Exact oracle semantics | Authored declaration | Current facade request |
|---|---|---|---|
| `addOne` production | `function`, `total`, `symbol(addOne)` | `#[k::function(total, sort = Int, syntax = ...)]` | Functional production schema, totality, explicit result sort/syntax, stable symbol lowering |
| `nonnegativeIdentity` production | partial `function`, `symbol(nonnegativeIdentity)` | `#[k::function(partial, ...)]` | Partiality must remain bottom when no equation applies; it is not `Option` |
| `priorityChoice` production | `function`, `total`, `symbol(priorityChoice)` | `#[k::function(total, ...)]` | Same functional-production path as `addOne` |
| `add-one` | unconditional equation | `#[k::equation] add_one` | Equation sentence kind and function-root validation |
| `nonnegative-identity` | equation requiring `0 <=Int I` | `#[k::requires(...)]` plus `#[k::equation]` | Reuse object-`Bool` condition checking; preserve equation scope |
| two `priority-choice-*` rules | priorities 40 and 80 | two `#[k::priority]` equations | Preserve explicit equation priority; do not infer source order |
| `zeroAlias` production/clause | alias symbol and reversible static expansion | `#[k::alias]` on production and clause | Alias production mode, static-clause IR, compile/init expansion, reverse unparse expansion |
| `operandEval` | `<k> HERE ... </k>` context alias | `#[k::context_alias(name = ..., here = ...)]` | Named template, HERE binder, configuration framing, zero-return validation |
| `double` production | `seqstrict(operandEval; 1)` | selected `#[k::seqstrict(using = ...)]` | Resolve alias group and named field; generate exactly one heat/cool pair using that template and `KResult` |
| `double` | integer doubling rule | ordinary `#[k::rule]` | Existing transition form; infer/refine the selected `Expr` child to `Int` from builtin use |
| five adjunct claims | concrete all-path reachability | five `#[k::claim(all_paths)]` clauses | Claim sentence kind, modality, framed pre/post configuration lowering |

The reference parser exposes five local productions in
`KRS-M3D-STATIC-SYNTAX`, six local rules in `KRS-M3D-STATIC`, and a parser
`badsentence` for the context alias. The compiled syntax module instead has
one `KContext` and the five productions. Generated selected strictness must
therefore be counted after compilation, where this fixture yields one heat
rule and one cool rule.

## Upstream verification ledger

| Surface | Binders and conditions | Authored status |
|---|---|---|
| four `IMP-VERIFICATION` normalizations | ordinary universal `Int` operands; no conditions | Fully spelled as four `#[k::simplification]` clauses |
| `addition-1` | no binders or conditions | Fully spelled as `addition_one` |
| `addition-var` | universal `N:Int`; requires `N ==Int 4` | Fully spelled as `addition_var` with an object-`Bool` requirement |
| `branching` | anonymous source `_B:Bool`; RHS existential `?N:Int`; Boolean disjunctive ensures; K/map/configuration frames; concrete `$n` token | Deferred: each relevant notation is designed, but concrete `Id` token authoring is absent and the combined lowering has no implemented schema |
| `sum-loop` | universals `S:Int`, `N:Int`; requires `0 <=Int N`; K/map rewrites; concrete `$s` and `$n` tokens | Deferred until concrete `Id` token literals and claim map rewrites have one settled authored spelling |
| `sum-spec` | universals `N:Int`, `S:Int`; requires `N >=Int 0`; circularity; K/map rewrites; concrete `$n` and `$s` tokens | Deferred for the same token/rewrite gaps and because circular-claim notation is not frozen |
| `addition-depth-zero` | the same `addition-1` claim run with proof depth zero | No extra authored sentence: this is a proof-invocation frontier, not a distinct claim |

Deferred does not mean weakened. In particular, the package does not replace
`?N` with a universal, name anonymous `_B` as an ordinary source variable,
erase `requires`/`ensures`, drop map frames, or encode circularity as a comment.

## Required public API and schema

The first implementation slice needs to expose and collect these attribute
families without routing through `rule`:

```text
function(total|partial, sort = S, syntax = "...")
equation
priority(integer)
alias                       # production and static clause
context_alias(name = id, here = binder)
seqstrict(using = id, sequence = [field...], result = Sort)
simplification[(priority = integer)]
claim(all_paths|one_path)
```

The normalized IR must keep distinct production mode and sentence-kind enums.
At minimum it needs functional totality, result sort, syntax/symbol identity,
equation conditions and priority, alias direction/mode, a context template and
HERE binder, strictness-to-alias references, simplifier priority, claim
modality, and binder kind/scope. Reusing transition priority for simplifier
priority or emitting claims as rules would be a semantic error.

The already designed follow-on binders and conditions are
`exists`, `forall`, `set_vars`, `fresh`, object-`Bool` `requires`/`ensures`,
and `and_bool!`/`or_bool!`. Claim lowering must quantify ordinary source
bindings universally, put `exists` at the RHS claim scope, keep anonymous
source binders anonymous, and preserve K/map/configuration frames.

Still-unsettled source spelling is intentionally limited to:

- explicit labels on equations, aliases, simplifications, and claims;
- concrete builtin `Id` token literals such as `$n` and `$s`; and
- circular reachability metadata (`#[k::circularity]` versus a claim modifier).

The compiler should not guess these spellings from Rust function names.

## Recommended vertical order

1. Land one total functional production plus one unconditional equation:
   `addOne(I) = I +Int 1`.
2. Add partial functions and object-`Bool` equation requirements.
3. Add equation priorities without conflating them with source order.
4. Add alias production/clause collection and reversible static lowering.
5. Add context aliases and `seqstrict(using = ...)`, asserting one heat/cool
   pair for `double`.
6. Add simplification as its own sentence kind.
7. Add claim modality and framed pre/post lowering, then the remaining binder,
   token-literal, ensures, map-rewrite, and circularity surface.

Each slice should advance the nested package's first diagnostic. The root
package must stay green throughout so the frontier cannot hide a regression in
the closed M3C surface.

At this baseline, `cargo check --locked` on the nested package exits 101 with
18 diagnostics. In addition to the first equation-pattern failure, the cascade
shows orphan `requires` helpers, unconsumed claim/context `cells!` patterns,
the unsupported `seqstrict(using = ...)` argument, and unconsumed
simplification term patterns. Those later messages are expected consequences
of absent outer sentence collectors; they are not eighteen independent fixes.
