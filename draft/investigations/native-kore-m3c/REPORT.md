# Native/reference M3C KORE structural delta

## Result

The metadata-normalized mismatch is exhaustive and has only four causes. No
constructor, sort, injection, strictness heat/cool rule, builtin axiom, or
authored rewrite body remains different after the corresponding compatibility
normalizations.

Inputs inspected:

| Input | SHA-256 |
|---|---|
| Java-reference `tests/m3c/rust-definition/target/krs/m3c-kompiled/definition.kore` | `e9ed8e82ca2687e999ce0a59d8665223683e8fdc6f81ca2a0ef2b23878a97fb3` |
| native `/dev/shm/krs-native-artifacts/m3c/definition.kore` | `1257fbfd8608cf4ef287368ca2d25460133ca7c983cc06d377e295fc4898016c` |

The existing normalizer removes `Location`, `Source`, `UNIQUE_ID`,
`contentStartLine`, and `digest`, sorts remaining attributes, and canonicalizes
only `_GenN`/`_DotVarN` suffixes. Its result is:

```text
reference=1069 actual=1147 missing=27 extra=105
```

These are sentence-multiset counts. All differing canonical sentences have
multiplicity one.

## Exhaustive partition

| Missing | Extra | Cause | Classification |
|---:|---:|---|---|
| 18 axioms | 18 axioms | Alpha-equivalent expression rules use Java's encoded source-variable names versus native authored names; two rules also use anonymous `_Gen` versus a native explicit wildcard name | Expected compatibility-policy normalization |
| 8 axioms | 8 axioms | Configuration-rule bodies become identical after alpha-renaming, but reference labels are module-qualified and native labels are not | Adapter shape |
| 1 axiom | 1 axiom | `var` has the same label issue and reference-only `cool-like` | Native frontend finalization divergence after adaptation |
| 0 | 39 symbols | Native named-field projector functions | Adapter-shape-induced conservative extension |
| 0 | 39 axioms | One defining equation for each native named-field projector | Adapter-shape-induced conservative extension |
| **27** | **105** | | |

The 18 expression rules are:

```text
add, and-false, and-true, div, eq-Bool, eq-Int, ge, gt, le, lt,
mul, ne-Bool, ne-Int, neg, not, or-false, or-true, sub
```

Sixteen differ only in ordinary variable spelling. `and-false` and `or-true`
also spell the unused operand as native `_krs_wildcard_0` versus a
reference-generated anonymous variable. Free KORE axiom variables are
implicitly universal, so consistent alpha-renaming does not change the
relation.

The eight label-only configuration rules are:

```text
assign, block, done, if-else, if-false, if-true, step, while
```

For example, the reference has `label("KRS-M3C-IMP.assign")`, while native has
`label("assign")`. The ninth configuration rule is `var`, which additionally
lacks `cool-like` natively.

The 39 projector fields are exactly:

| Owners | Fields | Count |
|---|---|---:|
| `add`, `and`, `div`, `eq`, `ge`, `gt`, `le`, `lt`, `mul`, `ne`, `or`, `sub` | `lhs`, `rhs` | 24 |
| `neg`, `not` | `value` | 2 |
| generated bracket `krsGenerated_54f869e8de0e01d3ccecb8fc` | `value` | 1 |
| `assign` | `name`, `value` | 2 |
| `block` | `body` | 1 |
| `ifThen` | `condition`, `body` | 2 |
| `ifThenElse` | `condition`, `then_branch`, `else_branch` | 3 |
| `sequence` | `first`, `second` | 2 |
| `while` | `condition`, `body` | 2 |
| **Total** | | **39** |

Each field produces one `project:<owner>:<field>` function symbol and one
equation, hence 78 native-only sentences. No other native sentence uses these
labels.

## Mechanical closure proof

The local AST tool applies each normalization independently and reports:

```text
metadata-only                                      1069/1147 missing=27 extra=105
alpha                                              1069/1147 missing=9  extra=87
alpha+labels                                       1069/1147 missing=1  extra=79
alpha+labels+named-projection-policy               1069/1069 missing=1  extra=1
alpha+labels+cool-like-policy                      1069/1147 missing=0  extra=78
alpha+labels+cool-like-policy+named-projection-policy
                                                   1069/1069 missing=0  extra=0
```

Run it with:

```bash
cargo run --quiet \
  --manifest-path draft/investigations/native-kore-m3c/Cargo.toml -- \
  tests/m3c/rust-definition/target/krs/m3c-kompiled/definition.kore \
  /dev/shm/krs-native-artifacts/m3c/definition.kore \
  KRS-M3C-IMP
```

The final zero/zero result is important: the four categories account for
every sentence, rather than sampling representative mismatches. Removing
`cool-like` in this staged calculation is only a diagnostic isolator; it is
not the recommended compatibility policy.

## Cause analysis

### Alpha naming: comparison policy

The reference emitter encodes authored source identifiers, for example `lhs`
as `V6C6873`, before KORE adds its `Var` prefix. Native KORE preserves `lhs`,
therefore spelling the same variable as `Varlhs`. The old comparator only
normalizes generated `_GenN` and `_DotVarN` names. Canonical alpha-renaming by
first occurrence, variable kind, and sort closes all 18 expression axioms and
the bodies of all nine configuration axioms.

This belongs in the equivalence oracle, not either compiler. The normalizer
must rename consistently within one sentence and must retain element versus
set kind and sort; global textual replacement is unsafe.

### Rule-label qualification: adapter shape

Shared K emission deliberately renders term rules as `rule ...
[label(name)]`, but configuration rules as K's bracket-labeled `rule [name]:`
form. Java qualifies the latter to `MODULE.name` and leaves the former's
explicit label attribute unchanged. Definition IR still distinguishes
`DefinitionRuleBody::Term` from `DefinitionRuleBody::Configuration`.

The native adapter currently inserts the same raw `sentence.label()` for both
body kinds at `crates/krs-k-rust/src/lib.rs:1096-1098`. The smallest exact fix
is therefore in the adapter: qualify only configuration-rule labels as
`{module}.{label}`. Do not qualify the 18 term-rule labels; their reference
values are already exact.

Label qualification is more than alpha-noise: labels are externally visible
for rule selection, tracing, and diagnostics, and unqualified labels can
collide across modules. The report normalizes them only to isolate later
causes.

### `var` and `cool-like`: native finalization divergence

After alpha-renaming, module-label normalization, and excluding named
projectors, the delta is exactly one missing and one extra axiom. Their bodies
are identical. The reference `var` axiom has:

```text
[cool-like{}(), label{}("KRS-M3C-IMP.var")]
```

and native has only:

```text
[label{}("var")]
```

The native frontend already contains the intended
`add_cool_like_attributes` pass. It looks for a variable-headed sequence in a
production carrying `maincell` (`k-rust/.../passes/finalize.rs:62-89` and
`:172-186`), and the compilation pipeline invokes it. The adapted `var` KORE
clearly begins its `k` sequence with `Varname:SortId` followed by `Vartail`.
Thus the behavior is a native finalization divergence for this adapted shape,
not missing authored metadata and not safe alpha-normalization.

The next diagnostic step should snapshot the prepared/concretized native
`var` term immediately before `add_cool_like_attributes`, including the
resolved `<k>` production attributes. Then fix the recognition boundary or
configuration metadata which prevents this rule from satisfying the pass.
Do not simply delete `cool-like` from the oracle: it is compiler-derived
backend metadata and the frontend explicitly intends to reproduce it.

### Named projectors: structured adapter shape plus native extension

The adapter intentionally preserves every Rust field as
`ProductionItem::NonTerminal { name: Some(field) }` at
`crates/krs-k-rust/src/lib.rs:1039-1043`. The emitted `.k` reference grammar is
positional and loses those names. Native `generate_sort_projections` calls
`named_projections` for local productions; its implementation creates a
function/equation pair for every named nonterminal
(`k-rust/.../generate_sort_helpers.rs:70-107` and `:158-238`).

These 78 sentences are a conservative, currently unused native extension; the
zero/zero closure after filtering proves they do not leak into any other M3C
sentence. For semantic equivalence, the smallest policy is to exclude complete
`project:<owner>:<field>` symbol/equation pairs from comparison while asserting
that no retained sentence references them. For literal Java KORE closure, add
a native compile option which suppresses named projections; stripping field
names in the KRS adapter is a worse fix because it discards useful structured
information before other native passes can use it.

## Smallest fixes in dependency order

1. **Fix the oracle first:** alpha-normalize every sentence variable by
   occurrence/kind/sort. This removes 18 missing and 18 extra false positives
   and makes later failures stable across variable spelling changes.
2. **Fix adapter rule labels:** module-qualify configuration-rule labels only.
   This removes eight pairs immediately and the label component of `var`.
3. **Fix the first actionable semantic mismatch:** instrument and correct
   native `add_cool_like_attributes` for the adapted `var` shape. With named
   projector helpers excluded, this is the sole remaining 1/1 mismatch.
4. **Choose and pin projection policy:** normally retain field names and ignore
   closed, unused named-projector pairs in semantic comparison. If exact KORE
   identity is required, suppress their generation through an explicit native
   compiler option rather than weakening the adapter.
5. **Promote closure:** after those choices, require the staged comparator's
   final `missing=0 extra=0`, and separately assert projector pairs are closed
   and unreferenced so the compatibility allowance cannot hide user semantics.

No shared compiler, adapter, authored fixture, or upstream native frontend was
modified by this investigation.
