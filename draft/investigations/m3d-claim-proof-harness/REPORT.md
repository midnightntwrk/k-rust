# M3D native Claim proof-harness investigation

## Result

The exact bridge is viable without synthesizing Java frontend metadata and
without pretending that a native Claim is a Rule:

```text
KRS Definition IR Claim
  -> k_rust::definition::Sentence::Claim
  -> compile_loaded_definition(... backend = Haskell).definition_kore
  -> parsed-KORE ownership split
       execution definition.kore (claims removed)
       one native spec.kore per selected Claim
  -> upstream-compatible parse-kompiled
       kprove --dry-run + --emit-json-spec only
  -> KRS-compatible execution-kompiled metadata
       claim-free native definition.kore replaces only its backend artifact
  -> direct kore-exec --prove native-spec.kore
  -> exact raw #Top plus frozen source-claim hashes
```

The two kompiled directories are a semantic boundary, not an optimization.
Pinned `kprove` parses upstream `.k` specifications only with the upstream IMP
frontend. Pinned `kore-exec` verifies and executes KRS terms only with metadata
compiled from generated KRS `.k` and the native KRS `definition.kore`. Neither
frontend is ever asked to parse terms produced by the other frontend.

The prototype completed all three cases:

| Case | Native label | Source claim | Result hash | Claim hash |
| --- | --- | --- | --- | --- |
| `branching` | `branching` | `IMP-SIMPLE-SPEC.branching` | `daa7dc7ca21072fe58ed50886864daa9062113fefb6560364bc0ddc034c92518` | `e6af137f0b47ee356524fb713866376c27a2e1e9673a1871ae9db15c8a23f940` |
| `sum-loop` | `sum-loop` | `IMP-SIMPLE-SPEC.sum-loop` | `daa7dc7ca21072fe58ed50886864daa9062113fefb6560364bc0ddc034c92518` | `f1e9802339a8cb1897fde38b247de3faea9c39757c338571dff71bc7f1b25ddb` |
| `sum-spec` | `sum-spec` | `IMP-SUM-SPEC.sum-spec` | `daa7dc7ca21072fe58ed50886864daa9062113fefb6560364bc0ddc034c92518` | `ee006de43e8076b944827ef3552295ea895cd7d59f81aff77e2b7d1658cee727` |

Each result was exit zero with normalized root `#Top`.

## Executable files

- `src/main.rs` uses the pinned k-rust KORE parser and printer. `split`
  materializes execution/spec KORE; `compare` checks native and Java Claim
  KORE; `assert-top` requires the backend result to be exactly KORE `#Top`;
  `fixture-merge` retains the independent bridge regression.
- `harness.py` performs the production-shaped run.
- `normalize.py` copies the frozen M3D proof and claim normalizers, including
  their fail-closed KAST node sets.
- `cases.json` owns the complete label/module/modality/hash matrix.
- `verify.py` builds a native-shaped, claim-bearing KORE fixture from the
  pinned Java proof KORE and exercises the separated parse/execute path.

Run the self-contained prototype from the KRS workspace root:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m3d-claim-proof-harness/verify.py
```

Once production emits claim-bearing native Haskell KORE, run the same path
against it directly:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m3d-claim-proof-harness/harness.py \
  --native-kore /absolute/path/to/krs-definition.kore \
  --execution-shell-source /absolute/path/to/generated-krs-definition.k \
  --semantic-module KRS-M3D-CLAIM-SLICE \
  --syntax-module KRS-M3D-CLAIM-SLICE \
  --workspace /tmp/krs-m3d-native-proof
```

The workspace must be absent or empty. Prebuilt directories may be supplied
independently as `--parse-skeleton` and `--execution-skeleton`. The strict
default retains structural claim comparison. The explicit
`--allow-unmapped-claim-structure` escape defers only the reviewed M4 symbol
identity comparison; it does not defer native validation, execution, `#Top`,
or source-claim hashing.

## Why two Haskell kompiled directories are retained

`kprove -d` is both a K frontend and a Haskell-backend driver. Parsing the
source specification needs serialized frontend state such as `compiled.bin`,
the scanner, syntax KORE, parsed definition data, backend/main-module markers,
and the rest of the normal `*-kompiled` directory. Native k-rust currently
returns textual `definition.kore`, `syntaxDefinition.kore`, and `macros.kore`;
it does not serialize Java `CompiledDefinition` state.

There is no need to reproduce that private serialization, or to mix it with
native execution. The harness:

1. creates/copies `parse-kompiled` from the upstream-compatible adjunct shell;
2. invokes `kprove --dry-run --emit-json-spec` there to obtain the selected
   source Claim KORE and frozen KAST-v4 claim JSON;
3. creates/copies `execution-kompiled` from generated KRS `.k` with claims
   removed, preserving matching backend symbol/configuration metadata;
4. replaces only `execution-kompiled/definition.kore` with the AST-split,
   claim-free native KRS execution definition; and
5. calls `kore-exec` directly with the separately split native Claim KORE.

The resulting backend shape is:

```text
kore-exec EXECUTION-KOMPILED/definition.kore
  --module KRS-M3D-CLAIM-SLICE
  --prove SPLIT/specs/CASE.kore
  --spec-module IMP-SIMPLE-SPEC
  --output KPROVE-TEMP/result.kore
```

The execution shell and native KORE must describe the same symbols, sorts,
configuration, and main module. Exact native-versus-source Claim comparison
remains the strict compatibility check; module-name checks alone are not
sufficient.

## Native Claim ownership and split contract

The splitter operates on k-rust's public parsed KORE AST. It never slices KORE
text or searches claim bodies with regular expressions.

For every entry in `cases.json`, it requires:

- exactly one `Sentence::Claim` in `KRS-M3D-STATIC` with the exact unqualified
  KRS label;
- no occurrence of that owned label in another KORE module;
- exactly one `weakAlwaysFinally` wrapper for `all-path` (or
  `weakExistsFinally` for `one-path`) and none of the other wrapper;
- no modality attribute that conflicts with that wrapper (the expected
  marker may be inherited from a module default and absent on the sentence);
- `circularity` exactly for `sum-spec`; and
- no `Sentence::Axiom` carrying the same label.

Every nonselected Claim remains in the execution definition. This exact-label
policy prevents a broad “remove every claim” operation from silently deleting
imported or future proof obligations.

The execution definition is the original parsed definition with only the
manifest-owned claims removed. Each proof definition contains one new module
with the pinned source spec-module name, one import of
`KRS-M3D-STATIC`, and the untouched native `Sentence::Claim`.

Before running the backend, `compare` locates the selected source and native
claims by their separate exact labels and compares parsed ASTs after only:

- alpha-normalizing variables by kind, spelling, and sort;
- dropping source/location/parser/generated-ID metadata;
- dropping the already-validated label and modality attributes; and
- sorting the remaining attributes.

The reachability wrapper and `circularity` remain in the comparison. This gate
connects the frozen source claim hash to the actual native claim; a successful
proof of a merely similar or accidentally weaker native claim is not enough.

## Result and oracle contract

The source-only `kprove` invocation retains the frozen selection options but
stops after frontend generation:

```text
kprove SOURCE-SPEC -d PARSE-KOMPILED
  -I UPSTREAM-DEFINITION
  -I tests/m3d/fixtures
  --spec-module SOURCE-MODULE
  --emit-json-spec CASE-claim.json
  --claims FULL-SOURCE-LABEL
  --dry-run
```

The emitted source claim JSON is processed by the frozen, fail-closed claim
normalizer and independently hash-checked. The backend result is parsed as
KORE and must be exactly `\top{R}()`; a frontier, wrapper, extra field, parse
failure, or nonzero backend exit fails. The corresponding frozen normalized
KAST-v4 `#Top` hash remains the recorded result hash. No JSON conversion of
native KRS terms is delegated to the upstream frontend.

## Production status

Production now emits all three labels as native `Sentence::Claim`, emits no
claim-derived rules, exposes Haskell-compatible KORE, and supplies generated
`.k` for execution metadata. The separated harness reaches pinned kore-exec
for each real native claim.

At the time of this report update, native execution still exposes one adapter
compatibility defect: Rust semantic/frame identifiers are emitted verbatim as
lowercase K variables (`s`, `n`, `tail`, and the non-underscore
`KRSAnonymous...`). Haskell classifies them as configuration variables and
rejects the reachability configuration as non-function-like. Native adaptation
must encode ordinary variables with valid uppercase K spelling, retain `?N`
for existentials, and retain an underscore-leading collision-free anonymous
spelling. This is a production/native-lowering blocker, not a reason to merge
the parse and execution frontends again.

The independent `fixture-merge` regression continues to prove the bridge
itself: it rewrites only the qualified oracle labels and injects real KORE
`Sentence::Claim` values. The same splitter, comparator, separated parser,
direct backend invocation, exact-Top check, and normalizers then run unchanged.

## Verification evidence

Validated locally on 2026-08-20 with K 7.1.337 and kore-exec 0.1.155:

```text
COMPARE source=IMP-SIMPLE-SPEC.branching native=branching equal=true
TOP sort=R
COMPARE source=IMP-SIMPLE-SPEC.sum-loop native=sum-loop equal=true
TOP sort=R
COMPARE source=IMP-SUM-SPEC.sum-spec native=sum-spec equal=true
TOP sort=R
PASS branching result=daa7...18 claim=e6af...940
PASS sum-loop  result=daa7...18 claim=f1e9...ddb
PASS sum-spec  result=daa7...18 claim=ee00...727
```
