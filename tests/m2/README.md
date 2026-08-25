# M2 independent reference oracle

This package is independent of production KRS crates and adapters. Its
handwritten input is `fixtures/foo-bar.k`; it must never be regenerated from,
or updated merely to match, an adapter artifact.

## Exact semantics

`KRS-M2-REFERENCE` declares `KItem`, `KResult`, and object sort `M2Obj`.
`foo` and `bar` are labeled nullary `M2Obj` constructors with concrete syntax.
The explicit subsort chain is `M2Obj < KResult < KItem`. The sole `<k>` cell
starts at `foo`, and the sole user transition is the unconditional
`foo => bar`.
The `<k>` cell content sort is `K`, not `M2Obj`: its initial content is the
`KSequence` `kseq(inj{M2Obj,KItem}(foo), dotk)`. Source Definition IR must
retain that `K`/`KSequence` layer distinctly from the object constructor sort;
an adapter may not type the cell as `M2Obj` merely because `foo` is its first
item.
The local `true:Bool` token is bootstrap syntax needed by portable `k-rust`
without loading the full prelude; it is not another object-language sort.

`fixtures/induced-rule-error.k` changes the rule to contain an undeclared `+`.
The pin-matched reference frontend must reject it at that exact authored token,
currently `induced-rule-error.k:13:19`.

## Run

```sh
python3 tests/m2/verify.py
```

All build products and compiled definitions are placed under a fresh system
temporary directory and removed when the verifier exits. The native helper is
locked independently and built with `default-features = false`, so the known
host Z3/static-C++ linker incompatibility is not mistaken for a frontend
failure.

Once M2A exposes artifacts without changing its API to satisfy this oracle:

```sh
python3 tests/m2/verify.py \
  --candidate-k path/to/generated.k \
  --candidate-module KRS-M2-REFERENCE \
  --candidate-definition-kore path/to/definition.kore \
  --candidate-syntax-kore path/to/syntaxDefinition.kore
```

The candidate `.k` is compiled by the pin-matched reference frontend. It is
not used as the native adapter. The two candidate KORE files are parsed and
compared as structural sentence multisets.

## External Rust authoring fixture

`rust-workspace/packages/m2-semantics` is a second independent input oracle.
It is an ordinary Cargo package whose only KRS dependency is the renamed
`language-host` facade. It authors exactly three open sorts, two nullary
constructors, one combined `Machine` configuration/initializer, and one
`Foo => Bar` transition. It never imports `krs-ir`, `krs-compiler`, or
`krs-k-rust`. The neighboring `m2-oracle-runner` is generated-tool-shaped: it
explicitly retains the semantics crate and is the only package allowed to
inspect collector/compiler/native artifacts.

The verifier treats this path as staged only while the public configuration
macros or `lower_descriptor_bundle` do not exist. Once those symbols are
wired, Cargo failures and missing lockfiles are hard failures; no positive,
negative, determinism, LSP, frontend, or native assertion is silently skipped.
The root integrator owns both external-workspace lockfiles.

The Rust gate independently asserts:

- protocol 5 and exactly one combined configuration descriptor owned by
  `Machine`, with no stable `init` item;
- exactly one `initializer_term_path#0 -> Foo` semantic reference and exact
  authored provenance for it;
- zero ordinary initializer calls during registration and collection;
- the direct chain `M2Obj < KResult < KItem`, builtin `KSequence` cell/body,
  `Foo` initializer, and structured `Foo => Bar` rewrite in semantic IR;
- deterministic Definition IR, canonical `.k`, symbol map, and source map,
  including generated ranges mapping to authored `Foo`, `Bar`, `Machine`, and
  `init` tokens;
- two byte-identical clean builds with path/`TypeId`/pointer leak rejection;
- four macro/UI failures and adversarial cross-wired-init, wrong-reference-kind,
  and stale split-file provenance failures; and
- rust-analyzer diagnostics, navigation, hover, and rename through the renamed
  facade.

The canonical `.k` is compiled by K 7.1.337 and executes `foo -> bar`. The
same Definition IR is sent directly to the adapter's provisional structured
oracle; emitted `.k` is never input to that route. The permanent entry point
must continue to report `StructuredDefinitionPreparationUnavailable` until
upstream exposes the invariant-preserving preparation boundary.

For the exact-location oracle, the verifier selects the generated rule-RHS
range whose origin is the authored Rust `Bar` token, substitutes an invalid
`+` at precisely that range, obtains the pinned K diagnostic, and maps it back
through `sources.json`. This tests the public generated-range seam without
inventing a production-only error API.

## Pins and capability results

`pins.json` pins K `7.1.337` at `4a46d123...`, `k-rust` `0.3.0` at
`58f33885...`, LLVM backend `0.1.140`, Haskell backend `0.1.155`, KAST JSON
v4, normalizer v1, and both handwritten fixture hashes. The verifier probes
every executable and version before use.

Observed locally on 2026-08-19:

- K CLI parse/compile: available at `v7.1.337`.
- LLVM execution: available; depth zero contains `foo`, normal form contains
  `bar`.
- Haskell `kore-exec`/`kore-rpc` and booster RPC: available at `0.1.155` but
  not needed to establish the one-backend M2 execution requirement;
  `kore-rpc-dev` is explicitly unavailable.
- portable native parse/compile/KORE reparse: available with pinned `k-rust`.
- installed pyk: `7.1.174`, a named pin mismatch, and therefore not used.
- default-feature native CLI: blocked by the documented static Z3/C++ host
  linker mismatch; the portable frontend lane remains available.
- production M2A source/KORE artifacts: unavailable until its contract is
  frozen and passed explicitly to the verifier.

`PASS`/`MATCH` denotes an executed check. `UNAVAILABLE`, `BLOCKED`, and
`MISMATCH` are distinct capability results and are never printed as success.
The command exits nonzero for a broken self-check or for an explicitly supplied
candidate that fails comparison.

## Normalization policy

Source-definition comparison selects exactly the requested project module and
retains all unknown nodes, fields, imports, semantic attributes, productions,
configuration-generated sentences, rule bodies, and conditions. It removes
only the enumerated source/location, parser-production, digest, content-offset,
and unique-ID metadata in `verify.py`; local sentence and import collections
are sorted, and generated variables are alpha-normalized. Unknown KAST shape
fails closed. Raw `parsed.json` is never goldened across K pins.

KORE comparison uses the pinned native KORE parser, strips only source,
location, digest, content-start, and unique-ID attributes, sorts attribute
sets, alpha-normalizes generated variable suffixes, and compares sentence
multisets for the requested module. It first compares the reference artifact
with itself so a broken normalizer cannot masquerade as an adapter mismatch.

The current portable native and Java source **local sentences match**. The
full source module remains a named mismatch because Java's implicit prelude
adds public import `MAP`, while the portable native path deliberately loads no
prelude to avoid Z3 inference. Correspondingly, full project KORE differs
(251 reference sentences versus 130 native sentences in the observed run).
The verifier retains this mismatch; it does not drop imported builtin
sentences or bless a smaller projection. M2 integration must either provide a
pin-compatible structured-preparation path with equivalent imports or record a
reviewed frontend capability decision.

The generated Rust fixture uses a narrower, explicit project-semantics
projection. It deliberately has no portable-native-only `true:Bool` bootstrap,
and compiler-owned production/rule identities need not equal handwritten
`symbol(foo)`, `symbol(bar)`, or an unlabeled handwritten rule. Sort edges,
concrete terminals, configuration, rewrite behavior, parsing, and execution
must agree. The verifier reports the bootstrap and MAP/full-closure differences
as named `MISMATCH` results; it never removes sentences from adapter output or
asks an adapter to invent reference-only declarations.

## API requests and risks

- M2A should supply emitted `.k`, module name, `definition.kore`, and
  `syntaxDefinition.kore` paths explicitly. No production API is assumed here.
- Definition IR must expose `<k>` content as sort `K`/`KSequence` while keeping
  `foo` and `bar` at `M2Obj` and their injection into `KItem`; this is asserted
  against parsed KAST and the depth-zero backend term.
- The permanent native adapter still needs the R11 invariant-preserving
  `prepare_definition(Definition, ...)` boundary; parsing generated `.k` is not
  an accepted substitute.
- Production diagnostics must map the induced `+` back to the authored KRS
  token. This package proves the reference K location only; it does not invent
  an unfrozen KRS source-map format.
- KAST JSON v4 cannot represent every future sentence kind. Any unsupported or
  unknown kind must block comparison until the versioned normalizer is
  classified, not be discarded.
