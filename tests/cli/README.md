# KRS CLI external acceptance oracle

This directory tests the installed behavior of the real `krs` executable. The
oracle never imports or calls `krs-cli` library APIs. Its authored fixture is a
normal standalone Cargo semantics package materialized from
`fixtures/foo-bar/Cargo.toml.in`; only the absolute local path dependency on the KRS
facade is substituted. That build-only path is deliberately absent from every
accepted artifact.

Run from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/cli/verify.py
```

The verifier builds the `krs` binary, then performs two clean runs from
different absolute paths. Each run checks all four commands against the same
`foo -> bar` theory:

- `check` validates exactly nine descriptors and one semantic module;
- `expand` produces canonical, deterministic layer-2 Rust source with three sorts, two constructors, one combined configuration, and one rule;
- `emit-k` creates the schema marker, the three IR/bundle documents, `definition.k`, `symbols.json`, and `sources.json`, and retains `ObjectTerm < KResult < KItem`, `<k> foo </k>`, and the `foo => bar` rule;
- `build` compiles the Definition IR through the structured k-rust frontend and creates exactly `.krs-artifacts`, `definition.kore`, `syntaxDefinition.kore`, and `macros.kore`.

Each run then exercises the run commands natively on the same theory, through `krs-exec` and the `k-rust` symbolic backend:

- `krs run --output json` reports `halt: stuck` after one step with `bar` at the head of `<k>`; `--output kore` prints the final state, which the reference step below compares with Java `krun`'s; `--trace` prints the one step with its authored source position;
- `krs parse --sort ObjectTerm` prints `foo` as KAST text and as KAST JSON.

Relocated outputs must be byte-identical and match `pins.json`. These pins are
independent of the in-tree minimal-definition oracle: this package intentionally has its own
stable Cargo name, K namespace, and source layout, all of which participate in
KRS identities. The verifier also rejects absolute paths, pointer-like values,
`TypeId`, `Self`, and Rust configuration-wrapper spellings in stable output.

A second fixture, `fixtures/dollar-ids`, is an assignment language whose claim
names the program identifier `$x`; the workspace test in `crates/krs-cli` pins
its exact emitted `spec.k`. K's rule grammar has no lexical syntax for `Id`
under `ID-SYNTAX`, so a bare `$x` stops `kprove` at its scanner (review finding
C2-002), and the emitted claims spell it `#token("$x","Id")`. The oracle emits
the fixture, compiles its `definition.k` with the Haskell backend, and requires
`kprove --dry-run` to read its `spec.k` with nothing upstream on the include
path; `pins.json` pins both emitted files.

A third fixture, `fixtures/claims`, is the foo-to-bar language with `$PGM` and two claims:
`foo-reaches-bar` holds and `bar-reaches-foo` does not.
`krs prove` must report them `proven` and `disproved` (exit status 1, since not every claim is proven),
and Java `kprove` on the emitted `spec.k`, against the Haskell `kompile` of the emitted `definition.k`, must agree;
those Java runs form the reference snapshot `claims-prove`.
The same fixture checks an unknown `--claim` (with its did-you-mean from `foo_reaches_bar` to the kebab label)
and the `file:line:column` of a program that does not parse.

Negative cases cover omitted and nonexistent facets, ambiguous Cargo package
names, an authored Cargo-check failure, preservation of an unowned
nonempty artifact directory, an unknown `-c` variable, and a FILE passed to a definition whose init function takes no program (exit status 2). The emitted K is compiled with the LLVM backend
and executed to prove `foo -> bar`.
The Java K results form the reference snapshots `execution`, `dollar-id-claims`, and `claims-prove` (`tests/support/reference.py`),
keyed by the `Krs.lock` K version and the digests of the emitted `definition.k` (and, for the dry run, `spec.k`).
`pins.json` `reference_sha256` pins their manifest digests, and by default the oracle replays the per-user reference cache entries stored under them,
so with a warm cache it needs no K tool; a cached entry whose emitted file differs fails closed.
When the cache does not hold an entry, and under `--refresh-reference`, `kompile`, `krun`, and `kprove` run live
and must be present, in `KRS_K_BIN` or on `PATH`, at the K version `Krs.lock` pins
(a missing tool fails closed, and present tools at a different version are a hard mismatch and are never used);
the live result must reproduce the pin, and it is stored only when every other check passes.

`pins.json` pins the fixtures (inputs, edited deliberately), the artifact
digests, and the reference snapshot digests (outputs). After an intended output
change, re-record the artifact digests by running the oracle
(add `--refresh-reference`, with the K tools, when the emitted K changed):

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/cli/verify.py --record
```

It rewrites `artifacts_sha256` and `reference_sha256` only when every other check passes.
