# Complete IMP equivalence gate

IMP is the first gate over one complete, ordinary Rust-authored IMP package.
It is not a roll-up of the state, control flow, or static semantics oracle PASS lines. The gate starts from
the single package in `rust-definition`, resolves one Descriptor Bundle into
one Semantic IR and one Definition IR, and sends that same Definition IR to
both canonical `.k` emission and native `k-rust` lowering.

The resulting Semantic IR intentionally contains `KRS-FRAMEWORK` for the
built-in `KItem`/`KResult` declarations and `KRS-IMP` for the
authored language.

The complete package contains the closed IMP control flow operational language, the four
IMP verification simplifications, the separately identified static adjunct,
all 15 upstream IMP claims, and five independently selectable adjunct claims.
Its only normal dependency is the author-facing `krs` facade renamed to `k`.
Every authored source file is rustc-valid Rust.

The authored and independently expanded IMP packages and the artifact probe are checked on the `Krs.lock` MSRV, Rust 1.88.0, by IMP.2's package checks.
Native/frontend helpers are additionally qualified on the current stable Rust, which must be at or above that MSRV.
Workspace-wide formatting, Clippy, tests, documentation, and the workspace MSRV check belong to the standard checks that CI's workspace job runs.
The complete eight-phase IMP gate passed against clean k-rust `195a77180add343b1ba2313dc20ae230bb7d3350` on 2026-10-06 JST.

## Evidence layers

`verify.py` owns the ordered top-level gate of eight layers and stops at the
first failed layer; its `PASS` and `FAIL` lines use these names:

- IMP.1 `preflight`: external checkout revisions and file digests,
  `Krs.lock` tool and schema versions, and the corpus;
  it requires only the tools of the layers that will run (see "Java K");
- IMP.2 `rust-and-lsp`: authored package formatting, Clippy, and MSRV
  checks; authored and expanded helper tests; authored helper docs;
  kompile tests; gate self-tests; `krs` and `krs-gate` builds; and
  diagnostic and readable IMP LSP evidence;
- IMP.3 `deterministic-artifacts`: repeated KRS collection, byte-exact
  layer-2 Rust expansion, `.k`, sidecar, IR, and native artifact
  determinism;
- IMP.4 `source-definition`: fail-closed parsed and compiled
  source-definition comparison;
- IMP.5 `native-kore`: native Definition/KORE comparison with reviewed
  constructor-axiom order canonicalization and the closed unused
  named-projector allowance;
- IMP.6 `parser-execution-search`: parser and unparser comparison over the
  expression, IMP state, and IMP control flow corpora; concrete execution,
  all frozen depth states, stuck states, and failures; and finite and
  bounded-live search frontier comparison;
- IMP.7 `bounded-proofs`: bounded proof comparison for the 20 claims plus
  the depth-zero invocation;
- IMP.8 `compatibility-reproduction`: stable-name, diagnostic-boundary,
   clean-reproduction, and final byte-for-byte compatibility checks.

`--audit-all` runs every layer whose prerequisites passed and reports every
failure instead of stopping at the first.

Layers are serial. Inside the behavior, proof, and compatibility layers every
independent case runs concurrently, bounded by `KRS_IMP_ORACLE_WORKERS`
(default 4, at most 32); the results are then checked serially in corpus and
pin order, so the evidence digests and the first reported difference do not
depend on the worker count. A timeout, unknown KAST/KORE node, missing
artifact, ambient pin mismatch, native/source fallback, or unclassified
difference fails the gate.

## Directory ownership

- `rust-definition/` is the complete facade-only authored language.
- `goldens/imp.expanded.rs` is the reviewed, rustc-checked layer-2 projection
  produced by `krs expand`; the gate byte-compares two live projections to it.
- `oracle/` contains fail-closed source, behavior, search, and proof
  comparison libraries.
- `native/` retains the comparator policy and parity evidence; the implementation lives in `crates/krs-gate/src/kore_compare.rs` and `crates/krs-gate/src/proof.rs`.
- `compatibility/` contains stable-name and four-boundary diagnostic cases.
- `corpus.json`, `pins.json`, and `verify.py` are the root integration
  contract and contain no alternate semantics.
- `proof-pins/` holds the three frozen reference-proof ledgers (`selected`,
  `reference`, and `adjunct`) as provenance; IMP does not read them and
  re-proves all 21 outcomes from `pins.json` itself.

The expression corpus lives in `corpus/expr/`; `corpus.json` names it and is
hash-pinned in `pins.json`. The IMP state, IMP control flow, and IMP static semantics corpora and upstream IMP sources
remain the canonical input files for the other cases; `corpus.json` points to
the IMP state, IMP control flow, and IMP static semantics ledgers, IMP checks those corpora against the ledgers'
`corpus_sha256` tables, and IMP does not copy them.

## Pins

`pins.json` holds three kinds of values:

- inputs IMP does not control: the IMP revision and the corpus digest.
  The K and k-rust revisions, the K, kore-exec, LLVM backend, and Z3
  versions, the MSRV, and the schema versions come from `Krs.lock`.
  Each external checkout must be clean at its pinned revision, which fixes every
  external file, so no external file is digested separately;
- outputs KRS produces: the artifact and native artifact digests, the
  source-definition projection digests, the claim-free LLVM artifact digests,
  the behavior summary, and the compatibility report digest;
- reviewed comparison policy: claim labels, the source-definition and term
  allowances, the native label map, and the 21 reference proof outcomes, which
  describe the upstream reference route rather than KRS output.

KRS source is not pinned, so a change that leaves every output identical passes
unchanged. After an intended output change, run the gate with `--record` (with
the same memory-bounded recipe below). It runs every phase and, only if all of
them pass, rewrites exactly the output pins it measured. It never rewrites an
input or a reviewed policy value; edit those deliberately.

## Java K

Every K invocation of the gate replays a committed reference snapshot by default (`tests/support/reference.py`),
so neither a full run nor `--artifacts-only` needs a K tool, the `z3` binary, or the K source checkout.
IMP.1 requires the Rust toolchain, `git`, and `rust-analyzer` (for the live LSP probes of IMP.2 and IMP.8) on every run.
Every KRS step stays live: the builds, the emitted and native artifacts, the native KORE comparator,
krs-gate's normalization, projection, frontier, and proof classification, and the native proof split.

Each snapshot is one directory under `reference/`:

- `kompile-tests/` (IMP.2): `kompile` of the canonical sources the `control_flow_lowering` and `fixed_state_lowering` kompile tests export through `KRS_REFERENCE_EXPORT_DIR`, keyed by each exported source;
- `source-definitions/` (IMP.4): the Haskell and LLVM `kompile` runs of the upstream reference (the static adjunct over upstream IMP) and of the emitted `definition.k`.
  It stores the `parsed.json` and `compiled.json` of both Haskell definitions and the actual `definition.kore` IMP.5 compares;
- `native-claims/` (IMP.5): `kprove --dry-run` on the emitted claims, storing the `spec.kore` the native comparator merges;
- `behavior/` (IMP.6): every `kast` and `krun` run of both routes, storing their output;
- `proofs/` (IMP.7): the two `kompile` runs, the 21 reference, 21 actual, and 21 dry-run `kprove` runs, the residual KORE `kprove` run of each incomplete proof, and the 21 `kore-exec` runs on the native build.
  Each proof's exit status is in the manifest, and its JSON result and emitted claim are stored one member per line, without source locations, so a proof result reads and diffs as text;
- `frontend-diagnostic/` (IMP.8): the `kompile` run of the K frontend probe's induced spec failure.

The reference side of each snapshot is keyed by the `Krs.lock` K version, the upstream IMP revision, and the static adjunct fixture.
The actual side is keyed by the digest of the emitted `definition.k`, which IMP.3 pins,
and by the digest of every file the invocation's argument vector names, such as `spec.k`, a generated execution input, or the native `definition.kore`.
`kore-exec` is keyed by the `Krs.lock` kore-exec version and the native definition and claim KORE that KRS built.
A change to what KRS emits or builds therefore fails closed at the first stale invocation and names `--refresh-reference`; replay never falls back to a live tool and never skips a layer.

The stored evidence is reduced only where no comparator reads the difference, and a live run hands the comparators the same reduced text:
the definitions omit the metadata attributes krs-gate removes and list each module's `localSentences` in sorted order,
and `spec.kore` lists its claims in sorted order, because K writes both in a run-dependent order for the emitted modules;
the install path of K's prelude, the name of `kprove`'s directory under `--temp-dir`, and the run-dependent number of each `kore-exec` log line are replaced by fixed text.

`--refresh-reference` runs every recorded invocation live instead.
It requires the K tools (`kompile`, `kast`, `krun`, `kprove`, `kore-exec`, `llvm-kompile`) at the `Krs.lock` versions,
the `z3` binary, and the clean K source checkout, and it rewrites only the snapshots it measured, only when every layer passed.
The proof harness and the K frontend probe run as child processes; a refresh stages their snapshots in the gate workspace,
and the gate promotes them with its own snapshots.
A refresh is a full live Java K run of the gate.
Under the host recipe below with a warm Cargo target it took 7.5 to 11 minutes, against under a minute for a replaying run,
and it needs memory for `KRS_IMP_ORACLE_WORKERS` concurrent JVMs.
Under heavy machine load, the live LLVM division-by-zero execution of IMP.6 can reach its eight-second watchdog before it prints the hook diagnostic;
that refresh then fails and writes nothing, and a rerun on a less loaded machine passes.
It may be combined with `--artifacts-only`, which then refreshes only the IMP.2 snapshot, and with `--record`.
Run it after an intended change to an emitted or native artifact, a K or upstream revision change, or a change to an argument vector, and review the snapshot diff with the output pins.

## Proof policy

All IMP proof invocations freeze semantic `depth = 100` and
`branching_allowed = 64`. Wall-clock time is only a process-safety watchdog.
Every proof command owns a new process session; timeout terminates and reaps
the complete Java/kore-exec/solver process group and produces no pinnable
status.

At those bounds, the reviewed reference route proves the six newly selected
finite upstream claims and retains one exact normalized frontier for `sum-N`,
both BMC claims, and `two-sum-spec`. Earlier IMP static semantics outcomes and the five adjunct
claims are selected independently. The IMP route must match status, claim,
complete result/frontier constraints, and the exact bounds; exit status alone
is not evidence.

## Running the gate

Use a filesystem with sufficient build space. Generated Cargo targets,
kompiled directories, and proof workspaces are disposable and are never
checked in.
By default, the IMP Cargo target is under `KRS_GATE_SCRATCH/krs-<checkout>-<key>/imp-root-target`,
where `KRS_GATE_SCRATCH` defaults to `/var/tmp` and `<key>` identifies the resolved checkout path.
`--target-dir` and `KRS_IMP_TARGET_DIR` select an explicit target instead.
Compatibility probe targets are under the selected target's `probes/` directory.

On a host without a memory envelope, run the oracle in parallel and leave
Cargo, the test harness, and the JVM their default parallelism:

```bash
TMPDIR=/tmp \
KRS_IMP_ORACLE_WORKERS=16 \
K_OPTS='-Xmx4096m -Xss2m' \
PYTHONDONTWRITEBYTECODE=1 \
python3 tests/imp/verify.py
```

`K_OPTS` matters only to a `--refresh-reference` run, the one that starts Java K.
In a refresh, each worker runs one `kast`, `krun`, `kprove`, or `kore-exec` process at a
time, so the worker count bounds the number of concurrent JVMs and should be
sized to the memory available, not only to the core count.

A memory-bounded environment uses the single-worker recipe below.
The LLVM runtime reserves a sparse 2 TiB virtual region for its semispace allocator.
This reservation does not consume 2 TiB of resident memory, but a hard `RLIMIT_AS` prevents the interpreter from starting.
For a memory-bounded run, set only the soft address-space limit and leave its hard limit unlimited.
In a refresh, the behavior oracle uses `prlimit` to restore the unlimited soft limit only for the two LLVM division-by-zero executions; Cargo, the K frontend, Haskell, and all proof routes retain the 12.5 GB ceiling.

```bash
ulimit -S -v 12500000
TMPDIR=/tmp \
KRS_IMP_ORACLE_WORKERS=1 \
CARGO_BUILD_JOBS=1 \
RUST_TEST_THREADS=1 \
GHCRTS=-N1 \
K_OPTS='-Xmx4096m -Xss2m -XX:ActiveProcessorCount=1' \
PYTHONDONTWRITEBYTECODE=1 \
python3 tests/imp/verify.py
```

The final PASS summary prints the KRS schema version, K and `k-rust` pins,
proof-bound policy, artifact hashes, and compatibility-policy version.

`--artifacts-only` runs IMP.1-IMP.3 (preflight, the Rust checks, and the
repeated emission, probe, and native builds with every emitted artifact
compared to its pin) and stops with a PASS line that says the comparison
layers IMP.4-IMP.8 were skipped. Those layers compare the emitted artifacts
with the reference routes and cannot find anything new while every artifact is
byte-identical to its pin, so the mode suits a change expected to leave the
output unchanged. Any artifact difference fails and asks for the full gate; the
mode cannot be combined with `--record` or `--audit-all`. The full run stays
the default.
