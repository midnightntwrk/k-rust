# M4 complete IMP equivalence gate

M4 is the first gate over one complete, ordinary Rust-authored IMP package.
It is not a roll-up of the earlier milestone PASS lines. The gate starts from
the single package in `rust-definition`, resolves one Descriptor Bundle into
one Semantic IR and one Definition IR, and sends that same Definition IR to
both canonical `.k` emission and native `k-rust` lowering.

The resulting Semantic IR intentionally contains `KRS-FRAMEWORK` for the
built-in `KItem`/`KResult` declarations and `KRS-M4-COMPLETE-IMP` for the
authored language.

The complete package contains the closed M3C operational language, the four
IMP verification simplifications, the separately identified static adjunct,
all 15 upstream IMP claims, and five independently selectable adjunct claims.
Its only normal dependency is the author-facing `krs` facade renamed to `k`.
Every authored source file is rustc-valid Rust.

The authored and independently expanded IMP packages are checked on Rust 1.88.0.
Native/frontend helpers are additionally qualified on exact stable Rust 1.98.0.
Clean k-rust `c41caa8bede96e279e0b058577dce504e4144f65` declares and enforces MSRV 1.88, so the gate also checks the workspace and every helper on exact Rust 1.88.0.
`K_RUST_UPSTREAM.toml` records the closed if-let-guard discrepancy that previously blocked this alignment.

## Evidence layers

`verify.py` owns the ordered top-level gate and stops at the first failed
layer:

1. exact source, tool, checkout, schema, lock, and corpus pins;
2. ordinary Rust formatting, check, Clippy, docs, tests, and LSP evidence;
3. repeated KRS collection, byte-exact layer-2 Rust expansion, `.k`, sidecar,
   IR, and native artifact determinism;
4. fail-closed parsed and compiled source-definition comparison;
5. native Definition/KORE comparison with only the reviewed closed unused
   named-projector allowance;
6. parser and unparser comparison over the M3A--M3C corpus;
7. concrete execution, all frozen depth states, stuck states, and failures;
8. finite and bounded-live search frontier comparison;
9. bounded proof comparison for the 20 claims plus the depth-zero invocation;
10. stable-name, diagnostic-boundary, clean-reproduction, and final
    byte-for-byte compatibility checks.

Behavior is parallelizable inside a layer, but layers are serial. A timeout,
unknown KAST/KORE node, missing artifact, ambient pin mismatch, native/source
fallback, or unclassified difference fails the gate.

## Directory ownership

- `rust-definition/` is the complete facade-only authored language.
- `goldens/imp.expanded.rs` is the reviewed, rustc-checked layer-2 projection
  produced by `krs expand`; the gate byte-compares two live projections to it.
- `oracle/` contains fail-closed source, behavior, search, and proof
  comparison libraries.
- `native/` contains the production native/reference KORE comparator.
- `compatibility/` contains stable-name and four-boundary diagnostic cases.
- `corpus.json`, `pins.json`, and `verify.py` are the root integration
  contract and contain no alternate semantics.

The M3 corpora and upstream IMP sources remain the canonical input files.
`corpus.json` points to and hashes them; M4 does not copy them.

## Proof policy

All M4 proof invocations freeze semantic `depth = 100` and
`branching_allowed = 64`. Wall-clock time is only a process-safety watchdog.
Every proof command owns a new process session; timeout terminates and reaps
the complete Java/kore-exec/solver process group and produces no pinnable
status.

At those bounds, the reviewed reference route proves the six newly selected
finite upstream claims and retains one exact normalized frontier for `sum-N`,
both BMC claims, and `two-sum-spec`. Earlier M3D outcomes and the five adjunct
claims are selected independently. The M4 route must match status, claim,
complete result/frontier constraints, and the exact bounds; exit status alone
is not evidence.

## Running the gate

Use a filesystem with sufficient build space. Generated Cargo targets,
kompiled directories, and proof workspaces are disposable and are never
checked in.

The LLVM runtime reserves a sparse 2 TiB virtual region for its semispace allocator.
This reservation does not consume 2 TiB of resident memory, but a hard `RLIMIT_AS` prevents the interpreter from starting.
For a memory-bounded run, set only the soft address-space limit and leave its hard limit unlimited.
The behavior oracle uses `prlimit` to restore the unlimited soft limit only for the two LLVM division-by-zero executions; Cargo, the K frontend, Haskell, and all proof routes retain the 12.5 GB ceiling.

```bash
ulimit -S -v 12500000
TMPDIR=/tmp \
KRS_M4_ORACLE_WORKERS=1 \
CARGO_BUILD_JOBS=1 \
RUST_TEST_THREADS=1 \
GHCRTS=-N1 \
K_OPTS='-Xmx4096m -Xss2m -XX:ActiveProcessorCount=1' \
PYTHONDONTWRITEBYTECODE=1 \
python3 tests/m4/verify.py
```

The final PASS summary prints the protocol/IR schema, K and `k-rust` pins,
proof-bound policy, artifact hashes, and compatibility-policy version.
