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

The authored and independently expanded IMP packages are checked on the `Krs.lock` MSRV, Rust 1.88.0.
Native/frontend helpers are additionally qualified on the current stable Rust, which must be at or above that MSRV.
Clean k-rust main `efda6192785d4113eeea2fa090e4662d30dc8801` declares and enforces MSRV 1.88, so the gate also checks the workspace and every helper on exact Rust 1.88.0.
Earlier k-rust revisions used if-let guards, which Rust 1.88.0 rejects; that discrepancy previously blocked this alignment and is now closed.
The complete M4.1-M4.8 gate passed against that pin on 2026-09-15 JST.

## Evidence layers

`verify.py` owns the ordered top-level gate and stops at the first failed
layer:

1. external checkout revisions and file digests, `Krs.lock` tool and schema
   versions, and the corpus;
2. ordinary Rust formatting, check, Clippy, docs, tests, and LSP evidence;
3. repeated KRS collection, byte-exact layer-2 Rust expansion, `.k`, sidecar,
   IR, and native artifact determinism;
4. fail-closed parsed and compiled source-definition comparison;
5. native Definition/KORE comparison with reviewed constructor-axiom order canonicalization and the closed unused named-projector allowance;
6. parser and unparser comparison over the expression, M3B, and M3C corpora;
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
- `proof-pins/` holds the three frozen reference-proof ledgers (`selected`,
  `reference`, and `adjunct`) as provenance; M4 does not read them and
  re-proves all 21 outcomes from `pins.json` itself.

The expression corpus lives in `corpus/expr/`; `corpus.json` names it and is
hash-pinned in `pins.json`. The M3B--M3D corpora and upstream IMP sources
remain the canonical input files for the other cases; `corpus.json` points to
the M3B--M3D ledgers, M4 checks those corpora against the ledgers'
`corpus_sha256` tables, and M4 does not copy them.

## Pins

`pins.json` holds three kinds of values:

- inputs M4 does not control: the IMP revision, the digests of the external
  k-rust and IMP files it relies on (`external_sha256`), and the corpus digest.
  The K and k-rust revisions, their tracked-tree digests, the K, kore-exec, LLVM
  backend, pyk, and Z3 versions, the MSRV, and the schema versions come from
  `Krs.lock`;
- outputs KRS produces: the artifact and native artifact digests, the
  source-definition projection digests, the LLVM capability diagnostic digest,
  the behavior summary, and the compatibility report digest;
- reviewed comparison policy: claim labels, the source-definition and term
  allowances, the native label map, and the 21 reference proof outcomes, which
  describe the upstream reference route rather than KRS output.

KRS source is not pinned, so a change that leaves every output identical passes
unchanged. After an intended output change, run the gate with `--record` (with
the same memory-bounded recipe below). It runs every phase and, only if all of
them pass, rewrites exactly the output pins it measured. It never rewrites an
input or a reviewed policy value; edit those deliberately.

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
