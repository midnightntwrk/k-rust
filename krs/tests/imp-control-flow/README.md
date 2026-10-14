# Independent IMP control-flow oracle

This directory freezes the external acceptance contract for the third explicit IMP vertical slice.
The verifier reads the KAST JSON output of the pinned K command-line tools through k-rust's reader in krs-gate.
Oracle independence rests on Java K having produced that output:
by default the verifier replays the Java K results of the reference snapshot `oracle` from the per-user reference cache,
and runs the pinned K tools live when the cache does not hold them or under `--refresh-reference`.
Neither the handwritten definition nor the corpus may import a KRS crate or KRS-generated artifact.

`fixtures/imp.k` layers directly on `tests/imp-state/fixtures/calc.k` with an ordinary
`requires`. It is a module-renamed transcription of modern IMP `imp.k` and
preserves all of its control-flow surface:

- `if` with and without `else`;
- `strict(1)` condition evaluation on the else-bearing form;
- the `avoid` resolution of the dangling-else ambiguity;
- deliberately non-strict `while` conditions;
- nonempty and empty blocks; and
- the labeled `if-true`, `if-false`, `if-else`, `while`, `block`, and `done`
  rules.

The reference toolchain is the K release `Krs.lock` pins. The upstream
sources are modern IMP commit `683a773418add3bcae8ded47c2b24e94494e1988`. Exact
upstream, inherited IMP state, corpus and fixture (`corpus_sha256`), definition, parse, execution, search, rejection, and
diagnostic hashes are recorded in `pins.json`.

## Parse and execution corpus

The eight accepted programs freeze empty/nonempty blocks, both outcomes of an
`if` without `else`, explicit `else`, nearest-`if` dangling-else binding,
control followed by another statement, and nested `if`/block/`while` forms.
Every source is checked with both `kast` and `kparse`; program unparsing must
reparse to the identical full KAST v4 tree.

| Program | Exact LLVM rewrites | Final environment | Main distinction |
| --- | ---: | --- | --- |
| `empty-block.imp` | 1 | `.Map` | empty block becomes `.K` |
| `if-true.imp` | 3 | `x |-> 1` | no-else desugaring, true branch |
| `if-false.imp` | 3 | `.Map` | no-else desugaring, implicit empty branch |
| `explicit-else.imp` | 2 | `x |-> 2` | false explicit branch |
| `dangling-else.imp` | 9 | `x |-> 1, y |-> 0` | `else` binds the nearest `if` |
| `block-sequence.imp` | 19 | `x |-> 1, y |-> 2, z |-> 3` | block framing and following code |
| `while-followed.imp` | 83 | `x |-> 0, y |-> 1` | repeated condition evaluation and continuation |
| `nested-control.imp` | 59 | `x |-> 0` | nested branch, block, and loop interaction |

All 187 configurations from depth zero through each accepted normal form are
hash-pinned. The depth-one states for both no-else cases are also inspected
structurally: their computation head must be the three-argument `if`/`else`
form produced by the labeled `[if-else]` rule.

## Search and nontermination

The LLVM definition is compiled with search enabled. Sixteen bounded
frontiers are retained across explicit branching, dangling-else control, and
`while (true) {}`. Every `--search --depth N` invocation must yield exactly one
`#Equals(Result, frontier)` solution and that frontier must equal ordinary
depth-bounded execution at the same depth.

The infinite loop is checked at depths 0, 1, 2, 3, 4, 8, 16, and 32. Every
exact configuration and search wrapper is hash-pinned, and none may have an
empty computation cell. This tests bounded nontermination without a timing
assumption or a timeout-as-success escape hatch.

## Structure, rejects, and diagnostics

The parsed definition must contain exactly five local control productions and
six labeled control rules, while retaining the IMP state expression and state
modules. The verifier checks `strict(1) + avoid` on the else-bearing
production, the absence of `strict` on `while`, exactly one new generated
strict context, 58 compiled rules, and 26 heat/cool pairs.

Four malformed programs freeze exact inner-parser diagnostics for a missing
condition, a missing else body, a stray else, and an unclosed block. Three
well-sorted parses freeze exact stuck states for integer and undefined
conditions. The induced outer-parser error separately proves that K selects
the authored `@` at `fixtures/induced-definition-error.k:2:27-2:28`.

## KRS implementation requirements exposed by this oracle

IMP control flow requires complete vertical support for:

1. five additional `Stmt` productions, including production-level `avoid`,
   formatting, and a strict argument position;
2. condition evaluation contexts and generated heat/cool rules without making
   `while` itself strict;
3. simultaneous computation-cell rewrites over `if`, `while`, block, `.K`,
   and `~>` terms;
4. no-else normalization into the existing else-bearing constructor;
5. exact source-local rule labels and nested term provenance; and
6. concrete depth bounds plus deterministic bounded-search result decoding.

## Verification

Run exactly:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/imp-control-flow/verify.py
```

With a warm reference cache the verifier needs no K tool.
`pins.json` `reference_sha256.oracle` pins the manifest digest of the snapshot, and the verifier replays the cache entry stored under it
(`tests/support/reference.py`; `${XDG_CACHE_HOME:-~/.cache}/krs/reference-outputs/v1` by default).
The manifest holds the snapshot key
(the `Krs.lock` K version, the K tools, and the digest of every fixture and corpus file)
and the digest of every stored file.
The stored `parsed.json` and `compiled.json` keep every module and sentence but omit the metadata attributes
(source locations, install paths, and production identifiers) that the normalized definition hashes remove,
and list each module's `localSentences` and `imports` in sorted order,
because K writes both in an order that varies between runs and checkouts and every check reads them as sets.
A cached entry whose key or argument vectors differ from the current ones fails closed;
the verifier never falls back from a cached entry to running Java K.

When the cache does not hold the pinned entry, the verifier runs the pinned K 7.1.337 tools live, from `KRS_K_BIN` or `PATH`,
and fails closed naming a missing tool.
The live result must reproduce the pinned digest, and it is stored only when every check passes.
After an intended change to a fixture, a corpus file, or the K version, re-record the pins with the K tools available:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/imp-control-flow/verify.py --refresh-reference --record
```

`--refresh-reference` reruns every invocation live whatever the cache holds,
and `--record` rewrites the output pins in `pins.json`, including `reference_sha256`.

On a disk-constrained host, set `KRS_IMP_CONTROL_FLOW_ORACLE_WORKERS=1` to serialize the
same pinned checks and reduce simultaneous K scanner temporaries. The default
remains up to eight workers; worker count does not change oracle inputs,
normalization, hashes, or assertions.
