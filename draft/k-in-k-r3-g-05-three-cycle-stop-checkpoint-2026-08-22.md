# R3-G-05 three-cycle stop checkpoint — 22 August 2026

Status: stopped at the packet's three-substantive-full-oracle-cycle cap. R3-G-05
is not accepted, R3-G exit evidence is not complete, and R3-G-06 is not active.
No fourth R3-G-05 cycle is authorized by this checkpoint.

## Clean source state

The current isolated implementation lineage is clean head
`d1523d8911523a6aa6603fb266e8c25c5ca1c449` on
`agent/r3-g-05-metadata-repair`, over final-cycle activation
`4006fac28ec20f47f136593fd135da36ccee4ea7`. Its complete bounded
zero-backend replay, Python compilation, shell syntax, scope audit, and
`git diff --check` pass. It is not integrated acceptance evidence.

The final repair binds every parser negative to changed bytes. Cycle 3's
`R3-G-05-parser-canonicality-v1` record confirms the canonical positive plus
all seven negatives passed with zero backend invocations and no constructed
output definition.

## Substantive cycle ledger

All three ignored outputs are failed-run provenance. They are never reusable,
finalizable, publishable, or committed as accepted evidence.

| cycle | clean head | fresh output | terminal boundary | result |
| ---: | --- | --- | --- | --- |
| 1 | `014d77690977805d06b9d4a1c3a334afb0fd5678` | `build/cycle-1-r3-g-05i` | `frontend-setup`, status 1 | driver `javac` exposed `productionStructure` scoped inside sibling `TraceAdapter`; no K definition/backend artifacts |
| 2 | `940d90172f360fa48e9b848516e419b200e6756f` | `build/cycle-2-r3-g-05j` | `frontend-setup`, status 1 | driver compiled; parser self-test exposed a no-op missing-delimiter adversary; no K definition/backend artifacts |
| 3 | `d1523d8911523a6aa6603fb266e8c25c5ca1c449` | `build/cycle-3-r3-g-05k` | `configuration-compile`, status 113 | driver and parser self-test passed; first Haskell configuration compilation produced provisional artifacts, then failed launching `kore-exec` |

Each cycle was substantive because its frontend/compiler result drove the next
repair or established the final boundary. No cycle failed from memory pressure.
The cycle-3 watchdog observed only 383,952 KiB peak session RSS, preserved the
4 GiB available-memory and 1 GiB swap floors, terminated/reaped the exact
session, and left `targetSessionEmpty: true`.

## Final boundary

Cycle 3's exact compiler diagnostic is:

```text
[Error] Critical: Error with I/O while executing kore-parser (IOException:
Cannot run program "kore-exec" (in directory
"/proc/self/fd/4/configuration-k-kompiled/."): error=2, No such file or
directory)
```

This is not a missing installation. In the same environment:

- `command -v kore-exec` resolves to
  `/home/sebdev20/.nix-profile/bin/kore-exec`;
- the pinned K package exposes its own `bin/kore-exec`; and
- `kore-exec --version` succeeds as `0.1.155`.

The failure strongly localizes to the secure output descriptor boundary. The
raw shell intentionally addresses its reserved output as `/proc/self/fd/4`.
`kompile` can create the definition there, but its JVM subsequently launches a
nested executable with a working directory beneath that descriptor path. The
child-spawn mechanism closes or cannot resolve the inherited descriptor before
the `chdir`/exec boundary, so an otherwise available `kore-exec` receives an
ENOENT launch failure.

Cycle 3 contains `configuration-k-kompiled/{compiled.bin,definition.kore,
backend.txt}` from the failed compiler attempt. They are provisional failure
artifacts only. There is no raw success, integrity manifest, finalized evidence,
or accepted R3-G-05 report.

## Stop decision

The next work is not R3-G-06 and not another raw retry. Resumption requires a
new root-owned split/repair authorization that explicitly addresses the
descriptor-rooted output versus nested compiler-child working-directory
contract, supplies zero-backend process-boundary adversaries, assigns a new
cycle policy, and preserves no-follow/no-replace output security. It must not
silently fall back to an unvalidated path or reuse any of the three outputs.

Until that decision is written and activated:

- R3-G-05 remains stopped and unaccepted;
- R3-G-06 through R4-G-05 and D1 remain dependency-blocked;
- no compiler/backend cycle is authorized; and
- C1, C2, optional leaves, and streaming monitors remain inactive.
