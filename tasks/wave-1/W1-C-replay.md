# W1-C: independent P1/P2/P3 replay

Status: authorized bounded investigation.

## Objective

Determine whether a fresh agent can reproduce the material P1, P2, and P3
conclusions from the repository and documented commands without relying on the
originating conversation.

The initial replay is diagnostic. It may not repair tracked source files.

## Starting inputs

- the baseline commit containing this packet;
- `draft/k-in-k-probe-p1.md`;
- `draft/k-in-k-probe-p2.md`;
- `draft/k-in-k-probe-p3.md`;
- `draft/k-in-k-oracles.md`;
- `p1/README.md`, `p2/README.md`, and `p3/README.md`; and
- the root package scripts.

## Procedure

1. Record the starting revision and relevant environment/tool versions.
2. Follow the documented installation/check prerequisites without altering
   tracked source.
3. Run the documented P1, P2, and P3 acceptance commands.
4. Capture each command, exit code, and relevant generated result digest.
5. Compare actual checks and normalized results with the corresponding report.
6. Classify any discrepancy as environment, documentation, nondeterminism,
   harness behavior, or substantive semantic mismatch.
7. For a failure, identify the smallest replayable blocker and proposed repair
   packet; do not fix it in this task.

## Owned paths

The agent may create or modify only:

- `investigations/w1-replay/**`;
- ignored build/output directories already used by the documented commands.

All tracked source, manifests, reports, and shared configuration are read-only.

## Required outputs

- `investigations/w1-replay/report.md` using the common worker return contract;
- one structured replay record per probe;
- exact commands, exit codes, environment facts, result paths, and digests;
- discrepancies and smallest follow-up packets, if any.

Do not copy large compiler logs into the report. Preserve them as referenced
artifacts when they materially explain a failure.

## Acceptance

Accept with `pass` when all three probes reproduce their material declared
checks from the starting revision.

Accept with `classified-discrepancy` when a probe does not reproduce but the
failure, environment, and smallest next packet are captured deterministically.

## Stop rule

Stop on a failure that requires tracked-source modification, unavailable
external credentials, a toolchain change, or more than one focused diagnostic
cycle beyond the initial replay. Preserve evidence instead of turning replay
into implementation.

