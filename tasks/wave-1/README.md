# Wave 1 task packets

Status: authorized task packets for the first orchestration wave begun on
19 August 2026.

All packets start from the baseline commit containing this directory. Each
agent must record the resolved `git rev-parse HEAD` value before doing work.
Agents work only in their assigned Git worktree and may not spawn subagents.

The three packets are:

- `W1-A-egress.md`: official-K ingress/configuration/egress investigation;
- `W1-B-audit.md`: independent capability and oracle audit; and
- `W1-C-replay.md`: independent P1/P2/P3 replay.

Common rules:

1. Preserve raw evidence under the packet's unique investigation directory.
2. Do not edit the roadmap, goal contracts, probe reports, root package
   manifests, or another packet's paths.
3. Treat existing source and reports as claims to test, not as conclusions that
   must be defended.
4. Record exact commands, environment assumptions, and artifact digests.
5. Stop rather than broaden the task when the packet's stopping condition is
   reached.
6. Commit accepted task-owned files on the worktree branch and return the
   commit hash. A classified blocker may return an evidence-only commit.
7. Do not merge, rebase, or cherry-pick other work. The root agent integrates.

Each final report must contain:

```text
verdict
starting revision
commands executed
evidence paths and digests
acceptance checks passed and failed
newly discovered contracts
requested shared-contract changes
remaining unknowns
recommended next packet
```

