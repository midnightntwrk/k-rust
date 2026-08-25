# W1-B: Gate D capability and oracle audit

Status: authorized bounded investigation.

## Objective

Independently audit the current complexity reconnaissance and produce a
candidate machine-readable classification that distinguishes immediate G1
work from conditional compiler-independence work.

This is an audit, not implementation and not a rewrite of the roadmap.

## Starting inputs

- the baseline commit containing this packet;
- `draft/k-in-k-complexity-plan.md`;
- `draft/k-in-k-execution-roadmap.md`;
- `draft/k-in-k-oracles.md`;
- all three probe reports;
- both goal feature contracts; and
- the pinned upstream source references named by the complexity plan.

## Questions

1. Are all 42 top-level capability groups represented and correctly bounded?
2. Which leaves are G1-required, conditional C1, C2, or optional?
3. What dependency edges and coupled ownership clusters constrain sequencing?
4. Which oracle grade actually supports each current conclusion?
5. Where are negative behavior, interaction coverage, or observation seams
   missing?
6. Which probe conclusions are narrower than wording elsewhere implies?
7. Which G1 leaves lack a deterministic acceptance command?

## Candidate matrix contract

Produce a machine-readable candidate matrix whose leaf entries include at
least:

```text
id
parent capability group
description
roadmap track
dependencies
coupled cluster or owner
current oracle grade
candidate acceptance command or missing-command marker
evidence references
status
unknowns
```

The candidate is audit evidence. The root agent decides whether to promote it
to the canonical matrix and may revise its schema during integration.

## Owned paths

The agent may create or modify only:

- `investigations/w1-audit/**`.

All existing plans, roadmaps, reports, source, and harnesses are read-only.

## Required outputs

- `investigations/w1-audit/report.md` using the common worker return contract;
- `investigations/w1-audit/capabilities.json` or `.csv`;
- a concise list of material omissions, overclaims, and unresolved oracle
  gaps, each with source references;
- a dependency/ownership summary sufficient for root integration.

## Acceptance

Accept when every top-level group is accounted for, every candidate leaf has a
track and evidence status, missing information remains explicit, and the
report is reproducible from files rather than conversation history.

## Stop rule

Stop rather than implementing missing behavior, modifying upstream sources, or
expanding into a complete F2/F3 product audit. If exact leaf decomposition is
blocked by unavailable evidence, preserve a named unknown and the narrowest
follow-up rather than guessing.

