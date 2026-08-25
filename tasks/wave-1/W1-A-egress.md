# W1-A: official-K ingress, configuration, and egress

Status: authorized bounded investigation.

## Objective

Determine whether the G1 definition-transformation path can round-trip through
the pinned official K toolchain, and identify the exact ingress,
configuration-generation, and egress trust boundaries.

This packet investigates K-in-K transforming a typed definition and returning
an accepted artifact to official K. It does not implement independent semantic
lowering or Kore emission.

## Starting inputs

- the baseline commit containing this packet;
- K v7.1.337 at commit
  `4a46d1231473b599c699160132fd6e76a5c46406`;
- `draft/k-in-k-execution-roadmap.md`, especially sections 2, R1, and R2-G;
- the P1 and P3 reports and executable fixtures;
- the oracle harness and its normalization policy.

## Questions

1. What supported or replayable artifacts can official K accept after a
   definition transformation?
2. Can parsed, disambiguated source sentences and configuration terms be
   transformed before configuration generation and then compiled normally?
3. If not, what post-configuration boundary works, and exactly which CF
   behavior becomes trusted?
4. Can an identity transformation preserve selected structural artifacts and
   backend behavior?
5. Can one small sentence edit and one observation-cell/configuration edit be
   represented, returned, compiled, and executed deterministically?
6. Which identity and provenance fields survive each candidate route?

Evaluate, where available:

- a supported structured compiler API;
- canonical generated K source;
- another structured/replayable definition artifact; and
- a temporary post-configuration adapter.

Do not claim a route works based only on serialization. It must re-enter
official K and reach the selected structural and behavioral oracle.

## Fixtures

Use at least two structurally different fixtures:

- Peano or Foobar for a small rule/function definition; and
- the P3 or another small IMP-like nested-configuration fixture.

The identity route must be tested on both. A minimal transformation may be
feature-isolated if configuration augmentation is not yet possible, but the
limitation must be explicit.

## Owned paths

The agent may create or modify only:

- `investigations/w1-egress/**`.

Existing fixtures, adapters, oracle code, and reports are read-only. If a
harness defect blocks the investigation, preserve the evidence and request a
separate repair packet rather than changing shared code.

## Required outputs

- `investigations/w1-egress/report.md` using the common worker return contract;
- machine-readable results and exact invocations under the same directory;
- a candidate adapter decision stating the preferred route, trust boundary,
  limitations, and fallback;
- replay commands that start from the recorded revision.

## Acceptance

Accept with `pass` if at least one route demonstrates identity re-entry for both
fixtures, preserves the declared structural and behavioral oracle, and either
demonstrates one safe transformation or precisely isolates the next missing
contract.

Accept with `classified-blocker` if no route works but every attempted route,
failure boundary, and smallest next experiment is preserved reproducibly.

## Stop rule

Stop after three substantive full-oracle cycles without acceptance, or when
progress would require modifying shared official-K adapters, implementing
independent lowering/Kore emission, or expanding the fixture beyond the stated
questions.

