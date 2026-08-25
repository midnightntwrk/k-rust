# BAG-01: evidence and completion integrity

Status: initial integrity surface integrated; final BAG-01 closure rerun is
authorized only after BAG-09 through BAG-16.

## Objective

Make the backend-agnostic investigation complete and auditable at claim level,
not merely as a file inventory. Passing its zero-backend verifier must
establish that no goal clause, portable semantic relation, evidence boundary,
or residual proof requirement has silently been omitted. This packet does not
decide or implement missing product semantics; it runs last and may not turn an
unfinished portable question into generic “Rust future work.”

## Starting inputs

- `draft/goal/execution-pattern-matching.md`;
- `draft/goal/semantic-mutation-testing.md`;
- `draft/k-in-k-execution-roadmap.md`;
- `draft/k-in-k-r2-g-product-checkpoint-2026-08-19.md`;
- `draft/k-in-k-wave-1-checkpoint-2026-08-19.md`;
- all accepted or terminal records under `evidence/`, `investigations/w1-*`,
  `investigations/r2-g-*`, and the R3-G checkpoints; and
- `investigations/backend-agnostic-goal-closure/`; and
- integrated BAG-02 through BAG-16 packets and their schemas, fixtures,
  vectors, roles, identities, receipts, adversaries, and Rust proof seams.

## Required changes

1. Complete `evidence-inventory.json` for the accepted, superseded, rejected,
   and terminal evidence that materially supports or bounds the portable
   package. At minimum, account explicitly for W1 egress, W1 in-process
   adapter, W1 audit, W1 replay, R2-G-04, and R2-G-05. Do not promote an old
   backend result into cross-backend proof.
2. Add a machine-readable completion checklist mapping every normative
   acceptance area in both goal specifications to its portable artifacts,
   evidence state, remaining implementation proof, and closure status. A
   requirement may remain open; omission may not masquerade as closure.
3. Define in `README.md` the exact criteria for declaring this investigation
   package complete, including independent audit and roadmap/decision
   consistency.
4. Extend the zero-backend verifier so it requires the mandatory evidence IDs
   and checklist IDs/fields, validates referenced paths and closed values, and
   rejects a deliberately omitted required entry. Checks must be driven from
   an explicit normative manifest or explicit required-ID set rather than only
   iterating whatever entries happen to exist.
5. Correct `closure-matrix.json` only where evidence/completion classification
   itself is unsupported. Do not resolve the separately audited observation,
   execution, mutation, corpus, or replay semantic gaps in this packet.
6. Build an exact residual ledger from both goal specifications. Give every MVP
   bullet/acceptance clause and every material architecture claim a stable
   requirement ID, exact source citation, portable artifacts, positive
   derivation/check, permanent contradiction/adversary, bounded historical
   evidence where relevant, and exactly one terminal disposition:
   `portable-closed`, `portable-closed-rust-proof-pending`,
   `retired-stack-bounded`, `product-decision-held`,
   `product-decision-required`, or `out-of-scope-by-recorded-decision`.
7. Apply a necessity test to every Rust-open sentence: name the exact native
   fact needed and why no finite/backend-neutral artifact can establish it.
   Native production/fidelity, branch-discovery truth, solver feasibility,
   supported-IR adapter coverage/injectivity, actual lowering/termination,
   resource/isolation enforcement, store atomicity, and producer fidelity may
   qualify. Identity, status, order, denotation, schema, and reuse policy do
   not.
8. Replace older suite-cache/replay and whole-definition/lossless-term claims
   with BAG-09 through BAG-16 surfaces. In particular, classify same-sentence
   overlap algebra and same-result pattern kills as portable closed with native
   proof pending; describe BAG-13 as the supported portable semantic slice;
   and classify streaming/performance, old-backend repair, backend logs, C1/C2,
   and large-corpus work by their recorded product/scope decisions rather than
   vague `explicitly-held` or `rust-proof-required` labels.
9. Run a final graph audit: recompute every self-ID domain; enumerate every
   structured role/schema/domain; validate all `{role,digest}` and
   resolver-relative material requirements; prove invocation/receipt/report
   acyclicity and exact child consumption; cover every schema/operation version;
   and require exact definition/test/query/profile/policy agreement across
   corpus, mutation, cache, replay, and receipts.
10. Route every genuinely native BAG-09 through BAG-16 residual to the smallest
    dependency-ordered Rust proof packet without prescribing implementation
    APIs, commands, paths, or store layout.
11. Freeze the exact audit subject. Derive a cycle-free `subjectPackageDigest`
    from a normalized inventory of required artifact paths plus content
    SHA-256/semantic IDs, the requirement-ledger digest, verifier/version
    digest, and package version. Define whether audit/manifest records are
    outside that normative root or use an explicit two-stage root; never create
    a self-hashing cycle. Every independent audit binds that exact subject.
    Final `completionStatus: complete` additionally requires the live root to
    match, audit status complete with no pending findings, every required
    artifact present, every requirement terminally disposed, and every audit
    subject equal to the live root. A stale audit cannot remain complete after
    refresh or integration.

## Ownership

The integration worker may modify only:

- `investigations/backend-agnostic-goal-closure/README.md`;
- `investigations/backend-agnostic-goal-closure/evidence-inventory.json`;
- `investigations/backend-agnostic-goal-closure/closure-matrix.json`;
- `investigations/backend-agnostic-goal-closure/verify.py`;
- new completion-manifest/checklist files directly under
  `investigations/backend-agnostic-goal-closure/` or its `schemas/` directory;
- `investigations/backend-agnostic-goal-closure/completion-audit.md`; and
- `investigations/backend-agnostic-goal-closure/rust-stack-handoff.md` for
  residual-to-proof routing only.

The worker must not edit contracts, fixtures, vectors, product-goal files,
D1, roadmaps, historical checkpoints, accepted evidence, or task packets.
Record any required out-of-scope semantic correction in the worker report; do
not paper over it in completion classifications. After integration, use three
fresh non-overlapping read-only audits: execution/observation/query/corpus;
mutation/patch/oracle/cache/receipt/campaign; and completion inventory/D1/
roadmap/handoff. Root resolves findings serially, then repeats fresh audits on
the resolved revision.

## Acceptance

- `python3 investigations/backend-agnostic-goal-closure/verify.py` passes;
- the verifier fails when each mandatory evidence/checklist entry is omitted
  in a temporary in-memory or temporary-directory adversarial check;
- all referenced repository paths exist;
- every goal acceptance area is present even when its proof remains open;
- every portable-closed claim names its positive fixture, recomputed relation,
  and at least one permanent adversary, with no stale/unreachable citation;
- no unmatched goal clause and no untyped `pending`, `TODO`, or “future work”
  remains; every remainder is an exact native or product residual;
- fixture refresh is byte-idempotent, official Draft 2020-12 validation passes,
  and the final audit lists why every remaining residual is inherently
  nonportable;
- all three independent finding-by-finding audits are resolved on the final
  revision;
- no backend, K, Java, Rust executor, compiler, or solver command is run; and
- `git diff --check` passes for owned changes.

## Return contract

Return a concise report containing the verdict, files changed, commands run,
check count, omissions closed, still-open portable gaps, out-of-scope change
requests, and recommended next packet. Do not commit; root owns integration.

## Stop rule

Stop and report rather than inventing product semantics, claiming execution
proof, or editing outside ownership. Use bounded Python/text operations only.
