# BAG-09: semantic termination and crash-oracle boundary

Status: integrated and independently accepted, 22 August 2026 (203,865
zero-backend checks, including official Draft 2020-12 validation).

## Objective

Distinguish a language-level semantic crash from an executor/backend failure
and make its pattern and mutation-oracle consequences derivable. The current
taxonomy deliberately leaves `semantic-crash` outside its outcome rules, a
pre-path pattern case maps it to `error`, and mutation-oracle validation may
map the same untyped failure object to `distinguish` without recording whether
the baseline, mutant, or both crashed.

This packet closes portable report semantics. The future Rust stack still has
to prove that a native terminal configuration was classified correctly.

## Normative model

A **semantic crash** is a trustworthy terminal result of the object-language
semantics under the pinned execution profile. It is data, not a report
failure. A process exit, panic, malformed backend response, worker loss,
resource stop, or inability to establish that terminal result is never a
semantic crash; it remains the corresponding backend, infrastructure, report,
or limit failure.

Represent every executed side of an oracle comparison with one typed terminal
operand:

```text
normal(valueDigest)
semantic-crash(crashDigest)
```

`crashDigest` uses `k-in-k/semantic-crash/v1` over the execution-profile
identity, the terminal configuration/result digest, and a closed
object-language crash classification. Do not use host exception text, process
status, stderr, stack traces, or pretty-printed K as identity. The portable
fixtures may supply this record; only native Rust evidence can prove its
derivation from execution.

### Resolved v1 terminal artifacts

After BAG-08, add exactly two structured artifact roles:

- `terminal-state`: canonical JSON
  `{schemaVersion, terminalStateDigest, value}` where `value` is one lossless
  portable term/result, identified in `k-in-k/terminal-state/v1` over the
  object without `terminalStateDigest`; and
- `semantic-crash`: canonical JSON
  `{schemaVersion, crashDigest, executionProfileDigest, terminalState,
  classification}` where `terminalState` is a BAG-08 key with role
  `terminal-state`, `classification` is exactly
  `declared-object-language-crash` in v1, and `crashDigest` is derived in
  `k-in-k/semantic-crash/v1` over the object without its self-ID.

The single crash classification is intentional: v1 records that the pinned
object-language semantics declares a crash, without inventing portable
language-specific exception categories. BAG-13 owns local portable-state
well-formedness; native configuration coverage/injectivity and proof that the
state came from the recorded execution remain Rust-owned.

Add one shared `executionTerminal` union to an event trace and copy it into
the corresponding pattern path record:

```text
normal(terminal-state key)
stuck(terminal-state key)
semantic-crash(semantic-crash key)
null
```

The relations are exact: `complete` is true iff the terminal is non-null;
`stopReason=terminal` admits `normal` or `semantic-crash`;
`stopReason=stuck` admits `stuck`; and query-satisfied, limit, solver, and
error stops require `complete=false` and null terminal evidence. A crash is a
`terminal` stop, not a new stop-reason enum. The path record's terminal must
equal its resolved trace terminal exactly. Witnesses continue to resolve
through that path. BAG-16 owns branch-set/global visited-versus-unvisited
completeness rather than this per-path primitive.

Remove `semantic-crash` from the generic failure classification enum and
failure outcome table. This makes that table total without a semantic-crash
verifier exception. Also close the table's existing `baseline-mismatch`
exception explicitly: in baseline-oracle context it derives
`baseline-oracle-failed`, aborts scoring, and is invalid in pattern, candidate,
or mutant outcome contexts. If retaining a historical semantic-crash input
spelling is necessary, reject it at the v1 interchange boundary rather than
silently interpreting it in two contexts.

## Pattern semantics

A path ending in a proven semantic crash is complete semantic execution, just
as another terminal object-language result is complete. Pattern matching still
examines the path's trustworthy event sequence:

- a witness before termination yields `match`;
- exhaustive absence on the complete crashed path yields `no-match`; and
- malformed/missing crash evidence yields `error`, while bounded or solver
  uncertainty remains `unknown`.

Add a typed terminal-result field to the trace/path evidence instead of
encoding semantic termination as a failure. A test-scoped “semantic crash
before any trustworthy path exists” is impossible: it is a backend/report
error because no semantic terminal path was produced.

## Mutation-oracle semantics

Do not use one record shape for baseline admission and mutant comparison.
Baseline-oracle results contain one baseline side and derive exactly one of
`accepted`, `timeout`, `unknown`, or `error`; they never manufacture a second
copy and compare the baseline to itself. Every oracle declaration has an
explicit `baselineTerminalPolicy` of `normal-required` or
`semantic-crash-allowed`, covered by manifest/report identity. A well-formed
baseline crash is accepted only by `semantic-crash-allowed`; under
`normal-required` it derives the explicit baseline-oracle-gate
`baseline-mismatch` disposition and aborts scoring. A normal terminal is
eligible under both. BAG-12 may later specialize baseline assertions by oracle
kind but must preserve this intentionality.

Mutant comparison results use one canonically ordered `operands` array with
exactly the `baseline` slot followed by the `mutant` slot. Each slot contains
one tagged normal operand, one tagged semantic-crash operand, or null. A
normal operand contains one BAG-08 key: role `pattern-result` for an
execution-pattern oracle and role `oracle-value` until BAG-12 specializes the
other kinds. A crash operand contains its `semantic-crash` key. Side is a
structural field, never encoded into the artifact role.

Keep one optional typed failure wrapper with `source` equal to
`baseline-execution`, `mutant-execution`, or `comparison`. The source makes
absence derivable: a baseline failure may prevent both operands, a mutant
failure retains the baseline operand, and a comparison failure requires both
operands. `skipped` alone has two null operands and no failure. No null side is
otherwise permitted. BAG-12 owns kind-specific normal operands and nontrivial
comparison receipts; BAG-15 later binds produced operands to exact attempts.

Derive the crash cases symmetrically:

- two normal operands use the declared projection/comparison and existing
  value equality rules;
- identical `semantic-crash` operands `agree`;
- one normal and one semantic crash, or two different semantic crashes,
  `distinguish` under `semantic-crash-distinguishes` and are `incomparable`
  under `semantic-crash-incomparable`; and
- absent operands are permitted only for `skipped` or when accompanied by the
  typed timeout/unknown/error failure that prevented the operand from being
  produced.

Both operands must retain role-typed value/crash artifacts in canonical
baseline-then-mutant order. A baseline semantic crash is not automatically a
campaign setup failure: an oracle may intentionally assert or compare
object-language failure behavior. A backend or infrastructure crash on either
side is always `error` and can never kill a mutant.

For mixed normal/crash or different-crash operands under
`semantic-crash-incomparable`, retain both operands and attach a
comparison-source `oracle/incomparable-result` failure so downstream
test/mutant exclusion is explicit. Identical crashes agree under either crash
policy. Backend, process, worker, report, limit, and solver failures never
become operands and never distinguish.

Mutant/test/campaign status and scoring derive from these oracle outcomes
exactly as for other comparisons. No special case may infer a kill directly
from a failure classification.

## Required evidence

- a complete semantic-crash path with a prior witness yields `match`;
- a complete semantic-crash path without a witness yields `no-match`;
- missing or untrustworthy terminal evidence cannot produce either result;
- normal/normal equal and unequal comparisons retain current behavior;
- crash/crash with identical identity agrees;
- crash/crash with different identities and normal/crash exercise both crash
  policies, in both baseline/mutant orientations;
- a baseline crash accepted by its oracle is representable without aborting
  the campaign; and
- backend/infrastructure failure on either side is always `error`.

Permanent adversaries must reject the old generic semantic-crash failure,
host-exception-derived crash identity, an operand with both normal and crash
values, a crash with no terminal evidence, a one-sided record that does not
identify the side, policy/outcome drift, a crash distinction with missing
operand artifacts, an infrastructure failure reported as a kill, and a
pattern `error` caused solely by a well-formed semantic terminal path. Also
reject `baseline-mismatch` outside the baseline-oracle gate and any taxonomy
entry left without a context-specific outcome/disposition.

More exactly, cover wrong crash/self IDs; terminal-state/profile drift after
refreshing enclosing IDs; dangling or wrong-role keys; unknown crash class;
diagnostic exception/stderr/exit/stack fields in semantic identity; incomplete
trace with a terminal; complete trace without one; crash paired with
stuck/limit/error stop; trace/path terminal drift; crash paths carrying a
generic failure; reordered/duplicate/missing operand sides; null sides without
the exact-source failure; skipped results with operands or failure; identical
crashes claimed different/incomparable; mixed/different crashes claimed agree;
both orientations under both policies; a fake baseline self-comparison;
missing baseline terminal policy; a crash accepted under `normal-required`;
a normal terminal rejected solely by either terminal policy; and policy drift
without changed manifest/report identity.

## Ownership

The worker may modify failure taxonomy prose/JSON, common/event-trace,
pattern-result, mutation-manifest/campaign schemas, minimal trace/campaign
fixtures, execution/mutation/failure vectors, contracts, verifier, refresh
helper, catalog roles where typed crash artifacts require them, completion
evidence, and Rust handoff terminal-result notes. Integrate after BAG-05 and
BAG-06; integrate after BAG-08 if it changes shared artifact references. Do
not edit goals/D1/roadmap, decide how Rust recognizes an object-language crash,
or run backend code.

BAG-09 owns only the terminal-state/crash primitive, trace/path terminal
relation, side-bearing crash shell and truth table, surgical removal of the
generic crash failure, and one explicit baseline-mismatch gate mapping. BAG-10
owns the complete taxonomy schema and context/disposition proof; BAG-12 owns
the six normal oracle kinds and their projection/comparison semantics; BAG-14
owns cache completeness; and BAG-15 owns producing invocation/receipt
provenance. Content-addressed/profile-bound crash evidence in BAG-09 is not a
claim that a backend produced it.

## Acceptance

- the failure taxonomy is total and has neither `semantic-crash` nor
  `baseline-mismatch` escape hatches;
- semantic termination is typed, side-specific, replay-identifiable, and
  distinct from backend/infrastructure failure;
- pattern and mutation outcomes derive from one consistent terminal model;
- baseline/mutant orientation and both crash policies are permanently tested;
- no backend failure can become a semantic distinction;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

## Stop rule

Stop rather than deriving semantic crashes from host failures, treating an
opaque exception digest as proof, or claiming the Rust backend classifies
terminal configurations correctly.

The portable verifier cannot determine what a dishonest hex digest was
originally derived from. It can forbid host-diagnostic fields, require exact
terminal/crash graph resolution, and reject host failures substituted as
semantic operands. Only native evidence can establish that a real terminal
configuration was recognized and normalized faithfully.
