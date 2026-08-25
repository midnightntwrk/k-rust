# BAG-04: canonical JSON boundary

Status: integrated backend-agnostic closure packet.

## Objective

Make direct canonicalization and digest derivation accept exactly the same
portable JSON value domain as file loading. Invalid in-memory host values must
be rejected deliberately before Python sorting, serialization, UTF-8 encoding,
or hashing can coerce them or raise an incidental exception.

This is a portable identity-boundary packet. It does not alter K semantics,
mutation selection, observation selection, schemas, replay flow, or backend
execution.

## Starting inputs

- `investigations/backend-agnostic-goal-closure/contracts.md`, section 1;
- `canonical`, `digest`, `load`, `unique_object`, and `reject_floats` in
  `investigations/backend-agnostic-goal-closure/verify.py`; and
- `investigations/backend-agnostic-goal-closure/vectors/canonicalization-vectors.json`.

## Normative portable value domain

Canonical JSON and every domain-separated digest accept only an acyclic value
tree built from these exact host value classes:

- null;
- booleans;
- signed 64-bit integers;
- Unicode NFC strings without UTF-16 surrogate code points;
- arrays represented by lists; and
- objects represented by dictionaries whose keys are strings satisfying the
  same NFC/surrogate rule.

Everything else is rejected. In particular:

- every float is forbidden, including finite values, negative zero, NaN, and
  positive or negative infinity;
- integers below `-(2**63)` or above `2**63 - 1` are forbidden;
- non-NFC strings and object keys are forbidden;
- any surrogate code point is forbidden in values or keys;
- tuples are not silently treated as arrays;
- sets, bytes, byte arrays, complex numbers, decimals, paths, enums, custom
  objects, and custom container/scalar subclasses are not coerced; and
- non-string dictionary keys are forbidden even when Python's JSON encoder
  could stringify them.

Booleans are booleans, not integers, despite Python's subclass relationship.
Repeated references to one acyclic value are permitted and serialize by value;
a direct or indirect list/dictionary cycle is not a JSON value and is rejected.

Duplicate object keys remain a parse-time error through `unique_object`.
Direct dictionaries cannot retain evidence of a duplicate that was already
overwritten, so direct canonicalization makes no impossible claim to recover
it.

## One shared preflight validator

Replace the loader-specific `reject_floats` boundary with one shared recursive
portable-value validator used by all three entry points:

1. `load` parses with duplicate-key detection, then validates the result;
2. `canonical` validates before invoking the serializer; and
3. `digest` obtains bytes only through the validated canonical function.

No caller may bypass this preflight by calling `digest` directly. Validation
must finish before `sort_keys`, JSON escaping, UTF-8 encoding, or SHA-256
processing begins. Serializer flags such as `allow_nan=False` are useful
defense in depth but are not the normative validator.

Use exact type checks where Python subclass behavior could coerce a nonportable
value. Track active list/dictionary identities to detect cycles without
rejecting harmless shared acyclic subvalues.

## Deterministic failures

Every invalid value must fail with the package's deliberate validation
exception, not an incidental `TypeError`, `ValueError`, `OverflowError`,
`UnicodeEncodeError`, recursion error, or serializer-specific message.

Failure diagnostics must contain a closed reason code and a stable structural
location. Suggested reason codes are:

- `unsupported-json-type`;
- `non-string-object-key`;
- `floating-point-forbidden`;
- `integer-out-of-range`;
- `non-nfc-string`;
- `surrogate-code-point`; and
- `cyclic-json-value`.

The implementation may preserve the current assertion-based verifier style,
but repeated validation of the same input must produce the same reason and
location. Diagnostics must not call user-defined conversion or representation
methods on unsupported objects. When one value contains several faults, use a
documented stable precedence/traversal rule or collect faults and select a
canonical first fault; do not let serializer iteration choose the error.

Object-key order remains semantically irrelevant for valid values. Validation
must not mutate or normalize the caller's object in place.

## Canonical serialization after validation

After successful preflight, retain the existing canonical decisions:

- NFC object keys sorted by Unicode code point;
- compact separators and no insignificant whitespace;
- JSON booleans and null in lowercase;
- shortest decimal spelling for signed 64-bit integers;
- required JSON escaping only;
- non-ASCII scalar values emitted directly; and
- UTF-8 bytes for domain-separated SHA-256.

Existing accepted canonical strings and digests must remain unchanged. This
packet closes acceptance at the boundary; it does not introduce a new digest
domain or package version.

## Required changes

1. Introduce one preflight validator implementing the exact domain above and
   route `load`, `canonical`, and `digest` through it.
2. Ensure validation occurs before sorting, serialization, UTF-8 encoding, and
   hashing. Preserve serializer safety flags as defense in depth.
3. Detect list/dictionary cycles deliberately while permitting repeated
   acyclic references.
4. Produce deterministic closed failure reasons and stable locations without
   invoking unsupported host-object methods.
5. Extend canonicalization vectors and direct in-memory verifier checks for all
   positive boundaries and mandatory adversaries below.
6. Clarify the section-1 contract so it applies to every in-memory identity
   payload, not only JSON artifacts loaded from disk.

## Positive evidence

Permanent bounded checks must prove:

- null, booleans, strings, lists, and dictionaries remain accepted;
- `-(2**63)` and `2**63 - 1` remain accepted with unchanged canonical decimal
  spelling;
- valid NFC non-ASCII keys sort canonically by Unicode code point;
- the existing canonicalization-vector strings and hashes are unchanged;
- a shared acyclic child value can occur more than once; and
- canonicalization does not mutate input arrays, objects, keys, or strings.

## Mandatory direct adversaries

Call both `canonical` and `digest` directly with small in-memory values and
prove deterministic rejection of:

- a finite float, `-0.0`, NaN, positive infinity, and negative infinity;
- both signed-64 overflow boundaries;
- a non-NFC string value and a non-NFC object key;
- a surrogate in a string value and in an object key;
- tuple, set, bytes, byte array, complex, decimal, and one custom object;
- custom subclasses of an otherwise accepted scalar and container;
- integer, boolean, null, and tuple object keys;
- a direct list cycle, direct dictionary cycle, and indirect mixed cycle;
- an invalid nested value beneath otherwise sortable keys; and
- a mixed-key object that would otherwise fail accidentally during
  `sort_keys=True`.

For every case, assert the deliberate reason code and stable location, and
assert that neither sorting nor UTF-8/serializer exceptions escape. Repeat
each check at least once to establish deterministic failure. Include at least
one object-key permutation case proving the documented multiple-fault rule is
stable.

Also retain the duplicate-key parse adversary and show that `load` and direct
canonicalization share every rejection rule that can exist in both input
forms.

## Ownership

The worker may modify only:

- `investigations/backend-agnostic-goal-closure/contracts.md`, section 1 and
  directly related canonicalization prose;
- `investigations/backend-agnostic-goal-closure/vectors/canonicalization-vectors.json`;
- canonicalization/loading helper code and its direct tests inside
  `investigations/backend-agnostic-goal-closure/verify.py`; and
- completion inventory references only if a newly added canonicalization
  vector artifact requires a mechanical entry.

Do not edit mutation schemas, registries, campaigns, or vectors owned by
BAG-02. Do not edit observation schemas, fixtures, or vectors owned by BAG-03.
Do not refresh unrelated fixture identities, edit goals/D1/roadmaps/historical
evidence, or add backend implementation code.

## Acceptance

- the zero-backend verifier passes after serial integration;
- every mandatory direct adversary rejects with its intended closed reason and
  no incidental host exception;
- existing valid canonical strings and digests are byte-for-byte unchanged;
- loader, canonical, and digest acceptance boundaries agree;
- validation demonstrably precedes sorting, serialization, UTF-8 encoding, and
  hashing;
- repeated invalid calls and the multiple-fault permutation case have stable
  diagnostics;
- valid shared acyclic values remain accepted and cyclic values reject;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- all checks are tiny in-memory values with bounded CPU and memory use; and
- `git diff --check` passes for owned changes.

## Return contract

Return a concise report containing the verdict, files changed, commands run,
zero-backend check count, preserved canonical hashes, mandatory adversary
reason/location results, cycle/shared-reference results, and any out-of-scope
identity issue discovered. Do not commit; root owns integration.

## Stop rule

Stop and report rather than accepting a host coercion, relying on serializer
exceptions as validation, changing accepted digest bytes, editing BAG-02 or
BAG-03 files, expanding into schema/backend behavior, or running backend
commands.
