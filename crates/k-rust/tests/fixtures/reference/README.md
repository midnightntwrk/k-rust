# Reference-derived fixtures

Each subsystem directory contains small artifacts produced by the K v7.1.337 reference toolchain at revision `4a46d1231473b599c699160132fd6e76a5c46406` and the Haskell backend `0.1.155` (`38afc81`).
Every case has a `reference.toml` that records each generated artifact's command, tool, exit code, and SHA-256 digest.
Hand-written inputs use `[[input]]`; a documented specification answer that intentionally differs from the toolchain uses `[[expectation]]` and names its source.
Tests consume the committed artifacts and therefore must not require the reference toolchain.

Project-authored probe paths describe their scenarios.
Their K module names and literal program tokens are retained where they identify symbols in captured KORE; those spellings are fixture inputs, not case identifiers.
Recorded refresh commands select the retained modules explicitly.

The `outer/undefined-sort` and `outer/undefined-sort-unrelated` diagnostics normalize the temporary source-directory prefix to `Source(test.k)`.
Their recorded commands repeat that normalization and preserve the compiler exit code; their SHA-256 digests cover the normalized captures.
Only the path prefix was changed in the existing captures; the diagnostic text was not remeasured.

Run `K_REFERENCE_REFRESH=1 scripts/reference-fixtures-refresh.sh <subsystem>/<case>...` to refresh selected cases after checking the pins.
No artifact may exceed 512 KiB.
A committed `definition.kore` must be a minimal backend-isolation fixture and must carry its justification in `reference.toml`.
Real-semantics definitions must never be committed here.

A consuming test must be named `reference_*` or start its body with `// reference: <command>` so the conformance census can identify its evidence source.
`scripts/conformance/subsystems.toml` defines the shared subsystem and fixture-home mapping.
Dedicated subsystem tests retain their source ownership when sharing a fixture; generic surface tests use the fixture home's default owner.
See [Testing contracts](../../../../../docs/testing.md) for placement and attribution rules.
