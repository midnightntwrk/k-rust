# Reference-derived fixtures

Each subsystem directory contains small artifacts produced by the K v7.1.337 reference toolchain at revision `4a46d1231473b599c699160132fd6e76a5c46406` and the Haskell backend `0.1.155` (`38afc81`).
Every case has a `reference.toml` that records each generated artifact's command, tool, exit code, and SHA-256 digest.
Hand-written inputs use `[[input]]`; an adjudicated specification answer that intentionally differs from the toolchain uses `[[expectation]]` and names its source.
Tests consume the committed artifacts and therefore must not require the reference toolchain.

Run `K_REFERENCE_REFRESH=1 scripts/reference-fixtures-refresh.sh <subsystem>/<case>...` to refresh selected cases after checking the pins.
No artifact may exceed 512 KiB.
A committed `definition.kore` must be a minimal backend-isolation fixture and must carry its justification in `reference.toml`.
Real-semantics definitions must never be committed here.

A consuming test must be named `reference_*` or start its body with `// reference: <command>` so the conformance census can identify it exactly and attribute a named fixture home to its owning subsystem.
