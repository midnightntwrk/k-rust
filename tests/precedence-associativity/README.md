# Precedence and associativity fixture

This isolated definition freezes the distinction between bare precedence
groups and explicit non-associativity:

- a bare precedence group emits no associativity sentence and permits
  iterated unary syntax (`!!true`);
- `non_assoc` emits K's explicit `non-assoc` sentence and rejects direct
  same-tier nesting (`true == true == true`).

Run `PYTHONDONTWRITEBYTECODE=1 python3 tests/precedence-associativity/verify.py` from the workspace
root. The verifier builds the production `krs` CLI, emits this Rust-authored
definition, compiles it with the pinned K frontend, and checks both parses.
It also parses both probes with native `krs parse`, plus `! true == false`,
whose only tree under the group priority `(Not) > (Eq)` is
`eq(not(true), false)`; the priority and associativity are declared by
production group only, so this checks that the native route resolves group
tags to the members' labels as K does.

The K frontend results form the reference snapshot `parse` (`tests/support/reference.py`),
keyed by the `Krs.lock` K version, the two probe digests, and the digest of the emitted `definition.k`.
`pins.json` `reference_sha256.parse` pins its manifest digest, and the verifier replays the per-user reference cache entry stored under it,
so with a warm cache it needs no K tool.
When the cache does not hold the entry, and under `--refresh-reference`, it runs the pinned K 7.1.337 tools live from `KRS_K_BIN` or `PATH`
and fails closed naming a missing tool; the live result must reproduce the pin and is stored only when every check passes.
A change to what KRS emits fails closed against a cached entry;
after an intended change, run the verifier with `--refresh-reference --record`, which rewrites `reference_sha256` in `pins.json`.
