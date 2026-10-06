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

The K frontend results are recorded in `reference/parse/`.
By default the verifier needs no K tool and replays them;
the snapshot is keyed by the `Krs.lock` K version, the two probe digests, and the digest of the emitted `definition.k`,
so a change to what KRS emits fails closed and names `--refresh-reference`.
To re-record, put the pinned K 7.1.337 `bin` directory on `PATH` and run the verifier with `--refresh-reference`;
it rewrites the snapshot only when every check passes.
