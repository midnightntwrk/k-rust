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
