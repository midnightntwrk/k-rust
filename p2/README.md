# P2 parser-architecture probe

P2 tests a replaceable official-K parsed-KAST adapter against isolated inner
parser features. It intentionally does not claim that delegating parsing to K
is an independent K-in-K parser.

```sh
bun run p2
```

The runner compiles five definitions and asserts exact canonical KAST for
priority, associativity, `prefer`, `avoid`, overload selection, user-list
completion, and a rule parsed with `--type-inference-mode checked` (SimpleSub
and Z3 must agree). Evidence is written to `p2/build/probe-result.json`.

See `draft/k-in-k-probe-p2.md` for the architecture decision and limitations.
