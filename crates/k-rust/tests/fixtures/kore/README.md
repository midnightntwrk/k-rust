# KORE parser fixtures

These fixtures come from `runtimeverification/k` at commit
`4a46d1231473b599c699160132fd6e76a5c46406` (`v7.1.337`):

`pyk/src/tests/unit/kore/test-data`

- `definitions/pass`: definitions accepted by the reference parser.
- `definitions/fail`: malformed definitions rejected by both `pyk` and `k-rust`.
- `patterns`: standalone pattern fixtures accepted by the reference parser.
- `json`: 41 KORE JSON v1 files containing 68 reference terms.

The fixtures are redistributed under the BSD 3-Clause license in `LICENSE.md`.

JSON is treated as a lossless wire format. `And`, `Or`, `LeftAssoc`, and `RightAssoc`
remain distinct syntax nodes; Scala-style collapsing and expansion is available only
through the explicit KAST-boundary normalization API.
