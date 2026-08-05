# KORE parser fixtures

These fixtures come from `runtimeverification/k` at commit
`4a46d1231473b599c699160132fd6e76a5c46406` (`v7.1.337`):

`pyk/src/tests/unit/kore/test-data`

- `definitions/pass`: definitions accepted by the reference parser.
- `definitions/fail`: malformed definitions rejected by both `pyk` and `k-rust`.
- `definitions/scala-compat`: inputs where the Scala K frontend and `pyk` intentionally differ.
- `patterns`: standalone pattern fixtures accepted by the reference parser.

The fixtures are redistributed under the BSD 3-Clause license in `LICENSE.md`.

`test-string-4.kore` is separated from the failure corpus because `pyk` rejects its unknown
`\0` escape, while the Scala frontend's `StringUtil` drops the backslash and accepts the input.
`k-rust` follows the Scala frontend for bug compatibility.
