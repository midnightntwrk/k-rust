# Upstream request ledgers

This directory holds the requests K-in-K2 makes of the sibling projects it builds on.
Each file is the single place where a request, its status, and any local workaround are recorded.

| File | Upstream | Status judged against |
|---|---|---|
| [`k-rust.toml`](k-rust.toml) | k-rust | `[reference_pin]`: the commit of `../inspirations/midnightntwrk/k-rust` that the workspace was last built against |
| [`krs.toml`](krs.toml) | KRS | `[reference_pin]`: the reviewed commit of `../krs` |

The format follows KRS's `draft/upstream/README.md`.
Requests that KRS already tracks against k-rust are listed under `[[krs_owned]]` by their KRS `id` and are not restated.

## Request fields

| Field | Content |
|---|---|
| `id` | Stable kebab-case identifier; never reused. |
| `title` | One-line statement of the defect or gap. |
| `kind` | `bug`, `correctness`, `missing-feature`, or another short class. |
| `status` | `open`, `partial`, `fixed`, `wontfix`, or `unknown`, judged at the reference pin. |
| `status_basis` | `test run at <commit> on <date>`, `static screen of source at <commit> on <date>`, or `carried from <source>, not requalified`. |
| `blocking` | Whether the request blocks a K-in-K2 goal. |
| `fixed_in` | The upstream commit, or `present at <pin>`; required when `status = "fixed"`. |
| `summary`, `reproducer`, `local_workaround`, `requested_action`, `sources` | As in the KRS ledger. |

`[[withdrawn]]` records requests that K-in-K2 no longer makes, with the reason.

## Moving the reference pin

k-rust is consumed as an on-disk path dependency, so moving the pin means building against the checkout's current commit.
Run `cargo test --workspace`, then re-screen every `open` and `partial` request at the new commit and update `status_basis` and `[reference_pin]`.
