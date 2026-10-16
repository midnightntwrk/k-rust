# Strict heating (IMP, `imp-llvm/imp.k`)

Origin: `draft/fable51-review/conformance-host/fixtures/collatz-memory/` of the main checkout (2026-09-06, head `8be7af0`), the guarded characterization of the collatz memory growth.
At that head plain `krun` explored every successor, so a `strict` `+` with two unevaluated identifier operands doubled the pending states per expression; `strict2-16.imp` took 85 s and 2.6 GiB, and `strict2-20.imp` was killed at 8 GiB.
The fix made plain `krun` follow one successor (`--strategy any`); searches still explore both heating orders.

`gen.py two K` prints `int a, s; a = 1;` and K copies of `s = s + a;` (two unevaluated operands), and `gen.py one K` the control with `s = s + 1;` (one).
The final state binds `s` to K, so the workloads check the value.
The originals used `s = a + a;`, whose result does not depend on K; the generator keeps the two unevaluated operands and makes the result checkable.

`fixtures/` holds the original programs and `measurements.toml` verbatim.
The workloads stress the number of heating orders a strict production gives: linear under plain execution, and the states a search keeps apart or rejoins.
