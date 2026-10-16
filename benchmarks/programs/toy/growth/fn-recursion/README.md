# Deep non-tail recursion

Origin: `draft/open-issues-2026-10/tickets/repro/perf/fn-recursion.sh` of the main checkout (FOLLOWUPS 2.3, "Deep non-tail recursion (fn.k) is super-linear in depth"); at `934d29e7` it grew 3.0-3.6 times per doubling, the control 1.9.
`fn.k` is copied verbatim from `draft/open-issues-2026-10/units/stack-cases-probes/fn.k`: `go(N)` builds `c^N(z)` in N steps, then evaluates `size(c^N(z)) = N` by non-tail recursion.
`fn-control.k` is the same with `run(0, _T) => 0`, the reproducer's `sed` edit: it builds the term and drops it.
The workloads stress function evaluation N levels deep. `fn.k` is also the definition of `kore-implies-memory`.
