# Unspecified equation records

Origin: `draft/open-issues-2026-10/tickets/repro/perf/unspecified-records.sh` of the main checkout (FOLLOWUPS 2.3, "Unspecified records accumulate within a bucket and are looked up linearly", from hooks-b-review-6's `wrapand{T}.k`); it did not reproduce at `934d29e7` (instructions per equation attempt flat), but took 212 s at `8d566c2d`.
`gen.py T` prints the definition: `substrString` with two recurring equations and a two-conjunct `requires`, started at `n(T)`; equation attempts grow about threefold per level of T.
The workload stresses equation attempts whose conditions are left unspecified.
