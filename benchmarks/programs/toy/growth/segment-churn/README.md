# Stack segment churn

Origin: `draft/open-issues-2026-10/tickets/repro/perf/segment-churn.sh` of the main checkout (FOLLOWUPS 2.3, "Segment churn"); at `934d29e7` each of the M copies mapped and unmapped 30 fresh 16 MiB stack segments.
`gen.py M` prints `p(C, p(C, ... C))` with M copies of `C = c^20000(a)`, each deeper than the main stack allows for the parser's guarded recursions.
The workload stresses repeated deep recursion that crosses onto extra stack segments.
