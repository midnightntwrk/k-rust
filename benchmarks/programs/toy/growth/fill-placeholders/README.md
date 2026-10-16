# SMT template filling

Origin: `draft/open-issues-2026-10/tickets/repro/perf/fill-placeholders.sh` of the main checkout (FOLLOWUPS 2.3, "fill_placeholders deep-copies each argument at every level"); at `934d29e7` the S-expression copies grew 4.1-4.5 times per doubling.
`gen.py abs N` prints `X /\ absInt^N(X) >=Int 0`; the `smt-hook` of `absInt` is a list template, so every level is filled into it.
`gen.py plus N` nests `_+Int_`, whose `smt-hook` is an atom: the control.
The workloads stress translating a deep term to SMT; Z3 itself dominates the run.
