# Predicate chains

Origin: `draft/open-issues-2026-10/tickets/repro/perf/predicate-chains.sh` of the main checkout (FOLLOWUPS 2.3, "Quadratic predicate shapes", backend-perf-review-1 F1-F3); at `934d29e7` the `\exists`, `\forall`, `\implies` and `\or`/`\not` chains grew about 4 times per doubling, the `\not` chain 1.7.
`gen.py` is `draft/open-issues-2026-10/tickets/repro/perf/predicate-chains.py` copied verbatim: `gen.py SHAPE D` prints `X /\ \floor(f(X)) /\ CHAIN`, CHAIN being D levels of one connective over `\ceil(f(X))`, with `f` and `g` partial functions of `pred.k`.
The workloads stress simplification of deep predicates under binders and connectives.
