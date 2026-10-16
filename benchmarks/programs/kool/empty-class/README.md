# KOOL empty class

Origin: `draft/open-issues-2026-10/tickets/repro/perf/kool-load-and-typing.sh` of the main checkout (FOLLOWUPS 2.3), which ran this program to measure loading the KOOL definition (1.03e9 instructions at `934d29e7`).
`empty.kool` is the reproducer's program: a main class with an empty constructor, so the run is almost all definition loading.
