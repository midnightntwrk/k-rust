# Ambiguous operator chain

Origin: `draft/open-issues-2026-10/tickets/repro/perf/ambiguous-chain.sh` of the main checkout (FOLLOWUPS 2.3, "A genuinely ambiguous chain"); at `934d29e7` it grew 8.3-8.8 times per doubling, 5.4 GB at 200 operands.
`amb.k` declares `+` and `-` both `[left]` with no relation between them.
`gen.py amb N` prints `0 + 1 + ... + (N-4) + 1 - 2 - 3`, which is ambiguous and refused; `gen.py ctl N` prints the unambiguous all-`+` chain of N operands.
The workload stresses the packed forest of every bracketing between the two operators, which is built and typed before the ambiguity is reported (cubic, a documented cost in `docs/backend-port.md`, "Known compile costs").
