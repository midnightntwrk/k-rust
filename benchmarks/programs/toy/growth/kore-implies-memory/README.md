# kore-implies output size

Origin: the `kore-implies-memory` reproducer of the 2026-10 open-issues round's performance follow-ups ("kore-implies memory"); at `934d29e7` peak RSS grew 3.2-3.9 times per doubling (11.1 GB at 20,000) because the JSON printer indented each line by its depth.
`gen.py N` prints the antecedent `c^N(z)` over `fn-recursion/fn.k`; the consequent is `X:SortT{}`, and the answer is the substitution `X = c^N(z)`, linear in N.
The workload stresses implication checking and JSON output of a term N levels deep.
