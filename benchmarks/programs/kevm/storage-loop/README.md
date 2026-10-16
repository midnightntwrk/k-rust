# KEVM storage loop (VMTests)

Origin: the storage-loop measurements of the open-issues 2026-10 round in the main checkout: `draft/open-issues-2026-10/units/w2-collections.md` ("KEVM storage loop", `measure.md` item K22), generator `units/w4-k22m-tools/gen.py`, run scripts `units/w8-tree-*/sl.sh`.
`gen.py` is copied verbatim.

`python3 gen.py N` prints a VMTests JSON test whose code runs `SSTORE(i, i + 1)` for `i < N` (`PUSH2 N; PUSH1 0; JUMPDEST; DUP1; PUSH1 1; ADD; DUP2; SSTORE; PUSH1 1; ADD; DUP2; DUP2; LT; PUSH1 5; JUMPI; STOP`) and whose `post` state lists the N expected slots.
`python3 gen.py N control` replaces the key `DUP2` by `PUSH1 0`, so one slot is rewritten N times and the `post` state is `{0x00: N}`.
The driver checks the `post` state: every run that matches ends in `<mode> SUCCESS` with exit 0, and a wrong `post` value ends with exit 1.

The distinct-slot program grows the account's storage `Map` and the `<accessedStorage>` `Set` by one entry per iteration, so it stresses the cost of persistent collection updates and of matching against a large map; the control has the same steps on a one-entry map.
At 16,384 slots the distinct program took about 215 s and 1.5 GB at the w8-tree-5a heads (3.56 GB at the earlier w2 heads), against 183 s and 250 MB for the control.
