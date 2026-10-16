# Map built by N updates

Origin: `draft/open-issues-2026-10/tickets/repro/perf/map-update.sh` of the main checkout (FOLLOWUPS 2.3, "Building an N-entry map by N `MAP.update`s is Θ(N²)"); at `934d29e7` the cost grew 3.3-3.9 times per doubling of N, against 1.8 for the control.
`map-build.k` inserts one key per step (`M[N <- N]`); `control.k` does the same steps on an `Int` cell.
Both gained one rule that, at 0, moves the size of the map (the counter) into `<k>` as `-N` and empties the cell, so the result checks N without printing the whole map.
The workloads stress the cost of one update on a large `Map`.
