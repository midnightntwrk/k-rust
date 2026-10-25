| case | mode | Lean = krust | Lean output = .out | krust output = .out | detail |
|---|---|---|---|---|---|
| collatz | run | pass | pass | pass | 1461 steps, stuck, equal to krust: true, 0 ms |
| div-nondet | search | pass | pass | via lean (equal configurations) | 126 states, 3 final, krust 3, krust's among ours: true, same set: true, complete: true, 11 ms |
| factorial | run | pass | pass | pass | 313 steps, stuck, equal to krust: true, 0 ms |
| higher-order | run | pass | pass | pass | 3873 steps, stuck, equal to krust: true, 0 ms |
| matrix | run | pass | fail | krust: error: captured output requires exactly one execution leaf, unconstrained and with exactly one stdout stream buffer; fou | 49 steps, undefined step (rule STDIN-STREAM.stdinParseInt), equal to krust: false, 0 ms |
| sortings | run | pass | pass | pass | 9072 steps, stuck, equal to krust: true, 0 ms |
| exceptions_01 | run | pass | pass | pass | 96 steps, stuck, equal to krust: true, 0 ms |
| exceptions_02 | run | pass | pass | pass | 76 steps, stuck, equal to krust: true, 0 ms |
| exceptions_03 | run | pass | pass | pass | 85 steps, stuck, equal to krust: true, 0 ms |
| exceptions_04 | run | pass | pass | pass | 93 steps, stuck, equal to krust: true, 0 ms |
| exceptions_05 | run | pass | pass | pass | 344 steps, stuck, equal to krust: true, 0 ms |
| exceptions_06 | run | pass | pass | pass | 323 steps, stuck, equal to krust: true, 0 ms |
| exceptions_07 | search | pass | pass | via lean (equal configurations) | 121 states, 2 final, krust 2, krust's among ours: true, same set: true, complete: true, 14 ms |
| exceptions_08 | run | pass | pass | pass | 168 steps, stuck, equal to krust: true, 0 ms |
| exceptions_09 | run | pass | pass | pass | 110 steps, stuck, equal to krust: true, 0 ms |
| exceptions_10 | run | pass | pass | pass | 53 steps, stuck, equal to krust: true, 0 ms |
| exceptions_11 | run | pass | pass | pass | 180 steps, stuck, equal to krust: true, 0 ms |
| exceptions_12 | run | pass | pass | pass | 161 steps, stuck, equal to krust: true, 0 ms |
| exceptions_13 | run | pass | pass | pass | 48 steps, stuck, equal to krust: true, 0 ms |
| exceptions_14 | run | pass | pass | pass | 27 steps, stuck, equal to krust: true, 0 ms |
| exceptions_15 | run | pass | pass | pass | 45 steps, stuck, equal to krust: true, 0 ms |
| threads_01 | search | pass | pass | via lean (equal configurations) | 288 states, 2 final, krust 2, krust's among ours: true, same set: true, complete: true, 45 ms |
| threads_02 | search | pass | pass | via lean (equal configurations) | 457 states, 3 final, krust 3, krust's among ours: true, same set: true, complete: true, 87 ms |
| threads_04 | search | pass | pass | via lean (equal configurations) | 9546 states, 8 final, krust 8, krust's among ours: true, same set: true, complete: true, 4199 ms |
| threads_05 | search | pass | pass | via lean (equal configurations) | 2568 states, 5 final, krust 5, krust's among ours: true, same set: true, complete: false, 1153 ms |
| threads_06 | search | pass | pass | via lean (equal configurations) | 11237 states, 4 final, krust 4, krust's among ours: true, same set: true, complete: true, 8211 ms |
| threads_07 | run | pass | pass | pass | 115 steps, stuck, equal to krust: true, 0 ms |
| threads_09 | search | pass | pass | via lean (equal configurations) | 837 states, 2 final, krust 2, krust's among ours: true, same set: true, complete: true, 220 ms |
| threads_10 | run | pass | pass | pass | 83 steps, stuck, equal to krust: true, 0 ms |
| threads_11 | run | pass | pass | pass | 113 steps, stuck, equal to krust: true, 0 ms |
| threads_12 | run | pass | pass | pass | 731 steps, stuck, equal to krust: true, 0 ms |
