# The long-run machine's program

`program.py` writes the program the `krs/run-machine-*` workloads run, as bytes on standard output, for the machine in `krs/tests/perf/fixtures/run-machine`.
The program and its instruction set were written for this benchmark; nothing here comes from another project.

It clears 4,096 bytes of memory, then polls an I/O register that nothing writes, so it runs for any number of steps.
The bytes depend on `--clear` alone, so the workloads generate them in their prepare step and no binary is tracked.

`program.py --check-map` checks that the opcode map, which the script holds beside the decoder's equations (`cpu/src/decode.rs`), gives every byte exactly one row.
