# k-rust-fuzz

`k-rust-fuzz` crafts concrete input values for a given program under a given K specification, so that an execution of that program reaches a stated target: a named rule, a pattern, or a difference between a baseline and a mutant definition.
It does not generate programs: random or grammar-driven program generation produces nothing a human would write, and the author (a person or an LLM) already writes the program.
The author marks the program's input holes beside the unmodified program (typed spans of data, such as an `Int` literal), names the target, and the crate chooses hole values, runs the program with k-rust, and reports.
The report holds either a witness that a concrete re-run confirmed (the hole values, the initial and final configurations, the outcome), or a bounded "no witness found" with the budget, the cases run, the coverage reached and the outcome counts, which is never a proof that no witness exists.

The library builds without k-rust's `cli` and Z3 features; the `z3` feature enables the solver-backed proposer.
The design is in the fz26 programme's `ARCHITECTURE.md`; the rustdoc of each item cites its section.
