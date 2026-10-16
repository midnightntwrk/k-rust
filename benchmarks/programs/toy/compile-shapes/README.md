# Compile and parser shapes

Generators and definitions for the compile-scaling and parser-stress workloads of `registry/grammar.toml` and `registry/growth.toml`.

- `gen3.py` is copied verbatim from `draft/open-issues-2026-10/units/stack-cases-probes/gen3.py` of the main checkout (a superset of `deep-inputs-first-principles/probes/gen3.py`).
  `gen3.py SHAPE N` prints a definition with N modules in an import chain (`modchain`), N sorts in a subsort chain (`subsorts`), N flat cells (`cells`), or N `f(i) => i` rules beside one `[owise]` rule (`owise`), among other shapes.
  Used by the fu-compile-scaling unit (`units/fu-compile-scaling.md`, fixes `d21ab66f`, `7ea4872a`) and by `tickets/repro/perf/owise-competitors.sh`.
- `gen4.py` is a reconstruction: the fu-compile-scaling unit's scratch `cs/gen4.py` was never committed.
  Its shapes follow the unit's descriptions and the shapes of the tests that pin the fixes (`inner::rules::tests::a_sequence_against_a_rewrite_decides_each_group_of_callers_once`, `kompile_depth::a_nesting_injected_at_every_level_compiles_in_memory_linear_in_its_depth`): a flat `~>` sequence written against a rewrite (`kseqrule`, P5, fix `1c78e912`), a `+Int` chain beside a second `~>` (`pluskseq`, refused after parsing), a `List{Int, ","}` literal in a rule (`listlit`, fix `ed339867`), and a nesting with a subsort injection at every level (`inj`, fix `6705e983`).
- `null1.k` is `draft/perf-wave-3/repro/null1.k.slow` copied verbatim: `Exp ::= Opt Exp Opt` with a nullable `Opt` derives `Exp` from itself without consuming input.
  Before `51b179ea` its rule parse never terminated; it is now refused as a cyclic derivation.
- `dn.k` is the reachable part of the grammar that drove the parser property test past 40 GB (`draft/open-issues-2026-10/units/w8-oom.md`, culprit case at `c4c420ef`): `S ::= S S | "c" "a" "c" "a" | "d" | S "d"`, with nothing ordering `S S` against `S "d"`.
  The input `d d ... d` (n tokens) is genuinely ambiguous; the original measured the parser in isolation (`units/w8-forest.md`), this one parses it as a program with `kast`.
