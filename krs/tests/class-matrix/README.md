# Class-test expectations

`expected.toml` states the expected outcome of every case that `krs_test_support::class_matrix`
generates: one construct in one slot of an accepted base, for readable records and claims, `cells!`
rules, initializers, the strict-subsort axis, every term shape at the term positions of every
sentence form, and the module-import axis. `pending.toml` lists the cases known not to conform.
The schema and the rules that read both files are documented in the `class_matrix` module.

The generator's own tests check that every base expands, that every case's ranges point at its
construct, and that both files parse:

```sh
cargo test -p krs-test-support --test class_matrix
```

## The full tier: gate `krs-class`

`scripts/krs-class.sh` runs every case through Cargo, rustc, the collector, and `emit-k`'s lowering
(`krs/crates/krs-cli/tests/class_matrix.rs`). The rule-level cases of one base share batch packages,
one command constructor per case; a rustc or collector error is attributed to the case whose text
holds it, a failure no case owns is bisected, and once a batch collects, each case is lowered from
the descriptors of the base and its own. A case is judged by

- K2: when refused, exactly one error, with a registered KRS code that `[internal]` does not list,
  located inside the case's entry, without a panic or an internal error; and the table's outcome
  where the table covers the case (until the table is reviewed, an uncovered case is only counted);
- K1, once collected: every anchor of the case's descriptors lies inside the case's text, and no
  semantic key is found twice during lowering;
- K3, once accepted (initializers aside): the accepted cases of a batch are printed together by
  `krs expand`, the printed source is collected again, and each case's own K sentences must be
  emitted again, byte for byte or after the normalization of `class_matrix/closure.rs`
  (alpha-renaming, `... </k>` for an explicit computation rest, `...` for a frame variable used
  once). Each shard prints, per form, how many cases are byte-identical, equal after
  normalization, different, or refused in the printed source. `KRS_CLASS_CLOSURE=0` skips it.

The `k4` shard compares KRS's sort judges with k-rust's subsort relations of each base's emitted
definition; its disagreements are keyed `lattice/class-BASE/JUDGE~JUDGE/CLASS`, and those about
`KItem ≤ K` or a list's element are only counted.

Run one shard (`readable`, `cells`, `init`, `terms`, `import`, `k4`), and choose the worker count yourself
when the default (from the load and the available memory) does not suit:

```sh
scripts/krs-class.sh --shard cells --workers 4
```

To iterate on a few cases, run the test directly with a glob over case IDs, and write one TSV line
per case and verdict to a directory:

```sh
KRS_CLASS_FILTER='readable/result/pc/*' KRS_CLASS_OUT=/tmp/class \
  cargo test -p krs-cli --no-default-features --test class_matrix -- --ignored readable
```

## Pending entries

A case that deviates fails the suite until `pending.toml` records it, keyed by the test and the case
(`k2/readable/result/pc/None`), with the finding that owns it (`unassigned` while none does) and the
deviation exactly as the harness prints it. `KRS_CLASS_OUT` writes the entries of every unrecorded
deviation to `<shard>.pending.toml`, with `finding = "unassigned"`, for review. A pending case that
conforms, or deviates differently, also fails: remove its entry, or record the new deviation.
