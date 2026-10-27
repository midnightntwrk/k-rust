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

- K2: when refused, exactly one error, with a registered KRS code of the author kind (the registry's
  `CodeKind`; a rustc error forwarded as `krs::rust-expansion::uncoded-error` does not count), located (its
  primary range or one of its labels) inside the site the table's rule names (the entry by default), without a panic or an internal error;
  and the table's outcome: accepted with the K the table records, or refused with the code of the
  case's mistake class. The table covers every case: a new case needs its entry.
  At a position rustc parses as Rust before any KRS macro reads it (a `#[k::rule]`,
  `#[k::equation]` or `#[k::simplification]` result, a `#[k::function]` shorthand's body, a
  `#[k::constant]` value; the generator marks these slots), a construct rustc's parser refuses
  (`y @ P`) is reported by rustc whatever KRS does. There the refusal conforms with rustc's parse
  error (an uncoded rustc error) beside KRS's one error, both inside the construct, and K2 judges
  KRS's error alone. The front stops at the same parse error (`krs::expand::parse`) and leaves the
  case to the full tier. No other position has this rule (`class_matrix::invariants`);
- K1, once collected: every anchor of the case's descriptors lies inside the case's text, and no
  semantic key is found twice during lowering;
- K3, once accepted (initializers aside): each case emits the K of every case its `same_k_as`
  names, the documented equal spellings; and the accepted cases of a batch are printed together by
  `krs expand`, the printed source is collected again, and each case's own K sentences must be
  emitted again, byte for byte or after the normalization of `class_matrix/closure.rs`
  (alpha-renaming, `... </k>` for an explicit computation rest, `...` for a frame variable used
  once or `_` there, and the digest of a generated label). Each shard prints, per form, how many cases are byte-identical, equal after
  normalization, different, or refused in the printed source. `KRS_CLASS_CLOSURE=0` skips it.

The `k4` shard compares KRS's sort judges with k-rust's subsort relations of each base's emitted
definition; its disagreements are keyed `lattice/class-BASE/JUDGE~JUDGE/CLASS`, and those about
`KItem ≤ K` or a list's element are only counted.

The `k5` shard checks `class_matrix::entry_points`: one package that uses all 53 entry points of
`krs-macros`, and one mutation per entry point that breaks its header and keeps every dependent.
Each mutation must give exactly one diagnostic, an error, under `krs check --message-format json`,
and exactly one error under plain `cargo check`, whose warnings are counted and not judged: a
failed item leaves its imports unused (`unused_imports`), which no proc macro can avoid without a
second error, and which `krs check` relays away. Its entry is keyed by the mutation,
`entry/attribute/cell`.

Run one shard (`readable`, `cells`, `init`, `terms`, `import`, `k4`, `k5`), and choose the worker count yourself
when the default (from the available memory, 3 GiB per worker) does not suit:

```sh
scripts/krs-class.sh --shard cells --workers 4
```

To iterate on a few cases, run the test directly with a glob over case IDs, and write one TSV line
per case and verdict to a directory:

```sh
KRS_CLASS_FILTER='readable/result/pc/*' KRS_CLASS_OUT=/tmp/class \
  cargo test -p krs-cli --no-default-features --test class_matrix -- --ignored readable
```

## Recording the accepted K

An accepted case's K, the sentences it adds to its base after K3's normalization with the case's
tag written `TAG` (for an initializer, its `configuration`), is written by the record mode, never by
hand:

```sh
scripts/krs-class.sh --record --shard readable --shard cells --shard init --shard terms --shard import
```

It writes `k` for every accepted case that no refusal rule covers, creating its `[accept."ID"]`
entry if needed, and keeps `same_k_as`. Review the change to `expected.toml` as a diff: a changed K
is a changed emission.

## Pending entries

A case that deviates fails the suite until `pending.toml` records it, keyed by the test and the case
(`k2/readable/result/pc/None`), with the finding that owns it (`unassigned` while none does) and the
deviation exactly as the harness prints it. `KRS_CLASS_OUT` writes the entries of every unrecorded
deviation to `<shard>.pending.toml`, with `finding = "unassigned"`, for review. A pending case that
conforms, or deviates differently, also fails: remove its entry, or record the new deviation.
