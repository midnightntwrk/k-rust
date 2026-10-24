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
