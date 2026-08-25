# M3 native `domains.md` capability probe

This probe preserves the M3A source fixture and the pinned `k-rust` builtin
closure. It exists to distinguish the portable sort-inference boundary from a
source, loader, or builtin incompatibility.

Portable reproduction:

```console
cargo run --locked --manifest-path spikes/m3-native-domains/Cargo.toml -- \
  load tests/m3a/fixtures/expr.k KRS-M3A-EXPR
```

At pinned `k-rust` commit `58f33885b736148dae189623d1aac989ce9be475`,
this reaches `krust-builtin://domains.md:170:3-170:103` in module
`ARRAY-IN-K` and returns `Z3InferenceRequired { ambiguity: true,
parametric_sorts: false }` while resolving that rule bubble.

Native reproduction on this Ubuntu 22.04 host:

```console
CARGO_INCREMENTAL=0 Z3_SYS_Z3_VERSION=4.13.3 \
  cargo run --locked --manifest-path spikes/m3-native-domains/Cargo.toml \
  --features native-z3 -- \
  load tests/m3a/fixtures/expr.k KRS-M3A-EXPR
```

This loads 78 modules and 719 local sentences. The same build accepts all nine
M3A accepted programs plus the two dynamically ill-sorted programs, and it
rejects both syntax-negative programs.

The explicit Z3 version is a packaging qualification, not a semantic bypass.
The pinned `z3-sys` 0.11.0 `gh-release` feature otherwise downloads Z3 4.16.0,
whose Linux archive fails to link on this host because it requires newer
glibc/libstdc++ symbols. The official Z3 4.13.3 archive links statically and
executes the required inference successfully. KRS should pin and qualify the
solver artifact instead of relying on the binding's default download version.

`compile` intentionally probes farther than the reported loader failure. It
currently reaches a separate `k-rust` limitation at the `add implicit
computation cell` stage (`No main cell found`) because the expression rules
live in a module below the module which declares the configuration. This is
unrelated to both Z3 inference and KRS structured-definition preparation.

Finally, `k_rust::kast::printer::Printer` prints canonical textual KAST, not
concrete object-language syntax. It therefore cannot honestly serve as the
M3A concrete unparse oracle.
