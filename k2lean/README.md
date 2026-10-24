# k2lean

k2lean generates a Lean 4 library from a K definition compiled by krust: one Lean type per sort, the definition's functions as Lean definitions, its rewrite rules as an inductive `Step` relation with an executable `step`, its K equations as proved theorems, and proofs that tie them together.
On top of a generated library it proves preserved invariants (a property kept by every rule, for every program), written either as a K function or as a Lean predicate.
It is part of k-rust's repository: the generator is a member of k-rust's workspace and reads KORE through `k-rust-kore`, at whatever commit the checkout is.

## Layout

| path | content |
|---|---|
| `crates/k2lean` | the generator (`k2lean gen`, and the commands of `docs/design.md`, §4), with its unit and snapshot tests |
| `lean/prelude` | `KPrelude`: the hooks, matching combinators and tactics every generated library uses, and the invariant core (`Preserved`, `k2l_preserve`) |
| `lean/claims` | `KClaims`: K reachability claims over a transition relation, and the claim tactic |
| `demos` | K inputs, hand-written Lean projects over generated libraries, and `regen.sh`, which regenerates and builds them |
| `generated` | where the libraries are generated; git tracks only each library's open lists and hand-written invariant module |
| `tests` | the gate (`gate.sh`, `gate-check.py`, `libs.sh`), its baseline and recorded outputs, kimp's golden cases, and the generator's fixtures |
| `pipelines` | human-run scripts that generate and build KEVM (`kevm.sh`, with KEVM's termination file) and KMIR (`kmir.sh`) in the arity-indexed term universe; not gate tiers |
| `docs` | `design.md` (what is generated and why it is sound, the encodings, measured costs, and what is open) and `invariants.md` (the user guide to preserved invariants) |

## Quick start

From the root of a k-rust checkout with the reference checkouts of `README.md`, "Compatibility evidence" (`k`, `imp-semantics`), krust built (`cargo build --release -p k-rust --bin krust`) and Lean's `elan` on `PATH`:

```sh
cargo build --release --locked -p k2lean      # target/release/k2lean
k2lean/demos/regen.sh                         # generate kimp, KRS IMP and two more, build the four IMP demos
k2lean/tests/gate.sh light                    # the regression gate's light tier
```

Each generated project pins Lean v4.34.0, which elan installs on first use.
A clean light gate builds several Lean libraries: about 1,000 s of CPU and 4 GB of peak memory (640 s wall on a shared 32-CPU host, 2026-10-24); a rerun builds only what changed.
To generate a library of your own definition:

```sh
target/release/krust kcompile my.k --main-module MY --syntax-module MY-SYNTAX --output-directory out/my
mkdir -p out/lean && cp -a k2lean/lean/prelude out/lean/
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json \
  --out out/generated/my --name My --prelude ../../lean/prelude
(cd out/generated/my && lake build My.Equations > build.log 2>&1)
```

An equation whose generated proof fails (here, a `Set` equation of `domains.md`) is turned into a named open obligation, and the library is generated again:

```sh
touch out/generated/my/open-obligations.txt
target/release/k2lean open-from-log out/generated/my/My/Equations.lean out/generated/my/build.log \
  out/generated/my/open-obligations.txt
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json \
  --out out/generated/my --name My --prelude ../../lean/prelude \
  --open-obligations out/generated/my/open-obligations.txt
(cd out/generated/my && lake build My My.Equations MyTest.Axioms)
```

`docs/invariants.md`, §2, explains the flags and the work-tree layout.

## Demos

| demo | shows |
|---|---|
| `demos/ImpRel` | the KRS IMP port (`demos/k/krs-imp`) and kimp are bisimilar: `k2lean relate` pairs their rules and generates the proof |
| `demos/ImpTypes` | kimp is type-sound for a K type checker (`demos/k/imp-typing.k`): preservation as a kind 2 invariant, and progress |
| `demos/ImpMut` | a mutant of kimp (`demos/k/kimp-mutant`) diverges from kimp, proved on a concrete configuration |
| `demos/KrsImpTyping` | every KRS IMP rule preserves the declared cell type `env: Map<Id, Value>`, from the KRS sidecar |
| `demos/SimpleEnv` | a kind 2 invariant of SIMPLE, strengthened to be inductive |
| `demos/k/kimp-inv`, `demos/k/simple-inv` | kind 1 invariants written as K functions |
| `demos/claims` | K claims of kimp proved in Lean, generically or by hand |

## Large definitions

The default term universe is one Lean type per sort, in one `mutual` block.
For definitions of KEVM's size, `gen --arity-terms` writes one inductive family indexed by the sorts instead, and `gen --det2` proves determinism along the rule index rather than over all pairs of rules (`--arity-terms` implies it); `docs/design.md`, §2.1 and §3.1, describes both and what they cost.
`pipelines/kevm.sh` and `pipelines/kmir.sh` run KEVM and KMIR through the generator and Lean, step by step; `docs/design.md`, §9, lists what is open.

## Testing

`cargo test -p k2lean` runs the generator's tests, which the workspace suite includes.
`tests/gate.sh light|heavy|arity` is the regression gate; `docs/testing.md` of the repository describes the tiers and when they are owed (`k2lean-light`, `k2lean-heavy`, `k2lean-arity` in `scripts/gates.toml`).

## Third-party material

Some test data and demo inputs derive from K's sources and from kimp (runtimeverification/imp-semantics):

- `demos/k/kimp-mutant` is kimp's `imp.k`, `calc.k` and `expr.k` at the pin of `scripts/reference-differential.toml`, with one rule changed;
- `demos/claims/specs/imp-ifs-uint64-spec.k` is kimp's `examples/specs/imp-ifs-spec.k` with one predicate written out;
- `tests/goldens` records krust and K results on kimp's example programs and on ports of programs of K's tutorial tests, whose texts the cases carry;
- the compiled fixtures and `demos/k/krs-imp/*.kore` contain the K builtin modules that krust compiles into every definition.

This material, from K and from kimp alike, keeps the K Framework's BSD 3-Clause license (`licenses/K-FRAMEWORK-BSD-3-Clause.txt`), and [NOTICE](../NOTICE) lists it; the rest of k2lean is licensed as k-rust is.
