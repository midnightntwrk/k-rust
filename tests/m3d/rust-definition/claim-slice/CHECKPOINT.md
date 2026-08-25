# M3D IMP claim-slice checkpoint

This isolated executable now authors the three claims frozen by
`draft/investigations/m3d-claim-surface/CONTRACT.md`:

- `branching`: one anonymous `Bool`, one RHS/`ensures` existential, two
  `orBool` branches, concrete `Id` tokens, an exact source map and both K and
  configuration frames;
- `sum-loop`: two universal `Int` binders, a `requires`, concrete `Id` tokens,
  entry-bearing maps and both frame kinds;
- `sum-spec`: the same relational state plus `circularity`.

The executable contains registration-order checks for descriptor, semantic,
Definition and emitted-K output. Once lowering reaches those layers it also
checks that all three exact labels emit as claims, all three adapt to native
`Sentence::Claim`, and none adapt to `Sentence::Rule`.

## Current result

From the KRS repository root:

```sh
CARGO_TARGET_DIR=/dev/shm/krs-claim-slice-target \
  cargo check --manifest-path tests/m3d/rust-definition/claim-slice/Cargo.toml --locked
```

passes. Collection, Semantic lowering, Definition lowering, deterministic
reordering checks and `.k` emission now all complete. Running the executable
currently stops at its first exact emission assertion because `branching`
contains:

```text
<env> #token("$n","Id") |-> 0 => #token("$n","Id") |-> V6E:Int </env>
```

The existential must render as `?N:Int`, and the anonymous occurrence is also
currently encoded as an ordinary reusable variable rather than `_B:Bool`.
The emitted claim omits its `ensures` clause and `sum-spec` omits
`[circularity]`. These are the intentional acceptance checks immediately
following the already-green exact-label checks.

## Surface deltas kept explicit

Two frozen spellings parse in the syntax-only prototype but are not yet
accepted by the real whole-configuration parser:

- qualified `k::map![...]` is rejected as an ordinary unsupported term root;
  the executable uses the otherwise-equivalent compiler-owned `map![...]`
  spelling already used by M3C;
- the constructor argument `-1` is rejected because unary-negative literals
  are absent from the current term grammar; the executable uses
  `int::sub(0, 1)` at that one site.

The semantic content remains the frozen IMP claim content. These two source
differences should be removed, rather than normalized into the contract, when
the term/state parser accepts the frozen forms.

## Follow-up gates after ordinal continuity lands

1. Run the executable through collection, Semantic IR, Definition IR, `.k`
   emission and native adaptation.
2. Inspect existential rendering: `branching` must emit `?N:Int`, not an
   ordinary variable.
3. Inspect anonymous rendering: the one `_B` occurrence must have a valid
   one-use anonymous name.
4. Assert emitted/native `ensures`, `[circularity]`, and the absence of an
   explicit all-path attribute.
5. Exercise the public native preparation/compile path and a
   Haskell-compatible K compile, then filter normalized KORE by the exact
   labels `branching`, `sum-loop`, and `sum-spec`.

The older always-red
`tests/m3d/rust-definition/surface/src/lib.rs` still has seven unlabeled
prototype claims. It should eventually gain explicit labels or be retired in
favor of focused slices; this fixture intentionally does not edit that shared
surface file.
