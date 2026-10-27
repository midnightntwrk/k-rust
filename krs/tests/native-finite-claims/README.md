# Checked finite-case guidance

This package keeps its semantic equations literal-only: `BitValue(true) = 1` and `BitValue(false) = 0`.
Arithmetic operations first appear in the claims, so compiling this proof also checks that standard builtin dependencies enter the proof's definition context.
Authored specification rules remain forbidden.

From the repository root, with `krs` built by `cargo build -p krs-cli`:

```console
target/debug/krs prove --manifest-path krs/tests/native-finite-claims/Cargo.toml \
  --package krs-native-finite-claims --definition main \
  --spec-module NATIVE-FINITE-SPEC --depth 3 --output json \
  --claim extracted-cases --claim inlined-cases --claim helper-composition
```

Every selected claim must be `proven`.
The `true | false` patterns offer every value of the standard `Bool` domain, and the tool proves every alternative before declaring the authored claim proven.
The two-command composition has four alternatives.
Dropping an alternative narrows the statement; this syntax does not establish coverage for an arbitrary user-chosen list of cases.

`unselected-inline` proves by semantic branching, while `unselected-helper` remains unresolved: the engine does not automatically derive a finite summary of the helper.
For this supported workflow, expose the finite cases in the claim as `extracted-cases` does.
The helper and inline forms then prove the same range property over the entire Boolean input domain, with no added lemma.

`invalid-cases` must be `disproved`.
`partly-false-cases` must also be `disproved`, even though one alternative proves; success on one case does not prove the original claim.
These results concern weak partial correctness; they do not establish termination of arbitrary programs.
