# Tour proof and outcome evidence

This gate keeps the tour's proof-capability matrix and outcome examples attached to checked evidence.
It checks:

- `verify_undefined_partial` checks the authored IMP partial declaration and sole guarded equation in semantics source, the proved positive claim through an IMP `Ledger` pin, and the negative application's docs-site page fragments.
- `verify_stuck_state` checks the IMP state corpus program text, the stuck-state aggregate through an IMP state `Ledger` pin, and the docs-site page fragments.
- `verify_authored_trap` checks KWasm's authored trap semantics source, the division-by-zero corpus cases, the native behavior digest through a KWasm `Ledger` pin, and the docs-site page fragments.
- `verify_llvm_claim_omission` checks the `Krs.lock` policy, claim-free LLVM artifacts through IMP `Ledger` pins, two named Rust tests via `cargo test --list`, and the docs-site page fragment.
- `verify_capability_matrix` checks authored IMP and KWasm claim counts in semantics source, proof outcomes through IMP `Ledger` pins, the reference KORE digest through a KWasm `Ledger` pin, two named Rust integration tests via `cargo test --list`, the KWasm gate's `--java-reference` option via `--help`, and the docs-site page fragments.

The IMP state, KWasm, and IMP gates assert their dynamic observations.
This gate reads their pins, never their code.
The undefined partial example is a checked consequence of the declaration and its complete equation set, not a captured `krun` trace.
The named-test checks build the listed Rust test binaries and require the Z3 library, which `tests/support` locates as it does for the other tour gates.

Run it from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/tour-proof-evidence/verify.py
```
