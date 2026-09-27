# Tour proof and outcome evidence

This focused gate keeps the documentation's proof-capability matrix and three
outcome examples attached to existing executable authorities.
It checks:

- IMP's partial declaration, sole guarded equation, and pinned proved positive
  claim before documenting the negative application as bottom;
- IMP state's hash-pinned two-step unresolved-variable stuck case;
- KWasm's authored trap constructor, division-by-zero corpus cases, and native
  result check;
- the LLVM claim-omission policy and IMP's pinned claim-free LLVM artifacts;
  and
- the exact IMP/KWasm/one-path evidence used to qualify each matrix cell.

The gate does not pretend to replace the owning native suites.
In particular, the undefined partial example is a checked consequence of the
declaration and its complete equation set, not a captured `krun` trace, while
the IMP state, KWasm, and IMP proof suites own their dynamic observations.

Run it from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/tour-proof-evidence/verify.py
```
