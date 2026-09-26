"""Shared, standard-library-only support for the `tests/<gate>/` verifiers.

A verifier puts `tests/` on `sys.path` in one line and imports what it needs:

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from support import ROOT, GateError
    from support.process import run

The modules are:

- `support.process`: subprocess execution with captured output and process-group
  cleanup;
- `support.parallel`: bounded, order-preserving concurrency for independent
  commands;
- `support.hashing`: file, text, canonical-JSON, tracked-tree, and artifact
  directory digests;
- `support.pins`: ledger loading, input and output pins, and `--record`;
- `support.lock`: the `Krs.lock` toolchain and schema pins;
- `support.tools`: executable, Z3 library, K tool, rustfmt, and rust-analyzer
  discovery, plus the scratch root and checkout-specific Cargo target directory;
- `support.checkouts`: pinned external checkout verification;
- `support.kdefinition`: helpers over emitted K definitions and KORE;
- `support.semantics`: the gate flow the KWasm, KMIR, and KEVM ports share;
- `support.lsp`: the rust-analyzer probe shared by the semantics gates.

The package needs only the standard library. It must stay importable by
Python 3.10, which runs the IMP oracles inside the pinned pyk environment;
`support.pins.load_toml` (and so `support.lock` and a TOML `Ledger`) alone
needs Python 3.11 for `tomllib`.

Its unit tests run with

    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/support -t tests
"""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
"""The repository root."""


class GateError(RuntimeError):
    """A required gate step failed, or observed evidence differs from its pin."""
