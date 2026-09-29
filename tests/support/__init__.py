"""Shared, standard-library-only support for the `tests/<gate>/` verifiers.

A verifier puts `tests/` on `sys.path` in one line and imports what it needs:

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from support import ROOT, GateError
    from support.process import run

The modules are:

- `support.krs_gate`: compile, definition.load, configure, execute, kore.read,
  observe, expect, and prove through the native gate protocol;
- `support.behavior`: shared native and Java case expectations and outcomes;
- `support.process`: subprocess execution with captured output and process-group
  cleanup;
- `support.parallel`: bounded, order-preserving concurrency for independent
  commands;
- `support.hashing`: file, text, canonical-JSON, and artifact directory
  digests;
- `support.pins`: ledger loading, input and output pins, and `--record`;
- `support.lock`: the `Krs.lock` toolchain and schema pins;
- `support.packages`: standalone Rust package ownership and gate checks;
- `support.tools`: executable, Z3 library, K tool, rustfmt, and rust-analyzer
  discovery, plus the scratch root and checkout-specific Cargo target directory;
- `support.krs`: the CLI build and invocation policy;
- `support.report`: gate result lines and failure accounting;
- `support.diagnostics`: JSON diagnostic envelope extraction;
- `support.checkouts`: pinned external checkout verification;
- `support.kdefinition`: helpers over emitted K definitions and KORE;
- `support.semantics`: the gate flow the KWasm, KMIR, and KEVM ports share;
- `support.imp_oracle`: orchestration for the two strict IMP reference oracles;
- `support.lsp`: the rust-analyzer probe shared by the semantics gates.

The package needs only the standard library. It must stay importable by
Python 3.10, which runs the IMP oracles inside the pinned pyk environment;
`support.pins.load_toml` (and so `support.lock` and a TOML `Ledger`) alone
needs Python 3.11 for `tomllib`.

Its unit tests run with

    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/support -t tests
"""

from __future__ import annotations

from collections.abc import Callable
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
"""The repository root."""


class GateError(RuntimeError):
    """A required gate step failed, or observed evidence differs from its pin."""


def entry(
    label: str,
    main: Callable[[], int | None],
    *,
    errors: tuple[type[Exception], ...] = (),
) -> None:
    """Run a gate entry point and report expected failures consistently.

    `GateError` is always an expected failure; a gate names any other exception
    type it reports without a traceback in `errors`.
    """
    try:
        result = main()
    except (GateError, *errors) as error:
        print(f"FAIL {label}: {error}", file=sys.stderr)
        raise SystemExit(1) from error
    if result is None:
        print(f"PASS {label}")
        raise SystemExit(0)
    raise SystemExit(result)
