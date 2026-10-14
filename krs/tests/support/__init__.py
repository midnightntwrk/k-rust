"""Shared, standard-library-only support for the `tests/<gate>/` verifiers.

A verifier puts `tests/` on `sys.path` in one line and imports what it needs:

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from support import ROOT, GateError
    from support.process import run

Python orchestrates; K, KORE, KAST, and IR data are read through krs-gate.

The modules are:

- `support.krs_gate`: compile, definition.load, configure, execute, search,
  kore.read, kore.digest, observe, expect, and prove through the native gate protocol;
- `support.behavior`: corpus-declared expectations, shared native and Java
  structural checks, and reported outcomes;
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
- `support.kdefinition`: emitted K definition checks;
- `support.semantics`: the gate flow the KWasm, KMIR, and KEVM ports share;
- `support.imp_oracle`: orchestration for the two strict IMP reference oracles;
- `support.reference`: reference-K (Java K) snapshots in a per-user cache,
  pinned by manifest digest, replayed by default and run live on a miss or
  under `--refresh-reference`;
- `support.lsp`: the rust-analyzer probe shared by the semantics gates.

The package needs only the standard library.

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
