#!/usr/bin/env python3
"""The four ports' emission, checked against the heavy gates' own pins.

For IMP, KEVM, KMIR, and KWasm this runs the steps of the port's heavy gate
that read only the port's packages and the KRS tools (`support.semantics`
`emission`, `imp/verify.py` `emission`), against that gate's ledger: rustfmt
and `krs fmt --check`, the `krs check` descriptor count and warnings, the
`krs expand` digest and its independent compile, two fresh emissions and a
cached replay, and the digest of every emitted artifact. A difference fails
here exactly as it would fail the heavy gate. The heavy pins are never
recorded here; an intended change to an artifact is recorded by the port's
own gate.

It also pins what the macros hand rustc in each package the heavy gate
compiles: the whole-file expansion of every source file under its `src/`, as
the digest of the generated text and of its source map, or of the diagnostics
with which the expander refuses the file (`krs-gate`'s `expansion.digest`).
These are the only pins this gate owns (`pins.toml` beside this file), and
`--record` rewrites them after every port passed.

What it does not run, and why that is sound while it passes: the Rust checks
(Clippy, tests, the MSRV check, rust-analyzer) see the macro output pinned
here, the facade crate, and the toolchain; the native compile, the behavior
corpus, and the Java reference read the emitted artifacts, whose bytes are
pinned, through the native code that `scripts/gates.toml` routes to the heavy
gates. The external checkouts are inputs of those layers only.

    python3 tests/ports-emit/verify.py [--record] [PORT...]
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys
import tempfile
import time
import tomllib
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate, semantics  # noqa: E402
from support.krs import build  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.tools import scratch_root  # noqa: E402
from imp import verify as imp  # noqa: E402
from kevm import verify as kevm  # noqa: E402
from kmir import verify as kmir  # noqa: E402
from kwasm import verify as kwasm  # noqa: E402


HERE = Path(__file__).resolve().parent
PINS_PATH = HERE / "pins.toml"


@dataclass(frozen=True)
class PortEmission:
    """One port: the packages whose macro output its heavy gate compiles, and its emission steps."""

    key: str
    label: str
    packages: tuple[str, ...]
    """Package directories relative to the KRS root."""
    emission: Callable[[Path, Path, Path], None]
    """Run the heavy gate's emission steps in a workspace, given `krs` and `krs-gate`."""


def semantics_port(module: object) -> PortEmission:
    port: semantics.Port = getattr(module, "PORT")
    hooks: semantics.Hooks = getattr(module, "HOOKS")

    def emission(workspace: Path, krs: Path, gate: Path) -> None:
        pins = Ledger(port.pins_path, emit_only=True)
        semantics.emission(port, hooks, workspace, krs, pins, gate, semantics.build_environment())

    return PortEmission(port.key, port.label, (f"semantics/{port.key}",), emission)


PORTS = (
    PortEmission(
        "imp", "IMP", ("tests/imp/rust-definition", "tests/imp/expanded-definition"),
        lambda workspace, krs, gate: imp.emission(Ledger(imp.PINS_PATH, emit_only=True), workspace, krs, gate),
    ),
    semantics_port(kevm),
    semantics_port(kmir),
    semantics_port(kwasm),
)


def crate_identity(package: Path) -> tuple[str, str]:
    """The library crate name and the dependency name through which the package names the facade."""

    with (package / "Cargo.toml").open("rb") as stream:
        manifest = tomllib.load(stream)
    crate = manifest.get("lib", {}).get("name") or manifest["package"]["name"].replace("-", "_")
    aliases = [
        name for name, dependency in manifest.get("dependencies", {}).items()
        if (dependency.get("package", name) if isinstance(dependency, dict) else name) == "krs"
    ]
    if len(aliases) != 1:
        raise GateError(f"{package / 'Cargo.toml'} must name the krs facade exactly once: {aliases}")
    return crate, aliases[0]


def module_path(crate: str, relative: Path) -> list[str]:
    """The module a source file under `src/` is, as rustc's file layout names it."""

    parts = list(relative.with_suffix("").parts)
    if parts[-1] in ("lib", "main", "mod"):
        parts.pop()
    return [crate, *parts]


def macro_output(session: krs_gate.Session, port: PortEmission) -> tuple[dict[str, dict[str, str]], list[str]]:
    """Every source file's expansion digests, keyed by its KRS-relative path, and the refused files."""

    digests: dict[str, dict[str, str]] = {}
    refused: list[str] = []
    for relative_package in port.packages:
        package = ROOT / relative_package
        crate, alias = crate_identity(package)
        sources = sorted((package / "src").rglob("*.rs"))
        if not sources:
            raise GateError(f"{relative_package} has no source files")
        for source in sources:
            display = source.relative_to(package).as_posix()
            result = session.expansion_digest(
                source, display, module_path(crate, source.relative_to(package / "src")), alias,
            )
            key = f"{relative_package}/{display}"
            if "refusal_sha256" in result:
                digests[key] = {"refusal_sha256": result["refusal_sha256"]}
                refused.append(key)
            else:
                digests[key] = {
                    "text_sha256": result["text_sha256"],
                    "source_map_sha256": result["source_map_sha256"],
                }
    return digests, refused


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--record", action="store_true",
        help="rewrite this gate's macro-output pins; the heavy gates' pins are never recorded here",
    )
    parser.add_argument(
        "ports", nargs="*", metavar="PORT",
        help="run only these ports (imp, kevm, kmir, kwasm); the registry entry runs all four",
    )
    arguments = parser.parse_args()
    unknown = sorted(set(arguments.ports) - {port.key for port in PORTS})
    if unknown:
        parser.error(f"unknown ports {unknown}")
    selected = [port for port in PORTS if not arguments.ports or port.key in arguments.ports]

    pins = Ledger(PINS_PATH, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.toml schema differs from 1")
    environment = semantics.build_environment()
    krs = build(environment)
    gate = krs_gate.build(environment=environment)

    with krs_gate.Session(gate, environment=environment) as session:
        for port in selected:
            digests, refused = macro_output(session, port)
            try:
                pins.expect(("macro_output", port.key), digests)
            except GateError as error:
                raise GateError(f"{port.label} macro output: {error}") from error
            note = f"; whole-file expansion refuses {', '.join(refused)}, pinned by its diagnostics" if refused else ""
            files = f"{len(digests)} source file{'' if len(digests) == 1 else 's'}"
            print(f"PASS {port.label} macro output: {files}{note}", flush=True)

    for port in selected:
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix=f"krs-ports-emit-{port.key}-", dir=scratch_root()) as temporary:
            try:
                port.emission(Path(temporary), krs, gate)
            except GateError as error:
                raise GateError(f"{port.label} emission against tests/{port.key}'s pins: {error}") from error
        print(
            f"PASS {port.label} emission: formatting, check, expansion, and artifacts match "
            f"tests/{port.key}'s pins ({time.monotonic() - started:.0f} s)",
            flush=True,
        )
    pins.finish("krs-ports-emit")
    return 0


if __name__ == "__main__":
    entry("krs-ports-emit", main)
