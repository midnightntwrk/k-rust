#!/usr/bin/env python3
"""Fail when the tracked tree depends on local-only notes, has a dead gate, or drifts from policy.

`draft/` holds untracked, machine-local working notes, and the former root
tracking ledgers now live there. A tracked file must not reference either,
because a fresh clone contains neither. For the same reason a tracked file
must not cite a local ticket id (`IR-nn`, `BL-nnn`, `CQ-nnn`); it states the
fact the ticket stood for instead. The check reads the Git index, so it covers
staged additions and ignores untracked files.

Every `tests/<gate>/` directory must also have an entry point: a `verify.py`,
or a `README.md` that states the command that runs it. A directory with
neither is a gate nobody can run, so its rot goes unnoticed. Every script a
gate README runs (`python3 tests/...`) must be tracked, so a README cannot
keep naming a verifier that was removed. `tests/support/` is the shared
verifier library, not a gate.

The workspace denies `unsafe_code` rather than forbidding it, because the Wasm
exports that `krs_wasm_abi::export!` declares carry `#[unsafe(no_mangle)]` and
must allow the lint locally. The forbid guarantee is kept here instead: only
`crates/krs-wasm-abi/src/lib.rs` may allow or expect `unsafe_code`, and no
root or crate manifest may lower the lint below `deny`.

Every tracked `Cargo.toml` that declares `rust-version` must match
`Krs.lock` `[cargo] msrv` at major.minor or inherit the workspace value, so
the minimum supported Rust has one source.

Every tracked `Cargo.toml` under `tests/` that declares its own `[workspace]`
must be a row of the standalone package table in `tests/support/packages.py`
unless it is under a `fixtures/` directory,
so no standalone package escapes its owning gate's format, lint, and MSRV checks.
Every row must name a tracked manifest that declares `[workspace]`.

    PYTHONDONTWRITEBYTECODE=1 python3 tests/repo-hygiene/verify.py
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, entry  # noqa: E402
from support.packages import PACKAGES  # noqa: E402
from support.process import run  # noqa: E402


SELF = Path(__file__).resolve().relative_to(ROOT).as_posix()

# A `draft/` path segment (not, for example, the npm scope `@open-draft/`),
# or a quoted "draft" component joined into a path in code.
DRAFT_PATH = re.compile(r"""(?:^|[^A-Za-z0-9_@-])draft/|["']draft["']\s*[/,)]""")
REMOVED_LEDGERS = re.compile(
    r"K_RUST_HANDOFF|K_RUST_UPSTREAM|K_RUST_MORE_SEMANTICS_REQUESTS|"
    r"MIR_SEMANTICS_UPSTREAM|RECOVERY_AUDIT|LAST_KNOWN_PROMPT|RECOVERY_PROVENANCE"
)
# A path under a spikes directory: the tracked one was removed (git history is its
# archive) and the browser-lessons spikes live in draft/. The bracket keeps this
# pattern itself out of a plain text search for the path.
SPIKE_PATH = re.compile(r"\bspikes[/]")
# A local ticket id. The bracket keeps this pattern out of its own search.
LOCAL_TICKET_ID = re.compile(r"\b(?:IR|BL|CQ)[-][0-9]{2,3}\b")
# A shell command that runs a gate, as a gate README must state one.
RUN_COMMAND = re.compile(r"\b(?:python3|cargo|bun|node)\s+\S")
# A repository script a README runs with python3, as `python3 tests/<gate>/<script>.py`.
PYTHON_SCRIPT = re.compile(r"\bpython3\s+(tests/[^\s`'\"]+\.py)\b")
# Directories under tests/ that are libraries rather than gates.
NOT_GATES = {"support"}
UNSAFE_EXCEPTION = "crates/krs-wasm-abi/src/lib.rs"
UNSAFE_ALLOW = re.compile(r"\b(?:allow|expect)\s*\([^)]*\bunsafe_code\b", re.DOTALL)
RUST_VERSION = re.compile(r"[0-9]+\.[0-9]+(?:\.[0-9]+)?\Z")


def tracked_files() -> list[str]:
    output = run(["git", "-C", ROOT, "ls-files", "-z"], text=False).stdout
    return [name for name in output.decode("utf-8").split("\0") if name]


def gate_entry_problems(files: list[str]) -> list[str]:
    tracked = set(files)
    gates = sorted(
        {
            parts[1]
            for parts in (name.split("/") for name in files)
            if parts[0] == "tests" and len(parts) > 2 and parts[1] not in NOT_GATES
        }
    )
    problems: list[str] = []
    for gate in gates:
        readme = f"tests/{gate}/README.md"
        text = (ROOT / readme).read_text(encoding="utf-8") if readme in tracked else ""
        for script in sorted(set(PYTHON_SCRIPT.findall(text))):
            if script not in tracked:
                problems.append(f"{readme}: runs {script}, which is not tracked")
        if f"tests/{gate}/verify.py" in tracked or RUN_COMMAND.search(text):
            continue
        problems.append(
            f"tests/{gate}/: gate has neither a verify.py nor a README.md stating the command that runs it"
        )
    return problems


def manifest_problems(relative: str, text: str, msrv: tuple[int, int]) -> list[str]:
    manifest = tomllib.loads(text)
    problems: list[str] = []
    for section in ("package", "workspace.package"):
        table = manifest
        for part in section.split("."):
            table = table.get(part, {})
        version = table.get("rust-version")
        if version is None or version == {"workspace": True}:
            continue
        if not isinstance(version, str) or not RUST_VERSION.fullmatch(version):
            problems.append(f"{relative}: [{section}] rust-version must be a version string or inherit the workspace value")
        elif tuple(map(int, version.split(".")[:2])) != msrv:
            problems.append(f"{relative}: [{section}] rust-version {version} differs from Krs.lock cargo.msrv {msrv[0]}.{msrv[1]}")

    if relative == "Cargo.toml" or relative.startswith("crates/"):
        lint = manifest.get("workspace", {}).get("lints", {}).get("rust", {}).get("unsafe_code")
        lint = manifest.get("lints", {}).get("rust", {}).get("unsafe_code", lint)
        if isinstance(lint, dict):
            lint = lint.get("level")
        if relative == "Cargo.toml" and lint != "deny":
            problems.append(f"{relative}: workspace unsafe_code lint must be deny, which the Wasm ABI exports need")
        elif lint in ("allow", "warn"):
            problems.append(f"{relative}: unsafe_code lint must be deny or forbid")
    return problems


def standalone_package_problems(files: list[str]) -> list[str]:
    tracked = set(files)
    registered = {package.manifest for package in PACKAGES}
    problems: list[str] = []
    for manifest in sorted(registered):
        if manifest not in tracked:
            problems.append(f"{manifest}: package table manifest is not tracked")
            continue
        try:
            cargo = tomllib.loads((ROOT / manifest).read_text(encoding="utf-8"))
        except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
            problems.append(f"{manifest}: cannot read package table manifest: {error}")
            continue
        if not isinstance(cargo.get("workspace"), dict):
            problems.append(f"{manifest}: package table manifest has no [workspace] table")
    for relative in files:
        parts = Path(relative).parts
        if (
            len(parts) < 3 or parts[0] != "tests" or parts[-1] != "Cargo.toml"
            or relative in registered or "fixtures" in parts[1:-1]
        ):
            continue
        path = ROOT / relative
        if not path.is_file():
            continue
        try:
            cargo = tomllib.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
            problems.append(f"{relative}: cannot read Cargo manifest: {error}")
            continue
        if isinstance(cargo.get("workspace"), dict):
            problems.append(f"{relative}: standalone Rust workspace has no package table row")
    return problems


def main() -> int:
    files = tracked_files()
    problems = gate_entry_problems(files)
    lock = tomllib.loads((ROOT / "Krs.lock").read_text(encoding="utf-8"))
    msrv = tuple(map(int, lock["cargo"]["msrv"].split(".")[:2]))
    problems.extend(standalone_package_problems(files))
    for relative in files:
        if relative == "draft" or relative.startswith("draft/"):
            problems.append(f"{relative}: tracked file under draft/")
            continue
        if relative == SELF:
            continue
        path = ROOT / relative
        if not path.is_file():
            continue
        data = path.read_bytes()
        if b"\0" in data:
            continue
        text = data.decode("utf-8", errors="replace")
        if relative.endswith(".rs"):
            for match in UNSAFE_ALLOW.finditer(text):
                if relative != UNSAFE_EXCEPTION:
                    number = text.count("\n", 0, match.start()) + 1
                    problems.append(f"{relative}:{number}: allows or expects unsafe_code outside the Wasm ABI macro")
        if relative == "Cargo.toml" or relative.endswith("/Cargo.toml"):
            problems.extend(manifest_problems(relative, text, msrv))
        for number, line in enumerate(text.splitlines(), start=1):
            for pattern, what in (
                (DRAFT_PATH, "references draft/"),
                (REMOVED_LEDGERS, "references a removed root ledger"),
                (SPIKE_PATH, "references a local-only spike path"),
                (LOCAL_TICKET_ID, "cites a local ticket id"),
            ):
                match = pattern.search(line)
                if match:
                    problems.append(f"{relative}:{number}: {what}: {line.strip()[:160]}")
    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f"FAIL repository hygiene: {len(problems)} finding(s)", file=sys.stderr)
        return 1
    print(
        "PASS repository hygiene: tracked references, gate entry points, standalone package table, "
        "unsafe_code lint policy, and Cargo MSRV"
    )
    return 0


if __name__ == "__main__":
    entry("repository hygiene", main)
