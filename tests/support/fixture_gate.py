"""Shared harness for the feature fixture gates (`tests/grammar-lexing` and its siblings).

A feature gate checks small KRS fixture packages end to end:

- KRS: `krs check`, `krs expand`, and `krs emit-k`, with the expansion and every
  emitted `.k` artifact pinned by digest (`expand.<package>`, `emitted.<package>.<artifact>`);
- the native route: the emitted Definition IR loaded into one `krs-gate` session,
  programs parsed through `configure` (k-rust selects `<MAIN>-SYNTAX` for `$PGM`)
  and run through `execute`;
- the Java K route: the emitted definition kompiled with `--syntax-module
  <MAIN>-SYNTAX`, programs parsed with `kast` and run with `krun`, all replayed
  from the per-user reference cache (`support.reference`);
- the comparison: each program's normalized outcome must agree on both routes.

Outcomes are normalized. A parse is `accepted` or `rejected`; a run is the final
computation cell, or `undefined` when the result is undefined: an LLVM
partial-function abort (krun exit 113 with an unevaluated function in the
computation) and a native `#Bottom` both normalize to `undefined`.

A fixture may pin a named divergence in its ledger's `known_divergences` table,
with the native and Java outcomes recorded separately. The gate fails closed when
either side changes, and when a pinned divergence disappears.

Negative fixtures pin the first diagnostic line of a failing `krs check`
(`diagnostics.<name>`), with absolute paths of the repository replaced.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import os
from pathlib import Path
import re
import subprocess
from typing import Any, Iterator, Mapping, Sequence

from support import ROOT, GateError, krs_gate
from support.hashing import sha256_file
from support.krs import Invocation
from support.pins import Ledger
from support.process import run
from support.reference import Key, Pin, Snapshot, repository_inputs, substitute


UNDEFINED = "undefined"
ACCEPTED = "accepted"
REJECTED = "rejected"
JAVA_TOOLS = ("kompile", "kast", "krun")
LLVM_PARTIAL_FUNCTION_ABORT = 113
_K_CELL = re.compile(r"<k>\s*(.*?)\s*</k>", re.DOTALL)
_SOURCE_LOCATION = substitute(r"\n\tSource\([^\n]*\)[\s\S]*", "\n")
"""K's scanner and parser errors name the program file; only the first line is compared."""


@dataclass(frozen=True)
class Fixture:
    """One KRS fixture package and its definition facet."""

    manifest: Path
    package: str
    definition: str = "main"
    dependencies: tuple[str, ...] = ()

    def invocation(self, krs: Path) -> Invocation:
        return Invocation(krs, self.manifest, self.package, self.definition)

    def argv_extra(self) -> list[str]:
        extra: list[str] = []
        for dependency in self.dependencies:
            extra.extend(("--dependency", dependency))
        return extra


@dataclass
class Emitted:
    """The emitted artifacts of one fixture and its main module."""

    fixture: Fixture
    directory: Path
    main_module: str

    @property
    def syntax_module(self) -> str:
        return f"{self.main_module}-SYNTAX"

    @property
    def definition_ir(self) -> Path:
        return self.directory / "definition-ir.json"

    @property
    def source(self) -> Path:
        return self.directory / "definition.k"


@dataclass
class Program:
    """One program text and the outcomes both routes must agree on."""

    name: str
    text: str
    parse: str
    run: str | None = None
    sort: str | None = None
    kast: str | None = None
    """When set, the Java `kast` output (KAST text) of an accepted program."""
    search: tuple[str, ...] | None = None
    """When set, the computation cells of every final state `search` reaches, as a multiset.

    A nondeterministic program sets `run` to `None`: `krun` picks one of its
    outcomes, so only the search is compared."""
    variables: tuple[tuple[str, str], ...] = ()
    """Further configuration variables `(NAME, text)`, bound beside `$PGM` on both routes."""


@dataclass
class FixtureGate:
    """The ledger, tools, and workspace one feature gate run shares."""

    label: str
    pins: Ledger
    workspace: Path
    krs: Path
    gate: Path
    environment: Mapping[str, str]
    refresh: bool = False
    divergences: dict[str, Any] = field(default_factory=dict)

    def _krs(self, fixture: Fixture, command: str, *extra: os.PathLike[str] | str, check: bool = True) -> subprocess.CompletedProcess[str]:
        argv = fixture.invocation(self.krs).argv(command, *fixture.argv_extra(), *extra)
        if check:
            return run(argv, environment=self.environment, timeout=900)
        return subprocess.run(
            argv, cwd=ROOT, env={**os.environ, **self.environment}, text=True,
            capture_output=True, timeout=900, check=False,
        )

    def check(self, fixture: Fixture, *extra: str) -> subprocess.CompletedProcess[str]:
        """Run `krs check` and require success."""

        return self._krs(fixture, "check", *extra)

    def partition(self, fixture: Fixture) -> tuple[str, list[str]]:
        """Pin and return the `krs check --partition` text and its warning headlines."""

        process = self._krs(fixture, "check", "--partition", check=False)
        if process.returncode != 0:
            raise GateError(f"{fixture.package}: krs check --partition failed:\n{process.stderr}")
        warnings = diagnostic_lines(process.stderr)
        self.pins.expect(("partition", fixture.package), process.stdout)
        self.pins.expect(("partition_warnings", fixture.package), warnings)
        return process.stdout, warnings

    def expand(self, fixture: Fixture) -> str:
        """Pin and return the deterministic `krs expand` reference surface."""

        expansion = self._krs(fixture, "expand").stdout
        self.pins.expect(("expand", fixture.package), _sha256_text(expansion))
        return expansion

    def build(self, fixture: Fixture) -> Path:
        """Compile the fixture natively and return the KORE artifact directory."""

        directory = self.workspace / "native" / fixture.package
        self._krs(fixture, "build", "--output", directory)
        return directory

    def run_command(self, fixture: Fixture, command: str, *extra: os.PathLike[str] | str) -> str:
        """Run a `krs parse`, `run`, `search`, or `prove` command on the fixture and return its stdout."""

        return self._krs(fixture, command, *extra).stdout

    def emit(self, fixture: Fixture) -> Emitted:
        """Emit canonical K, pin every `.k` artifact, and return the artifacts."""

        directory = self.workspace / "emitted" / fixture.package
        self._krs(fixture, "emit-k", "--output", directory)
        for artifact in sorted(directory.glob("*.k")):
            self.pins.expect(("emitted", fixture.package, artifact.name), sha256_file(artifact))
        modules = krs_gate.ir_query(self.gate, directory, {"kind": "modules"}, environment=self.environment)
        return Emitted(fixture, directory, modules["main_module"])

    def diagnostic(self, name: str, fixture: Fixture, *extra: str) -> str:
        """Require `krs check` to fail and pin its diagnostic lines."""

        process = self._krs(fixture, "check", *extra, check=False)
        if process.returncode == 0:
            raise GateError(f"{name}: krs check unexpectedly accepted {fixture.package}")
        lines = diagnostic_lines(process.stderr)
        if not lines:
            raise GateError(f"{name}: krs check failed without a diagnostic:\n{process.stderr}")
        self.pins.expect(("diagnostics", name), lines)
        return "\n".join(lines)

    def compare(
        self, emitted: Emitted, programs: Sequence[Program], *, sort: str, search: bool = False,
    ) -> dict[str, Any]:
        """Run every program on both routes and require the pinned outcomes to agree.

        With `search`, Java K kompiles with `--enable-search`, and each program
        with a `search` expectation is also searched on both routes: native
        `search` and `krun --search` must reach the same multiset of final
        computation cells.
        """

        native = self._native_outcomes(emitted, programs)
        java = self._java_outcomes(emitted, programs, sort=sort, search=search)
        observed: dict[str, Any] = {}
        known = self.divergences.get(emitted.fixture.package, {})
        for program in programs:
            routes = {"native": native[program.name], "java": java[program.name]}
            divergence = known.get(program.name)
            if divergence is not None:
                if routes != divergence:
                    raise GateError(
                        f"{emitted.fixture.package} {program.name}: pinned divergence changed: "
                        f"expected {divergence}, observed {routes}"
                    )
                observed[program.name] = routes
                continue
            if routes["native"] != routes["java"]:
                raise GateError(
                    f"{emitted.fixture.package} {program.name}: native {routes['native']} "
                    f"differs from Java K {routes['java']}"
                )
            expected: dict[str, Any] = {"parse": program.parse, "run": program.run}
            if program.search is not None:
                expected["search"] = sorted(program.search)
            if routes["native"] != expected:
                raise GateError(
                    f"{emitted.fixture.package} {program.name}: both routes observed "
                    f"{routes['native']}, expected {expected}"
                )
            observed[program.name] = routes["native"]
        self.pins.expect(("outcomes", emitted.fixture.package), observed)
        return observed

    def _native_outcomes(self, emitted: Emitted, programs: Sequence[Program]) -> dict[str, dict[str, Any]]:
        outcomes: dict[str, dict[str, Any]] = {}
        with krs_gate.Session(self.gate, environment=self.environment) as session:
            session.load(emitted.definition_ir, emitted.main_module)
            for program in programs:
                try:
                    pattern = session.configure({"PGM": program.text, **dict(program.variables)})["pattern"]
                except GateError:
                    outcomes[program.name] = {"parse": REJECTED, "run": None}
                    continue
                if program.run is None:
                    outcomes[program.name] = {"parse": ACCEPTED, "run": None}
                    if program.search is not None:
                        outcomes[program.name]["search"] = _native_search(session, program, pattern)
                    continue
                leaves = session.execute(pattern).get("leaves") or []
                if not leaves or any("bottom" in str(leaf.get("reason", "")).lower() for leaf in leaves):
                    outcomes[program.name] = {"parse": ACCEPTED, "run": UNDEFINED}
                    continue
                session.execute(pattern, keep=program.name)
                try:
                    if program.run == ".K":
                        session.expect(program.name, "k", text=".K")
                    else:
                        session.expect(program.name, "k", head=program.run)
                    actual = program.run
                except GateError as error:
                    actual = f"differs: {error}"
                outcomes[program.name] = {"parse": ACCEPTED, "run": actual}
                if program.search is not None:
                    outcomes[program.name]["search"] = _native_search(session, program, pattern)
        return outcomes

    def _java_outcomes(
        self, emitted: Emitted, programs: Sequence[Program], *, sort: str, search: bool = False,
    ) -> dict[str, dict[str, Any]]:
        sources = [emitted.source]
        program_directory = self.workspace / "programs" / emitted.fixture.package
        program_directory.mkdir(parents=True, exist_ok=True)
        paths = {}
        for program in programs:
            path = program_directory / f"{program.name}.pgm"
            path.write_text(program.text + "\n", encoding="utf-8")
            paths[program.name] = path
        k = Snapshot(
            f"{self.label}/{emitted.fixture.package}",
            Key(tools=JAVA_TOOLS, inputs=repository_inputs([])),
            workspace=self.workspace, refresh=self.refresh,
            pin=Pin(self.pins, emitted.fixture.package),
        )
        compiled = self.workspace / "kompiled" / emitted.fixture.package
        process = k.run(
            "kompile/definition", "kompile",
            [
                *sources, "--main-module", emitted.main_module,
                "--syntax-module", emitted.syntax_module,
                "--backend", "llvm", "--output-definition", compiled,
                *(("--enable-search",) if search else ()),
            ],
            timeout=900,
        )
        if process.returncode != 0:
            raise GateError(f"{emitted.fixture.package}: kompile rejected the emitted definition:\n{process.stderr}")
        outcomes: dict[str, dict[str, Any]] = {}
        for program in programs:
            parsed = k.run(
                f"kast/{program.name}", "kast",
                ["--definition", compiled, "--sort", program.sort or sort, paths[program.name]],
                timeout=120, streams={"stderr": _SOURCE_LOCATION},
            )
            if parsed.returncode != 0:
                outcomes[program.name] = {"parse": REJECTED, "run": None}
                continue
            if program.kast is not None and parsed.stdout.strip() != program.kast:
                raise GateError(
                    f"{emitted.fixture.package} {program.name}: kast printed {parsed.stdout.strip()!r}, "
                    f"expected {program.kast!r}"
                )
            bindings = [f"-c{name}={value}" for name, value in program.variables]
            if program.run is None:
                outcomes[program.name] = {"parse": ACCEPTED, "run": None}
            else:
                executed = k.run(
                    f"krun/{program.name}", "krun",
                    ["--definition", compiled, *bindings, paths[program.name]],
                    timeout=120,
                )
                outcomes[program.name] = {"parse": ACCEPTED, "run": java_run_outcome(executed)}
            if program.search is not None:
                if not search:
                    raise GateError(f"{program.name}: a search expectation needs compare(..., search=True)")
                searched = k.run(
                    f"krun-search/{program.name}", "krun",
                    ["--definition", compiled, "--search", *bindings, paths[program.name]],
                    timeout=120,
                )
                outcomes[program.name]["search"] = java_search_outcome(searched)
        print(f"PASS {self.label} {emitted.fixture.package} reference snapshot: {k.finish()}")
        return outcomes


def java_run_outcome(process: subprocess.CompletedProcess[str]) -> str:
    """Normalize a `krun` result to the final computation cell or `undefined`."""

    if process.returncode == LLVM_PARTIAL_FUNCTION_ABORT:
        return UNDEFINED
    if process.returncode != 0:
        raise GateError(f"krun failed with status {process.returncode}:\n{process.stderr}")
    match = _K_CELL.search(process.stdout)
    if match is None:
        raise GateError(f"krun printed no computation cell:\n{process.stdout}")
    cell = re.sub(r"\s+", " ", match.group(1)).strip()
    cell = re.sub(r"\s*~>\s*\.K$", "", cell)
    return ".K" if cell in ("", ".K") else cell


def _native_search(session: krs_gate.Session, program: Program, pattern: str) -> list[str]:
    """The multiset of final computation cells native search reaches, by the expected texts."""

    prefix = f"{program.name}#search#"
    count = session.search(pattern, keep_each=prefix)["states"]
    candidates = sorted(set(program.search or ()))
    observed = []
    for index in range(count):
        state = f"{prefix}{index}"
        matched = [
            candidate for candidate in candidates
            if session.request(
                "expect", state=state, cell="k",
                **({"text": ".K"} if candidate == ".K" else {"head": candidate}),
            )["met"]
        ]
        observed.append(matched[0] if len(matched) == 1 else f"unmatched state {index}")
    return sorted(observed)


def java_search_outcome(process: subprocess.CompletedProcess[str]) -> list[str]:
    """Normalize `krun --search` output to the sorted computation cells of its solutions."""

    if process.returncode != 0:
        raise GateError(f"krun --search failed with status {process.returncode}:\n{process.stderr}")
    cells = []
    for match in _K_CELL.finditer(process.stdout):
        cell = re.sub(r"\s+", " ", match.group(1)).strip()
        cell = re.sub(r"\s*~>\s*\.K$", "", cell)
        cells.append(".K" if cell in ("", ".K") else cell)
    if not cells:
        raise GateError(f"krun --search printed no computation cell:\n{process.stdout}")
    return sorted(cells)


def diagnostic_lines(stderr: str) -> list[str]:
    """Return the `error[...]`/`warning[...]` headlines of a KRS diagnostic report, path-free."""

    lines = []
    for line in stderr.splitlines():
        if re.match(r"^(error|warning)(\[[^\]]+\])?: ", line) or line.startswith("krs: "):
            lines.append(line.replace(os.fspath(ROOT), "{{root}}"))
    return lines


def _sha256_text(text: str) -> str:
    import hashlib

    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def fixture_packages(manifest: Path, names: Sequence[str]) -> Iterator[Fixture]:
    for name in names:
        yield Fixture(manifest, name)



def kore_attribute_lines(gate: Path, kore: Path, labels: Sequence[str], names: Sequence[str], *,
                         environment: Mapping[str, str] | None = None) -> str:
    """Return the named string attributes of the labels' KORE symbol declarations, one line each.

    `krs-gate` parses the definition (Java K writes each declaration on one
    line and k-rust across several); the lines name K labels.
    """

    rows = krs_gate.kore_attributes(gate, kore, labels, names, environment=environment)
    return "".join(
        f"{label} " + " ".join(f"{name}={rows[label][name]!r}" for name in sorted(rows[label])) + "\n"
        for label in labels
    )
