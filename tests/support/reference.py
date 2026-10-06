"""Recorded reference-K results: committed snapshots replayed by default.

A reference-K (Java K) invocation is a function of the K release, the tool, its
argument vector, the upstream revisions it reads, and the bytes of its inputs.
None of these change between ordinary gate runs, so a gate replays a committed
snapshot of the invocation instead of running Java K again.

A snapshot is one directory under the owning gate's directory.
Its `manifest.toml` holds the key and the digest of every stored file:

- the key: the K version from `Krs.lock`, the K tool names the snapshot may
  run, the upstream revisions it reads, and the digests of its declared input
  files (fixtures, corpora, and the files they `require`);
- one `[[invocation]]` table per recorded tool run: a label, the argument
  vector, the digest of every regular file the argument vector names (so a
  KRS-emitted `.k` or `spec.k` is keyed by its digest), the exit status, the
  standard stream digests, and the digests of the declared output files the
  comparators read.

A declared output, and either standard stream, may name a reducer that
removes what no comparator reads, or what varies between runs of the same
invocation, before it is stored. A live run hands the comparators the reduced
text too, so live and replayed runs check the same evidence.
`json_without_members` removes named object members, such as source-location
attributes, from a JSON file; `indented_json` spells a JSON document one member
per line so a stored proof result or claim reads and diffs as text;
`substitute` rewrites a regular expression.
A declared output whose path the tool chooses (such as the `spec.kore` that
`kprove --dry-run` writes under a fresh directory in its `--temp-dir`) names a
`locate` function; a live run reads the file it finds, and both modes leave
the evidence at the declared path.

Every other file in the directory is a stored stream or output named after its
invocation label; only the evidence the comparators consume is stored, never a
whole kompiled directory.
Absolute paths of the gate workspace, the repository, and its parent directory
are stored as the placeholders `{{work}}`, `{{root}}`, and `{{external}}`, and
restored on replay, so a snapshot is independent of the checkout location.

A gate opens its snapshots in one of two modes:

- replay (the default): the manifest key must equal the current key, each
  requested invocation must have been recorded with the same argument vector
  and input digests, every stored file must match its digest, and every
  recorded invocation must be requested exactly once.
  A missing snapshot or any difference fails closed and names
  `--refresh-reference`; replay never falls back to running Java K and never
  skips;
- refresh (`--refresh-reference`): the pinned K tools run live, and
  `Snapshot.finish` rewrites the snapshot from exactly the invocations that ran.
  A gate calls `finish` only after every step passed, so a failing run leaves
  the committed snapshot unchanged.

`--refresh-reference` is distinct from `--record`: `--record` rewrites output
pins in a gate ledger, and `--refresh-reference` rewrites reference snapshots.
A gate accepts both together.

A gate that runs a snapshot-backed helper as a child process passes it
`--reference-staging DIR` with `--refresh-reference`: the helper writes its
refreshed snapshot to that staging directory, and the gate's `Promotion`
replaces the committed snapshot only after every one of its own steps passed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading
from typing import Any, Callable, Mapping, Sequence

from support import ROOT, GateError
from support.hashing import sha256_file, sha256_text
from support.lock import k_version
from support.pins import load_toml
from support.process import run
from support.tools import k_tool


SCHEMA = 1
MANIFEST = "manifest.toml"
REFRESH_OPTION = "--refresh-reference"
REFRESH_ADVICE = f"run the gate with {REFRESH_OPTION} (Java K on PATH) to re-record it"
STAGING_OPTION = "--reference-staging"
_LABEL = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._@+-]*(/[A-Za-z0-9][A-Za-z0-9._@+-]*)*$")
_STREAMS = ("stdout", "stderr")


def add_refresh_argument(parser: argparse.ArgumentParser) -> None:
    """Add the `--refresh-reference` option every snapshot-backed gate shares."""

    parser.add_argument(
        REFRESH_OPTION,
        dest="refresh_reference",
        action="store_true",
        help=(
            "run the pinned Java K tools live and rewrite the reference snapshots "
            "they measured, only if every step passes"
        ),
    )


def add_staging_argument(parser: argparse.ArgumentParser) -> None:
    """Add the `--reference-staging` option of a helper a gate runs as a child process."""

    parser.add_argument(
        STAGING_OPTION,
        dest="reference_staging",
        type=Path,
        help=(
            f"with {REFRESH_OPTION}, write the refreshed snapshot to this directory "
            "for the calling gate to promote, instead of rewriting the committed one"
        ),
    )


def live_tools(names: Sequence[str]) -> dict[str, str]:
    """Locate each named K tool and require the `Krs.lock` K version.

    Only a live (refresh) run calls this; replay needs no K tool.
    """

    return {name: k_tool(name, k_version()) for name in names}


@dataclass(frozen=True)
class Key:
    """What a snapshot depends on besides each invocation's argument vector.

    `inputs` maps a stable name (a repository-relative path) to a file whose
    digest enters the key; it must cover every file a recorded tool reads that
    no upstream revision or argument-vector digest already fixes, including
    the files a definition `require`s.
    """

    tools: tuple[str, ...]
    upstream: Mapping[str, str] = field(default_factory=dict)
    inputs: Mapping[str, Path] = field(default_factory=dict)

    def render(self) -> dict[str, Any]:
        """The manifest spelling of the key, with every input digested now."""

        return {
            "k_version": k_version(),
            "tools": sorted(set(self.tools)),
            "upstream": {name: str(self.upstream[name]) for name in sorted(self.upstream)},
            "inputs": {name: sha256_file(self.inputs[name]) for name in sorted(self.inputs)},
        }


@dataclass(frozen=True)
class Output:
    """A file a recorded tool writes and a comparator reads.

    `reduce` maps the file's text to the stored evidence; it must keep
    everything a comparator reads and be deterministic.
    `locate`, when the tool chooses where it writes the file, finds that one
    file after a live run; its reduced text is then written to `path`, where
    replay also restores it, so a comparator always reads `path`.
    """

    path: Path
    reduce: Callable[[str], str] | None = None
    locate: Callable[[], Path] | None = None


def json_without_members(names: Sequence[str]) -> Callable[[str], str]:
    """A reducer that drops every JSON object member with one of `names`, at any depth.

    The result is canonical JSON: sorted keys, no insignificant whitespace,
    and a final newline.
    """

    dropped = frozenset(names)

    def strip(value: Any) -> Any:
        if isinstance(value, dict):
            return {key: strip(item) for key, item in value.items() if key not in dropped}
        if isinstance(value, list):
            return [strip(item) for item in value]
        return value

    def reduce(text: str) -> str:
        return json.dumps(strip(json.loads(text)), sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"

    return reduce


def json_sorted_lists(names: Sequence[str]) -> Callable[[str], str]:
    """A reducer that sorts every JSON list that is the value of a member named in `names`.

    Elements are ordered by their canonical spelling, and the result is
    canonical JSON as `json_without_members` writes it. Use it only for a list
    the comparators read as a multiset, such as the sentences of a module.
    """

    sorted_names = frozenset(names)

    def canonical(value: Any) -> str:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

    def order(value: Any) -> Any:
        if isinstance(value, dict):
            return {
                key: sorted((order(item) for item in child), key=canonical)
                if key in sorted_names and isinstance(child, list) else order(child)
                for key, child in value.items()
            }
        if isinstance(value, list):
            return [order(item) for item in value]
        return value

    def reduce(text: str) -> str:
        return canonical(order(json.loads(text))) + "\n"

    return reduce


def sorted_kore_claims(text: str) -> str:
    """A reducer that sorts the claim blocks of a KORE spec module by their text.

    `kprove` writes each claim as a `// claim` comment line followed by its
    axiom, in an order that varies between runs; the comparators read the
    claims by label. Every line is kept.
    """

    lines = text.splitlines(keepends=True)
    starts = [index for index, line in enumerate(lines) if line.startswith("// claim ")]
    if not starts:
        return text
    end = next(
        (index for index in range(starts[-1], len(lines)) if lines[index].startswith("endmodule")),
        len(lines),
    )
    blocks = ["".join(lines[start:stop]) for start, stop in zip(starts, [*starts[1:], end])]
    return "".join(lines[:starts[0]]) + "".join(sorted(blocks)) + "".join(lines[end:])


def indented_json(text: str) -> str:
    """A reducer that spells one JSON document with one member or element per line.

    Member order and every value are kept, so the stored text is the same
    JSON value as the tool's output, readable and diffable as text.
    Text that is not one JSON document, such as the empty output of a failed
    run, is kept unchanged.
    """

    try:
        value = json.loads(text)
    except ValueError:
        return text
    return json.dumps(value, indent=1, ensure_ascii=False) + "\n"


def substitute(pattern: str, replacement: str) -> Callable[[str], str]:
    """A reducer that replaces every match of the regular expression `pattern`."""

    compiled = re.compile(pattern)
    return lambda text: compiled.sub(replacement, text)


reduce_kore_exec_log = substitute(r"(?m)^kore-exec: \[\d+\]", "kore-exec: [-]")
"""kore-exec prefixes each log line with a run-dependent number; no comparator reads it."""

reduce_kprove_temp = substitute(r"\.kprove-[0-9a-f-]+", ".kprove-TEMP")
"""kprove names its directory under `--temp-dir` by time and a random UUID; no comparator reads it."""

reduce_store_paths = substitute(r"/nix/store/[0-9a-z]{32}-[^/\s\")]*", "NIX-STORE")
"""K records the install path of its prelude (`domains.md`) in source attributes, which no comparator reads."""


_KORE_SENTENCE = re.compile(r"\s*(?:axiom|claim|symbol|hooked-symbol|sort|hooked-sort|alias|import|module|endmodule)\b")
_KORE_IMPORT = re.compile(r"\s*import\s")
_KORE_GENERATED = re.compile(r"(?<![A-Za-z0-9'-])Var'Unds'Gen([0-9]+)(?![A-Za-z0-9'-])")


def _kore_sentences(text: str) -> list[list[str]]:
    """The lines of a KORE text split before each line that starts a sentence or module."""

    chunks: list[list[str]] = [[]]
    for line in text.splitlines(keepends=True):
        if _KORE_SENTENCE.match(line) and chunks[-1]:
            chunks.append([])
        chunks[-1].append(line)
    return chunks


def sorted_kore_imports(text: str) -> str:
    """A reducer that sorts each run of consecutive `import` lines of a KORE text.

    K writes a module's imports in an order that can vary between runs; the
    KORE comparator reads a module's sentences as a multiset.
    """

    lines = text.splitlines(keepends=True)
    result: list[str] = []
    run_lines: list[str] = []
    for line in lines:
        if _KORE_IMPORT.match(line):
            run_lines.append(line)
            continue
        result.extend(sorted(run_lines))
        run_lines = []
        result.append(line)
    result.extend(sorted(run_lines))
    return "".join(result)


def renumbered_kore_generated_variables(text: str) -> str:
    """A reducer that renumbers K's generated `_GenN` variables within each KORE sentence.

    The Haskell backend numbers the variables it generates (such as those of an
    `owise` rule's negated side condition) in an order that can vary between
    runs. A variable is local to its sentence, so each sentence's `_Gen`
    variables are renamed bijectively to `_Gen0`, `_Gen1`, ... in order of first
    occurrence: an alpha-renaming, which the KORE comparator's per-sentence
    alpha normalization already ignores.
    """

    def renumber(chunk: str) -> str:
        names: dict[str, str] = {}

        def rename(match: re.Match[str]) -> str:
            return names.setdefault(match.group(1), f"Var'Unds'Gen{len(names)}")

        return _KORE_GENERATED.sub(rename, chunk)

    return "".join(renumber("".join(chunk)) for chunk in _kore_sentences(text))


def repository_inputs(paths: Sequence[Path]) -> dict[str, Path]:
    """Name each input file by its repository-relative path."""

    return {path.resolve().relative_to(ROOT).as_posix(): path for path in paths}


class Placeholders:
    """The reversible substitution of checkout-specific absolute paths."""

    def __init__(self, workspace: Path) -> None:
        pairs = [
            ("{{work}}", os.fspath(workspace.resolve())),
            ("{{root}}", os.fspath(ROOT)),
            ("{{external}}", os.fspath(ROOT.parent)),
        ]
        # The longest path is replaced first, so a path inside another keeps
        # its more specific placeholder.
        self.pairs = sorted(pairs, key=lambda pair: len(pair[1]), reverse=True)

    def store(self, text: str) -> str:
        for placeholder, _ in self.pairs:
            if placeholder in text:
                raise GateError(f"tool output already contains the snapshot placeholder {placeholder}")
        for placeholder, path in self.pairs:
            text = text.replace(path, placeholder)
        return text

    def restore(self, text: str) -> str:
        for placeholder, path in self.pairs:
            text = text.replace(placeholder, path)
        return text


@dataclass
class _Invocation:
    label: str
    argv: list[str]
    inputs: dict[str, str]
    returncode: int
    streams: dict[str, str]
    outputs: dict[str, str]
    """Normalized output path -> stored text."""

    def stored_files(self) -> dict[str, str]:
        """Snapshot-relative file name -> stored text, omitting empty streams."""

        files = {
            f"{self.label}.{stream}": text for stream, text in self.streams.items() if text
        }
        for path, text in self.outputs.items():
            files[f"{self.label}.out.{path.rsplit('/', 1)[-1]}"] = text
        return files

    def manifest(self) -> dict[str, Any]:
        return {
            "label": self.label,
            "argv": self.argv,
            "returncode": self.returncode,
            **{stream: sha256_text(self.streams[stream]) for stream in _STREAMS},
            "inputs": dict(sorted(self.inputs.items())),
            "outputs": {path: sha256_text(text) for path, text in sorted(self.outputs.items())},
        }


class Snapshot:
    """One snapshot directory, opened for replay or for a live refresh."""

    def __init__(
        self,
        directory: Path,
        key: Key,
        *,
        workspace: Path,
        refresh: bool,
        executables: Mapping[str, str] | None = None,
    ) -> None:
        """Open `directory`; replay checks the key now and fails closed.

        A refresh needs `executables` for every tool in the key, normally from
        `live_tools`.
        """

        self.directory = directory
        self.key = key
        self.refresh = refresh
        self.placeholders = Placeholders(workspace)
        self.rendered_key = key.render()
        self._lock = threading.Lock()
        self._invocations: dict[str, _Invocation] = {}
        self._recorded: dict[str, dict[str, Any]] = {}
        self._consumed: set[str] = set()
        if refresh:
            missing = sorted(set(key.tools) - set(executables or {}))
            if missing:
                raise GateError(f"a reference refresh needs the K tools {', '.join(missing)}")
            self.executables = dict(executables or {})
        else:
            self.executables = {}
            self._load()

    @property
    def name(self) -> str:
        try:
            return self.directory.relative_to(ROOT).as_posix()
        except ValueError:
            return os.fspath(self.directory)

    def _fail(self, problem: str) -> GateError:
        return GateError(f"reference snapshot {self.name}: {problem}; {REFRESH_ADVICE}")

    def _load(self) -> None:
        manifest_path = self.directory / MANIFEST
        if not manifest_path.is_file():
            raise self._fail("is missing")
        manifest = load_toml(manifest_path)
        if manifest.get("schema") != SCHEMA:
            raise self._fail(f"has schema {manifest.get('schema')!r}, not {SCHEMA}")
        recorded_key = manifest.get("key")
        if recorded_key != self.rendered_key:
            raise self._fail(f"key differs: {describe_difference(recorded_key, self.rendered_key)}")
        invocations = manifest.get("invocation", [])
        if not isinstance(invocations, list):
            raise self._fail("manifest invocation is not an array of tables")
        expected_files = {MANIFEST}
        for entry in invocations:
            label = entry.get("label") if isinstance(entry, dict) else None
            if not isinstance(label, str) or not _LABEL.match(label) or label in self._recorded:
                raise self._fail(f"manifest invocation label {label!r} is missing, invalid, or repeated")
            self._recorded[label] = entry
            for stream in _STREAMS:
                if entry.get(stream) != sha256_text(""):
                    expected_files.add(f"{label}.{stream}")
            for path in entry.get("outputs", {}):
                expected_files.add(f"{label}.out.{path.rsplit('/', 1)[-1]}")
        actual_files = {
            path.relative_to(self.directory).as_posix()
            for path in self.directory.rglob("*") if path.is_file()
        }
        if actual_files != expected_files:
            raise self._fail(
                f"files differ from the manifest: unexpected={sorted(actual_files - expected_files)}, "
                f"missing={sorted(expected_files - actual_files)}"
            )

    def _stored_text(self, name: str, digest: str) -> str:
        if digest == sha256_text(""):
            return ""
        text = (self.directory / name).read_text(encoding="utf-8")
        if sha256_text(text) != digest:
            raise self._fail(f"{name} differs from its manifest digest")
        return text

    def _normalize_argv(self, argv: Sequence[str]) -> list[str]:
        return [self.placeholders.store(argument) for argument in argv]

    def _input_digests(self, argv: Sequence[str], outputs: Sequence[Output]) -> dict[str, str]:
        excluded = {os.fspath(output.path) for output in outputs}
        digests = {}
        for argument in argv:
            if argument in excluded:
                continue
            path = Path(argument)
            if path.is_absolute() and path.is_file():
                digests[self.placeholders.store(argument)] = sha256_file(path)
        return digests

    def run(
        self,
        label: str,
        tool: str,
        arguments: Sequence[str | os.PathLike[str]],
        *,
        timeout: float,
        outputs: Sequence[Path | Output] = (),
        prefix: Sequence[str] = (),
        streams: Mapping[str, Callable[[str], str]] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """Run or replay one K tool invocation and return its completed process.

        `outputs` names the files the tool writes that a comparator reads;
        they are stored (reduced, when an `Output` names a reducer), and
        replay writes the stored text back to the same paths.
        `prefix` names a wrapper command (such as `timeout`) and its options;
        its first element is resolved on PATH only in a live run.
        `streams` maps `stdout` or `stderr` to a reducer applied before storing.
        """

        if not _LABEL.match(label):
            raise GateError(f"invalid reference invocation label: {label!r}")
        if tool not in self.key.tools:
            raise GateError(f"reference snapshot {self.name} does not declare the K tool {tool!r}")
        declared = [output if isinstance(output, Output) else Output(output) for output in outputs]
        if len({output.path.name for output in declared}) != len(declared):
            raise GateError(f"reference invocation {label} declares outputs with one file name twice")
        reducers = dict(streams or {})
        if not set(reducers) <= set(_STREAMS):
            raise GateError(f"reference invocation {label} reduces unknown streams {sorted(reducers)}")
        resolved = [os.fspath(argument) for argument in arguments]
        argv = self._normalize_argv([*prefix, tool, *resolved])
        inputs = self._input_digests(resolved, declared)
        with self._lock:
            # The label is reserved before a live run starts, so two
            # concurrent runs cannot both record under it.
            if label in self._consumed:
                raise GateError(f"reference invocation label {label} is used twice")
            self._consumed.add(label)
        if self.refresh:
            return self._run_live(label, tool, resolved, argv, inputs, timeout, declared, prefix, reducers)
        return self._replay(label, argv, inputs, [output.path for output in declared])

    def _run_live(
        self,
        label: str,
        tool: str,
        resolved: list[str],
        argv: list[str],
        inputs: dict[str, str],
        timeout: float,
        outputs: Sequence[Output],
        prefix: Sequence[str],
        reducers: Mapping[str, Callable[[str], str]],
    ) -> subprocess.CompletedProcess[str]:
        command = list(prefix)
        if command:
            wrapper = shutil.which(command[0])
            if wrapper is None:
                raise GateError(f"the wrapper command {command[0]} is unavailable")
            command[0] = wrapper
        command = [*command, self.executables[tool], *resolved]
        process = run(command, timeout=timeout, check=False)
        stored_outputs = {}
        for output in outputs:
            source = output.locate() if output.locate is not None else output.path
            if source.is_file():
                text = source.read_text(encoding="utf-8")
                if output.reduce is not None:
                    text = output.reduce(text)
                if output.reduce is not None or source != output.path:
                    output.path.parent.mkdir(parents=True, exist_ok=True)
                    output.path.write_text(text, encoding="utf-8")
                stored_outputs[self.placeholders.store(os.fspath(output.path))] = self.placeholders.store(text)
        observed = {"stdout": process.stdout or "", "stderr": process.stderr or ""}
        for stream, reduce in reducers.items():
            observed[stream] = reduce(observed[stream])
        invocation = _Invocation(
            label=label,
            argv=argv,
            inputs=inputs,
            returncode=process.returncode,
            streams={stream: self.placeholders.store(text) for stream, text in observed.items()},
            outputs=stored_outputs,
        )
        with self._lock:
            self._invocations[label] = invocation
        return subprocess.CompletedProcess(process.args, process.returncode, observed["stdout"], observed["stderr"])

    def _replay(
        self, label: str, argv: list[str], inputs: dict[str, str], outputs: Sequence[Path]
    ) -> subprocess.CompletedProcess[str]:
        entry = self._recorded.get(label)
        if entry is None:
            raise self._fail(f"has no recorded invocation {label}")
        if entry.get("argv") != argv:
            raise self._fail(
                f"invocation {label} was recorded for another argument vector: "
                f"recorded={entry.get('argv')}, requested={argv}"
            )
        if entry.get("inputs") != inputs:
            raise self._fail(
                f"invocation {label} input digests differ: "
                f"{describe_difference(entry.get('inputs'), inputs)}"
            )
        recorded_outputs = entry.get("outputs", {})
        requested_outputs = {self.placeholders.store(os.fspath(path)): path for path in outputs}
        if not set(recorded_outputs) <= set(requested_outputs):
            raise self._fail(
                f"invocation {label} recorded outputs {sorted(recorded_outputs)} "
                f"that were not requested: {sorted(requested_outputs)}"
            )
        for normalized, digest in recorded_outputs.items():
            text = self._stored_text(f"{label}.out.{normalized.rsplit('/', 1)[-1]}", digest)
            destination = requested_outputs[normalized]
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(self.placeholders.restore(text), encoding="utf-8")
        streams = {
            stream: self.placeholders.restore(self._stored_text(f"{label}.{stream}", entry.get(stream, "")))
            for stream in _STREAMS
        }
        returncode = entry.get("returncode")
        if not isinstance(returncode, int):
            raise self._fail(f"invocation {label} has no integer returncode")
        command = [self.placeholders.restore(argument) for argument in argv]
        return subprocess.CompletedProcess(command, returncode, streams["stdout"], streams["stderr"])

    def finish(self) -> str:
        """Complete the snapshot after every gate step passed; return a report line.

        Replay requires that every recorded invocation was requested.
        A refresh rewrites the directory from exactly the invocations that ran.
        """

        if not self.refresh:
            unused = sorted(set(self._recorded) - self._consumed)
            if unused:
                raise self._fail(f"recorded invocations were not requested: {unused}")
            return f"replayed {len(self._consumed)} recorded invocations from {self.name}"
        changed = self.write()
        state = "rewrote" if changed else "already matched"
        return f"refreshed {len(self._invocations)} invocations; {state} {self.name}"

    def render(self) -> dict[str, str]:
        """The complete refreshed directory as file name -> text."""

        files: dict[str, str] = {}
        entries = []
        for label in sorted(self._invocations):
            invocation = self._invocations[label]
            for name, text in invocation.stored_files().items():
                if name in files or name == MANIFEST:
                    raise GateError(f"reference snapshot file name {name} is produced twice")
                files[name] = text
            entries.append(invocation.manifest())
        manifest = {"schema": SCHEMA, "key": self.rendered_key, "invocation": entries}
        files[MANIFEST] = dump_manifest(manifest)
        return files

    def write(self) -> bool:
        """Replace the snapshot directory with the refreshed one; return whether it changed."""

        if not self.refresh:
            raise GateError("only a refresh can write a reference snapshot")
        files = {name: text.encode("utf-8") for name, text in self.render().items()}
        return replace_directory(self.directory, files)


def directory_files(directory: Path) -> dict[str, bytes]:
    """Every regular file below `directory` as relative path -> bytes."""

    if not directory.is_dir():
        return {}
    return {
        path.relative_to(directory).as_posix(): path.read_bytes()
        for path in directory.rglob("*") if path.is_file()
    }


def replace_directory(directory: Path, files: Mapping[str, bytes]) -> bool:
    """Make `directory` hold exactly `files`; return whether anything changed.

    The new contents are written beside it first and then renamed into place.
    """

    if directory_files(directory) == dict(files):
        return False
    staging = directory.with_name(f".{directory.name}.refresh")
    if staging.exists():
        shutil.rmtree(staging)
    for name, data in files.items():
        path = staging / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    if directory.exists():
        shutil.rmtree(directory)
    staging.rename(directory)
    return True


def snapshot_directory(committed: Path, refresh: bool, staging: Path | None) -> Path:
    """Where a helper opens its snapshot: the staging directory only for a staged refresh."""

    if staging is None:
        return committed
    if not refresh:
        raise GateError(f"{STAGING_OPTION} requires {REFRESH_OPTION}")
    return staging


@dataclass(frozen=True)
class Promotion:
    """A snapshot a child process refreshed into `staged`, promoted by the calling gate.

    `finish` has the same contract as `Snapshot.finish`: the gate calls it only
    after every step passed, and only then is the committed snapshot rewritten.
    """

    staged: Path
    committed: Path

    def finish(self) -> str:
        files = directory_files(self.staged)
        if MANIFEST not in files:
            raise GateError(f"the refreshed snapshot {self.staged} has no {MANIFEST}")
        changed = replace_directory(self.committed, files)
        try:
            name = self.committed.relative_to(ROOT).as_posix()
        except ValueError:
            name = os.fspath(self.committed)
        state = "rewrote" if changed else "already matched"
        return f"promoted a child refresh; {state} {name}"


def describe_difference(recorded: Any, current: Any) -> str:
    """Name the top-level entries that differ between two manifest tables."""

    if not isinstance(recorded, dict) or not isinstance(current, dict):
        return f"recorded={json.dumps(recorded, sort_keys=True)}, current={json.dumps(current, sort_keys=True)}"
    names = sorted(set(recorded) | set(current))
    parts = []
    for name in names:
        if recorded.get(name) != current.get(name):
            parts.append(
                f"{name}: recorded={json.dumps(recorded.get(name), sort_keys=True)}, "
                f"current={json.dumps(current.get(name), sort_keys=True)}"
            )
    return "; ".join(parts) or "none"


_BARE_KEY = re.compile(r"^[A-Za-z0-9_-]+$")


def _key(name: str) -> str:
    return name if _BARE_KEY.match(name) else json.dumps(name, ensure_ascii=False)


def _value(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return "[" + ", ".join(_value(item) for item in value) + "]"
    raise GateError(f"the snapshot manifest cannot spell {value!r}")


def _table(header: str, values: Mapping[str, Any]) -> list[str]:
    lines = [header] if header else []
    lines.extend(f"{_key(name)} = {_value(value)}" for name, value in values.items() if not isinstance(value, dict))
    return lines


def dump_manifest(manifest: Mapping[str, Any]) -> str:
    """Spell a manifest as deterministic TOML: scalars, string lists, and one array of tables.

    Nested tables keep the order of their mapping, which the snapshot already sorts.
    """

    sections = ["\n".join(_table("", {"schema": manifest["schema"]}))]
    key = manifest["key"]
    sections.append("\n".join(_table("[key]", key)))
    for name, value in key.items():
        if isinstance(value, dict):
            sections.append("\n".join(_table(f"[key.{_key(name)}]", value)))
    for entry in manifest["invocation"]:
        block = _table("[[invocation]]", entry)
        for name, value in entry.items():
            if isinstance(value, dict):
                block.append("")
                block.extend(_table(f"[invocation.{_key(name)}]", value))
        sections.append("\n".join(block))
    return "\n\n".join(sections) + "\n"
