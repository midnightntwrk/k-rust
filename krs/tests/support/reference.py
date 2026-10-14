"""Reference-K results: a per-user cache of reduced Java K evidence, pinned by digest.

A reference-K (Java K) invocation is a function of the K release, the tool, its
argument vector, the upstream revisions it reads, and the bytes of its inputs.
None of these change between ordinary gate runs, so a gate replays a stored
result instead of running Java K again. A stored result is a cache entry that
any run with the pinned K tools can regenerate, not repository content.

A snapshot is the evidence of the invocations one gate step runs together,
spelled as a directory whose `manifest.toml` holds the key and the digest of
every stored file:

- the key: the K version from `Krs.lock`, the K tool names the snapshot may
  run, the upstream revisions it reads, and the digests of its declared input
  files (fixtures, corpora, and the files they `require`);
- one `[[invocation]]` table per tool run: a label, the argument vector, the
  digest of every regular file the argument vector names (so a KRS-emitted
  `.k` or `spec.k` is keyed by its digest), the exit status, the standard
  stream digests, and the digests of the declared output files the
  comparators read.

A declared output, and either standard stream, may name a reducer that
removes what no comparator reads, or what varies between runs of the same
invocation, before it is stored. A live run hands the comparators the reduced
text too, so live and replayed runs check the same evidence.
`json_without_members` removes named object members, such as source-location
attributes, from a JSON file; `indented_json` spells a JSON document one member
per line so a stored proof result or claim reads and diffs as text;
`substitute` rewrites a regular expression.
Before any of these, a live run applies `reduce_run_dependent_text` to both
streams of every invocation: the K tools themselves print text that differs
between runs of one invocation (the number before each `kore-exec` log line,
the temporary directory and files of a shell-wrapped tool such as `krun`, the
places where such a tool folds an error message that names those paths, and
the suffix K's frontend gives a generated `#lambda` label), so no snapshot that
records it could be reproduced.
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

The SHA-256 of `manifest.toml` names the whole snapshot, because the manifest
holds the digest of every other file. A gate pins it in its ledger table
`reference_sha256` (an output pin that `--record` rewrites), and the cache
stores the snapshot under it:

    ${XDG_CACHE_HOME:-~/.cache}/krs/reference-outputs/v1/entries/<first two digits>/<digest>/

`KRS_REFERENCE_CACHE_DIR` names another store directory; it must not lie in
the repository. The store belongs to one Unix user. An entry unused for
`KRS_REFERENCE_CACHE_MAX_UNUSED_DAYS` (30) days is deleted, at most once a day.

A gate opens a snapshot in one of three ways:

- hit: the cache holds a valid entry under the pinned digest. The entry's key
  must equal the current key, each requested invocation must have been
  recorded with the same argument vector and input digests, and every recorded
  invocation must be requested exactly once. Any difference fails closed: the
  pinned evidence no longer describes what the gate runs, which only an
  intended change explains, and `--refresh-reference --record` re-records it.
  A hit never falls back to running Java K and needs no K tool;
- miss: no digest is pinned, or the cache holds no valid entry under it. The
  pinned K tools run live, located on the first invocation; a missing tool
  fails closed and says how to provide one;
- refresh (`--refresh-reference`): the K tools run live whatever the cache holds.

A live run is complete only when `Snapshot.finish` is called, which a gate
does after every step passed. The digest of its manifest must equal the pin
(with `--record` it becomes the pin), so a different or nondeterministic K
installation fails instead of replacing the evidence; only then is the entry
written, to a temporary directory in the store that is renamed into place.
A failing run therefore stores nothing.

`--refresh-reference` is distinct from `--record`: `--record` rewrites output
pins in a gate ledger, including `reference_sha256`, and `--refresh-reference`
reruns the K tools instead of replaying the cache. A gate accepts both together.

A gate that runs a snapshot-backed helper as a child process passes it
`--reference-staging DIR` and `--reference-sha256 DIGEST` (the pinned digest):
the helper writes its finished snapshot, replayed or live, to the staging
directory, and the gate's `Promotion` checks it against the pin and stores it
only after every one of its own steps passed.
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
import tempfile
import threading
import time
import tomllib
from typing import Any, Callable, Mapping, Sequence

from support import ROOT, GateError
from support.hashing import sha256_bytes, sha256_file, sha256_text
from support.lock import k_version
from support.pins import Ledger
from support.process import run
from support.tools import install_k_advice, k_tool


SCHEMA = 1
MANIFEST = "manifest.toml"
PIN_TABLE = "reference_sha256"
"""The ledger table in which a gate pins the manifest digest of each of its snapshots."""
CACHE_VARIABLE = "KRS_REFERENCE_CACHE_DIR"
CACHE_LAYOUT = "v1"
MAX_UNUSED_VARIABLE = "KRS_REFERENCE_CACHE_MAX_UNUSED_DAYS"
DEFAULT_MAX_UNUSED_DAYS = 30.0
PRUNE_INTERVAL_SECONDS = 86400.0
REFRESH_OPTION = "--refresh-reference"
STAGING_OPTION = "--reference-staging"
DIGEST_OPTION = "--reference-sha256"
CHANGE_ADVICE = (
    f"if the change is intended, run the gate with {REFRESH_OPTION} --record "
    "(with the pinned K tools) to re-record it"
)
_LABEL = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._@+-]*(/[A-Za-z0-9][A-Za-z0-9._@+-]*)*$")
_DIGEST = re.compile(r"^[0-9a-f]{64}$")
_STREAMS = ("stdout", "stderr")


def add_refresh_argument(parser: argparse.ArgumentParser) -> None:
    """Add the `--refresh-reference` option every snapshot-backed gate shares."""

    parser.add_argument(
        REFRESH_OPTION,
        dest="refresh_reference",
        action="store_true",
        help=(
            "run the pinned Java K tools live instead of replaying the reference cache; "
            "the results are stored only if every step passes"
        ),
    )


def add_child_arguments(parser: argparse.ArgumentParser) -> None:
    """Add the options a gate passes to a snapshot-backed helper it runs as a child process."""

    parser.add_argument(
        STAGING_OPTION,
        dest="reference_staging",
        type=Path,
        help="write the finished snapshot to this directory for the calling gate to check and store",
    )
    parser.add_argument(
        DIGEST_OPTION,
        dest="reference_sha256",
        help="the manifest digest the calling gate pins, which names the cache entry to replay",
    )


def child_arguments(staging: Path, pin: "Pin", refresh: bool) -> list[str]:
    """The arguments that let a child process replay or run the snapshot `pin` names."""

    expected = pin.value()
    return [
        STAGING_OPTION, os.fspath(staging),
        *([DIGEST_OPTION, expected] if expected else []),
        *([REFRESH_OPTION] if refresh else []),
    ]


def live_tools(names: Sequence[str]) -> dict[str, str]:
    """Locate each named K tool and require the `Krs.lock` K version.

    Only a live run calls this; a cache hit needs no K tool.
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


# upstream k/run-dependent-output-text covers this and the reducers below that remove
# run-dependent Java K text: k-util temp names, fold -s breaks, kprove temp
# directories, and KORE import order.
reduce_kore_exec_log = substitute(r"(?m)^kore-exec: \[\d+\]", "kore-exec: [-]")
"""kore-exec prefixes each log line with a run-dependent number; no comparator reads it."""

_K_UTIL_TEMP = re.compile(r"[^\s'\"]*/\.(k[a-z]*)-[0-9]{4}(?:-[0-9]{2}){5}-[A-Za-z0-9]{10}(?![A-Za-z0-9])")
_K_UTIL_TEMP_FILE = re.compile(r"(\.k[a-z]*-TEMP/tmp\.(?:[^\s/'\"]+\.)?)[A-Za-z0-9]{10}(?![A-Za-z0-9])")


def reduce_k_util_temp(text: str) -> str:
    """Replace the temporary directory, and the `mktemp` files in it, of a shell-wrapped K tool.

    K's `k-util.sh` creates `<TMPDIR>/.<tool>-<date and time>-XXXXXXXXXX` for
    each run of a tool such as `krun`, which names it and its
    `tmp.<kind>.XXXXXXXXXX` files in an error message; the directory becomes
    `TMPDIR/.<tool>-TEMP` and each file `tmp.<kind>.TEMP`.
    """

    text = _K_UTIL_TEMP.sub(lambda match: f"TMPDIR/.{match.group(1)}-TEMP", text)
    return _K_UTIL_TEMP_FILE.sub(lambda match: f"{match.group(1)}TEMP", text)


# upstream k/resolvefun-lambda-label-nondeterminism
_K_LAMBDA = re.compile(r"(#lambda[^\s()`'\"]*_)[0-9]*(?![A-Za-z0-9_])")


def reduce_lambda_suffixes(text: str) -> str:
    """Replace the suffix of every generated `#lambda<hint1>_<hint2>_<n>` label with `N`.

    K's `ResolveFun` numbers the lambdas that share both hints in an order
    that depends on hashes of the sentences, source paths included, so one
    definition kompiled from different checkouts names a lambda differently;
    its warnings and `krun`'s output of a stuck lambda application print that
    name. A label
    whose hint contains a parenthesis or quote is left as it is; a stored KORE
    definition is renumbered by `krs-gate kore-canonicalize` instead.
    """

    return _K_LAMBDA.sub(r"\1N", text)


_K_UTIL_ERROR = re.compile(r"\[Error\] (?:krun|kparse|kparse-gen|kore-print): ")
_K_UTIL_FOLD_WIDTH = 80
_BLANKS = " \t"


def _fold_columns(segment: str) -> int:
    """The column `fold` reaches at the end of `segment`, counting UTF-8 bytes as `fold` does."""

    column = 0
    for character in segment:
        if character == "\t":
            column += 8 - column % 8
        elif character == "\b":
            column = max(column - 1, 0)
        elif character == "\r":
            column = 0
        else:
            column += len(character.encode("utf-8"))
    return column


def _fold_break(segment: str, following: str) -> bool:
    """Whether `fold -s` ended `segment` only because `following` did not fit beside it.

    `fold -s -w 80` breaks a line after its last blank when the next word
    would pass column 80, and inside a word only when the 80 columns hold no
    blank; either way it inserts nothing but the newline.
    """

    if not following or following[0] in _BLANKS:
        return False
    columns = _fold_columns(segment)
    if columns > _K_UTIL_FOLD_WIDTH:
        return False
    if segment.endswith(tuple(_BLANKS)):
        word = re.match(r"[^ \t]*", following)
        assert word is not None
        return columns + _fold_columns(word.group()) >= _K_UTIL_FOLD_WIDTH
    return columns == _K_UTIL_FOLD_WIDTH and not any(blank in segment for blank in _BLANKS)


# upstream k/run-dependent-output-text
def unfold_k_util_errors(text: str) -> str:
    """Rejoin the lines `fold -s` split in an error message of a shell-wrapped K tool.

    K's `k-util.sh` pipes each `[Error] <tool>: <message>` of `krun`, `kparse`,
    `kparse-gen`, and `kore-print` through `fold -s` at 80 columns. A failed
    command is reported as its argument vector, whose paths (the gate
    workspace, `TMPDIR`) have run-dependent lengths, so the breaks move from
    run to run even after the paths themselves are reduced. Rejoining makes
    each message one line again; it must see the text before any path is
    replaced, because the breaks depend on the original lengths.
    """

    lines = text.split("\n")
    joined: list[str] = []
    index = 0
    while index < len(lines):
        line = segment = lines[index]
        if _K_UTIL_ERROR.match(line):
            while index + 1 < len(lines) and _fold_break(segment, lines[index + 1]):
                index += 1
                segment = lines[index]
                line += segment
        joined.append(line)
        index += 1
    return "\n".join(joined)


def reduce_run_dependent_text(text: str) -> str:
    """Remove the text that a K tool prints differently on each run of one invocation.

    A live run applies it to both streams of every invocation before the
    invocation's own reducers: `unfold_k_util_errors` (first, while the
    original path lengths are still visible), `reduce_kore_exec_log`,
    `reduce_k_util_temp`, and `reduce_lambda_suffixes`.
    """

    text = unfold_k_util_errors(text)
    return reduce_lambda_suffixes(reduce_k_util_temp(reduce_kore_exec_log(text)))


# upstream k/run-dependent-output-text
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


# upstream k/run-dependent-output-text
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


def reduce_kore_definition(text: str) -> str:
    """A reducer for a kompiled `definition.kore` that `krs-gate kore-compare` reads.

    It replaces K's install path, sorts each run of `import` lines, and
    renumbers the generated `_Gen` variables of each sentence; K writes the
    last two in a run-dependent order, and the comparator reads sentences as an
    alpha-normalized multiset.
    """

    return renumbered_kore_generated_variables(sorted_kore_imports(reduce_store_paths(text)))


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



def cache_root(environ: Mapping[str, str] = os.environ) -> Path:
    """The store directory: `KRS_REFERENCE_CACHE_DIR`, or the per-user default.

    The default is `${XDG_CACHE_HOME:-~/.cache}/krs/reference-outputs/v1`.
    A store inside the repository is refused, so an entry is never committed.
    """

    explicit = environ.get(CACHE_VARIABLE)
    if explicit:
        root = Path(explicit).expanduser()
    else:
        base = environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
        root = Path(base) / "krs" / "reference-outputs" / CACHE_LAYOUT
    root = root.absolute()
    resolved = root.resolve()
    if resolved == ROOT or ROOT in resolved.parents:
        raise GateError(f"the reference cache {root} is inside the repository; set {CACHE_VARIABLE} to a directory outside it")
    return root


def max_unused_seconds(environ: Mapping[str, str] = os.environ) -> float:
    value = environ.get(MAX_UNUSED_VARIABLE, "")
    try:
        days = float(value) if value else DEFAULT_MAX_UNUSED_DAYS
    except ValueError as error:
        raise GateError(f"{MAX_UNUSED_VARIABLE} must be a number of days: {value!r}") from error
    if not days > 0:
        raise GateError(f"{MAX_UNUSED_VARIABLE} must be positive: {value!r}")
    return days * 86400.0


def manifest_files(manifest: Mapping[str, Any]) -> dict[str, str]:
    """Every file a snapshot directory holds besides its manifest, as name -> digest.

    An empty standard stream is not stored. Raises `ValueError` for a
    malformed manifest.
    """

    if manifest.get("schema") != SCHEMA:
        raise ValueError(f"has schema {manifest.get('schema')!r}, not {SCHEMA}")
    invocations = manifest.get("invocation", [])
    if not isinstance(invocations, list):
        raise ValueError("manifest invocation is not an array of tables")
    files: dict[str, str] = {}
    labels: set[str] = set()
    for entry in invocations:
        label = entry.get("label") if isinstance(entry, dict) else None
        if not isinstance(label, str) or not _LABEL.match(label) or label in labels:
            raise ValueError(f"manifest invocation label {label!r} is missing, invalid, or repeated")
        labels.add(label)
        for stream in _STREAMS:
            digest = entry.get(stream)
            if not isinstance(digest, str):
                raise ValueError(f"invocation {label} has no {stream} digest")
            if digest != sha256_text(""):
                files[f"{label}.{stream}"] = digest
        outputs = entry.get("outputs", {})
        if not isinstance(outputs, dict):
            raise ValueError(f"invocation {label} outputs are not a table")
        for path, digest in outputs.items():
            files[f"{label}.out.{path.rsplit('/', 1)[-1]}"] = digest
    return files


def snapshot_problem(files: Mapping[str, bytes]) -> str | None:
    """Why a snapshot directory, as name -> bytes, is not complete and intact, or None."""

    data = files.get(MANIFEST)
    if data is None:
        return f"has no {MANIFEST}"
    try:
        expected = manifest_files(tomllib.loads(data.decode("utf-8")))
    except (UnicodeError, tomllib.TOMLDecodeError, ValueError) as error:
        return f"has an unreadable manifest: {error}"
    actual = set(files) - {MANIFEST}
    if actual != set(expected):
        return (
            f"files differ from the manifest: unexpected={sorted(actual - set(expected))}, "
            f"missing={sorted(set(expected) - actual)}"
        )
    for name, digest in sorted(expected.items()):
        if sha256_bytes(files[name]) != digest:
            return f"{name} differs from its manifest digest"
    return None


@dataclass(frozen=True)
class Entry:
    """A valid cache entry: its directory, its manifest digest, and the parsed manifest."""

    directory: Path
    digest: str
    manifest: Mapping[str, Any]


class Cache:
    """The per-user store of snapshots, each under the SHA-256 of its manifest."""

    def __init__(self, root: Path | None = None) -> None:
        self.root = root if root is not None else cache_root()

    def entry_path(self, digest: str) -> Path:
        return self.root / "entries" / digest[:2] / digest

    def load(self, digest: str | None) -> Entry | None:
        """The valid entry stored under `digest`, or None; a hit marks the entry used."""

        if not digest or not _DIGEST.match(digest):
            return None
        directory = self.entry_path(digest)
        files = directory_files(directory)
        if MANIFEST not in files or sha256_bytes(files[MANIFEST]) != digest or snapshot_problem(files):
            return None
        try:
            os.utime(directory)
        except OSError:
            pass
        return Entry(directory, digest, tomllib.loads(files[MANIFEST].decode("utf-8")))

    def holds(self, digest: str | None) -> bool:
        return self.load(digest) is not None

    def store(self, files: Mapping[str, bytes]) -> str:
        """Store a complete snapshot under its manifest digest and return the digest.

        The files are written to a new directory below the store's `tmp/` and
        renamed into place, so an interrupted store leaves no partial entry.
        An existing valid entry is kept: equal digests mean equal contents.
        """

        problem = snapshot_problem(files)
        if problem:
            raise GateError(f"refusing to store an incomplete reference snapshot: it {problem}")
        digest = sha256_bytes(files[MANIFEST])
        if self.load(digest) is not None:
            return digest
        temporary_root = self.root / "tmp"
        temporary_root.mkdir(parents=True, exist_ok=True)
        staging = Path(tempfile.mkdtemp(prefix=f".{digest[:12]}.", dir=temporary_root))
        try:
            for name, data in files.items():
                path = staging / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            final = self.entry_path(digest)
            final.parent.mkdir(parents=True, exist_ok=True)
            if final.exists():
                # An invalid entry under this digest is replaced.
                stale = final.with_name(f".{digest}.stale.{os.getpid()}.{time.time_ns()}")
                os.rename(final, stale)
                shutil.rmtree(stale, ignore_errors=True)
            try:
                os.rename(staging, final)
            except OSError:
                # Another process stored the same digest first.
                if self.load(digest) is None:
                    raise
        finally:
            if staging.exists():
                shutil.rmtree(staging, ignore_errors=True)
        self.prune()
        return digest

    def prune(self, *, force: bool = False) -> int:
        """Delete entries unused for the maximum unused age, at most once a day; return the count."""

        stamp = self.root / "last-prune"
        now = time.time()
        try:
            if not force and stamp.exists() and now - stamp.stat().st_mtime < PRUNE_INTERVAL_SECONDS:
                return 0
            self.root.mkdir(parents=True, exist_ok=True)
            stamp.touch()
        except OSError:
            return 0
        limit = max_unused_seconds()
        removed = 0
        for directory in sorted((self.root / "entries").glob("*/*")):
            try:
                unused = now - directory.stat().st_mtime
            except OSError:
                continue
            if directory.is_dir() and unused > limit:
                shutil.rmtree(directory, ignore_errors=True)
                removed += 1
        for directory in sorted((self.root / "tmp").glob("*")):
            try:
                if now - directory.stat().st_mtime > PRUNE_INTERVAL_SECONDS:
                    shutil.rmtree(directory, ignore_errors=True)
            except OSError:
                continue
        return removed


@dataclass(frozen=True)
class Pin:
    """Where a gate pins one snapshot's manifest digest: `ledger[PIN_TABLE][name]`."""

    ledger: Ledger
    name: str

    def value(self) -> str | None:
        pinned = self.ledger.get(PIN_TABLE)
        value = pinned.get(self.name) if isinstance(pinned, dict) else None
        return value if isinstance(value, str) else None

    def expect(self, digest: str) -> None:
        self.ledger.expect((PIN_TABLE, self.name), digest)

    def describe(self) -> str:
        return f"{self.ledger.path.name} {PIN_TABLE}.{self.name}"


def entry_difference(cache: Cache, expected: str | None, manifest: Mapping[str, Any]) -> str:
    """Name what differs between the cached entry `expected` and a measured manifest."""

    entry = cache.load(expected)
    if entry is None:
        return "the pinned entry is not in the reference cache, so the differing invocations are unknown"
    parts = []
    if entry.manifest.get("key") != manifest.get("key"):
        parts.append(f"key: {describe_difference(entry.manifest.get('key'), manifest.get('key'))}")
    recorded = {item["label"]: item for item in entry.manifest.get("invocation", [])}
    measured = {item["label"]: item for item in manifest.get("invocation", [])}
    labels = sorted(label for label in set(recorded) | set(measured) if recorded.get(label) != measured.get(label))
    if labels:
        parts.append(f"invocations {labels[:8]}{' and more' if len(labels) > 8 else ''}")
    return "; ".join(parts) or "nothing but the manifest spelling"


def check_pin(cache: Cache, pin: Pin | None, expected: str | None, digest: str, manifest: Mapping[str, Any], name: str) -> None:
    """Compare a measured snapshot digest with its pin, or keep it under `--record`."""

    if pin is None:
        return
    if not pin.ledger.record and expected is not None and digest != expected:
        raise GateError(
            f"reference snapshot {name}: the measured K evidence {digest} differs from its pin "
            f"{pin.describe()}={expected} ({entry_difference(cache, expected, manifest)}); "
            "a different or nondeterministic K installation produced it, or a reference input changed; "
            "if the change is intended, run the gate with --record"
        )
    pin.expect(digest)


class Snapshot:
    """One snapshot, replayed from the reference cache or run live."""

    def __init__(
        self,
        name: str,
        key: Key,
        *,
        workspace: Path,
        refresh: bool,
        pin: Pin | None = None,
        expected: str | None = None,
        staging: Path | None = None,
        tools: Callable[[], Mapping[str, str]] | None = None,
        cache: Cache | None = None,
    ) -> None:
        """Open the snapshot `name`; a hit checks the entry's key now and fails closed.

        `pin` names the gate ledger entry that holds the manifest digest;
        a helper run as a child process gets the digest as `expected` and
        writes its finished snapshot to `staging` instead of the cache.
        `tools` locates the K tools of a live run (default `live_tools` for
        the key's tools); it is called once, on the first live invocation.
        """

        self.name = name
        self.key = key
        self.pin = pin
        self.expected = pin.value() if pin is not None else expected
        self.staging = staging
        self.cache = cache if cache is not None else Cache()
        self.placeholders = Placeholders(workspace)
        self.rendered_key = key.render()
        self._tools = tools
        self._executables: dict[str, str] | None = None
        self._tool_error: GateError | None = None
        self._lock = threading.Lock()
        self._tools_lock = threading.Lock()
        self._invocations: dict[str, _Invocation] = {}
        self._recorded: dict[str, dict[str, Any]] = {}
        self._consumed: set[str] = set()
        self.entry: Entry | None = None
        if refresh:
            self.mode, self.reason = "refresh", f"{REFRESH_OPTION} runs the K tools live"
        else:
            self.entry = self.cache.load(self.expected)
            if self.entry is not None:
                self.mode, self.reason = "hit", f"replays the reference cache entry {self.expected}"
                self._load(self.entry)
            elif self.expected is None:
                self.mode, self.reason = "miss", "no reference digest is pinned for it"
            else:
                self.mode = "miss"
                self.reason = f"the reference cache {self.cache.root} holds no entry {self.expected}"

    @property
    def live(self) -> bool:
        """Whether the K tools run live (a miss or a refresh) rather than replay."""

        return self.mode != "hit"

    def _fail(self, problem: str) -> GateError:
        return GateError(f"reference snapshot {self.name}: {problem}; {CHANGE_ADVICE}")

    def _load(self, entry: Entry) -> None:
        recorded_key = entry.manifest.get("key")
        if recorded_key != self.rendered_key:
            raise self._fail(
                f"the pinned entry {entry.digest} was recorded for another key: "
                f"{describe_difference(recorded_key, self.rendered_key)}"
            )
        for item in entry.manifest.get("invocation", []):
            self._recorded[item["label"]] = item

    def _stored_text(self, name: str, digest: str) -> str:
        if digest == sha256_text(""):
            return ""
        assert self.entry is not None
        text = (self.entry.directory / name).read_text(encoding="utf-8")
        if sha256_text(text) != digest:
            raise GateError(f"reference cache entry {self.entry.directory}: {name} changed while it was replayed")
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

    def _live_executables(self) -> Mapping[str, str]:
        """Locate the K tools once, on the first live invocation, or fail closed."""

        with self._tools_lock:
            if self._tool_error is not None:
                raise self._tool_error
            if self._executables is None:
                try:
                    found = dict(self._tools() if self._tools is not None else live_tools(self.key.tools))
                    missing = sorted(set(self.key.tools) - set(found))
                    if missing:
                        raise GateError(f"the K tools {', '.join(missing)} are unavailable; {install_k_advice()}")
                except GateError as error:
                    self._tool_error = GateError(
                        f"reference snapshot {self.name}: {self.reason}, so its K invocations must run live: {error}"
                    )
                    raise self._tool_error from error
                self._executables = found
            return self._executables

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
        stdin: Path | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """Run or replay one K tool invocation and return its completed process.

        `outputs` names the files the tool writes that a comparator reads;
        they are stored (reduced, when an `Output` names a reducer), and
        replay writes the stored text back to the same paths.
        `prefix` names a wrapper command (such as `timeout`) and its options;
        its first element is resolved on PATH only in a live run.
        `streams` maps `stdout` or `stderr` to a reducer applied before storing,
        after `reduce_run_dependent_text`, which a live run applies to both.
        `stdin` names a file fed to the tool's standard input; its digest is an
        input of the invocation, recorded under `<stdin>`.
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
        if stdin is not None:
            inputs["<stdin>"] = sha256_file(stdin)
        with self._lock:
            # The label is reserved before a live run starts, so two
            # concurrent runs cannot both record under it.
            if label in self._consumed:
                raise GateError(f"reference invocation label {label} is used twice")
            self._consumed.add(label)
        if not self.live:
            return self._replay(label, argv, inputs, [output.path for output in declared])
        executable = self._live_executables()[tool]
        return self._run_live(
            label, executable, resolved, argv, inputs, timeout, declared, prefix, reducers,
            stdin=stdin,
        )

    def _run_live(
        self,
        label: str,
        executable: str,
        resolved: list[str],
        argv: list[str],
        inputs: dict[str, str],
        timeout: float,
        outputs: Sequence[Output],
        prefix: Sequence[str],
        reducers: Mapping[str, Callable[[str], str]],
        *,
        stdin: Path | None = None,
    ) -> subprocess.CompletedProcess[str]:
        command = list(prefix)
        if command:
            wrapper = shutil.which(command[0])
            if wrapper is None:
                raise GateError(f"the wrapper command {command[0]} is unavailable")
            command[0] = wrapper
        command = [*command, executable, *resolved]
        process = run(
            command, timeout=timeout, check=False,
            input=stdin.read_text(encoding="utf-8") if stdin is not None else None,
        )
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
        observed = {
            "stdout": reduce_run_dependent_text(process.stdout or ""),
            "stderr": reduce_run_dependent_text(process.stderr or ""),
        }
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
            raise self._fail(f"the pinned entry has no recorded invocation {label}")
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

        A hit requires that every recorded invocation was requested. A live
        run checks its manifest digest against the pin and only then stores
        the snapshot in the cache, or in the staging directory of a child.
        """

        if not self.live:
            assert self.entry is not None
            unused = sorted(set(self._recorded) - self._consumed)
            if unused:
                raise self._fail(f"recorded invocations were not requested: {unused}")
            if self.pin is not None:
                self.pin.expect(self.entry.digest)
            if self.staging is not None:
                replace_directory(self.staging, directory_files(self.entry.directory))
            return f"{self.name}: replayed {len(self._consumed)} invocations from the reference cache entry {self.entry.digest[:12]}"
        files = {name: text.encode("utf-8") for name, text in self.render().items()}
        digest = sha256_bytes(files[MANIFEST])
        manifest = tomllib.loads(files[MANIFEST].decode("utf-8"))
        check_pin(self.cache, self.pin, self.expected, digest, manifest, self.name)
        if self.staging is not None:
            replace_directory(self.staging, files)
            stored = f"staged {digest[:12]} for the calling gate"
        else:
            self.cache.store(files)
            stored = f"stored the reference cache entry {digest[:12]}"
        return f"{self.name}: ran {len(self._invocations)} invocations live ({self.reason}); {stored}"

    def render(self) -> dict[str, str]:
        """The complete snapshot of a live run as file name -> text."""

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


@dataclass(frozen=True)
class Promotion:
    """A snapshot a child process finished into `staged`, checked and stored by the calling gate.

    `finish` has the same contract as `Snapshot.finish`: the gate calls it only
    after every step passed, and only then is the snapshot stored in the cache.
    """

    staged: Path
    name: str
    pin: Pin
    cache: Cache | None = None

    def finish(self) -> str:
        cache = self.cache if self.cache is not None else Cache()
        files = directory_files(self.staged)
        problem = snapshot_problem(files)
        if problem:
            raise GateError(f"the child's reference snapshot {self.name} in {self.staged} {problem}")
        digest = sha256_bytes(files[MANIFEST])
        manifest = tomllib.loads(files[MANIFEST].decode("utf-8"))
        check_pin(cache, self.pin, self.pin.value(), digest, manifest, self.name)
        cache.store(files)
        return f"{self.name}: checked the child's snapshot against its pin; the reference cache holds entry {digest[:12]}"


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
