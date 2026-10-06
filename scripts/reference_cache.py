#!/usr/bin/env python3
"""Content-addressed cache of pinned reference-K tool results.

A reference tool invocation (kompile, krun, kast, kprove, kprint, kore-parser, kore-exec, or a
conformance recipe that runs them) is a function of the reference installation, its argument
vector, its semantic environment, and the bytes it reads. When none of those changed, rerunning
it reproduces its result, so the gates may replay a stored result instead. The cache sits below
the gates: krust always runs, every comparison always runs, and the pin checks always run before
any lookup. A hit hands the gate the exit status, the standard streams, and every file the tool
created, changed, or deleted under its declared output roots, restored byte for byte from an
entry whose manifest digests are checked first.

The key is the SHA-256 of a canonical JSON preimage that is stored in the entry and compared on
every hit. It holds the schema, the manifest pins, the tool identity, the argument vector and
working directory with per-run scratch prefixes replaced by placeholders, the semantic
environment, the stdin digest, the digests of declared inputs, the pre-state digest of every
output root, and, for kompile and kprove, the digests of the `kdep` requires closure (looked up in
direct mode, as ccache does: a closure recorded on a miss is re-hashed on lookup). The closure is
computed and hashed before the tool runs and checked again after it, and the index also records
every absent path at which a new file could change what a `requires` name resolves to; a lookup
misses when any of them exists.

Modes (REFERENCE_CACHE): `off` runs the tool; `on` replays a valid entry younger than the maximum
age and stores a miss; `refresh` runs and overwrites; `verify` runs the tool when an entry exists
and reports a difference from the stored result beyond the reference's own run-to-run variation
(ReferenceCache._verify). The default is `on`, except under CI=true (no persistent cache there, so
the result is the uncached behaviour) and under REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED=1 (no pins,
so no valid key).

Results that are never stored: timeouts, signal deaths, outputs that look like a reference crash
or resource exhaustion, any result under the RLIMIT_AS fallback guard other than a successful
non-LLVM run, results whose closure could not be computed, and results whose inputs changed
while the tool ran.

The command-line interface is used by the shell gates (scripts/reference-cache.sh); the Python
interface by the conformance driver (scripts/conformance/run.py).
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import shutil
import socket
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

SCHEMA = "k-rust-reference-outputs-v1"
MODES = ("off", "on", "refresh", "verify")
DEFAULT_MAX_AGE_DAYS = 14.0
NIX_STORE = "/nix/store/"
PRUNE_INTERVAL_SECONDS = 86400
# Files younger than this are re-hashed instead of trusted from the in-process digest memo, so a
# write within the file system's timestamp granularity cannot hide behind an unchanged mtime.
DIGEST_MEMO_MIN_AGE_SECONDS = 2.0
# Environment variables that change what a reference tool computes or prints. Memory, heap,
# thread-count and guard settings are resource settings and are recorded as metadata only.
SEMANTIC_ENVIRONMENT = ("GHCRTS", "LANG", "LC_ALL", "LC_CTYPE", "LC_MESSAGES", "TZ")
# JVM system properties in K_OPTS that only size the Scala thread pools.
RESOURCE_PROPERTIES = (
    "scala.concurrent.context.numThreads",
    "scala.concurrent.context.maxThreads",
    "scala.concurrent.context.minThreads",
)
# A superset of the conformance driver's crash classifier: a result that ran out of a resource
# describes the machine, not the reference semantics, and must be recomputed.
RESOURCE_FAILURE = re.compile(
    r"panicked|outofmemory|out of memory|stackoverflow|stack overflow|segmentation fault|"
    r"failed to create.*thread|unable to create native thread|cannot allocate memory|"
    r"backend crashed|core dumped|\bkilled\b",
    re.I,
)
# Options of kompile and kprove that take a value, so the closure computation can find the
# source positional. Unknown options are assumed to be flags; a misparse makes the closure
# computation fail, and the result is then simply not stored.
VALUE_OPTIONS = {
    "--backend", "--main-module", "--syntax-module", "--output-definition", "-o", "--md-selector",
    "-I", "--hook-namespaces", "--type-inference-mode", "--post-process", "--top-cell",
    "--profile-rule-parsing", "--bison-stack-max-depth", "--llvm-kompile-type",
    "--llvm-kompile-output", "-ccopt", "-w", "--warnings", "-W", "-Wno", "-d", "--directory",
    "--definition", "-O", "--concrete-rules", "--smt-prelude", "--llvm-kompile-flags",
    "--spec-module", "--def-module", "--smt", "--smt-timeout", "--branching-allowed", "--depth",
    "--claim", "--claims", "--exclude", "--trusted", "--debug-script", "--max-counterexamples",
    "--output", "--output-file", "--save-directory", "--haskell-backend-command",
    "--kore-exec-command", "--log-level", "--temp-dir", "--emit-json-spec",
}


class CacheError(Exception):
    """A condition that makes one invocation uncacheable; the tool still runs."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def truthy(value: str | None) -> bool:
    return value not in (None, "", "0", "false", "False", "FALSE", "no")


def resolve_mode(environ=os.environ) -> tuple[str, str]:
    """The cache mode and why it was chosen."""
    requested = environ.get("REFERENCE_CACHE", "")
    if requested and requested not in MODES:
        raise ValueError(f"REFERENCE_CACHE must be one of {', '.join(MODES)}: {requested}")
    if environ.get("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "0") == "1":
        return "off", "REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED=1 skips the pins every key needs"
    if requested:
        return requested, "REFERENCE_CACHE"
    if truthy(environ.get("CI")):
        return "off", "CI=true and REFERENCE_CACHE unset: CI keeps no cache between runs"
    return "on", "default"


def cache_root(environ=os.environ) -> Path:
    explicit = environ.get("REFERENCE_CACHE_DIR")
    if explicit:
        return Path(explicit)
    base = environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
    return Path(base) / "k-rust" / "reference-outputs" / "v1"


def max_age_seconds(environ=os.environ) -> float:
    value = environ.get("REFERENCE_CACHE_MAX_AGE_DAYS", "")
    days = float(value) if value else DEFAULT_MAX_AGE_DAYS
    if not days > 0:
        raise ValueError("REFERENCE_CACHE_MAX_AGE_DAYS must be positive")
    return days * 86400.0


def k_opts_semantics(k_opts: str) -> list[str]:
    """The JVM system properties of K_OPTS other than thread-pool sizing."""
    kept = []
    for token in k_opts.split():
        if not token.startswith("-D"):
            continue
        name = token[2:].split("=", 1)[0]
        if name not in RESOURCE_PROPERTIES:
            kept.append(token)
    return kept


# --- file digests -------------------------------------------------------------------------------

_digest_memo: dict[tuple[int, int, int, int], str] = {}


def file_digest(path: str, st: os.stat_result | None = None, memo: bool = True) -> str:
    """The SHA-256 of a file; `memo=False` reads the file even when the memo knows its stat."""
    st = st or os.stat(path)
    memo_key = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns)
    trusted = memo and time.time() - st.st_mtime_ns / 1e9 > DIGEST_MEMO_MIN_AGE_SECONDS
    if trusted and memo_key in _digest_memo:
        return _digest_memo[memo_key]
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    value = digest.hexdigest()
    if trusted:
        _digest_memo[memo_key] = value
    return value


def walk(root: str, exclude_top=()):
    """Every directory, file and symlink below root as (relative path, lstat), sorted."""
    entries = []
    if not os.path.lexists(root):
        return entries
    if not os.path.isdir(root) or os.path.islink(root):
        return [("", os.lstat(root))]
    for current, directories, files in os.walk(root):
        relative_dir = os.path.relpath(current, root)
        if relative_dir == ".":
            relative_dir = ""
            directories[:] = [d for d in directories if not any(_match(d, p) for p in exclude_top)]
            files = [f for f in files if not any(_match(f, p) for p in exclude_top)]
        kept = []
        for name in directories:
            path = os.path.join(current, name)
            rel = os.path.join(relative_dir, name)
            st = os.lstat(path)
            entries.append((rel, st))
            if not stat.S_ISLNK(st.st_mode):
                kept.append(name)
        directories[:] = kept
        for name in files:
            rel = os.path.join(relative_dir, name)
            entries.append((rel, os.lstat(os.path.join(current, name))))
    entries.sort(key=lambda entry: entry[0])
    return entries


def _match(name: str, pattern: str) -> bool:
    if pattern.endswith("*"):
        return name.startswith(pattern[:-1])
    return name == pattern


def tree_digest(root: str, exclude_top=()) -> str:
    """A digest of names, kinds, executable bits, link targets and file contents below root."""
    if not os.path.lexists(root):
        return "absent"
    digest = hashlib.sha256()
    for rel, st in walk(root, exclude_top):
        path = os.path.join(root, rel) if rel else root
        if stat.S_ISLNK(st.st_mode):
            record = f"L {rel}\0{os.readlink(path)}"
        elif stat.S_ISDIR(st.st_mode):
            record = f"D {rel}"
        elif stat.S_ISREG(st.st_mode):
            record = f"F {rel}\0{st.st_mode & 0o111:o}\0{file_digest(path, st)}"
        else:
            record = f"O {rel}\0{stat.S_IFMT(st.st_mode):o}"
        digest.update(record.encode("utf-8", "surrogateescape") + b"\n")
    return digest.hexdigest()


def path_digest(path: str) -> str:
    if os.path.isdir(path) and not os.path.islink(path):
        return "tree:" + tree_digest(path)
    if os.path.isfile(path):
        return "file:" + file_digest(path)
    if os.path.islink(path):
        return "link:" + os.readlink(path)
    return "absent"


def snapshot(root: str, exclude_top=()) -> dict[str, tuple]:
    """Change-detection state of every entry below root."""
    state = {}
    for rel, st in walk(root, exclude_top):
        path = os.path.join(root, rel) if rel else root
        target = os.readlink(path) if stat.S_ISLNK(st.st_mode) else None
        state[rel] = (stat.S_IFMT(st.st_mode), st.st_size, st.st_mtime_ns, st.st_ino,
                      st.st_mode & 0o7777, target)
    return state


def changes(before: dict, after: dict) -> tuple[list[str], list[str]]:
    """(created or modified, deleted) relative paths."""
    changed = [rel for rel, value in after.items() if before.get(rel) != value]
    deleted = [rel for rel in before if rel not in after]
    return sorted(changed), sorted(deleted)


# --- tool identity ------------------------------------------------------------------------------

_STORE_PATH = re.compile(r"^(/nix/store/[0-9a-z]{32}-[^/]+)(/.*)?$")
_identity_memo: dict[str, dict] = {}


def tool_identity(tool_path: str, root: Path | None = None) -> dict:
    """An identity of the installation a reference tool belongs to.

    A Nix store path names immutable content, so the resolved store path is the identity. Any
    other installation (the CI release package) is identified by the digest of the tool and of
    its K library and include trees, memoised per stat signature.
    """
    real = os.path.realpath(tool_path)
    if real in _identity_memo:
        return _identity_memo[real]
    if not os.path.exists(real):
        raise CacheError(f"reference tool does not exist: {tool_path}")
    match = _STORE_PATH.match(real)
    if match:
        identity = {"store": match.group(1), "tool": match.group(2) or ""}
    else:
        identity = _installation_identity(real, root)
    _identity_memo[real] = identity
    return identity


def _installation_identity(real: str, root: Path | None) -> dict:
    prefix = Path(real).parent.parent
    candidates = [Path(real)]
    for tree in (prefix / "lib" / "kframework", prefix / "include" / "kframework"):
        if tree.is_dir():
            for rel, st in walk(str(tree)):
                if stat.S_ISREG(st.st_mode):
                    candidates.append(tree / rel)
    java = shutil.which("java")
    if java:
        candidates.append(Path(os.path.realpath(java)))
    signature = sha256_bytes(canonical([
        [str(path), *(lambda st: [st.st_size, st.st_mtime_ns, st.st_ino])(path.stat())]
        for path in candidates
    ]))
    memo = root / "identity" / f"{signature}.json" if root else None
    if memo and memo.is_file():
        try:
            return json.loads(memo.read_text())
        except (OSError, json.JSONDecodeError):
            pass
    digest = hashlib.sha256()
    for path in candidates:
        digest.update(str(path).encode() + b"\0" + file_digest(str(path)).encode() + b"\n")
    identity = {"installation": str(prefix), "digest": digest.hexdigest()}
    if memo:
        try:
            memo.parent.mkdir(parents=True, exist_ok=True)
            _atomic_write(memo, json.dumps(identity).encode())
        except OSError:
            pass
    return identity


# --- kdep closure -------------------------------------------------------------------------------

def closure_request(argv: list[str]) -> tuple[str, list[str]]:
    """The source file and the kdep options of a kompile or kprove argument vector."""
    positionals, forwarded = [], []
    index = 0
    while index < len(argv):
        argument = argv[index]
        if argument.startswith("-"):
            name, has_value, value = argument.partition("=")
            if has_value:
                if name in ("-I", "--md-selector"):
                    forwarded += [name, value]
                index += 1
                continue
            if argument.startswith("-I") and len(argument) > 2:
                forwarded += ["-I", argument[2:]]
                index += 1
                continue
            if argument in VALUE_OPTIONS:
                if index + 1 >= len(argv):
                    raise CacheError(f"option {argument} has no value")
                if argument in ("-I", "--md-selector"):
                    forwarded += [argument, argv[index + 1]]
                index += 2
                continue
            index += 1
            continue
        positionals.append(argument)
        index += 1
    sources = [p for p in positionals if p.endswith((".k", ".md"))]
    if len(sources) != 1:
        raise CacheError(f"expected one K source among {positionals}")
    return sources[0], forwarded


def parse_kdep(text: str) -> list[str]:
    """The dependency paths of kdep's make rule."""
    joined = re.sub(r"\\\n", " ", text)
    _, separator, dependencies = joined.partition(":")
    if not separator:
        raise CacheError("kdep printed no dependency rule")
    tokens = re.findall(r"(?:\\.|[^\s\\])+", dependencies)
    paths = [re.sub(r"\\(.)", r"\1", token) for token in tokens]
    if not paths:
        raise CacheError("kdep printed no dependencies")
    return paths


def kdep_files(kdep: str, argv: list[str], cwd: str, environment: dict) -> tuple[list[str], list[str]]:
    """The absolute paths of the requires closure kdep resolves, and the directories a `requires`
    name can be resolved against: the -I directories, the directory of every file in the closure
    (a name may be relative to the requiring file), and, conservatively, the working directory."""
    source, forwarded = closure_request(argv)
    completed = subprocess.run(
        [kdep, *forwarded, source], cwd=cwd, env=environment, stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if completed.returncode != 0:
        raise CacheError("kdep failed: " + completed.stderr.decode("utf-8", "replace")[:300])
    files = sorted({os.path.normpath(os.path.join(cwd, path))
                    for path in parse_kdep(completed.stdout.decode("utf-8", "surrogateescape"))})
    for path in files:
        if not os.path.isfile(path):
            raise CacheError(f"kdep listed a missing file: {path}")
    directories = {os.path.normpath(os.path.abspath(cwd)),
                   os.path.dirname(os.path.normpath(os.path.join(cwd, source)))}
    directories.update(os.path.normpath(os.path.join(cwd, forwarded[index + 1]))
                       for index in range(0, len(forwarded), 2) if forwarded[index] == "-I")
    directories.update(os.path.dirname(path) for path in files)
    return files, sorted(directories)


def _in_store(path: str) -> bool:
    return path.startswith(NIX_STORE)


def shadow_candidates(files: list[str], directories: list[str]) -> list[str]:
    """Every path, other than a closure file, at which a file could change what kompile reads.

    Which file a `requires` name denotes depends on which of its candidate locations exist, so a
    file appearing at another candidate can replace a required file without changing it. The
    names are every way a closure file is reachable from a search directory, and the candidates
    are each name under each search directory: a superset of the real lookup whatever order the
    directories are tried in. A superset only adds misses, never a stale hit. Names are not
    formed across the Nix store boundary (a relative name from a mutable directory into the
    store, or back), and no candidate lies in the store: its existing paths never change.
    """
    names = {os.path.relpath(path, directory)
             for path in files for directory in directories
             if _in_store(path) == _in_store(directory)}
    closure = set(files)
    candidates = set()
    for directory in directories:
        if _in_store(directory):
            continue
        for name in names:
            candidate = os.path.normpath(os.path.join(directory, name))
            if candidate not in closure and not _in_store(candidate):
                candidates.add(candidate)
    return sorted(candidates)


def filesystem_now_ns(directory: Path) -> int:
    """A time no later than the timestamp of any file written from now on: the modification time
    of a file created now, or the precise clock if that is earlier (or the file cannot be made)."""
    now = time.time_ns()
    try:
        with tempfile.NamedTemporaryFile(prefix=".clock.", dir=directory) as stamp:
            return min(now, os.fstat(stamp.fileno()).st_mtime_ns)
    except OSError:
        return now


def stat_signature(st: os.stat_result) -> list[int]:
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]


@dataclass
class ClosureState:
    """The requires closure as it was before the tool ran.

    `closure` and `absent` are normalised for the key and the direct-mode index; `files` maps each
    absolute closure path to its digest and stat signature, and `absent_paths` lists the absolute
    shadow candidates that did not exist, so the state can be checked again after the run.
    """
    closure: list
    absent: list
    files: dict
    absent_paths: list

    def change(self) -> str | None:
        """Why the closure the tool read may differ from this state, or None."""
        for path, (digest, signature) in self.files.items():
            try:
                st = os.stat(path)
                if stat_signature(st) != signature or file_digest(path, st, memo=False) != digest:
                    return f"a required file changed while the tool ran: {path}"
            except OSError:
                return f"a required file disappeared while the tool ran: {path}"
        for path in self.absent_paths:
            if os.path.lexists(path):
                return f"a file that can shadow a required file appeared while the tool ran: {path}"
        return None


# --- the cache ----------------------------------------------------------------------------------

@dataclass
class Invocation:
    """One reference tool invocation, as the caller describes it."""
    tool: str
    argv: list[str]
    cwd: str
    tool_path: str
    environment: dict
    roots: list[str] = field(default_factory=list)
    root_excludes: tuple = ()
    inputs: list[str] = field(default_factory=list)
    stdin_path: str | None = None
    closure: str | None = None
    kdep: str | None = None
    store_statuses: tuple | None = None
    merged: bool = False
    extra: dict = field(default_factory=dict)
    label: str = ""


@dataclass
class Result:
    rc: int
    stdout: bytes
    stderr: bytes
    seconds: float
    timed_out: bool
    status: str
    detail: str = ""
    created: float | None = None
    key: str | None = None


class ReferenceCache:
    def __init__(self, mode: str, root: Path, pins: dict, max_age: float,
                 placeholders: dict | None = None, guard_kind: str = "", log_path: str | None = None,
                 context: dict | None = None):
        if mode not in MODES:
            raise ValueError(f"unknown cache mode {mode}")
        self.mode = mode
        self.root = Path(root)
        self.pins = pins
        self.max_age = max_age
        self.placeholders = sorted(
            ((name, os.path.abspath(path)) for name, path in (placeholders or {}).items() if path),
            key=lambda item: -len(item[1]),
        )
        self.guard_kind = guard_kind
        self.log_path = log_path
        self.context = context or {}
        self.counts: dict[str, int] = {}
        self.mismatches: list[str] = []
        self._lock = threading.Lock()

    # -- key -----------------------------------------------------------------------------------

    def normalise(self, text: str) -> str:
        for name, path in self.placeholders:
            text = text.replace(path, "@{" + name + "}")
        return text

    def expand(self, text: str) -> str:
        """The path a normalised path names in this run."""
        for name, path in self.placeholders:
            text = text.replace("@{" + name + "}", path)
        return text

    def semantic_environment(self, environment: dict, names=()) -> dict:
        selected = {}
        for name in (*SEMANTIC_ENVIRONMENT, *names):
            if name in environment:
                selected[name] = self.normalise(environment[name])
        selected["K_OPTS"] = k_opts_semantics(environment.get("K_OPTS", ""))
        return selected

    def base_preimage(self, invocation: Invocation, stdin_digest: str | None,
                      env_names=()) -> dict:
        return {
            "schema": SCHEMA,
            "pins": self.pins,
            "tool": {"name": invocation.tool,
                     "identity": tool_identity(invocation.tool_path, self.root)},
            "argv": [self.normalise(argument) for argument in invocation.argv],
            "cwd": self.normalise(os.path.abspath(invocation.cwd)),
            "environment": self.semantic_environment(invocation.environment, env_names),
            "streams": "merged" if invocation.merged else "separate",
            "stdin": stdin_digest,
            "inputs": self.input_digests(invocation),
            "argument_files": self.argument_files(invocation),
            "roots": [[self.normalise(os.path.abspath(root)),
                       tree_digest(root, invocation.root_excludes)] for root in invocation.roots],
            "root_excludes": list(invocation.root_excludes),
            "extra": invocation.extra,
        }

    def argument_files(self, invocation: Invocation) -> list:
        """Every argument (or `--option=value` value) that names an existing regular file is an
        input the tool may read: its content enters the key whatever the argument vector says."""
        return sorted([self.normalise(path), file_digest(path)]
                      for path in argument_paths(invocation))

    def input_digests(self, invocation: Invocation) -> list:
        return [[self.normalise(os.path.abspath(path)), path_digest(path)]
                for path in invocation.inputs]

    # -- storage -------------------------------------------------------------------------------

    def entry_path(self, key: str) -> Path:
        return self.root / "entries" / key[:2] / key

    def index_path(self, direct_key: str) -> Path:
        return self.root / "direct" / direct_key[:2] / f"{direct_key}.json"

    def load(self, key: str, preimage: dict) -> dict | None:
        """A stored entry whose manifest and preimage check out, or None."""
        entry = self.entry_path(key)
        manifest = entry / "manifest.sha256"
        try:
            lines = manifest.read_text().splitlines()
            listed = {}
            for line in lines:
                digest, name = line.split("  ", 1)
                listed[name] = digest
            for name in ("key.json", "meta.json", "result.json", "stdout", "stderr"):
                if name not in listed:
                    return None
            for name, digest in listed.items():
                if "/" in name or name.startswith("."):
                    return None
                if file_digest(str(entry / name)) != digest:
                    return None
            if (entry / "key.json").read_bytes() != canonical(preimage):
                return None
            meta = json.loads((entry / "meta.json").read_text())
            result = json.loads((entry / "result.json").read_text())
            archive = result.get("archive")
            if archive and archive not in listed:
                return None
            return {"path": entry, "meta": meta, "result": result,
                    "stdout": (entry / "stdout").read_bytes(),
                    "stderr": (entry / "stderr").read_bytes()}
        except (OSError, ValueError, KeyError):
            return None

    def store(self, key: str, preimage: dict, invocation: Invocation, result: Result,
              captured: list[tuple[str, dict]], seconds: float) -> None:
        temporary = Path(tempfile.mkdtemp(prefix=f".{key}.", dir=self._ensure(self.root / "tmp")))
        try:
            archive = None
            members = [(index, rel) for index, (_, change) in enumerate(captured)
                       for rel in change["changed"]]
            if members:
                archive = "files.tar.zst" if "zst" in tarfile.TarFile.OPEN_METH else "files.tar.gz"
                mode = "w:zst" if archive.endswith("zst") else "w:gz"
                with tarfile.open(temporary / archive, mode) as tar:
                    for index, rel in members:
                        root = captured[index][0]
                        source = os.path.join(root, rel) if rel else root
                        tar.add(source, arcname=f"r{index}/{rel}" if rel else f"r{index}",
                                recursive=False)
            outcome = {
                "rc": result.rc,
                "archive": archive,
                "deleted": {f"r{index}": change["deleted"] for index, (_, change) in enumerate(captured)},
                "changed": {f"r{index}": change["changed"] for index, (_, change) in enumerate(captured)},
            }
            meta = {
                "created": time.time(),
                "seconds": round(seconds, 3),
                "label": invocation.label,
                "tool": invocation.tool,
                "host": socket.gethostname(),
                "guard": self.guard_kind,
                "roots": [os.path.abspath(root) for root, _ in captured],
                "placeholders": dict(self.placeholders),
                "context": self.context,
                "resources": {"K_OPTS": invocation.environment.get("K_OPTS", "")},
            }
            (temporary / "key.json").write_bytes(canonical(preimage))
            (temporary / "meta.json").write_bytes(canonical(meta))
            (temporary / "result.json").write_bytes(canonical(outcome))
            (temporary / "stdout").write_bytes(result.stdout)
            (temporary / "stderr").write_bytes(result.stderr)
            names = ["key.json", "meta.json", "result.json", "stdout", "stderr"] + ([archive] if archive else [])
            (temporary / "manifest.sha256").write_text(
                "".join(f"{file_digest(str(temporary / name))}  {name}\n" for name in names))
            final = self.entry_path(key)
            self._ensure(final.parent)
            if final.exists():
                stale = final.parent / f".{key}.stale.{os.getpid()}.{time.time_ns()}"
                try:
                    os.rename(final, stale)
                    shutil.rmtree(stale, ignore_errors=True)
                except OSError:
                    pass
            try:
                os.rename(temporary, final)
            except OSError:
                # Another process stored the same key first; its entry is equally valid.
                shutil.rmtree(temporary, ignore_errors=True)
        except BaseException:
            shutil.rmtree(temporary, ignore_errors=True)
            raise

    def restore(self, entry: dict, roots: list[str]) -> None:
        result = entry["result"]
        for index, root in enumerate(roots):
            for rel in reversed(result["deleted"].get(f"r{index}", [])):
                path = os.path.join(root, rel) if rel else root
                if os.path.isdir(path) and not os.path.islink(path):
                    shutil.rmtree(path)
                elif os.path.lexists(path):
                    os.unlink(path)
        archive = result.get("archive")
        if not archive:
            return
        with tarfile.open(entry["path"] / archive, "r:*") as tar:
            for member in tar.getmembers():
                label, _, rel = member.name.partition("/")
                if not label.startswith("r") or not label[1:].isdigit():
                    raise CacheError(f"unexpected archive member {member.name}")
                index = int(label[1:])
                if index >= len(roots):
                    raise CacheError(f"archive member {member.name} names no root")
                root = roots[index]
                if not rel:
                    # The root is itself a single output file.
                    rel = os.path.basename(root)
                    root = os.path.dirname(root)
                parts = Path(rel).parts
                if Path(rel).is_absolute() or ".." in parts:
                    raise CacheError(f"unsafe archive member {member.name}")
                destination = os.path.join(root, rel)
                if os.path.lexists(destination):
                    is_dir = os.path.isdir(destination) and not os.path.islink(destination)
                    if member.isdir() and is_dir:
                        pass
                    elif is_dir:
                        shutil.rmtree(destination)
                    else:
                        os.unlink(destination)
                member.name = rel
                tar.extract(member, path=root, filter="tar")

    def _ensure(self, path: Path) -> Path:
        path.mkdir(parents=True, exist_ok=True)
        return path

    # -- logging and pruning -------------------------------------------------------------------

    def record(self, invocation: Invocation, result: Result, elapsed: float) -> None:
        with self._lock:
            self.counts[result.status] = self.counts.get(result.status, 0) + 1
            if result.status == "verify-mismatch":
                self.mismatches.append(f"{invocation.label}: {result.detail}")
        if not self.log_path:
            return
        line = {
            "label": invocation.label,
            "tool": invocation.tool,
            "status": result.status,
            "detail": result.detail,
            "key": result.key,
            "created": result.created,
            "elapsed": round(elapsed, 3),
        }
        try:
            with open(self.log_path, "a") as log:
                log.write(json.dumps(line, sort_keys=True) + "\n")
        except OSError:
            pass

    def prune(self, force: bool = False) -> int:
        """Delete entries older than the maximum age, at most once a day; returns the count."""
        stamp = self.root / "last-prune"
        now = time.time()
        try:
            if not force and stamp.exists() and now - stamp.stat().st_mtime < PRUNE_INTERVAL_SECONDS:
                return 0
            self._ensure(self.root)
            stamp.touch()
        except OSError:
            return 0
        removed = 0
        entries = self.root / "entries"
        for meta in entries.glob("*/*/meta.json") if entries.is_dir() else ():
            try:
                created = json.loads(meta.read_text()).get("created", 0)
            except (OSError, ValueError):
                created = 0
            if now - created > self.max_age:
                shutil.rmtree(meta.parent, ignore_errors=True)
                removed += 1
        for directory in ((self.root / "tmp"), (self.root / "direct")):
            if not directory.is_dir():
                continue
            for path in directory.rglob("*"):
                try:
                    if now - path.lstat().st_mtime > max(self.max_age, 86400):
                        if path.is_dir():
                            shutil.rmtree(path, ignore_errors=True)
                        else:
                            path.unlink()
                except OSError:
                    pass
        return removed

    # -- the operation -------------------------------------------------------------------------

    def run(self, invocation: Invocation, runner, env_names=()) -> Result:
        """Run or replay one invocation. `runner()` runs the tool and returns
        (rc, stdout bytes, stderr bytes, seconds, timed_out)."""
        started = time.monotonic()
        if self.mode == "off":
            result = self._fresh(runner, "off")
            self.record(invocation, result, time.monotonic() - started)
            return result
        try:
            stdin_digest = (file_digest(invocation.stdin_path)
                            if invocation.stdin_path and os.path.exists(invocation.stdin_path) else None)
            base = self.base_preimage(invocation, stdin_digest, env_names)
            preimage, direct_key = self._lookup_preimage(invocation, base)
        except (CacheError, OSError) as error:
            result = self._fresh(runner, "uncacheable", str(error))
            self.record(invocation, result, time.monotonic() - started)
            return result
        key = sha256_bytes(canonical(preimage)) if preimage else None
        entry = self.load(key, preimage) if key else None
        detail = ""
        if (entry and invocation.store_statuses is not None
                and entry["result"]["rc"] not in invocation.store_statuses):
            # The caller retries other statuses as transient, so a stored one is not replayed.
            detail = f"stored status {entry['result']['rc']} is not one the caller accepts"
            entry = None
        if entry and self.mode == "on":
            age = time.time() - entry["meta"].get("created", 0)
            if age <= self.max_age:
                try:
                    self.restore(entry, invocation.roots)
                except (OSError, tarfile.TarError, CacheError) as error:
                    detail = f"restore failed: {error}"
                else:
                    result = Result(entry["result"]["rc"], entry["stdout"], entry["stderr"],
                                    time.monotonic() - started, False, "hit",
                                    created=entry["meta"].get("created"), key=key)
                    self.record(invocation, result, time.monotonic() - started)
                    return result
            else:
                detail = f"entry older than the maximum age ({age / 86400:.1f} days)"
        closure_state = None
        if invocation.closure is not None and not (self.mode == "verify" and entry):
            # The closure is computed and hashed before the tool runs and checked again after
            # it, so a result is stored only under the closure the tool actually read.
            try:
                closure_state = self._closure_before(invocation)
            except (CacheError, OSError, subprocess.SubprocessError) as error:
                closure_state = CacheError(str(error))
        result, captured, seconds = self._capture(invocation, runner)
        if self.mode == "verify" and entry:
            result = self._verify(invocation, runner, entry, result, captured)
            if result.detail:
                # A second run started from the first run's outputs, so neither run's changes
                # describe the key's pre-state: a contradicted entry is dropped (the next run
                # recomputes it), and one that differs only nondeterministically is kept.
                if result.status == "verify-mismatch":
                    shutil.rmtree(entry["path"], ignore_errors=True)
                self.record(invocation, result, time.monotonic() - started)
                return result
        else:
            result.status = "refresh" if self.mode == "refresh" else "miss"
            result.detail = detail
        stored, outcome = self._store_quietly(invocation, base, direct_key, result, captured,
                                              seconds, closure_state)
        if stored:
            result.key = outcome
        elif result.status in ("miss", "refresh"):
            result.status = "uncacheable"
            result.detail = outcome
        self.record(invocation, result, time.monotonic() - started)
        return result

    def _lookup_preimage(self, invocation: Invocation, base: dict):
        if invocation.closure is None:
            return base, None
        if invocation.closure != "kdep":
            raise CacheError(f"unknown closure kind {invocation.closure}")
        direct_key = sha256_bytes(canonical(base))
        try:
            index = json.loads(self.index_path(direct_key).read_text())
            closure, absent = index["closure"], index["absent"]
        except (OSError, ValueError, KeyError, TypeError):
            return None, direct_key
        for path, digest in closure:
            try:
                if file_digest(self.expand(path)) != digest:
                    return None, direct_key
            except OSError:
                return None, direct_key
        for path in absent:
            # A file at another candidate location of a required name can replace what the
            # recorded closure resolved to without changing any recorded file.
            if os.path.lexists(self.expand(path)):
                return None, direct_key
        return dict(base, closure=closure), direct_key

    def _closure_before(self, invocation: Invocation) -> ClosureState:
        """The requires closure and its shadow candidates, hashed before the tool runs.

        A closure file or an existing shadow candidate whose modification or status-change time
        is not before kdep started may have changed between kdep reading it and its digest being
        taken, so such a state is refused. The start is read from the file system's own clock
        (filesystem_now_ns), because the kernel stamps files from a coarse clock that can lag the
        precise one: a write just after a precise reading could carry an earlier timestamp.
        """
        if invocation.closure != "kdep":
            raise CacheError(f"unknown closure kind {invocation.closure}")
        if not invocation.kdep:
            raise CacheError("no kdep executable for the closure")
        started = filesystem_now_ns(self._ensure(self.root / "tmp"))
        files, directories = kdep_files(invocation.kdep, invocation.argv, invocation.cwd,
                                        invocation.environment)
        state = {}
        for path in files:
            st = os.stat(path)
            if max(st.st_mtime_ns, st.st_ctime_ns) >= started:
                raise CacheError(f"a required file changed while its closure was computed: {path}")
            state[path] = (file_digest(path, st, memo=False), stat_signature(st))
        absent = []
        for candidate in shadow_candidates(files, directories):
            try:
                st = os.lstat(candidate)
            except FileNotFoundError:
                absent.append(candidate)
                continue
            except NotADirectoryError:
                absent.append(candidate)
                continue
            if max(st.st_mtime_ns, st.st_ctime_ns) >= started:
                raise CacheError(f"a file that can shadow a required file appeared while its "
                                 f"closure was computed: {candidate}")
        return ClosureState(
            closure=[[self.normalise(path), digest] for path, (digest, _) in state.items()],
            absent=[self.normalise(path) for path in absent],
            files=state,
            absent_paths=absent,
        )

    def _fresh(self, runner, status: str, detail: str = "") -> Result:
        rc, out, err, seconds, timed_out = runner()
        return Result(rc, out, err, seconds, timed_out, status, detail)

    def _capture(self, invocation: Invocation, runner):
        before = [snapshot(root, invocation.root_excludes) for root in invocation.roots]
        rc, out, err, seconds, timed_out = runner()
        captured = []
        for root, prior in zip(invocation.roots, before):
            changed, deleted = changes(prior, snapshot(root, invocation.root_excludes))
            captured.append((root, {"changed": changed, "deleted": deleted}))
        return Result(rc, out, err, seconds, timed_out, "miss"), captured, seconds

    def storable(self, invocation: Invocation, result: Result) -> str | None:
        """Why a fresh result must not be stored, or None."""
        if result.timed_out:
            return "timed out"
        if result.rc < 0 or result.rc > 128:
            return f"terminated by a signal (status {result.rc})"
        text = result.stdout[-65536:] + b"\n" + result.stderr[-65536:]
        if RESOURCE_FAILURE.search(text.decode("utf-8", "replace")):
            return "output reports a crash or resource exhaustion"
        if invocation.store_statuses is not None and result.rc not in invocation.store_statuses:
            return f"status {result.rc} is not one the caller stores"
        if self.guard_kind == "rlimit-as":
            command = " ".join(invocation.argv)
            if result.rc != 0 or "llvm" in command or invocation.tool.startswith("llvm"):
                return "the RLIMIT_AS fallback guard can fail this run for want of address space"
        return None

    def _store_quietly(self, invocation, base, direct_key, result, captured, seconds,
                       closure_state=None):
        reason = self.storable(invocation, result)
        if reason:
            return False, reason
        try:
            preimage = base
            if invocation.closure is not None:
                if not isinstance(closure_state, ClosureState):
                    raise CacheError(str(closure_state or "no closure was computed"))
                preimage = dict(base, closure=closure_state.closure)
            # The inputs must still be what the key says: a concurrent edit invalidates the run.
            argument_files = sorted(
                [self.normalise(path), file_digest(path)]
                for path in argument_paths(invocation)
                if self.normalise(path) in {name for name, _ in base["argument_files"]})
            if (self.input_digests(invocation) != base["inputs"]
                    or argument_files != base["argument_files"]):
                return False, "an input changed while the tool ran"
            if closure_state is not None:
                change = closure_state.change()
                if change:
                    return False, change
            key = sha256_bytes(canonical(preimage))
            self.store(key, preimage, invocation, result, captured, seconds)
            if closure_state is not None:
                index = self.index_path(direct_key)
                self._ensure(index.parent)
                _atomic_write(index, canonical({"closure": closure_state.closure,
                                                "absent": closure_state.absent}))
            return True, key
        except (CacheError, OSError, tarfile.TarError) as error:
            return False, f"not stored: {error}"

    def _verify(self, invocation, runner, entry, fresh: Result, captured) -> Result:
        """Compare a fresh result with the stored one and report a difference that shows a key
        missing an input (or a stale entry).

        The pinned reference is not byte-deterministic: run concurrently, kompile emits the
        sentences of definition.kore and allRules.txt in a run-dependent order with
        run-dependent generated variable numbers, and its binary artifacts (cache.bin, scanner,
        compiled.bin) differ from run to run. So a text difference counts only when it survives
        line order and per-line renumbering of generated names, a binary file counts only by its
        presence (each is compiled from the same definition as the text artifacts, which are
        compared), and a remaining difference counts only when a second fresh run reproduces the
        first one byte for byte.
        """
        first = self._observation(fresh, captured)
        stored = self._stored_observation(entry)
        names = sorted(set(first) | set(stored))
        classes = {name: classify_difference(stored.get(name), first.get(name)) for name in names}
        candidates = [name for name in names if classes[name] == "candidate"]
        tolerated = [name for name in names if classes[name] in ("equivalent", "binary")]
        if not candidates:
            fresh.status = "verify-ok"
            if tolerated:
                fresh.detail = "nondeterministic output: " + ", ".join(tolerated[:8])
            return fresh
        second_result, second_captured, _ = self._capture(invocation, runner)
        second = self._observation(second_result, second_captured)
        reproducible = [name for name in candidates if first.get(name) == second.get(name)]
        nondeterministic = tolerated + [name for name in candidates if name not in reproducible]
        if reproducible:
            second_result.status = "verify-mismatch"
            second_result.detail = "differs from the stored entry: " + ", ".join(reproducible[:8])
        else:
            second_result.status = "verify-ok"
            second_result.detail = "nondeterministic output: " + ", ".join(nondeterministic[:8])
        return second_result

    def _observation(self, result: Result, captured) -> dict:
        placeholders = self.placeholders
        roots = [root for root, _ in captured]
        observed = {"rc": ("meta", str(result.rc)),
                    "stdout": neutral_digest(result.stdout, placeholders, roots),
                    "stderr": neutral_digest(result.stderr, placeholders, roots)}
        for index, (root, change) in enumerate(captured):
            observed[f"r{index}:deleted"] = ("meta", canonical(change["deleted"]).decode())
            for rel in change["changed"]:
                path = os.path.join(root, rel) if rel else root
                name = f"r{index}/{rel}" if rel else f"r{index}"
                if os.path.islink(path):
                    observed[name] = ("meta", "link:" + os.readlink(path))
                elif os.path.isdir(path):
                    observed[name] = ("meta", "dir")
                else:
                    with open(path, "rb") as source:
                        observed[name] = neutral_digest(source.read(), placeholders, roots)
        return observed

    def _stored_observation(self, entry: dict) -> dict:
        result = entry["result"]
        meta = entry["meta"]
        placeholders = sorted(meta.get("placeholders", {}).items(), key=lambda item: -len(item[1]))
        roots = meta.get("roots", [])
        observed = {"rc": ("meta", str(result["rc"])),
                    "stdout": neutral_digest(entry["stdout"], placeholders, roots),
                    "stderr": neutral_digest(entry["stderr"], placeholders, roots)}
        for label, deleted in result.get("deleted", {}).items():
            observed[f"{label}:deleted"] = ("meta", canonical(deleted).decode())
        archive = result.get("archive")
        if archive:
            with tarfile.open(entry["path"] / archive, "r:*") as tar:
                for member in tar.getmembers():
                    if member.isfile():
                        data = tar.extractfile(member).read()
                        observed[member.name] = neutral_digest(data, placeholders, roots)
                    elif member.issym():
                        observed[member.name] = ("meta", "link:" + member.linkname)
                    else:
                        observed[member.name] = ("meta", "dir")
        return observed


GENERATED_NUMBER = re.compile(rb"(Gen)([0-9]+)")


def neutral_digest(data: bytes, placeholders, roots) -> tuple:
    """("text" or "binary", exact digest, canonical digest) of bytes with the placeholder paths and
    the output roots named neutrally, so a result recorded in another scratch directory compares
    equal to a fresh one. The canonical digest of text ignores line order and renumbers the
    generated names (`...Gen<n>`) of each line by first occurrence."""
    for name, path in placeholders:
        data = data.replace(path.encode(), b"@{" + name.encode() + b"}")
    for index, root in enumerate(roots):
        data = data.replace(root.encode(), f"@{{r{index}}}".encode())
    exact = sha256_bytes(data)
    try:
        if b"\0" in data:
            raise UnicodeDecodeError("utf-8", data, 0, 1, "NUL byte")
        data.decode("utf-8")
    except UnicodeDecodeError:
        return ("binary", exact, None)
    lines = []
    for line in data.split(b"\n"):
        numbers: dict[bytes, bytes] = {}

        def renumber(match, numbers=numbers):
            return match.group(1) + numbers.setdefault(match.group(2), str(len(numbers)).encode())
        lines.append(GENERATED_NUMBER.sub(renumber, line))
    return ("text", exact, sha256_bytes(b"\n".join(sorted(lines))))


def classify_difference(stored, fresh) -> str:
    """same, equivalent (text equal up to line order and generated numbering), binary (a binary
    file present on both sides), or candidate (a difference verify must examine)."""
    if stored == fresh:
        return "same"
    if stored is None or fresh is None or stored[0] != fresh[0] or stored[0] == "meta":
        return "candidate"
    if stored[0] == "binary":
        return "binary"
    return "equivalent" if stored[2] == fresh[2] else "candidate"


def argument_paths(invocation: Invocation) -> list[str]:
    paths = set()
    for argument in invocation.argv[1:]:
        for candidate in {argument, argument.partition("=")[2]} - {""}:
            path = os.path.abspath(os.path.join(invocation.cwd, candidate))
            if os.path.isfile(path):
                paths.add(path)
    return sorted(paths)


def _atomic_write(path: Path, data: bytes) -> None:
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as target:
            target.write(data)
        os.replace(temporary, path)
    except BaseException:
        if os.path.exists(temporary):
            os.unlink(temporary)
        raise


# --- command-line interface for the shell gates ---------------------------------------------------

def same_open_file(first: int, second: int) -> bool:
    try:
        a, b = os.fstat(first), os.fstat(second)
    except OSError:
        return False
    return (a.st_dev, a.st_ino) == (b.st_dev, b.st_ino) and not stat.S_ISCHR(a.st_mode)


def finite_stdin() -> bool:
    """Standard input is a regular file or /dev/null, so reading it to its end cannot block."""
    try:
        st = os.fstat(0)
    except OSError:
        return False
    if stat.S_ISREG(st.st_mode):
        return True
    try:
        null = os.stat(os.devnull)
    except OSError:
        return False
    return stat.S_ISCHR(st.st_mode) and st.st_rdev == null.st_rdev


def cli_run(arguments) -> int:
    argv = arguments.command
    if argv and argv[0] == "--":
        argv = argv[1:]
    if not argv:
        print("reference_cache.py run: no command", file=sys.stderr)
        return 2
    environment = dict(os.environ)
    merged = same_open_file(1, 2)
    stdin_bytes = None
    stdin_file = None
    inherit_stdin = False
    if arguments.stdin:
        if finite_stdin():
            stdin_bytes = sys.stdin.buffer.read()
            stdin_file = tempfile.NamedTemporaryFile(prefix="reference-cache-stdin.", delete=False)
            stdin_file.write(stdin_bytes)
            stdin_file.close()
        else:
            # A terminal or a pipe is read only if and when the tool reads it; reading it here
            # could block where the tool would not, so such a run passes it through uncached.
            inherit_stdin = True

    last = []

    def runner():
        started = time.monotonic()
        completed = subprocess.run(
            argv, cwd=arguments.cwd, env=environment,
            input=stdin_bytes,
            stdin=None if stdin_bytes is not None or inherit_stdin else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT if merged else subprocess.PIPE,
            check=False,
        )
        last[:] = [(completed.returncode, completed.stdout, completed.stderr or b"",
                    time.monotonic() - started, False)]
        return last[0]

    try:
        mode, _ = resolve_mode(environment)
        if inherit_stdin:
            raise CacheError("standard input is neither a regular file nor /dev/null")
        pins = json.loads(environment.get("REFERENCE_CACHE_PINS", "") or "null")
        if mode != "off" and pins is None:
            raise CacheError("REFERENCE_CACHE_PINS is unset: the gate did not check its pins")
        placeholders = dict(item.split("=", 1) for item in arguments.placeholder)
        cache = ReferenceCache(
            mode, cache_root(environment), pins, max_age_seconds(environment), placeholders,
            environment.get("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", ""),
            environment.get("REFERENCE_CACHE_LOG"),
            {"script": environment.get("REFERENCE_CACHE_SCRIPT", "")},
        )
        invocation = Invocation(
            tool=arguments.tool,
            argv=argv,
            cwd=arguments.cwd,
            tool_path=shutil.which(argv[0]) or argv[0],
            environment=environment,
            roots=[os.path.abspath(root) for root in arguments.output_root],
            inputs=[os.path.abspath(path) for path in arguments.input],
            stdin_path=stdin_file.name if stdin_file else None,
            closure="kdep" if arguments.kdep else None,
            kdep=arguments.kdep,
            store_statuses=tuple(arguments.store_status) if arguments.store_status else None,
            merged=merged,
            label=arguments.label,
        )
        if mode != "off":
            cache.prune()
        result = cache.run(invocation, runner, env_names=tuple(arguments.env))
    except Exception as error:  # noqa: BLE001 - the cache must never change a gate's outcome
        # Without the cache the tool simply runs; a failure after it ran keeps its result.
        rc, out, err, _, _ = last[0] if last else runner()
        result = Result(rc, out, err, 0.0, False, "uncacheable", str(error))
        log = environment.get("REFERENCE_CACHE_LOG")
        if log:
            with open(log, "a") as handle:
                handle.write(json.dumps({"label": arguments.label, "tool": arguments.tool,
                                         "status": "uncacheable", "detail": str(error)}) + "\n")
    finally:
        if stdin_file:
            os.unlink(stdin_file.name)
    sys.stdout.buffer.write(result.stdout)
    sys.stdout.buffer.flush()
    if not merged:
        sys.stderr.buffer.write(result.stderr)
        sys.stderr.buffer.flush()
    if result.rc < 0:
        return 128 - result.rc
    return result.rc


STATUS_ORDER = ("hit", "miss", "refresh", "verify-ok", "verify-mismatch", "uncacheable", "off")


def describe_counts(counts: dict) -> list[str]:
    return [f"{counts[name]} {name}" for name in STATUS_ORDER if counts.get(name)]


def cli_summary(arguments) -> int:
    counts: dict[str, int] = {}
    mismatches = []
    try:
        with open(arguments.log) as log:
            for line in log:
                record = json.loads(line)
                counts[record["status"]] = counts.get(record["status"], 0) + 1
                if record["status"] == "verify-mismatch":
                    mismatches.append(f"{record.get('label') or record.get('tool')}: {record.get('detail')}")
    except FileNotFoundError:
        pass
    parts = describe_counts(counts)
    mode, why = resolve_mode(os.environ)
    print(f"[reference-cache] mode {mode} ({why}): {', '.join(parts) or 'no reference calls'}"
          f"; store {cache_root(os.environ)}")
    for mismatch in mismatches:
        print(f"[reference-cache] verify mismatch: {mismatch}", file=sys.stderr)
    return 1 if mismatches else 0


def cli_mode(arguments) -> int:
    try:
        mode, why = resolve_mode(os.environ)
        max_age_seconds(os.environ)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    print(f"{mode}\t{why}")
    return 0


def cli_prune(arguments) -> int:
    cache = ReferenceCache("on", cache_root(os.environ), None, max_age_seconds(os.environ))
    print(f"removed {cache.prune(force=True)} entries older than the maximum age")
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    commands = parser.add_subparsers(dest="action", required=True)
    run = commands.add_parser("run", help="run or replay one reference tool invocation")
    run.add_argument("--tool", required=True)
    run.add_argument("--label", default="")
    run.add_argument("--cwd", default=os.getcwd())
    run.add_argument("--placeholder", action="append", default=[], metavar="NAME=PATH")
    run.add_argument("--output-root", action="append", default=[])
    run.add_argument("--input", action="append", default=[])
    run.add_argument("--env", action="append", default=[])
    run.add_argument("--stdin", action="store_true", help="the tool reads standard input")
    run.add_argument("--kdep", help="key on the kdep requires closure of the K source")
    run.add_argument("--store-status", action="append", type=int, default=[])
    run.add_argument("command", nargs=argparse.REMAINDER)
    summary = commands.add_parser("summary", help="summarise a run log; fails on a verify mismatch")
    summary.add_argument("--log", required=True)
    commands.add_parser("prune", help="delete entries older than the maximum age")
    commands.add_parser("mode", help="print the effective mode; fail on an invalid setting")
    arguments = parser.parse_args(argv)
    if arguments.action == "run":
        return cli_run(arguments)
    if arguments.action == "summary":
        return cli_summary(arguments)
    if arguments.action == "mode":
        return cli_mode(arguments)
    return cli_prune(arguments)


if __name__ == "__main__":
    raise SystemExit(main())
