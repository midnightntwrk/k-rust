"""Discovery of the external executables and libraries the gates run."""

from __future__ import annotations

import ctypes
from hashlib import sha256
import mmap
import os
from pathlib import Path
import re
import shutil
import subprocess
from typing import Mapping

from support import REPOSITORY, ROOT, GateError
from support.process import compact, run


def nix_store() -> Path:
    """The Nix store searched for pinned libraries; `KRS_NIX_STORE` overrides it."""

    return Path(os.environ.get("KRS_NIX_STORE", "/nix/store"))


def scratch_root() -> Path:
    """The disk-backed directory for gate workspaces and Cargo targets.

    `KRS_GATE_SCRATCH` overrides the default `/var/tmp`; the heavy gates' target
    variables such as `KRS_KWASM_ROOT_TARGET` still override single targets.
    The directory is created if it does not exist.
    """

    root = Path(os.environ.get("KRS_GATE_SCRATCH", "/var/tmp"))
    root.mkdir(parents=True, exist_ok=True)
    return root


def checkout_scratch() -> Path:
    """The persistent scratch directory for this resolved repository checkout."""

    key = sha256(os.fsencode(ROOT.resolve())).hexdigest()[:12]
    directory = scratch_root() / f"krs-{ROOT.name}-{key}"
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def executable(name: str) -> str:
    """Resolve `name` on PATH or fail."""

    found = shutil.which(name)
    if found is None:
        raise GateError(f"required executable is unavailable: {name}")
    return found


def tool_target() -> Path:
    """The Cargo target directory the gates build their tools (`krs`, `krs-gate`) in.

    The light gates also compile every package they check here, and so do the
    collectors that `krs` generates for those packages, which inherit
    `CARGO_TARGET_DIR`: one directory compiles the KRS facade, its proc macros,
    and the tools once, rather than once per gate. Cargo keys each artifact by
    package, features, profile, and compiler, so packages that select different
    features of one crate keep separate artifacts here, and a build is
    serialized by Cargo's lock on the directory. It is `KRS_TOOL_TARGET`, else
    the caller's `CARGO_TARGET_DIR`, else the repository's `target/`, where
    `cargo build` and `cargo test` put the same crates.
    """

    configured = os.environ.get("KRS_TOOL_TARGET") or os.environ.get("CARGO_TARGET_DIR")
    if not configured:
        return REPOSITORY / "target"
    target = Path(configured)
    return target if target.is_absolute() else ROOT / target


def target_environment() -> dict[str, str]:
    """The environment entry that makes Cargo, and `krs` through it, build in `tool_target`."""

    return {"CARGO_TARGET_DIR": os.fspath(tool_target())}


def workspace_debug_binary(name: str) -> Path:
    """Locate a workspace debug binary in the shared tool target directory."""

    suffix = ".exe" if os.name == "nt" else ""
    return tool_target() / "debug" / f"{name}{suffix}"


Z3_ROUTES = ("gh-release", "system")


def z3_route() -> str:
    """How the `krs` and `krs-gate` a gate builds acquire Z3: `KRUST_GATE_Z3`.

    The variable is the one the repository's other gates read. `gh-release`,
    the default, builds with the crates' default features, which download the
    Z3 release `Krs.lock` `[solver] linked` names and link it statically; the
    download is `z3-sys`'s build script, which runs once per build-script output
    directory and ignores `--offline`, so an offline machine takes the other
    route. `system` builds with `z3-inference` alone, linked to the library
    `z3_library_dir` locates and checks (`z3_environment`), unless a `z3-sys`
    provider such as a `pkg-config` file names another. Either way the build is
    checked afterwards (`require_linked_z3`).
    """

    route = os.environ.get("KRUST_GATE_Z3") or "gh-release"
    if route not in Z3_ROUTES:
        raise GateError(f"KRUST_GATE_Z3 must be one of {', '.join(Z3_ROUTES)}, not {route!r}")
    return route


def z3_cargo_arguments(*features: str) -> list[str]:
    """The Cargo arguments that select `z3_route` for a build of a Z3-linking KRS crate.

    `features` are the package's other default features a `system` build keeps,
    since it turns the default features off.
    """

    if z3_route() == "gh-release":
        return []
    return ["--no-default-features", "--features", ",".join(("z3-inference", *features))]


# `Z3_get_full_version` returns the C string literal `Z3_FULL_VERSION`, so a
# library or an executable that links Z3 statically holds it, NUL-terminated.
# Z3's Python build writes it `Z3 4.16.0.0`; its CMake build, which makes the
# published 5.x assets, writes the bare four-part version, followed by the commit
# hash and the `git describe` text when it knows them (`5.3.3.0 430d19e6…
# 430d19e`). A bare version is recognized only as a whole C string (after a NUL),
# since four dotted numbers alone are no evidence of Z3.
Z3_FULL_VERSION = re.compile(rb"(?:Z3 |(?<=\x00))(\d+\.\d+\.\d+)\.\d+(?: [A-Za-z0-9._-]+){0,2}\x00")


def embedded_z3_releases(path: Path) -> set[str]:
    """The Z3 releases whose full-version literal `path` holds."""

    try:
        with open(path, "rb") as file:
            if os.fstat(file.fileno()).st_size == 0:
                return set()
            with mmap.mmap(file.fileno(), 0, access=mmap.ACCESS_READ) as content:
                return {match.group(1).decode() for match in Z3_FULL_VERSION.finditer(content)}
    except OSError as error:
        raise GateError(f"cannot read {path}: {error}") from error


_LIBRARY_RELEASES: dict[tuple[str, int, int], str] = {}


def z3_library_release(library: Path) -> str:
    """The Z3 release of the library file `library`.

    A shared library is asked (`Z3_get_version`); an archive cannot be loaded,
    so its release is the one its full-version literal names. A gate asks for
    the same library many times, so the answer is kept per file and version
    of its content (path, size and modification time).
    """

    try:
        status = library.stat()
    except OSError as error:
        raise GateError(f"cannot read {library}: {error}") from error
    key = (os.fspath(library.resolve()), status.st_size, status.st_mtime_ns)
    if key not in _LIBRARY_RELEASES:
        _LIBRARY_RELEASES[key] = _read_library_release(library)
    return _LIBRARY_RELEASES[key]


def _read_library_release(library: Path) -> str:
    if library.suffix == ".a":
        releases = embedded_z3_releases(library)
        if len(releases) != 1:
            found = ", ".join(sorted(releases)) or "none"
            raise GateError(f"cannot tell which Z3 release {library} holds (full-version literals: {found})")
        return releases.pop()
    try:
        loaded = ctypes.CDLL(os.fspath(library))
        parts = [ctypes.c_uint() for _ in range(4)]
        loaded.Z3_get_version(*(ctypes.byref(part) for part in parts))
    except (OSError, AttributeError) as error:
        raise GateError(f"cannot ask {library} for its Z3 version: {error}") from error
    return ".".join(str(part.value) for part in parts[:3])


def z3_directory_release(directory: Path) -> str:
    """The Z3 release a link against `directory` takes: its `libz3.so`, else its `libz3.a`."""

    shared = directory / "libz3.so"
    return z3_library_release(shared if shared.is_file() else directory / "libz3.a")


def z3_library_dir() -> Path:
    """Locate the directory of the Z3 library a build from the environment links.

    `KRS_Z3_LIB` wins when set; it may name the library directory itself or the
    package root that contains `lib/`, and it must hold the `Krs.lock`
    `[solver] linked` release, or the gate fails rather than link another.
    Otherwise the Nix store is searched for that release, static
    (`*-z3-static-VERSION`, which wraps the release's published build, the one
    the `gh-release` route downloads) before shared (`*-z3-VERSION-lib`). A
    directory qualifies when it holds `libz3.so` or `libz3.a` of that release;
    the linker takes the archive when no shared library is beside it, and the
    build then links Z3 statically.
    """

    from support.lock import linked_z3_version

    version = linked_z3_version()
    configured = os.environ.get("KRS_Z3_LIB")
    if configured:
        directory = library_directory(Path(configured))
        if directory is None:
            raise GateError(f"KRS_Z3_LIB={configured} holds neither libz3.so nor libz3.a (nor does its lib/)")
        release = z3_directory_release(directory)
        if release != version:
            raise GateError(
                f"KRS_Z3_LIB={configured} holds Z3 {release}, but krs links Z3 {version} "
                "(Krs.lock [solver] linked): point it at that release's library directory, or unset it"
            )
        return directory
    candidates = sorted(nix_store().glob(f"*-z3-static-{version}/lib"))
    candidates.extend(sorted(nix_store().glob(f"*-z3-{version}-lib/lib")))
    for candidate in candidates:
        directory = library_directory(candidate)
        if directory is not None and z3_directory_release(directory) == version:
            return directory
    raise GateError(f"Z3 {version} was not found; set KRS_Z3_LIB to its library directory")


def library_directory(candidate: Path) -> Path | None:
    """`candidate` or its `lib/`, whichever first holds `libz3.so` or `libz3.a`."""

    for directory in (candidate, candidate / "lib"):
        if any(directory.joinpath(name).is_file() for name in ("libz3.so", "libz3.a")):
            return directory
    return None


def z3_library_environment() -> dict[str, str]:
    """Link-time and run-time library paths with the linked Z3 release first.

    A build that takes k-rust's `z3-inference` alone links that library: the
    `system` route's `krs` and `krs-gate`, and the IMP artifact probe on either
    route.
    """

    z3 = os.fspath(z3_library_dir())
    return {
        name: os.pathsep.join(item for item in (z3, os.environ.get(name)) if item)
        for name in ("LIBRARY_PATH", "LD_LIBRARY_PATH")
    }


def z3_environment() -> dict[str, str]:
    """The library paths the `z3_route` build of `krs` and `krs-gate` needs.

    On the `system` route, `z3_library_environment`; on the `gh-release` route,
    none, since that build links the downloaded archive statically whatever the
    paths hold, so it needs no Z3 on the machine.
    """

    return z3_library_environment() if z3_route() == "system" else {}


def require_linked_z3(binary: Path, environment: Mapping[str, str] | None = None) -> None:
    """Fail unless `binary` links the `Krs.lock` `[solver] linked` Z3 release.

    A static link holds the release's full-version literal. Otherwise the
    `libz3` the dynamic loader resolves for `binary` under `environment` (what
    the gate runs it with) is asked for its version. This checks the build
    itself, so it also catches a release a `z3-sys` provider or
    `Z3_SYS_Z3_VERSION` substituted.
    """

    from support.lock import linked_z3_version

    version = linked_z3_version()
    embedded = embedded_z3_releases(binary)
    if embedded:
        if embedded != {version}:
            raise GateError(
                f"{binary} links Z3 {', '.join(sorted(embedded))}, but krs links Z3 {version} (Krs.lock [solver] linked)"
            )
        return
    listed = run(["ldd", binary], environment=environment, timeout=60, check=False)
    resolved = [line.strip() for line in listed.stdout.splitlines() if line.strip().startswith("libz3.")]
    if not resolved:
        raise GateError(f"{binary} links no Z3 this check recognizes; krs links Z3 {version} (Krs.lock [solver] linked)")
    name, _, location = resolved[0].partition(" => ")
    library = Path(location.rsplit(" (", 1)[0].strip())
    if not location or location.startswith("not found") or not library.is_file():
        raise GateError(f"{binary} needs {name}, which its run environment does not provide")
    release = z3_library_release(library)
    if release != version:
        raise GateError(
            f"{binary} loads Z3 {release} from {library}, but krs links Z3 {version} (Krs.lock [solver] linked)"
        )


def find_k_tool(name: str) -> str | None:
    """Locate one K executable: in `KRS_K_BIN` when set, otherwise on PATH."""

    configured = os.environ.get("KRS_K_BIN")
    if configured:
        candidate = Path(configured) / name
        return os.fspath(candidate) if candidate.is_file() and os.access(candidate, os.X_OK) else None
    return shutil.which(name)


def install_k_advice() -> str:
    """How to provide the pinned K tools, for a message about a missing one."""

    from support.lock import k_version

    return (
        f"install K v{k_version()} (the release Krs.lock pins) and put its bin directory on PATH, "
        "or set KRS_K_BIN to that directory"
    )


def k_executable(name: str) -> str:
    found = find_k_tool(name)
    if found is None:
        where = f"in KRS_K_BIN={os.environ['KRS_K_BIN']}" if os.environ.get("KRS_K_BIN") else "on PATH"
        raise GateError(f"required K tool {name!r} is not {where}; {install_k_advice()}")
    return found


def k_tool(name: str, version: str) -> str:
    """Locate one K executable and require it to report K `version` (no `v` prefix)."""

    found = k_executable(name)
    reported = run([found, "--version"], timeout=30, check=False)
    if not k_version_matches(reported, version):
        raise GateError(f"{name} is not pinned to K v{version}: {compact(reported)}")
    return found


def k_version_matches(reported: subprocess.CompletedProcess[str], version: str) -> bool:
    """Return whether a K version command succeeded and reported exactly the pinned version.

    The reported version is the first whitespace-separated stdout token of the form
    `v<digit>...`; it must equal `v{version}`, so `v7.1.3` does not match `v7.1.337`.
    """

    if reported.returncode != 0:
        return False
    token = next(
        (
            token for token in reported.stdout.split()
            if len(token) > 1 and token[0] == "v" and token[1].isascii() and token[1].isdigit()
        ),
        None,
    )
    return token == f"v{version}"


def rustfmt() -> Path:
    """Find a working rustfmt executable.

    `KRS_RUSTFMT` wins, then rustfmt on PATH, then each rustup toolchain with
    stable first, so an active toolchain that lacks rustfmt is bypassed.
    The path is absolute but not resolved: the rustup proxy dispatches on its file name.
    """

    configured = os.environ.get("KRS_RUSTFMT")
    candidates = [configured] if configured else []
    on_path = shutil.which("rustfmt")
    if on_path is not None:
        candidates.append(on_path)
    rustup = shutil.which("rustup")
    if rustup is not None:
        listed = run([rustup, "toolchain", "list"], timeout=30, check=False)
        toolchains = [line.split()[0] for line in listed.stdout.splitlines() if line.strip()]
        toolchains.sort(key=lambda toolchain: (not toolchain.startswith("stable"), toolchain))
        for toolchain in toolchains:
            located = run(
                [rustup, "which", "--toolchain", toolchain, "rustfmt"], timeout=30, check=False
            )
            if located.returncode == 0 and located.stdout.strip():
                candidates.append(located.stdout.strip())
    for candidate in candidates:
        try:
            probe = run([candidate, "--version"], timeout=30, check=False)
        except OSError:
            continue
        if probe.returncode == 0:
            return Path(shutil.which(candidate) or candidate).absolute()
    raise GateError("a working rustfmt was not found; set KRS_RUSTFMT to the executable")


def rustfmt_environment() -> dict[str, str]:
    """The environment entry that makes `krs fmt` run the working rustfmt.

    `krs fmt` starts the executable that `RUSTFMT` names (`crates/krs-fmt/src/rustfmt.rs`).
    Naming the executable leaves PATH unchanged: a toolchain's `bin` directory also holds
    that toolchain's `cargo`, which ahead of the rustup proxy rejects `cargo +stable`.
    """

    return {"RUSTFMT": os.fspath(rustfmt())}


def rust_analyzer() -> Path:
    """Locate the qualified rust-analyzer.

    `KRS_RUST_ANALYZER` wins when set; then the pinned 1.97.1 builds under the
    scratch root; then rust-analyzer on PATH.
    """

    configured = os.environ.get("KRS_RUST_ANALYZER")
    if configured:
        candidate = Path(configured)
        if not candidate.is_file():
            raise GateError(f"KRS_RUST_ANALYZER does not name a file: {configured}")
        return candidate.absolute()
    scratch = scratch_root()
    candidates = [
        scratch / "krs-ra-1.97.1-bin/rust-analyzer",
        scratch / "krs-rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/rust-analyzer",
    ]
    ambient = shutil.which("rust-analyzer")
    if ambient:
        candidates.append(Path(ambient))
    for candidate in candidates:
        if candidate.is_file():
            return candidate.absolute()
    raise GateError("could not locate the qualified rust-analyzer")
