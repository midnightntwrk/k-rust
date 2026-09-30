"""Discovery of the external executables and libraries the gates run."""

from __future__ import annotations

from hashlib import sha256
import os
from pathlib import Path
import shutil
import subprocess

from support import ROOT, GateError
from support.process import compact, run


def nix_store() -> Path:
    """The Nix store searched for pinned libraries; `KRS_NIX_STORE` overrides it."""

    return Path(os.environ.get("KRS_NIX_STORE", "/nix/store"))


def scratch_root() -> Path:
    """The disk-backed directory for gate workspaces and Cargo targets.

    `KRS_GATE_SCRATCH` overrides the default `/var/tmp`; per-gate target
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


def workspace_debug_binary(name: str) -> Path:
    """Locate a workspace binary under Cargo's configured target directory."""

    target = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target"))
    if not target.is_absolute():
        target = ROOT / target
    suffix = ".exe" if os.name == "nt" else ""
    return target / "debug" / f"{name}{suffix}"


def z3_library_dir() -> Path:
    """Locate the qualified Z3 shared-library directory.

    `KRS_Z3_LIB` wins when set; it may name the library directory itself or the
    package root that contains `lib/`. Otherwise the Nix store is searched for
    the `Krs.lock` solver version.
    """

    from support.lock import z3_version

    version = z3_version()
    configured = os.environ.get("KRS_Z3_LIB")
    candidates = [Path(configured)] if configured else []
    candidates.extend(sorted(nix_store().glob(f"*-z3-{version}-lib/lib")))
    for candidate in candidates:
        for directory in (candidate, candidate / "lib"):
            if directory.joinpath("libz3.so").is_file():
                return directory
    raise GateError(f"Z3 {version} was not found; set KRS_Z3_LIB to its shared-library directory")


def z3_environment() -> dict[str, str]:
    """Link-time and run-time library paths with the qualified Z3 first."""

    z3 = os.fspath(z3_library_dir())
    return {
        name: os.pathsep.join(item for item in (z3, os.environ.get(name)) if item)
        for name in ("LIBRARY_PATH", "LD_LIBRARY_PATH")
    }


def find_k_tool(name: str) -> str | None:
    """Locate one K executable: in `KRS_K_BIN` when set, otherwise on PATH."""

    configured = os.environ.get("KRS_K_BIN")
    if configured:
        candidate = Path(configured) / name
        return os.fspath(candidate) if candidate.is_file() and os.access(candidate, os.X_OK) else None
    return shutil.which(name)


def k_executable(name: str) -> str:
    found = find_k_tool(name)
    if found is None:
        raise GateError(
            f"required K tool {name!r} is unavailable; put the pinned K bin directory "
            "on PATH or set KRS_K_BIN"
        )
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


def rustfmt_dir() -> Path:
    """Find the directory of a working rustfmt.

    `KRS_RUSTFMT` wins, then rustfmt on PATH, then each rustup toolchain with
    stable first, so an active toolchain that lacks rustfmt is bypassed.
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
            return Path(candidate).parent
    raise GateError("a working rustfmt was not found; set KRS_RUSTFMT to the executable")


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
