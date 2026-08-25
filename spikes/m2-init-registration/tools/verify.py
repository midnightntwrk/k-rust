#!/usr/bin/env python3
"""Reproduce all positive, negative, determinism, and editor evidence."""

from __future__ import annotations

import hashlib
import os
import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Cargo.toml"
UI_MANIFEST = ROOT / "ui" / "Cargo.toml"

UI_CASES = {
    "raw_associated_submit": ("`const` items in this context need a name", "E"),
    "self_boundary": ("can't use `Self` from outer item", "E0401"),
    "trait_impl": ("is not a member of trait", "E0407"),
    "free_function": ("cannot find type `Self` in this scope", "E0411"),
    "duplicate_init": ("duplicate definitions with name `init`", "E0592"),
    "unsupported_item": ("expected `fn`", "macro"),
    "missing_init": ("no associated function or constant named `__krs_initializer_payload`", "E0599"),
}


def run(
    command: list[str],
    *,
    cwd: pathlib.Path = ROOT,
    env: dict[str, str] | None = None,
    check: bool = True,
    timeout: int = 180,
) -> subprocess.CompletedProcess[bytes]:
    merged = os.environ.copy()
    merged["CARGO_TERM_COLOR"] = "never"
    if env:
        merged.update(env)
    result = subprocess.run(command, cwd=cwd, env=merged, capture_output=True, timeout=timeout)
    if check and result.returncode:
        sys.stdout.buffer.write(result.stdout)
        sys.stderr.buffer.write(result.stderr)
        raise AssertionError(f"command failed: {' '.join(command)}")
    return result


def cargo(*arguments: str, target: pathlib.Path | None = None, check: bool = True):
    env = {"CARGO_TARGET_DIR": str(target)} if target else None
    return run(["cargo", *arguments], env=env, check=check)


def tool_gates() -> None:
    print("==> format/check/test/Clippy")
    cargo("fmt", "--manifest-path", str(MANIFEST), "--all", "--", "--check")
    with tempfile.TemporaryDirectory(prefix="m2-init-tools-") as directory:
        target = pathlib.Path(directory)
        cargo(
            "check",
            "--manifest-path",
            str(MANIFEST),
            "--workspace",
            "--all-targets",
            "--locked",
            "--offline",
            target=target,
        )
        cargo(
            "test",
            "--manifest-path",
            str(MANIFEST),
            "--workspace",
            "--locked",
            "--offline",
            target=target,
        )
        cargo(
            "clippy",
            "--manifest-path",
            str(MANIFEST),
            "--workspace",
            "--all-targets",
            "--locked",
            "--offline",
            "--",
            "-D",
            "warnings",
            target=target,
        )
    cargo("fmt", "--manifest-path", str(UI_MANIFEST), "--all", "--", "--check")


def negative_gates() -> None:
    print("==> expected compiler failures")
    with tempfile.TemporaryDirectory(prefix="m2-init-ui-") as directory:
        target = pathlib.Path(directory)
        for case, (message, code) in UI_CASES.items():
            result = cargo(
                "check",
                "--manifest-path",
                str(UI_MANIFEST),
                "--bin",
                case,
                "--locked",
                "--offline",
                target=target,
                check=False,
            )
            assert result.returncode != 0, f"{case} unexpectedly compiled"
            stderr = result.stderr.decode(errors="replace")
            assert message in stderr, f"{case}: missing {message!r}\n{stderr}"
            if code.startswith("E0"):
                assert f"error[{code}]" in stderr, f"{case}: missing {code}\n{stderr}"
            assert re.search(rf"--> src/{re.escape(case)}\.rs:\d+:\d+", stderr), stderr
            print(f"    {case}: {code}")


def collect(target: pathlib.Path) -> bytes:
    result = cargo(
        "run",
        "--manifest-path",
        str(MANIFEST),
        "-p",
        "m2-init-collector",
        "--locked",
        "--offline",
        "--quiet",
        target=target,
    )
    assert not result.stderr, result.stderr.decode()
    return result.stdout


def determinism_gate() -> None:
    print("==> two independent clean collector builds")
    with tempfile.TemporaryDirectory(prefix="m2-init-clean-a-") as first_directory:
        first = collect(pathlib.Path(first_directory))
    with tempfile.TemporaryDirectory(prefix="m2-init-clean-b-") as second_directory:
        second = collect(pathlib.Path(second_directory))
    assert first == second
    text = first.decode()
    assert text.count("|method=init") == 3
    assert "Alpha::init" in text and "Beta::init" in text and "Gamma::init" in text
    assert text.endswith("runtime_init_calls=0\n")
    assert "TypeId" not in text and "0x" not in text
    digest = hashlib.sha256(first).hexdigest()
    print(first.decode(), end="")
    print(f"collector_sha256={digest}")


def main() -> None:
    tool_gates()
    negative_gates()
    determinism_gate()
    print("==> rust-analyzer")
    result = run([sys.executable, str(ROOT / "tools" / "lsp_probe.py")], timeout=180)
    sys.stdout.buffer.write(result.stdout)
    sys.stderr.buffer.write(result.stderr)
    print("all M2 initializer registration spike gates passed")


if __name__ == "__main__":
    main()

