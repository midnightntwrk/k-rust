#!/usr/bin/env python3
"""Reproduce the builtin-registration spike's complete evidence."""

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
EXPECTED_HASH = "9df3cd5bc7c4b9a47a604e8f4ea47119458e0d041ce13290747742040a64d642"
UI_CASES = {
    "ordinary_function": ("function item, not a type", "E0747"),
    "unknown_alias": ("unresolved module or unlinked crate `missing_module`", "E0433"),
    "wrong_arity": ("this struct takes 2 arguments but 1 argument was supplied", "E0061"),
    "wrong_operand": ("expected `Int`, found `String`", "E0308"),
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


def cargo(
    *arguments: str,
    target: pathlib.Path | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[bytes]:
    env = {"CARGO_TARGET_DIR": str(target)} if target else None
    return run(["cargo", *arguments], env=env, check=check)


def source_contract() -> None:
    print("==> source contract")
    facade = (ROOT / "crates" / "facade" / "src" / "lib.rs").read_text()
    macros = (ROOT / "crates" / "macros" / "src" / "lib.rs").read_text()
    semantics_manifest = (ROOT / "crates" / "semantics" / "Cargo.toml").read_text()
    semantics = (ROOT / "crates" / "semantics" / "src" / "lib.rs").read_text()
    assert "pub use Add as add;" in facade and "pub use Sub as sub;" in facade
    assert "TypeId::of::<#path>()" in macros
    assert "package = \"m3-builtin-facade\"" in semantics_manifest
    for spelling in ["dialect::int::add(x, y)", "integer::add(x, y)", "plus(x, y)"]:
        assert spelling in semantics


def tool_gates() -> None:
    print("==> format/check/test/Clippy")
    cargo("fmt", "--manifest-path", str(MANIFEST), "--all", "--", "--check")
    cargo("fmt", "--manifest-path", str(UI_MANIFEST), "--all", "--", "--check")
    with tempfile.TemporaryDirectory(prefix="m3-builtin-tools-") as directory:
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


def negative_gates() -> None:
    print("==> expected compiler failures")
    with tempfile.TemporaryDirectory(prefix="m3-builtin-ui-") as directory:
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
            assert f"error[{code}]" in stderr, f"{case}: missing {code}\n{stderr}"
            assert message in stderr, f"{case}: missing {message!r}\n{stderr}"
            assert re.search(rf"--> src/{re.escape(case)}\.rs:\d+:\d+", stderr), stderr
            print(f"    {case}: {code}")


def collect(target: pathlib.Path) -> bytes:
    result = cargo(
        "run",
        "--manifest-path",
        str(MANIFEST),
        "-p",
        "m3-builtin-collector",
        "--locked",
        "--offline",
        "--quiet",
        target=target,
    )
    assert not result.stderr, result.stderr.decode(errors="replace")
    return result.stdout


def determinism_gate() -> None:
    print("==> two independent clean collector builds")
    with tempfile.TemporaryDirectory(prefix="m3-builtin-clean-a-") as directory:
        first = collect(pathlib.Path(directory))
    with tempfile.TemporaryDirectory(prefix="m3-builtin-clean-b-") as directory:
        second = collect(pathlib.Path(directory))
    assert first == second
    text = first.decode()
    assert text.count("operation=INT.add") == 3
    assert text.count("operation=INT.sub") == 1
    assert "path=dialect::int::add" in text
    assert "path=integer::add" in text
    assert "path=plus" in text
    assert text.endswith("runtime_application_calls=0\nruntime_marker_drops=0\n")
    assert "TypeId" not in text and "0x" not in text and str(ROOT) not in text
    digest = hashlib.sha256(first).hexdigest()
    assert digest == EXPECTED_HASH, (digest, EXPECTED_HASH)
    print(text, end="")
    print(f"collector_sha256={digest}")


def main() -> None:
    source_contract()
    tool_gates()
    negative_gates()
    determinism_gate()
    print("==> rust-analyzer")
    sys.stdout.flush()
    result = run([sys.executable, str(ROOT / "tools" / "lsp_probe.py")], timeout=180)
    sys.stdout.buffer.write(result.stdout)
    sys.stderr.buffer.write(result.stderr)
    print("all M3 builtin registration spike gates passed")


if __name__ == "__main__":
    main()
