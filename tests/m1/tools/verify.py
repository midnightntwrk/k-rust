#!/usr/bin/env python3
"""One bounded, actionable entry point for the complete external M1 oracle."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import Any


M1 = pathlib.Path(__file__).resolve().parents[1]
REPO = M1.parents[1]
WORKSPACE = M1 / "workspace"
MANIFEST = WORKSPACE / "Cargo.toml"
UI_MANIFEST = M1 / "ui" / "Cargo.toml"
LSP = M1 / "tools" / "lsp_probe.py"


@dataclass(frozen=True)
class UiCase:
    name: str
    message: str
    source: str
    line: int
    code: str | None = None


UI_CASES = (
    UiCase("wrong_sort_item", "expected `trait`", "wrong_sort_item.rs", 4),
    UiCase("wrong_constructor_item", "expected `struct`", "wrong_constructor_item.rs", 6),
    UiCase(
        "malformed_constructor",
        "missing required argument `sort = ...`",
        "malformed_constructor.rs",
        3,
    ),
    UiCase(
        "malformed_rule",
        "the root must be a named path, call, or record constructor",
        "malformed_rule.rs",
        8,
    ),
    UiCase(
        "malformed_term",
        "the root must be a named path, call, or record constructor",
        "malformed_term.rs",
        4,
    ),
    UiCase(
        "duplicate_binder",
        "the same binding cannot be introduced more than once",
        "duplicate_binder.rs",
        7,
    ),
    UiCase(
        "missing_path",
        "cannot find module or crate `missing`",
        "missing_path.rs",
        6,
        "E0433",
    ),
    UiCase(
        "blanket_coherence",
        "conflicting implementations",
        "blanket_coherence.rs",
        10,
        "E0119",
    ),
)


def announce(label: str) -> None:
    print(f"==> {label}", flush=True)


def run(
    command: list[str],
    *,
    cwd: pathlib.Path = REPO,
    env: dict[str, str] | None = None,
    timeout: int = 180,
    check: bool = True,
) -> subprocess.CompletedProcess[bytes]:
    merged = os.environ.copy()
    merged["CARGO_TERM_COLOR"] = "never"
    if env:
        merged.update(env)
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            env=merged,
            capture_output=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        raise AssertionError(f"command timed out after {timeout}s: {' '.join(command)}") from error
    if check and result.returncode:
        sys.stdout.buffer.write(result.stdout)
        sys.stderr.buffer.write(result.stderr)
        raise AssertionError(
            f"command failed with status {result.returncode}: {' '.join(command)}"
        )
    return result


def cargo(
    *arguments: str,
    target: pathlib.Path | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[bytes]:
    env = {"CARGO_TARGET_DIR": str(target)} if target else None
    return run(["cargo", *arguments], env=env, check=check)


def host_target() -> str:
    output = run(["rustc", "-vV"], timeout=10).stdout.decode()
    for line in output.splitlines():
        if line.startswith("host: "):
            return line.removeprefix("host: ")
    raise AssertionError("rustc -vV did not report a host target")


def check_tooling() -> None:
    commands = (
        ("format", ["fmt", "--manifest-path", str(MANIFEST), "--all", "--", "--check"]),
        (
            "locked all-target check",
            [
                "check",
                "--manifest-path",
                str(MANIFEST),
                "--workspace",
                "--all-targets",
                "--locked",
                "--offline",
            ],
        ),
        (
            "locked tests",
            ["test", "--manifest-path", str(MANIFEST), "--workspace", "--locked", "--offline"],
        ),
        (
            "warnings-denied Clippy",
            [
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
            ],
        ),
        (
            "UI formatting",
            ["fmt", "--manifest-path", str(UI_MANIFEST), "--all", "--", "--check"],
        ),
    )
    with tempfile.TemporaryDirectory(prefix="krs-m1-tools-") as directory:
        target = pathlib.Path(directory)
        for label, arguments in commands:
            announce(label)
            cargo(*arguments, target=target)


def check_ui() -> None:
    announce("expected compiler failures")
    with tempfile.TemporaryDirectory(prefix="krs-m1-ui-") as directory:
        target = pathlib.Path(directory)
        for case in UI_CASES:
            result = cargo(
                "check",
                "--manifest-path",
                str(UI_MANIFEST),
                "--bin",
                case.name,
                "--locked",
                "--offline",
                target=target,
                check=False,
            )
            assert result.returncode != 0, f"{case.name} unexpectedly compiled"
            stderr = result.stderr.decode(errors="replace")
            assert case.message in stderr, (
                f"{case.name}: missing error message {case.message!r}\n{stderr}"
            )
            if case.code:
                assert f"error[{case.code}]" in stderr, (
                    f"{case.name}: missing error category {case.code}\n{stderr}"
                )
            location = re.compile(
                rf"-->\s+src/{re.escape(case.source)}:{case.line}:\d+"
            )
            assert location.search(stderr), (
                f"{case.name}: missing responsible source line "
                f"src/{case.source}:{case.line}\n{stderr}"
            )
            print(f"    {case.name}: expected {case.code or 'macro error'} at line {case.line}")


def metadata(path: pathlib.Path) -> bytes:
    result = run(
        [
            "cargo",
            "metadata",
            "--manifest-path",
            str(MANIFEST),
            "--format-version",
            "1",
            "--locked",
            "--offline",
        ],
        timeout=60,
    )
    path.write_bytes(result.stdout)
    return result.stdout


def collect_once(directory: pathlib.Path, label: str) -> tuple[bytes, bytes]:
    metadata_path = directory / "metadata.json"
    selection_path = directory / "selection.json"
    metadata(metadata_path)
    result = cargo(
        "run",
        "--manifest-path",
        str(MANIFEST),
        "-p",
        "m1-oracle-runner",
        "--locked",
        "--offline",
        "--quiet",
        "--",
        str(metadata_path),
        str(selection_path),
        host_target(),
        target=directory / "target",
    )
    assert not result.stderr, f"{label}: collector wrote logs to stderr:\n{result.stderr.decode()}"
    return selection_path.read_bytes(), result.stdout


def strings(value: Any):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, nested in value.items():
            yield key
            yield from strings(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from strings(nested)


def assert_artifacts(selection_bytes: bytes, bundle_bytes: bytes) -> dict[str, Any]:
    selection = json.loads(selection_bytes)
    bundle = json.loads(bundle_bytes)
    assert selection["schema"] == 2
    assert len(selection["facets"]) == 2
    facets = {facet["package"]: facet for facet in selection["facets"]}
    assert facets["root-semantics"]["crate-root"] == "root_language_api"
    assert facets["base-semantics"]["crate-root"] == "base_language_api"
    assert all(facet["cargo-source"] == "workspace" for facet in facets.values())

    assert bundle["protocol_version"] == 4
    descriptors = bundle["descriptors"]
    assert len(descriptors) == 24
    ids = [json.dumps(item["id"], sort_keys=True) for item in descriptors]
    assert len(set(ids)) == len(ids)
    kind_order = {"sort": 0, "constructor": 1, "rule": 2, "equation": 3, "claim": 4}

    def id_key(item: dict[str, Any]) -> tuple[Any, ...]:
        identity = item["id"]
        package = identity["package"]
        return (
            package["k_namespace"],
            package["cargo_name"],
            package["cargo_version"],
            package["cargo_source"],
            identity["module_path"],
            identity["item_name"],
            kind_order[identity["item_kind"]],
            identity["disambiguator"],
        )

    assert [id_key(item) for item in descriptors] == sorted(
        id_key(item) for item in descriptors
    ), "canonical descriptors are not sorted"

    actual_items = {
        (
            item["id"]["package"]["cargo_name"],
            tuple(item["id"]["module_path"]),
            item["id"]["item_name"],
            item["id"]["item_kind"],
        )
        for item in descriptors
    }
    expected_items = {
        ("base-semantics", (), "BaseItem", "sort"),
        ("base-semantics", (), "Common", "sort"),
        ("base-semantics", (), "Same", "constructor"),
        ("base-semantics", (), "Unit", "constructor"),
        ("base-semantics", ("nested",), "Common", "sort"),
        ("base-semantics", ("nested",), "Same", "constructor"),
        ("root-semantics", (), "KItem", "sort"),
        ("root-semantics", (), "KResult", "sort"),
        ("root-semantics", (), "Expr", "sort"),
        ("root-semantics", (), "Value", "sort"),
        ("root-semantics", (), "Common", "sort"),
        ("root-semantics", (), "Same", "constructor"),
        ("root-semantics", (), "Pair", "constructor"),
        ("root-semantics", (), "Wrap", "constructor"),
        ("root-semantics", (), "ValueNode", "constructor"),
        ("root-semantics", (), "native_swap", "rule"),
        ("root-semantics", (), "macro_swap", "rule"),
        ("root-semantics", (), "zero_bindings", "rule"),
        ("root-semantics", (), "ordinal_gap", "rule"),
        ("root-semantics", (), "cross_package", "rule"),
        ("root-semantics", ("nested",), "Common", "sort"),
        ("root-semantics", ("nested",), "Same", "constructor"),
        ("root-semantics", ("nested",), "Done", "constructor"),
        ("root-semantics", ("nested",), "Keep", "constructor"),
    }
    assert actual_items == expected_items

    stable_ids = set(ids)
    kind_by_id = {
        json.dumps(item["id"], sort_keys=True): item["id"]["item_kind"]
        for item in descriptors
    }
    expected_bindings = {
        "native_swap": ["first", "second"],
        "macro_swap": ["first", "second"],
        "zero_bindings": [],
        "ordinal_gap": ["日本"],
        "cross_package": [],
    }
    expected_reference_counts = {
        "native_swap": 4,
        "macro_swap": 4,
        "zero_bindings": 4,
        "ordinal_gap": 6,
        "cross_package": 4,
    }
    for item in descriptors:
        payload = item["descriptor"]
        if item["descriptor_kind"] == "sort":
            targets = payload["parents"]
            expected_kind = "sort"
        elif item["descriptor_kind"] == "constructor":
            targets = [payload["sort"]] + [
                field["sort"] for field in payload["fields"] if "sort" in field
            ]
            expected_kind = "sort"
        else:
            name = item["id"]["item_name"]
            assert payload["parameters"][0]["bindings"] == expected_bindings[name]
            assert len(payload["references"]) == expected_reference_counts[name]
            keys = [
                (reference["key"]["role"], reference["key"]["ordinal"])
                for reference in payload["references"]
            ]
            assert len(keys) == len(set(keys))
            for reference in payload["references"]:
                role = reference["key"]["role"]
                target_key = json.dumps(reference["target"], sort_keys=True)
                required = (
                    "sort" if role in {"rule_type", "rule_result_type"} else "constructor"
                )
                assert kind_by_id[target_key] == required
            targets = [reference["target"] for reference in payload["references"]]
            targets.extend(parameter["sort"] for parameter in payload["parameters"])
            targets.append(payload["result_sort"])
            expected_kind = None
        for target in targets:
            encoded = json.dumps(target, sort_keys=True)
            assert encoded in stable_ids, f"unresolved stable reference: {target}"
            if expected_kind:
                assert kind_by_id[encoded] == expected_kind

    expected_packages = {"root-semantics", "base-semantics"}
    assert {
        item["id"]["package"]["cargo_name"] for item in descriptors
    } == expected_packages
    for item in descriptors:
        origin = item["origin"]
        assert [frame["kind"] for frame in origin] == [
            "authored",
            "macro_invocation",
            "generated_descriptor",
        ]
        authored = origin[0]["range"]
        assert authored["start_byte"] < authored["end_byte"]
        source = authored["file"]
        assert source["package_relative_path"] == "src/lib.rs"
        assert re.fullmatch(r"[0-9a-f]{64}", source["content_sha256"])

    forbidden = str(REPO.resolve())
    for value in (*strings(selection), *strings(bundle)):
        assert forbidden not in value, f"absolute checkout path leaked: {value}"
        assert not value.startswith("/"), f"absolute path leaked: {value}"

    return {
        "protocol": bundle["protocol_version"],
        "descriptors": len(descriptors),
        "selection_sha256": hashlib.sha256(selection_bytes).hexdigest(),
        "bundle_sha256": hashlib.sha256(bundle_bytes).hexdigest(),
    }


def check_collection() -> dict[str, Any]:
    announce("two independent clean collections")
    with tempfile.TemporaryDirectory(prefix="krs-m1-a-") as first_dir, tempfile.TemporaryDirectory(
        prefix="krs-m1-b-"
    ) as second_dir:
        first = collect_once(pathlib.Path(first_dir), "first")
        second = collect_once(pathlib.Path(second_dir), "second")
    assert first[0] == second[0], "canonical selection bytes differ across clean targets"
    assert first[1] == second[1], "DescriptorBundle bytes differ across clean targets"
    return assert_artifacts(*first)


def check_lsp() -> dict[str, Any]:
    announce("production rust-analyzer diagnostics/navigation/hover/rename")
    result = run([sys.executable, str(LSP)], timeout=150)
    if result.stderr:
        sys.stderr.buffer.write(result.stderr)
    return json.loads(result.stdout)


def main() -> None:
    check_tooling()
    check_ui()
    collection = check_collection()
    lsp = check_lsp()
    announce("M1 oracle passed")
    print(json.dumps({"collection": collection, "lsp": lsp}, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"M1 oracle failed: {error}", file=sys.stderr)
        raise
