#!/usr/bin/env python3
"""Native parity gate for explicit descriptor registration.

An inventory-mode census of a copy of `tests/tour-minimal` lists every
registered descriptor factory, and the product's `krs-expand` renderer through
`krs-gate` supplies the crate-root registration table appended to that copy.
Inventory-mode collection of the copy (configuration A,
default `krs` features) and explicit-mode collection of the same copy with
`default-features = false` (configuration B) must produce byte-identical
canonical descriptor bundles.

Both configurations compile the same absolute path: `krs-macros` hashes
`Span::file()` into factory names, so a table is valid only for the path the
crate is compiled from.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.hashing import sha256_bytes  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.tools import checkout_scratch, executable, z3_environment  # noqa: E402


FIXTURE = ROOT / "tests" / "tour-minimal"
FACADE = ROOT / "crates" / "krs"
PACKAGE = "krs-tour-minimal"
DEFINITION = "main"
BUNDLE = "descriptor-bundle.json"
FACADE_DEPENDENCY = 'k = { package = "krs", path = "../../crates/krs" }'
HIDDEN_CONSTRUCTOR = """
// The product table must carry this constructor under cfg; both bundles must omit it.
#[k::constructor(sort = ObjectTerm, syntax = "hidden")]
#[cfg(any())]
pub struct Hidden;
"""
CENSUS_MAIN = """\
//! Lists every inventory registration linked into this process.

#[allow(unused_extern_crates)]
extern crate lesson as _;

fn main() {
    let census = krs::__private::registration_census();
    for registration in &census.registrations {
        println!("registration\\t{}\\t{}", registration.path, registration.manifest_dir);
    }
    for manifest_dir in &census.framework_requests {
        println!("framework\\t{manifest_dir}");
    }
}
"""


def cli_environment() -> dict[str, str]:
    return {**z3_environment(), "CARGO_TERM_COLOR": "never", "CARGO_NET_OFFLINE": "true"}


def production_binary(override: Path | None, environment: dict[str, str]) -> Path:
    if override is not None:
        binary = override.resolve()
        if not binary.is_file():
            raise GateError(f"requested KRS binary does not exist: {binary}")
        return binary
    return build(environment, timeout=1200)


def facade_dependency(*, inventory: bool) -> str:
    features = "" if inventory else ", default-features = false"
    return f'k = {{ package = "krs", path = {json.dumps(os.fspath(FACADE))}{features} }}'


def set_inventory(copy: Path, *, inventory: bool) -> None:
    """Switches the copy's `krs` dependency between configurations A and B."""

    manifest = copy / "Cargo.toml"
    text = manifest.read_text(encoding="utf-8")
    current = facade_dependency(inventory=not inventory)
    if text.count(current) == 1:
        manifest.write_text(
            text.replace(current, facade_dependency(inventory=inventory)),
            encoding="utf-8",
        )
    elif text.count(facade_dependency(inventory=inventory)) != 1:
        raise GateError("the copy's facade dependency was not rewritten as expected")


def copy_fixture(destination: Path, *, extra_source: str) -> Path:
    shutil.copytree(
        FIXTURE,
        destination,
        ignore=shutil.ignore_patterns("target", "verify.py", "__pycache__"),
    )
    manifest = destination / "Cargo.toml"
    text = manifest.read_text(encoding="utf-8")
    if text.count(FACADE_DEPENDENCY) != 1:
        raise GateError("tour-minimal no longer declares the expected facade dependency")
    manifest.write_text(
        text.replace(FACADE_DEPENDENCY, facade_dependency(inventory=True)),
        encoding="utf-8",
    )
    if extra_source:
        with (destination / "src" / "lib.rs").open("a", encoding="utf-8") as source:
            source.write(extra_source)
    return destination


def cargo_metadata(manifest: Path, environment: dict[str, str]) -> dict[str, Any]:
    output = run(
        [
            executable("cargo"),
            "+stable",
            "metadata",
            "--format-version",
            "1",
            "--no-deps",
            "--offline",
            "--manifest-path",
            manifest,
        ],
        environment=environment,
        timeout=1200,
    )
    return json.loads(output.stdout)


def fixture_identity(copy: Path, environment: dict[str, str]) -> tuple[str, str]:
    """Returns the library crate root and the `krs` dependency alias."""

    metadata = cargo_metadata(copy / "Cargo.toml", environment)
    [package] = [item for item in metadata["packages"] if item["name"] == PACKAGE]
    [library] = [
        target["name"] for target in package["targets"] if "lib" in target["kind"]
    ]
    [facade] = [
        dependency.get("rename") or dependency["name"]
        for dependency in package["dependencies"]
        if dependency["name"] == "krs"
    ]
    return library, facade


def take_census(
    lesson: Path, workspace: Path, environment: dict[str, str]
) -> dict[str, Any]:
    census = workspace / "census"
    (census / "src").mkdir(parents=True)
    (census / "Cargo.toml").write_text(
        "[package]\n"
        'name = "krs-registration-census"\n'
        'version = "0.0.0"\n'
        'edition = "2024"\n'
        "publish = false\n\n"
        "[dependencies]\n"
        f'lesson = {{ package = "{PACKAGE}", path = {json.dumps(os.fspath(lesson))} }}\n'
        f"krs = {{ path = {json.dumps(os.fspath(FACADE))} }}\n\n"
        "[workspace]\n",
        encoding="utf-8",
    )
    (census / "src" / "main.rs").write_text(CENSUS_MAIN, encoding="utf-8")
    output = run(
        [
            executable("cargo"),
            "+stable",
            "run",
            "--quiet",
            "--offline",
            "--manifest-path",
            census / "Cargo.toml",
        ],
        environment=environment,
        timeout=1200,
        cwd=census,
    )
    registrations = []
    framework_requests = []
    for line in output.stdout.splitlines():
        kind, *fields = line.split("\t")
        if kind == "registration" and len(fields) == 2:
            registrations.append({"path": fields[0], "manifest_dir": fields[1]})
        elif kind == "framework" and len(fields) == 1:
            framework_requests.append(fields[0])
        else:
            raise GateError(f"unexpected census line: {line!r}")
    if not registrations:
        raise GateError("the census found no registrations")
    return {"registrations": registrations, "framework_requests": framework_requests}


def registration_path(registration: dict[str, Any], crate_root: str) -> str:
    return "::".join([crate_root, *registration["module_path"][1:], registration["factory"]])


def verify_registration_census(
    product: dict[str, Any], census: dict[str, Any], lesson: Path, crate_root: str
) -> None:
    """Requires the product registrations and framework request to match inventory."""

    manifest_dir = lesson.resolve()
    inventory_paths = sorted(
        registration["path"]
        for registration in census["registrations"]
        if Path(registration["manifest_dir"]).resolve() == manifest_dir
    )
    rust_paths = sorted(
        registration_path(registration, crate_root)
        for registration in product["registrations"]
        if not registration["cfg"]
    )
    if rust_paths != inventory_paths:
        rust = Counter(rust_paths)
        inventory = Counter(inventory_paths)
        raise GateError(
            "product registrations differ from the copy's census: "
            f"missing from product={sorted((inventory - rust).elements())}, "
            f"absent from census={sorted((rust - inventory).elements())}"
        )
    census_paths = {registration["path"] for registration in census["registrations"]}
    for registration in product["registrations"]:
        cfg = registration["cfg"]
        if not cfg:
            continue
        path = registration_path(registration, crate_root)
        if ["".join(attribute.split()) for attribute in cfg] != ["#[cfg(any())]"]:
            raise GateError(f"product registration {path} has unsupported cfg {cfg!r}")
        if path in census_paths:
            raise GateError(f"cfg-disabled product registration {path} appears in the census")
    requests_framework = any(
        Path(directory).resolve() == manifest_dir
        for directory in census["framework_requests"]
    )
    if product["requests_framework"] != requests_framework:
        raise GateError(
            "product framework request differs from the copy's census: "
            f"product={product['requests_framework']}, census={requests_framework}"
        )


def append_table(copy: Path, table: str) -> None:
    with (copy / "src" / "lib.rs").open("a", encoding="utf-8") as source:
        source.write(table)


def emit_bundle(
    binary: Path,
    copy: Path,
    output: Path,
    registration: str,
    environment: dict[str, str],
    *,
    check: bool = True,
) -> bytes | None:
    process = run(
        Invocation(binary, copy / "Cargo.toml", PACKAGE, DEFINITION).argv(
            "emit-k", "--registration", registration, "--output", output
        ),
        environment=environment,
        timeout=1200,
        check=check,
    )
    if process.returncode != 0:
        return None
    return (output / BUNDLE).read_bytes()


def descriptor_ids(directory: Path, gate: Path, environment: dict[str, str]) -> list[str]:
    rows = krs_gate.ir_query(gate, directory, {"kind": "descriptors"}, environment=environment)["rows"]
    return sorted(json.dumps(row["id"], sort_keys=True) for row in rows)


def collect_both(
    binary: Path, copy: Path, output: Path, environment: dict[str, str]
) -> tuple[bytes, bytes | None]:
    """Collects configuration A, then configuration B, of one copy."""

    set_inventory(copy, inventory=True)
    inventory_bundle = emit_bundle(
        binary, copy, output / "inventory", "inventory", environment
    )
    assert inventory_bundle is not None
    set_inventory(copy, inventory=False)
    explicit_bundle = emit_bundle(
        binary, copy, output / "explicit", "explicit", environment, check=False
    )
    set_inventory(copy, inventory=True)
    return inventory_bundle, explicit_bundle


def parity(
    binary: Path,
    workspace: Path,
    name: str,
    extra_source: str,
    environment: dict[str, str],
    gate: Path,
) -> dict[str, Any]:
    """Runs census, product table rendering, and both collections for one fixture variant."""

    root = workspace / name
    root.mkdir()
    copy = copy_fixture(root / "lesson", extra_source=extra_source)
    crate_root, facade = fixture_identity(copy, environment)
    census = take_census(copy, root, environment)
    source = copy / "src" / "lib.rs"
    product = krs_gate.registration_table(
        gate, source, source.relative_to(copy).as_posix(), crate_root, facade,
        environment=environment,
    )
    verify_registration_census(product, census, copy, crate_root)
    table = product["table"]
    authored = source.read_bytes()
    append_table(copy, table)
    inventory_bundle, explicit_bundle = collect_both(
        binary, copy, root / "out", environment
    )
    if explicit_bundle is None:
        raise GateError(f"{name}: explicit-mode collection failed")
    if inventory_bundle != explicit_bundle:
        raise GateError(
            f"{name}: explicit bundle {sha256_bytes(explicit_bundle)} differs from inventory bundle {sha256_bytes(inventory_bundle)}"
        )
    return {
        "root": root,
        "copy": copy,
        "authored": authored,
        "census": census,
        "registrations": product["registrations"],
        "table": table,
        "bundle": inventory_bundle,
        "source": source.read_bytes(),
    }


def verify_rejects_inventory(
    binary: Path, workspace: Path, environment: dict[str, str]
) -> None:
    copy = copy_fixture(workspace / "rejected", extra_source="")
    process = run(
        Invocation(binary, copy / "Cargo.toml", PACKAGE, DEFINITION).argv(
            "emit-k", "--registration", "explicit", "--output", workspace / "rejected-out"
        ),
        environment=environment,
        timeout=1200,
        check=False,
    )
    if process.returncode == 0 or "inventory" not in process.stderr:
        raise GateError(
            f"explicit mode accepted a graph with `inventory` enabled: {compact(process)}"
        )


def verify_sensitivity(
    binary: Path, base: dict[str, Any], environment: dict[str, str], gate: Path
) -> tuple[str, str]:
    """Removes one table line and requires the parity comparison to fail.

    The mutation is applied at the base copy's own path so that the remaining
    factory names stay valid.
    """

    lines = base["table"].splitlines(keepends=True)
    factories = [
        index for index, line in enumerate(lines)
        if line.lstrip().startswith("registrar.factory(")
    ]
    if not factories:
        raise GateError("the product table has no unconditional factory line to remove")
    # The rule descriptor is referenced by no other descriptor, so omitting it
    # still collects successfully and exercises byte comparison itself.
    rules = [index for index in factories if "head_rule_descriptor" in lines[index]]
    removed = lines.pop((rules or factories)[-1]).strip()
    source = base["copy"] / "src" / "lib.rs"
    source.write_bytes(base["authored"] + "".join(lines).encode("utf-8"))
    try:
        inventory_bundle, explicit_bundle = collect_both(
            binary, base["copy"], base["root"] / "sensitivity", environment
        )
    finally:
        source.write_bytes(base["source"])
    if explicit_bundle is None:
        return removed, "explicit collection failed"
    if explicit_bundle == inventory_bundle:
        raise GateError(f"removing `{removed}` did not change the explicit bundle")
    missing = sorted(
        set(descriptor_ids(base["root"] / "sensitivity" / "inventory", gate, environment)) - set(descriptor_ids(base["root"] / "sensitivity" / "explicit", gate, environment))
    )
    return removed, f"explicit bundle lacks {len(missing)} descriptor(s)"


def verify_fixture_difference(
    binary: Path, workspace: Path, base: dict[str, Any], environment: dict[str, str]
) -> str:
    """Requires the copy to differ from the unmodified fixture only in its source hash."""

    run(
        Invocation(binary, FIXTURE / "Cargo.toml", PACKAGE, DEFINITION).argv(
            "emit-k", "--output", workspace / "fixture-out"
        ),
        environment=environment,
        timeout=1200,
    )
    fixture_bundle = (workspace / "fixture-out" / BUNDLE).read_bytes()
    original = sha256_bytes((FIXTURE / "src" / "lib.rs").read_bytes())
    modified = sha256_bytes(base["source"])
    if fixture_bundle.count(original.encode()) == 0:
        raise GateError("the fixture bundle does not carry the fixture source hash")
    if fixture_bundle.replace(original.encode(), modified.encode()) != base["bundle"]:
        raise GateError(
            "the copy's bundle differs from the unmodified fixture beyond the src/lib.rs hash"
        )
    return sha256_bytes(fixture_bundle)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--krs",
        type=Path,
        help="use an existing production KRS binary instead of building one",
    )
    parser.add_argument(
        "--evidence",
        type=Path,
        help="directory receiving the census, table, bundles, and hashes",
    )
    arguments = parser.parse_args()

    environment = cli_environment()
    binary = production_binary(arguments.krs, environment)
    gate = krs_gate.configured_or_build(checkout_scratch() / "explicit-registration-root-target")

    with tempfile.TemporaryDirectory(prefix="krs-explicit-registration-") as temporary:
        workspace = Path(temporary)

        verify_rejects_inventory(binary, workspace, environment)
        print("PASS planning: explicit mode rejects an active `inventory` feature")

        base = parity(binary, workspace, "base", "", environment, gate)
        count = len(base["registrations"])
        print(
            f"PASS parity: explicit and inventory bundles are byte-identical "
            f"({len(base['bundle'])} bytes, sha256 {sha256_bytes(base['bundle'])}, {count} table entries)"
        )

        fixture_digest = verify_fixture_difference(binary, workspace, base, environment)
        print(
            "PASS fixture: the tabled copy differs from the unmodified fixture only in the src/lib.rs hash"
        )

        removed, effect = verify_sensitivity(binary, base, environment, gate)
        print(f"PASS sensitivity: removing `{removed}` breaks parity ({effect})")

        hidden = parity(binary, workspace, "cfg", HIDDEN_CONSTRUCTOR, environment, gate)
        hidden_registrations = [
            registration for registration in hidden["registrations"]
            if ["".join(attribute.split()) for attribute in registration["cfg"]] == ["#[cfg(any())]"]
        ]
        constructors = [
            registration for registration in hidden_registrations
            if registration["factory"].startswith("__krs_constructor_descriptor_")
        ]
        if len(constructors) != 1:
            raise GateError("the product registration list must carry the Hidden constructor under #[cfg(any())]")
        table_lines = {line.strip() for line in hidden["table"].splitlines()}
        for registration in hidden_registrations:
            path = registration_path(registration, "crate")
            cfg_prefix = " ".join(registration["cfg"])
            if f"{cfg_prefix} registrar.factory({path});" not in table_lines:
                raise GateError(f"the product table does not carry the cfg-prefixed factory {path}")
        base_ids = descriptor_ids(base["root"] / "out" / "inventory", gate, environment)
        for mode in ("inventory", "explicit"):
            if descriptor_ids(hidden["root"] / "out" / mode, gate, environment) != base_ids:
                raise GateError(f"the cfg-disabled constructor changed the {mode} descriptor set")
        print("PASS cfg: the product table carries a cfg-disabled constructor absent from both bundles")

        if arguments.evidence is not None:
            evidence = arguments.evidence
            evidence.mkdir(parents=True, exist_ok=True)
            census = {
                "registrations": [
                    {
                        "path": item["path"],
                        "manifest_dir": "<KRS>/crates/krs"
                        if Path(item["manifest_dir"]).resolve() == FACADE.resolve()
                        else "<COPY>",
                    }
                    for item in base["census"]["registrations"]
                ],
                "framework_requests": [
                    "<COPY>" for _ in base["census"]["framework_requests"]
                ],
            }
            (evidence / "census.json").write_text(
                json.dumps(census, indent=2) + "\n", encoding="utf-8"
            )
            (evidence / "registration-table.rs").write_text(
                base["table"], encoding="utf-8"
            )
            (evidence / "bundle-inventory.json").write_bytes(base["bundle"])
            (evidence / "bundle-explicit.json").write_bytes(base["bundle"])
            (evidence / "hashes.txt").write_text(
                f"{sha256_bytes(base['bundle'])}  bundle-inventory.json\n"
                f"{sha256_bytes(base['bundle'])}  bundle-explicit.json\n"
                f"{fixture_digest}  unmodified tour-minimal bundle\n"
                f"{sha256_bytes(hidden['bundle'])}  cfg-variant bundle (both modes)\n",
                encoding="utf-8",
            )
    print("PASS explicit-registration")
    return 0


if __name__ == "__main__":
    entry("explicit-registration", main, errors=(OSError, json.JSONDecodeError))
