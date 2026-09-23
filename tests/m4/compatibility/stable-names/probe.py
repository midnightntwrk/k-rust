#!/usr/bin/env python3
"""Fail-closed static capability probe for the R10 stable-name move gate."""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from support import ROOT, GateError  # noqa: E402
from support.process import run  # noqa: E402


HERE = Path(__file__).resolve().parent
PROBE_TARGET = {"CARGO_TARGET_DIR": "/tmp/krs-m4-stable-probe-target"}


def capability_report(root: Path = ROOT) -> dict[str, object]:
    bundle = (root / "crates/krs-ir/src/bundle.rs").read_text(encoding="utf-8")
    facade = (root / "crates/krs/src/lib.rs").read_text(encoding="utf-8")
    macros = (root / "crates/krs-macros/src/lib.rs").read_text(encoding="utf-8")
    identity = (root / "crates/krs-ir/src/identity.rs").read_text(encoding="utf-8")
    lowering = (root / "crates/krs-compiler/src/lowering.rs").read_text(encoding="utf-8")
    fixtures = {
        name: (HERE / name / "src/lib.rs").is_file()
        for name in ("baseline", "private-move", "public-move", "public-move-pinned")
    }
    return {
        "schema": 1,
        "fixtures": fixtures,
        "stable_id_has_module_path": "module_path: Vec<String>" in identity,
        "descriptor_has_visibility": all(token in bundle for token in (
            "pub declarations: Vec<DescriptorDeclaration>",
            "pub visibility: RustVisibility",
            "pub explicit_symbol: Option<ExplicitSymbol>",
        )) and "pub enum RustVisibility" in identity,
        "symbol_macro_exported": "pub fn symbol(" in macros and "symbol," in facade,
        "explicit_symbol_lowered": all(token in lowering for token in (
            "fn stable_symbol_text(", ".explicit_symbol()", ".final_component()",
        )),
    }


FIXTURE_PACKAGES = {
    "baseline": "krs-m4-stable-baseline",
    "private-move": "krs-m4-stable-private-move",
    "public-move": "krs-m4-stable-public-move",
    "public-move-pinned": "krs-m4-stable-public-move-pinned",
}


def normalized_descriptor(descriptor: dict[str, object]) -> dict[str, object]:
    value = copy.deepcopy(descriptor)

    def visit(node: object) -> object:
        if isinstance(node, list):
            return [visit(child) for child in node]
        if not isinstance(node, dict):
            return node
        result = {}
        for key, child in node.items():
            if key == "provenance":
                continue
            if key == "package" and isinstance(child, dict):
                result[key] = {"k_namespace": child.get("k_namespace")}
            else:
                result[key] = visit(child)
        return result

    normalized = visit(value)
    assert isinstance(normalized, dict)
    return normalized


def descriptor_bundle_fixture(krs: Path, name: str) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix=f"krs-m4-stable-{name}-", dir="/tmp") as temporary:
        output = Path(temporary) / "emit"
        process = run(
            [
                krs, "emit-k", "--manifest-path", HERE / name / "Cargo.toml",
                "--package", FIXTURE_PACKAGES[name], "--definition", "main",
                "--backend", "llvm", "--output", output,
            ],
            environment=PROBE_TARGET,
            timeout=180,
            check=False,
        )
        if process.returncode != 0:
            raise GateError(f"{name} descriptor emission failed: {process.stderr[:1200]}")
        try:
            value = json.loads(
                (output / "descriptor-bundle.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError) as error:
            raise GateError(f"{name} descriptor bundle is invalid: {error}") from error
    if set(value) != {"protocol_version", "descriptors", "declarations"}:
        raise GateError(f"{name} descriptor bundle has an unknown envelope")
    if not isinstance(value["descriptors"], list) or not isinstance(value["declarations"], list):
        raise GateError(f"{name} descriptor bundle has non-list descriptor data")
    if len(value["descriptors"]) != len(value["declarations"]):
        raise GateError(f"{name} declaration metadata does not cover every descriptor")
    return value


def emit_fixture(krs: Path, name: str, backend: str, output: Path) -> dict[str, object]:
    process = run(
        [
            krs, "emit-k", "--manifest-path", HERE / name / "Cargo.toml",
            "--package", FIXTURE_PACKAGES[name], "--definition", "main",
            "--backend", backend, "--output", output,
        ],
        environment=PROBE_TARGET,
        timeout=180,
        check=False,
    )
    if process.returncode != 0:
        raise GateError(f"{name}/{backend} emission failed: {process.stderr[:1200]}")
    try:
        value = json.loads((output / "symbols.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise GateError(f"{name}/{backend} symbols sidecar is invalid: {error}") from error
    if set(value) != {"schema_version", "entries"} or not isinstance(value["entries"], list):
        raise GateError(f"{name}/{backend} symbols sidecar has an unknown envelope")
    return value


def move_evidence(krs: Path) -> dict[str, object]:
    bundles = {name: descriptor_bundle_fixture(krs, name) for name in FIXTURE_PACKAGES}

    def stable_key(descriptor: dict[str, object]) -> tuple[tuple[str, ...], str, str]:
        identity = descriptor["id"]
        return (tuple(identity["module_path"]), identity["item_name"], identity["item_kind"])

    def declarations(name: str) -> dict[tuple[tuple[str, ...], str, str], dict[str, object]]:
        return {stable_key(value): value for value in bundles[name]["declarations"]}

    def public_projection(name: str) -> list[dict[str, object]]:
        public = {
            stable_key(declaration)
            for declaration in bundles[name]["declarations"]
            if declaration.get("visibility") == {"visibility": "public"}
        }
        return sorted(
            (
                normalized_descriptor(descriptor)
                for descriptor in bundles[name]["descriptors"]
                if stable_key(descriptor) in public
            ),
            key=lambda descriptor: json.dumps(descriptor, sort_keys=True),
        )

    def stable_symbol_projection(sidecar: dict[str, object]) -> list[dict[str, object]]:
        selected = [
            {
                "identity": entry["identity"],
                "emitted_name": entry["emitted_name"],
                "symbol_kind": entry.get("symbol_kind"),
            }
            for entry in sidecar["entries"]
            if entry.get("emitted_name") in {"Expr", "publicValue"}
        ]
        if len(selected) != 2:
            raise GateError("stable-name sidecar must expose exactly Expr and publicValue")
        return sorted(selected, key=lambda entry: json.dumps(entry, sort_keys=True))

    def stable_symbol_source_keys(sidecar: dict[str, object]) -> list[str]:
        keys = [
            entry["source_map_key"] for entry in sidecar["entries"]
            if entry.get("emitted_name") in {"Expr", "publicValue"}
        ]
        if len(keys) != 2 or not all(isinstance(key, str) for key in keys):
            raise GateError("stable-name sidecar lacks exact public source-map keys")
        return sorted(keys)

    baseline_keys = {stable_key(value) for value in bundles["baseline"]["descriptors"]}
    private_keys = {stable_key(value) for value in bundles["private-move"]["descriptors"]}
    public_keys = {stable_key(value) for value in bundles["public-move"]["descriptors"]}
    baseline_private = {key for key in baseline_keys if key[0] == ("internal_old",)}
    moved_private = {key for key in private_keys if key[0] == ("internal_new",)}
    baseline_public = {key for key in baseline_keys if key[0] == ("api",)}
    moved_public = {key for key in public_keys if key[0] == ("moved_api",)}
    pinned_keys = {stable_key(value) for value in bundles["public-move-pinned"]["descriptors"]}
    pinned_public = {key for key in pinned_keys if key[0] == ("moved_api",)}
    pinned_declarations = declarations("public-move-pinned")
    pinned_symbols = {
        key: declaration.get("explicit_symbol")
        for key, declaration in pinned_declarations.items()
        if key[0] == ("moved_api",) and declaration.get("explicit_symbol") is not None
    }

    with tempfile.TemporaryDirectory(prefix="krs-m4-stable-", dir="/tmp") as temporary:
        temporary = Path(temporary)
        sidecars = {
            name: emit_fixture(krs, name, "llvm", temporary / f"{name}-llvm")
            for name in FIXTURE_PACKAGES
        }
        baseline_haskell = emit_fixture(
            krs, "baseline", "haskell", temporary / "baseline-haskell"
        )
        projections = {
            name: stable_symbol_projection(sidecar) for name, sidecar in sidecars.items()
        }
        source_keys = {
            name: stable_symbol_source_keys(sidecar) for name, sidecar in sidecars.items()
        }

    return {
        "baseline_descriptors": len(bundles["baseline"]["descriptors"]),
        "exact_public_visibility_recovered": len([
            declaration for declaration in bundles["baseline"]["declarations"]
            if declaration.get("visibility") == {"visibility": "public"}
        ]) == 3,
        "private_move_public_projection_equal": (
            public_projection("baseline") == public_projection("private-move")
        ),
        "private_internal_identity_changed": bool(baseline_private and moved_private)
            and baseline_private != moved_private,
        "public_identity_change_detected": bool(baseline_public and moved_public)
            and baseline_public != moved_public,
        "pinned_descriptor_provenance_moved": bool(baseline_public and pinned_public)
            and baseline_public != pinned_public,
        "pinned_exact_symbols_recovered": set(pinned_symbols.values())
            == {"api::Expr", "api::PublicValue"},
        "package_version_and_fixture_path_do_not_change_public_symbol": (
            projections["baseline"] == projections["private-move"]
        ),
        "unpinned_public_move_changes_symbol_identity": (
            projections["baseline"] != projections["public-move"]
        ),
        "pinned_reordered_public_move_preserves_symbol_identity": (
            projections["baseline"] == projections["public-move-pinned"]
        ),
        "pinned_move_preserves_distinct_provenance": (
            source_keys["baseline"] != source_keys["public-move-pinned"]
        ),
        "backend_selection_does_not_change_symbols": (
            sidecars["baseline"] == baseline_haskell
        ),
    }


def verify(report: dict[str, object]) -> None:
    fixtures = report.get("fixtures")
    if not isinstance(fixtures, dict) or not fixtures or not all(fixtures.values()):
        raise GateError("all four stable-name move fixtures are required")
    if report.get("stable_id_has_module_path") is not True:
        raise GateError("StableItemId no longer carries a canonical module path")
    blockers = []
    if report.get("descriptor_has_visibility") is not True:
        blockers.append("descriptor visibility is absent")
    if report.get("symbol_macro_exported") is not True:
        blockers.append("author-facing #[k::symbol] is absent")
    if report.get("explicit_symbol_lowered") is not True:
        blockers.append("explicit stable symbols do not reach the lowering naming pass")
    if blockers:
        raise GateError("; ".join(blockers))
    evidence = report.get("move_evidence")
    if evidence is not None:
        if not isinstance(evidence, dict):
            raise GateError("move evidence has an unknown shape")
        failed = sorted(
            key for key, value in evidence.items()
            if key != "baseline_descriptors" and value is not True
        )
        if evidence.get("baseline_descriptors") != 6 or failed:
            raise GateError(f"stable-name move evidence failed: {failed}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report-only", action="store_true")
    parser.add_argument("--krs", type=Path)
    arguments = parser.parse_args()
    report = capability_report()
    if arguments.krs:
        report["move_evidence"] = move_evidence(arguments.krs.resolve())
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    if not arguments.report_only:
        verify(report)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"BLOCKED stable names: {error}", file=sys.stderr)
        raise SystemExit(1)
