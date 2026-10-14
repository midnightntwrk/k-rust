#!/usr/bin/env python3
"""Generate documentation data from the semantics coverage ledger."""

from __future__ import annotations

import sys
import tomllib
from pathlib import Path
from typing import Any


SITE = Path(__file__).resolve().parent.parent
ROOT = SITE.parent / "krs"
LEDGER = ROOT / "semantics" / "coverage.toml"
OUTPUT = SITE / "src" / "pages" / "advanced" / "language-scale.mdx"
START = "{/* generated:port-coverage:start */}"
END = "{/* generated:port-coverage:end */}"

PORT_NAMES = {
    "kwasm": "KWasm",
    "kevm": "KEVM",
    "kmir": "KMIR",
}
SCALAR_FIELDS = (
    "package",
    "authority_commit",
    "authority_k_version",
    "source_files",
    "source_syntax_declarations",
    "source_rules",
    "krs_equations",
    "krs_machine_rules",
    "krs_claims",
    "pinned_executions",
    "complete",
)
LIST_FIELDS = ("implemented", "adapters", "deferred")


def require(port: dict[str, Any], field: str) -> Any:
    if field not in port:
        raise SystemExit(f"{port.get('id', 'unknown port')}: missing {field}")
    return port[field]


def load_coverage() -> list[dict[str, Any]]:
    with LEDGER.open("rb") as source:
        ledger = tomllib.load(source)

    if ledger.get("schema") != 1:
        raise SystemExit(f"unsupported semantics coverage schema: {ledger.get('schema')!r}")
    qualification_k_version = ledger.get("qualification_k_version")
    if not isinstance(qualification_k_version, str) or not qualification_k_version:
        raise SystemExit("semantics coverage ledger lacks qualification_k_version")

    ports = []
    seen = set()
    for port in ledger.get("port", []):
        port_id = require(port, "id")
        if port_id not in PORT_NAMES:
            raise SystemExit(f"unknown semantics port: {port_id}")
        if port_id in seen:
            raise SystemExit(f"duplicate semantics port: {port_id}")
        seen.add(port_id)

        generated = {
            "id": port_id,
            "name": PORT_NAMES[port_id],
            "qualificationKVersion": qualification_k_version,
        }
        for field in SCALAR_FIELDS:
            generated[field] = require(port, field)
        for field in LIST_FIELDS:
            values = require(port, field)
            if not isinstance(values, list) or not all(
                isinstance(value, str) and value for value in values
            ):
                raise SystemExit(f"{port_id}: {field} must be a list of nonempty strings")
            generated[field] = values
        ports.append(generated)

    missing = set(PORT_NAMES) - seen
    if missing:
        raise SystemExit(f"semantics coverage ledger omits ports: {sorted(missing)}")
    return ports


def plural(count: int, singular: str, plural_form: str | None = None) -> str:
    return singular if count == 1 else plural_form or f"{singular}s"


def render_inventory(title: str, values: list[str], empty: str) -> list[str]:
    lines = ["<details>", f"<summary>{len(values)} {title}</summary>", ""]
    if values:
        lines.extend(f"- {value}" for value in values)
    else:
        lines.append(empty)
    lines.extend(["", "</details>"])
    return lines


def render(ports: list[dict[str, Any]]) -> str:
    lines = [START]
    for port in ports:
        status = "complete" if port["complete"] else "incomplete"
        implemented_count = len(port["implemented"])
        claim_count = port["krs_claims"]
        lines.extend(
            [
                "",
                f"### {port['name']}",
                "",
                f"**Status: {status}.**",
                f"This extract contains {implemented_count} implemented coverage entries, {port['krs_equations']} equations, {port['krs_machine_rules']} machine rules, and {claim_count} {plural(claim_count, 'claim')}.",
                "",
                f"- Package: `{port['package']}`",
                f"- Pinned authority: K {port['authority_k_version']} at `{port['authority_commit']}`",
                f"- KRS qualification release: K {port['qualificationKVersion']}",
                f"- Authority inventory: {port['source_files']} source files, {port['source_syntax_declarations']} syntax declarations, and {port['source_rules']} rules",
                f"- Pinned executions: {port['pinned_executions']}",
                "",
            ]
        )
        lines.extend(
            render_inventory(
                "implemented coverage entries",
                port["implemented"],
                "No implemented coverage is recorded.",
            )
        )
        lines.append("")
        lines.extend(
            render_inventory(
                f"recorded adapter {plural(len(port['adapters']), 'boundary', 'boundaries')}",
                port["adapters"],
                "No adapter boundary is recorded.",
            )
        )
        lines.append("")
        lines.extend(
            render_inventory(
                "deferred areas",
                port["deferred"],
                "No deferred area is recorded.",
            )
        )
    lines.extend(["", END])
    return "\n".join(lines)


def main() -> None:
    arguments = sys.argv[1:]
    if len(arguments) > 1 or (arguments and arguments[0] not in {"--check", "--write"}):
        raise SystemExit("usage: sync-port-coverage.py [--check|--write]")

    generated = render(load_coverage())
    if not OUTPUT.is_file():
        raise SystemExit(f"coverage documentation page does not exist: {OUTPUT}")
    source = OUTPUT.read_text(encoding="utf-8")
    if source.count(START) != 1 or source.count(END) != 1:
        raise SystemExit("coverage documentation page must contain one generated marker pair")
    start = source.index(START)
    end = source.index(END, start) + len(END)
    current = source[start:end]

    if arguments == ["--write"]:
        OUTPUT.write_text(source[:start] + generated + source[end:], encoding="utf-8")
        print(f"updated {OUTPUT}")
        return
    if current != generated:
        raise SystemExit(
            "generated semantics port coverage documentation is stale; "
            "run `python3 scripts/sync-port-coverage.py --write`"
        )
    print("src/pages/advanced/language-scale.mdx port coverage is current")


if __name__ == "__main__":
    main()
