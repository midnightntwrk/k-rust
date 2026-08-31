#!/usr/bin/env python3
"""Generate the release baseline displayed by the tour from Krs.lock."""

from __future__ import annotations

from pathlib import Path
import sys
import tomllib


SITE = Path(__file__).resolve().parent.parent
ROOT = SITE.parent
LOCK = ROOT / "Krs.lock"
OUTPUT = SITE / "src" / "pages" / "index.mdx"
START = "{/* generated:compatibility:start */}"
END = "{/* generated:compatibility:end */}"


def render() -> str:
    with LOCK.open("rb") as source:
        lock = tomllib.load(source)
    required = {
        "schema": lock.get("schema"),
        "descriptor": lock.get("schemas", {}).get("descriptor_protocol"),
        "definition": lock.get("schemas", {}).get("definition_ir"),
        "msrv": lock.get("cargo", {}).get("msrv"),
        "k": lock.get("k", {}).get("version"),
        "k_commit": lock.get("k", {}).get("commit"),
        "k_rust": lock.get("k_rust", {}).get("version"),
        "k_rust_commit": lock.get("k_rust", {}).get("commit"),
        "solver": lock.get("solver", {}).get("version"),
    }
    missing = [name for name, value in required.items() if value in (None, "")]
    if missing:
        raise SystemExit(f"Krs.lock omits compatibility fields: {missing}")
    if required["schema"] != 1:
        raise SystemExit(f"unsupported Krs.lock schema: {required['schema']!r}")
    return "\n".join(
        [
            START,
            "",
            ":::info Current checked baseline",
            f"This tour targets KRS descriptor protocol **{required['descriptor']}**, Definition IR **{required['definition']}**, K **{required['k']}**, and k-rust **{required['k_rust']}**.",
            "The values are generated from `Krs.lock`; examples outside this baseline are not silently treated as equivalent.",
            ":::",
            "",
            "| Boundary | Checked compatibility |",
            "| --- | --- |",
            f"| Authoring toolchain | Rust {required['msrv']} or newer within the repository's qualified range |",
            f"| Descriptor protocol | Schema {required['descriptor']} |",
            f"| Definition IR | Schema {required['definition']} |",
            f"| K toolchain | {required['k']} at `{required['k_commit']}` |",
            f"| Native frontend | k-rust {required['k_rust']} at `{required['k_rust_commit']}` |",
            f"| Solver profile | Z3 {required['solver']} |",
            "",
            END,
        ]
    )


def main() -> None:
    if sys.argv[1:] not in ([], ["--check"], ["--write"]):
        raise SystemExit("usage: sync-compatibility.py [--check|--write]")
    generated = render()
    source = OUTPUT.read_text(encoding="utf-8")
    if source.count(START) != 1 or source.count(END) != 1:
        raise SystemExit("index page must contain one compatibility marker pair")
    start = source.index(START)
    end = source.index(END, start) + len(END)
    if sys.argv[1:] == ["--write"]:
        OUTPUT.write_text(source[:start] + generated + source[end:], encoding="utf-8")
        print(f"updated {OUTPUT}")
    elif source[start:end] != generated:
        raise SystemExit(
            "generated compatibility baseline is stale; run "
            "`python3 scripts/sync-compatibility.py --write`"
        )
    else:
        print("src/pages/index.mdx compatibility baseline is current")


if __name__ == "__main__":
    main()
