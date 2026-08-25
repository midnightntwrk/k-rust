#!/usr/bin/env python3
"""Bounded JSON-KAST post-processor for the W1-A egress investigation.

The official K `--post-process` hook appends the input JSON filename to the
configured command and requires the transformed definition on stdout.  This
adapter deliberately supports only the exact experiment modes recorded here.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("expected top-level JSON object")
    if value.get("format") != "KAST" or value.get("version") != 4:
        raise ValueError("expected pinned KAST v4 envelope")
    return value


def walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def att_value(node: Any, key: str) -> Any | None:
    if not isinstance(node, dict):
        return None
    att = node.get("att")
    if not isinstance(att, dict):
        return None
    entries = att.get("att")
    if not isinstance(entries, dict):
        return None
    return entries.get(key)


def mutate_start_to_bump(definition: dict[str, Any]) -> None:
    """Change only P3's labeled startup rule from `start => read()+bump` to `start => bump`.

    This operates at the fully compiled boundary.  The target rule body has
    already been wrapped in generated cells.  We locate it by the surviving
    source label and replace the unique `add(read(), bump)` RHS subtree with
    its `bump` argument, preserving all rule/configuration wrappers and attrs.
    """

    targets = [node for node in walk(definition) if isinstance(node, dict) and att_value(node, "label") == "start-program"]
    if len(targets) != 1:
        raise ValueError(f"expected one start-program sentence, found {len(targets)}")
    target = targets[0]
    replacements = 0

    def transform(value: Any) -> Any:
        nonlocal replacements
        if isinstance(value, dict):
            raw_label = value.get("label")
            label = raw_label.get("name") if isinstance(raw_label, dict) else None
            args = value.get("args")
            if label == "add" and isinstance(args, list) and len(args) == 2:
                left, right = args
                if (
                    isinstance(left, dict)
                    and isinstance(left.get("label"), dict)
                    and left["label"].get("name") == "read"
                    and isinstance(right, dict)
                    and isinstance(right.get("label"), dict)
                    and right["label"].get("name") == "bump"
                ):
                    replacements += 1
                    return right
            return {key: transform(child) for key, child in value.items()}
        if isinstance(value, list):
            return [transform(child) for child in value]
        return value

    transformed = transform(target)
    if replacements != 1:
        raise ValueError(f"expected one startup RHS subtree, replaced {replacements}")
    target.clear()
    target.update(transformed)


def inject_empty_default_configuration(definition: dict[str, Any]) -> None:
    """Restore the module that emitted `parsed.json` trims but re-entry requires.

    `DefinitionParsing.parseDefinitionAndResolveBubbles` unconditionally looks
    up this module even when a fully parsed definition contains no bubbles.
    The module must be semantically empty here: importing generated default
    configuration sentences would conflict with the already-generated user
    configuration.
    """

    term = definition.get("term")
    if not isinstance(term, dict) or term.get("node") != "KDefinition":
        raise ValueError("expected KDefinition term")
    modules = term.get("modules")
    if not isinstance(modules, list):
        raise ValueError("expected definition modules")
    names = [module.get("name") for module in modules if isinstance(module, dict)]
    if "DEFAULT-CONFIGURATION" in names:
        raise ValueError("DEFAULT-CONFIGURATION already present")
    modules.append(
        {
            "node": "KFlatModule",
            "name": "DEFAULT-CONFIGURATION",
            "imports": [],
            "localSentences": [],
            "att": {"node": "KAtt", "att": {}},
        }
    )
    main_module_name = term.get("mainModule")
    main_modules = [module for module in modules if isinstance(module, dict) and module.get("name") == main_module_name]
    if len(main_modules) != 1:
        raise ValueError(f"expected one main module {main_module_name!r}, found {len(main_modules)}")
    imports = main_modules[0].get("imports")
    if not isinstance(imports, list):
        raise ValueError("expected main-module imports")
    imports.append({"node": "KImport", "name": "DEFAULT-CONFIGURATION", "isPublic": True})


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "mode",
        choices=(
            "identity",
            "p3-start-to-bump",
            "parsed-reentry-identity",
            "parsed-reentry-p3-start-to-bump",
        ),
    )
    parser.add_argument("input", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    definition = load(args.input)
    if args.mode.startswith("parsed-reentry-"):
        inject_empty_default_configuration(definition)
    if args.mode in ("p3-start-to-bump", "parsed-reentry-p3-start-to-bump"):
        mutate_start_to_bump(definition)
    json.dump(definition, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
