#!/usr/bin/env python3
"""Synchronize the documentation composition fixture from the M1 authority."""

from __future__ import annotations

import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
AUTHORITY = ROOT / "tests" / "m1" / "workspace" / "packages"
PACKAGES = ("base-semantics", "root-semantics")


def expected_files() -> dict[Path, str]:
    files: dict[Path, str] = {}
    for package in PACKAGES:
        for relative in (Path("Cargo.toml"), Path("src/lib.rs")):
            source = (AUTHORITY / package / relative).read_text(encoding="utf-8")
            if relative.name == "Cargo.toml":
                source = source.replace("../../../../../crates/krs", "../../../../crates/krs")
            elif package == "base-semantics":
                nested = source.index("pub mod nested {")
                collector = source.index(
                    "/// A reachable name used only to satisfy the current collector-entrypoint plan model."
                )
                source = source[:nested] + source[collector:]
                source = source.replace(
                    "#[k::sort]\npub trait Common: BaseItem {}",
                    '#[k::symbol("tour::BaseCommon")]\n#[k::sort]\npub trait Common: BaseItem {}',
                ).replace(
                    '#[k::constructor(sort = Common, syntax = "same-base")]\npub struct Same;',
                    '#[k::symbol("tour::BaseSame")]\n#[k::constructor(sort = Common, syntax = "same-base")]\npub struct Same;',
                ).replace(
                    "    #[k::sort]\n    pub trait Common {}",
                    '    #[k::symbol("tour::BaseNestedCommon")]\n    #[k::sort]\n    pub trait Common {}',
                ).replace(
                    '    #[k::constructor(sort = Common, syntax = "same-base-nested")]\n    pub struct Same;',
                    '    #[k::symbol("tour::BaseNestedSame")]\n    #[k::constructor(sort = Common, syntax = "same-base-nested")]\n    pub struct Same;',
                )
            elif package == "root-semantics":
                nested_rules = source.index("#[k::rule]\npub fn zero_bindings")
                cross_package = source.index("#[k::rule]\npub fn cross_package")
                source = source[:nested_rules] + source[cross_package:]
                nested_module = source.index("pub mod nested {")
                source = source[:nested_module]
                source = source.replace(
                    "use language_host as k;\nuse k::Term;",
                    "use k::Term;\nuse k::builtin::KSequence;\nuse language_host as k;",
                ).replace(
                    "k::term![nested::Keep { value: 日本, marker: nested::Done }]",
                    "k::term![nested::Keep {\n        value: 日本,\n        marker: nested::Done\n    }]",
                ).replace(
                    "#[k::sort]\npub trait Common: KItem {}",
                    '#[k::symbol("tour::RootCommon")]\n#[k::sort]\npub trait Common: KItem {}',
                ).replace(
                    '#[k::constructor(sort = Common, syntax = "same-root")]\npub struct Same;',
                    '#[k::symbol("tour::RootSame")]\n#[k::constructor(sort = Common, syntax = "same-root")]\npub struct Same;\n\n#[cfg(tour_mode = "extended")]\n#[k::constructor(sort = Common, syntax = "extended-root")]\npub struct Extended;',
                ).replace(
                    "    #[k::sort]\n    pub trait Common: KItem {}",
                    '    #[k::symbol("tour::RootNestedCommon")]\n    #[k::sort]\n    pub trait Common: KItem {}',
                ).replace(
                    '    #[k::constructor(sort = Common, syntax = "same-root-nested")]\n    pub struct Same;',
                    '    #[k::symbol("tour::RootNestedSame")]\n    #[k::constructor(sort = Common, syntax = "same-root-nested")]\n    pub struct Same;',
                )
                source = source.rstrip()
                source += """

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![Same] }
    }
}
"""
            source = source.rstrip() + "\n"
            files[HERE / "packages" / package / relative] = source
    return files


def main() -> None:
    write = "--write" in sys.argv
    stale: list[Path] = []
    for path, expected in expected_files().items():
        if write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected, encoding="utf-8")
            print(f"updated {path.relative_to(ROOT)}")
        elif not path.is_file() or path.read_text(encoding="utf-8") != expected:
            stale.append(path)
    if stale:
        names = ", ".join(str(path.relative_to(ROOT)) for path in stale)
        raise SystemExit(
            f"tour-composition sources are stale: {names}; run sync.py --write"
        )
    if not write:
        print("tour-composition sources current: two packages and manifests")


if __name__ == "__main__":
    main()
