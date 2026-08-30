#!/usr/bin/env python3
"""Generate KMIR's concrete initial KORE from a pinned SMIR file."""

from __future__ import annotations

import argparse
from pathlib import Path

from kmir.kast import ConcreteMode, make_call_config
from kmir.kmir import KMIR
from kmir.smir import SMIRInfo
from pyk.kast.inner import KSort


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("definition", type=Path)
    parser.add_argument("smir", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    smir_info = SMIRInfo.from_file(args.smir).reduce_to("main")
    kmir = KMIR(args.definition)
    cell_maps = kmir._make_smir_maps(smir_info)
    config, _ = make_call_config(
        kmir.definition,
        smir_info=smir_info,
        start_symbol="main",
        mode=ConcreteMode(),
        cell_maps=cell_maps,
    )
    initial = kmir.kast_to_kore(config, KSort("GeneratedTopCell"))
    args.output.write_text(initial.text)


if __name__ == "__main__":
    main()
