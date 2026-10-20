#!/usr/bin/env python3
"""Run a test tier of the kink crates, check it against its budget, and lint tier membership.

    scripts/kink-tier.py run TIER [--z3] [--no-budget] [--and EXPR] [-- NEXTEST_ARGS...]
    scripts/kink-tier.py budget TIER JUNIT
    scripts/kink-tier.py lint [--z3]

TIER is light, kink, heavy, gate (light and kink in one run) or all (every tier).
`--and EXPR` narrows the tier to the tests that also match the nextest filterset EXPR
(for example `--and 'package(kink-flow)'`); the budget is not judged on a narrowed run.
`--z3` runs the Z3 profile: the packages and skipped binaries of `[z3]` in
.config/kink-tiers.toml, with `--features z3`; run it under `with-z3-static-4.16.0`.
The tiers, the module convention and the budgets are documented in .config/kink-tiers.toml.
"""

import json
import os
import shutil
import subprocess
import sys
import time
import tomllib
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIG = ROOT / ".config" / "kink-tiers.toml"
JUNIT = ROOT / "target" / "nextest" / "ci" / "junit.xml"
KINK = "package(/^kink-/)"
TIER_MODULES = {"kink": "kink_tier", "heavy": "heavy", "external": "external"}


def module_filter(module):
    return f"test(/(^|::){module}::/)"


def tier_of(name):
    """The tier of a test from its path: the first tier module it is inside, else light."""
    parts = name.split("::")[:-1]
    for tier, module in TIER_MODULES.items():
        if module in parts:
            return tier
    return "light"


def config():
    with CONFIG.open("rb") as f:
        return tomllib.load(f)


def selection(tier, z3, cfg, narrow=None):
    """The nextest arguments that select TIER, narrowed to NARROW if given."""
    if z3:
        packages = [arg for p in cfg["z3"]["packages"] for arg in ("-p", p)]
        packages += ["--features", "z3"]
    else:
        packages = ["--workspace"]
    expr = KINK
    heavy, kink, external = (module_filter(TIER_MODULES[t]) for t in ("heavy", "kink", "external"))
    if tier == "light":
        ignored = []
    elif tier == "kink":
        ignored, expr = ["--run-ignored", "only"], f"{expr} & {kink}"
    elif tier == "heavy":
        ignored, expr = ["--run-ignored", "only"], f"{expr} & {heavy}"
    elif tier == "gate":
        ignored, expr = ["--run-ignored", "all"], f"{expr} & not {heavy} & not {external}"
    elif tier == "all":
        ignored, expr = ["--run-ignored", "all"], f"{expr} & not {external}"
    else:
        sys.exit(f"unknown tier {tier!r}: light, kink, heavy, gate or all")
    if z3 and tier != "heavy" and cfg["z3"]["skip_binaries"]:
        skipped = " | ".join(f"binary_id({b})" for b in cfg["z3"]["skip_binaries"])
        expr = f"{expr} & not ({skipped})"
    if narrow:
        expr = f"({expr}) & ({narrow})"
    return packages + ignored + ["-E", expr]


def busy():
    load = os.getloadavg()[0]
    return load, load > (os.cpu_count() or 1) / 2


def budget(tier, junit, cfg, loads):
    """Check a JUnit report against TIER's budget; return the exit status."""
    try:
        root = ET.parse(junit).getroot()
    except (OSError, ET.ParseError) as e:
        print(f"kink-tier budget: no readable JUnit report at {junit}: {e}", file=sys.stderr)
        return 1
    cases = [
        (float(c.get("time", "0")), f"{c.get('classname')} {c.get('name')}")
        for c in root.iter("testcase")
        if c.find("skipped") is None
    ]
    if not cases:
        print("kink-tier budget: the report holds no test that ran", file=sys.stderr)
        return 1
    wall = float(root.get("time", "0"))
    limits = cfg["tier"][tier]
    over = []
    if wall > limits["wall_s"]:
        over.append(f"wall {wall:.1f} s over the {tier} budget of {limits['wall_s']} s")
    bound = cfg["tier"]["light"]["per_test_s"]
    for seconds, name in cases:
        light = tier_of(name.split(" ", 1)[1]) == "light"
        if (tier in ("light", "gate", "all") and light) and seconds > bound:
            over.append(f"light test over {bound} s: {name} ({seconds:.1f} s)")
    cases.sort(reverse=True)
    print(f"kink-tier {tier}: {len(cases)} tests, wall {wall:.1f} s (budget {limits['wall_s']} s), "
          f"summed {sum(s for s, _ in cases):.0f} s, load {loads}, {os.cpu_count()} CPUs")
    print("slowest:")
    for seconds, name in cases[:20]:
        print(f"  {seconds:8.1f} s  {name}")
    if not over:
        return 0
    for line in over:
        print(f"OVER BUDGET: {line}", file=sys.stderr)
    if any(b for _, b in loads):
        print("kink-tier budget: the host was busy (load over half the CPUs), so the budget is "
              "reported, not judged", file=sys.stderr)
        return 0
    return 1


def run(argv):
    z3 = "--z3" in argv
    check = "--no-budget" not in argv
    extra = argv[argv.index("--") + 1:] if "--" in argv else []
    own = argv[:argv.index("--")] if "--" in argv else argv
    narrow = None
    if "--and" in own:
        at = own.index("--and")
        if at + 1 >= len(own):
            sys.exit(__doc__)
        narrow = own[at + 1]
        own = own[:at] + own[at + 2:]
        check = False
    positional = [a for a in own if not a.startswith("--")]
    if len(positional) != 1:
        sys.exit(__doc__)
    tier, cfg = positional[0], config()
    command = ["cargo", "nextest", "run", "--profile", "ci", "--no-fail-fast"]
    command += selection(tier, z3, cfg, narrow) + extra
    print("+", " ".join(command), flush=True)
    start = busy()
    began = time.monotonic()
    status = subprocess.call(command, cwd=ROOT)
    print(f"kink-tier {tier}{' (z3)' if z3 else ''}: exit {status}, "
          f"{time.monotonic() - began:.1f} s including the build", flush=True)
    if not check or tier == "all":
        return status
    if JUNIT.exists():
        kept = JUNIT.with_name(f"junit-{tier}{'-z3' if z3 else ''}.xml")
        shutil.copyfile(JUNIT, kept)
        print(f"kink-tier: JUnit report kept at {kept}")
    return status or budget(tier, JUNIT, cfg, [start, busy()])


def lint(argv):
    z3 = "--z3" in argv
    cfg = config()
    packages = selection("light", z3, cfg)[:-2]
    listed = subprocess.run(
        ["cargo", "nextest", "list", *packages, "--run-ignored", "all",
         "--message-format", "json", "-E", KINK],
        cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True,
    ).stdout
    problems, counts = [], {}
    for binary, suite in json.loads(listed)["rust-suites"].items():
        for name, case in suite["testcases"].items():
            if case["filter-match"]["status"] != "matches":
                continue
            tier = tier_of(name)
            counts[tier] = counts.get(tier, 0) + 1
            if case["ignored"] and tier == "light":
                problems.append(f"{binary} {name}: ignored outside a kink_tier, heavy or external "
                                "module, so no tier runs it")
            if not case["ignored"] and tier != "light":
                problems.append(f"{binary} {name}: inside a {TIER_MODULES[tier]} module but not "
                                "ignored, so the light tier runs it")
    print("kink-tier lint:", ", ".join(f"{t} {n}" for t, n in sorted(counts.items())))
    for line in problems:
        print(f"LINT: {line}", file=sys.stderr)
    return 1 if problems else 0


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    command, argv = sys.argv[1], sys.argv[2:]
    if command == "run":
        return run(argv)
    if command == "budget" and len(argv) == 2:
        cfg = config()
        return budget(argv[0], Path(argv[1]), cfg, [busy()])
    if command == "lint":
        return lint(argv)
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.exit(main())
