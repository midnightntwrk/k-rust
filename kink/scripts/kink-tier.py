#!/usr/bin/env python3
"""Run a test tier of the kink crates, check it against its budget, and lint tier membership.

    kink/scripts/kink-tier.py run TIER [--portable] [--no-budget] [--and EXPR] [-- NEXTEST_ARGS...]
    kink/scripts/kink-tier.py budget TIER JUNIT
    kink/scripts/kink-tier.py lint [--portable]

TIER is light, kink, heavy, gate (light and kink in one run) or all (every tier).
`--and EXPR` narrows the tier to the tests that also match the nextest filterset EXPR
(for example `--and 'package(kink-flow)'`); the budget is not judged on a narrowed run.
Every run selects the kink packages (`-p`, each package of kink/crates) and runs cargo at the
root of k-rust's workspace. The default is the Z3 profile, the kink packages' default features
(less the binaries of `[z3] skip_binaries` in kink/.config/kink-tiers.toml). Z3 is acquired as
k-rust's gates acquire it (docs/testing.md): by default k-rust's `z3-inference-gh-release`
downloads the Z3 release at build time; with `KRUST_GATE_Z3=system` the build links the Z3 the
build environment provides, for example under `with-z3-static-4.16.0`.
`--portable` runs the portable (no-Z3) profile, the kink packages with `--no-default-features`.
The JUnit report is read from nextest's store directory (`target/nextest` under the workspace root,
which nextest keeps there even when `CARGO_TARGET_DIR` moves cargo's build output).
The tiers, the module convention and the budgets are documented in kink/.config/kink-tiers.toml.
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

# kink's directory inside k-rust, and the root of k-rust's workspace, where cargo runs.
ROOT = Path(__file__).resolve().parent.parent
WORKSPACE = ROOT.parent
CONFIG = ROOT / ".config" / "kink-tiers.toml"
NEXTEST = WORKSPACE / ".config" / "nextest.toml"
# The nextest profile of the tier runs (WORKSPACE/.config/nextest.toml), which writes the report.
PROFILE = "kink"
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


def junit():
    """The JUnit report of a tier run, in nextest's store directory: `[store] dir` of the root
    nextest configuration, by default `target/nextest` under the workspace root. nextest keeps it
    there whatever CARGO_TARGET_DIR says (cargo-nextest 0.9.143), so a run with another cargo
    target directory still writes its report under the workspace's own `target/`."""
    with NEXTEST.open("rb") as f:
        store = tomllib.load(f).get("store", {}).get("dir", "target/nextest")
    return WORKSPACE / store / PROFILE / "junit.xml"


def config():
    with CONFIG.open("rb") as f:
        return tomllib.load(f)


def kink_packages():
    """The kink packages: the package of each directory of kink/crates."""
    names = []
    for manifest in sorted((ROOT / "crates").glob("*/Cargo.toml")):
        with manifest.open("rb") as f:
            names.append(tomllib.load(f)["package"]["name"])
    return names


def selection(tier, portable, cfg, narrow=None):
    """The nextest arguments that select TIER, narrowed to NARROW if given."""
    packages = [arg for p in kink_packages() for arg in ("-p", p)]
    z3 = not portable
    if portable:
        packages += ["--no-default-features"]
    elif os.environ.get("KRUST_GATE_Z3") != "system":
        packages += ["--features", "k-rust/z3-inference-gh-release"]
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
    portable = "--portable" in argv
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
    command = ["cargo", "nextest", "run", "--profile", PROFILE, "--no-fail-fast"]
    command += selection(tier, portable, cfg, narrow) + extra
    print("+", " ".join(command), flush=True)
    start = busy()
    began = time.monotonic()
    report = junit()
    if report.exists():
        report.unlink()
    status = subprocess.call(command, cwd=WORKSPACE)
    print(f"kink-tier {tier}{' (portable)' if portable else ''}: exit {status}, "
          f"{time.monotonic() - began:.1f} s including the build", flush=True)
    if not check or tier == "all":
        return status
    if report.exists():
        kept = report.with_name(f"junit-{tier}{'-portable' if portable else ''}.xml")
        shutil.copyfile(report, kept)
        print(f"kink-tier: JUnit report kept at {kept}")
    return status or budget(tier, report, cfg, [start, busy()])


def lint(argv):
    portable = "--portable" in argv
    cfg = config()
    packages = selection("light", portable, cfg)[:-2]
    listed = subprocess.run(
        ["cargo", "nextest", "list", *packages, "--run-ignored", "all",
         "--message-format", "json", "-E", KINK],
        cwd=WORKSPACE, check=True, stdout=subprocess.PIPE, text=True,
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
    # An override whose filter matches no test (a test renamed or moved into a tier module) would
    # silently stop applying its group or timeout. Checked in either profile, each of which lists
    # every kink package; k-rust's own overrides name no kink package and are left out.
    with NEXTEST.open("rb") as f:
        overrides = tomllib.load(f).get("profile", {}).get("default", {}).get("overrides", [])
    for override in overrides:
        if "kink-" not in override["filter"]:
            continue
        matched = subprocess.run(
            ["cargo", "nextest", "list", *packages, "--run-ignored", "all",
             "--message-format", "json", "-E", override["filter"]],
            cwd=WORKSPACE, check=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
        ).stdout
        if not any(case["filter-match"]["status"] == "matches"
                   for suite in json.loads(matched)["rust-suites"].values()
                   for case in suite["testcases"].values()):
            problems.append(f"{NEXTEST.relative_to(WORKSPACE)} override matches no test: "
                            f"{override['filter']}")
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
