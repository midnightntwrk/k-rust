# The core area's registry (tests/gate-check.py loads it; the gate phases are in core.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "kimp": {"ns": "KImp", "tier": "light", "not_regenerated": ["KImpBench/Programs.lean"]},
    "kimp-d2": {"ns": "KImp", "tier": "light", "not_regenerated": ["KImpBench/Programs.lean"]},
    "krsimp": {"ns": "KrsImp", "tier": "light"},
    "ovl": {"ns": "KOvl", "tier": "light", "not_regenerated": ["KOvlBench/Programs.lean"]},
    "ens": {"ns": "KEns", "tier": "light"},
    "freekey": {"ns": "FreeKey", "tier": "light"},
    "symcoll": {"ns": "SymColl", "tier": "light"},
    "alias": {"ns": "KAlias", "tier": "light"},
    "simple": {"ns": "KSimple", "tier": "heavy"},
    "kterm-ar": {"ns": "KTerm", "tier": "light"},
}


def measure_unit(c):
    # the failures are checked from the run itself (none may fail), so only the count is recorded
    return {"passed": c.run.get("unit_passed")}


def measure_kimp(c):
    """kimp's goldens and step traces (kimp-test.out, written by kimp's test driver)."""
    out = read(c.meas / "kimp-test.out") or ""
    gm = re.search(r"^goldens: (\d+)/(\d+) pass", out, re.M)
    return {
        "goldens_pass": int(gm.group(1)) if gm else None,
        "goldens_total": int(gm.group(2)) if gm else None,
        "trace_states": sum(int(x) for x in re.findall(r"^PASS trace .*?: (\d+) configurations equal", out, re.M)) if out else None,
        "trace_failures": len(re.findall(r"^FAIL trace", out, re.M)) if out else None,
    }


def measure_simple(c):
    """SIMPLE's cases against krust (simple-acceptance.toml, written by simple's run)."""
    acc = read(c.meas / "simple-acceptance.toml")
    return {"cases": len(re.findall(r"^\[\[case\]\]", acc, re.M)) if acc else None,
            "lean_eq_krust": len(re.findall(r'^lean_vs_krust = "pass"', acc, re.M)) if acc else None,
            "lean_out_eq_out": len(re.findall(r'^lean_vs_out = "pass"', acc, re.M)) if acc else None}


# `unit` is the generator's test count, measured by every tier (gate-check.py compares it itself)
RECORDS = {
    "unit": {"tier": "light", "measure": measure_unit},
    "kimp": {"tier": "light", "measure": measure_kimp},
    "simple": {"tier": "heavy", "measure": measure_simple},
}

OUTPUTS = {
    "goldens.toml": {"tier": "light", "compare": "exact"},
    "kimp-test.out": {"tier": "light", "compare": "exact"},
    "simple-acceptance.toml": {"tier": "heavy", "compare": "strip-ms"},
    "simple-acceptance.md": {"tier": "heavy", "compare": "strip-ms"},
}
