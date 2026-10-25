# The claims area's registry (tests/gate-check.py loads it; the gate phases are in claims.sh).
# The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    # on ImpRel and kimp-claims-ps, both per-sort (ImpRel is a holdout of the relational area)
    "ImpRelClaims": {"tier": "heavy", "encoding": "per-sort", "sources": ["demos/ImpRelClaims/ImpRelClaims/Transfers.lean"]},
    # on ImpUnroll and kimp-claims-ps, both per-sort (ImpUnroll is a holdout of the relational area)
    "ImpUnrollClaims": {"tier": "heavy", "encoding": "per-sort", "sources": ["demos/ImpUnrollClaims/ImpUnrollClaims/Transfers.lean"]},
}


def measure_claims(c):
    """kimp's claims (claims.toml), kimpinv's (claims-inv.toml), their guards and kc_auto lines."""
    ct = read(c.meas / "claims.toml")
    ci = read(c.meas / "claims-inv.toml")
    ax = read(c.meas / "axioms.txt")
    kc = read(c.meas / "kc-auto-stats.txt")
    return {"claims": len(re.findall(r"^\[\[claim\]\]", ct, re.M)) if ct else None,
            "stated": len(re.findall(r"^stated = true", ct, re.M)) if ct else None,
            "inv_stated": len(re.findall(r"^stated = true", ci, re.M)) if ci else None,
            "induction_obligations": sum(int(x) for x in re.findall(r"^obligations = (\d+)", ct, re.M)) if ct else None,
            "guarded": len([l for l in ax.splitlines() if l.strip()]) if ax else None,
            "kc_auto": len([l for l in kc.splitlines() if "kc_auto" in l]) if kc else None,
            "kc_auto_open": sum(int(x) for x in re.findall(r"(\d+) open", kc)) if kc else None}


RECORDS = {
    # on kimp and kimpinv (the arity universe); kimp-claims-ps is the same modules over kimp-ps
    "claims": {"tier": "heavy", "measure": measure_claims,
               "sources": ["generated/kimp-claims", "generated/kimp-claims-ps", "generated/kimpinv-claims"]},
}

OUTPUTS = {
    "claims.toml": {"tier": "heavy", "compare": "exact"},
    "claims-inv.toml": {"tier": "heavy", "compare": "exact"},
    "kprove.txt": {"tier": "heavy", "compare": "exact"},
    "kc-auto-stats.txt": {"tier": "heavy", "compare": "sorted-lines"},  # Lake replays logs in build order
    "axioms.txt": {"tier": "heavy", "compare": "axiom-sets"},
    "replay/addition-2.toml": {"tier": "heavy", "compare": "strip-seconds"},
    "replay/branching.toml": {"tier": "heavy", "compare": "strip-seconds"},
    "replay/sum-loop.toml": {"tier": "heavy", "compare": "strip-seconds"},
}
