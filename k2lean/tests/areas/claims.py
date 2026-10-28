# The claims area's registry (tests/gate-check.py loads it; the gate phases are in claims.sh).
# The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    # on ImpRel and kimp-claims (the arity universe)
    "ImpRelClaims": {"tier": "heavy", "sources": ["demos/ImpRelClaims/ImpRelClaims/Transfers.lean"]},
    # on ImpUnroll and kimp-claims (the arity universe)
    "ImpUnrollClaims": {"tier": "heavy", "sources": ["demos/ImpUnrollClaims/ImpUnrollClaims/Transfers.lean"]},
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


def measure_impplus(c):
    """IMP++'s claims (claims-impplus.toml), their guard and kc_auto lines."""
    ct = read(c.meas / "claims-impplus.toml")
    ax = read(c.meas / "axioms-impplus.txt")
    kc = read(c.meas / "kc-auto-impplus.txt")
    return {"claims": len(re.findall(r"^\[\[claim\]\]", ct, re.M)) if ct else None,
            "stated": len(re.findall(r"^stated = true", ct, re.M)) if ct else None,
            "guarded": len([l for l in ax.splitlines() if l.strip()]) if ax else None,
            "kc_auto": len([l for l in kc.splitlines() if "kc_auto" in l]) if kc else None,
            "kc_auto_open": sum(int(x) for x in re.findall(r"(\d+) open", kc)) if kc else None}


RECORDS = {
    # on kimp and kimpinv (the arity universe)
    "claims": {"tier": "heavy", "measure": measure_claims,
               "sources": ["generated/kimp-claims", "generated/kimpinv-claims"]},
    # on impplus (the soundness area's library; a `Step` that is not a function)
    "impplus-claims": {"tier": "light", "measure": measure_impplus,
                       "sources": ["generated/impplus-claims"]},
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
    "claims-impplus.toml": {"tier": "light", "compare": "exact"},
    "kc-auto-impplus.txt": {"tier": "light", "compare": "sorted-lines"},
}
