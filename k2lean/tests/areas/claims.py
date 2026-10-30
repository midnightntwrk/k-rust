# The claims area's registry (tests/gate-check.py loads it; the gate phases are in claims.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    # a strict operator in a `Step` that is not a function (demos/claims/specs/strict.k)
    "kstrict": {"ns": "KStrict", "tier": "light"},
    # tables of equations of several priorities, a decoder of bit patterns over a table of registers
    # and an independent table (tests/fixtures/prio/prio.k)
    "kprio": {"ns": "KPrio", "tier": "light"},
}

DEMOS = {
    # on ImpRel and kimp-claims (the arity universe)
    "ImpRelClaims": {"tier": "heavy", "sources": ["demos/ImpRelClaims/ImpRelClaims/Transfers.lean"]},
    # on ImpUnroll and kimp-claims (the arity universe)
    "ImpUnrollClaims": {"tier": "heavy", "sources": ["demos/ImpUnrollClaims/ImpUnrollClaims/Transfers.lean"]},
}


def listed(ct, key):
    """The entries of claims.toml with status KEY: a claim's `KEY = …` line (`open = true`,
    `refuted = "R"`, `hand = "R"`), and the names in an induction's `KEY = [...]`."""
    claims = len(re.findall(rf"^{key} = (?:true|\")", ct, re.M))
    obls = sum(len(re.findall(r'"[^"]*"', x)) for x in re.findall(rf"^{key} = \[(.*)\]$", ct, re.M))
    return claims + obls


def measure_claims(c):
    """kimp's claims (claims.toml), kimpinv's (claims-inv.toml), their guards and kc_auto lines;
    of the open list's entries, those refuted (as the guard checked them, refuted.txt), proved by
    hand, and open."""
    ct = read(c.meas / "claims.toml")
    ci = read(c.meas / "claims-inv.toml")
    ax = read(c.meas / "axioms.txt")
    kc = read(c.meas / "kc-auto-stats.txt")
    rf = read(c.meas / "refuted.txt")
    return {"claims": len(re.findall(r"^\[\[claim\]\]", ct, re.M)) if ct else None,
            "stated": len(re.findall(r"^stated = true", ct, re.M)) if ct else None,
            "inv_stated": len(re.findall(r"^stated = true", ci, re.M)) if ci else None,
            "induction_obligations": sum(int(x) for x in re.findall(r"^obligations = (\d+)", ct, re.M)) if ct else None,
            "guarded": len([l for l in ax.splitlines() if l.strip()]) if ax else None,
            "kc_auto": len([l for l in kc.splitlines() if "kc_auto" in l]) if kc else None,
            "kc_auto_open": sum(int(x) for x in re.findall(r"(\d+) open", kc)) if kc else None,
            "refuted": len([l for l in rf.splitlines() if l.strip()]) if rf is not None else None,
            "hand": listed(ct, "hand") if ct else None,
            "open": listed(ct, "open") if ct else None}


def measure_spec(tag):
    """The claims of one specification (claims-TAG.toml), their guard (axioms-TAG.txt) and kc_auto
    lines (kc-auto-TAG.txt)."""
    def measure(c):
        ct = read(c.meas / f"claims-{tag}.toml")
        ax = read(c.meas / f"axioms-{tag}.txt")
        kc = read(c.meas / f"kc-auto-{tag}.txt")
        return {"claims": len(re.findall(r"^\[\[claim\]\]", ct, re.M)) if ct else None,
                "stated": len(re.findall(r"^stated = true", ct, re.M)) if ct else None,
                "guarded": len([l for l in ax.splitlines() if l.strip()]) if ax else None,
                "kc_auto": len([l for l in kc.splitlines() if "kc_auto" in l]) if kc else None,
                "kc_auto_open": sum(int(x) for x in re.findall(r"(\d+) open", kc)) if kc else None}
    return measure


RECORDS = {
    # on kimp and kimpinv (the arity universe)
    "claims": {"tier": "heavy", "measure": measure_claims,
               "sources": ["generated/kimp-claims", "generated/kimpinv-claims"]},
    # on impplus (the soundness area's library; a `Step` that is not a function)
    "impplus-claims": {"tier": "light", "measure": measure_spec("impplus"),
                       "sources": ["generated/impplus-claims"]},
    # on kstrict (the area's own library; claims whose successors do not reduce: `tryRel`)
    "strict-claims": {"tier": "light", "measure": measure_spec("strict"),
                      "sources": ["generated/strict-claims"]},
    # on kprio (the area's own library; a decoder against an independent table, one opcode and a
    # family by its fields, and a refuted family claim)
    "prio-claims": {"tier": "light", "measure": measure_spec("prio"),
                    "sources": ["generated/prio-claims"]},
}

OUTPUTS = {
    "claims.toml": {"tier": "heavy", "compare": "exact"},
    "claims-inv.toml": {"tier": "heavy", "compare": "exact"},
    "kprove.txt": {"tier": "heavy", "compare": "exact"},
    "kc-auto-stats.txt": {"tier": "heavy", "compare": "sorted-lines"},  # Lake replays logs in build order
    "axioms.txt": {"tier": "heavy", "compare": "axiom-sets"},
    "refuted.txt": {"tier": "heavy", "compare": "axiom-sets"},
    "replay/addition-2.toml": {"tier": "heavy", "compare": "strip-seconds"},
    "replay/branching.toml": {"tier": "heavy", "compare": "strip-seconds"},
    "replay/sum-loop.toml": {"tier": "heavy", "compare": "strip-seconds"},
    "claims-impplus.toml": {"tier": "light", "compare": "exact"},
    "kc-auto-impplus.txt": {"tier": "light", "compare": "sorted-lines"},
    "claims-strict.toml": {"tier": "light", "compare": "exact"},
    "kc-auto-strict.txt": {"tier": "light", "compare": "sorted-lines"},
    "claims-prio.toml": {"tier": "light", "compare": "exact"},
    "kc-auto-prio.txt": {"tier": "light", "compare": "sorted-lines"},
}
