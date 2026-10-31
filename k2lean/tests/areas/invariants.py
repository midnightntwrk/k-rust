# The invariants area's registry (tests/gate-check.py loads it; the gate phases are in invariants.sh).
# The format of every area's registry is described in gate-check.py's docstring.

# libraries built only as far as their invariant needs: no `…Test.Axioms` guard (guard False)
LIBS = {
    "kimpinv": {"ns": "KImpInv", "tier": "light", "guard": False},
    "kimpkeys": {"ns": "KImpKeys", "tier": "light", "guard": False},
    "kimpkeys-hand": {"ns": "KImpKeys", "tier": "light", "guard": False},
    "kimpfold": {"ns": "KImpInv", "tier": "light", "guard": False},
    "kimptop": {"ns": "KImpInv", "tier": "light", "guard": False},
    "kimpboth": {"ns": "KImpInv", "tier": "light", "guard": False},
    "nested": {"ns": "KNested", "tier": "light", "guard": False},
    "range": {"ns": "KRange", "tier": "light", "guard": False},
    "kfold": {"ns": "KKFold", "tier": "light", "guard": False},
    "anyfold": {"ns": "KAnyFold", "tier": "light", "guard": False},
    "walk": {"ns": "KWalk", "tier": "light", "guard": False},
    "drfinv": {"ns": "Drf", "tier": "light", "guard": False},
    "simpleinv": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simplestore": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simplet": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simpleenvs": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
}

# kind 1 invariants (`DIR/NS/Invariants.lean`); krsimp's library is core's, its invariant this area's
INVS = {
    "krsimp": {"ns": "KrsImp", "tier": "light"},
    "kimpinv": {"ns": "KImpInv", "tier": "light"},
    "kimpkeys": {"ns": "KImpKeys", "tier": "light"},
    "kimpkeys-hand": {"ns": "KImpKeys", "tier": "light"},
    "kimpfold": {"ns": "KImpInv", "tier": "light"},
    "kimptop": {"ns": "KImpInv", "tier": "light"},
    "kimpboth": {"ns": "KImpInv", "tier": "light"},
    "nested": {"ns": "KNested", "tier": "light"},
    "range": {"ns": "KRange", "tier": "light"},
    "kfold": {"ns": "KKFold", "tier": "light"},
    "anyfold": {"ns": "KAnyFold", "tier": "light"},
    "walk": {"ns": "KWalk", "tier": "light"},
    "drfinv": {"ns": "Drf", "tier": "light"},
    "simpleinv": {"ns": "KSimpleInv", "tier": "heavy"},
    "simplestore": {"ns": "KSimpleInv", "tier": "heavy"},
    "simplet": {"ns": "KSimpleInv", "tier": "heavy"},
    "simpleenvs": {"ns": "KSimpleInv", "tier": "heavy"},
}

DEMOS = {
    "KrsImpTyping": {"tier": "light"},
    "ImpWrites": {"tier": "light"},
    "Kind2Template": {"tier": "light"},
    "InvBudget": {"tier": "light"},
}

NEGATIVE = {"krsimp-ill-typed": {"tier": "light"}}


def measure_meas(d, ns):
    """The step measure of library d (`gen --measure`, `d/NS/Measure.lean`): its rule cases, those
    proved by `k2l_measure`, and the open ones (open-measure-cases.txt)."""
    def measure(c):
        m = read(c.tree / "generated" / d / ns / "Measure.lean")
        ol = read(c.tree / "generated" / d / "open-measure-cases.txt") or ""
        opened = sorted(l.split(" | ")[0].strip() for l in ol.splitlines() if l.strip() and not l.startswith("#"))
        return {"cases": len(re.findall(r"^theorem .* : Step\.Rel\.", m, re.M)) if m else None,
                "auto": len(re.findall(r":= by k2l_meas$", m, re.M)) if m else None,
                "open": opened}
    return measure


RECORDS = {
    # corout's measure (the confluence area's library corout, built by its demo TwoParamEnds):
    # every rule lowers it (INV-15)
    "corout-measure": {"tier": "light", "measure": measure_meas("corout", "Corout"), "sources": []},
}
