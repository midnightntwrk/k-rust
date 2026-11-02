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
    "twoparamvals": {"ns": "TwoParam", "tier": "light", "guard": False},
    "ledger": {"ns": "Ledger", "tier": "light", "guard": False},
    "escrow": {"ns": "Escrow", "tier": "light", "guard": False},
    "tickets": {"ns": "Tickets", "tier": "light", "guard": False},
    "fuel": {"ns": "Fuel", "tier": "light", "guard": False},
    "flagsmirror": {"ns": "KFlags", "tier": "light", "guard": False},
    "flagscache": {"ns": "KFlags", "tier": "light", "guard": False},
    "racelogstep": {"ns": "Racelog", "tier": "light", "guard": False},
    "ledgersupply": {"ns": "Ledger", "tier": "light", "guard": False},
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
    "twoparamvals": {"ns": "TwoParam", "tier": "light"},
    "ledger": {"ns": "Ledger", "tier": "light"},
    "escrow": {"ns": "Escrow", "tier": "light"},
    "tickets": {"ns": "Tickets", "tier": "light"},
    "fuel": {"ns": "Fuel", "tier": "light"},
    "flagsmirror": {"ns": "KFlags", "tier": "light"},
    "flagscache": {"ns": "KFlags", "tier": "light"},
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
    proved by `k2l_measure`, and the open ones (open-measure-cases.txt); under the invariant
    (`--measure-invariant`), also how its bound is proved (`Measure.bound`: "auto" or "hand")."""
    def measure(c):
        m = read(c.tree / "generated" / d / ns / "Measure.lean")
        ol = read(c.tree / "generated" / d / "open-measure-cases.txt") or ""
        opened = sorted(l.split(" | ")[0].strip() for l in ol.splitlines() if l.strip() and not l.startswith("#"))
        r = {"cases": len(re.findall(r"^theorem .* : Step\.Rel\.", m, re.M)) if m else None,
             "auto": len(re.findall(r"^theorem .* : Step\.Rel\..*:= by k2l_meas$", m, re.M)) if m else None,
             "open": opened}
        b = re.search(r"^theorem Measure\.bound .*:= (.*)$", m, re.M) if m else None
        if b:
            r["bound"] = "auto" if b.group(1) == "by k2l_meas" else "hand"
        return r
    return measure


def step_meas(d, ns):
    """The step property of library d (`gen --step-property`, `d/NS/StepProp.lean`; INV-21): its rule
    cases, those proved by `k2l_step`, and the open ones (open-step-cases.txt); with
    `--step-property-trans`, how its transitivity is proved ("auto" or "hand"); and the theorems of
    the tracked hand module (a refutation, where the property is false)."""
    def measure(c):
        m = read(c.tree / "generated" / d / ns / "StepProp.lean")
        h = read(c.tree / "generated" / d / ns / "StepPropHand.lean")
        ol = read(c.tree / "generated" / d / "open-step-cases.txt") or ""
        r = {"cases": len(re.findall(r"^theorem .* : Step\.Rel\..* StepProp\.holds :=", m, re.M)) if m else None,
             "auto": len(re.findall(r"^theorem .* : Step\.Rel\..* StepProp\.holds := by k2l_stepp$", m, re.M)) if m else None,
             "open": sorted(l.split(" | ")[0].strip() for l in ol.splitlines()
                            if l.strip() and not l.startswith("#"))}
        t = re.search(r"^theorem StepProp\.trans : .*\n *(.*)$", m, re.M) if m else None
        r["trans"] = None if not t else ("auto" if t.group(1).strip() == "k2l_stepp" else "hand")
        r["hand"] = sorted(re.findall(r"^theorem (\S+)", h, re.M)) if h else []
        return r
    return measure


RECORDS = {
    # corout's measure (the confluence area's library corout, built by its demo TwoParamEnds):
    # every rule lowers it (INV-15)
    "corout-measure": {"tier": "light", "measure": measure_meas("corout", "Corout"), "sources": []},
    # twoparam's measure (the confluence area's library twoparam, built by its demo TwoParamTx): the
    # work left, a sum over the <tasks> cell map, lowered by every rule (INV-17)
    "twoparam-measure": {"tier": "light", "measure": measure_meas("twoparam", "TwoParam"), "sources": []},
    # twolayer's measure (the confluence area's library twolayer, built by its demo TwoLayerTx): the
    # work left in the tasks and in the suspended processes' code, two sums
    "twolayer-measure": {"tier": "light", "measure": measure_meas("twolayer", "TwoLayer"), "sources": []},
    # measures under the invariant (INV-20): each rule's decrease under it, and its bound once
    "tickets-measure": {"tier": "light", "measure": measure_meas("tickets", "Tickets"), "sources": []},
    "fuel-measure": {"tier": "light", "measure": measure_meas("fuel", "Fuel"), "sources": []},
    # step properties (INV-21): ledger's fees never decrease (beside its invariant), tickets' next id
    # and what is left (over its whole <pool>, beside its invariant and measure; transitive),
    # racelog's accumulated work (a rule matching a cell map; transitive), and ledger's false
    # supplyUp (its `burn` case open, refuted in the hand module)
    "ledger-step": {"tier": "light", "measure": step_meas("ledger", "Ledger"), "sources": []},
    "tickets-step": {"tier": "light", "measure": step_meas("tickets", "Tickets"), "sources": []},
    "racelog-step": {"tier": "light", "measure": step_meas("racelogstep", "Racelog"), "sources": []},
    "ledgersupply-step": {"tier": "light", "measure": step_meas("ledgersupply", "Ledger"), "sources": []},
}
