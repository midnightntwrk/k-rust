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
    # per-sort: on the arity universe the backward direction of `workersIn`'s walk lemma
    # (InvariantDefs.lean) leaves the match's catch-all arm on the one-constructor cell sort open
    "walk": {"ns": "KWalk", "tier": "light", "guard": False, "encoding": "per-sort"},
    "simpleinv": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simplestore": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simplet": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    # kimpinv in the per-sort encoding, for kimpinv's claims (claims.sh), which stay on it (CLM-5)
    "kimpinv-ps": {"ns": "KImpInv", "tier": "heavy", "guard": False, "encoding": "per-sort"},
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
    "walk": {"ns": "KWalk", "tier": "light"},
    "simpleinv": {"ns": "KSimpleInv", "tier": "heavy"},
    "simplestore": {"ns": "KSimpleInv", "tier": "heavy"},
    "simplet": {"ns": "KSimpleInv", "tier": "heavy"},
    "kimpinv-ps": {"ns": "KImpInv", "tier": "heavy"},
}

DEMOS = {
    "KrsImpTyping": {"tier": "light"},
    "ImpWrites": {"tier": "light"},
    "Kind2Template": {"tier": "light"},
    "InvBudget": {"tier": "light"},
    "SimpleEnv": {"tier": "heavy", "encoding": "per-sort"},
}

NEGATIVE = {"krsimp-ill-typed": {"tier": "light"}}
