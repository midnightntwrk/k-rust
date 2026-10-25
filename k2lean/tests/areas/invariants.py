# The invariants area's registry (tests/gate-check.py loads it; the gate phases are in invariants.sh).
# The format of every area's registry is described in gate-check.py's docstring.

# libraries built only as far as their invariant needs: no `…Test.Axioms` guard (guard False)
LIBS = {
    "kimpinv": {"ns": "KImpInv", "tier": "light", "guard": False},
    "kimpkeys": {"ns": "KImpKeys", "tier": "light", "guard": False},
    "kimpkeys-hand": {"ns": "KImpKeys", "tier": "light", "guard": False},
    "kimpfold": {"ns": "KImpInv", "tier": "light", "guard": False},
    "kimptop": {"ns": "KImpInv", "tier": "light", "guard": False},
    "nested": {"ns": "KNested", "tier": "light", "guard": False},
    "simpleinv": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simplestore": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
    "simplet": {"ns": "KSimpleInv", "tier": "heavy", "guard": False},
}

# kind 1 invariants (`DIR/NS/Invariants.lean`); krsimp's library is core's, its invariant this area's
INVS = {
    "krsimp": {"ns": "KrsImp", "tier": "light"},
    "kimpinv": {"ns": "KImpInv", "tier": "light"},
    "kimpkeys": {"ns": "KImpKeys", "tier": "light"},
    "kimpkeys-hand": {"ns": "KImpKeys", "tier": "light"},
    "kimpfold": {"ns": "KImpInv", "tier": "light"},
    "kimptop": {"ns": "KImpInv", "tier": "light"},
    "nested": {"ns": "KNested", "tier": "light"},
    "simpleinv": {"ns": "KSimpleInv", "tier": "heavy"},
    "simplestore": {"ns": "KSimpleInv", "tier": "heavy"},
    "simplet": {"ns": "KSimpleInv", "tier": "heavy"},
}

DEMOS = {
    "KrsImpTyping": {"tier": "light"},
    "ImpWrites": {"tier": "light"},
    "Kind2Template": {"tier": "light"},
    "SimpleEnv": {"tier": "heavy"},
}

NEGATIVE = {"krsimp-ill-typed": {"tier": "light"}}
