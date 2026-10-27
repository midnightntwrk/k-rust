# The soundness area's registry (tests/gate-check.py loads it; the gate phases are in soundness.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "imptypes": {"ns": "KImpTypes", "tier": "light"},
    # kimp's expression language and its checker, for ExprTypes (below)
    "kexpr": {"ns": "KExpr", "tier": "light"},
    "exprtypes": {"ns": "KExprTypes", "tier": "light"},
}

DEMOS = {
    "ImpTypes": {"tier": "light", "sources": ["demos/ImpTypes/ImpTypes/Tr.lean", "demos/ImpTypes/correspondence.toml",
                                              "demos/ImpTypes/ImpTypes/Typing.lean", "demos/ImpTypes/ImpTypes/Soundness.lean"]},
    # a language whose programs end with a value, with no cell typed by hand (`soundness --typing typeOf`)
    "ExprTypes": {"tier": "light", "sources": ["demos/ExprTypes/ExprTypes/Tr.lean", "demos/ExprTypes/correspondence.toml",
                                                "demos/ExprTypes/ExprTypes/Typing.lean", "demos/ExprTypes/ExprTypes/Soundness.lean"]},
}
