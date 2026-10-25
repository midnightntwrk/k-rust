# The soundness area's registry (tests/gate-check.py loads it; the gate phases are in soundness.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "imptypes": {"ns": "KImpTypes", "tier": "light"},
}

DEMOS = {
    "ImpTypes": {"tier": "light", "sources": ["demos/ImpTypes/ImpTypes/Tr.lean", "demos/ImpTypes/correspondence.toml",
                                              "demos/ImpTypes/ImpTypes/Typing.lean", "demos/ImpTypes/ImpTypes/Soundness.lean"]},
}
