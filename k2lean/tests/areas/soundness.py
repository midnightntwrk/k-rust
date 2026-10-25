# The soundness area's registry (tests/gate-check.py loads it; the gate phases are in soundness.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "imptypes": {"ns": "KImpTypes", "tier": "light"},
    # imptypes in the per-sort encoding, for ImpTypes (below)
    "imptypes-ps": {"ns": "KImpTypes", "tier": "light", "encoding": "per-sort"},
}

DEMOS = {
    # on kimp-ps and imptypes-ps: `soundness` writes Typing.lean's proofs for the per-sort encoding
    "ImpTypes": {"tier": "light", "encoding": "per-sort", "sources": ["demos/ImpTypes/ImpTypes/Tr.lean", "demos/ImpTypes/correspondence.toml",
                                              "demos/ImpTypes/ImpTypes/Typing.lean", "demos/ImpTypes/ImpTypes/Soundness.lean"]},
}
