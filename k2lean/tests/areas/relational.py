# The relational area's registry (tests/gate-check.py loads it; the gate phases are in relational.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "kmut": {"ns": "KMut", "tier": "light"},
}

DEMOS = {
    "ImpRel": {"tier": "light", "sources": ["demos/ImpRel/ImpRel/Bisim.lean", "demos/ImpRel/correspondence.toml"]},
    "ImpMut": {"tier": "light", "sources": ["demos/ImpMut/ImpMut/Tr.lean", "demos/ImpMut/correspondence.toml"]},
    "PeanoRel": {"tier": "light", "sources": ["generated/peano", "generated/peanob",
                                              "demos/PeanoRel/PeanoRel/Bisim.lean", "demos/PeanoRel/correspondence.toml"]},
    "CellMapRel": {"tier": "light", "sources": ["generated/cellmap", "generated/cellmapb",
                                                "demos/CellMapRel/CellMapRel/Bisim.lean", "demos/CellMapRel/correspondence.toml"]},
    "ImpUnroll": {"tier": "light", "sources": ["generated/kunroll",
                                               "demos/ImpUnroll/ImpUnroll/Tr.lean", "demos/ImpUnroll/ImpUnroll/Refine.lean",
                                               "demos/ImpUnroll/correspondence.toml", "demos/ImpUnroll/refine.toml"]},
}
