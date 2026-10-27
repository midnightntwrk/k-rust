# The relational area's registry (tests/gate-check.py loads it; the gate phases are in relational.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "kmut": {"ns": "KMut", "tier": "light"},
}

DEMOS = {
    # ImpRel relates kimp-ps and krsimp-ps (per-sort): its arity bisimulation's build exceeds 14 GB
    "ImpRel": {"tier": "light", "encoding": "per-sort", "sources": ["demos/ImpRel/ImpRel/Bisim.lean", "demos/ImpRel/correspondence.toml"]},
    # ImpUnroll (kimp-ps, kunroll per-sort): its hand module Relation.lean is written over the
    # per-sort constructors and their `injEq` lemmas
    "ImpMut": {"tier": "light", "sources": ["demos/ImpMut/ImpMut/Tr.lean", "demos/ImpMut/correspondence.toml"]},
    "PeanoRel": {"tier": "light", "sources": ["generated/peano", "generated/peanob",
                                              "demos/PeanoRel/PeanoRel/Bisim.lean", "demos/PeanoRel/correspondence.toml"]},
    "CellMapRel": {"tier": "light", "sources": ["generated/cellmap", "generated/cellmapb",
                                                "demos/CellMapRel/CellMapRel/Bisim.lean", "demos/CellMapRel/correspondence.toml"]},
    "PickRel": {"tier": "light", "sources": ["generated/pick", "generated/pickb",
                                             "demos/PickRel/PickRel/Bisim.lean", "demos/PickRel/correspondence.toml"]},
    "ImpUnroll": {"tier": "light", "encoding": "per-sort", "sources": ["generated/kunroll",
                                               "demos/ImpUnroll/ImpUnroll/Tr.lean", "demos/ImpUnroll/ImpUnroll/Refine.lean",
                                               "demos/ImpUnroll/correspondence.toml", "demos/ImpUnroll/refine.toml"]},
}
