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
    "PickRel": {"tier": "light", "sources": ["generated/pick", "generated/pickb",
                                             "demos/PickRel/PickRel/Bisim.lean", "demos/PickRel/correspondence.toml"]},
    "ImpUnroll": {"tier": "light", "sources": ["generated/kunroll",
                                               "demos/ImpUnroll/ImpUnroll/Tr.lean", "demos/ImpUnroll/ImpUnroll/Refine.lean", "demos/ImpUnroll/ImpUnroll/RefineDefs.lean",
                                               "demos/ImpUnroll/correspondence.toml", "demos/ImpUnroll/refine.toml"]},
    "ImpPrintRefine": {"tier": "light", "sources": ["generated/kprint", "generated/kprintu",
                                                    "demos/ImpPrintRefine/ImpPrintRefine/Tr.lean", "demos/ImpPrintRefine/ImpPrintRefine/Refine.lean", "demos/ImpPrintRefine/ImpPrintRefine/RefineDefs.lean",
                                                    "demos/ImpPrintRefine/correspondence.toml", "demos/ImpPrintRefine/refine.toml"]},
    "VmPopRefine": {"tier": "light", "sources": ["generated/vmpop", "generated/vmpop1",
                                                 "demos/VmPopRefine/VmPopRefine/Tr.lean", "demos/VmPopRefine/VmPopRefine/Refine.lean", "demos/VmPopRefine/VmPopRefine/RefineDefs.lean",
                                                 "demos/VmPopRefine/correspondence.toml", "demos/VmPopRefine/refine.toml"]},
    # refuted by two runs (REL-7): the mutated rule's parts open, `Open.refuted` by the witnesses
    "ImpUnrollMut": {"tier": "light", "sources": ["generated/kunrollle",
                                                  "demos/ImpUnrollMut/ImpUnrollMut/Tr.lean", "demos/ImpUnrollMut/ImpUnrollMut/Refine.lean", "demos/ImpUnrollMut/ImpUnrollMut/RefineDefs.lean",
                                                  "demos/ImpUnrollMut/ImpUnrollMut/Witnesses.lean",
                                                  "demos/ImpUnrollMut/correspondence.toml", "demos/ImpUnrollMut/refine.toml"]},
    "VmPopMut": {"tier": "light", "sources": ["generated/vmpop", "generated/vmpop1skip",
                                              "demos/VmPopMut/VmPopMut/Tr.lean", "demos/VmPopMut/VmPopMut/Refine.lean", "demos/VmPopMut/VmPopMut/RefineDefs.lean",
                                              "demos/VmPopMut/VmPopMut/Witnesses.lean",
                                              "demos/VmPopMut/correspondence.toml", "demos/VmPopMut/refine.toml"]},
    # under a legality (REL-8): an optimization that holds only where the invariant does, the parts
    # that need it by hand (Hand.lean), and a wrong one refuted by a program from a legal start
    "VmEmptyRefine": {"tier": "light", "sources": ["generated/vmempty", "generated/vmemptyopt",
                                                   "demos/VmEmptyRefine/VmEmptyRefine/Tr.lean", "demos/VmEmptyRefine/VmEmptyRefine/Refine.lean",
                                                   "demos/VmEmptyRefine/VmEmptyRefine/RefineDefs.lean", "demos/VmEmptyRefine/VmEmptyRefine/Hand.lean",
                                                   "demos/VmEmptyRefine/correspondence.toml", "demos/VmEmptyRefine/refine.toml"]},
    "RangeIncRefine": {"tier": "light", "sources": ["generated/rangeinc", "generated/rangeincopt",
                                                    "demos/RangeIncRefine/RangeIncRefine/Tr.lean", "demos/RangeIncRefine/RangeIncRefine/Refine.lean",
                                                    "demos/RangeIncRefine/RangeIncRefine/RefineDefs.lean", "demos/RangeIncRefine/RangeIncRefine/Hand.lean",
                                                    "demos/RangeIncRefine/correspondence.toml", "demos/RangeIncRefine/refine.toml"]},
    # with no legality (REL-9): refuted at a configuration that no program reaches
    "VmEmptyOpen": {"tier": "light", "sources": ["generated/vmempty", "generated/vmemptyopt",
                                                 "demos/VmEmptyOpen/VmEmptyOpen/Tr.lean", "demos/VmEmptyOpen/VmEmptyOpen/Refine.lean",
                                                 "demos/VmEmptyOpen/VmEmptyOpen/RefineDefs.lean", "demos/VmEmptyOpen/VmEmptyOpen/Witnesses.lean",
                                                 "demos/VmEmptyOpen/correspondence.toml", "demos/VmEmptyOpen/refine.toml"]},
    "VmPopLegal": {"tier": "light", "sources": ["generated/vmpopinv", "generated/vmpop1",
                                                "demos/VmPopLegal/VmPopLegal/Tr.lean", "demos/VmPopLegal/VmPopLegal/Refine.lean",
                                                "demos/VmPopLegal/VmPopLegal/RefineDefs.lean",
                                                "demos/VmPopLegal/correspondence.toml", "demos/VmPopLegal/refine.toml"]},
    "VmEmptyMut": {"tier": "light", "sources": ["generated/vmempty", "generated/vmemptystale",
                                                "demos/VmEmptyMut/VmEmptyMut/Tr.lean", "demos/VmEmptyMut/VmEmptyMut/Refine.lean",
                                                "demos/VmEmptyMut/VmEmptyMut/RefineDefs.lean", "demos/VmEmptyMut/VmEmptyMut/Witnesses.lean",
                                                "demos/VmEmptyMut/correspondence.toml", "demos/VmEmptyMut/refine.toml"]},
}

# each refine demo's parts (`fwd_tr.«RULE»`, `fwd_x.«RULE»`, `bwd_tr.«RULE»`, `bwd_x.«RULE»`) and
# priority lemmas (`pri_fwd.«RULE»`, `pri_bwd.«RULE»`, REL-8), compared by name: generic, by hand or
# open (REL-6); the three bisimilar pairs' parts are all generated, the legal ones' by hand where the
# invariant is needed, the mutants' open ones listed in their demo (open.txt)
for _d in ("ImpUnroll", "ImpPrintRefine", "VmPopRefine", "ImpUnrollMut", "VmPopMut",
           "VmEmptyRefine", "RangeIncRefine", "VmPopLegal", "VmEmptyMut", "VmEmptyOpen"):
    DEMOS[_d]["slots"] = {"prefixes": ["fwd_tr.", "fwd_x.", "bwd_tr.", "bwd_x.", "pri_fwd.", "pri_bwd."]}
