# The soundness area's registry (tests/gate-check.py loads it; the gate phases are in soundness.sh).
# The format of every area's registry is described in gate-check.py's docstring.

LIBS = {
    "imptypes": {"ns": "KImpTypes", "tier": "light"},
    # kimp's expression language and its checker, for ExprTypes (below)
    "kexpr": {"ns": "KExpr", "tier": "light"},
    "exprtypes": {"ns": "KExprTypes", "tier": "light"},
    # IMP++ (K's tutorial) and its checker, for ImpPlusTypes (below)
    "impplus": {"ns": "KImpPlus", "tier": "light"},
    "impplustypes": {"ns": "KImpPlusTypes", "tier": "light"},
    # no stuck states (`gen --progress`): a stack machine, and its variant without a rule; built as
    # far as their invariant and `progress` (no `…Test.Axioms`; the modules assert their axioms)
    "vm": {"ns": "KVm", "tier": "light", "guard": False},
    "vmstuck": {"ns": "KVmStuck", "tier": "light", "guard": False},
    # the stack machine with priorities: three ranks (SND-15)
    "vmpri": {"ns": "KVmPri", "tier": "light", "guard": False},
    # the same with `<k>` in a cell map: coroutines, and their variant with a join that can deadlock
    "coro": {"ns": "Coro", "tier": "light", "guard": False},
    "corojoin": {"ns": "CoroJoin", "tier": "light", "guard": False},
}

INVS = {
    "vm": {"ns": "KVm", "tier": "light"},
    "vmstuck": {"ns": "KVmStuck", "tier": "light"},
    "vmpri": {"ns": "KVmPri", "tier": "light"},
    "coro": {"ns": "Coro", "tier": "light"},
    "corojoin": {"ns": "CoroJoin", "tier": "light"},
}

PROGS = {
    "vm": {"ns": "KVm", "tier": "light"},
    "vmstuck": {"ns": "KVmStuck", "tier": "light"},
    "vmpri": {"ns": "KVmPri", "tier": "light"},
    "coro": {"ns": "Coro", "tier": "light"},
    "corojoin": {"ns": "CoroJoin", "tier": "light"},
    # under a kind 2 invariant (demos/HandoffConf/HandoffConf/Live.lean): the progress modules are the
    # demo's, which holds the invariant (`gen --progress-out`); the library is the confluence area's
    "handoff": {"ns": "HandoffConf", "tier": "light", "dir": "demos/HandoffConf",
                "sources": ["demos/HandoffConf/HandoffConf/ProgressDefs.lean",
                            "demos/HandoffConf/HandoffConf/Progress.lean"]},
    # type soundness as an instance (SND-16): kimp under its runtime typing ImpTypes.Typed
    # (demos/ImpTypes/ImpTypes/Typed.lean), the progress modules written into demos/ImpTypes
    "imptypes": {"ns": "ImpTypes", "tier": "light", "dir": "demos/ImpTypes",
                 "sources": ["demos/ImpTypes/ImpTypes/ProgressDefs.lean",
                             "demos/ImpTypes/ImpTypes/Progress.lean"]},
    # IMP++ under its runtime typing ImpPlusTypes.Typed (SND-17): `<k>` in the cell map `<threads>`,
    # four priority ranks, and the ending `kDone` (a thread may wait at `join` forever)
    "impplustypes": {"ns": "ImpPlusTypes", "tier": "light", "dir": "demos/ImpPlusTypes",
                     "sources": ["demos/ImpPlusTypes/ImpPlusTypes/ProgressDefs.lean",
                                 "demos/ImpPlusTypes/ImpPlusTypes/Progress.lean"]},
}

DEMOS = {
    "ImpTypes": {"tier": "light", "sources": ["demos/ImpTypes/ImpTypes/Tr.lean", "demos/ImpTypes/correspondence.toml",
                                              "demos/ImpTypes/ImpTypes/Typing.lean", "demos/ImpTypes/ImpTypes/Soundness.lean"]},
    # a language whose programs end with a value, with no cell typed by hand (`soundness --typing typeOf`)
    "ExprTypes": {"tier": "light", "sources": ["demos/ExprTypes/ExprTypes/Tr.lean", "demos/ExprTypes/correspondence.toml",
                                                "demos/ExprTypes/ExprTypes/Typing.lean", "demos/ExprTypes/ExprTypes/Soundness.lean"]},
    # a kind 2 invariant over impplus: store locations below K's generated counter, thread ids at most it
    "ImpPlusFresh": {"tier": "light"},
    # a second semantics: threads in a cell map (`Final` waits at `join`), ranked rules, two hole sorts
    "ImpPlusTypes": {"tier": "light", "sources": ["demos/ImpPlusTypes/ImpPlusTypes/Tr.lean", "demos/ImpPlusTypes/correspondence.toml",
                                                    "demos/ImpPlusTypes/ImpPlusTypes/Typing.lean", "demos/ImpPlusTypes/ImpPlusTypes/Soundness.lean"]},
}
