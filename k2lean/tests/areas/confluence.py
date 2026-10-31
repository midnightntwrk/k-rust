# The confluence area's registry (tests/gate-check.py loads it; the gate phases are in confluence.sh).
# The format of every area's registry is described in gate-check.py's docstring. Each confluence demo's
# slots (`join.K.r₁.r₂`) are compared by name (`slots`): generic, by hand or refuted as its open-joins
# list marks them, or open (RaceConf has no list: every slot is generic).

DEMOS = {
    # workers adding to a shared accumulator: by worker (`confluence --threads workers --slots`), and
    # every pair of rules a slot (`confluence --slots`, `RaceConf.Pairs`)
    "RaceConf": {"tier": "light", "sources": ["generated/race",
                                              "demos/RaceConf/RaceConf/Views.lean", "demos/RaceConf/RaceConf/Slots.lean",
                                              "demos/RaceConf/RaceConf/Pairs/Views.lean",
                                              "demos/RaceConf/RaceConf/Pairs/Slots.lean",
                                              "demos/RaceConf/confluence.toml", "demos/RaceConf/pairs.toml"],
                 "slots": {"prefixes": ["join.", "Pairs.join."]}},
    # SIMPLE's steps of two threads joined generically, the joins they leave as slots, those the
    # generic attempts do not prove open (`confluence --threads threads --slots`)
    "SimpleConf": {"tier": "heavy", "sources": ["demos/SimpleConf/SimpleConf/Views.lean",
                                                "demos/SimpleConf/SimpleConf/Slots.lean"],
                   "slots": {"prefixes": ["join."], "list": "demos/SimpleConf/open-joins.txt"}},
    # coroutines over a UTXO ledger, the same views with the joins they leave as slots
    # (`confluence --threads procs --slots`)
    "UtxoConf": {"tier": "light", "sources": ["generated/utxo",
                                              "demos/UtxoConf/UtxoConf/Views.lean", "demos/UtxoConf/UtxoConf/Slots.lean",
                                              "demos/UtxoConf/confluence.toml"],
                 "slots": {"prefixes": ["join."], "list": "demos/UtxoConf/open-joins.txt"}},
    # a coordination script's tasks run when their inputs are ready, a resume's segment one step
    "HandoffConf": {"tier": "light", "sources": ["generated/handoff",
                                                 "demos/HandoffConf/HandoffConf/Views.lean",
                                                 "demos/HandoffConf/HandoffConf/Slots.lean",
                                                 "demos/HandoffConf/confluence.toml"],
                    "slots": {"prefixes": ["join."]}},
    # the same script run in its order into it, its translation generated (`relate --roots`), the
    # simulation by hand, composed by the prelude's
    # `KPrelude.Forward` (`HandoffSeqRel.result_unique`), and every order ends there
    # (`HandoffSeqRel.transaction`, with HandoffConf's `terminates`); built against HandoffConf's phase
    "HandoffSeqRel": {"tier": "light", "sources": ["generated/handoffseq",
                                                   "demos/HandoffSeqRel/HandoffSeqRel/Tr.lean",
                                                   "demos/HandoffSeqRel/correspondence.toml"]},
    # workers writing one cell: the slot of two writes refuted by two runs of a program, and every
    # slot generic under the data-race freedom `drfOk` (`DrfConf.Legal`)
    "DrfConf": {"tier": "light", "sources": ["generated/drf",
                                             "demos/DrfConf/DrfConf/Views.lean", "demos/DrfConf/DrfConf/Slots.lean",
                                             "demos/DrfConf/DrfConf/Legal/Views.lean",
                                             "demos/DrfConf/DrfConf/Legal/Slots.lean",
                                             "demos/DrfConf/confluence.toml", "demos/DrfConf/legal.toml"],
                "slots": {"prefixes": ["join.", "Legal.join."], "list": "demos/DrfConf/open-joins.txt"}},
    # the two-layer prototype: a coordination script's tasks running a coroutine language's segments;
    # the races of two tasks refuted together by two runs, and every slot generic under `wf`
    "TwoConf": {"tier": "light", "sources": ["generated/twolayer",
                                             "demos/TwoConf/TwoConf/Views.lean", "demos/TwoConf/TwoConf/Slots.lean",
                                             "demos/TwoConf/TwoConf/Legal/Views.lean",
                                             "demos/TwoConf/TwoConf/Legal/Slots.lean",
                                             "demos/TwoConf/confluence.toml", "demos/TwoConf/legal.toml"],
                "slots": {"prefixes": ["join.", "Legal.join."], "list": "demos/TwoConf/open-joins.txt"}},
    # its parameterized form: a segment's register and code parameters of the definition, every slot
    # generic under `wf` for every instance
    "TwoParamConf": {"tier": "light", "sources": ["generated/twoparam",
                                                  "demos/TwoParamConf/TwoParamConf/Views.lean",
                                                  "demos/TwoParamConf/TwoParamConf/Slots.lean",
                                                  "demos/TwoParamConf/confluence.toml"],
                     "slots": {"prefixes": ["join."]}},
    # the parameters from the coroutine language on its own, by hand over the translations of code;
    # built against TwoParamConf's phase
    "TwoParamInst": {"tier": "light", "sources": ["generated/corout",
                                                  "demos/TwoParamInst/TwoParamInst/Tr.lean",
                                                  "demos/TwoParamInst/TwoParamInst/Back.lean"]},
}

# SIMPLE's pairs of rules classified, and its slots by premise and class with their statuses
# (`confluence --threads --slots`)
OUTPUTS = {
    "simple-confluence.toml": {"tier": "heavy", "compare": "exact"},
}
