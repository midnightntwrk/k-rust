# The confluence area's registry (tests/gate-check.py loads it; the gate phases are in confluence.sh).
# The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    # workers adding to a shared accumulator: by worker (`confluence --threads workers --slots`), and
    # every pair of rules a slot (`confluence --slots`, `RaceConf.Pairs`)
    "RaceConf": {"tier": "light", "sources": ["generated/race",
                                              "demos/RaceConf/RaceConf/Views.lean", "demos/RaceConf/RaceConf/Slots.lean",
                                              "demos/RaceConf/RaceConf/Pairs/Views.lean",
                                              "demos/RaceConf/RaceConf/Pairs/Slots.lean",
                                              "demos/RaceConf/confluence.toml", "demos/RaceConf/pairs.toml"]},
    # SIMPLE's steps of two threads joined generically, the joins they leave as slots, those the
    # generic attempts do not prove open (`confluence --threads threads --slots`)
    "SimpleConf": {"tier": "heavy", "sources": ["demos/SimpleConf/SimpleConf/Views.lean",
                                                "demos/SimpleConf/SimpleConf/Slots.lean"]},
    # coroutines over a UTXO ledger, the same views with the joins they leave as slots
    # (`confluence --threads procs --slots`)
    "UtxoConf": {"tier": "light", "sources": ["generated/utxo",
                                              "demos/UtxoConf/UtxoConf/Views.lean", "demos/UtxoConf/UtxoConf/Slots.lean",
                                              "demos/UtxoConf/confluence.toml"]},
    # a coordination script's tasks run when their inputs are ready, a resume's segment one step
    "HandoffConf": {"tier": "light", "sources": ["generated/handoff",
                                                 "demos/HandoffConf/HandoffConf/Views.lean",
                                                 "demos/HandoffConf/HandoffConf/Slots.lean",
                                                 "demos/HandoffConf/confluence.toml"]},
    # the same script run in its order into it, by hand (`HandoffSeqRel.result_unique`); built
    # against HandoffConf's phase
    "HandoffSeqRel": {"tier": "light", "sources": ["generated/handoffseq"]},
    # workers writing one cell: the slot of two writes refuted by hand, so `OpenJoins` is false
    "DrfConf": {"tier": "light", "sources": ["generated/drf",
                                             "demos/DrfConf/DrfConf/Views.lean", "demos/DrfConf/DrfConf/Slots.lean",
                                             "demos/DrfConf/confluence.toml"]},
}

# SIMPLE's pairs of rules classified, and its slots by premise and class with their statuses
# (`confluence --threads --slots`)
OUTPUTS = {
    "simple-confluence.toml": {"tier": "heavy", "compare": "exact"},
}
