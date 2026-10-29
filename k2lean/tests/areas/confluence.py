# The confluence area's registry (tests/gate-check.py loads it; the gate phases are in confluence.sh).
# The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    "RaceConf": {"tier": "light", "sources": ["generated/race",
                                              "demos/RaceConf/RaceConf/Confluence.lean", "demos/RaceConf/confluence.toml"]},
    # SIMPLE's steps of two threads joined generically, the rest as hypotheses (`confluence --threads`)
    "SimpleConf": {"tier": "heavy", "sources": ["demos/SimpleConf/SimpleConf/Views.lean"]},
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
}

# SIMPLE's pairs of rules classified, and what SimpleConf leaves open (`confluence --threads`)
OUTPUTS = {
    "simple-confluence.toml": {"tier": "heavy", "compare": "exact"},
}
