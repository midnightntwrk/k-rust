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
    # workers logging their steps: by equality the slot of two workers' steps refuted at a peak of a
    # program, and modulo the order of the log and the last writer every slot generic
    # (`confluence --equiv`, `RaceLogConf.Equiv`)
    "RaceLogConf": {"tier": "light", "sources": ["generated/racelog",
                                                 "demos/RaceLogConf/RaceLogConf/Views.lean",
                                                 "demos/RaceLogConf/RaceLogConf/Slots.lean",
                                                 "demos/RaceLogConf/RaceLogConf/Equiv/Views.lean",
                                                 "demos/RaceLogConf/RaceLogConf/Equiv/Slots.lean",
                                                 "demos/RaceLogConf/confluence.toml", "demos/RaceLogConf/equiv.toml"],
                    "slots": {"prefixes": ["join.", "Equiv.join.", "Equiv.equiv."],
                              "list": "demos/RaceLogConf/open-joins.txt"}},
    # the same without threads: a map of jobs run in any order, each logged
    "JobsConf": {"tier": "light", "sources": ["generated/jobs",
                                              "demos/JobsConf/JobsConf/Views.lean", "demos/JobsConf/JobsConf/Slots.lean",
                                              "demos/JobsConf/JobsConf/Equiv/Views.lean",
                                              "demos/JobsConf/JobsConf/Equiv/Slots.lean",
                                              "demos/JobsConf/confluence.toml", "demos/JobsConf/equiv.toml"],
                 "slots": {"prefixes": ["join.", "Equiv.join.", "Equiv.equiv."],
                           "list": "demos/JobsConf/open-joins.txt"}},
    # the same two with an `owise` rule (two priority ranks), modulo the same equivalences: every
    # slot and every rule's lemma generic (`confluence --equiv` with priorities)
    "RaceLogOwConf": {"tier": "light", "sources": ["generated/racelogow",
                                                   "demos/RaceLogOwConf/RaceLogOwConf/Views.lean",
                                                   "demos/RaceLogOwConf/RaceLogOwConf/Slots.lean",
                                                   "demos/RaceLogOwConf/confluence.toml"],
                      "slots": {"prefixes": ["join.", "equiv."]}},
    "JobsOwConf": {"tier": "light", "sources": ["generated/jobsow",
                                                "demos/JobsOwConf/JobsOwConf/Views.lean",
                                                "demos/JobsOwConf/JobsOwConf/Slots.lean",
                                                "demos/JobsOwConf/confluence.toml"],
                   "slots": {"prefixes": ["join.", "equiv."]}},
    # jobs whose steps remove bindings of the map (tests/jobs-remove.py): two removals, or a removal
    # and an update, at two bindings commute
    "JobsRmConf": {"tier": "light", "sources": ["generated/jobsrm",
                                                "demos/JobsRmConf/JobsRmConf/Views.lean",
                                                "demos/JobsRmConf/JobsRmConf/Slots.lean",
                                                "demos/JobsRmConf/confluence.toml"],
                   "slots": {"prefixes": ["join.", "equiv."]}},
    "JobsDropConf": {"tier": "light", "sources": ["generated/jobsdrop",
                                                  "demos/JobsDropConf/JobsDropConf/Views.lean",
                                                  "demos/JobsDropConf/JobsDropConf/Slots.lean",
                                                  "demos/JobsDropConf/confluence.toml"],
                     "slots": {"prefixes": ["join.", "equiv."]}},
    # jobs removed when they run and inserted by two counters (tests/jobs-remove.py, mode submit): a
    # removal and an insertion, or two insertions at two keys, commute
    "JobsSubConf": {"tier": "light", "sources": ["generated/jobssub",
                                                 "demos/JobsSubConf/JobsSubConf/Views.lean",
                                                 "demos/JobsSubConf/JobsSubConf/Slots.lean",
                                                 "demos/JobsSubConf/confluence.toml"],
                    "slots": {"prefixes": ["join.", "equiv."]}},
    # utxo with cells its processes write and no rule reads (tests/utxo-relaxed.py), by process
    # modulo the equivalence: creations and spends at two keys of the ledger commute (relaxed cells
    # in the views' classes)
    "UtxoRelConf": {"tier": "light", "sources": ["generated/utxorel",
                                                 "demos/UtxoRelConf/UtxoRelConf/Views.lean",
                                                 "demos/UtxoRelConf/UtxoRelConf/Slots.lean",
                                                 "demos/UtxoRelConf/confluence.toml"],
                    "slots": {"prefixes": ["join.", "equiv."],
                              "list": "demos/UtxoRelConf/open-joins.txt"}},
    # SIMPLE's steps of two threads joined generically, the joins they leave as slots, those the
    # generic attempts do not prove open (`confluence --threads threads --slots`)
    "SimpleConf": {"tier": "heavy", "sources": ["demos/SimpleConf/SimpleConf/Views.lean",
                                                "demos/SimpleConf/SimpleConf/Slots.lean"],
                   "slots": {"prefixes": ["join.", "flush."], "list": "demos/SimpleConf/open-joins.txt"}},
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
    # the same without the script's well-formedness: its races refuted at peaks of programs that have
    # them, run at an instance of the parameters (`--witness-instance`)
    "HandoffRaceConf": {"tier": "light", "sources": ["demos/HandoffRaceConf/HandoffRaceConf/Views.lean",
                                                     "demos/HandoffRaceConf/HandoffRaceConf/Slots.lean",
                                                     "demos/HandoffRaceConf/confluence.toml"],
                        "slots": {"prefixes": ["join."], "list": "demos/HandoffRaceConf/open-joins.txt"}},
    # the two-layer prototype: a coordination script's tasks running a coroutine language's segments;
    # the races of two tasks refuted together by two runs, and every slot generic under `wf`
    "TwoConf": {"tier": "light", "sources": ["generated/twolayer",
                                             "demos/TwoConf/TwoConf/Views.lean", "demos/TwoConf/TwoConf/Slots.lean",
                                             "demos/TwoConf/TwoConf/Legal/Views.lean",
                                             "demos/TwoConf/TwoConf/Legal/Slots.lean",
                                             "demos/TwoConf/confluence.toml", "demos/TwoConf/legal.toml"],
                "slots": {"prefixes": ["join.", "Legal.join."], "list": "demos/TwoConf/open-joins.txt"}},
    # the same under the weaker legality `wfOut`: the race of two spends refuted by two runs of a
    # program `wfOut` admits (its legality the hand module's) and at a peak, every other slot generic
    "TwoOutConf": {"tier": "light", "sources": ["generated/twolayerout",
                                                "demos/TwoOutConf/TwoOutConf/Views.lean",
                                                "demos/TwoOutConf/TwoOutConf/Slots.lean",
                                                "demos/TwoOutConf/confluence.toml"],
                   "slots": {"prefixes": ["join.", "witness."], "list": "demos/TwoOutConf/open-joins.txt"}},
    # its parameterized form: a segment's register and code parameters of the definition, every slot
    # generic under `wf` for every instance
    "TwoParamConf": {"tier": "light", "sources": ["generated/twoparam",
                                                  "demos/TwoParamConf/TwoParamConf/Views.lean",
                                                  "demos/TwoParamConf/TwoParamConf/Slots.lean",
                                                  "demos/TwoParamConf/confluence.toml"],
                     "slots": {"prefixes": ["join."]}},
    # the same under `valsOk` alone: its races refuted from legal starts at an instance
    "TwoParamOkConf": {"tier": "light", "sources": ["generated/twoparamok",
                                                    "demos/TwoParamOkConf/TwoParamOkConf/Views.lean",
                                                    "demos/TwoParamOkConf/TwoParamOkConf/Slots.lean",
                                                    "demos/TwoParamOkConf/confluence.toml"],
                       "slots": {"prefixes": ["join.", "witness."], "list": "demos/TwoParamOkConf/open-joins.txt"}},
    # the parameters from the coroutine language on its own, by hand over the translations of code;
    # built against TwoParamConf's phase
    "TwoParamInst": {"tier": "light", "sources": ["generated/corout",
                                                  "demos/TwoParamInst/TwoParamInst/Tr.lean",
                                                  "demos/TwoParamInst/TwoParamInst/Back.lean"]},
    # every segment ends (B's, INV-15): corout's measure, generated in generated/corout; built
    # against TwoParamInst's phase
    "TwoParamEnds": {"tier": "light"},
    # the transaction statement of the parameterized form (B's, INV-17): twoparam's measure, generated
    # in generated/twoparam, with TwoParamConf's `terminal_unique`; built against TwoParamConf's phase
    "TwoParamTx": {"tier": "light"},
    "TwoLayerTx": {"tier": "light"},
    # IMP++'s threads joined generically up to the flush of K's stdout stream, the theorem the
    # observation's (`confluence --threads threads --obs output --slots`), its races refuted at
    # peaks of the programs in demos/ImpPlusConf/witnesses
    # (the library impplus is the soundness area's, which records its sources)
    "ImpPlusConf": {"tier": "light", "sources": ["demos/ImpPlusConf/ImpPlusConf/Views.lean",
                                                 "demos/ImpPlusConf/ImpPlusConf/Slots.lean",
                                                 "demos/ImpPlusConf/confluence.toml"],
                    "slots": {"prefixes": ["join.", "flush."], "list": "demos/ImpPlusConf/open-joins.txt"}},
}

# SIMPLE's pairs of rules classified, and its slots by premise and class with their statuses
# (`confluence --threads --slots`)
OUTPUTS = {
    "simple-confluence.toml": {"tier": "heavy", "compare": "exact"},
}
