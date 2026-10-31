# The noninterference area's registry (tests/gate-check.py loads it; the gate phases are in
# noninterference.sh). The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    "ImpNI": {"tier": "light", "sources": ["generated/kimpni", "generated/impsec",
                                           "demos/ImpNI/ImpNI/Tr.lean", "demos/ImpNI/ImpNI/NI.lean",
                                           "demos/ImpNI/ImpNI/Spec.lean",
                                           "demos/ImpNI/ImpNI/Levels.lean", "demos/ImpNI/ImpNI/Stack.lean",
                                           "demos/ImpNI/ImpNI/Proof.lean",
                                           "demos/ImpNI/correspondence.toml", "demos/ImpNI/noninterference.toml"]},
    "ContractNI": {"tier": "light", "sources": ["generated/contract", "generated/contractsec",
                                                "demos/ContractNI/ContractNI/Tr.lean",
                                                "demos/ContractNI/ContractNI/NI.lean",
                                                "demos/ContractNI/ContractNI/Spec.lean",
                                                "demos/ContractNI/ContractNI/Levels.lean",
                                                "demos/ContractNI/ContractNI/Stack.lean",
                                                "demos/ContractNI/ContractNI/Proof.lean",
                                                "demos/ContractNI/correspondence.toml",
                                                "demos/ContractNI/noninterference.toml"]},
}
