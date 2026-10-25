# The noninterference area's registry (tests/gate-check.py loads it; the gate phases are in
# noninterference.sh). The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    "ImpNI": {"tier": "light", "sources": ["generated/impsec",
                                           "demos/ImpNI/ImpNI/Tr.lean", "demos/ImpNI/ImpNI/NI.lean",
                                           "demos/ImpNI/ImpNI/Levels.lean", "demos/ImpNI/ImpNI/Stack.lean",
                                           "demos/ImpNI/ImpNI/Proof.lean",
                                           "demos/ImpNI/correspondence.toml", "demos/ImpNI/noninterference.toml"]},
}
