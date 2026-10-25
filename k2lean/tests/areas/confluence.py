# The confluence area's registry (tests/gate-check.py loads it; the gate phases are in confluence.sh).
# The format of every area's registry is described in gate-check.py's docstring.

DEMOS = {
    "RaceConf": {"tier": "light", "sources": ["generated/race",
                                              "demos/RaceConf/RaceConf/Confluence.lean", "demos/RaceConf/confluence.toml"]},
}

# SIMPLE's pairs of rules classified (`confluence --report-only`)
OUTPUTS = {
    "simple-confluence.toml": {"tier": "heavy", "compare": "exact"},
}
