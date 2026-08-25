#!/usr/bin/env python3
"""Verify the accepted pre-CF Java hook was reused without algorithm changes."""

import sys
from pathlib import Path

task, accepted = (Path(value) for value in sys.argv[1:])
task_text = task.read_text(encoding="utf-8")
task_text = task_text.replace("R3_G_05", "R3_G_02").replace("R3-G-05", "R3-G-02")
expected = accepted.read_text(encoding="utf-8")
scratch_repair = (
    ("  private final Path recordPath;", "  private final Path javaScratch;"),
    ("      Path recordPath,\n      String primarySource,",
     "      Path javaScratch,\n      String primarySource,"),
    ("    this.recordPath = recordPath;", "    this.javaScratch = javaScratch;"),
    ("runK(request.program, kDefinition, recordPath)",
     "runK(request.program, kDefinition, javaScratch)"),
    ("private static String runK(String program, Path definition, Path recordPath)",
     "private static String runK(String program, Path definition, Path javaScratch)"),
    ("      Path parent = recordPath.getParent(); Files.createDirectories(parent);\n"
     "      Path file = Files.createTempFile(parent, \"configuration-\", \".kink\");",
     "      Path file = Files.createTempFile(javaScratch, \"configuration-\", \".kink\");"),
)
for original, repaired in scratch_repair:
    if expected.count(original) != 1:
        raise SystemExit("accepted pre-CF source no longer has the expected scratch authority")
    expected = expected.replace(original, repaired)
if task_text != expected:
    raise SystemExit(
        "task pre-CF hook differs beyond task naming and the exact stable-scratch repair")
