#!/usr/bin/env python3
"""Write the fixture jobs with jobs removed from the map, for `k2lean confluence --equiv` without
threads.

usage: jobs-remove.py JOBS_K OUT_K MODE

Writes tests/fixtures/jobs/jobs.k with the map losing bindings, so that two steps each remove a
different binding of it:
- `remove`: `run` removes the job it runs (`J:Int |-> false => .Map`) instead of marking it;
- `drop`: `run` marks the job as the fixture does, and a rule `drop` removes a job that has run
  (`_:Int |-> true => .Map`), so a removal meets an update at another binding.
The other cells are the fixture's, so `--equiv done=perm` reads them unchanged (`demos/JobsRmConf`,
`demos/JobsDropConf`, `docs/design.md`, section 3.6). The script fails if the file does not
contain exactly the text it rewrites.
"""
import sys

src, dst, mode = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(src).read()
run = "  rule <jobs> ... J:Int |-> (false => true) ... </jobs>\n"
edits = {
    "remove": [(run, "  rule <jobs> ... J:Int |-> false => .Map ... </jobs>\n")],
    "drop": [
        (
            "       <done> ... (.List => ListItem(J)) </done> [label(run)]\n",
            "       <done> ... (.List => ListItem(J)) </done> [label(run)]\n"
            "  rule <jobs> ... _:Int |-> true => .Map ... </jobs> [label(drop)]\n",
        )
    ],
}
if mode not in edits:
    sys.exit(f"jobs-remove.py: MODE is one of {', '.join(edits)}")
for old, new in edits[mode]:
    if text.count(old) != 1:
        sys.exit(f"jobs-remove.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
