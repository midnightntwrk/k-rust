#!/usr/bin/env python3
"""Write the fixture jobs with jobs removed from the map, or inserted into it, for
`k2lean confluence --equiv` without threads.

usage: jobs-remove.py JOBS_K OUT_K MODE

Writes tests/fixtures/jobs/jobs.k with the map losing bindings, so that two steps each remove a
different binding of it:
- `remove`: `run` removes the job it runs (`J:Int |-> false => .Map`) instead of marking it;
- `drop`: `run` marks the job as the fixture does, and a rule `drop` removes a job that has run
  (`_:Int |-> true => .Map`), so a removal meets an update at another binding;
- `submit`: `run` removes the job it runs, as in `remove`, and rules `even` and `odd` insert a job
  numbered by a counter of their own (`<evens>`, `<odds>`; keys `2 *Int N` and `2 *Int N +Int 1`),
  so a removal meets an insertion, and an insertion one at another key.
The other cells are the fixture's, so `--equiv done=perm` reads them unchanged (`demos/JobsRmConf`,
`demos/JobsDropConf`, `demos/JobsSubConf`, `docs/design.md`, section 3.6). The script fails if the file does not
contain exactly the text it rewrites.
"""
import sys

src, dst, mode = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(src).read()
run = "  rule <jobs> ... J:Int |-> (false => true) ... </jobs>\n"
remove = (run, "  rule <jobs> ... J:Int |-> false => .Map ... </jobs>\n")
edits = {
    "remove": [remove],
    "drop": [
        (
            "       <done> ... (.List => ListItem(J)) </done> [label(run)]\n",
            "       <done> ... (.List => ListItem(J)) </done> [label(run)]\n"
            "  rule <jobs> ... _:Int |-> true => .Map ... </jobs> [label(drop)]\n",
        )
    ],
    "submit": [
        remove,
        (
            "      <done> .List </done>\n",
            "      <done> .List </done>\n      <evens> 0 </evens>\n      <odds> 0 </odds>\n",
        ),
        (
            "       <done> ... (.List => ListItem(J)) </done> [label(run)]\n",
            "       <done> ... (.List => ListItem(J)) </done> [label(run)]\n"
            "  rule <evens> N => N +Int 1 </evens>\n"
            "       <jobs> ... .Map => 2 *Int N |-> false ... </jobs> [label(even)]\n"
            "  rule <odds> N => N +Int 1 </odds>\n"
            "       <jobs> ... .Map => 2 *Int N +Int 1 |-> false ... </jobs> [label(odd)]\n",
        ),
    ],
}
if mode not in edits:
    sys.exit(f"jobs-remove.py: MODE is one of {', '.join(edits)}")
for old, new in edits[mode]:
    if text.count(old) != 1:
        sys.exit(f"jobs-remove.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
