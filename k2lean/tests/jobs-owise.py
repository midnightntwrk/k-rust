#!/usr/bin/env python3
"""Write the fixture jobs with an `owise` rule, for `k2lean confluence --equiv` with priority ranks.

usage: jobs-owise.py JOBS_K OUT_K

Writes tests/fixtures/jobs/jobs.k with `run` for a positive job only (`requires J >Int 0`) and a
job that is not positive run by an `owise` rule at priority 200, after the default 50: it is
marked run and appended to `<done>` but not added to `<total>`, and it runs only once no positive
job is left (`J:Int |-> (false => true)`, labelled `last`). The cells are the fixture's, so
`--equiv done=perm` reads them unchanged (`demos/JobsOwConf`, `docs/design.md`, section 3.6). The
script fails if the file does not contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ("""       <done> ... (.List => ListItem(J)) </done> [label(run)]
""", """       <done> ... (.List => ListItem(J)) </done> requires J >Int 0 [label(run)]
  rule <jobs> ... J:Int |-> (false => true) ... </jobs>
       <done> ... (.List => ListItem(J)) </done> [owise, label(last)]
"""),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"jobs-owise.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
