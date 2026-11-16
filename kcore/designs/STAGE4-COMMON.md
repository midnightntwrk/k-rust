# Stage-4 common brief (every lane R/F/V; read after RULES.md)

Base: BASE-1 head cd4909b2 (CN-3 U1 complete + RC-2 + C6). Main checkout (read-only spec):
/home/sebastiengllmt/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust/draft-personal/k-semantics-core-2026-11/
- designs/CN-3-merged-constructs.md: READ ITS TOP "Annotations after U1" FIRST; §2-3 are fixed texts no lane edits; §4 is your lane.
- findings/CN3-ADD-addendum.md, findings/REVIEW-CN3-ADD.md, findings/REVIEW-U1c.md, findings/HOOK-READING-decision.md.
- TICKETS-2026-11-11.toml: the [goal] table, and the entries "BASE-1 partial", "U1a+U1b DONE", "REVIEW-U1c DONE".

Standing rulings:
1. Parentheses around each `⊧` conjunct are authorised (`⊧` binds at 26, below `∧`); do not stop on them.
2. No lane edits a declaration of CN-3 §2 or §3, or another lane's owned declarations (CN-3 §4). Lane R owns `rulesPlain`'s body, F `clausesPlain`'s, V `paramsPlain`'s; all three now sit in Tie.lean (C6 done), and `ok`/`okAll`/`okT`/`okHeadT` conjoin them. Do not edit `declsOK`, `ok`, `okAll` or the generator's plain decision (KcoreGen `plain` argument) unless your brief names it.
3. Headline/pinned statements do not change. Pins, test/pins-peano.sh, Axioms, Witnesses must pass unchanged. If a fixed text does not elaborate, or a pinned statement would have to change, STOP that unit and report with the Lean error.
4. Cone reporting: run lake-serial on test/ConeV.lean (or `lake env lean test/ConeV.lean` under the memory scope), then `python3 -I test/cone.py <main>/core-cone.txt .lake/cone-v.txt --old-rev <rev the committed cone was computed at> --diff` (from kcore-merge 0e4ddd03 on, cone.py compares each declaration's text and the roots section; in a tree branched before it, copy that test/cone.py in, or give the plain textual `diff` of the changed cone entries by hand). Every changed or added declaration must be yours by CN-3 §4 or newly reached by one of yours.
5. AM-3: regenerate the Cond.bound cone (test/ReviewCone.lean writes findings/work/review-cone/core-bound.txt). Its declarations, their line spans and its roots must be identical to the committed file; the third column (source file length) may move. A lane may change a declaration of that cone that it owns by CN-3 §4 (report each moved declaration/span and why); a change to Cond.bound itself, or to a reached declaration owned by no lane or by another lane, is a STOP. (Corrected 2026-11-16 after V1.) Restore the committed review-cone files afterwards; cones are regenerated at INT.
6. Generated package files are regenerated at INT, not merged: run test/regen.sh and report the diff, but commit regenerated packages only if your change intends a generated-text change, and say why.
7. A lane's validation is RULES line 41's; never run.sh/final.sh/judge/syn30/syn100, no example kernel rebuilds, no sleep/poll loops.
8. KcoreGen.lean's headlineAt/genWf/genFnHyp/genTie take a `plain` argument (BASE-1); keep it.
