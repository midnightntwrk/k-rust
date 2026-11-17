/-
  The review cone (v) of test/ReviewCone.lean (the core with the hypothesis on the functions, and
  the definitions the rows' statements and the tie's mention),
  computed from the root list test/roots.toml and written to .lake/cone-v.txt for test/cone.py to
  compare with the committed cone. Run from the package root: `lake env lean test/ConeV.lean`.
-/
import KcoreSpec
import KcoreSpec.ReviewCone

#review_cone_roots "test/roots.toml" to ".lake/cone-v.txt"
