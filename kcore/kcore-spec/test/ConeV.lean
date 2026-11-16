/-
  The review cone (v) of test/ReviewCone.lean (the core with the hypothesis on the functions), written
  to .lake/cone-v.txt for test/cone.py to compare with the committed cone. Run from the package root:
  `lake env lean test/ConeV.lean`.
-/
import KcoreSpec
import KcoreSpec.ReviewCone

#review_cone "(v) KCore core: soundness and completeness over a semantics, from the hypothesis on its functions" [KCore.SoundC, KCore.CompleteC, KCore.ExactC, KCore.StepIs, KCore.Semantics.coreOK, KCore.FnHyp]
  to ".lake/cone-v.txt"
