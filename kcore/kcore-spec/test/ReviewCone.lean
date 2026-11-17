/-
  The review cones of KCore (KCORE-SPEC.md §10), written to .lake/review-cone-*.txt (in the build
  directory, as test/ConeV.lean's .lake/cone-v.txt; the committed cone (v) is ../core-cone.txt).
  Run from the package root, after `lake build`:

      lake env lean test/ReviewCone.lean

  (i)   the step relation: the frozen layer a user's statement over F2 reads (F2 has no per-project
        statements yet; F1's comparable cone is its step relation, m3-spec/cone/f1-step.txt);
  (ii)  the emit route: F2's `emit` and `wf`;
  (iii) the root track: soundness and completeness over F2, with `parse` read by its type only;
  (iv)  the core: soundness and completeness over a semantics, with what they assume of it
        (`Semantics.coreOK`, `CoreObligations`), written to .lake/review-cone-core.txt;
  (v)   the core with the semantic hypothesis on the functions (`FnHyp`) in place of the named
        obligations, with the definitions the rows' statements and the tie's mention, its roots
        and opaque declarations the list test/roots.toml (test/ConeV.lean computes the same cone),
        written to .lake/review-cone-core-hyp.txt;
  (vi)  the texts the statements over the plain step read (`SoundC₀`, `CompleteC₀` and the lemmas
        that say each edited declaration is the plain one where the definition is plain), written
        to .lake/review-cone-core-old.txt;
  (vii) the binders of a condition (`Cond.bound`), read by `ruleSorted` and `clauseSorted` once
        they admit a condition other than `\top`, written to .lake/review-cone-core-bound.txt.
-/
import KcoreSpec
import KcoreSpec.ReviewCone

#review_cone "(i) KCore step relation" [KCore.Step]
  to ".lake/review-cone-f2-i-step.txt"

#review_cone "(ii) KCore emit route: emit and wf" [KCore.emit, KCore.Definition.emit, KCore.wf]
  to ".lake/review-cone-f2-ii-emit-route.txt"

#review_cone "(iii) KCore root track: soundness and completeness over KCore" [KCore.Sound, KCore.Complete, KCore.StepIs, KCore.wf, KCore.Tied]
  opaque [KCore.Parse.parse] to ".lake/review-cone-f2-iii-root-track.txt"

#review_cone "(iv) KCore core: soundness and completeness over a semantics" [KCore.SoundC, KCore.CompleteC, KCore.ExactC, KCore.StepIs, KCore.Semantics.coreOK, KCore.CoreObligations]
  to ".lake/review-cone-core.txt"

#review_cone_roots "test/roots.toml" to ".lake/review-cone-core-hyp.txt"

#review_cone "(vi) KCore: the texts before U1" [KCore.SoundC₀, KCore.CompleteC₀, KCore.step_plain,
    KCore.eval_plain, KCore.evalTerm_plain, KCore.fails_plain, KCore.applies_of_binds,
    KCore.prioRuleK_plain, KCore.fnItems_plain, KCore.Faithful.Γc_plain]
  to ".lake/review-cone-core-old.txt"

#review_cone "(vii) KCore: the binders of a condition (read by ruleSorted and clauseSorted from lanes R1, F1 on)"
    [KCore.Cond.bound] to ".lake/review-cone-core-bound.txt"
