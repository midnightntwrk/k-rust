/-
  Layer 1 of the tie on `f2-examples/rulecool.kompile.kore` (fixture e2-rule): `wf defn = true`, by
  the kernel, and `not_reordered`: the emitted user module and the text's differ in length (test/TieRuleCoolText.lean holds the rest of the tie). Run from the package root:
  `lake env lean -j1 test/TieRuleCoolWf.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCoolWf

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-- `Reordered` keeps the length of each module. -/
theorem reordered_lengths {e k : Kore.Definition} (h : Reordered e k) :
    (e.modules.zip k.modules).all (fun mm => mm.1.sentences.length == mm.2.sentences.length) = true :=
  List.all_eq_true.mpr fun mm hm => beq_iff_eq.mpr (h.2.2 mm hm).2.2.length_eq

theorem lengths_differ :
    (defn.emit.modules.zip kore.modules).all (fun mm => mm.1.sentences.length == mm.2.sentences.length) = false := by
  decide +kernel

/-- **`defn` does not print back to the text up to order**, so `Tied kore` fails at its last
conjunct. -/
theorem not_reordered : ¬ Reordered defn.emit kore := fun h => by
  have := reordered_lengths h
  rw [lengths_differ] at this
  exact Bool.false_ne_true this

end KCore.TieRuleCoolWf

#print axioms KCore.TieRuleCoolWf.wf_defn
#print axioms KCore.TieRuleCoolWf.not_reordered
