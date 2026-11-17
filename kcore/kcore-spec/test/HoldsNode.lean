/-
  The Holds lemma one constructor at a time (KcoreSpec/HoldsNode.lean): each lemma exists and
  rests on no axiom beyond Lean's. Run from the package root: `lake env lean -j1 test/HoldsNode.lean`.
-/
import KcoreSpec.HoldsNode

open KCore KCore.HoldsShape

#print axioms holdsAt_of_den
#print axioms AtomFacts.termAt
#print axioms wellSorted_extN
#print axioms holdsAt_top
#print axioms holdsAt_bot
#print axioms holdsAt_not
#print axioms holdsAt_and
#print axioms holdsAt_or
#print axioms holdsAt_implies
#print axioms holdsAt_ceil
#print axioms holdsAt_equals
#print axioms holdsAt_mem
#print axioms holdsAt_ex
#print axioms holdsAt_all
#print axioms holdsAt_exMatch
