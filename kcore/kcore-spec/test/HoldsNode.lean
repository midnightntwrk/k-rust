/-
  The Holds lemma one constructor at a time (KcoreSpec/HoldsNode.lean), along an evaluation of a
  function's clauses (`holds_den4Cl`, KcoreSpec/OpenClauseDen.lean) and at the sort variable `R`
  (KcoreSpec/ClausePreTie.lean): each lemma exists and rests on no axiom beyond Lean's. A term's
  evaluation is read at a σ well sorted on the term's variables only (`evalTerm_den4ClPreOcc`), and
  a reading depends on σ at the variables read only (`TermAt.congr_occ`, `HoldsAt.congr_occ`, and
  `HoldsReadT.congr_NIR` for a truth value with its terms' readings). Run from the
  package root: `lake env lean -j1 test/HoldsNode.lean`.
-/
import KcoreSpec.ClausePreTie
import KcoreSpec.ClausePreCore

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
#print axioms termAt_of_all
#print axioms KCore.Faithful.holds_den4Cl
#print axioms KCore.Faithful.holds_den4ClPre
#print axioms nodeFacts_of_core
#print axioms holdsAt_atR
#print axioms withPre_interp
#print axioms KCore.Faithful.evalTerm_den4ClPreOcc
#print axioms KCore.Faithful.evalTerms_den4ClPreOcc
#print axioms KCore.Faithful.evalTerm_den4ClPre
#print axioms KCore.Faithful.evalTerms_den4ClPre
#print axioms TermAt.congr_occ
#print axioms HoldsAt.congr_occ
#print axioms HoldsReadT.congr_NIR
#print axioms HoldsReadT.holdsAt
