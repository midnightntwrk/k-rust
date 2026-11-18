/-
  The premises Γ builds directly as AML patterns apply Γ's heads only
  (KcoreSpec/TieHeadsAml.lean): the statements, and the axioms their proofs use.
  Run from the package root: `lake env lean -j1 test/TieHeadsAml.lean`.
-/
import KcoreSpec.TieHeadsAml

set_option autoImplicit false

open KCore KCore.Faithful KCore.GHWalk KCore.GHAml

#check @GHAml.InGH
#check @GHAml.symArityItem_inGH
#check @GHAml.sigItems_inGH
#check @GHAml.ΓSig_inGH
#check @GHAml.trAxiom_inGH
#check @GHAml.gens_ok
#check @GHAml.ovlArgs_cov
#check @GHAml.over_ok
#check @GHAml.consItemsK_inGH
#check @GHAml.ΓCons_inGH
#check @GHAml.collSyms_ks
#check @GHAml.collNoJunk_inGH
#check @GHAml.collAxioms_inGH
#check @GHAml.ΓColls_inGH
#check @GHAml.boolClosed_inGH
#check @GHAml.Γcl_inGH

/-- Under `coreOK`, a premise of the signature, the constructors, the collections or Bool's
closure applies no head Γ lacks. -/
example (c : Semantics) (h : c.coreOK = true) (φ : KoreAML.P)
    (hφ : ΓSig c φ ∨ ΓCons c φ ∨ ΓColls c φ ∨ Γcl c φ) (t : KoreAML.VarTable)
    (g : String × List Kore.KSort) (hg : headP t g ∉ gammaHeadsP c) : headP t g ∉ headsP φ := by
  intro hm
  apply hg
  rcases hφ with hφ | hφ | hφ | hφ
  · exact ΓSig_inGH φ hφ _ hm
  · exact ΓCons_inGH h φ hφ _ hm
  · exact ΓColls_inGH h φ hφ _ hm
  · exact Γcl_inGH φ hφ _ hm

#print axioms GHAml.sigItems_inGH
#print axioms GHAml.ΓSig_inGH
#print axioms GHAml.consItemsK_inGH
#print axioms GHAml.ΓCons_inGH
#print axioms GHAml.collNoJunk_inGH
#print axioms GHAml.ΓColls_inGH
#print axioms GHAml.Γcl_inGH
