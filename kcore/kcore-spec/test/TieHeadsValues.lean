/-
  The values and graphs in Γ apply Γ's heads only (KcoreSpec/TieHeadsValues.lean): the
  statements, and the axioms their proofs use.
  Run from the package root: `lake env lean -j1 test/TieHeadsValues.lean`.
-/
import KcoreSpec.TieHeadsValues

set_option autoImplicit false

open KCore KCore.Faithful KCore.GHWalk KCore.GHAml KCore.GHVal

#check @GHVal.valHead_mem
#check @GHVal.kore_val
#check @GHVal.koreList_val
#check @GHVal.den_val
#check @GHVal.symApp_val
#check @GHVal.ΓDomains_inGH
#check @GHVal.ΓFallback_inGH

/-- Under `coreOK`, a value's KORE applies only heads of Γ. -/
example (c : Semantics) (h : c.coreOK = true) (v : GroundTerm) (s : Srt) (hv : c.sortOf v = some s) :
    ∀ g ∈ appHeadsOf (v.kore c), g ∈ gammaHeads c :=
  kore_val h v s hv

/-- Under `coreOK`, a premise of the domains or of the fallback applies no head Γ lacks. -/
example (c : Semantics) (h : c.coreOK = true) (φ : KoreAML.P) (hφ : ΓDomains c φ ∨ ΓFallback c φ)
    (t : KoreAML.VarTable) (g : String × List Kore.KSort) (hg : headP t g ∉ gammaHeadsP c) :
    headP t g ∉ headsP φ := by
  intro hm
  apply hg
  rcases hφ with hφ | hφ
  · exact ΓDomains_inGH h φ hφ _ hm
  · exact ΓFallback_inGH h φ hφ _ hm

#print axioms GHVal.kore_val
#print axioms GHVal.den_val
#print axioms GHVal.ΓDomains_inGH
#print axioms GHVal.ΓFallback_inGH
