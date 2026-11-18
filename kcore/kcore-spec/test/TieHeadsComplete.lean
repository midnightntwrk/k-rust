/-
  Every head a premise of the theory applies is one of Γ's heads (KcoreSpec/TieHeadsComplete.lean):
  the statements, and the axioms their proofs use.
  Run from the package root: `lake env lean -j1 test/TieHeadsComplete.lean`.
-/
import KcoreSpec.TieHeadsComplete

set_option autoImplicit false

open KCore KCore.Faithful KCore.GHWalk KCore.GHAml KCore.GHComplete

#check @GHComplete.kernelItems_inGH
#check @GHComplete.fnItems_inGH
#check @GHComplete.ruleItems_inGH
#check @GHComplete.closureDisjunct_inGH
#check @GHComplete.Γstep_inGH
#check @GHComplete.gamma_heads_complete
#check @GHComplete.trSort_eq_sortSym
#check @GHComplete.headP_mem_iff
#check @GHComplete.gamma_lacks_head
#check @GHComplete.headsA_of_psyms
#check @GHComplete.premise_symbol_names

/-- The statement, written out: under `coreOK`, each head of each premise of the theory with the
step's closure is the translation of one of `gammaHeads c`. -/
example (c : Semantics) (h : c.coreOK = true) (φ : KoreAML.P) (hφ : (Γc c ∪ Γstep c) φ)
    (g : String × List KoreAML.P) (hg : g ∈ headsP φ) :
    ∃ g' ∈ gammaHeads c, headP [] g' = g :=
  List.mem_map.mp (gamma_heads_complete c h φ hφ g hg)

/-- What `gammaHasHead` decides is about the theory: a head it refuses is in no premise, at any
variable table. -/
example (c : Semantics) (h : c.coreOK = true) (g : String × List Kore.KSort)
    (hg : gammaHasHead c g = false) (φ : KoreAML.P) (hφ : φ ∈ Γc c) (t : KoreAML.VarTable) :
    headP t g ∉ headsP φ :=
  gamma_lacks_head c h g hg φ (Or.inl hφ) t

/-- `ite` at a sort Γ has no symbol for, and `inj` at a pair outside `subsorts`, are such heads:
the reader tells `Lblite SortK` from `Lblite`. -/
example : headP [] ("Lblite", [KoreAML.srt "K"]) ≠ headP [] ("Lblite", []) := by decide

/-- A head and its translation are in Γ's lists together. -/
example (c : Semantics) (t : KoreAML.VarTable) (g : String × List Kore.KSort)
    (hg : g ∉ gammaHeads c) : headP t g ∉ gammaHeadsP c :=
  fun hm => hg (headP_mem_iff.mp hm)

/-- The names: a symbol of a premise is `inj` or named as the head of a symbol of `kernelSyms`. -/
example (c : Semantics) (h : c.coreOK = true) (φ : KoreAML.P) (hφ : (Γc c ∪ Γstep c) φ) (n : String)
    (hn : KoreAML.Sym.symbol n ∈ psyms φ) (hni : n ≠ "inj") :
    ∃ k ∈ kernelSyms c, n = (gammaHead c k.name).1 :=
  (premise_symbol_names c h φ hφ n hn).resolve_left hni

#print axioms GHComplete.gamma_heads_complete
#print axioms GHComplete.headP_mem_iff
#print axioms GHComplete.gamma_lacks_head
#print axioms GHComplete.premise_symbol_names
