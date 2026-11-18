/-
  The registry family on `f2-examples/ens.kompile.kore` (C14, the surplus of the signature), on the
  literals `kore` and `defn`. Run from the package root: `lake env lean -j1 test/TieEnsRegistry.lean`.

  `ss` and `ks` are computed from the text: the registry sorts it does not declare without sort
  parameters (18 of them), and the interpreted hooked symbols (`hookSigs`) it does not declare
  without sort parameters, the same two tests by which `surplusItem` classes an item of the
  signature as surplus.

  - `registry_detached`: `detachedB c ss ks = true`. Each conjunct is its own kernel decision, the
    signature's items by ranges (`tieAllE_range`), and `detachedB` is reassembled from them. By
    `detached_of_decided` the names of `ss` and `ks` are detached from `c` (`registry_names_detached`):
    every premise of the theory that names one of them is an item of the registry family
    (`RegistryItem`).
  - `surplus_registry`: every item of `sigItems c` that `surplusItem` classes as surplus (those of
    `sig_origin`, test/TieEnsSig.lean, that are no declaration's item) names one of those names, so
    it is a `RegistryItem` at them.
  - `ens_conservative`, `ens_exact_own`: the registry family at those names is conservative
    (`registry_conservative`) and no step at values rests on it (`exact_own`), under `FnHyp c`
    from the functions' obligations, each empty on the text by a kernel decision (`fnHyp`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEns

open KCore ML Faithful KoreAML DetachedB

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The registry sorts the text does not declare without sort parameters. -/
noncomputable def ss : List Srt := (List.range nRegSorts).filter fun s =>
  !(kore.sortDecls.any fun sd => sd.name == "Sort" ++ regSortNames.getD s "" && sd.params.isEmpty)

/-- The interpreted hooked symbols the text does not declare without sort parameters. -/
noncomputable def ks : List Sym := (hookSigs.map (·.name)).filter fun k =>
  !(kore.symbolDecls.any fun sd => sd.name == regSymNames.getD k "" && sd.params.isEmpty)

theorem ss_length : ss.length = 18 := by decide +kernel

/-! ## Decisions over a list, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem regAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-! ## `detachedB`, conjunct by conjunct -/

theorem sortsE : sortsB c ss ks = true := by decide +kernel
theorem hooksE : ks.all (fun k => hookSigs.any (·.name == k)) = true := by decide +kernel
theorem collsE : builtinColls.all (fun k => sOK c ss ks k.sort || (collAxioms c k).isEmpty) = true := by
  decide +kernel
theorem valuesE : valuesB c ss ks = true := by decide +kernel
theorem graphsE : graphsB c ss ks = true := by decide +kernel
theorem itemsE : (consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all
    (fun it => clean c ss ks it.pat) = true := by decide +kernel
theorem allCollsE : c.allColls.all (fun k =>
    if builtinColls.contains k && ss.contains k.sort then (collAxioms c k).isEmpty
    else clean c ss ks (collNoJunk c k) && (collAxioms c k).all (clean c ss ks)) = true := by decide +kernel
theorem boolE : clean c ss ks (boolClosed c) = true := by decide +kernel

/-- An item of the signature: it names none of the names or is the registry's own (`listsB`), and
where `surplusItem` classes it as surplus it names one of them. -/
noncomputable def sigP (it : Item) : Bool :=
  (clean c ss ks it.pat || regSig c ss ks it.pat) &&
    (!surplusItem kore it || (psyms it.pat).any (isName c ss ks))

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigP = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 26).all sigP = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigP = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigP = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigP = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigP = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigP = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigP = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigP = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigP = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigP = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigP = true := by decide +kernel
theorem sigE_190 : ((sigItems c).drop 190).all sigP = true := by decide +kernel

theorem sigE : (sigItems c).all sigP = true :=
    regAllE_range (a := 0) (n := 34) sigE_0 <|
    regAllE_range (a := 34) (n := 26) sigE_34 <|
    regAllE_range (a := 60) (n := 13) sigE_60 <|
    regAllE_range (a := 73) (n := 13) sigE_73 <|
    regAllE_range (a := 86) (n := 13) sigE_86 <|
    regAllE_range (a := 99) (n := 13) sigE_99 <|
    regAllE_range (a := 112) (n := 13) sigE_112 <|
    regAllE_range (a := 125) (n := 13) sigE_125 <|
    regAllE_range (a := 138) (n := 13) sigE_138 <|
    regAllE_range (a := 151) (n := 13) sigE_151 <|
    regAllE_range (a := 164) (n := 13) sigE_164 <|
    regAllE_range (a := 177) (n := 13) sigE_177 <|
    sigE_190

theorem sigP_of {it : Item} (h : it ∈ sigItems c) :
    (clean c ss ks it.pat || regSig c ss ks it.pat) = true ∧
      (!surplusItem kore it || (psyms it.pat).any (isName c ss ks)) = true :=
  Bool.and_eq_true_iff.mp (List.all_eq_true.mp sigE it h)

/-! ## The registry family -/

/-- **`detachedB` holds on ens** at the registry sorts and interpreted hooked symbols the text does
not declare. -/
theorem registry_detached : detachedB c ss ks = true := by
  have hs : (sigItems c).all (fun it => clean c ss ks it.pat || regSig c ss ks it.pat) = true :=
    List.all_eq_true.mpr fun it h => (sigP_of h).1
  simp only [detachedB, listsB, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨sortsE, hooksE⟩, collsE⟩, ⟨⟨⟨hs, itemsE⟩, allCollsE⟩, boolE⟩⟩, valuesE⟩, graphsE⟩

/-- The names of `ss` and `ks` are detached from `c`. -/
theorem registry_names_detached : Detached c (DetachedB.names c ss ks) :=
  detached_of_decided c ss ks coreOK registry_detached

/-- **Every surplus item of the signature is a `RegistryItem`** at the names of `ss` and `ks`: it
is a premise of the theory (an item of `sigItems c`) naming one of them. -/
theorem surplus_registry : ∀ it ∈ sigItems c, surplusItem kore it = true →
    RegistryItem c (DetachedB.names c ss ks) it.pat := by
  intro it hit hsur
  have h2 := (sigP_of hit).2
  rw [hsur, Bool.not_true, Bool.false_or] at h2
  obtain ⟨σ, hσ, hn⟩ := List.any_eq_true.mp h2
  have hΓ : (Γc c ∪ Γstep c) it.pat :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨it, hit, rfl⟩)))))))))
  exact registry_names_detached.2.2 it.pat hΓ ⟨σ, hσ, isName_iff.mp hn⟩

/-! ## The registry family is conservative on ens -/

def callOrder : List Nat := [364]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- What the statements assume of ens' functions, from their obligations, none open. -/
theorem fnHyp : FnHyp c :=
  fnHyp_of_fnObligations coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) ParamsTotal.nil
    (FnObligations.of_nil term_named total_named agree_named match_named)

/-- **The registry family at the names ens does not declare is conservative.** -/
theorem ens_conservative : RegistryConservative c (DetachedB.names c ss ks) :=
  registry_conservative (hpreTop := by decide +kernel) c ss ks coreOK fnHyp registry_detached

/-- **No step of ens at values rests on the registry family** at the names it does not declare. -/
theorem ens_exact_own : ExactOwn c (DetachedB.names c ss ks) :=
  exact_own (hpreTop := by decide +kernel) c ss ks coreOK fnHyp registry_detached

end KCore.TieEns

#check @KCore.TieEns.ens_conservative
#check @KCore.TieEns.ens_exact_own
#check @KCore.TieEns.registry_detached
#check @KCore.TieEns.surplus_registry
#print axioms KCore.TieEns.registry_detached
#print axioms KCore.TieEns.surplus_registry

/-- info: 'KCore.TieEns.ens_exact_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEns.ens_exact_own
/-- info: 'KCore.TieEns.ens_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEns.ens_conservative
