/-
  The registry family on kimp's text as kompile wrote it (C14, the surplus of the signature;
  `examples/ref-kimp/RefKimp/definition.kore`), on the literals `kore` and `defn`. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean -j1 test/TieKimpRegistry.lean`.

  `ss` and `ks` are computed from the text: the registry sorts it does not declare without sort
  parameters, and the interpreted hooked symbols (`hookSigs`) it does not declare without sort
  parameters, the same two tests by which `surplusItem` classes an item of the signature as
  surplus. They are the lists `ssL` (18 sorts) and `ksL` (78 symbols) written out (`ss_eq`,
  `ks_eq`, a kernel decision each); the conjuncts are decided at the written lists, which costs
  the kernel less (`graphsB` on kimp: 6.8 GiB at the written lists, 10.2 GiB at the computed ones).

  - `registry_detached`: `detachedB c ss ks = true`. Each conjunct is its own kernel decision, and
    `detachedB` is reassembled from them. The signature's 263 items are decided by ranges
    (`regAllE_range`), once for `listsB`'s conjunct (`sigCE`) and once for the surplus items
    (`sigSE`). The items of the other lists (the constructors', the functions', the
    rules', the closure item of the step) are decided list by list on `cleanF`, which is `clean`
    computed by recursion on the pattern (`cleanF_eq`): one decision of the four lists together
    exceeds 12 GiB.
    By `detached_of_decided` the names of `ss` and `ks` are detached from `c`
    (`registry_names_detached`): every premise of the theory that names one of them is an item of
    the registry family (`RegistryItem`).
  - `surplus_registry`: every item of `sigItems c` that `surplusItem` classes as surplus (those of
    `sig_origin`, test/TieKimpSig.lean, that are no declaration's item) names one of those names,
    so it is a `RegistryItem` at them.
  - `kimp_conservative`, `kimp_exact_own`: the registry family at those names is conservative
    (`registry_conservative`) and no step at values rests on it (`exact_own`), under `FnHyp c`
    from the functions' obligations, each empty on the text by a kernel decision (`fnHyp`).
  - `kimp_registry_everyH`: the names detached, the family conservative and no step at values resting on
    it, at `c.withHooks H` for every H: `detachedB` reads no
    interpretation (`detachedB_withHooks`), and the obligations, empty and read under none, give
    `FnHyp (c.withHooks H)` (`fnHyp_everyH`, by `fnHyp_decided`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimpRegistry

open KCore ML Faithful KoreAML DetachedB

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap
theorem preTop : c.clausesPreTop = true := by decide +kernel

/-- The registry sorts the text does not declare without sort parameters. -/
noncomputable def ss : List Srt := (List.range nRegSorts).filter fun s =>
  !(kore.sortDecls.any fun sd => sd.name == "Sort" ++ regSortNames.getD s "" && sd.params.isEmpty)

/-- The interpreted hooked symbols the text does not declare without sort parameters. -/
noncomputable def ks : List Sym := (hookSigs.map (·.name)).filter fun k =>
  !(kore.symbolDecls.any fun sd => sd.name == regSymNames.getD k "" && sd.params.isEmpty)

/-- `ss`, written out. -/
def ssL : List Srt := [8, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-- `ks`, written out. -/
def ksL : List Sym := [233, 234, 230, 231, 232, 228, 236, 238, 239, 240, 252, 255, 256, 257, 258, 259, 260, 226, 227,
  222, 223, 237, 261, 253, 254,
  263, 264, 266, 267, 268, 269, 270, 271, 273, 277, 280, 282, 283, 284, 281, 285, 286, 287, 288, 289,
  290, 265, 278, 272, 304, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 299, 305, 379, 357, 358, 359,
  360, 361, 362, 363, 364, 365, 366, 367, 369, 370, 371, 368]

theorem ss_eq : ss = ssL := by decide +kernel
theorem ks_eq : ks = ksL := by decide +kernel

/-! ## Decisions over a list, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem regAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-! ## `clean`, by recursion on the pattern -/

/-- `clean`, by recursion on the pattern, with no list of its symbols built. -/
def cleanF (c : Semantics) (ss : List Srt) (ks : List Sym) : KoreAML.P → Bool
  | .symbol σ => !isName c ss ks σ
  | .application a b | .implication a b => cleanF c ss ks a && cleanF c ss ks b
  | .existential _ a | .mu _ a => cleanF c ss ks a
  | _ => true

theorem cleanF_eq (c : Semantics) (ss : List Srt) (ks : List Sym) :
    ∀ φ : KoreAML.P, cleanF c ss ks φ = clean c ss ks φ
  | .symbol σ => by simp [cleanF]
  | .application a b => by rw [cleanF, cleanF_eq c ss ks a, cleanF_eq c ss ks b]; exact (clean_app a b).symm
  | .implication a b => by rw [cleanF, cleanF_eq c ss ks a, cleanF_eq c ss ks b]; exact (clean_imp a b).symm
  | .existential x a => by rw [cleanF, cleanF_eq c ss ks a]; exact (clean_ex x a).symm
  | .mu X a => by rw [cleanF, cleanF_eq c ss ks a]; exact (clean_mu X a).symm
  | .evar _ => rfl
  | .svar _ => rfl
  | .bottom => rfl

/-! ## `detachedB` at the written lists, conjunct by conjunct -/

theorem sortsE : sortsB c ssL ksL = true := by decide +kernel
theorem hooksE : ksL.all (fun k => hookSigs.any (·.name == k)) = true := by decide +kernel
theorem collsE : builtinColls.all (fun k => sOK c ssL ksL k.sort || (collAxioms c k).isEmpty) = true := by
  decide +kernel
theorem valuesE : valuesB c ssL ksL = true := by decide +kernel
theorem graphsE : graphsB c ssL ksL = true := by decide +kernel
theorem allCollsE : c.allColls.all (fun k =>
    if builtinColls.contains k && ssL.contains k.sort then (collAxioms c k).isEmpty
    else clean c ssL ksL (collNoJunk c k) && (collAxioms c k).all (clean c ssL ksL)) = true := by decide +kernel
theorem boolE : clean c ssL ksL (boolClosed c) = true := by decide +kernel

theorem consE : (consItemsK c).all (fun it => cleanF c ssL ksL it.pat) = true := by decide +kernel
theorem fnE : (fnItems c).all (fun it => cleanF c ssL ksL it.pat) = true := by decide +kernel
theorem ruleE : (ruleItems c).all (fun it => cleanF c ssL ksL it.pat) = true := by decide +kernel
theorem closureE : cleanF c ssL ksL (stepClosureItem c).pat = true := by decide +kernel

theorem itemsE : (consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all
    (fun it => clean c ssL ksL it.pat) = true := by
  rw [List.all_eq_true]
  intro it hit
  rw [← cleanF_eq]
  simp only [List.mem_append, List.mem_singleton] at hit
  rcases hit with ((h | h) | h) | h
  · exact List.all_eq_true.mp consE it h
  · exact List.all_eq_true.mp fnE it h
  · exact List.all_eq_true.mp ruleE it h
  · rw [h]; exact closureE

/-- An item of the signature names none of the names or is the registry's own (`listsB`). -/
noncomputable def sigC (it : Item) : Bool := clean c ssL ksL it.pat || regSig c ssL ksL it.pat

/-- An item of the signature that `surplusItem` classes as surplus names one of the names. The
names are looked for first: where one is found, `surplusItem`'s search of the text is not made. -/
noncomputable def sigS (it : Item) : Bool := (psyms it.pat).any (isName c ssL ksL) || !surplusItem kore it

theorem sigCE_0 : (((sigItems c).drop 0).take 31).all sigC = true := by decide +kernel
theorem sigCE_31 : (((sigItems c).drop 31).take 35).all sigC = true := by decide +kernel
theorem sigCE_66 : (((sigItems c).drop 66).take 35).all sigC = true := by decide +kernel
theorem sigCE_101 : (((sigItems c).drop 101).take 35).all sigC = true := by decide +kernel
theorem sigCE_136 : (((sigItems c).drop 136).take 35).all sigC = true := by decide +kernel
theorem sigCE_171 : (((sigItems c).drop 171).take 11).all sigC = true := by decide +kernel
theorem sigCE_182 : (((sigItems c).drop 182).take 13).all sigC = true := by decide +kernel
theorem sigCE_195 : (((sigItems c).drop 195).take 13).all sigC = true := by decide +kernel
theorem sigCE_208 : (((sigItems c).drop 208).take 13).all sigC = true := by decide +kernel
theorem sigCE_221 : (((sigItems c).drop 221).take 13).all sigC = true := by decide +kernel
theorem sigCE_234 : (((sigItems c).drop 234).take 13).all sigC = true := by decide +kernel
theorem sigCE_247 : (((sigItems c).drop 247).take 13).all sigC = true := by decide +kernel
theorem sigCE_260 : ((sigItems c).drop 260).all sigC = true := by decide +kernel

theorem sigCE : (sigItems c).all sigC = true :=
    regAllE_range (a := 0) (n := 31) sigCE_0 <|
    regAllE_range (a := 31) (n := 35) sigCE_31 <|
    regAllE_range (a := 66) (n := 35) sigCE_66 <|
    regAllE_range (a := 101) (n := 35) sigCE_101 <|
    regAllE_range (a := 136) (n := 35) sigCE_136 <|
    regAllE_range (a := 171) (n := 11) sigCE_171 <|
    regAllE_range (a := 182) (n := 13) sigCE_182 <|
    regAllE_range (a := 195) (n := 13) sigCE_195 <|
    regAllE_range (a := 208) (n := 13) sigCE_208 <|
    regAllE_range (a := 221) (n := 13) sigCE_221 <|
    regAllE_range (a := 234) (n := 13) sigCE_234 <|
    regAllE_range (a := 247) (n := 13) sigCE_247 <|
    sigCE_260

theorem sigSE_0 : (((sigItems c).drop 0).take 31).all sigS = true := by decide +kernel
theorem sigSE_31 : (((sigItems c).drop 31).take 35).all sigS = true := by decide +kernel
theorem sigSE_66 : (((sigItems c).drop 66).take 35).all sigS = true := by decide +kernel
theorem sigSE_101 : (((sigItems c).drop 101).take 35).all sigS = true := by decide +kernel
theorem sigSE_136 : (((sigItems c).drop 136).take 35).all sigS = true := by decide +kernel
theorem sigSE_171 : (((sigItems c).drop 171).take 11).all sigS = true := by decide +kernel
theorem sigSE_182 : (((sigItems c).drop 182).take 13).all sigS = true := by decide +kernel
theorem sigSE_195 : (((sigItems c).drop 195).take 13).all sigS = true := by decide +kernel
theorem sigSE_208 : (((sigItems c).drop 208).take 13).all sigS = true := by decide +kernel
theorem sigSE_221 : (((sigItems c).drop 221).take 13).all sigS = true := by decide +kernel
theorem sigSE_234 : (((sigItems c).drop 234).take 13).all sigS = true := by decide +kernel
theorem sigSE_247 : (((sigItems c).drop 247).take 13).all sigS = true := by decide +kernel
theorem sigSE_260 : ((sigItems c).drop 260).all sigS = true := by decide +kernel

theorem sigSE : (sigItems c).all sigS = true :=
    regAllE_range (a := 0) (n := 31) sigSE_0 <|
    regAllE_range (a := 31) (n := 35) sigSE_31 <|
    regAllE_range (a := 66) (n := 35) sigSE_66 <|
    regAllE_range (a := 101) (n := 35) sigSE_101 <|
    regAllE_range (a := 136) (n := 35) sigSE_136 <|
    regAllE_range (a := 171) (n := 11) sigSE_171 <|
    regAllE_range (a := 182) (n := 13) sigSE_182 <|
    regAllE_range (a := 195) (n := 13) sigSE_195 <|
    regAllE_range (a := 208) (n := 13) sigSE_208 <|
    regAllE_range (a := 221) (n := 13) sigSE_221 <|
    regAllE_range (a := 234) (n := 13) sigSE_234 <|
    regAllE_range (a := 247) (n := 13) sigSE_247 <|
    sigSE_260

/-! ## The registry family -/

theorem registry_detachedL : detachedB c ssL ksL = true := by
  simp only [detachedB, listsB, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨sortsE, hooksE⟩, collsE⟩, ⟨⟨⟨sigCE, itemsE⟩, allCollsE⟩, boolE⟩⟩, valuesE⟩, graphsE⟩

/-- **`detachedB` holds on kimp** at the registry sorts and interpreted hooked symbols the text does
not declare. -/
theorem registry_detached : detachedB c ss ks = true := by
  rw [ss_eq, ks_eq]; exact registry_detachedL

/-- The names of `ss` and `ks` are detached from `c`. -/
theorem registry_names_detached : Detached c (DetachedB.names c ss ks) :=
  detached_of_decided c ss ks coreOK registry_detached

/-- **Every surplus item of the signature is a `RegistryItem`** at the names of `ss` and `ks`: it
is a premise of the theory (an item of `sigItems c`) naming one of them. -/
theorem surplus_registry : ∀ it ∈ sigItems c, surplusItem kore it = true →
    RegistryItem c (DetachedB.names c ss ks) it.pat := by
  intro it hit hsur
  have h2 : sigS it = true := List.all_eq_true.mp sigSE it hit
  rw [sigS, hsur, Bool.not_true, Bool.or_false, ← ss_eq, ← ks_eq] at h2
  obtain ⟨σ, hσ, hn⟩ := List.any_eq_true.mp h2
  have hΓ : (Γc c ∪ Γstep c) it.pat :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨it, hit, rfl⟩)))))))))
  exact registry_names_detached.2.2 it.pat hΓ ⟨σ, hσ, isName_iff.mp hn⟩

/-! ## The registry family is conservative on kimp -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- What the statements assume of kimp's functions, from their obligations, none open. -/
theorem fnHyp : FnHyp c :=
  fnHyp_of_fnObligations coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) ParamsTotal.nil
    (FnObligations.of_nil term_named total_named agree_named match_named)

/-- **The registry family at the names kimp does not declare is conservative.** -/
theorem kimp_conservative : RegistryConservative c (DetachedB.names c ss ks) :=
  registry_conservative (hpreTop := preTop) c ss ks coreOK fnHyp registry_detached

/-- **No step of kimp at values rests on the registry family** at the names it does not declare. -/
theorem kimp_exact_own : ExactOwn c (DetachedB.names c ss ks) :=
  exact_own (hpreTop := preTop) c ss ks coreOK fnHyp registry_detached

/-! ## For every H -/

/-- What the statements assume of kimp's functions under every interpretation H: the obligations
named on the text are empty and read no interpretation (`fnHyp_decided`). -/
theorem fnHyp_everyH (H : HookParams) : FnHyp (c.withHooks H) :=
  ParamSchema.fnHyp_decided c coreOK (by decide +kernel) (by decide +kernel) preTop (by decide +kernel)
    term_named total_named agree_named match_named H

/-- **The registry family at the names kimp does not declare, for every H**: detached,
conservative and resting no step at values, at `c.withHooks H`, from the decision at `c`
(`registry_withHooks_of_decided`, `detachedB_withHooks`). -/
theorem kimp_registry_everyH (H : HookParams) :
    Detached (c.withHooks H) (DetachedB.names (c.withHooks H) ss ks) ∧
    RegistryConservative (c.withHooks H) (DetachedB.names (c.withHooks H) ss ks) ∧
    ExactOwn (c.withHooks H) (DetachedB.names (c.withHooks H) ss ks) :=
  registry_withHooks_of_decided c H ss ks coreOK preTop (fnHyp_everyH H) registry_detached

end KCore.TieKimpRegistry

#check @KCore.TieKimpRegistry.registry_detached
#check @KCore.TieKimpRegistry.registry_names_detached
#check @KCore.TieKimpRegistry.surplus_registry
#check @KCore.TieKimpRegistry.kimp_conservative
#check @KCore.TieKimpRegistry.kimp_exact_own
#check @KCore.TieKimpRegistry.kimp_registry_everyH

/-- info: 'KCore.TieKimpRegistry.registry_detached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRegistry.registry_detached
/-- info: 'KCore.TieKimpRegistry.surplus_registry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRegistry.surplus_registry
/-- info: 'KCore.TieKimpRegistry.kimp_exact_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRegistry.kimp_exact_own
/-- info: 'KCore.TieKimpRegistry.kimp_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRegistry.kimp_conservative
/-- info: 'KCore.TieKimpRegistry.kimp_registry_everyH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRegistry.kimp_registry_everyH
