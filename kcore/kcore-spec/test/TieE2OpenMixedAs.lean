/-
  The tie (C14) on `f2-examples/e2-open-mixed-as.kompile.kore`, the kompiled text of construct fixture e2-open-mixed-as
  (`test/constructs/fixtures/e2-open-mixed-as`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e2-open-mixed-as`, its rules section by hand; run from the package root:
  `lake env lean -j1 test/TieE2OpenMixedAs.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 154 sentences of the user module E2-OPEN-MIXED-AS, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the open
    generator `and` is a parameter declared without `hook` and without `function`, of which the
    text states no equation.
  - `sig_origin`: each of the 212 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`); its one open generator is `and`
    (`params_raw`), of B. It owes no fact
    about its functions (`term_named`, `total_named`, `agree_named`, `match_named`), so `Γc` with the
    step's closure has a model for every H that satisfies the open generator's laws (`facts`,
    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`); `and`
    has no law, so that is every H (`openLaws_any`, `consistent_any`).
    `lawHooks c H` is admitted by the library's sentences wherever H is (`libAdmitted_lawHooks`), so
    `lawHooks c HookParams.lib` satisfies the laws, the open generators' `functional` sentences and
    the library's sentences together (`lawHooks_lib`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (31): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (104), by hand, in the section `The rules` (`Cut`): each of Γ's rule items is a
    consequence of its text sentence, `Cut.ruleText` in `ruleItems`' order (`Cut.rule_from_text`,
    W1, every H; `Cut.rules_account`). The section's other headline statements (its comment says
    what each states): `Cut.cut_parts`, `Cut.cut_text`, `Cut.φ_sub`, `Cut.φ'_split`, `Cut.left_sub`,
    `Cut.and_inB`, `Cut.right_parts`, `Cut.right_defined`, `Cut.rule_to_text`, `Cut.rule_tie`.
  - Constructor sentences (34): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 8 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (48): Γ with it has no model (`idem_refuted`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); open generator
    functional: owed as `OpenTotal` (`open_functional_not_item`); no direction: `absent_closed`.

  `and`'s functional sentence (56) is no item of Γ and is owed at values as `OpenTotal`
  (`open_functional_not_item`); the account holds it in `open generator functional`, of the
  direction `hypothesis`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (25);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2OpenMixedAs

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-open-mixed-as.kompile.kore"
definition_of defn from "f2-examples/e2-open-mixed-as.kompile.kore"
user_axioms U from "f2-examples/e2-open-mixed-as.kompile.kore" module "E2-OPEN-MIXED-AS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `and`, the text's one open generator (`raw`), and B, its sort. -/
def and : Sym := 390
def b : Srt := 32

theorem names : c.symName and = "Lbland" ∧ c.sortName b = "B" := by decide +kernel

/-- **The definition's one open generator is `and`**, of B, `assoc` false and `idem` false. -/
theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =
    [(and, [33, 33], b, false, false)] := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-OPEN-MIXED-AS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 154 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
      128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]),
   ("rewrite rule", [104]),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 57, 60, 81, 82, 89, 91]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30, 58, 61]),
   ("distinctness", [59, 90]),
   ("no junk", [92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]),
   ("function functional", [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 39, 43, 51, 52, 53, 54, 55, 63, 80, 83, 84, 85, 86, 87]),
   ("collection law", [40, 41, 42, 44, 45, 46, 47, 49, 50]),
   ("library", [105, 156]),
   ("set idempotence", [48]),
   ("set-variable lemma", [157]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", [56]),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [37, 38, 62, 88, 106, 107, 108, 109, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151,
      152, 153, 154, 155])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 31), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 10), ("subsort", 16), ("injectivity", 6), ("distinctness", 2), ("no junk", 12), ("function functional", 16), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 1), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 23)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it
(`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-- The sentences of the no-direction class that are equations of a projection `project:X` (their
left side applies `Lblproject'Coln'X`), each with X. -/
def absentProj : List (Nat × String) :=
  [(141, "A"), (142, "B"), (143, "Bool"), (144, "GeneratedCounterCell"),
   (145, "GeneratedCounterCellOpt"), (146, "GeneratedTopCell"), (147, "GeneratedTopCellFragment"),
   (148, "Int"), (149, "K"), (150, "KCell"), (151, "KCellOpt"), (152, "KItem"), (153, "List"),
   (154, "Map"), (155, "Set")]

/-- Each sort of `absentProj` is K, KItem or a sort below KItem of Γ, with K and KItem
constructor sorts. -/
theorem absent_proj_below_c : absentProj.all (fun p => GenEqs.projBelowB c p.2) = true := by
  decide +kernel

/-- **The projections the no-direction class defines are of sorts below KItem**: `absentProj` is
the list of the no-direction sentences whose left side applies a symbol `Lblproject'Coln'X`, each
with that X, and each such X is K, KItem or a sort below KItem of Γ, with K and KItem constructor
sorts (`GenEqs.projBelowB`). So the pattern each of these equations is at is functional and
injective on X in every model of Γ (`GenEqs.projSel_fun`, `GenEqs.projSel_inj`): what the
equation states of the pattern's symbols, Γ entails. -/
theorem absent_proj_below (H : HookParams) :
    (userAxioms.filter (fun ad => (classOf "no direction").contains ad.index &&
        ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "Lblproject'Coln'")).map
      (fun ad => (ad.index, AttrsAgree.eqnHead ad.ax.pattern)) =
      absentProj.map (fun p => (p.1, some ("Lblproject'Coln'" ++ p.2))) ∧
    absentProj.all (fun p => GenEqs.projBelowB (cH H) p.2) = true :=
  ⟨by rw [userAxioms_eq]; decide +kernel, absent_proj_below_c⟩

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(10, "subsort"), (18, "subsort"), (56, "open generator functional"),
   (57, "constructor functional"), (58, "injectivity"), (59, "distinctness"),
   (60, "constructor functional"), (61, "injectivity"), (64, "function functional"),
   (65, "function functional"), (89, "constructor functional"), (90, "distinctness"),
   (91, "constructor functional"), (92, "no junk"), (93, "no junk"), (103, "no junk"),
   (104, "rewrite rule"), (109, "no direction"), (110, "function equation"),
   (111, "function equation"), (112, "function equation"), (113, "function equation"),
   (141, "no direction"), (142, "no direction"), (157, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. The open generator `and` is a parameter (`raw`) that no
registry hook interprets, declared without `hook` and without `function`, and the text states
no equation of it (`AttrsAgree.eqnsOf`), which `AttrsAgree.hooks` admits. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

/-! ## The declarations: `sig_origin` and `decls_entailed`, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFrom = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 13).all sigFrom = true := by decide +kernel
theorem sigE_47 : (((sigItems c).drop 47).take 13).all sigFrom = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFrom = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFrom = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFrom = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFrom = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFrom = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFrom = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFrom = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFrom = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFrom = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFrom = true := by decide +kernel
theorem sigE_190 : (((sigItems c).drop 190).take 13).all sigFrom = true := by decide +kernel
theorem sigE_203 : ((sigItems c).drop 203).all sigFrom = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 212 := by decide +kernel

/-- **Every item of Γ's signature has its origin**: the item of a declaration of the text, or the
sort constant of a registry sort or the arity of an interpreted hooked symbol that the text does not
declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAllE_whole (p := sigFrom) <|
    tieAllE_range (a := 0) (n := 34) sigE_0 <|
    tieAllE_range (a := 34) (n := 13) sigE_34 <|
    tieAllE_range (a := 47) (n := 13) sigE_47 <|
    tieAllE_range (a := 60) (n := 13) sigE_60 <|
    tieAllE_range (a := 73) (n := 13) sigE_73 <|
    tieAllE_range (a := 86) (n := 13) sigE_86 <|
    tieAllE_range (a := 99) (n := 13) sigE_99 <|
    tieAllE_range (a := 112) (n := 13) sigE_112 <|
    tieAllE_range (a := 125) (n := 13) sigE_125 <|
    tieAllE_range (a := 138) (n := 13) sigE_138 <|
    tieAllE_range (a := 151) (n := 13) sigE_151 <|
    tieAllE_range (a := 164) (n := 13) sigE_164 <|
    tieAllE_range (a := 177) (n := 13) sigE_177 <|
    tieAllE_range (a := 190) (n := 13) sigE_190 <|
    sigE_203

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)
noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- The declarations of the text: sorts, sorts without parameters, symbols, symbols without
parameters that Γ has, symbols with parameters, symbols without parameters that Γ lacks. -/
theorem decl_counts :
    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,
      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 92, 61, 4, 27) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 25).all inSigItems = true := by decide +kernel
theorem declsE_25 : (((declItems).drop 25).take 25).all inSigItems = true := by decide +kernel
theorem declsE_50 : (((declItems).drop 50).take 25).all inSigItems = true := by decide +kernel
theorem declsE_75 : ((declItems).drop 75).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    tieAllE_range (a := 50) (n := 25) declsE_50 <|
    declsE_75

/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of
a symbol Γ has, for every H. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-! ## Consistency for every H satisfying the open generator's laws -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- No function's fact is named: under every interpretation that satisfies the open generator's
laws, `FnFacts` holds. -/
theorem facts (H : HookParams) (hop : OpenLaws (cH H)) : FnFacts (cH H) callOrder [] :=
  FnFacts.of_nil_laws
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) hop

/-- **`Γc` with the step's closure has a model, for every H that satisfies the open generator's laws**
(`OpenLaws`). -/
theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hop)

/-- **`lawHooks c H` satisfies the laws and gives `and` a value at every pair of argument values**,
for every H; so `Γc` with the step's closure has a model there. -/
theorem lawHooks_laws (H : HookParams) :
    OpenLaws (c.withHooks (lawHooks c H)) ∧ OpenTotal (c.withHooks (lawHooks c H)) :=
  ⟨openLaws_lawHooks c coreOK H, openTotal_lawHooks c coreOK H⟩

theorem consistent_lawHooks (H : HookParams) : Consistent (c.withHooks (lawHooks c H)) :=
  consistent (lawHooks c H) (lawHooks_laws H).1

/-- **`lawHooks c H` is admitted by the library's sentences wherever H is and gives `_RangeMap_`
no value**, for every H (`KCore.libAdmitted_lawHooks`). -/
theorem libAdmitted_lawHooks (H : HookParams) (ha : (c.withHooks H).libAdmitted)
    (hrm : ∀ vs, H.app rmConcat vs = none) : (c.withHooks (lawHooks c H)).libAdmitted :=
  KCore.libAdmitted_lawHooks c coreOK H ha hrm

/-- **`lawHooks c HookParams.lib` satisfies the laws, the open generators' `functional` sentences
and the library's sentences together.** -/
theorem lawHooks_lib :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted :=
  ⟨(lawHooks_laws HookParams.lib).1, (lawHooks_laws HookParams.lib).2,
    libAdmitted_lawHooks HookParams.lib (libAdmitted_lib_of_coreOK coreOK) lib_app_rmConcat_none⟩

/-- **`and` has no law: `OpenLaws` holds under every interpretation.** -/
theorem openLaws_any (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'
  rw [params_raw, List.mem_singleton] at hm
  simp only [Prod.mk.injEq] at hm
  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent_any (H : HookParams) : Consistent (cH H) := consistent H (openLaws_any H)

/-! ## Function functional (16): the sort predicates' `functional` sentences, at values in every model of Γc -/

/- The class holds the `functional` sentences of 16 sort predicates `isX`,
`\exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val:SortBool{}, LblisX{}(K0:SortK{})))`. KCore builds
the sort predicates (`Semantics.sortPreds`): each has a value at every K, and a model of `Γc` reads
its application at a value's element as that value's element (`LibEv.sortPredFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and no condition over a
variable the patterns leave open). So each sentence holds in every model of `Γc`, and of `Γc` with
the step's closure, at every valuation sending K0 to a value, for every H, from the sort predicates'
own results and without `FnHyp`. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- **`fnFunText` is the account's function functional class**: the same indices, each once. -/
theorem fnFun_account : (classOf "function functional").isPerm (fnFunText.map (·.index)) = true := by
  decide +kernel

/-- The sentence is the `functional` sentence of a sort predicate of `c`, over the one sort
variable `R`, with its variables' sorts the registry's. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the 16 reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\top`, no clause binds a variable by `\exists`, and no clause has
a condition over a variable its patterns leave open. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => !cl.reqOpen) = true := by
  decide +kernel

theorem fnFun_noWitH (H : HookParams) : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = false := by
  intro fn hfn cl hcl
  have h := List.all_eq_true.mp (List.all_eq_true.mp fnFun_clauses.2.2 fn hfn) cl hcl
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  simp [Clause.needsWitness, h]

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), without `FnHyp`. -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany⟩ := hok
  obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
  exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2.1)
    (fun fn hfn cl hcl hw => absurd hw (by rw [fnFun_noWitH H fn hfn cl hcl]; decide)) hfn hfp.2 ad hfp.1 hsv

/-- The same in every model of `Γc` with the step's closure, the theory `Consistent` asks a model of. -/
theorem fnFun_at_values_step (H : HookParams) : ∀ ad ∈ fnFunText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H)) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => fnFun_at_values H ad had M hM I (fun φ hφ => hI φ (Or.inl hφ))

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (31 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 31 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax126, U.ax134, U.ax133, U.ax132, U.ax131, U.ax138, U.ax137, U.ax140, U.ax139, U.ax136,
   U.ax135, U.ax115, U.ax114, U.ax125, U.ax124, U.ax121, U.ax120, U.ax123, U.ax122, U.ax128,
   U.ax127, U.ax130, U.ax129, U.ax117, U.ax116, U.ax119, U.ax118, U.ax113, U.ax112, U.ax111,
   U.ax110]

set_option maxHeartbeats 1000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel
decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl
  rw [fn_shape, List.getElem?_map] at h1
  cases hf : fnText[j]? with
  | none => rw [hf] at h1; cases h1
  | some ad =>
    rw [hf] at h1
    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
    have he : (trS ad).pat = it.pat := Option.some.inj h1
    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## No junk -/

/-- `\or{S}(\top{S}(), \bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/
def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)

theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}
    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by
  intro e m
  unfold orTopBot
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sOr, interp_sTop hD hS]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

theorem nj94 : (trS U.ax94).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj99 : (trS U.ax99).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj102 : (trS U.ax102).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax94, U.ax99, U.ax102], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj94]; exact orTopBot_valid hD rfl
  · rw [nj99]; exact orTopBot_valid hD rfl
  · rw [nj102]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax92, U.ax93, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax92, U.ax93, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax103).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (103)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax103).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30,
   U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax81, U.ax82, U.ax89, U.ax90, U.ax91]

theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel

theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax48.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax48).pat = (trAxiom [] [] U.ax48).pat := by decide +kernel

/-- `0` as a KItem, and the set `SetItem(0)`. -/
def a0 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  simp only [Semantics.sortsOf, s1_sort H]
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem idem_vars : (U.ax48.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax48.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax48.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 48 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax48).pat) := by
  intro M _ I hI hax
  rw [idem_trS] at hax
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI (set_numbered H)
  rw [set_name] at hσS1
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (s1_sort H) KoreAML.val0
  rw [set_name] at hesort
  let a := elemOf (cH H) I s1
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax48.ax.sortVars U.ax48.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax48.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax48.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m
    rw [idem_vars] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσS2
    · rw [List.mem_singleton.mp hk, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hesort
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    rw [idem_sort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' a
    rw [KoreAML.interp_inhOf_of hRv]; exact ha)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar)).interpret
      I e' a := by
    have := hP; simp only [tbl] at this ⊢; rw [idem_pattern] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.set)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName Srt.set = "Set" from set_name H, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) ↔ b = a
    rw [hKv]
  have happ := (hall a ha).mpr ((hK a).mpr rfl)
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at happ
  have hden : (KoreAML.den (symApp (cH H) setConcat (GroundTerm.koreList (cH H) [s1, s1]))).interpret I KoreAML.val0 a := by
    unfold KoreAML.den
    rw [symApp_withHooks, tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp happ
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    refine KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, ?_, (hes b0).mpr ((hK b0).mp hb0), h0⟩,
      (hes b1).mpr ((hK b1).mp hb1), h1⟩
    exact (sym_congr (e := KoreAML.val0) (e' := e') _ f0).mpr hf0
  have hgraph := sat_dom hI (Or.inl ⟨_, [s1, s1], none, concat_sig, concat_args H, concat_none,
    fun _ => concat_heard, rfl⟩)
  exact ((KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a).mp hden

end Idem


/-! ## The functional sentence of `and` (56): owed as `OpenTotal` -/

/-- **Γ holds no item for `and`'s functional sentence**: the constructors' items state the
functionality of the generators that are no open generator only. The sentence is owed, at values,
as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : !(consItemsK c).any (·.pat == (trS U.ax56).pat) &&
    !(fnItems c).any (·.pat == (trS U.ax56).pat) &&
    (classOf "open generator functional" == [56]) = true := by
  decide +kernel

/-! ## Over `Γc`, the theory the statements are about -/

/-- `Γc` holds every premise of Γ. -/
theorem Γ_sub_Γc (c : Semantics) {φ : P} (h : Γ c φ) : Γc c φ := Or.inl h

/-- What Γ entails, `Γc` entails. -/
theorem entails_c {c : Semantics} {ψ : P} (h : Γ c ⊧ ψ) : Γc c ⊧ ψ :=
  fun hI => h fun φ hφ => hI φ (Γ_sub_Γc c hφ)

/-- Bool holds only its literals here, and the definition reads a confined sort: `Γcl` holds its
one item, `boolClosed`. -/
theorem gammaCl_eq (H : HookParams) (φ : P) : Γcl (cH H) φ ↔ φ = boolClosed (cH H) :=
  ⟨fun h => h.2.2, fun h => ⟨readsConfined_c, (by decide +kernel : c.litSort Srt.bool = true), h⟩⟩

theorem decls_entailed_c (H : HookParams) : ∀ it ∈ declItems, Γc (cH H) ⊧ it.pat :=
  fun it hit => entails_c (decls_entailed H it hit)
theorem fns_entailed_c (H : HookParams) : ∀ ad ∈ fnText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (fns_entailed H ad had)
theorem nojunk_trivial_entailed_c (H : HookParams) :
    ∀ ad ∈ [U.ax94, U.ax99, U.ax102], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax92, U.ax93, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax103).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 48 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax48).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

/-! ## The rules (104): W1 and W2 through the cut with the alias, for every H (by hand)

Γ's one rule is `<k> c((X #as Z) & Y) => d(Z) </k>` (sentence 104) read through the cut with the
alias a condition (`Parse.ovlCut`, `Parse.cutOvlApps`, `Parse.cutAsBinds`): its left side holds
the variable `Open0` (`V`, of B) in the place of `and(X ∧ Z, Y)` (`φ'`, `X #as Z` being
`\and{A}(X, Z)`), and its `pre` is `Open0 ∈ and(Z, Y) ∧ Z ∈ X` (`φ := and(Z, Y)`). Γ's axiom of the
rule is `\rewrites(K[V] ∧ ⊤ ∧ (V ∈ φ ∧ Z ∈ X) ∧ ⌈r⌉, r)` (`cut_parts`), and sentence 104 is the
item of `\rewrites(K[φ'] ∧ ⊤, r)` at the table of Γ's axiom, its variables renamed (`cut_text`).

`X ∧ Z` denotes Z's element where it is X's and nothing elsewhere, and an application is pointwise
and empty at an empty argument, so at a valuation where Z ∈ X holds `φ` and `φ'` have the same
elements (`φ_sub`), and an element of `φ'` is one where Z ∈ X holds (`φ'_split`). `K[φ']` is the
union of `K[b]` over the elements b of `φ'` (`KoreAML.cut_sem`). So:
- the sentence gives Γ's item (`rule_from_text`, W1, every H): an element of Γ's left side is one
  of `K[V]` with V's value in `φ` where Z ∈ X holds, so one of `K[φ']` (`TieRuleLhs.rule_w1`, the
  context monotone as in `TieRuleCut.cutLeft_sub`);
- Γ's item gives the sentence in a model of Γ (`rule_to_text`, W2, every H; both as one statement,
  `rule_tie`): an element of the text's left side is one of `K[V] ∧ ⊤ ∧ (V ∈ φ ∧ Z ∈ X)` at V an
  element b of `φ'`, which is in B by `and`'s arity item A A → B (`and_inB`), and `⌈r⌉` holds of it
  (`RightDefined`, `right_defined`: the right side `<generatedTop>(<k>(kseq(d(Z), dotk)), C) ∧ ⊤`
  is built of the text's variables and of constructors whose Cons-Fun items Γ has,
  `TieRuleCut.rightDefined_of_Γ`); Γ's item at V := b gives the step (`TieRuleCut.item_w2`, the
  split as in `TieRuleCut.cutLeft_split`).
`TieRuleCut.openCut_tie` does not apply as stated: the membership is one conjunct with the alias's,
and the text's application holds `X ∧ Z` where the membership holds Z. The statements are over the
models of Γ; `Γc` holds every premise of Γ, so they hold in every model of `Γc` too. -/

namespace Cut

/-- The rule `<k> c((X #as Z) & Y) => d(Z) </k>` read through the cut. -/
noncomputable def rCut : Rule := c.rules[0]'(by decide +kernel)

theorem rules_len : c.rules.length = 1 := by decide +kernel

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax104]

theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

/-- Γ's axiom of the cut rule. -/
noncomputable def pCut : Kore.Pattern := prioRuleK c rCut

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], pCut, []⟩⟩] := by kernel_rfl

/-- The parts `\rewrites{C}(L', r)` of the cut rule's axiom. -/
noncomputable def qCut : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts pCut).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

/-- The context of its left side's term around the argument of `c`. -/
noncomputable def K : KoreCutCtx :=
  ((TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead qCut.2.1)).getD (.hole, .top KoreAML.R)).1

/-- The variable of the cut, `Open0` (the rule's fifth variable), of B. -/
def V : Kore.EVar := ⟨⟨⟨"VarV4"⟩⟩, KoreAML.srt "B"⟩
/-- X, Z and Y, the rule's first three variables, of A. -/
def X : Kore.EVar := ⟨⟨⟨"VarV0"⟩⟩, KoreAML.srt "A"⟩
def Z : Kore.EVar := ⟨⟨⟨"VarV1"⟩⟩, KoreAML.srt "A"⟩
def Y : Kore.EVar := ⟨⟨⟨"VarV2"⟩⟩, KoreAML.srt "A"⟩

/-- The application of the membership, `and(Z, Y)`. -/
def φ : Kore.Pattern := .app ⟨⟨"Lbland"⟩⟩ [] [.var (.evar Z), .var (.evar Y)]
/-- `X #as Z`, `\and{A}(X, Z)`. -/
def XZ : Kore.Pattern := .and (KoreAML.srt "A") [.var (.evar X), .var (.evar Z)]
/-- The application the text writes, `and(X #as Z, Y)`. -/
def φ' : Kore.Pattern := .app ⟨⟨"Lbland"⟩⟩ [] [XZ, .var (.evar Y)]

/-- The two memberships of `pre`: `V ∈ φ` and the alias's `Z ∈ X`. -/
noncomputable def inV : Kore.Pattern := .in V.sort qCut.1 (.var (.evar V)) φ
noncomputable def inZ : Kore.Pattern := .in Z.sort qCut.1 (.var (.evar Z)) (.var (.evar X))
/-- `⌈r⌉`, the conjunct Γ's left side holds after `pre`. -/
noncomputable def ceilR : Kore.Pattern := .ceil qCut.1 qCut.1 qCut.2.2

/-- Γ's left side. -/
noncomputable def Lg : Kore.Pattern :=
  .and qCut.1 [K.fill (.var (.evar V)), .top qCut.1, .and qCut.1 [inV, inZ], ceilR]

/-- **Γ's axiom of the cut rule is `\rewrites(K[V] ∧ ⊤ ∧ (V ∈ φ ∧ Z ∈ X) ∧ ⌈r⌉, r)`** (kernel). -/
theorem cut_parts : TieRuleLhs.rwParts pCut = some (qCut.1, Lg, qCut.2.2) := by decide +kernel

/-- The left side as the text writes it: `and(X #as Z, Y)` in the place of the variable, and no
conjunct after `\top`. -/
noncomputable def Ltext : Kore.Pattern := .and qCut.1 (K.fill φ' :: [.top qCut.1])

/-- The free variables of the text's form: X, Z, Y and the counter cell's. -/
noncomputable def fT : List VarKey := (freeOf [] (.rewrites qCut.1 Ltext qCut.2.2)).eraseDups

/-- **Sentence 104 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**, its four
variables renamed (kernel): in Γ's table the variable of the cut is the first, the counter cell's
the second, then Z, Y and X as `pre` holds them. -/
theorem cut_text : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pCut) fT qCut.1 Ltext qCut.2.2)
    [(5, 1), (4, 5), (2, 4), (3, 2), (5, 3)] = some (trS U.ax104).pat := by decide +kernel
theorem fT_free : fT.all (fun k => (freeOf [] pCut).eraseDups.contains k) = true := by decide +kernel
theorem fG_split : (freeOf [] pCut).eraseDups.all (fun k => fT.contains k || k == evarKey V) = true := by
  decide +kernel
theorem K_noAlias : K.noAlias ⟨tableOf [] pCut, []⟩ = true := by decide +kernel
/-- The variable of the cut is free in nothing of the two items but its occurrence and its
membership `V ∈ φ` (kernel). -/
theorem cut_fresh : TieRuleCut.cutFreshB (tableOf [] pCut) fT qCut.1 K V φ qCut.2.2 [.top qCut.1] [inZ, ceilR] = true := by
  decide +kernel

theorem X_idx : (tableOf [] pCut).ev (evarKey X) = ⟨5⟩ := by decide +kernel
theorem Z_idx : (tableOf [] pCut).ev (evarKey Z) = ⟨3⟩ := by decide +kernel
theorem Y_idx : (tableOf [] pCut).ev (evarKey Y) = ⟨4⟩ := by decide +kernel
theorem tr_φ : tr ⟨tableOf [] pCut, []⟩ φ = (sym (.symbol "Lbland") ⬝ .evar ⟨3⟩) ⬝ .evar ⟨4⟩ := by decide +kernel
theorem tr_φ' : tr ⟨tableOf [] pCut, []⟩ φ' =
    (sym (.symbol "Lbland") ⬝ tr ⟨tableOf [] pCut, []⟩ XZ) ⬝ .evar ⟨4⟩ := by decide +kernel
theorem tr_inV : tr ⟨tableOf [] pCut, []⟩ inV = sIn (trSort (tableOf [] pCut) V.sort) (trSort (tableOf [] pCut) qCut.1)
    (.evar ((tableOf [] pCut).ev (evarKey V))) (tr ⟨tableOf [] pCut, []⟩ φ) := by simp only [inV, tr]
theorem tr_inZ : tr ⟨tableOf [] pCut, []⟩ inZ = sIn (trSort (tableOf [] pCut) Z.sort) (trSort (tableOf [] pCut) qCut.1)
    (.evar ⟨3⟩) (.evar ⟨5⟩) := by decide +kernel

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- `X ∧ Z` holds w exactly where w is the value of both. -/
theorem XZ_iff (e : Valuation M) (w : M) :
    (tr ⟨tableOf [] pCut, []⟩ XZ).interpret I e w ↔ w = e.evalEvar ⟨5⟩ ∧ w = e.evalEvar ⟨3⟩ := by
  unfold XZ
  rw [interp_and (List.cons_ne_nil _ _)]
  constructor
  · intro h
    have h1 := h _ List.mem_cons_self
    have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [TieRuleCut.tr_evarCut, X_idx, interp_evar] at h1
    rw [TieRuleCut.tr_evarCut, Z_idx, interp_evar] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [TieRuleCut.tr_evarCut, X_idx, interp_evar]; exact h1
    · rw [List.mem_singleton.mp hp, TieRuleCut.tr_evarCut, Z_idx, interp_evar]; exact h2

/-- **Where Z and X have one value, every element of `and(Z, Y)` is one of `and(X ∧ Z, Y)`.** -/
theorem φ_sub (e : Valuation M) (hZX : e.evalEvar ⟨3⟩ = e.evalEvar ⟨5⟩) (w : M)
    (hw : (tr ⟨tableOf [] pCut, []⟩ φ).interpret I e w) : (tr ⟨tableOf [] pCut, []⟩ φ').interpret I e w := by
  rw [tr_φ] at hw
  rw [tr_φ']
  obtain ⟨f1, y, hf1, hy, h2⟩ := interp_app.mp hw
  obtain ⟨f0, z, hf0, hz, h1⟩ := interp_app.mp hf1
  rw [interp_evar] at hz
  exact interp_app.mpr ⟨f1, y, interp_app.mpr ⟨f0, z, hf0, (XZ_iff e z).mpr ⟨hz.trans hZX, hz⟩, h1⟩, hy, h2⟩

/-- **An element of `and(X ∧ Z, Y)` is one where Z and X have one value, and one of
`and(Z, Y)`.** -/
theorem φ'_split (e : Valuation M) (w : M) (hw : (tr ⟨tableOf [] pCut, []⟩ φ').interpret I e w) :
    e.evalEvar ⟨3⟩ = e.evalEvar ⟨5⟩ ∧ (tr ⟨tableOf [] pCut, []⟩ φ).interpret I e w := by
  rw [tr_φ'] at hw
  rw [tr_φ]
  obtain ⟨f1, y, hf1, hy, h2⟩ := interp_app.mp hw
  obtain ⟨f0, z, hf0, hz, h1⟩ := interp_app.mp hf1
  obtain ⟨hzX, hzZ⟩ := (XZ_iff e z).mp hz
  exact ⟨hzZ.symm.trans hzX, interp_app.mpr ⟨f1, y, interp_app.mpr ⟨f0, z, hf0, (interp_evar).mpr hzZ, h1⟩, hy, h2⟩⟩

/-- **Γ's left side is in the text's**: at one valuation, an element of
`K[V] ∧ ⊤ ∧ (V ∈ φ ∧ Z ∈ X) ∧ ⌈r⌉` is one of `K[φ'] ∧ ⊤`. -/
theorem left_sub (e : Valuation M) (w : M) (h : (tr ⟨tableOf [] pCut, []⟩ Lg).interpret I e w) :
    (tr ⟨tableOf [] pCut, []⟩ Ltext).interpret I e w := by
  unfold Lg at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  have hm := h (.and qCut.1 [inV, inZ]) (by simp)
  rw [interp_and (List.cons_ne_nil _ _)] at hm
  have hin := hm inV List.mem_cons_self
  have hiz := hm inZ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [tr_inV] at hin
  rw [tr_inZ] at hiz
  unfold sIn at hin hiz
  obtain ⟨_, _, v, -, -, hv, -⟩ := interp_sCeil_raw.mp hin
  obtain ⟨_, _, z, -, -, hz, -⟩ := interp_sCeil_raw.mp hiz
  rw [interp_sAnd, interp_evar] at hv
  rw [interp_sAnd, interp_evar, interp_evar] at hz
  have hZX : e.evalEvar ⟨3⟩ = e.evalEvar ⟨5⟩ := hz.1.symm.trans hz.2
  have hsub : ∀ a', (tr ⟨tableOf [] pCut, []⟩ (.var (.evar V))).interpret I e a' →
      (tr ⟨tableOf [] pCut, []⟩ φ').interpret I e a' := by
    intro a' ha'
    rw [TieRuleCut.tr_evarCut, interp_evar] at ha'
    rw [ha', ← hv.1]
    exact φ_sub e hZX v hv.2
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact TieRuleLhs.tr_fill_mono _ K K_noAlias hsub w (h _ List.mem_cons_self)
  · rw [List.mem_singleton.mp hp]; exact h _ (by simp)

end

/-- **W1 for the rule**: Γ's rule item is a consequence of its sentence, for every H
(`TieRuleLhs.rule_w1`, `left_sub`). -/
theorem rule_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hj
  match j, hj with
  | 0, hj =>
    cases hj
    exact ⟨U.ax104, rfl, fun {M} _ {I} hI =>
      TieRuleLhs.rule_w1 (TiePair.defOK_texts hI) cut_parts cut_text fT_free
        (hI _ (Or.inl (List.mem_singleton_self _))) fun e _ _ w hw => left_sub e w hw⟩
  | j + 1, hj => simp at hj

def sortA : Srt := 33
def topSrt : Srt := 17
theorem sorts_named : c.sortName sortA = "A" ∧ c.sortName topSrt = "GeneratedTopCell" := by decide +kernel
theorem b_numbered (H : HookParams) : b < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : b < nRegSorts + c.sortNames.length)
theorem a_numbered (H : HookParams) : sortA < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : sortA < nRegSorts + c.sortNames.length)
theorem top_numbered (H : HookParams) : topSrt < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topSrt < nRegSorts + c.sortNames.length)

/-- `and`'s arity item: applied to elements of A it gives elements of B only. -/
def andArity : P :=
  ((sym (.symbol "Lbland") ⬝ inhOf (sym (.sort "SortA"))) ⬝ inhOf (sym (.sort "SortA"))) ⊆⊆ inhOf (sym (.sort "SortB"))

theorem andArity_sig : (sigItems c).any (fun it => decide (it.pat = andArity)) = true := by decide +kernel

theorem Z_free : evarKey Z ∈ fT := by decide +kernel
theorem Y_free : evarKey Y ∈ fT := by decide +kernel
theorem sortA_tr : trSort (tableOf [] pCut) (KoreAML.srt "A") = sym (.sort "SortA") := by decide +kernel
theorem sortB_tr : trSort (tableOf [] pCut) (KoreAML.srt "B") = sym (.sort "SortB") := by decide +kernel
theorem sortTop_tr : trSort (tableOf [] pCut) qCut.1 = sym (.sort "SortGeneratedTopCell") := by decide +kernel

/-- **Every element of `and(Z, Y)` is in B**, where Z and Y are in A (`and`'s arity item, of the
signature). -/
theorem and_inB (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] pCut) k).interpret I e m) (w : M)
    (hw : (tr ⟨tableOf [] pCut, []⟩ φ).interpret I e w) : (inhOf (sym (.sort "SortB")) : P).interpret I e w := by
  obtain ⟨it, hit, hpat⟩ := List.any_eq_true.mp andArity_sig
  have har : I ⊧ᴵ andArity := by
    rw [← of_decide_eq_true hpat]
    exact hSig _ (Or.inl (Or.inl ⟨it, by rw [sigItems_withHooks]; exact hit, rfl⟩))
  have hgZ := (TieRuleLhs.guard_evarKey hD).mp (hg _ Z_free)
  have hgY := (TieRuleLhs.guard_evarKey hD).mp (hg _ Y_free)
  rw [show Z.sort = KoreAML.srt "A" from rfl, sortA_tr, Z_idx] at hgZ
  rw [show Y.sort = KoreAML.srt "A" from rfl, sortA_tr, Y_idx] at hgY
  rw [tr_φ] at hw
  obtain ⟨f1, y, hf1, hy, h2⟩ := interp_app.mp hw
  obtain ⟨f0, z, hf0, hz, h1⟩ := interp_app.mp hf1
  rw [interp_evar] at hz hy
  unfold andArity at har
  refine (interp_included hD).mp (har e default) w (interp_app.mpr ⟨f1, y, interp_app.mpr ⟨f0, z, hf0, ?_, h1⟩, ?_, h2⟩)
  · rw [hz]; exact hgZ
  · rw [hy]; exact hgY

/-- The premise of W2: `⌈r⌉`, the definedness of the right side (the conjunct Γ's item of every
rule adds to the text's left side), holds of every element of the text's left side, where the
guards of the text's variables hold. -/
def RightDefined {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] pCut) k).interpret I e m) →
    ∀ w, (tr ⟨tableOf [] pCut, []⟩ Ltext).interpret I e w → (tr ⟨tableOf [] pCut, []⟩ ceilR).interpret I e w

/-- The term of the right side, `<generatedTop>(<k>(kseq(d(Z), dotk)), C)`. -/
noncomputable def rr : Kore.Pattern :=
  match qCut.2.2 with
  | .and _ (p :: _) => p
  | p => p

/-- **The right side is `rr ∧ ⊤`**, of the sort of the top cell (kernel). -/
theorem right_parts : qCut.1 = srtOf c topSrt ∧ qCut.2.2 = .and (srtOf c topSrt) [rr, .top (srtOf c topSrt)] := by
  decide +kernel

/-- The constructors of the right side, each with the name of its sort. -/
def rightCtors : List (String × KoreAML.CtorSig) :=
  [("GeneratedTopCell", ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("K", ⟨"dotk", [], "K"⟩),
   ("KItem", ⟨"Lbld", ["A"], "KItem"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCut.funsInB c rightCtors = true := by decide +kernel

/-- The right side's term is built of the text's variables and of those constructors, at arguments
of their sorts (kernel). -/
theorem right_built : TieRuleCut.builtB rightCtors fT rr "GeneratedTopCell" = true := by decide +kernel

/-- **The premise of W2 holds in every model of Γ**, for every H: the right side holds one
element where the guards of the text's variables hold, by the Cons-Fun items of its constructors. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : RightDefined I := by
  intro e m hg w hw
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hb : TieRuleCut.builtB rightCtors fT rr ((cH H).sortName topSrt) = true := by
    rw [show (cH H).sortName topSrt = "GeneratedTopCell" from sorts_named.2]; exact right_built
  have hwT : (inhOf (trSort (tableOf [] pCut) (srtOf (cH H) topSrt))).interpret I e w := by
    have h1 := (interp_and (List.cons_ne_nil _ _)).mp hw (.top qCut.1) (List.mem_cons_of_mem _ List.mem_cons_self)
    have h2 : tr ⟨tableOf [] pCut, []⟩ (.top qCut.1) = sTop (trSort (tableOf [] pCut) qCut.1) := by rw [tr]
    rw [h2, interp_sTop hD (by rw [sortTop_tr]; rfl)] at h1
    rw [right_parts.1] at h1
    exact h1
  have h := TieRuleCut.rightDefined_of_Γ hI (top_numbered H)
    ((TieRuleCut.funsInB_withHooks c H rightCtors).trans right_funs) hb e m hg w hwT
  unfold ceilR
  rw [right_parts.1, right_parts.2]
  exact h

/-- **W2 for the rule**: Γ's rule item gives sentence 104 in a model of Γ, for every H: an element
of the text's left side is one of Γ's at V an element of `and(X ∧ Z, Y)` (`φ'_split`,
`TieRuleCut.item_w2`). -/
theorem rule_to_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    ∀ it ∈ ruleItems (cH H), (I ⊧ᴵ it.pat) → (I ⊧ᴵ (trS U.ax104).pat) := by
  intro it hit hg
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rw [List.mem_singleton.mp hit] at hg
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hdef := right_defined H hI
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (b_numbered H)
  obtain ⟨σA, hσA1, hσA2⟩ := TieRhs.sortSing_sig hD hSig (a_numbered H)
  obtain ⟨σT, hσT1, hσT2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered H)
  rw [show (cH H).sortName b = "B" from names.2] at hσB1
  rw [show (cH H).sortName sortA = "A" from sorts_named.1] at hσA1
  rw [show (cH H).sortName topSrt = "GeneratedTopCell" from sorts_named.2] at hσT1
  have hB : ∀ (e : Valuation M) w, (trSort (tableOf [] pCut) V.sort).interpret I e w ↔ w = σB := fun e w => by
    rw [show V.sort = KoreAML.srt "B" from rfl, sortB_tr]; exact hσB1 w
  have hA : ∀ (e : Valuation M) w, (trSort (tableOf [] pCut) Z.sort).interpret I e w ↔ w = σA := fun e w => by
    rw [show Z.sort = KoreAML.srt "A" from rfl, sortA_tr]; exact hσA1 w
  have hT : ∀ (e : Valuation M) w, (trSort (tableOf [] pCut) qCut.1).interpret I e w ↔ w = σT := fun e w => by
    rw [sortTop_tr]; exact hσT1 w
  refine (TiePair.renSeq_iff cut_text).mpr ?_
  have h2 := TieRuleLhs.trAxiom_rule qCut.1 Lg qCut.2.2
  rw [← TieRuleLhs.rwParts_eq cut_parts] at h2
  rw [h2] at hg
  have hfresh := cut_fresh
  simp only [TieRuleCut.cutFreshB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hfresh
  obtain ⟨⟨⟨⟨⟨⟨hKx, hφx⟩, hrx⟩, hCx⟩, hrn⟩, hgx⟩, hCt⟩ := hfresh
  have hZx := hrx inZ (by simp)
  have hRx := hrx ceilR (by simp)
  have hTx := hrx (.top qCut.1) (by simp)
  intro e m
  refine TieRuleCut.item_w2 hD hg hCx hrn e m fun hgT w hw => ?_
  have hw' := (interp_and (List.cons_ne_nil _ _)).mp hw
  have hKφ := hw' _ List.mem_cons_self
  have htop := hw' (.top qCut.1) (List.mem_cons_of_mem _ List.mem_cons_self)
  have haC : Inh I σT w := by
    have h1 := htop
    simp only [tr] at h1
    rw [interp_sTop hD hCt, interp_inhOf_of (hT e)] at h1
    exact h1
  rw [tr_cutCtx _ _ K K_noAlias] at hKφ
  obtain ⟨v, hv, hKv⟩ := (cut_sem ((tableOf [] pCut).ev (evarKey V)) (tr ⟨tableOf [] pCut, []⟩ φ')
    (K.toCut ⟨tableOf [] pCut, []⟩) (KoreCutCtx.toCut_fresh K (TieRuleCut.sidesFresh_noRead K hKx)) e w).mp hKφ
  obtain ⟨hZX, hvφ⟩ := φ'_split e v hv
  have hvB : Inh I σB v := by
    have h1 := and_inB H hD hSig e m hgT v hvφ
    rw [← sortB_tr, show KoreAML.srt "B" = V.sort from rfl] at h1
    exact (interp_inhOf_of (hB e)).mp h1
  refine ⟨v, fun k hk => ?_, ?_⟩
  · rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp fG_split k hk) with hk' | hk'
    · have hkT := List.contains_iff_mem.mp hk'
      exact (TieRuleCut.notFree_cut (hgx k hkT) e v m).mpr (hgT k hkT)
    · rw [beq_iff_eq.mp hk', TieRuleLhs.guard_evarKey hD, interp_inhOf_of (hB _)]
      have hval : (⟨Function.update e.evalEvar ((tableOf [] pCut).ev (evarKey V)) v, e.evalSvar⟩ :
          Valuation M).evalEvar ((tableOf [] pCut).ev (evarKey V)) = v := by simp
      rw [hval]; exact hvB
  · unfold Lg
    rw [interp_and (List.cons_ne_nil _ _)]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [tr_cutCtx _ _ K K_noAlias, TieRuleCut.tr_evarCut]; exact hKv
    · exact (TieRuleCut.notFree_cut hTx e v w).mpr htop
    · rw [interp_and (List.cons_ne_nil _ _)]
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · rw [tr_inV]
        have hval : (⟨Function.update e.evalEvar ((tableOf [] pCut).ev (evarKey V)) v, e.evalSvar⟩ :
            Valuation M).evalEvar ((tableOf [] pCut).ev (evarKey V)) = v := by simp
        rw [interp_sIn hD hc (hB _) (hT _) hσB2 hσT2 (fun a' ha' => by
          rw [interp_evar, hval] at ha'
          rw [ha']; exact hvB) w]
        refine ⟨⟨v, ?_, (TieRuleCut.notFree_cut hφx e v v).mpr hvφ⟩, haC⟩
        rw [interp_evar, hval]
      · refine (TieRuleCut.notFree_cut hZx e v w).mpr ?_
        rw [tr_inZ]
        have hgZ := (TieRuleLhs.guard_evarKey hD).mp (hgT _ Z_free)
        rw [Z_idx] at hgZ
        exact (interp_sIn_evar_svin hD hc (hA e) (hT e) hσA2 hσT2 ((interp_inhOf_of (hA e)).mp hgZ) w).mpr
          ⟨hZX, haC⟩
    · exact (TieRuleCut.notFree_cut hRx e v w).mpr (hdef e m hgT w hw)

/-- **The tie of the rule's sentence**: in a model of Γ, sentence 104 and Γ's rule item hold
together, for every H. -/
theorem rule_tie (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    (I ⊧ᴵ (trS U.ax104).pat) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], pCut, []⟩⟩).pat) := by
  refine ⟨fun h => TieRuleLhs.rule_w1 (defOK hI) cut_parts cut_text fT_free h fun e _ _ w hw => left_sub e w hw,
    fun h => rule_to_text H hI _ ?_ h⟩
  rw [TiePair.ruleItems_withHooks, ruleItems_eq]
  exact List.mem_singleton_self _

end Cut

end KCore.TieE2OpenMixedAs

#check @KCore.TieE2OpenMixedAs.params_raw
#check @KCore.TieE2OpenMixedAs.readsConfined_c
#check @KCore.TieE2OpenMixedAs.userAxioms_eq
#check @KCore.TieE2OpenMixedAs.coreOK
#check @KCore.TieE2OpenMixedAs.wf_defn
#check @KCore.TieE2OpenMixedAs.account
#check @KCore.TieE2OpenMixedAs.account_sizes
#check @KCore.TieE2OpenMixedAs.account_classes
#check @KCore.TieE2OpenMixedAs.account_absent
#check @KCore.TieE2OpenMixedAs.absent_closed
#check @KCore.TieE2OpenMixedAs.absent_proj_below_c
#check @KCore.TieE2OpenMixedAs.absent_proj_below
#check @KCore.TieE2OpenMixedAs.lists_in_account
#check @KCore.TieE2OpenMixedAs.attrs_agree
#check @KCore.TieE2OpenMixedAs.sig_origin
#check @KCore.TieE2OpenMixedAs.decls_entailed
#check @KCore.TieE2OpenMixedAs.consistent
#check @KCore.TieE2OpenMixedAs.fnFun_indices
#check @KCore.TieE2OpenMixedAs.fnFun_account
#check @KCore.TieE2OpenMixedAs.fnFun_checked
#check @KCore.TieE2OpenMixedAs.fnFun_trS
#check @KCore.TieE2OpenMixedAs.fnFun_at_values
#check @KCore.TieE2OpenMixedAs.fnFun_at_values_step
#check @KCore.TieE2OpenMixedAs.fn_shape
#check @KCore.TieE2OpenMixedAs.fns_account
#check @KCore.TieE2OpenMixedAs.fns_entailed
#check @KCore.TieE2OpenMixedAs.fns_from_text
#check @KCore.TieE2OpenMixedAs.fn_prios
#check @KCore.TieE2OpenMixedAs.nojunk_trivial_entailed
#check @KCore.TieE2OpenMixedAs.nojunk_items_entailed
#check @KCore.TieE2OpenMixedAs.nojunk_kitem_entailed
#check @KCore.TieE2OpenMixedAs.cons_entailed
#check @KCore.TieE2OpenMixedAs.idem_refuted
#check @KCore.TieE2OpenMixedAs.names
#check @KCore.TieE2OpenMixedAs.facts
#check @KCore.TieE2OpenMixedAs.lawHooks_laws
#check @KCore.TieE2OpenMixedAs.consistent_lawHooks
#check @KCore.TieE2OpenMixedAs.libAdmitted_lawHooks
#check @KCore.TieE2OpenMixedAs.lawHooks_lib
#check @KCore.TieE2OpenMixedAs.openLaws_any
#check @KCore.TieE2OpenMixedAs.consistent_any
#check @KCore.TieE2OpenMixedAs.open_functional_not_item
#check @KCore.TieE2OpenMixedAs.gammaCl_eq
#check @KCore.TieE2OpenMixedAs.decls_entailed_c
#check @KCore.TieE2OpenMixedAs.fns_entailed_c
#check @KCore.TieE2OpenMixedAs.nojunk_trivial_entailed_c
#check @KCore.TieE2OpenMixedAs.nojunk_items_entailed_c
#check @KCore.TieE2OpenMixedAs.nojunk_kitem_entailed_c
#check @KCore.TieE2OpenMixedAs.cons_entailed_c
#check @KCore.TieE2OpenMixedAs.idem_refuted_c
#check @KCore.TieE2OpenMixedAs.Cut.rules_account
#check @KCore.TieE2OpenMixedAs.Cut.rule_from_text
#check @KCore.TieE2OpenMixedAs.Cut.cut_parts
#check @KCore.TieE2OpenMixedAs.Cut.cut_text
#check @KCore.TieE2OpenMixedAs.Cut.φ_sub
#check @KCore.TieE2OpenMixedAs.Cut.φ'_split
#check @KCore.TieE2OpenMixedAs.Cut.left_sub
#check @KCore.TieE2OpenMixedAs.Cut.and_inB
#check @KCore.TieE2OpenMixedAs.Cut.right_parts
#check @KCore.TieE2OpenMixedAs.Cut.right_defined
#check @KCore.TieE2OpenMixedAs.Cut.rule_to_text
#check @KCore.TieE2OpenMixedAs.Cut.rule_tie
#print axioms KCore.TieE2OpenMixedAs.params_raw
#print axioms KCore.TieE2OpenMixedAs.readsConfined_c
#print axioms KCore.TieE2OpenMixedAs.userAxioms_eq
#print axioms KCore.TieE2OpenMixedAs.coreOK
#print axioms KCore.TieE2OpenMixedAs.wf_defn
#print axioms KCore.TieE2OpenMixedAs.account
#print axioms KCore.TieE2OpenMixedAs.account_sizes
#print axioms KCore.TieE2OpenMixedAs.account_classes
#print axioms KCore.TieE2OpenMixedAs.account_absent
#print axioms KCore.TieE2OpenMixedAs.absent_closed
#print axioms KCore.TieE2OpenMixedAs.absent_proj_below_c
#print axioms KCore.TieE2OpenMixedAs.absent_proj_below
#print axioms KCore.TieE2OpenMixedAs.lists_in_account
#print axioms KCore.TieE2OpenMixedAs.attrs_agree
#print axioms KCore.TieE2OpenMixedAs.sig_origin
#print axioms KCore.TieE2OpenMixedAs.decls_entailed
#print axioms KCore.TieE2OpenMixedAs.consistent
#print axioms KCore.TieE2OpenMixedAs.fnFun_indices
#print axioms KCore.TieE2OpenMixedAs.fnFun_account
#print axioms KCore.TieE2OpenMixedAs.fnFun_checked
#print axioms KCore.TieE2OpenMixedAs.fnFun_trS
#print axioms KCore.TieE2OpenMixedAs.fnFun_at_values
#print axioms KCore.TieE2OpenMixedAs.fnFun_at_values_step
#print axioms KCore.TieE2OpenMixedAs.fn_shape
#print axioms KCore.TieE2OpenMixedAs.fns_account
#print axioms KCore.TieE2OpenMixedAs.fns_entailed
#print axioms KCore.TieE2OpenMixedAs.fns_from_text
#print axioms KCore.TieE2OpenMixedAs.fn_prios
#print axioms KCore.TieE2OpenMixedAs.nojunk_trivial_entailed
#print axioms KCore.TieE2OpenMixedAs.nojunk_items_entailed
#print axioms KCore.TieE2OpenMixedAs.nojunk_kitem_entailed
#print axioms KCore.TieE2OpenMixedAs.cons_entailed
#print axioms KCore.TieE2OpenMixedAs.idem_refuted
#print axioms KCore.TieE2OpenMixedAs.names
#print axioms KCore.TieE2OpenMixedAs.facts
#print axioms KCore.TieE2OpenMixedAs.lawHooks_laws
#print axioms KCore.TieE2OpenMixedAs.consistent_lawHooks
#print axioms KCore.TieE2OpenMixedAs.libAdmitted_lawHooks
#print axioms KCore.TieE2OpenMixedAs.lawHooks_lib
#print axioms KCore.TieE2OpenMixedAs.openLaws_any
#print axioms KCore.TieE2OpenMixedAs.consistent_any
#print axioms KCore.TieE2OpenMixedAs.open_functional_not_item
#print axioms KCore.TieE2OpenMixedAs.gammaCl_eq
#print axioms KCore.TieE2OpenMixedAs.decls_entailed_c
#print axioms KCore.TieE2OpenMixedAs.fns_entailed_c
#print axioms KCore.TieE2OpenMixedAs.nojunk_trivial_entailed_c
#print axioms KCore.TieE2OpenMixedAs.nojunk_items_entailed_c
#print axioms KCore.TieE2OpenMixedAs.nojunk_kitem_entailed_c
#print axioms KCore.TieE2OpenMixedAs.cons_entailed_c
#print axioms KCore.TieE2OpenMixedAs.idem_refuted_c
#print axioms KCore.TieE2OpenMixedAs.Cut.rules_account
#print axioms KCore.TieE2OpenMixedAs.Cut.rule_from_text
#print axioms KCore.TieE2OpenMixedAs.Cut.cut_parts
#print axioms KCore.TieE2OpenMixedAs.Cut.cut_text
#print axioms KCore.TieE2OpenMixedAs.Cut.φ_sub
#print axioms KCore.TieE2OpenMixedAs.Cut.φ'_split
#print axioms KCore.TieE2OpenMixedAs.Cut.left_sub
#print axioms KCore.TieE2OpenMixedAs.Cut.and_inB
#print axioms KCore.TieE2OpenMixedAs.Cut.right_parts
#print axioms KCore.TieE2OpenMixedAs.Cut.right_defined
#print axioms KCore.TieE2OpenMixedAs.Cut.rule_to_text
#print axioms KCore.TieE2OpenMixedAs.Cut.rule_tie
