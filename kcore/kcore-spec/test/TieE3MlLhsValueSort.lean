/-
  The tie (C14) on `f2-examples/e3-ml-lhs-value-sort.kompile.kore`, the kompiled text of construct fixture e3-ml-lhs-value-sort
  (`test/constructs/fixtures/e3-ml-lhs-value-sort`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-lhs-value-sort`, its rules section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlLhsValueSort.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 298 sentences of the user module E3-ML-LHS-VALUE-SORT, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 215 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (31): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (186, 187, 188), by hand, in the section `The rules` (`Rules`): each of Γ's rule
    items is a consequence of its text sentence with the items of the text's signature `nonemptyItem
    ⟨"SortVal", [], false⟩`, `nonemptyItem ⟨"SortInt", [], true⟩` (`Rules.ruleSigAux`; each an item
    of `(Theory.ofDefinition kore).signature`, `Rules.ruleSigAux_text`) and the text's signature
    (`ΓSig`), `Rules.ruleText` in `ruleItems`' order (`Rules.rule_from_text_aux`, W1, every H;
    `Rules.rules_account`). `ΓSig` holds the items of the text's declarations or surplus ones, the
    sort constant of a registry sort or the arity of a hooked symbol that the text does not declare
    at that shape (`sig_origin`), and the arity of every literal (`dvArityAll`). Two limits, argued
    and not proved: that a surplus item of a name the text declares with sort parameters adds no
    consequence in the text's symbols; and that `dvArityAll` at a literal no axiom of the text
    writes, no item of the text, adds none either. The section's other headline statements (its
    comment says what each states): `Rules.val_elem`, `Rules.int_elem`, `Rules.app0_inh`,
    `Rules.d_inh`, `Rules.e_inh`, `Rules.p_inh`, `Rules.q_inh`.
  - Constructor sentences (59): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 8 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (62): Γ with it has no model (`idem_refuted`).
  - Library sample, 199 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (50);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlLhsValueSort

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-lhs-value-sort.kompile.kore"
definition_of defn from "f2-examples/e3-ml-lhs-value-sort.kompile.kore"
user_axioms U from "f2-examples/e3-ml-lhs-value-sort.kompile.kore" module "E3-ML-LHS-VALUE-SORT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-LHS-VALUE-SORT")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 298 := by decide +kernel

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
  [("function equation", [247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264,
      265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277]),
   ("rewrite rule", [186, 187, 188]),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 78, 86, 92, 98, 102, 129, 130, 132, 136, 143]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30, 93, 103, 133, 137]),
   ("distinctness", [79, 80, 81, 82, 83, 84, 87, 88, 89, 90, 91, 94, 95, 96, 97, 99, 100, 101, 104, 105, 134]),
   ("no junk", [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]),
   ("function functional", [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      57, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 77, 85, 106, 108, 126, 127, 128, 131, 135, 138,
      139, 140, 141]),
   ("collection law", [54, 55, 56, 58, 59, 60, 61, 63, 64]),
   ("library", [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
      180, 181, 182, 183, 184, 185, 189, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
      202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
      220, 221, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238,
      239, 240, 241, 242, 280, 281, 282, 283, 299, 300]),
   ("set idempotence", [62]),
   ("set-variable lemma", [157, 158, 159, 160, 161, 301]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [37, 41, 43, 74, 76, 107, 125, 142, 144, 190, 222, 243, 244, 245, 246, 278, 279, 284, 285,
      286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298])]

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
    [("function equation", 31), ("rewrite rule", 3), ("priority equation", 0), ("constructor functional", 14), ("subsort", 16), ("injectivity", 8), ("distinctness", 21), ("no junk", 12), ("function functional", 16), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 32)] := by
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
  [(284, "Bool"), (285, "Exp"), (286, "GeneratedCounterCell"), (287, "GeneratedCounterCellOpt"),
   (288, "GeneratedTopCell"), (289, "GeneratedTopCellFragment"), (290, "Int"), (291, "K"),
   (292, "KCell"), (293, "KCellOpt"), (294, "KItem"), (295, "List"), (296, "Map"), (297, "Set"),
   (298, "Val")]

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
  [(14, "subsort"), (16, "subsort"), (78, "constructor functional"), (79, "distinctness"),
   (80, "distinctness"), (81, "distinctness"), (82, "distinctness"), (83, "distinctness"),
   (84, "distinctness"), (86, "constructor functional"), (87, "distinctness"),
   (88, "distinctness"), (89, "distinctness"), (90, "distinctness"), (91, "distinctness"),
   (92, "constructor functional"), (93, "injectivity"), (94, "distinctness"), (95, "distinctness"),
   (96, "distinctness"), (97, "distinctness"), (98, "constructor functional"),
   (99, "distinctness"), (100, "distinctness"), (101, "distinctness"),
   (102, "constructor functional"), (103, "injectivity"), (104, "distinctness"),
   (105, "distinctness"), (110, "function functional"), (124, "function functional"),
   (132, "constructor functional"), (133, "injectivity"), (134, "distinctness"),
   (136, "constructor functional"), (137, "injectivity"), (143, "constructor functional"),
   (146, "no junk"), (155, "no junk"), (156, "no junk"), (186, "rewrite rule"),
   (187, "rewrite rule"), (188, "rewrite rule"), (246, "no direction"), (249, "function equation"),
   (250, "function equation"), (276, "function equation"), (277, "function equation"),
   (285, "no direction"), (298, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
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

theorem sig_sizes : (sigItems c).length = 215 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 138, 99, 5, 34) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 25).all inSigItems = true := by decide +kernel
theorem declsE_25 : (((declItems).drop 25).take 25).all inSigItems = true := by decide +kernel
theorem declsE_50 : (((declItems).drop 50).take 25).all inSigItems = true := by decide +kernel
theorem declsE_75 : (((declItems).drop 75).take 25).all inSigItems = true := by decide +kernel
theorem declsE_100 : ((declItems).drop 100).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    tieAllE_range (a := 50) (n := 25) declsE_50 <|
    tieAllE_range (a := 75) (n := 25) declsE_75 <|
    declsE_100

/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of
a symbol Γ has, for every H. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-! ## Consistency for every H -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

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
def fnFunIdx : List Nat := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]

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
  [U.ax261, U.ax269, U.ax268, U.ax267, U.ax266, U.ax273, U.ax272, U.ax275, U.ax274, U.ax271,
   U.ax270, U.ax248, U.ax247, U.ax260, U.ax259, U.ax256, U.ax255, U.ax258, U.ax257, U.ax263,
   U.ax262, U.ax265, U.ax264, U.ax252, U.ax251, U.ax254, U.ax253, U.ax277, U.ax276, U.ax250,
   U.ax249]

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

theorem nj145 : (trS U.ax145).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj151 : (trS U.ax151).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj154 : (trS U.ax154).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax145, U.ax151, U.ax154], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj145]; exact orTopBot_valid hD rfl
  · rw [nj151]; exact orTopBot_valid hD rfl
  · rw [nj154]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax146, U.ax147, U.ax148, U.ax149, U.ax150, U.ax152, U.ax153, U.ax156],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax146, U.ax147, U.ax148, U.ax149, U.ax150, U.ax152, U.ax153, U.ax156],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax155).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (155)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax155).pat := by
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
   U.ax78, U.ax79, U.ax80, U.ax81, U.ax82, U.ax83, U.ax84, U.ax86, U.ax87, U.ax88, U.ax89, U.ax90,
   U.ax91, U.ax92, U.ax93, U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax99, U.ax100, U.ax101,
   U.ax102, U.ax103, U.ax104, U.ax105, U.ax129, U.ax130, U.ax132, U.ax133, U.ax134, U.ax136,
   U.ax137, U.ax143]

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

theorem idem_pattern : U.ax62.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax62).pat = (trAxiom [] [] U.ax62).pat := by decide +kernel

/-- `0` as a KItem, and the set `SetItem(0)`. -/
def a0 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem idem_vars : (U.ax62.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax62.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax62.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 62 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax62).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax62.ax.sortVars U.ax62.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax62.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax62.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 199, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax199).pat = (trAxiom [] [] U.ax199).pat := by decide +kernel
theorem s166_pattern : U.ax199.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax199.ax.sortVars.map sortVarKey ++ freeOf [] U.ax199.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax199.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 199 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax199.ax.sortVars U.ax199.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax199).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax199.ax.sortVars U.ax199.ax.pattern = t at he ⊢
  rw [s166_pattern]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hIg := (interp_guard_evar hD).mp hg.2
  rw [interp_equal hD]
  intro a
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  have hS : ∀ b, (trSort t (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) e
  obtain ⟨hes0, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 0) = some Srt.int from rfl) e
  have hgraph := sat_dom hI (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int n, KCore.int 0], some (KCore.int (n - 0)),
    by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  simp only [Int.sub_zero] at hg2
  -- the left side at `e` is the graph's application
  have hL : ∀ b, (tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])).interpret I e b ↔
      (KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0]))).interpret I e b := by
    intro b
    have h1 : tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ .evar (t.ev kI)) ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt")) := rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int n)) ⬝ den (cH H) (KCore.int 0) := by
      rw [symApp_noInst (c := cH H) (f := intSub) (by rw [(sub_name H).1]; exact (sub_name H).2), (sub_name H).1]; rfl
    rw [h1, h2]
    refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) b
    · rw [interp_evar, he, hes]
    · rw [den_int0]
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hL b, hg2 b, hes b]
    rw [KoreAML.tr]
    show _ ↔ (sAnd (tr ⟨t, []⟩ vI) (tr ⟨t, []⟩ (.top (KoreAML.srt "Int")))).interpret I e b
    rw [interp_sAnd, KoreAML.tr]
    show _ ↔ (Pattern.evar (t.ev kI)).interpret I e b ∧ (sTop (trSort t (KoreAML.srt "Int"))).interpret I e b
    rw [interp_evar, he, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of hS]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩


theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)
/-- **Sentence 199 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax199 (trS U.ax199).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The rules (186, 187, 188): W1 from the sentences, the G-nonempty items of Val and Int and the text's signature, for every H (by hand)

Three sentences, five rule items, each with a variable of its axiom that a rule read from it does
not hold at a sort with an element: 186, `e(_:Val) #Or d() => b()` (`rE`, `rD`); 187,
`p(_:Int) #Or q(_:Int) => b()` (`rP`, `rQ`); 188, `c(#Exists Y:Val. a()) => b()` (`rC`). Each
sentence states its rewrite for every element of its variables' sorts; Γ's item of a rule read
without a variable states it once, and the sentence entails it where the variable's sort has an
element (`TieRuleUnheld.rule_w1_drop`, `TieRuleUnheld.sub_exists_unheld`), which the text's
G-nonempty item of Val or Int gives (`ruleSigAux`, `ruleSigAux_text`: items of the signature of
`Theory.ofDefinition kore`, which `ΓSig` does not hold). The arities of `e`, `p`, `q` and of the
constant `d` (`ΓSig`) put each disjunct in `\or{SortExp{}}`. So each item is a consequence of its
sentence with those two items and the text's signature (`rule_from_text_aux`, every H); no item of
`ΓDomains` is a premise. -/

deriving instance DecidableEq for KoreAML.SortDecl

namespace Rules

def kCell : Sym := 384
def symA : Sym := 386
def symB : Sym := 387
def symC : Sym := 388
def symD : Sym := 389
def symE : Sym := 390
def symP : Sym := 391
def symQ : Sym := 392
def symV : Sym := 393
def sVal : Srt := 32
def sExp : Srt := 33

theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" ∧ c.symName symE = "Lble" ∧ c.symName symP = "Lblp" ∧
    c.symName symQ = "Lblq" ∧ c.symName symV = "Lblv" := by
  decide +kernel

theorem sort_names : c.sortName sVal = "Val" ∧ c.sortName sExp = "Exp" ∧ c.sortName Srt.int = "Int" := by
  decide +kernel

/-! ### The rules: Γ's five axioms -/

noncomputable def rE : Rule := c.rules[0]'(by decide +kernel)
noncomputable def rD : Rule := c.rules[1]'(by decide +kernel)
noncomputable def rP : Rule := c.rules[2]'(by decide +kernel)
noncomputable def rQ : Rule := c.rules[3]'(by decide +kernel)
noncomputable def rC : Rule := c.rules[4]'(by decide +kernel)

/-- Γ's axioms of the rules: `e(X) => b()`, `d() => b()`, `p(X) => b()`, `q(X) => b()`,
`c(a()) => b()`. -/
noncomputable def pE : Kore.Pattern := prioRuleK c rE
noncomputable def pD : Kore.Pattern := prioRuleK c rD
noncomputable def pP : Kore.Pattern := prioRuleK c rP
noncomputable def pQ : Kore.Pattern := prioRuleK c rQ
noncomputable def pC : Kore.Pattern := prioRuleK c rC

theorem ruleItems_eq : ruleItems c =
    [trAxiom [] [] ⟨0, "kernel", ⟨[], pE, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], pD, []⟩⟩,
     trAxiom [] [] ⟨0, "kernel", ⟨[], pP, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], pQ, []⟩⟩,
     trAxiom [] [] ⟨0, "kernel", ⟨[], pC, []⟩⟩] := by kernel_rfl

/-- The parts `\rewrites{C}(L', r)` of an axiom. -/
noncomputable def partsOf (p : Kore.Pattern) : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

noncomputable def qE := partsOf pE
noncomputable def qD := partsOf pD
noncomputable def qP := partsOf pP
noncomputable def qQ := partsOf pQ
noncomputable def qC := partsOf pC

kernel_rfl qE_eq : TieRuleLhs.rwParts pE = some qE
kernel_rfl qD_eq : TieRuleLhs.rwParts pD = some qD
kernel_rfl qP_eq : TieRuleLhs.rwParts pP = some qP
kernel_rfl qQ_eq : TieRuleLhs.rwParts pQ = some qQ
kernel_rfl qC_eq : TieRuleLhs.rwParts pC = some qC

/-- The context of a left side's term around the subterm at `path`, and the subterm. -/
noncomputable def cutOf (path : List Nat) (q : Kore.KSort × Kore.Pattern × Kore.Pattern) : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt path (TieRuleLhs.andHead q.2.1)).getD (.hole, .top KoreAML.R)

/-- Around the item of the `k` cell, for the four rules read from a disjunction. -/
noncomputable def cutE := cutOf [0, 0, 0, 0] qE
noncomputable def cutD := cutOf [0, 0, 0, 0] qD
noncomputable def cutP := cutOf [0, 0, 0, 0] qP
noncomputable def cutQ := cutOf [0, 0, 0, 0] qQ
/-- Around the argument of `c`. -/
noncomputable def cutC := cutOf [0, 0, 0, 0, 0] qC

kernel_rfl lE_eq : qE.2.1 = .and qE.1 (cutE.1.fill cutE.2 :: .top qE.1 :: (TieRuleLhs.andTail qE.2.1).drop 1)
kernel_rfl lD_eq : qD.2.1 = .and qD.1 (cutD.1.fill cutD.2 :: .top qD.1 :: (TieRuleLhs.andTail qD.2.1).drop 1)
kernel_rfl lP_eq : qP.2.1 = .and qP.1 (cutP.1.fill cutP.2 :: .top qP.1 :: (TieRuleLhs.andTail qP.2.1).drop 1)
kernel_rfl lQ_eq : qQ.2.1 = .and qQ.1 (cutQ.1.fill cutQ.2 :: .top qQ.1 :: (TieRuleLhs.andTail qQ.2.1).drop 1)
kernel_rfl lC_eq : qC.2.1 = .and qC.1 (cutC.1.fill cutC.2 :: .top qC.1 :: (TieRuleLhs.andTail qC.2.1).drop 1)

/-- The variable of `rE`, of Val, and of `rP` and `rQ`, of Int (the first of each rule). -/
noncomputable def xV : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Val")
noncomputable def xI : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Int")

/-- The variable of the sentence that the rule does not hold: a name no axiom of Γ holds. -/
noncomputable def yV : Kore.EVar := KoreAML.evar "VarUnheld" (KoreAML.srt "Val")
noncomputable def yI : Kore.EVar := KoreAML.evar "VarUnheld" (KoreAML.srt "Int")

-- The subterms as Γ writes them.
kernel_rfl dE_eq : cutE.2 = symApp c symE [.var (.evar xV)]
kernel_rfl dD_eq : cutD.2 = symApp c symD []
kernel_rfl dP_eq : cutP.2 = symApp c symP [.var (.evar xI)]
kernel_rfl dQ_eq : cutQ.2 = symApp c symQ [.var (.evar xI)]
kernel_rfl dC_eq : cutC.2 = symApp c symA []

/-! ### The left sides as the text writes them -/

/-- Sentence 186 in the variables of `rE`: the item of the `k` cell is `\or{SortExp{}}(e(X), d())`. -/
noncomputable def LtextE : Kore.Pattern :=
  .and qE.1 [cutE.1.fill (.or (KoreAML.srt "Exp") [cutE.2, symApp c symD []]), .top qE.1]

/-- Sentence 186 in the variables of `rD`, with the variable `rD` does not hold. -/
noncomputable def LtextD : Kore.Pattern :=
  .and qD.1 [cutD.1.fill (.or (KoreAML.srt "Exp") [symApp c symE [.var (.evar yV)], cutD.2]), .top qD.1]

/-- Sentence 187 in the variables of `rP`: `\or{SortExp{}}(p(X), q(Y))`, Y not held by `rP`. -/
noncomputable def LtextP : Kore.Pattern :=
  .and qP.1 [cutP.1.fill (.or (KoreAML.srt "Exp") [cutP.2, symApp c symQ [.var (.evar yI)]]), .top qP.1]

/-- Sentence 187 in the variables of `rQ`: `\or{SortExp{}}(p(Y), q(X))`, Y not held by `rQ`. -/
noncomputable def LtextQ : Kore.Pattern :=
  .and qQ.1 [cutQ.1.fill (.or (KoreAML.srt "Exp") [symApp c symP [.var (.evar yI)], cutQ.2]), .top qQ.1]

/-- Sentence 188 in the variables of `rC`: the argument of `c` is `\exists{SortExp{}}(Y:Val, a())`. -/
noncomputable def LtextC : Kore.Pattern :=
  .and qC.1 [cutC.1.fill (.exist (KoreAML.srt "Exp") yV cutC.2), .top qC.1]

noncomputable def fTE : List VarKey := (freeOf [] (.rewrites qE.1 LtextE qE.2.2)).eraseDups
noncomputable def fTD : List VarKey := (freeOf [] (.rewrites qD.1 LtextD qD.2.2)).eraseDups
noncomputable def fTP : List VarKey := (freeOf [] (.rewrites qP.1 LtextP qP.2.2)).eraseDups
noncomputable def fTQ : List VarKey := (freeOf [] (.rewrites qQ.1 LtextQ qQ.2.2)).eraseDups
noncomputable def fTC : List VarKey := (freeOf [] (.rewrites qC.1 LtextC qC.2.2)).eraseDups

/-- The table of sentence 188's form: the bound variable first, as in the text. -/
noncomputable def tC : VarTable := tableOf [] (.rewrites qC.1 LtextC qC.2.2)

/-! ### Each sentence is the item of its form (kernel), up to the indices of the variables -/

theorem rule_textE : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pE) fTE qE.1 LtextE qE.2.2) [] = some (trS U.ax186).pat := by
  decide +kernel
theorem fT_freeE : fTE.all (fun k => (freeOf [] pE).eraseDups.contains k) = true := by decide +kernel
theorem K_noAliasE : cutE.1.noAlias ⟨tableOf [] pE, []⟩ = true := by decide +kernel

theorem rule_textD : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pD) fTD qD.1 LtextD qD.2.2) [(3, 9), (2, 3), (1, 2), (9, 1)] = some (trS U.ax186).pat := by
  decide +kernel
theorem K_noAliasD : cutD.1.noAlias ⟨tableOf [] pD, []⟩ = true := by decide +kernel

theorem rule_textP : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pP) fTP qP.1 LtextP qP.2.2) [(4, 9), (3, 4), (2, 3), (9, 2)] = some (trS U.ax187).pat := by
  decide +kernel
theorem K_noAliasP : cutP.1.noAlias ⟨tableOf [] pP, []⟩ = true := by decide +kernel

theorem rule_textQ : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pQ) fTQ qQ.1 LtextQ qQ.2.2) [(4, 9), (3, 4), (2, 3), (1, 2), (9, 1)] = some (trS U.ax187).pat := by
  decide +kernel
theorem K_noAliasQ : cutQ.1.noAlias ⟨tableOf [] pQ, []⟩ = true := by decide +kernel

/-- Sentence 188 is the item of its form at the form's own table. -/
theorem rule_textC : TiePair.renSeq (TieRuleLhs.itemAt tC fTC qC.1 LtextC qC.2.2) [] = some (trS U.ax188).pat := by
  decide +kernel
/-- Γ's item of `rC` is the item of its axiom at that table, up to the indices of the variables. -/
theorem ruleC_item : TiePair.renSeq (TieRuleLhs.itemAt tC fTC qC.1 qC.2.1 qC.2.2) [(2, 1), (3, 2)] =
    some (trAxiom [] [] ⟨0, "kernel", ⟨[], pC, []⟩⟩).pat := by
  decide +kernel
theorem K_noAliasC : cutC.1.noAlias ⟨tC, []⟩ = true := by decide +kernel

/-! ### The variable a rule does not hold is in no part of its item -/

theorem dropD : (∀ k ∈ fTD, k = evarKey yV ∨ k ∈ (freeOf [] pD).eraseDups) ∧
    (tr ⟨tableOf [] pD, []⟩ (.rewrites qD.1 qD.2.1 qD.2.2) ≡ inhOf (trSort (tableOf [] pD) qD.1)).isFreeEvar
      ((tableOf [] pD).ev (evarKey yV)) = false ∧
    (∀ k ∈ (freeOf [] pD).eraseDups, (guardOf (tableOf [] pD) k).isFreeEvar ((tableOf [] pD).ev (evarKey yV)) = false) := by
  decide +kernel

theorem dropP : (∀ k ∈ fTP, k = evarKey yI ∨ k ∈ (freeOf [] pP).eraseDups) ∧
    (tr ⟨tableOf [] pP, []⟩ (.rewrites qP.1 qP.2.1 qP.2.2) ≡ inhOf (trSort (tableOf [] pP) qP.1)).isFreeEvar
      ((tableOf [] pP).ev (evarKey yI)) = false ∧
    (∀ k ∈ (freeOf [] pP).eraseDups, (guardOf (tableOf [] pP) k).isFreeEvar ((tableOf [] pP).ev (evarKey yI)) = false) := by
  decide +kernel

theorem dropQ : (∀ k ∈ fTQ, k = evarKey yI ∨ k ∈ (freeOf [] pQ).eraseDups) ∧
    (tr ⟨tableOf [] pQ, []⟩ (.rewrites qQ.1 qQ.2.1 qQ.2.2) ≡ inhOf (trSort (tableOf [] pQ) qQ.1)).isFreeEvar
      ((tableOf [] pQ).ev (evarKey yI)) = false ∧
    (∀ k ∈ (freeOf [] pQ).eraseDups, (guardOf (tableOf [] pQ) k).isFreeEvar ((tableOf [] pQ).ev (evarKey yI)) = false) := by
  decide +kernel

/-- The body `a()` of the `\exists` does not hold its variable. -/
theorem freeC : (tr ⟨tC, []⟩ cutC.2).isFreeEvar (tC.ev (evarKey yV)) = false := by decide +kernel

/-! ### Elements of the sorts, and the disjuncts' sort -/

def vV : GroundTerm := .ctor symV []
def dV : GroundTerm := .ctor symD []

/-- The items of the text's signature that give Val and Int an element (G-nonempty of the
declarations `sort SortVal{}` and `hooked-sort SortInt{}`), which `ΓSig` does not hold. -/
def valNonempty : Item := nonemptyItem ⟨"SortVal", [], false⟩
def intNonempty : Item := nonemptyItem ⟨"SortInt", [], true⟩

theorem sortDecls_mem : (⟨"SortVal", [], false⟩ : SortDecl) ∈ kore.sortDecls ∧
    (⟨"SortInt", [], true⟩ : SortDecl) ∈ kore.sortDecls := by decide +kernel

/-- G-nonempty of a declared sort is an item of the signature of the text's theory. -/
theorem nonempty_text {sd : SortDecl} (h : sd ∈ kore.sortDecls) :
    nonemptyItem sd ∈ (Theory.ofDefinition kore).signature := by
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, h, rfl⟩)))))

/-- **Val has an element**, in a model of Val's G-nonempty item. -/
theorem val_elem {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hN : I ⊧ᴵ valNonempty.pat) : ∃ a, InS I "Val" a :=
  nonempty_of hD hN (e := KoreAML.val0)

/-- **Int has an element**, in a model of Int's G-nonempty item. -/
theorem int_elem {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hN : I ⊧ᴵ intNonempty.pat) : ∃ a, InS I "Int" a :=
  nonempty_of hD hN (e := KoreAML.val0)

/-- `d`'s signature: a constant of Exp. -/
def kd : CtorSig := ⟨symD, [], sExp⟩

theorem kd_mem : kd ∈ kernelSyms c := by decide +kernel
theorem noInst_d : instDecode? (c.symName kd.name) = none := by decide +kernel

/-- **The arity of a constant, from `ΓSig`**: what a symbol of no argument denotes is in its result
sort. -/
theorem app0_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {k : CtorSig} (hk : k ∈ kernelSyms c) (hargs : k.args = [])
    (hno : instDecode? (c.symName k.name) = none) {t : VarTable} {e : Valuation M} (m : M)
    (h : (tr ⟨t, []⟩ (symApp c k.name [])).interpret I e m) : InS I (c.sortName k.result) m := by
  rw [tr_symApp, trArgs_appList, interp_appList] at h
  obtain ⟨a, ha, bs, hbs, hm⟩ := h
  cases hbs
  have hit : I ⊧ᴵ (symArityItem c k).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity hk, rfl⟩))
  rw [symArityItem_noInst hno] at hit
  rw [symHead_noInst (c := c) hno] at ha
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  apply (inS_iff (I := I) KoreAML.val0).mp
  apply hinc
  rw [interp_appList]
  refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [], ?_, hm⟩
  simp only [hargs, List.map_nil]
  exact .nil

/-- **`d()` denotes elements of Exp** (the arity of the constant `d`, `ΓSig`). -/
theorem d_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M}
    (b : M) (h : (tr ⟨t, []⟩ (symApp c symD [])).interpret I e b) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e b := by
  have h1 := app0_inh hD hS (k := kd) kd_mem rfl noInst_d b h
  rw [show c.sortName kd.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- The signatures of `e`, `p` and `q`. -/
def ke : CtorSig := ⟨symE, [sVal], sExp⟩
def kp : CtorSig := ⟨symP, [Srt.int], sExp⟩
def kq : CtorSig := ⟨symQ, [Srt.int], sExp⟩

theorem k_mem : ke ∈ kernelSyms c ∧ kp ∈ kernelSyms c ∧ kq ∈ kernelSyms c := by decide +kernel
theorem noInst : instDecode? (c.symName ke.name) = none ∧ instDecode? (c.symName kp.name) = none ∧
    instDecode? (c.symName kq.name) = none := by decide +kernel

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- The guard of a variable of the sort n puts its value in n. -/
theorem x_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {t : VarTable}
    {e : Valuation M} {m0 : M} {x : Kore.EVar} {n : String} (hx : x.sort = KoreAML.srt n)
    (hg : (guardOf t (evarKey x)).interpret I e m0)
    (b : M) (h : (tr ⟨t, []⟩ (.var (.evar x))).interpret I e b) : InS I n b := by
  have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
  simp only [tr] at h
  rw [interp_evar] at h
  rw [h]
  rw [hx, trSort_srt] at h1
  exact (inS_iff _).mp h1

/-- **`e` at a pattern whose elements are in Val is in Exp** (the arity of `e`, `ΓSig`). -/
theorem e_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Val" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c symE [p])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  have h1 := TieRuleUnheld.app1_inh hD hS (k := ke) (s := sVal) k_mem.1 rfl noInst.1
    (fun b hb => by rw [show c.sortName sVal = "Val" from sort_names.1]; exact hp b hb) m h
  rw [show c.sortName ke.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- **`p` at a pattern whose elements are in Int is in Exp.** -/
theorem p_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Int" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c symP [p])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  have h1 := TieRuleUnheld.app1_inh hD hS (k := kp) (s := Srt.int) k_mem.2.1 rfl noInst.2.1
    (fun b hb => by rw [show c.sortName Srt.int = "Int" from sort_names.2.2]; exact hp b hb) m h
  rw [show c.sortName kp.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- **`q` at a pattern whose elements are in Int is in Exp.** -/
theorem q_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Int" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c symQ [p])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  have h1 := TieRuleUnheld.app1_inh hD hS (k := kq) (s := Srt.int) k_mem.2.2 rfl noInst.2.2
    (fun b hb => by rw [show c.sortName Srt.int = "Int" from sort_names.2.2]; exact hp b hb) m h
  rw [show c.sortName kq.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

theorem x_freeE : evarKey xV ∈ (freeOf [] pE).eraseDups := by decide +kernel
theorem x_inP : evarKey xI ∈ fTP := by decide +kernel
theorem x_inQ : evarKey xI ∈ fTQ := by decide +kernel

/-! ### Every element of Γ's left side is one of the text's -/

/-- `rE`: `e(X)` is in `\or{SortExp{}}(e(X), d())`. -/
theorem leftE {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ (freeOf [] pE).eraseDups, (guardOf (tableOf [] pE) k).interpret I e m0)
    (h : (tr ⟨tableOf [] pE, []⟩ qE.2.1).interpret I e a) : (tr ⟨tableOf [] pE, []⟩ LtextE).interpret I e a := by
  rw [lE_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextE
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutE.1 K_noAliasE (TieRuleLhs.sub_or_left fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dE_eq] at h'
    exact e_inh hD hS (fun b hb => x_inh hD rfl (hg _ x_freeE) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rD`: `d()` is in `\or{SortExp{}}(e(Y), d())`. -/
theorem leftD {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] pD, []⟩ qD.2.1).interpret I e a) : (tr ⟨tableOf [] pD, []⟩ LtextD).interpret I e a := by
  rw [lD_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextD
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutD.1 K_noAliasD (TieRuleLhs.sub_or_right fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dD_eq] at h'
    exact d_inh hD hS a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rP`: `p(X)` is in `\or{SortExp{}}(p(X), q(Y))`. -/
theorem leftP {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ fTP, (guardOf (tableOf [] pP) k).interpret I e m0)
    (h : (tr ⟨tableOf [] pP, []⟩ qP.2.1).interpret I e a) : (tr ⟨tableOf [] pP, []⟩ LtextP).interpret I e a := by
  rw [lP_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextP
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutP.1 K_noAliasP (TieRuleLhs.sub_or_left fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dP_eq] at h'
    exact p_inh hD hS (fun b hb => x_inh hD rfl (hg _ x_inP) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rQ`: `q(X)` is in `\or{SortExp{}}(p(Y), q(X))`. -/
theorem leftQ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ fTQ, (guardOf (tableOf [] pQ) k).interpret I e m0)
    (h : (tr ⟨tableOf [] pQ, []⟩ qQ.2.1).interpret I e a) : (tr ⟨tableOf [] pQ, []⟩ LtextQ).interpret I e a := by
  rw [lQ_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextQ
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutQ.1 K_noAliasQ (TieRuleLhs.sub_or_right fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dQ_eq] at h'
    exact q_inh hD hS (fun b hb => x_inh hD rfl (hg _ x_inQ) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rC`: `a()` is in `\exists Y:Val. a()`, Val having an element. -/
theorem leftC {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hex : ∃ a, InS I "Val" a) (e : Valuation M) (a : M)
    (h : (tr ⟨tC, []⟩ qC.2.1).interpret I e a) : (tr ⟨tC, []⟩ LtextC).interpret I e a := by
  rw [lC_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextC
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact TieRuleLhs.tr_fill_mono _ cutC.1 K_noAliasC
      (fun a' h' => TieRuleUnheld.sub_exists_unheld hD rfl hex freeC a' h') a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-! ### W1 -/

/-- The rule sentences. -/
noncomputable def ruleText : List AxiomDecl := [U.ax186, U.ax187, U.ax188]

/-- The rule sentences are the class rewrite rule of the account. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

/-- The sentence each of Γ's rule items is read from, in `ruleItems`' order. -/
noncomputable def ruleTextOf : List AxiomDecl := [U.ax186, U.ax186, U.ax187, U.ax187, U.ax188]

/-- No other sentence of the text is a premise. -/
noncomputable def ruleAux : List AxiomDecl := []

/-- The items of the text's signature the statement reads, which `ΓSig` does not hold: Val and Int
have an element. -/
def ruleSigAux : List Item := [nonemptyItem ⟨"SortVal", [], false⟩, nonemptyItem ⟨"SortInt", [], true⟩]

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rcases List.mem_cons.mp hit with rfl | hit
  · exact nonempty_text sortDecls_mem.1
  · rw [List.mem_singleton.mp hit]; exact nonempty_text sortDecls_mem.2

/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's five rule items, with its
premise `⌈r⌉`, is a consequence of the sentence it is read from (`ruleTextOf`) with the G-nonempty
items of Val and Int (`ruleSigAux`) and the text's signature (`ΓSig`), for every H. The signature
gives the arities of `e`, `p` and `q` (a disjunct `f(X)` is in `\or{SortExp{}}`) and of the
constant `d` (`d()` is in Exp); the G-nonempty items give, for the four items that do not hold a
variable of their sentence, an element of that variable's sort. No item of `ΓDomains` is a
premise. -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  have pre : ∀ {ad : AxiomDecl} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M},
      I ⊧ᴵP (TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H)) →
        DefOK I ∧ (I ⊧ᴵ (trS ad).pat) ∧ (I ⊧ᴵP ΓSig c) ∧ (I ⊧ᴵ valNonempty.pat) ∧ (I ⊧ᴵ intNonempty.pat) := fun hI =>
    ⟨TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ),
     hI _ (Or.inl (Or.inl (List.mem_cons_self ..))),
     fun φ hφ => hI φ (Or.inr (by unfold ΓSig at hφ ⊢; rw [sigItems_withHooks]; exact hφ)),
     hI _ (Or.inl (Or.inl (by simp [ruleAux, ruleSigAux, valNonempty]))),
     hI _ (Or.inl (Or.inl (by simp [ruleAux, ruleSigAux, intNonempty])))⟩
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl
  · refine ⟨U.ax186, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, -, -⟩ := pre hI
    exact TieRuleLhs.rule_w1 hD qE_eq rule_textE fT_freeE hT fun e m0 hg a ha => leftE hD hS e m0 a hg ha
  · refine ⟨U.ax186, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, hV, -⟩ := pre hI
    exact TieRuleUnheld.rule_w1_drop hD (x := yV) rfl qD_eq rule_textD dropD.1 dropD.2.1 dropD.2.2
      (val_elem hD hV) hT fun e _ _ a ha => leftD hD hS e a ha
  · refine ⟨U.ax187, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, -, hN⟩ := pre hI
    exact TieRuleUnheld.rule_w1_drop hD (x := yI) rfl qP_eq rule_textP dropP.1 dropP.2.1 dropP.2.2
      (int_elem hD hN) hT fun e m0 hg a ha => leftP hD hS e m0 a hg ha
  · refine ⟨U.ax187, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, -, hN⟩ := pre hI
    exact TieRuleUnheld.rule_w1_drop hD (x := yI) rfl qQ_eq rule_textQ dropQ.1 dropQ.2.1 dropQ.2.2
      (int_elem hD hN) hT fun e m0 hg a ha => leftQ hD hS e m0 a hg ha
  · refine ⟨U.ax188, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, -, hV, -⟩ := pre hI
    have h1 : I ⊧ᴵ TieRuleLhs.itemAt tC fTC qC.1 qC.2.1 qC.2.2 := fun e m =>
      TieRuleLhs.lhs_entails hD (fT := fTC) (fG := fTC) (fun _ hk => hk) ((TiePair.renSeq_iff rule_textC).mp hT) e m
        (fun _ a ha => leftC hD (val_elem hD hV) e a ha)
    exact (TiePair.renSeq_iff ruleC_item).mpr h1

/-- The priority each sentence's attributes state is its rules'. -/
theorem rule_prios : ruleTextOf.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) = c.rules.map (·.prio) := by
  decide +kernel

end Rules

end KCore.TieE3MlLhsValueSort

#check @KCore.TieE3MlLhsValueSort.noRaw
#check @KCore.TieE3MlLhsValueSort.readsConfined_c
#check @KCore.TieE3MlLhsValueSort.userAxioms_eq
#check @KCore.TieE3MlLhsValueSort.coreOK
#check @KCore.TieE3MlLhsValueSort.wf_defn
#check @KCore.TieE3MlLhsValueSort.account
#check @KCore.TieE3MlLhsValueSort.account_sizes
#check @KCore.TieE3MlLhsValueSort.account_classes
#check @KCore.TieE3MlLhsValueSort.account_absent
#check @KCore.TieE3MlLhsValueSort.absent_closed
#check @KCore.TieE3MlLhsValueSort.absent_proj_below_c
#check @KCore.TieE3MlLhsValueSort.absent_proj_below
#check @KCore.TieE3MlLhsValueSort.lists_in_account
#check @KCore.TieE3MlLhsValueSort.attrs_agree
#check @KCore.TieE3MlLhsValueSort.sig_origin
#check @KCore.TieE3MlLhsValueSort.decls_entailed
#check @KCore.TieE3MlLhsValueSort.consistent
#check @KCore.TieE3MlLhsValueSort.fnFun_indices
#check @KCore.TieE3MlLhsValueSort.fnFun_account
#check @KCore.TieE3MlLhsValueSort.fnFun_checked
#check @KCore.TieE3MlLhsValueSort.fnFun_trS
#check @KCore.TieE3MlLhsValueSort.fnFun_at_values
#check @KCore.TieE3MlLhsValueSort.fnFun_at_values_step
#check @KCore.TieE3MlLhsValueSort.fn_shape
#check @KCore.TieE3MlLhsValueSort.fns_account
#check @KCore.TieE3MlLhsValueSort.fns_entailed
#check @KCore.TieE3MlLhsValueSort.fns_from_text
#check @KCore.TieE3MlLhsValueSort.fn_prios
#check @KCore.TieE3MlLhsValueSort.nojunk_trivial_entailed
#check @KCore.TieE3MlLhsValueSort.nojunk_items_entailed
#check @KCore.TieE3MlLhsValueSort.nojunk_kitem_entailed
#check @KCore.TieE3MlLhsValueSort.cons_entailed
#check @KCore.TieE3MlLhsValueSort.idem_refuted
#check @KCore.TieE3MlLhsValueSort.lib166
#check @KCore.TieE3MlLhsValueSort.lib166_at_values
#check @KCore.TieE3MlLhsValueSort.Rules.rules_account
#check @KCore.TieE3MlLhsValueSort.Rules.rule_from_text_aux
#check @KCore.TieE3MlLhsValueSort.Rules.ruleSigAux_text
#check @KCore.TieE3MlLhsValueSort.Rules.val_elem
#check @KCore.TieE3MlLhsValueSort.Rules.int_elem
#check @KCore.TieE3MlLhsValueSort.Rules.app0_inh
#check @KCore.TieE3MlLhsValueSort.Rules.d_inh
#check @KCore.TieE3MlLhsValueSort.Rules.e_inh
#check @KCore.TieE3MlLhsValueSort.Rules.p_inh
#check @KCore.TieE3MlLhsValueSort.Rules.q_inh
#print axioms KCore.TieE3MlLhsValueSort.noRaw
#print axioms KCore.TieE3MlLhsValueSort.readsConfined_c
#print axioms KCore.TieE3MlLhsValueSort.userAxioms_eq
#print axioms KCore.TieE3MlLhsValueSort.coreOK
#print axioms KCore.TieE3MlLhsValueSort.wf_defn
#print axioms KCore.TieE3MlLhsValueSort.account
#print axioms KCore.TieE3MlLhsValueSort.account_sizes
#print axioms KCore.TieE3MlLhsValueSort.account_classes
#print axioms KCore.TieE3MlLhsValueSort.account_absent
#print axioms KCore.TieE3MlLhsValueSort.absent_closed
#print axioms KCore.TieE3MlLhsValueSort.absent_proj_below_c
#print axioms KCore.TieE3MlLhsValueSort.absent_proj_below
#print axioms KCore.TieE3MlLhsValueSort.lists_in_account
#print axioms KCore.TieE3MlLhsValueSort.attrs_agree
#print axioms KCore.TieE3MlLhsValueSort.sig_origin
#print axioms KCore.TieE3MlLhsValueSort.decls_entailed
#print axioms KCore.TieE3MlLhsValueSort.consistent
#print axioms KCore.TieE3MlLhsValueSort.fnFun_indices
#print axioms KCore.TieE3MlLhsValueSort.fnFun_account
#print axioms KCore.TieE3MlLhsValueSort.fnFun_checked
#print axioms KCore.TieE3MlLhsValueSort.fnFun_trS
#print axioms KCore.TieE3MlLhsValueSort.fnFun_at_values
#print axioms KCore.TieE3MlLhsValueSort.fnFun_at_values_step
#print axioms KCore.TieE3MlLhsValueSort.fn_shape
#print axioms KCore.TieE3MlLhsValueSort.fns_account
#print axioms KCore.TieE3MlLhsValueSort.fns_entailed
#print axioms KCore.TieE3MlLhsValueSort.fns_from_text
#print axioms KCore.TieE3MlLhsValueSort.fn_prios
#print axioms KCore.TieE3MlLhsValueSort.nojunk_trivial_entailed
#print axioms KCore.TieE3MlLhsValueSort.nojunk_items_entailed
#print axioms KCore.TieE3MlLhsValueSort.nojunk_kitem_entailed
#print axioms KCore.TieE3MlLhsValueSort.cons_entailed
#print axioms KCore.TieE3MlLhsValueSort.idem_refuted
#print axioms KCore.TieE3MlLhsValueSort.lib166
#print axioms KCore.TieE3MlLhsValueSort.lib166_at_values
#print axioms KCore.TieE3MlLhsValueSort.Rules.rules_account
#print axioms KCore.TieE3MlLhsValueSort.Rules.rule_from_text_aux
#print axioms KCore.TieE3MlLhsValueSort.Rules.ruleSigAux_text
#print axioms KCore.TieE3MlLhsValueSort.Rules.val_elem
#print axioms KCore.TieE3MlLhsValueSort.Rules.int_elem
#print axioms KCore.TieE3MlLhsValueSort.Rules.app0_inh
#print axioms KCore.TieE3MlLhsValueSort.Rules.d_inh
#print axioms KCore.TieE3MlLhsValueSort.Rules.e_inh
#print axioms KCore.TieE3MlLhsValueSort.Rules.p_inh
#print axioms KCore.TieE3MlLhsValueSort.Rules.q_inh
