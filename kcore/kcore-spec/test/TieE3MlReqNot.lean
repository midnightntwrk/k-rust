/-
  The tie (C14) on `f2-examples/mlreqnot.kompile.kore`, the kompiled text of construct fixture e3-ml-req-not
  (`test/constructs/fixtures/e3-ml-req-not`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-req-not`, its rules section by hand (its text written there is
  `f2-examples/mlreqnot.kompile.kore` byte for byte, which this test reads); run from the package root:
  `lake env lean -j1 test/TieE3MlReqNot.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 264 sentences of the user module E3-ML-REQ-NOT, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 208 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes
    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's
    condition (`owed_rules`, `owed_clauses`), so Γ with the step's closure has a model for every
    H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (157), by hand, in the section `The rules` (`Rules`): each of Γ's rule items is a
    consequence of its text sentence with the text's sentences 138 (library), 133 (library), 147
    (library), 49 (hooked functional), 46 (hooked functional) (`Rules.ruleAux`), the item of the
    text's signature `nonemptyItem ⟨"SortInt", [], true⟩` (`Rules.ruleSigAux`; each an item of
    `(Theory.ofDefinition kore).signature`, `Rules.ruleSigAux_text`), the text's signature (`ΓSig`)
    and the premise `boolClosed` (every element of Bool is `true`'s or `false`'s), `Rules.ruleText`
    in `ruleItems`' order (`Rules.rule_from_text_closed`, W1, every H; `Rules.rules_account`).
    `ΓSig` holds the items of the text's declarations or surplus ones, the sort constant of a
    registry sort or the arity of a hooked symbol that the text does not declare at that shape
    (`sig_origin`), and the arity of every literal (`dvArityAll`). Two limits, argued and not
    proved: that a surplus item of a name the text declares with sort parameters adds no consequence
    in the text's symbols; and that `dvArityAll` at a literal no axiom of the text writes, no item
    of the text, adds none either. No sentence of the text states `boolClosed`; its ground is the
    builtin domain Bool, whose values are `true` and `false`; Γ does not hold it, the definition
    reading no confined sort (`readsConfined_c`: Γc is Γ), and without it W1 does not hold
    (`Rules.rule_not_from_text`). The other direction: `Rules.rule157_at_values`. Sentence 157 is
    tied under the premise (`underPremise`), not `uncovered`. The section's other headline
    statements (its comment says what each states): `Rules.rule_text0`, `Rules.true_iff_not_false`,
    `Rules.cond_iff`, `Rules.left_sub`, `Rules.left_sup`, `Rules.lit_sents`,
    `Rules.boolDist_of_text`, `Rules.boolDist_from_text`, `Rules.ClosedNeg157.sat_sig`,
    `Rules.ClosedNeg157.L0_o`, `Rules.ClosedNeg157.Ltext0_empty`, `Rules.ClosedNeg157.sat_fnl`,
    `Rules.ClosedNeg157.sat_simp`, `Rules.ClosedNeg157.text_holds`, `Rules.ClosedNeg157.item_fails`,
    `Rules.ClosedNeg157.sat_pre`, `Rules.ClosedNeg157.bool_other`, `Rules.rule_w2_closed`,
    `Rules.right_defined`, `Rules.rule_w2_closed_noprem`, `Rules.gt_at_value`,
    `Rules.left_sup_values`, `Rules.closed_model`.
  - Constructor sentences (32): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (61): Γ with it has no model (`idem_refuted`).
  - Library sample, 168 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (16);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
  The rule sentences tied under a premise that no sentence of the text states are `underPremise`
  (1), with the premise's name.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlReqNot

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlreqnot.kompile.kore"
definition_of defn from "f2-examples/mlreqnot.kompile.kore"
user_axioms U from "f2-examples/mlreqnot.kompile.kore" module "E3-ML-REQ-NOT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-REQ-NOT")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 264 := by decide +kernel

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
  [("function equation", [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233,
      234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]),
   ("rewrite rule", [157]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 78, 82, 106, 107, 109]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 83]),
   ("distinctness", [79, 80, 84]),
   ("no junk", [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]),
   ("function functional", [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
      56, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 77, 81, 86, 103, 104, 105, 108, 110, 111,
      112, 113, 114]),
   ("collection law", [53, 54, 55, 57, 58, 59, 60, 62, 63]),
   ("library", [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
      151, 152, 153, 154, 155, 156, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170,
      171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188,
      189, 190, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207,
      208, 209, 210, 211, 247, 248, 249, 250, 265, 266]),
   ("set idempotence", [61]),
   ("set-variable lemma", [128, 129, 130, 131, 132, 267]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 40, 42, 73, 75, 85, 102, 115, 116, 159, 191, 212, 213, 214, 215, 245, 246, 251, 252, 253,
      254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264])]

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
    [("function equation", 29), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 9), ("subsort", 15), ("injectivity", 5), ("distinctness", 3), ("no junk", 11), ("function functional", 15), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 31)] := by
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
  [(251, "Bool"), (252, "Exp"), (253, "GeneratedCounterCell"), (254, "GeneratedCounterCellOpt"),
   (255, "GeneratedTopCell"), (256, "GeneratedTopCellFragment"), (257, "Int"), (258, "K"),
   (259, "KCell"), (260, "KCellOpt"), (261, "KItem"), (262, "List"), (263, "Map"), (264, "Set")]

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
  [(14, "subsort"), (78, "constructor functional"), (79, "distinctness"), (80, "distinctness"),
   (82, "constructor functional"), (83, "injectivity"), (84, "distinctness"),
   (88, "function functional"), (109, "constructor functional"), (118, "no junk"),
   (127, "no junk"), (157, "rewrite rule"), (215, "no direction"), (218, "function equation"),
   (219, "function equation"), (252, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- The rule sentences tied under a premise that no sentence of the text states, with the premise:
Γ's items are a consequence of the sentence with it, and the section on the rules states the other
direction. -/
def underPremise : List (Nat × String) :=
  [(157, "boolClosed")]

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

theorem sig_sizes : (sigItems c).length = 208 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 131, 93, 5, 33) := by
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

theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  (FnFacts.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)
    (show c.params.all (fun k => !k.raw) = true by decide +kernel)).obligations (openDecidedH H)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Function functional (15): the sort predicates' `functional` sentences, at values in every model of Γc -/

/- The class holds the `functional` sentences of 15 sort predicates `isX`,
`\exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val:SortBool{}, LblisX{}(K0:SortK{})))`. KCore builds
the sort predicates (`Semantics.sortPreds`): each has a value at every K, and a model of `Γc` reads
its application at a value's element as that value's element (`LibEv.sortPredFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and no condition over a
variable the patterns leave open). So each sentence holds in every model of `Γc`, and of `Γc` with
the step's closure, at every valuation sending K0 to a value, for every H, from the sort predicates'
own results and without `FnHyp`. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]

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

/-- None of the 15 reads a declaration or an alias. -/
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

/-! ## Function equations (29 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax230, U.ax238, U.ax237, U.ax236, U.ax235, U.ax242, U.ax241, U.ax244, U.ax243, U.ax240,
   U.ax239, U.ax217, U.ax216, U.ax229, U.ax228, U.ax225, U.ax224, U.ax227, U.ax226, U.ax232,
   U.ax231, U.ax234, U.ax233, U.ax221, U.ax220, U.ax223, U.ax222, U.ax219, U.ax218]

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

theorem nj117 : (trS U.ax117).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj123 : (trS U.ax123).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj126 : (trS U.ax126).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax117, U.ax123, U.ax126], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj117]; exact orTopBot_valid hD rfl
  · rw [nj123]; exact orTopBot_valid hD rfl
  · rw [nj126]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax118, U.ax119, U.ax120, U.ax121, U.ax122, U.ax124, U.ax125],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax118, U.ax119, U.ax120, U.ax121, U.ax122, U.ax124, U.ax125],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax127).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (127)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax127).pat := by
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
   U.ax16, U.ax17, U.ax18, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax78,
   U.ax79, U.ax80, U.ax82, U.ax83, U.ax84, U.ax106, U.ax107, U.ax109]

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

theorem idem_pattern : U.ax61.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax61).pat = (trAxiom [] [] U.ax61).pat := by decide +kernel

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
theorem idem_vars : (U.ax61.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax61.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax61.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 61 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax61).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax61.ax.sortVars U.ax61.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax61.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax61.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 168, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax168).pat = (trAxiom [] [] U.ax168).pat := by decide +kernel
theorem s166_pattern : U.ax168.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax168.ax.sortVars.map sortVarKey ++ freeOf [] U.ax168.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax168.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 168 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax168.ax.sortVars U.ax168.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax168).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax168.ax.sortVars U.ax168.ax.pattern = t at he ⊢
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
/-- **Sentence 168 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax168 (trS U.ax168).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The rules (157): W1 under `boolClosed`, the negation without it, and the sentence at values, for every H (by hand)

Sentence 157 (`go(X) => done requires #Not(X >Int 0)`) is read through `notAsCondition`: its left side
holds `\equals{Bool}(\not{Bool}(X >Int 0), true)`, Γ's item the condition `\equals{Bool}(X >Int 0,
false)`. The two denote one set where every element of Bool is `true`'s or `false`'s (`boolClosed`)
and no element is both (`boolDist`): `cond_iff`. `boolDist` is a consequence of the text's sentences
138, 133, 147, 49, 46 (`ruleAux`) with Int's G-nonempty item (`ruleSigAux`) and `ΓSig`
(`boolDist_from_text`, from `TieReqBool.boolLits_of_text_sig`). `boolClosed` is a fact of the builtin domain Bool that no
sentence of the text is known to state, and Γ of this text does not hold it (the definition reads
no confined sort, `readsConfined_c`).
- `rule_from_text_closed` (W1): Γ's rule item is a consequence of the sentence with `ruleAux`,
  `ruleSigAux`, `boolClosed` and `ΓSig`.
- `rule_not_from_text`: the same premises without `boolClosed` do not entail it (the countermodel
  `ClosedNeg157.J`, with a third element of Bool). Whether the whole text entails the item is open:
  `ClosedNeg157.J` is not shown a model of the text's other sentences.
- `rule157_at_values`: Γ entails sentence 157 at values, with no closure of Bool; `rule_w2_closed`,
  `rule_w2_closed_noprem`: in a model of Γ that satisfies `boolClosed` the sentence holds.
- `closed_model`: Γ with the step's closure has a model that satisfies `boolClosed`, for every H. -/

deriving instance DecidableEq for KoreAML.SortDecl

namespace Rules

/-! ### The rule's two forms -/

def gtName : String := "Lbl'Unds-GT-'Int'Unds'"
def tC : Kore.KSort := srt "GeneratedTopCell"
def xP : Kore.Pattern := ev "VarV0" (srt "Int")
def kP : Kore.Pattern := ev "VarV1" (srt "K")
def cP : Kore.Pattern := ev "VarV2" (srt "GeneratedCounterCell")
/-- `X >Int 0`. -/
def gtX : Kore.Pattern := ap gtName [xP, .dv (srt "Int") "0"]
/-- `t = lit` at Bool, in the top cell's sort. -/
def eqB (a : Kore.Pattern) (lit : String) : Kore.Pattern := .equals (srt "Bool") tC a (.dv (srt "Bool") lit)
/-- The configuration `<generatedTop> <k> inj{Exp,KItem}(t) ~> K </k> C </generatedTop>`. -/
def cfg (a : Kore.Pattern) : Kore.Pattern :=
  ap "Lbl'-LT-'generatedTop'-GT-'" [ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [injP "Exp" "KItem" a, kP]], cP]
/-- The rule's right side. -/
def rhs0 : Kore.Pattern := .and tC [cfg (ap "Lbldone" []), .top tC]
/-- `⌈R⌉`, the last conjunct of Γ's left side. -/
def ceilR : Kore.Pattern := .ceil tC tC rhs0
/-- Γ's left side: the term, no `requires`, the reading's condition `X >Int 0 = false`, `⌈R⌉`. -/
def L0 : Kore.Pattern := .and tC [cfg (ap "Lblgo" [xP]), .top tC, eqB gtX "false", ceilR]
/-- The text's left side: the term and `\not{Bool}(X >Int 0) = true`. -/
def Ltext0 : Kore.Pattern := .and tC [cfg (ap "Lblgo" [xP]), eqB (.not (srt "Bool") gtX) "true"]

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl
theorem p0_eq : p0 = .rewrites tC L0 rhs0 := by decide +kernel
theorem p0_parts : TieRuleLhs.rwParts p0 = some (tC, L0, rhs0) := by rw [p0_eq]; rfl

def fT0 : List VarKey := (freeOf [] (.rewrites tC Ltext0 rhs0)).eraseDups

/-- **Sentence 157 is the item of `\rewrites{C}(Ltext0, rhs0)` at the table of Γ's axiom** (kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rhs0) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT0 := by decide +kernel

/-- Sentence 157 is the item of the text's left side at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rhs0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- Γ's item of the rule is the item of Γ's left side at its table and its free variables. -/
theorem item_eq : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat =
    TieRuleLhs.itemAt (tableOf [] p0) (freeOf [] p0).eraseDups tC L0 rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC L0 rhs0
  rw [← p0_eq] at h
  exact h

/-! ### The two facts of Bool -/

/-- ΓDomains' item for the values `true` and `false`: no element is both. -/
noncomputable def boolDist (H : HookParams) : P :=
  ∼(den (cH H) (KCore.bool true) ⋀ den (cH H) (KCore.bool false))

theorem boolDist_mem (H : HookParams) : ΓDomains (cH H) (boolDist H) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool true, KCore.bool false, Srt.bool, (by decide +kernel : (distinctSorts c).contains Srt.bool = true),
    by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel,
    by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel, by decide, rfl⟩)))

theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = tr ⟨[], []⟩ (.dv (srt "Bool") "true") := by
  show den c (KCore.bool true) = _; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = tr ⟨[], []⟩ (.dv (srt "Bool") "false") := by
  show den c (KCore.bool false) = _; decide +kernel

/-- `boolClosed` of this text: every element of Bool is `true`'s or `false`'s. -/
theorem boolClosed_eq (H : HookParams) : boolClosed (cH H) =
    (inhOf (sortP "Bool") ⊆⊆
      (tr ⟨[], []⟩ (.dv (srt "Bool") "true") ⋁ tr ⟨[], []⟩ (.dv (srt "Bool") "false"))) := by
  show boolClosed c = _; decide +kernel

theorem bool_name (H : HookParams) : (cH H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **On Bool, `true`'s elements are those that are not `false`'s**: no element is both
(`boolDist`), and every element of Bool is one of them (`boolClosed`). -/
theorem true_iff_not_false (H : HookParams) (hD : DefOK I) (hdist : I ⊧ᴵ boolDist H)
    (hcl : I ⊧ᴵ boolClosed (cH H)) {σB : M} (hσB : ∀ a, I.evalSymb (.sort ("Sort" ++ "Bool")) a ↔ a = σB)
    (t : VarTable) (e : Valuation M) (b : M) (hb : Inh I σB b) :
    (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e b ↔
      ¬ (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e b := by
  rw [tr_dv, tr_dv]
  constructor
  · intro hT hF
    have h := hdist e b
    unfold boolDist at h
    rw [den_true, den_false, tr_dv, tr_dv, interpret_neg, interpret_conj] at h
    exact h ⟨hT, hF⟩
  · intro hF
    have h := hcl e b
    rw [boolClosed_eq, interp_included hD] at h
    have h' := h b ((interp_inhOf_of (S := sortP "Bool") hσB).mpr hb)
    rw [tr_dv, tr_dv, interpret_disj] at h'
    exact h'.resolve_right hF

theorem eqB_tr (t : VarTable) (p : Kore.Pattern) (lit : String) : tr ⟨t, []⟩ (eqB p lit) =
    sEquals (trSort t (srt "Bool")) (trSort t tC) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ (.dv (srt "Bool") lit)) := by
  unfold eqB; rw [tr]

/-- **The reading's condition and the text's denote one set**: `X >Int 0 = false` and
`\not{Bool}(X >Int 0) = true`, in a model of definedness and the signature with `boolDist` and
`boolClosed`. -/
theorem cond_iff [Inhabited M] (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hdist : I ⊧ᴵ boolDist H) (hcl : I ⊧ᴵ boolClosed (cH H)) (t : VarTable) (e : Valuation M) (a : M) :
    (tr ⟨t, []⟩ (eqB gtX "false")).interpret I e a ↔
      (tr ⟨t, []⟩ (eqB (.not (srt "Bool") gtX) "true")).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.bool < nRegSorts) (Nat.le_add_right _ _) : Srt.bool < nRegSorts + (cH H).sortNames.length)
  rw [bool_name] at hσB1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSB : ∀ b, (trSort t (srt "Bool")).interpret I e b ↔ b = σB := by rw [trSort_srt]; exact hσB1
  have hSC : ∀ b, (trSort t tC).interpret I e b ↔ b = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  have hnot : ∀ b, Inh I σB b → ((tr ⟨t, []⟩ (.not (srt "Bool") gtX)).interpret I e b ↔
      ¬ (tr ⟨t, []⟩ gtX).interpret I e b) := by
    intro b hb
    rw [tr, interp_sNot]
    exact ⟨fun h => h.1, fun h => ⟨h, (interp_inhOf_of hSB).mpr hb⟩⟩
  have hlit := fun b hb => true_iff_not_false H hD hdist hcl hσB1 t e b hb
  rw [eqB_tr, eqB_tr, interp_sEquals hD hc hSB hSC hσB2 hσ2, interp_sEquals hD hc hSB hSC hσB2 hσ2]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun b hb => by rw [hnot b hb, hlit b hb, h b hb]⟩
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun b hb => ?_⟩
    have h1 := h b hb
    rw [hnot b hb, hlit b hb] at h1
    exact ⟨fun hg => Classical.byContradiction fun hF => h1.mpr hF hg,
      fun hF => Classical.byContradiction fun hg => h1.mp hg hF⟩

/-- `⊤` of the top cell's sort holds of the elements a condition at that sort holds of. -/
theorem top_of_cond [Inhabited M] (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (t : VarTable) (e : Valuation M) (a : M) {p : Kore.Pattern} {lit : String}
    (h : (tr ⟨t, []⟩ (eqB p lit)).interpret I e a) : (tr ⟨t, []⟩ (.top tC)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.bool < nRegSorts) (Nat.le_add_right _ _) : Srt.bool < nRegSorts + (cH H).sortNames.length)
  rw [bool_name] at hσB1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSB : ∀ b, (trSort t (srt "Bool")).interpret I e b ↔ b = σB := by rw [trSort_srt]; exact hσB1
  have hSC : ∀ b, (trSort t tC).interpret I e b ↔ b = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  rw [eqB_tr, interp_sEquals hD hc hSB hSC hσB2 hσ2] at h
  rw [tr]
  exact (interp_sTop hD (by unfold tC; rw [trSort_srt]; rfl) a).mpr ((interp_inhOf_of hSC).mpr h.1)

/-- **Γ's left side of the rule is inside the text's**, in a model of definedness and the
signature with `boolDist` and `boolClosed`. -/
theorem left_sub [Inhabited M] (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hdist : I ⊧ᴵ boolDist H) (hcl : I ⊧ᴵ boolClosed (cH H)) (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ L0).interpret I e a) : (tr ⟨t, []⟩ Ltext0).interpret I e a := by
  unfold L0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact (cond_iff H hD hc hSig hdist hcl t e a).mp (h (eqB gtX "false") (by simp))

/-- **The text's left side with `⌈R⌉` is inside Γ's**, in a model of definedness and the signature
with `boolDist` and `boolClosed`. `⌈R⌉` is the hypothesis `hR`. -/
theorem left_sup [Inhabited M] (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hdist : I ⊧ᴵ boolDist H) (hcl : I ⊧ᴵ boolClosed (cH H)) (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ Ltext0).interpret I e a) (hR : (tr ⟨t, []⟩ ceilR).interpret I e a) :
    (tr ⟨t, []⟩ L0).interpret I e a := by
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have h1 := h (eqB (.not (srt "Bool") gtX) "true") (by simp)
  unfold L0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact top_of_cond H hD hc hSig t e a h1
  · exact (cond_iff H hD hc hSig hdist hcl t e a).mpr h1
  · exact hR

end

/-! ### The Bool literals from the text's sentences

The text writes no sentence about `\dv{SortBool{}}("true")` alone. It writes three sentences of
module INT-KORE over element variables and the functional sentences of `_==Int_` and `_=/=Int_`.
At an element n of Int, with both sort variables at Int: `n ==Int n` is one element of Bool among
Bool's and agrees with `true` on Bool; `n =/=Int n` likewise with `false`; and `false` does not
agree with `n ==Int n` on Bool. The lemma is
`TieReqBool.boolLits_of_text_sig`, on the patterns `TieReqBool` writes for the five sentences. -/

/-- **Each of the five sentences is the pattern `TieReqBool` writes for it** (kernel):
INT-KORE.eq-int-true-left (138), INT-KORE.neq-int-false-left (133), INT-KORE.eq-int-false-rigth
(147), and the functional sentences of `_==Int_` (49) and `_=/=Int_` (46). -/
theorem lit_sents :
    (trS U.ax138).pat = TieReqBool.sentPat TieReqBool.eqIntTrueLeftAx ∧
    (trS U.ax133).pat = TieReqBool.sentPat TieReqBool.neqIntFalseLeftAx ∧
    (trS U.ax147).pat = TieReqBool.sentPat TieReqBool.eqIntFalseRightAx ∧
    (trS U.ax49).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.eqIntName) ∧
    (trS U.ax46).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.neqIntName) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The other sentences of the text the statement reads. -/
noncomputable def ruleAux : List AxiomDecl := [U.ax138, U.ax133, U.ax147, U.ax49, U.ax46]

/-- The item of the text's signature the statement reads, which `ΓSig` does not hold: Int has an
element (G-nonempty of the declaration `hooked-sort SortInt{}`). -/
def ruleSigAux : List Item := [nonemptyItem ⟨"SortInt", [], true⟩]

theorem intDecl_mem : (⟨"SortInt", [], true⟩ : SortDecl) ∈ kore.sortDecls := by decide +kernel

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rw [List.mem_singleton.mp hit]
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, intDecl_mem, rfl⟩)))))

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := by
  show c.sortName Srt.int = _; decide +kernel

/-- **No element is both `true`'s and `false`'s** in an interpretation with definedness and the
signature that satisfies the five sentences and Int's G-nonempty item: `boolDist` from the text. -/
theorem boolDist_of_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hT : ∀ φ ∈ ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat), I ⊧ᴵ φ) : I ⊧ᴵ boolDist H := by
  intro e m
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hT' : ∀ φ ∈ [(trS U.ax138).pat, (trS U.ax133).pat, (trS U.ax147).pat, (trS U.ax49).pat, (trS U.ax46).pat,
      (nonemptyItem ⟨"SortInt", [], true⟩).pat], I ⊧ᴵ φ := hT
  obtain ⟨s1, s2, s3, s4, s5⟩ := lit_sents
  obtain ⟨σB, aF, aT, -, -, haf, hat, hne, -, -⟩ := TieReqBool.boolLits_of_text_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.int < nRegSorts) (Nat.le_add_right _ _) :
      Srt.int < nRegSorts + (cH H).sortNames.length) (int_name H)
    (hT' _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    (s1 ▸ hT' _ (.head _)) (s2 ▸ hT' _ (.tail _ (.head _))) (s3 ▸ hT' _ (.tail _ (.tail _ (.head _))))
    (s4 ▸ hT' _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (s5 ▸ hT' _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) [] e
  unfold boolDist
  rw [interpret_neg, interpret_conj, den_true, den_false]
  rintro ⟨h1, h2⟩
  exact hne (((haf m).mp h2).symm.trans ((hat m).mp h1))

/-- **The text entails `boolDist`**, for every H: from the five sentences, Int's G-nonempty item
and the signature. -/
theorem boolDist_from_text (H : HookParams) :
    TiePair.Texts (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat)) ∪ ΓSig (cH H) ⊧ boolDist H := by
  intro M _ I hI
  exact boolDist_of_text H (TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)) (fun φ hφ => hI φ (Or.inr hφ))
    fun φ hφ => hI φ (Or.inl (Or.inl hφ))

/-! ### W1 does not hold without `boolClosed`: the countermodel

An interpretation in which every sort holds every element, `_==Int_` and `_=/=Int_` decide the
equality of their two arguments into `true`'s element `tt` and `false`'s element `ff`, `_>Int_`
gives `ff`, every other symbol and literal gives the element `o`, and nothing has a successor.
Bool then holds `o`, which neither literal denotes: the complement of `X >Int 0` in Bool holds `o`
with `tt`, so the text's condition `\not{Bool}(X >Int 0) = true` fails everywhere and sentence 157
holds with an empty left side, while Γ's condition `X >Int 0 = false` holds and Γ's item asks a
successor of `o`. The sentences `ruleAux` say of the two literals only how `_==Int_` and `_=/=Int_`
meet them; none bounds Bool's elements. -/

namespace ClosedNeg157

inductive El where
  | d | i | c0 | c1 | c2 | n | gt | gt1 | eq | ne | dvT | dvF | tt | ff | o
  | eq1 (a : El)
  | ne1 (a : El)

instance : Inhabited El := ⟨.o⟩

def evS : KoreAML.Sym → Set El
  | .defined => fun m => m = .d
  | .inh => fun m => m = .i
  | .ceil => fun m => m = .c0
  | .next => fun m => m = .n
  | .dv lit => fun m => m = (if lit = "true" then El.dvT else if lit = "false" then El.dvF else El.o)
  | .symbol s => fun m => m = (if s = gtName then El.gt else if s = TieReqBool.eqIntName then El.eq
      else if s = TieReqBool.neqIntName then El.ne else El.o)
  | _ => fun m => m = .o

def evA : El → El → Set El
  | .d, _ => fun _ => True
  | .i, _ => fun _ => True
  | .c0, _ => fun m => m = .c1
  | .c1, _ => fun m => m = .c2
  | .c2, _ => fun _ => True
  | .n, _ => fun _ => False
  | .gt, _ => fun m => m = .gt1
  | .gt1, _ => fun m => m = .ff
  | .eq, a => fun m => m = .eq1 a
  | .eq1 a, b => fun m => (a = b ∧ m = .tt) ∨ (a ≠ b ∧ m = .ff)
  | .ne, a => fun m => m = .ne1 a
  | .ne1 a, b => fun m => (a = b ∧ m = .ff) ∨ (a ≠ b ∧ m = .tt)
  | .dvT, _ => fun m => m = .tt
  | .dvF, _ => fun m => m = .ff
  | _, _ => fun m => m = .o

/-- The interpretation. -/
def J : Interpretation KoreAML.Sym El := ⟨evS, evA⟩

theorem defOK_J : DefOK J := fun _ _ => ⟨.d, rfl, True.intro⟩
theorem inh_all (σ m : El) : Inh J σ m := ⟨.i, rfl, True.intro⟩
theorem isSort_all (σ : El) : IsSort J σ := ⟨.o, rfl, inh_all _ _⟩

theorem inhOf_of {S : P} {e : Valuation El} (h : ∃ σ, S.interpret J e σ) (m : El) : (inhOf S).interpret J e m :=
  interp_inhOf.mpr (h.imp fun σ hσ => ⟨hσ, inh_all σ m⟩)

theorem inhOf_sort (n : String) (e : Valuation El) (m : El) : (inhOf (sym (.sort n))).interpret J e m :=
  inhOf_of (S := sym (.sort n)) ⟨.o, (rfl : El.o = El.o)⟩ m
theorem inhOf_evar (x : EVar) (e : Valuation El) (m : El) : (inhOf (.evar x)).interpret J e m :=
  inhOf_of (S := .evar x) ⟨e.evalEvar x, (rfl : e.evalEvar x = e.evalEvar x)⟩ m

theorem sat_def (x : EVar) : J ⊧ᴵ @definedness KoreAML.Sym _ x := by
  intro e m
  simp only [definedness, Pattern.interpret]
  rintro ⟨a, ha⟩
  exact ha ⟨.d, _, rfl, rfl, True.intro⟩

theorem guarded_of {ws : List P} {φ : P} {e : Valuation El} {m : El} (h : φ.interpret J e m) :
    (guarded ws φ).interpret J e m := by
  cases ws with
  | nil => exact h
  | cons w ws => exact fun _ => h

theorem sat_ceilDef : J ⊧ᴵ ceilDefItem.pat := by
  intro e m
  unfold ceilDefItem
  dsimp only
  refine guarded_of ?_
  rw [interp_equal defOK_J]
  intro a
  constructor
  · intro _; exact inhOf_evar _ e a
  · intro _
    rw [interp_sCeil_raw]
    exact ⟨_, _, _, rfl, rfl, rfl, .c2, ⟨.c1, ⟨.c0, rfl, rfl⟩, rfl⟩, True.intro⟩

/-- **The interpretation satisfies the signature of every semantics.** -/
theorem sat_sig (s : Semantics) : J ⊧ᴵP ΓSig s := by
  intro φ hφ
  rcases hφ with hφ | ⟨lit, rfl⟩
  · rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · simp only [sigItems, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at hit
      rcases hit with ((rfl | ⟨s', hs, rfl⟩) | ⟨k, hk, rfl⟩) | rfl | rfl | rfl
      · exact sat_def _
      · intro e m
        show (sExists ⟨1⟩ (sym .sortSort) (sym (.sort ("Sort" ++ s.sortName s')) ≡ .evar ⟨1⟩)).interpret J e m
        rw [interp_sExists]
        refine ⟨.o, ?_, ?_⟩
        · rw [interp_member defOK_J]; exact inhOf_of (S := sym .sortSort) ⟨.o, (rfl : El.o = El.o)⟩ _
        · rw [interp_equal defOK_J]
          intro b
          rw [interp_evar]
          simp only [Function.update_same]
          exact Iff.rfl
      · obtain ⟨hd, xs, -, hw⟩ := symApp_head s k.name
        intro e m
        rw [symArityItem_of_symApp hw, interp_included defOK_J]
        intro a _
        exact inhOf_sort _ e a
      · intro e m
        unfold ceilArityItem
        dsimp only
        refine guarded_of ?_
        rw [interp_included defOK_J]
        intro a _
        exact inhOf_evar _ e a
      · exact sat_ceilDef
      · intro e m
        show (sNext (inhOf (sym (.sort ("Sort" ++ s.sortName topCellSort)))) ⊆⊆
          inhOf (sym (.sort ("Sort" ++ s.sortName topCellSort)))).interpret J e m
        rw [interp_included defOK_J]
        intro a _
        exact inhOf_sort _ e a
    · exact sat_def x
  · intro e m
    unfold dvArityItem
    dsimp only
    refine guarded_of ?_
    rw [interp_included defOK_J]
    intro a _
    exact inhOf_evar _ e a

/-! ### Patterns in the interpretation -/

/-- φ denotes the one element x. -/
def Sing (φ : P) (e : Valuation El) (x : El) : Prop := ∀ m, φ.interpret J e m ↔ m = x

section
variable {t : VarTable} {e : Valuation El}

theorem symb_iff (f : String) (m : El) : J.evalSymb (.symbol f) m ↔
    m = (if f = gtName then El.gt else if f = TieReqBool.eqIntName then El.eq
      else if f = TieReqBool.neqIntName then El.ne else El.o) := Iff.rfl

theorem symb_eq (m : El) : J.evalSymb (.symbol TieReqBool.eqIntName) m ↔ m = .eq := by
  rw [symb_iff, if_neg (show ¬ TieReqBool.eqIntName = gtName by decide), if_pos rfl]

theorem symb_ne (m : El) : J.evalSymb (.symbol TieReqBool.neqIntName) m ↔ m = .ne := by
  rw [symb_iff, if_neg (show ¬ TieReqBool.neqIntName = gtName by decide),
    if_neg (show ¬ TieReqBool.neqIntName = TieReqBool.eqIntName by decide), if_pos rfl]

theorem sing_symbol {f : String} (hf : f ≠ gtName) (hf1 : f ≠ TieReqBool.eqIntName)
    (hf2 : f ≠ TieReqBool.neqIntName) : Sing (sym (.symbol f)) e .o := fun m => by
  show J.evalSymb (.symbol f) m ↔ m = .o
  rw [symb_iff, if_neg hf, if_neg hf1, if_neg hf2]
theorem sing_sort (n : String) : Sing (sym (.sort n)) e .o := fun _ => Iff.rfl
theorem sing_evar (x : EVar) : Sing (.evar x) e (e.evalEvar x) := fun _ => Iff.rfl

/-- An application whose head denotes `o` denotes `o`. -/
theorem sing_app_o {φ ψ : P} {y : El} (h1 : Sing φ e .o) (h2 : Sing ψ e y) : Sing (φ ⬝ ψ) e .o := fun m => by
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    rw [(h1 a).mp ha] at hab
    exact hab
  · rintro rfl
    exact ⟨.o, y, (h1 _).mpr rfl, (h2 _).mpr rfl, rfl⟩

theorem tr_ev (n : String) (s : Kore.KSort) : tr ⟨t, []⟩ (ev n s) = .evar (t.ev (evarKey (evar n s))) := by
  unfold ev; rw [tr]

theorem sing_cfg {a : Kore.Pattern} (h : Sing (tr ⟨t, []⟩ a) e .o) : Sing (tr ⟨t, []⟩ (cfg a)) e .o := by
  unfold cfg ap kP cP
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_injP, appList, tr_ev]
  exact sing_app_o (sing_app_o (sing_symbol (by decide) (by decide) (by decide))
    (sing_app_o (sing_symbol (by decide) (by decide) (by decide))
      (sing_app_o (sing_app_o (sing_symbol (by decide) (by decide) (by decide))
        (sing_app_o (sing_app_o (sing_app_o (sing_symbol (by decide) (by decide) (by decide)) (sing_sort _))
          (sing_sort _)) h))
        (sing_evar _)))) (sing_evar _)

theorem sing_go : Sing (tr ⟨t, []⟩ (ap "Lblgo" [xP])) e .o := by
  unfold ap xP
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_ev]
  exact sing_app_o (sing_symbol (by decide) (by decide) (by decide)) (sing_evar _)

theorem sing_done : Sing (tr ⟨t, []⟩ (ap "Lbldone" [])) e .o := by
  unfold ap
  simp only [tr_app0, trArgs_nil]
  exact sing_symbol (by decide) (by decide) (by decide)

/-- `X >Int 0` denotes `false`'s element at every X. -/
theorem sing_gt : Sing (tr ⟨t, []⟩ gtX) e .ff := fun m => by
  unfold gtX ap xP
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_ev, tr_dv]
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    rw [interp_app] at ha
    obtain ⟨a', b', ha', -, hab'⟩ := ha
    have h1 : a' = .gt := ha'
    subst h1
    have h2 : a = .gt1 := hab'
    subst h2
    exact hab
  · rintro rfl
    exact ⟨.gt1, .o, interp_app.mpr ⟨.gt, _, rfl, rfl, rfl⟩, interp_app.mpr ⟨.o, .o, rfl, rfl, rfl⟩, rfl⟩

theorem sing_true : Sing (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) e .tt := fun m => by
  rw [tr_dv, interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    have h1 : a = .dvT := ha
    subst h1
    exact hab
  · rintro rfl
    exact ⟨.dvT, .o, rfl, rfl, rfl⟩

theorem sing_false : Sing (tr ⟨t, []⟩ (.dv (srt "Bool") "false")) e .ff := fun m => by
  rw [tr_dv, interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    have h1 : a = .dvF := ha
    subst h1
    exact hab
  · rintro rfl
    exact ⟨.dvF, .o, rfl, rfl, rfl⟩

theorem hS (n : String) : ∀ b, (trSort t (srt n)).interpret J e b ↔ b = .o := by
  rw [trSort_srt]; exact fun _ => Iff.rfl

theorem inh_srt (n : String) (m : El) : (inhOf (trSort t (srt n))).interpret J e m := by
  rw [trSort_srt]; exact inhOf_sort _ e m

theorem top_holds (m : El) : (tr ⟨t, []⟩ (.top tC)).interpret J e m := by
  rw [tr]
  refine (interp_sTop defOK_J (by unfold tC; rw [trSort_srt]; rfl) m).mpr ?_
  exact inh_srt _ m

theorem rhs_o : (tr ⟨t, []⟩ rhs0).interpret J e .o := by
  unfold rhs0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (sing_cfg sing_done _).mpr rfl
  · exact top_holds _

/-- **Γ's left side holds of `o`** at every valuation: `X >Int 0` and `false` denote one element. -/
theorem L0_o : (tr ⟨t, []⟩ L0).interpret J e .o := by
  unfold L0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (sing_cfg sing_go _).mpr rfl
  · exact top_holds _
  · rw [eqB_tr]
    exact (interp_sEquals defOK_J sat_ceilDef (hS _) (hS _) (isSort_all _) (isSort_all _) _).mpr
      ⟨inh_all _ _, fun a _ => (sing_gt a).trans (sing_false a).symm⟩
  · unfold ceilR
    rw [tr]
    exact (interp_sCeil defOK_J sat_ceilDef (hS _) (hS _) (isSort_all _) (isSort_all _)
      (fun a _ => inh_all _ a) _).mpr ⟨⟨.o, rhs_o⟩, inh_all _ _⟩

/-- **The text's left side holds of nothing**: `\not{Bool}(X >Int 0)` holds of `o`, an element of
Bool that `true` does not denote. -/
theorem Ltext0_empty (a : El) : ¬ (tr ⟨t, []⟩ Ltext0).interpret J e a := by
  intro h
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have h1 := h (eqB (.not (srt "Bool") gtX) "true") (by simp)
  rw [eqB_tr] at h1
  have h2 := ((interp_sEquals defOK_J sat_ceilDef (hS _) (hS _) (isSort_all _) (isSort_all _) a).mp h1).2
    .o (inh_all _ _)
  have h3 : (tr ⟨t, []⟩ (.not (srt "Bool") gtX)).interpret J e .o := by
    rw [tr, interp_sNot]
    exact ⟨fun hg => (by cases (sing_gt _).mp hg), inh_srt _ _⟩
  cases (sing_true _).mp (h2.mp h3)

/-- Nothing has a successor. -/
theorem next_empty (φ : P) (m : El) : ¬ (sNext φ).interpret J e m := by
  unfold sNext
  rw [interp_app]
  rintro ⟨a, b, ha, -, hab⟩
  have h1 : a = .n := ha
  subst h1
  exact hab

theorem tr_rw (C : Kore.KSort) (X r : Kore.Pattern) :
    tr ⟨t, []⟩ (.rewrites C X r) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ r) := by rw [tr]

end

/-! ### The sentences of the Bool literals in the interpretation -/

/-- An equality between sorts that denote one element each holds where its two sides denote the
same elements: every sort holds every element. -/
theorem sEq_iff {e : Valuation El} {S S' φ ψ : P} {σ σ' : El} (hS : ∀ a, S.interpret J e a ↔ a = σ)
    (hS' : ∀ a, S'.interpret J e a ↔ a = σ') (m : El) :
    (sEquals S S' φ ψ).interpret J e m ↔ ∀ a, (φ.interpret J e a ↔ ψ.interpret J e a) := by
  rw [interp_sEquals defOK_J sat_ceilDef hS hS' (isSort_all _) (isSort_all _)]
  exact ⟨fun h a => h.2 a (inh_all _ _), fun h => ⟨inh_all _ _, fun a _ => h a⟩⟩

/-- `K1 ==Int K2` denotes `tt` where the two are one element and `ff` where they are two. -/
theorem app34_eq (e : Valuation El) (m : El) : (TieReqBool.app34 TieReqBool.eqIntName).interpret J e m ↔
    (e.evalEvar ⟨3⟩ = e.evalEvar ⟨4⟩ ∧ m = .tt) ∨ (e.evalEvar ⟨3⟩ ≠ e.evalEvar ⟨4⟩ ∧ m = .ff) := by
  unfold TieReqBool.app34
  rw [interp_app]
  constructor
  · rintro ⟨f, y, hf, hy, hfy⟩
    rw [interp_app] at hf
    obtain ⟨g, x, hg, hx, hgx⟩ := hf
    have hg' : g = .eq := (symb_eq g).mp hg
    subst hg'
    have hf' : f = .eq1 x := hgx
    subst hf'
    have hx' : x = e.evalEvar ⟨3⟩ := hx
    have hy' : y = e.evalEvar ⟨4⟩ := hy
    subst hx' hy'
    exact hfy
  · intro h
    exact ⟨.eq1 (e.evalEvar ⟨3⟩), e.evalEvar ⟨4⟩,
      interp_app.mpr ⟨.eq, e.evalEvar ⟨3⟩, (symb_eq _).mpr rfl, rfl, rfl⟩, rfl, h⟩

/-- `K1 =/=Int K2` denotes `ff` where the two are one element and `tt` where they are two. -/
theorem app34_ne (e : Valuation El) (m : El) : (TieReqBool.app34 TieReqBool.neqIntName).interpret J e m ↔
    (e.evalEvar ⟨3⟩ = e.evalEvar ⟨4⟩ ∧ m = .ff) ∨ (e.evalEvar ⟨3⟩ ≠ e.evalEvar ⟨4⟩ ∧ m = .tt) := by
  unfold TieReqBool.app34
  rw [interp_app]
  constructor
  · rintro ⟨f, y, hf, hy, hfy⟩
    rw [interp_app] at hf
    obtain ⟨g, x, hg, hx, hgx⟩ := hf
    have hg' : g = .ne := (symb_ne g).mp hg
    subst hg'
    have hf' : f = .ne1 x := hgx
    subst hf'
    have hx' : x = e.evalEvar ⟨3⟩ := hx
    have hy' : y = e.evalEvar ⟨4⟩ := hy
    subst hx' hy'
    exact hfy
  · intro h
    exact ⟨.ne1 (e.evalEvar ⟨3⟩), e.evalEvar ⟨4⟩,
      interp_app.mpr ⟨.ne, e.evalEvar ⟨3⟩, (symb_ne _).mpr rfl, rfl, rfl⟩, rfl, h⟩

theorem litP_true {e : Valuation El} (m : El) : (TieReqBool.litP "true").interpret J e m ↔ m = .tt := by
  unfold TieReqBool.litP
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    have h1 : a = .dvT := ha
    subst h1
    exact hab
  · rintro rfl
    exact ⟨.dvT, .o, rfl, rfl, rfl⟩

theorem litP_false {e : Valuation El} (m : El) : (TieReqBool.litP "false").interpret J e m ↔ m = .ff := by
  unfold TieReqBool.litP
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    have h1 : a = .dvF := ha
    subst h1
    exact hab
  · rintro rfl
    exact ⟨.dvF, .o, rfl, rfl, rfl⟩

theorem eqR_one (x y : El) : ∃ v, ∀ m, ((x = y ∧ m = El.tt) ∨ (x ≠ y ∧ m = El.ff)) ↔ m = v := by
  by_cases h : x = y
  · exact ⟨.tt, fun m => ⟨fun hm => hm.elim (fun h1 => h1.2) (fun h1 => absurd h h1.1), fun hm => Or.inl ⟨h, hm⟩⟩⟩
  · exact ⟨.ff, fun m => ⟨fun hm => hm.elim (fun h1 => absurd h1.1 h) (fun h1 => h1.2), fun hm => Or.inr ⟨h, hm⟩⟩⟩

theorem neR_one (x y : El) : ∃ v, ∀ m, ((x = y ∧ m = El.ff) ∨ (x ≠ y ∧ m = El.tt)) ↔ m = v := by
  by_cases h : x = y
  · exact ⟨.ff, fun m => ⟨fun hm => hm.elim (fun h1 => h1.2) (fun h1 => absurd h h1.1), fun hm => Or.inl ⟨h, hm⟩⟩⟩
  · exact ⟨.tt, fun m => ⟨fun hm => hm.elim (fun h1 => absurd h1.1 h) (fun h1 => h1.2), fun hm => Or.inr ⟨h, hm⟩⟩⟩

/-- **A functional sentence of a symbol from two Ints to Bool holds** where the symbol applied to
two elements denotes one element. -/
theorem sat_fnl {f : String} {R : El → El → El → Prop}
    (happ : ∀ (e : Valuation El) (m : El),
      (TieReqBool.app34 f).interpret J e m ↔ R (e.evalEvar ⟨3⟩) (e.evalEvar ⟨4⟩) m)
    (hone : ∀ x y, ∃ v, ∀ m, R x y m ↔ m = v) : J ⊧ᴵ TieReqBool.sentPat (TieReqBool.fnlBoolAx f) := by
  intro e m
  rw [TieReqBool.fnlBool_shape, interpret_impl]
  intro _
  rw [interp_equal defOK_J]
  intro a
  refine ⟨fun _ => inhOf_evar _ e a, fun _ => ?_⟩
  obtain ⟨v, hv⟩ := hone (e.evalEvar ⟨3⟩) (e.evalEvar ⟨4⟩)
  rw [interp_sExists]
  refine ⟨v, ?_, ?_⟩
  · rw [interp_member defOK_J]
    exact inhOf_of (S := TieReqBool.boolP) ⟨.o, (rfl : El.o = El.o)⟩ _
  · refine (sEq_iff (S := TieReqBool.boolP) (S' := (.evar ⟨1⟩ : P)) (σ := .o) (fun _ => Iff.rfl)
      (fun _ => Iff.rfl) a).mpr fun b => ?_
    rw [happ, interp_evar]
    simp only [Function.update_same, Function.update_noteq (show (⟨3⟩ : EVar) ≠ ⟨2⟩ by decide),
      Function.update_noteq (show (⟨4⟩ : EVar) ≠ ⟨2⟩ by decide)]
    exact (hv b).symm

/-- **A simplification sentence holds** where its two sides hold the same at every valuation. -/
theorem sat_simp {L Rr : P} (h : ∀ (e : Valuation El) (a : El), L.interpret J e a ↔ Rr.interpret J e a) :
    J ⊧ᴵ (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: TieReqBool.g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩) L Rr) ≡ inhOf (.evar ⟨1⟩))) := by
  intro e m
  rw [interpret_impl]
  intro _
  rw [interp_equal defOK_J]
  intro a
  refine ⟨fun _ => inhOf_evar _ e a, fun _ => ?_⟩
  rw [interp_sImp]
  refine ⟨inhOf_evar _ e a, fun _ => ?_⟩
  exact (sEq_iff (S := (.evar ⟨2⟩ : P)) (S' := (.evar ⟨1⟩ : P)) (fun _ => Iff.rfl) (fun _ => Iff.rfl) a).mpr (h e)

/-- `\equals{SortInt{}, Q0}(K1, K2)` holds where K1 and K2 are one element. -/
theorem k12_iff (e : Valuation El) (a : El) :
    (sEquals TieReqBool.intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)).interpret J e a ↔
      e.evalEvar ⟨3⟩ = e.evalEvar ⟨4⟩ := by
  refine (sEq_iff (S := TieReqBool.intP) (S' := (.evar ⟨2⟩ : P)) (σ := .o) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) a).trans ⟨fun h => ?_, fun h b => ?_⟩
  · exact interp_evar.mp ((h (e.evalEvar ⟨3⟩)).mp (interp_evar.mpr rfl))
  · rw [interp_evar, interp_evar, h]

theorem top2 (e : Valuation El) (a : El) : (sTop (.evar ⟨2⟩)).interpret J e a :=
  (interp_sTop defOK_J rfl a).mpr (inhOf_evar _ e a)

/-- `(K1 ==Int K2) = true` holds where K1 and K2 are one element. -/
theorem eqTrue_iff (e : Valuation El) (a : El) :
    (sEquals TieReqBool.boolP (.evar ⟨2⟩) (TieReqBool.app34 TieReqBool.eqIntName)
      (TieReqBool.litP "true")).interpret J e a ↔ e.evalEvar ⟨3⟩ = e.evalEvar ⟨4⟩ := by
  refine (sEq_iff (S := TieReqBool.boolP) (S' := (.evar ⟨2⟩ : P)) (σ := .o) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) a).trans ⟨fun h => ?_, fun h b => ?_⟩
  · apply Classical.byContradiction
    intro hne
    cases (litP_true .ff).mp ((h .ff).mp ((app34_eq e .ff).mpr (Or.inr ⟨hne, rfl⟩)))
  · rw [app34_eq, litP_true]
    exact ⟨fun hb => hb.elim (fun h1 => h1.2) (fun h1 => absurd h h1.1), fun hb => Or.inl ⟨h, hb⟩⟩

/-- `(K1 =/=Int K2) = false` holds where K1 and K2 are one element. -/
theorem neFalse_iff (e : Valuation El) (a : El) :
    (sEquals TieReqBool.boolP (.evar ⟨2⟩) (TieReqBool.app34 TieReqBool.neqIntName)
      (TieReqBool.litP "false")).interpret J e a ↔ e.evalEvar ⟨3⟩ = e.evalEvar ⟨4⟩ := by
  refine (sEq_iff (S := TieReqBool.boolP) (S' := (.evar ⟨2⟩ : P)) (σ := .o) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) a).trans ⟨fun h => ?_, fun h b => ?_⟩
  · apply Classical.byContradiction
    intro hne
    cases (litP_false .tt).mp ((h .tt).mp ((app34_ne e .tt).mpr (Or.inr ⟨hne, rfl⟩)))
  · rw [app34_ne, litP_false]
    exact ⟨fun hb => hb.elim (fun h1 => h1.2) (fun h1 => absurd h h1.1), fun hb => Or.inl ⟨h, hb⟩⟩

/-- `false = (K1 ==Int K2)` holds where K1 and K2 are two elements. -/
theorem falseEq_iff (e : Valuation El) (a : El) :
    (sEquals TieReqBool.boolP (.evar ⟨2⟩) (TieReqBool.litP "false")
      (TieReqBool.app34 TieReqBool.eqIntName)).interpret J e a ↔ e.evalEvar ⟨3⟩ ≠ e.evalEvar ⟨4⟩ := by
  refine (sEq_iff (S := TieReqBool.boolP) (S' := (.evar ⟨2⟩ : P)) (σ := .o) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) a).trans ⟨fun h heq => ?_, fun h b => ?_⟩
  · cases (litP_false .tt).mp ((h .tt).mpr ((app34_eq e .tt).mpr (Or.inl ⟨heq, rfl⟩)))
  · rw [app34_eq, litP_false]
    exact ⟨fun hb => Or.inr ⟨h, hb⟩, fun hb => hb.elim (fun h1 => absurd h1.1 h) (fun h1 => h1.2)⟩

/-- INT-KORE.eq-int-true-left holds: both sides say that K1 and K2 are one element. -/
theorem sat_eqTrueLeft : J ⊧ᴵ TieReqBool.sentPat TieReqBool.eqIntTrueLeftAx := by
  rw [TieReqBool.simp_shape_tt]
  exact sat_simp fun e a => by
    rw [eqTrue_iff, interp_sAnd, k12_iff]
    exact ⟨fun h => ⟨h, top2 e a⟩, fun h => h.1⟩

/-- INT-KORE.neq-int-false-left holds: both sides say that K1 and K2 are one element. -/
theorem sat_neFalseLeft : J ⊧ᴵ TieReqBool.sentPat TieReqBool.neqIntFalseLeftAx := by
  rw [TieReqBool.simp_shape_nf]
  exact sat_simp fun e a => by
    rw [neFalse_iff, interp_sAnd, k12_iff]
    exact ⟨fun h => ⟨h, top2 e a⟩, fun h => h.1⟩

/-- INT-KORE.eq-int-false-rigth holds: both sides say that K1 and K2 are two elements. -/
theorem sat_eqFalseRight : J ⊧ᴵ TieReqBool.sentPat TieReqBool.eqIntFalseRightAx := by
  rw [TieReqBool.simp_shape_ff]
  exact sat_simp fun e a => by
    rw [falseEq_iff, interp_sAnd, interp_sNot, k12_iff]
    exact ⟨fun h => ⟨⟨h, inhOf_evar _ e a⟩, top2 e a⟩, fun h => h.1.1⟩

theorem sat_fnlEq : J ⊧ᴵ TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.eqIntName) :=
  sat_fnl (R := fun x y m => (x = y ∧ m = El.tt) ∨ (x ≠ y ∧ m = El.ff)) app34_eq eqR_one

theorem sat_fnlNe : J ⊧ᴵ TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.neqIntName) :=
  sat_fnl (R := fun x y m => (x = y ∧ m = El.ff) ∨ (x ≠ y ∧ m = El.tt)) app34_ne neR_one

/-- Int has an element. -/
theorem sat_intNonempty : J ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat := by
  intro e m
  show (notEqual (inhOf (sym (.sort "SortInt"))) ⊥ : P).interpret J e m
  rw [interp_notEqual defOK_J]
  intro h
  exact interpret_bottom.mp ((h .o).mp (inhOf_sort _ e .o))

/-! ### Sentence 157 and Γ's rule item in the interpretation -/

theorem free0 : (freeOf [] (.rewrites tC L0 rhs0)).eraseDups =
    [.evar "VarV0" (srt "Int"), .evar "VarV1" (srt "K"), .evar "VarV2" (srt "GeneratedCounterCell")] := by
  decide +kernel

/-- **The interpretation satisfies sentence 157**: its left side holds of nothing. -/
theorem text_holds : J ⊧ᴵ (trS U.ax157).pat := by
  rw [trS157]
  intro e m
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro _
  rw [interp_equal defOK_J]
  intro a
  rw [tr_rw]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun h => h.1, fun hi => ⟨hi, fun hl => absurd hl (Ltext0_empty a)⟩⟩

/-- **The interpretation does not satisfy Γ's item of the rule**: at every valuation its left side
holds of `o`, which has no successor. -/
theorem item_fails : ¬ (J ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat) := by
  intro h
  rw [p0_eq, TieRuleLhs.trAxiom_rule] at h
  have h1 := h ⟨fun _ => .o, fun _ _ => False⟩ .o
  unfold TieRuleLhs.itemAt at h1
  rw [interpret_impl, free0] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl <;>
      exact (interp_guard_evar defOK_J).mpr (inh_srt _ _))
  rw [interp_equal defOK_J] at h2
  have h3 := (h2 .o).mpr (inh_srt _ _)
  rw [tr_rw] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  exact next_empty _ _ (h3.2 L0_o)

/-- **The interpretation satisfies the premises of W1 without `boolClosed`**, for every H:
sentence 157, the sentences `ruleAux`, the signature item `ruleSigAux` and `ΓSig`. -/
theorem sat_pre (H : HookParams) : J ⊧ᴵP (TiePair.Texts ((trS U.ax157).pat ::
    (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H)) := by
  intro φ hφ
  rcases hφ with (hφ | ⟨x, rfl⟩) | hφ
  · have hφ' : φ ∈ [(trS U.ax157).pat, (trS U.ax138).pat, (trS U.ax133).pat, (trS U.ax147).pat,
        (trS U.ax49).pat, (trS U.ax46).pat, (nonemptyItem ⟨"SortInt", [], true⟩).pat] := hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ'
    obtain ⟨s1, s2, s3, s4, s5⟩ := lit_sents
    rcases hφ' with h | h | h | h | h | h | h
    · rw [h]; exact text_holds
    · rw [h, s1]; exact sat_eqTrueLeft
    · rw [h, s2]; exact sat_neFalseLeft
    · rw [h, s3]; exact sat_eqFalseRight
    · rw [h, s4]; exact sat_fnlEq
    · rw [h, s5]; exact sat_fnlNe
    · rw [h]; exact sat_intNonempty
  · exact sat_def x
  · exact sat_sig (cH H) φ hφ

/-- **In the interpretation Bool has an element that neither literal denotes**, and the literals
denote two elements. -/
theorem bool_other (e : Valuation El) :
    (inhOf (sortP "Bool")).interpret J e .o ∧
    ¬ (tr ⟨[], []⟩ (.dv (srt "Bool") "true")).interpret J e .o ∧
    ¬ (tr ⟨[], []⟩ (.dv (srt "Bool") "false")).interpret J e .o ∧
    ¬ ∃ a, (tr ⟨[], []⟩ (.dv (srt "Bool") "true")).interpret J e a ∧
      (tr ⟨[], []⟩ (.dv (srt "Bool") "false")).interpret J e a :=
  ⟨inhOf_sort _ e _, fun h => (by cases (sing_true _).mp h), fun h => (by cases (sing_false _).mp h),
    fun ⟨a, h1, h2⟩ => (by cases ((sing_true a).mp h1).symm.trans ((sing_false a).mp h2))⟩

end ClosedNeg157

/-! ### W1 and W2 -/

/-- The rule sentence of the text. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

/-- The rule sentence is the class rewrite rule of the account. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

/-- **W1 for the rule, under `boolClosed`**: Γ's one rule item is a consequence of sentence 157
with the text's sentences `ruleAux`, Int's G-nonempty item, `boolClosed` and the signature, for
every H. `boolClosed` is the one premise that is no sentence or signature item of the text; no
item of `ΓDomains` is among the premises. -/
theorem rule_from_text_closed (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
      TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat) ++
        [boolClosed (cH H)])) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  refine ⟨U.ax157, List.mem_singleton_self _, ?_⟩
  intro M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hT : ∀ φ ∈ (trS U.ax157).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat) ++
      [boolClosed (cH H)]), I ⊧ᴵ φ := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hdist : I ⊧ᴵ boolDist H := boolDist_of_text H hD hSig
    fun φ hφ => hT φ (List.mem_cons_of_mem _ (List.mem_append_left _ hφ))
  have hcl : I ⊧ᴵ boolClosed (cH H) :=
    hT _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  rw [List.mem_singleton.mp hit]
  exact TieRuleLhs.rule_w1 hD p0_parts rule_text0 fT_free0 (hT _ (List.mem_cons_self ..))
    fun e _ _ a ha => left_sub H hD hc hSig hdist hcl _ e a ha

/-- **W1 for the rule does not hold without `boolClosed`**, for every H: sentence 157 with the
text's sentences `ruleAux`, Int's G-nonempty item and the signature does not entail Γ's rule item.
The interpretation `ClosedNeg157.J` satisfies these premises (`ClosedNeg157.sat_pre`) and not the
item (`ClosedNeg157.item_fails`); in it Bool has an element neither literal denotes
(`ClosedNeg157.bool_other`). -/
theorem rule_not_from_text (H : HookParams) :
    ¬ ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
      TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪
        ΓSig (cH H) ⊧ it.pat := by
  intro h
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  obtain ⟨ad, had, hent⟩ := h _ hit
  have had' : ad = U.ax157 := List.mem_singleton.mp had
  subst had'
  exact ClosedNeg157.item_fails (hent (I := ClosedNeg157.J) (ClosedNeg157.sat_pre H))

/-- **W2 for the rule, with the guard, under `boolClosed`**: in a model of Γ that satisfies
`boolClosed`, sentence 157 holds at each valuation at which `⌈R⌉` holds wherever the text's left
side holds, for every H. -/
theorem rule_w2_closed (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) (e : Valuation M)
    (hR : ∀ a, (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a → (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a)
    (m : M) : (trS U.ax157).pat.interpret I e m := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hdist : I ⊧ᴵ boolDist H := sat_dom hI (boolDist_mem H)
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [item_eq] at hg
  rw [trS157]
  exact TieRuleLhs.lhs_entails hD free_sub hg e m fun _ a ha =>
    left_sup H hD hc hSig hdist hcl _ e a ha (hR a ha)

/-! ### The right side is defined in every model of Γ -/

/-- The generators of the right side's term: the top cell, the `k` cell, `kseq`, the injection of
Exp into KItem and the constructor `done`. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp"),
   ("Exp", .ctor ⟨"Lbldone", [], "Exp"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- The right side's term is built of the text's variables and of those generators (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT0 (cfg (ap "Lbldone" [])) "GeneratedTopCell" = true := by
  decide +kernel

theorem sorts_numbered : Srt.bool < nRegSorts + c.sortNames.length ∧ topCellSort < nRegSorts + c.sortNames.length ∧
    c.sortName Srt.bool = "Bool" ∧ c.sortName topCellSort = "GeneratedTopCell" := by decide +kernel

/-- **The premise `⌈R⌉` of `rule_w2_closed` holds in every model of Γ**, for every H: where the
guards of the text's variables hold, the right side holds one element, by the Cons-Fun items of its
generators, so `⌈R⌉` holds of every element of the top cell's sort, which the `requires` of the
text's left side (an `\equals` at that sort) keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT0, (guardOf (tableOf [] p0) k).interpret I e m) (a : M)
    (ha : (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have ha' : (tr ⟨tableOf [] p0, []⟩ (.and tC [cfg (ap "Lblgo" [xP]),
      .equals (srt "Bool") (srt "GeneratedTopCell") (.not (srt "Bool") gtX) (.dv (srt "Bool") "true")])).interpret I e a := ha
  have h1 := (interp_and (List.cons_ne_nil _ _)).mp ha' _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact TieRuleCutG.rightDefined_top hI sorts_numbered.2.1
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from sorts_numbered.2.2.2)
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg a
    (TieRuleCutG.equals_top hI sorts_numbered.1 (show (cH H).sortName Srt.bool = "Bool" from sorts_numbered.2.2.1)
      sorts_numbered.2.1 (show (cH H).sortName topCellSort = "GeneratedTopCell" from sorts_numbered.2.2.2) h1)

/-- **W2 for the rule, under `boolClosed`, without the premise `⌈R⌉`**: sentence 157 holds in
every model of Γ that satisfies `boolClosed`, for every H. -/
theorem rule_w2_closed_noprem (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) : I ⊧ᴵ (trS U.ax157).pat := by
  intro e m
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hdist : I ⊧ᴵ boolDist H := sat_dom hI (boolDist_mem H)
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [item_eq] at hg
  rw [trS157]
  exact TieRuleLhs.lhs_entails hD free_sub hg e m fun hgs a ha =>
    left_sup H hD hc hSig hdist hcl _ e a ha (right_defined H hI e m hgs a ha)

/-! ### Sentence 157 at values, with no closure of Bool -/

/-- Γ's variable X. -/
def xX : Kore.EVar := KoreAML.evar "VarV0" (srt "Int")

/-- The sentence's variable `X` is free in it and has the index of Γ's variable at the argument of
`go`. -/
theorem x_index : KoreAML.VarKey.evar "VarX" (srt "Int") ∈ (freeOf [] U.ax157.ax.pattern).eraseDups ∧
    (tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev (.evar "VarX" (srt "Int")) =
      (tableOf [] p0).ev (evarKey xX) := by decide +kernel

/-- `X >Int 0` as a library term over the one variable. -/
def gtT : Term := .app intGt [.var 0, .dv Srt.int (.int 0)]
def gtVars : LibEv.Vars := [("VarV0", Srt.int)]

theorem gt_kore_all : (fun H : HookParams => LibEv.kore (cH H) gtVars gtT) = fun _ => gtX := by kernel_rfl
theorem gt_srt (H : HookParams) : LibEv.srt? (cH H) gtVars gtT = some Srt.bool := by
  simp only [gtT, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem gt_key (H : HookParams) : LibEv.vkey (cH H) gtVars 0 = evarKey xX := by
  show LibEv.vkey c gtVars 0 = _; decide +kernel
theorem shapesOK_c : c.shapesOK = true := by decide +kernel
theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : srt (c.sortName S) = srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      srt (c.sortName S) = srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
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

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **`X >Int 0` at a value of X holds nothing, or is `true`'s element, or is `false`'s**: a term
over the variable, a domain value and an interpreted symbol, of sort Bool, denotes the element of
its value or nothing (`LibEv.den_val`: the graph of `>Int` in `ΓDomains`), and a value of Bool is
`true` or `false`. -/
theorem gt_at_value [Inhabited M] (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) {v : GroundTerm}
    (hv : (cH H).sortOf v = some Srt.int)
    (hden : (den (cH H) v).interpret I e (e.evalEvar ((tableOf [] p0).ev (evarKey xX)))) :
    (∀ m, ¬ (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e m) ∨
      ∃ b : Bool, ∀ m, (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e m ↔ (den (cH H) (KCore.bool b)).interpret I e m := by
  obtain ⟨a0, ha0, -⟩ := den_single hI hv e
  have hlen : gtVars.length = 1 := rfl
  have hσ : ∀ i p, gtVars[i]? = some p → ∃ w, [(0, v)].lookup i = some w ∧ (cH H).sortOf w = some p.2 := by
    intro i p hp
    have hi : i < gtVars.length := (List.getElem?_eq_some_iff.mp hp).1
    rw [hlen] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    obtain rfl : ("VarV0", Srt.int) = p := Option.some.inj hp
    exact ⟨v, rfl, hv⟩
  have hag : ∀ i w, i < gtVars.length → [(0, v)].lookup i = some w →
      ∀ m, m = e.evalEvar ((tableOf [] p0).ev (LibEv.vkey (cH H) gtVars i)) ↔ (den (cH H) w).interpret I e m := by
    intro i w hi hw m
    rw [hlen] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    cases (show some v = some w from hw)
    rw [gt_key, ha0, (ha0 _).mp hden]
  obtain ⟨hval, hsrt⟩ := LibEv.den_val (coreOKH H) hI hσ hag gtT (gt_srt H)
  rw [congrFun gt_kore_all H] at hval
  cases hw : LibEv.val (cH H) [(0, v)] gtT with
  | none =>
    left; intro m h
    rw [hval, hw] at h; exact h
  | some w =>
    have hws := hsrt w hw
    rw [Semantics.sortOf_withHooks _ _ noRaw] at hws
    obtain ⟨b, rfl⟩ := shape_bool shapesOK_c hws
    exact Or.inr ⟨b, fun m => by rw [hval, hw]; rfl⟩

/-- **At a value of X, the text's left side with `⌈R⌉` is inside Γ's**, in every model of Γ, with
no closure of Bool. `X >Int 0` is `true`'s element, `false`'s, or holds nothing (`gt_at_value`).
The text's condition says `true` holds exactly the elements of Bool outside `X >Int 0`. Where
`X >Int 0` holds nothing, that set holds `false`'s element, which is not `true`'s. Where it is
`true`'s element, that set does not hold it. Where it is `false`'s, Γ's condition
`X >Int 0 = false` holds. -/
theorem left_sup_values [Inhabited M] (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M)
    (hat : AtValues (cH H) I e U.ax157.ax) (a : M)
    (h : (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a) (hR : (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ L0).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSC : ∀ b, (trSort (tableOf [] p0) tC).interpret I e b ↔ b = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  obtain ⟨σB, aF, aT, hSB, hσB, haf, haT, hne, hif, hit⟩ :=
    TieReqBool.boolTwo hD hSig hDom (sortOf_false H) (sortOf_true H) ((den_false H).trans (tr_dv ..))
      ((den_true H).trans (tr_dv ..)) (tableOf [] p0) e
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarX" (srt "Int") x_index.1
  rw [x_index.2] at hden
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have h1 := h (eqB (.not (srt "Bool") gtX) "true") (by simp)
  have h1' := h1
  rw [eqB_tr, interp_sEquals hD hc hSB hSC hσB hσ2] at h1'
  obtain ⟨ha, hn⟩ := h1'
  have hnot : ∀ b, Inh I σB b → ((tr ⟨tableOf [] p0, []⟩ (.not (srt "Bool") gtX)).interpret I e b ↔
      ¬ (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e b) := by
    intro b hb
    rw [tr, interp_sNot]
    exact ⟨fun h => h.1, fun h => ⟨h, (interp_inhOf_of hSB).mpr hb⟩⟩
  have hcond : (tr ⟨tableOf [] p0, []⟩ (eqB gtX "false")).interpret I e a := by
    rw [eqB_tr, interp_sEquals hD hc hSB hSC hσB hσ2]
    refine ⟨ha, fun b hb => ?_⟩
    rcases gt_at_value H hI e hv hden with hemp | ⟨bb, hbb⟩
    · exact absurd ((haT aF).mp ((hn aF hif).mp ((hnot aF hif).mpr (hemp aF)))) hne
    · cases bb with
      | true =>
        have hg : (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e aT := by
          rw [hbb aT, den_true H, tr_dv, ← tr_dv (t := tableOf [] p0)]; exact (haT aT).mpr rfl
        exact absurd hg ((hnot aT hit).mp ((hn aT hit).mpr ((haT aT).mpr rfl)))
      | false => rw [hbb b, den_false H, tr_dv, tr_dv]
  unfold L0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact top_of_cond H hD hc hSig _ e a h1
  · exact hcond
  · exact hR

end

/-- **Sentence 157 is entailed at values** (`EntailsAtValues`), for every H, with no closure of
Bool: at a value of X the text's left side is inside Γ's (`left_sup_values`, with `⌈R⌉` by
`right_defined`), and Γ's item gives the sentence. -/
theorem rule157_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat := by
  intro M _ I hI e hat m
  have hD := defOK hI
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [item_eq] at hg
  rw [trS157]
  exact TieRuleLhs.lhs_entails hD free_sub hg e m fun hgs a ha =>
    left_sup_values H hI e hat a ha (right_defined H hI e m hgs a ha)

/-! ### The premise `boolClosed` does not empty the statements -/


def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  (FnFacts.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)
    (show c.params.all (fun k => !k.raw) = true by decide +kernel)).obligations (openDecidedH H)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

theorem litSort_bool (H : HookParams) : (cH H).litSort Srt.bool = true :=
  (by decide +kernel : c.litSort Srt.bool = true)

open Faithful.Model in
/-- **Γ with the step's closure has a model that satisfies `boolClosed`, for every H**: the value
model at its own step, whose elements of Bool are the two literals' (`boolClosed_modelClT`). -/
theorem closed_model (H : HookParams) : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γ (cH H) ∪ Γstep (cH H))) ∧ (I ⊧ᴵ boolClosed (cH H)) := by
  have h := coreOKH H
  have h' := Semantics.coreOK_iff_ex.mp h
  have hf := fnHypH H
  have hm : HypModelCore (cH H) := hypModel_of_fnHyp h hf
  exact ⟨_, inferInstance, _, stdI_V_model_coreEx hm (fnModel_of_fnHyp h hf).2
    (fun fn hfn cl hcl =>
      have hcp := (Semantics.sortedOKClEx_parts (Semantics.sortedOKClEx_of_sortedOKEx
        (Semantics.coreOKEx_parts h').1)).2.1 fn hfn cl hcl
      ⟨hcp.1, (Semantics.clausePlainOpenEx_parts hcp.2).1, (Semantics.clausePlainOpenEx_parts hcp.2).2.1⟩)
    (clausePreDecided_of_fnHyp h hf) (clausePostDecided_of_fnHypCEx h' hf) hf.2.2.2.2.2,
    boolClosed_modelClT hm (litSort_bool H)⟩

end Rules

end KCore.TieE3MlReqNot

#check @KCore.TieE3MlReqNot.noRaw
#check @KCore.TieE3MlReqNot.readsConfined_c
#check @KCore.TieE3MlReqNot.userAxioms_eq
#check @KCore.TieE3MlReqNot.coreOK
#check @KCore.TieE3MlReqNot.wf_defn
#check @KCore.TieE3MlReqNot.account
#check @KCore.TieE3MlReqNot.account_sizes
#check @KCore.TieE3MlReqNot.account_classes
#check @KCore.TieE3MlReqNot.account_absent
#check @KCore.TieE3MlReqNot.absent_closed
#check @KCore.TieE3MlReqNot.absent_proj_below_c
#check @KCore.TieE3MlReqNot.absent_proj_below
#check @KCore.TieE3MlReqNot.lists_in_account
#check @KCore.TieE3MlReqNot.attrs_agree
#check @KCore.TieE3MlReqNot.sig_origin
#check @KCore.TieE3MlReqNot.decls_entailed
#check @KCore.TieE3MlReqNot.consistent
#check @KCore.TieE3MlReqNot.fnFun_indices
#check @KCore.TieE3MlReqNot.fnFun_account
#check @KCore.TieE3MlReqNot.fnFun_checked
#check @KCore.TieE3MlReqNot.fnFun_trS
#check @KCore.TieE3MlReqNot.fnFun_at_values
#check @KCore.TieE3MlReqNot.fnFun_at_values_step
#check @KCore.TieE3MlReqNot.fn_shape
#check @KCore.TieE3MlReqNot.fns_account
#check @KCore.TieE3MlReqNot.fns_entailed
#check @KCore.TieE3MlReqNot.fns_from_text
#check @KCore.TieE3MlReqNot.fn_prios
#check @KCore.TieE3MlReqNot.nojunk_trivial_entailed
#check @KCore.TieE3MlReqNot.nojunk_items_entailed
#check @KCore.TieE3MlReqNot.nojunk_kitem_entailed
#check @KCore.TieE3MlReqNot.cons_entailed
#check @KCore.TieE3MlReqNot.idem_refuted
#check @KCore.TieE3MlReqNot.lib166
#check @KCore.TieE3MlReqNot.lib166_at_values
#check @KCore.TieE3MlReqNot.owed_rules
#check @KCore.TieE3MlReqNot.owed_clauses
#check @KCore.TieE3MlReqNot.openDecidedH
#check @KCore.TieE3MlReqNot.Rules.rules_account
#check @KCore.TieE3MlReqNot.Rules.rule_from_text_closed
#check @KCore.TieE3MlReqNot.Rules.ruleSigAux_text
#check @KCore.TieE3MlReqNot.Rules.rule157_at_values
#check @KCore.TieE3MlReqNot.Rules.rule_not_from_text
#check @KCore.TieE3MlReqNot.Rules.rule_text0
#check @KCore.TieE3MlReqNot.Rules.true_iff_not_false
#check @KCore.TieE3MlReqNot.Rules.cond_iff
#check @KCore.TieE3MlReqNot.Rules.left_sub
#check @KCore.TieE3MlReqNot.Rules.left_sup
#check @KCore.TieE3MlReqNot.Rules.lit_sents
#check @KCore.TieE3MlReqNot.Rules.boolDist_of_text
#check @KCore.TieE3MlReqNot.Rules.boolDist_from_text
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_sig
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.L0_o
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.Ltext0_empty
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_fnl
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_simp
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.text_holds
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.item_fails
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_pre
#check @KCore.TieE3MlReqNot.Rules.ClosedNeg157.bool_other
#check @KCore.TieE3MlReqNot.Rules.rule_w2_closed
#check @KCore.TieE3MlReqNot.Rules.right_defined
#check @KCore.TieE3MlReqNot.Rules.rule_w2_closed_noprem
#check @KCore.TieE3MlReqNot.Rules.gt_at_value
#check @KCore.TieE3MlReqNot.Rules.left_sup_values
#check @KCore.TieE3MlReqNot.Rules.closed_model
#print axioms KCore.TieE3MlReqNot.noRaw
#print axioms KCore.TieE3MlReqNot.readsConfined_c
#print axioms KCore.TieE3MlReqNot.userAxioms_eq
#print axioms KCore.TieE3MlReqNot.coreOK
#print axioms KCore.TieE3MlReqNot.wf_defn
#print axioms KCore.TieE3MlReqNot.account
#print axioms KCore.TieE3MlReqNot.account_sizes
#print axioms KCore.TieE3MlReqNot.account_classes
#print axioms KCore.TieE3MlReqNot.account_absent
#print axioms KCore.TieE3MlReqNot.absent_closed
#print axioms KCore.TieE3MlReqNot.absent_proj_below_c
#print axioms KCore.TieE3MlReqNot.absent_proj_below
#print axioms KCore.TieE3MlReqNot.lists_in_account
#print axioms KCore.TieE3MlReqNot.attrs_agree
#print axioms KCore.TieE3MlReqNot.sig_origin
#print axioms KCore.TieE3MlReqNot.decls_entailed
#print axioms KCore.TieE3MlReqNot.consistent
#print axioms KCore.TieE3MlReqNot.fnFun_indices
#print axioms KCore.TieE3MlReqNot.fnFun_account
#print axioms KCore.TieE3MlReqNot.fnFun_checked
#print axioms KCore.TieE3MlReqNot.fnFun_trS
#print axioms KCore.TieE3MlReqNot.fnFun_at_values
#print axioms KCore.TieE3MlReqNot.fnFun_at_values_step
#print axioms KCore.TieE3MlReqNot.fn_shape
#print axioms KCore.TieE3MlReqNot.fns_account
#print axioms KCore.TieE3MlReqNot.fns_entailed
#print axioms KCore.TieE3MlReqNot.fns_from_text
#print axioms KCore.TieE3MlReqNot.fn_prios
#print axioms KCore.TieE3MlReqNot.nojunk_trivial_entailed
#print axioms KCore.TieE3MlReqNot.nojunk_items_entailed
#print axioms KCore.TieE3MlReqNot.nojunk_kitem_entailed
#print axioms KCore.TieE3MlReqNot.cons_entailed
#print axioms KCore.TieE3MlReqNot.idem_refuted
#print axioms KCore.TieE3MlReqNot.lib166
#print axioms KCore.TieE3MlReqNot.lib166_at_values
#print axioms KCore.TieE3MlReqNot.owed_rules
#print axioms KCore.TieE3MlReqNot.owed_clauses
#print axioms KCore.TieE3MlReqNot.openDecidedH
#print axioms KCore.TieE3MlReqNot.Rules.rules_account
#print axioms KCore.TieE3MlReqNot.Rules.rule_from_text_closed
#print axioms KCore.TieE3MlReqNot.Rules.ruleSigAux_text
#print axioms KCore.TieE3MlReqNot.Rules.rule157_at_values
#print axioms KCore.TieE3MlReqNot.Rules.rule_not_from_text
#print axioms KCore.TieE3MlReqNot.Rules.rule_text0
#print axioms KCore.TieE3MlReqNot.Rules.true_iff_not_false
#print axioms KCore.TieE3MlReqNot.Rules.cond_iff
#print axioms KCore.TieE3MlReqNot.Rules.left_sub
#print axioms KCore.TieE3MlReqNot.Rules.left_sup
#print axioms KCore.TieE3MlReqNot.Rules.lit_sents
#print axioms KCore.TieE3MlReqNot.Rules.boolDist_of_text
#print axioms KCore.TieE3MlReqNot.Rules.boolDist_from_text
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_sig
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.L0_o
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.Ltext0_empty
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_fnl
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_simp
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.text_holds
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.item_fails
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.sat_pre
#print axioms KCore.TieE3MlReqNot.Rules.ClosedNeg157.bool_other
#print axioms KCore.TieE3MlReqNot.Rules.rule_w2_closed
#print axioms KCore.TieE3MlReqNot.Rules.right_defined
#print axioms KCore.TieE3MlReqNot.Rules.rule_w2_closed_noprem
#print axioms KCore.TieE3MlReqNot.Rules.gt_at_value
#print axioms KCore.TieE3MlReqNot.Rules.left_sup_values
#print axioms KCore.TieE3MlReqNot.Rules.closed_model
