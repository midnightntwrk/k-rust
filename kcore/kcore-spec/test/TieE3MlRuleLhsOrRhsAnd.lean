/-
  The tie (C14) on `f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore`, the kompiled text of construct fixture e3-ml-rule-lhs-or-rhs-and
  (`test/constructs/fixtures/e3-ml-rule-lhs-or-rhs-and`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-rule-lhs-or-rhs-and`, its rules section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlRuleLhsOrRhsAnd.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 151 sentences of the user module E3-ML-RULE-LHS-OR-RHS-AND, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 209 items of `sigItems c` is a declaration's item of the text or a
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
  - Rewrite rules (104), by hand, in the section `The rules` (`RuleW1`): each of Γ's rule items is a
    consequence of its text sentence with the text's signature (`ΓSig`), `RuleW1.ruleText` in
    `ruleItems`' order (`RuleW1.rule_from_text_sig`, W1, every H; `RuleW1.rules_account`). `ΓSig`
    holds the items of the text's declarations or surplus ones, the sort constant of a registry sort
    or the arity of a hooked symbol that the text does not declare at that shape (`sig_origin`), and
    the arity of every literal (`dvArityAll`). Two limits, argued and not proved: that a surplus
    item of a name the text declares with sort parameters adds no consequence in the text's symbols;
    and that `dvArityAll` at a literal no axiom of the text writes, no item of the text, adds none
    either. The section's other headline statements (its comment says what each states):
    `RuleW1.p0_eq`, `RuleW1.right_read`, `RuleW1.rule_text0`, `RuleW1.and_var_top`,
    `RuleW1.un_arity`, `RuleW1.left_of`, `RuleW1.left_c`, `RuleW1.left_d`, `RuleW1.right_iff`.
  - Constructor sentences (37): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (47): Γ with it has no model (`idem_refuted`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (22);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlRuleLhsOrRhsAnd

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore" module "E3-ML-RULE-LHS-OR-RHS-AND"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-RULE-LHS-OR-RHS-AND")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 151 := by decide +kernel

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
      128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]),
   ("rewrite rule", [104]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 55, 59, 62, 65, 85, 86]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 63, 66]),
   ("distinctness", [56, 57, 58, 60, 61, 64]),
   ("no junk", [93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]),
   ("function functional", [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 38, 42, 50, 51, 52, 53, 54, 68, 84, 87, 88, 89, 90, 91]),
   ("collection law", [39, 40, 41, 43, 44, 45, 46, 48, 49]),
   ("library", [105, 153]),
   ("set idempotence", [47]),
   ("set-variable lemma", [154]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 37, 67, 92, 106, 107, 108, 109, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
      150, 151, 152])]

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
    [("function equation", 29), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 10), ("subsort", 15), ("injectivity", 6), ("distinctness", 6), ("no junk", 11), ("function functional", 15), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 22)] := by
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
  [(139, "Bool"), (140, "Exp"), (141, "GeneratedCounterCell"), (142, "GeneratedCounterCellOpt"),
   (143, "GeneratedTopCell"), (144, "GeneratedTopCellFragment"), (145, "Int"), (146, "K"),
   (147, "KCell"), (148, "KCellOpt"), (149, "KItem"), (150, "List"), (151, "Map"), (152, "Set")]

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
  [(14, "subsort"), (55, "constructor functional"), (56, "distinctness"), (57, "distinctness"),
   (58, "distinctness"), (59, "constructor functional"), (60, "distinctness"),
   (61, "distinctness"), (62, "constructor functional"), (63, "injectivity"), (64, "distinctness"),
   (65, "constructor functional"), (66, "injectivity"), (70, "function functional"),
   (94, "no junk"), (103, "no junk"), (104, "rewrite rule"), (109, "no direction"),
   (112, "function equation"), (113, "function equation"), (140, "no direction"),
   (154, "set-variable lemma")]

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

theorem sig_sizes : (sigItems c).length = 209 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 89, 59, 4, 26) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 25).all inSigItems = true := by decide +kernel
theorem declsE_25 : (((declItems).drop 25).take 25).all inSigItems = true := by decide +kernel
theorem declsE_50 : ((declItems).drop 50).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    declsE_50

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
def fnFunIdx : List Nat := [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]

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
  [U.ax124, U.ax132, U.ax131, U.ax130, U.ax129, U.ax136, U.ax135, U.ax138, U.ax137, U.ax134,
   U.ax133, U.ax111, U.ax110, U.ax123, U.ax122, U.ax119, U.ax118, U.ax121, U.ax120, U.ax126,
   U.ax125, U.ax128, U.ax127, U.ax115, U.ax114, U.ax117, U.ax116, U.ax113, U.ax112]

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

theorem nj93 : (trS U.ax93).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj99 : (trS U.ax99).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj102 : (trS U.ax102).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax93, U.ax99, U.ax102], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj93]; exact orTopBot_valid hD rfl
  · rw [nj99]; exact orTopBot_valid hD rfl
  · rw [nj102]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
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
   U.ax16, U.ax17, U.ax18, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax55,
   U.ax56, U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax62, U.ax63, U.ax64, U.ax65, U.ax66, U.ax85,
   U.ax86]

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

theorem idem_pattern : U.ax47.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax47).pat = (trAxiom [] [] U.ax47).pat := by decide +kernel

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
theorem idem_vars : (U.ax47.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax47.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax47.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 47 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax47).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax47.ax.sortVars U.ax47.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax47.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax47.ax.pattern).eraseDups,
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


/-! ## The rules (104): W1 per disjunct over the signature, for every H (by hand)

Γ reads sentence 104, `c(X) #Or d(X) => X #And a()` in the `k` cell, through `orSplit` with
`andTermsCut` on each rule read: one rule per disjunct, `c(X) => X` and `d(X) => X`, each with the
cut's condition `X ∈ a()` in its right side (the variable form) and `⌈right⌉` more on its left
side (`p0_eq`, `p1_eq`). Sentence 104 is the item of the text's two sides at the table of Γ's
axioms (`rule_text0`, kernel; the two axioms have one table). Where X has an element of Exp, Γ's
right side `C[X] ∧ ⊤ ∧ X ∈ a()` and the text's `C[X ∧ a()] ∧ ⊤` denote one set, in a model of
definedness and the signature (`right_iff`); each of Γ's left sides is inside the text's
(`left_c`, `left_d`): `\or{SortExp{}}` holds the elements of its disjuncts that are in Exp, and the
arity of `c` and of `d` (`ΓSig`) puts them there (`un_arity`). So each of Γ's two rule items is a
consequence of the one sentence and the signature (`rule_from_text_sig`, W1, every H). -/

namespace RuleW1

theorem names : c.symName 385 = "Lbla" ∧ c.symName 387 = "Lblc" ∧ c.symName 388 = "Lbld" ∧
    c.sortName 32 = "Exp" := by decide +kernel

/-! ### The rule's forms -/

def tC : Kore.KSort := srt "GeneratedTopCell"
def eS : Kore.KSort := srt "Exp"
/-- The variable X of the rule. -/
def v : Kore.EVar := evar "VarV0" eS
def xP : Kore.Pattern := .var (.evar v)
def kP : Kore.Pattern := ev "VarV1" (srt "K")
def cP : Kore.Pattern := ev "VarV2" (srt "GeneratedCounterCell")
def aP : Kore.Pattern := ap "Lbla" []
def cX : Kore.Pattern := ap "Lblc" [xP]
def dX : Kore.Pattern := ap "Lbld" [xP]

/-- The context of the `k` cell's first item at the sort Exp:
`<generatedTop>(<k>(kseq(inj{Exp, KItem}(·), K)), C)`. -/
def K : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [eS, srt "KItem"] [] .hole []) [kP]) []) [cP]

/-- The text's left side: `c(X) ∨ d(X)` in the cell. -/
def Ltext : Kore.Pattern := .and tC [K.fill (.or eS [cX, dX]), .top tC]
/-- The text's right side: `X ∧ a()` in the cell. -/
def rtext : Kore.Pattern := .and tC [K.fill (.and eS [xP, aP]), .top tC]
/-- Γ's right side, of both rules: X in the cell, with the cut's condition `X ∈ a()`. -/
def rhs0 : Kore.Pattern := .and tC [K.fill xP, .top tC, .in eS tC xP aP]
/-- `⌈right⌉`, the last conjunct of Γ's left sides. -/
def ceilR : Kore.Pattern := .ceil tC tC rhs0
/-- Γ's left side of the rule of the disjunct `d`: the term, no `requires`, `⌈right⌉`. -/
def Lof (d : Kore.Pattern) : Kore.Pattern := .and tC [K.fill d, .top tC, ceilR]

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
/-- Γ's axioms of the two rules. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
noncomputable def p1 : Kore.Pattern := prioRuleK c r1
theorem ruleItems_eq : ruleItems c =
    [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by kernel_rfl
/-- **Γ's axioms of the two rules** (kernel): one per disjunct, with one right side. -/
theorem p0_eq : p0 = .rewrites tC (Lof cX) rhs0 := by decide +kernel
theorem p1_eq : p1 = .rewrites tC (Lof dX) rhs0 := by decide +kernel
/-- **The right side of each rule read is the cut's** (`ruleRight`, kernel). -/
theorem right_read : ruleRight c r0 = rhs0 ∧ ruleRight c r1 = rhs0 := by decide +kernel

/-- The table of Γ's axioms. -/
noncomputable def tbl : VarTable := tableOf [] p0
theorem tbl1_eq : tableOf [] p1 = tbl := by decide +kernel

def fT : List VarKey := (freeOf [] (.rewrites tC Ltext rtext)).eraseDups

/-- **Sentence 104 is the item of `\rewrites{C}(Ltext, rtext)` at the table of Γ's axioms**
(kernel). -/
theorem rule_text0 :
    TiePair.renSeq (TieRuleLhs.itemAt tbl fT tC Ltext rtext) [] = some (trS U.ax104).pat := by
  decide +kernel
theorem free_sub0 : ∀ k ∈ fT, k ∈ (freeOf [] p0).eraseDups := by decide +kernel
theorem free_sub1 : ∀ k ∈ fT, k ∈ (freeOf [] p1).eraseDups := by decide +kernel
theorem free_sup0 : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT := by decide +kernel
theorem free_sup1 : ∀ k ∈ (freeOf [] p1).eraseDups, k ∈ fT := by decide +kernel
theorem v_free : evarKey v ∈ fT := by decide +kernel

theorem trS104 : (trS U.ax104).pat = TieRuleLhs.itemAt tbl fT tC Ltext rtext := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- Γ's items of the rules are the items of Γ's sides at the table and their free variables. -/
theorem item_eq0 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat =
    TieRuleLhs.itemAt tbl (freeOf [] p0).eraseDups tC (Lof cX) rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC (Lof cX) rhs0
  rw [← p0_eq] at h
  exact h
theorem item_eq1 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩).pat =
    TieRuleLhs.itemAt tbl (freeOf [] p1).eraseDups tC (Lof dX) rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC (Lof dX) rhs0
  rw [← p1_eq, tbl1_eq] at h
  exact h

theorem exp_name (H : HookParams) : (cH H).sortName 32 = "Exp" := names.2.2.2
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-! ### A rule item, pointwise -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

theorem tr_rw104 (t : VarTable) (C : Kore.KSort) (L r : Kore.Pattern) :
    tr ⟨t, []⟩ (.rewrites C L r) = sRewrites (trSort t C) (tr ⟨t, []⟩ L) (tr ⟨t, []⟩ r) := by rw [tr]

/-- A rule item that holds gives, where its guards hold, a successor in its right side to each
element of its left side that is in the rule's sort. -/
theorem item_elim104 (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
    (h : I ⊧ᴵ TieRuleLhs.itemAt t f C L r) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ f, (guardOf t k).interpret I e m) (a : M)
    (ha : (inhOf (trSort t C)).interpret I e a) (hl : (tr ⟨t, []⟩ L).interpret I e a) :
    (sNext (tr ⟨t, []⟩ r)).interpret I e a := by
  have h1 := h e m
  unfold TieRuleLhs.itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg k hk)
  rw [interp_equal hD] at h2
  have h3 := (h2 a).mpr ha
  rw [tr_rw104] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  exact h3.2 hl

/-- A rule item holds at a valuation where, under its guards, each element of its left side in
the rule's sort has a successor in its right side. -/
theorem item_intro104 (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
    (e : Valuation M) (m : M)
    (h : (∀ k ∈ f, (guardOf t k).interpret I e m) → ∀ a, (inhOf (trSort t C)).interpret I e a →
      (tr ⟨t, []⟩ L).interpret I e a → (sNext (tr ⟨t, []⟩ r)).interpret I e a) :
    (TieRuleLhs.itemAt t f C L r).interpret I e m := by
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ f, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  rw [interp_equal hD]
  intro a
  rw [tr_rw104]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun hf => hf.1, fun ha => ⟨ha, h hg' a ha⟩⟩

/-- The next-step operator is monotone. -/
theorem next_mono104 {φ ψ : P} {e : Valuation M} {a : M} (h : ∀ b, φ.interpret I e b → ψ.interpret I e b) :
    (sNext φ).interpret I e a → (sNext ψ).interpret I e a := by
  unfold sNext
  rw [interp_app, interp_app]
  rintro ⟨x, b, hx, hb, hxb⟩
  exact ⟨x, b, hx, h b hb, hxb⟩

/-- An application context at a disjunction: each element is one of the context at a disjunct. -/
theorem fill_or104 {s φ ψ : P} {e : Valuation M} : ∀ (C : CutCtx) (m : M),
    (C.fill (sOr s φ ψ)).interpret I e m → (C.fill φ).interpret I e m ∨ (C.fill ψ).interpret I e m
  | .hole, _, hm => (interp_sOr.mp hm).2
  | .fn C χ, m, hm => by
    obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
    rcases fill_or104 C a ha with h | h
    · exact .inl (interp_app.mpr ⟨a, b, h, hb, hab⟩)
    · exact .inr (interp_app.mpr ⟨a, b, h, hb, hab⟩)
  | .arg χ C, m, hm => by
    obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
    rcases fill_or104 C b hb with h | h
    · exact .inl (interp_app.mpr ⟨a, b, ha, h, hab⟩)
    · exact .inr (interp_app.mpr ⟨a, b, ha, h, hab⟩)

/-- **The variable form of the cut, with a conjunct inside the sort**: `\and{C}(K[V], E,
\in{S,C}(V, u))` is `\and{C}(K[\and{S}(V, u)], E)` where V has an element of S and every element
of E is in C. -/
theorem and_var_top [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (v : Kore.EVar) (u E : Kore.Pattern) (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hv : Inh I σ (e.evalEvar (ctx.vars.ev (evarKey v))))
    (hE : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u])).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E])).interpret I e m := by
  have hand : tr ctx (.and S [.var (.evar v), u]) =
      sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u) := by simp only [tr, trAndList]
  have hfillv : tr ctx (K.fill (.var (.evar v))) =
      (K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v))) := by
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hl : tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u]) =
      sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v)))) (sAnd (tr ctx E)
        (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) := by
    simp only [tr, trAndList]
    rw [hfillv]
  have hr : tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E]) =
      sAnd ((K.toCut ctx).fill (sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK, hand]
  rw [hl, hr, interp_sAnd, interp_sAnd, interp_sAnd, CutCtx.fill_evar_and,
    mem_iff_cut hD hc hS hC hσ hσ' _ hv]
  constructor
  · rintro ⟨hCx, hEm, hu, -⟩; exact ⟨⟨hu, hCx⟩, hEm⟩
  · rintro ⟨⟨hu, hCx⟩, hEm⟩; exact ⟨hCx, hEm, hu, hE m hEm⟩

end

/-! ### The arity of `c` and `d` -/

/-- The signatures of `c` and `d`. -/
def kc : CtorSig := ⟨387, [32], 32⟩
def kd : CtorSig := ⟨388, [32], 32⟩

theorem kc_mem : kc ∈ kernelSyms c := by decide +kernel
theorem kd_mem : kd ∈ kernelSyms c := by decide +kernel
theorem noInst_c : instDecode? (c.symName kc.name) = none := by decide +kernel
theorem noInst_d : instDecode? (c.symName kd.name) = none := by decide +kernel

kernel_rfl sigItems_withHooks104 : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

kernel_rfl cX_eq : cX = symApp c kc.name [xP]
kernel_rfl dX_eq : dX = symApp c kd.name [xP]

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **The arity of a symbol of one argument from Exp to Exp, from `ΓSig`**: what it builds from
an element of Exp is in Exp. -/
theorem un_arity [Inhabited M] (k : CtorSig) (hk : k ∈ kernelSyms c) (hni : instDecode? (c.symName k.name) = none)
    (hargs : k.args = [32]) (hres : k.result = 32) (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {e : Valuation M} {a : M} (ha : (symHead c k.name).interpret I e a)
    {b0 m : M} (h0 : InS I "Exp" b0) (hm : AppE I a [b0] m) : InS I "Exp" m := by
  have hit : I ⊧ᴵ (symArityItem c k).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity hk, rfl⟩))
  rw [symArityItem_noInst (k := k) hni] at hit
  rw [symHead_noInst (c := c) (f := k.name) hni] at ha
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  have hn : c.sortName 32 = "Exp" := names.2.2.2
  rw [hres, hn] at hinc
  apply (inS_iff (I := I) (s := "Exp") (a := m) KoreAML.val0).mp
  apply hinc
  rw [interp_appList]
  refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [b0], ?_, hm⟩
  simp only [hargs, List.map_cons, List.map_nil, trSort_srt, hn]
  exact .cons ((inS_iff _).mpr h0) .nil

/-- Such a symbol at a pattern whose elements are in Exp is in Exp. -/
theorem un_inh [Inhabited M] (k : CtorSig) (hk : k ∈ kernelSyms c) (hni : instDecode? (c.symName k.name) = none)
    (hargs : k.args = [32]) (hres : k.result = 32) (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Exp" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c k.name [p])).interpret I e m) :
    (inhOf (trSort t eS)).interpret I e m := by
  rw [tr_symApp, trArgs_appList, interp_appList] at h
  obtain ⟨a, ha, bs, hbs, hm⟩ := h
  simp only [List.map_cons, List.map_nil] at hbs
  cases hbs with
  | cons hb0 hbs =>
    cases hbs
    unfold eS
    rw [trSort_srt]
    exact (inS_iff _).mpr (un_arity k hk hni hargs hres hD hS ha (hp _ hb0) hm)

/-- The guard of X puts its value in Exp. -/
theorem x_inh [Inhabited M] (hD : DefOK I) {t : VarTable} {e : Valuation M} {m0 : M}
    (hg : (guardOf t (evarKey v)).interpret I e m0)
    (b : M) (h : (tr ⟨t, []⟩ xP).interpret I e b) : InS I "Exp" b := by
  have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
  unfold xP at h
  simp only [tr] at h
  rw [interp_evar] at h
  rw [h]
  have : v.sort = KoreAML.srt "Exp" := rfl
  rw [this, trSort_srt] at h1
  exact (inS_iff _).mp h1

/-! ### The inclusions -/

/-- **Γ's left side of the rule of a disjunct is inside the text's**, the disjunct's elements in
Exp: its first conjunct is inside the cell at the disjunction, and its conjunct `⌈right⌉` is not
asked. -/
theorem left_of {t : VarTable} {e : Valuation M} {d : Kore.Pattern}
    (hor : ∀ a, (tr ⟨t, []⟩ d).interpret I e a → (tr ⟨t, []⟩ (.or eS [cX, dX])).interpret I e a)
    (a : M) (h : (tr ⟨t, []⟩ (Lof d)).interpret I e a) : (tr ⟨t, []⟩ Ltext).interpret I e a := by
  unfold Lof at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact TieRuleLhs.tr_fill_mono ⟨t, []⟩ K rfl hor a (h _ (List.mem_cons_self ..))
  · exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **Γ's left side of the rule of `c` is inside the text's**, where X's guard holds. -/
theorem left_c [Inhabited M] (hD : DefOK I) (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {m0 : M}
    (hg : (guardOf t (evarKey v)).interpret I e m0)
    (a : M) (h : (tr ⟨t, []⟩ (Lof cX)).interpret I e a) : (tr ⟨t, []⟩ Ltext).interpret I e a :=
  left_of (TieRuleLhs.sub_or_left fun a' h' => by
    rw [cX_eq] at h'
    exact un_inh kc kc_mem noInst_c rfl rfl hD hS (fun b hb => x_inh hD hg b hb) a' h') a h

/-- **Γ's left side of the rule of `d` is inside the text's**, where X's guard holds. -/
theorem left_d [Inhabited M] (hD : DefOK I) (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {m0 : M}
    (hg : (guardOf t (evarKey v)).interpret I e m0)
    (a : M) (h : (tr ⟨t, []⟩ (Lof dX)).interpret I e a) : (tr ⟨t, []⟩ Ltext).interpret I e a :=
  left_of (TieRuleLhs.sub_or_right fun a' h' => by
    rw [dX_eq] at h'
    exact un_inh kd kd_mem noInst_d rfl rfl hD hS (fun b hb => x_inh hD hg b hb) a' h') a h

/-- **The cut's statement at each rule read**: where X's guard holds, Γ's right side `C[X] ∧ ⊤ ∧
X ∈ a()` and the text's `C[X ∧ a()] ∧ ⊤` denote one set, in a model of definedness and the
signature. -/
theorem right_iff [Inhabited M] (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    {t : VarTable} {e : Valuation M} {m0 : M} (hg : (guardOf t (evarKey v)).interpret I e m0) (m : M) :
    (tr ⟨t, []⟩ rhs0).interpret I e m ↔ (tr ⟨t, []⟩ rtext).interpret I e m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σE, hσE1, hσE2⟩ := TieRhs.sortSing_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
  rw [exp_name] at hσE1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSE : ∀ x, (trSort t eS).interpret I e x ↔ x = σE := by unfold eS; rw [trSort_srt]; exact hσE1
  have hSC : ∀ x, (trSort t tC).interpret I e x ↔ x = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  have hv : Inh I σE (e.evalEvar (t.ev (evarKey v))) := by
    have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
    rw [show v.sort = eS from rfl] at h1
    exact (interp_inhOf_of hSE).mp h1
  exact and_var_top hD hc ⟨t, []⟩ K rfl eS tC v aP (.top tC) e hSE hSC hσE2 hσ2 hv
    (fun x hx => by
      rw [tr] at hx
      exact (interp_inhOf_of hSC).mp ((interp_sTop hD (by unfold tC; rw [trSort_srt]; rfl) x).mp hx)) m

end

/-! ### W1, per disjunct -/

/-- Γ's item of a rule whose left side is inside the text's is a consequence of sentence 104 and
the signature. -/
theorem item_of_sentence (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hT : I ⊧ᴵ (trS U.ax104).pat) {L' : Kore.Pattern} {fG : List VarKey} (hfG : ∀ k ∈ fT, k ∈ fG)
    (hL : ∀ (e : Valuation M) (m0 : M), (guardOf tbl (evarKey v)).interpret I e m0 →
      ∀ a, (tr ⟨tbl, []⟩ L').interpret I e a → (tr ⟨tbl, []⟩ Ltext).interpret I e a) :
    I ⊧ᴵ TieRuleLhs.itemAt tbl fG tC L' rhs0 := by
  rw [trS104] at hT
  intro e m
  refine item_intro104 hD e m fun hg a ha hl => ?_
  have hgv := hg _ (hfG _ v_free)
  exact next_mono104 (fun b hb => (right_iff H hD hc hSig hgv b).mpr hb)
    (item_elim104 hD hT e m (fun k hk => hg k (hfG k hk)) a ha (hL e m hgv a hl))

/-- The text sentences of Γ's rules: the one sentence, of which each of Γ's two rule items (one per
disjunct) is a consequence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax104]

theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

/-- **W1 per disjunct, over the signature, and the converse for `ruleItems`**: each of Γ's two
rule items is a consequence of sentence 104 and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  refine ⟨U.ax104, List.mem_cons_self, ?_⟩
  intro M _ I hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hS : I ⊧ᴵP ΓSig c := fun φ hφ => hSig φ (by
    unfold ΓSig at hφ ⊢; rw [sigItems_withHooks104]; exact hφ)
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inr ⟨x, rfl⟩))
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  have hT : I ⊧ᴵ (trS U.ax104).pat := hI _ (Or.inl (Or.inl ⟨trS U.ax104, List.mem_singleton_self _, rfl⟩))
  rcases List.mem_cons.mp hit with rfl | hit
  · rw [item_eq0]
    exact item_of_sentence H hD hc hSig hT free_sub0 fun e m0 hg a ha => left_c hD hS hg a ha
  · rw [List.mem_singleton.mp hit, item_eq1]
    exact item_of_sentence H hD hc hSig hT free_sub1 fun e m0 hg a ha => left_d hD hS hg a ha

end RuleW1

end KCore.TieE3MlRuleLhsOrRhsAnd

#check @KCore.TieE3MlRuleLhsOrRhsAnd.noRaw
#check @KCore.TieE3MlRuleLhsOrRhsAnd.readsConfined_c
#check @KCore.TieE3MlRuleLhsOrRhsAnd.userAxioms_eq
#check @KCore.TieE3MlRuleLhsOrRhsAnd.coreOK
#check @KCore.TieE3MlRuleLhsOrRhsAnd.wf_defn
#check @KCore.TieE3MlRuleLhsOrRhsAnd.account
#check @KCore.TieE3MlRuleLhsOrRhsAnd.account_sizes
#check @KCore.TieE3MlRuleLhsOrRhsAnd.account_classes
#check @KCore.TieE3MlRuleLhsOrRhsAnd.account_absent
#check @KCore.TieE3MlRuleLhsOrRhsAnd.absent_closed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.absent_proj_below_c
#check @KCore.TieE3MlRuleLhsOrRhsAnd.absent_proj_below
#check @KCore.TieE3MlRuleLhsOrRhsAnd.lists_in_account
#check @KCore.TieE3MlRuleLhsOrRhsAnd.attrs_agree
#check @KCore.TieE3MlRuleLhsOrRhsAnd.sig_origin
#check @KCore.TieE3MlRuleLhsOrRhsAnd.decls_entailed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.consistent
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_indices
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_account
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_checked
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_trS
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_at_values
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_at_values_step
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fn_shape
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fns_account
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fns_entailed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fns_from_text
#check @KCore.TieE3MlRuleLhsOrRhsAnd.fn_prios
#check @KCore.TieE3MlRuleLhsOrRhsAnd.nojunk_trivial_entailed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.nojunk_items_entailed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.nojunk_kitem_entailed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.cons_entailed
#check @KCore.TieE3MlRuleLhsOrRhsAnd.idem_refuted
#check @KCore.TieE3MlRuleLhsOrRhsAnd.owed_rules
#check @KCore.TieE3MlRuleLhsOrRhsAnd.owed_clauses
#check @KCore.TieE3MlRuleLhsOrRhsAnd.openDecidedH
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.rules_account
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.rule_from_text_sig
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.p0_eq
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.right_read
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.rule_text0
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.and_var_top
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.un_arity
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.left_of
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.left_c
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.left_d
#check @KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.right_iff
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.noRaw
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.readsConfined_c
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.userAxioms_eq
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.coreOK
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.wf_defn
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.account
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.account_sizes
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.account_classes
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.account_absent
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.absent_closed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.absent_proj_below_c
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.absent_proj_below
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.lists_in_account
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.attrs_agree
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.sig_origin
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.decls_entailed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.consistent
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_indices
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_account
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_checked
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_trS
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_at_values
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fnFun_at_values_step
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fn_shape
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fns_account
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fns_entailed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fns_from_text
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.fn_prios
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.nojunk_trivial_entailed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.nojunk_items_entailed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.nojunk_kitem_entailed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.cons_entailed
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.idem_refuted
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.owed_rules
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.owed_clauses
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.openDecidedH
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.rules_account
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.rule_from_text_sig
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.p0_eq
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.right_read
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.rule_text0
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.and_var_top
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.un_arity
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.left_of
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.left_c
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.left_d
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd.RuleW1.right_iff
