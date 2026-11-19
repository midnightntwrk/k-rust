/-
  The tie (C14) on `f2-examples/e3-setvar-rewrite.kompile.kore`, the kompiled text of construct fixture e3-setvar-rewrite
  (`test/constructs/fixtures/e3-setvar-rewrite`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-setvar-rewrite`, except the rule's section and the empty list
  `uncovered`, written by hand (tiegen leaves sentence 104 uncovered); run from the package root: `lake env lean -j1 test/TieE3SetvarRewrite.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 151 sentences of the user module E3-SETVAR-REWRITE, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 209 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes
    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's
    condition (`owed_rules`, `owed_clauses`), so `Γc` with the step's closure has a model for every
    H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (37): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (47): Γ with it has no model (`idem_refuted`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  - Rewrite rule (1), written by hand: sentence 104, `c(@S, @S) => d(@S)` in the `k` cell, holds
    a set variable, and Γ's item of the rule read from it has one element variable per occurrence,
    the right one bound by `\exists` and a member of one of the left ones. Γ's item (with the
    premise `⌈rhs ∧ ens⌉`) is a consequence of the sentence with Γ's signature, for every H
    (`rule_from_text_sig`, `ruleText` in `ruleItems`' order): the item writes the membership with
    `\in`, which the sentence does not hold, so the premise set is the sentence with `ΓSig` (the
    sorts and `\ceil`'s definition; no rule's item), not the sentence alone as in the ties tiegen
    writes (`rule_from_text`). `rule_prios`: the priority the sentence states is the rule's.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (22);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3SetvarRewrite

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-setvar-rewrite.kompile.kore"
definition_of defn from "f2-examples/e3-setvar-rewrite.kompile.kore"
user_axioms U from "f2-examples/e3-setvar-rewrite.kompile.kore" module "E3-SETVAR-REWRITE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-SETVAR-REWRITE")

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

/-- **`Γc` with the step's closure has a model, for every H.** -/
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

/-! ## The rule (1 sentence): W1 over the signature

Sentence 104, `c(@S, @S) => d(@S)` in the `k` cell, holds a set variable; Γ's item of the rule the
reader reads has one element variable per occurrence, the right one bound by `\exists` and a member
of one of the left ones. Γ's item is a consequence of the sentence at the set of the two left
elements (`SvCtx.atSet_iff`, the direction of `setvar_rewrite_singleton` from the sentence to its
instances at elements). The item writes the membership with `\in`, which the sentence does not
hold, so the consequence is over the sentence with Γ's signature (`ΓSig`: the sorts, and
`\ceil`'s definition), not over the sentence alone; `ΓSig` holds no rule's item. -/

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax104]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

namespace SvR

/-- Two contexts of one shape whose side patterns have the same elements, the first's read at `e`
and the second's at `e'`. -/
inductive Same {M : Type} (I : Interpretation KoreAML.Sym M) (e e' : Valuation M) : SvCtx → SvCtx → Prop
  | hole : Same I e e' .hole .hole
  | side {ψ ψ' : P} : (∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) → Same I e e' (.side ψ) (.side ψ')
  | app {C C' D D' : SvCtx} : Same I e e' C C' → Same I e e' D D' → Same I e e' (.app C D) (.app C' D')
  | andSide {C C' : SvCtx} {ψ ψ' : P} : Same I e e' C C' → (∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) →
      Same I e e' (.andSide C ψ) (.andSide C' ψ')

theorem Same.holes {M : Type} {I : Interpretation KoreAML.Sym M} {e e' : Valuation M} {C C' : SvCtx}
    (h : Same I e e' C C') : C.holes = C'.holes := by
  induction h with
  | hole => rfl
  | side _ => rfl
  | app _ _ ih1 ih2 => simp only [SvCtx.holes, ih1, ih2]
  | andSide _ _ ih => simp only [SvCtx.holes, ih]

/-- Such contexts have the same elements at the same elements for the occurrences. -/
theorem Same.den {M : Type} {I : Interpretation KoreAML.Sym M} {e e' : Valuation M} {C C' : SvCtx}
    (h : Same I e e' C C') : ∀ (a : Nat → M) (n : Nat) (m : M), C.den I e a n m ↔ C'.den I e' a n m := by
  induction h with
  | hole => intro a n m; exact Iff.rfl
  | side hs => intro a n m; exact hs m
  | app h1 _ ih1 ih2 => intro a n m; simp only [SvCtx.den, ih1, ih2, h1.holes]
  | andSide _ hs ih => intro a n m; simp only [SvCtx.den, ih, hs]

def topC : Kore.KSort := srt "GeneratedTopCell"
def expS : Kore.KSort := srt "Exp"

/-! The sentence. -/

def S : Kore.SVar := ⟨⟨⟨"VarS"⟩⟩, expS⟩
def dv1 : Kore.Pattern := ev "Var'Unds'DotVar1" (srt "K")
def dv0 : Kore.Pattern := ev "Var'Unds'DotVar0" (srt "GeneratedCounterCell")

/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(x), k)), counter)`. -/
def cfg (k counter x : Kore.Pattern) : Kore.Pattern :=
  ap "Lbl'-LT-'generatedTop'-GT-'" [ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [injP "Exp" "KItem" x, k]], counter]

/-- Sentence 104's pattern. -/
def ax : Kore.Pattern :=
  .rewrites topC
    (.and topC [cfg dv1 dv0 (ap "Lblc" [.var (.svar S), .var (.svar S)]), .top topC])
    (.and topC [cfg dv1 dv0 (ap "Lbld" [.var (.svar S)]), .top topC])

theorem ax_text : U.ax104.ax = ⟨[], ax, U.ax104.ax.attributes⟩ := by decide +kernel
theorem ax_trS : (trS U.ax104).pat = (trAxiom [] [] U.ax104).pat := by decide +kernel

def tblT : VarTable := tableOf [] ax
def X : SVar := tblT.sv (svarKey S)

/-- The configuration around the `k` cell's first item, as a context of applications, the two
variables beside the item as the patterns `k` and `counter`. -/
def cfgCtx (tbl : VarTable) (k counter : P) (item : SvCtx) : SvCtx :=
  .app (.app (.side (sym (.symbol "Lbl'-LT-'generatedTop'-GT-'")))
    (.app (.side (sym (.symbol "Lbl'-LT-'k'-GT-'")))
      (.app (.app (.side (sym (.symbol "kseq")))
        (.app (.side (sym (.symbol "inj") ⬝ trSort tbl expS ⬝ trSort tbl (srt "KItem"))) item))
        (.side k))))
    (.side counter)

def cItem : SvCtx := .app (.app (.side (sym (.symbol "Lblc"))) .hole) .hole
def dItem : SvCtx := .app (.side (sym (.symbol "Lbld"))) .hole

def LT : SvCtx := .andSide (cfgCtx tblT (tr ⟨tblT, []⟩ dv1) (tr ⟨tblT, []⟩ dv0) cItem) (sTop (trSort tblT topC))
def RT : SvCtx := .andSide (cfgCtx tblT (tr ⟨tblT, []⟩ dv1) (tr ⟨tblT, []⟩ dv0) dItem) (sTop (trSort tblT topC))

theorem tr_ax : tr ⟨tblT, []⟩ ax = sRewrites (trSort tblT topC) (LT.atSet X) (RT.atSet X) := rfl

set_option linter.unusedSimpArgs false in
theorem sidesT : LT.Sides X ∧ RT.Sides X := by
  refine ⟨?_, ?_⟩ <;> simp only [LT, RT, cItem, dItem, cfgCtx, SvCtx.Sides, and_self, true_and, and_true] <;> decide

/-! Γ's item. -/

def v0 : Kore.Pattern := ev "VarV0" expS
def v1 : Kore.Pattern := ev "VarV1" expS
def v2 : Kore.Pattern := ev "VarV2" (srt "K")
def v3 : Kore.Pattern := ev "VarV3" (srt "GeneratedCounterCell")
def v4 : Kore.Pattern := ev "VarV4" expS

/-- The right side of Γ's axiom: `∃Z. d(Z) ∧ ⊤ ∧ (Z ∈ A₀ ∨ Z ∈ A₁)`. -/
def rhsG : Kore.Pattern :=
  .exist topC (evar "VarV4" expS) (.and topC [cfg v2 v3 (ap "Lbld" [v4]), .top topC,
    .or topC [.in expS topC v4 v0, .in expS topC v4 v1]])

/-- Γ's axiom of the rule: `\rewrites(c(A₀, A₁) ∧ ⊤ ∧ ⌈R⌉, R)`. -/
def gPat : Kore.Pattern :=
  .rewrites topC (.and topC [cfg v2 v3 (ap "Lblc" [v0, v1]), .top topC, .ceil topC topC rhsG]) rhsG

theorem g_eq : prioRuleK c r0 = gPat := by decide +kernel

def tblG : VarTable := tableOf [] gPat
def k0 : VarKey := .evar "VarV0" expS
def k1 : VarKey := .evar "VarV1" expS
def k2 : VarKey := .evar "VarV2" (srt "K")
def k3 : VarKey := .evar "VarV3" (srt "GeneratedCounterCell")

def LG : SvCtx := cfgCtx tblG (.evar ⟨3⟩) (.evar ⟨4⟩) cItem
def RG : SvCtx := cfgCtx tblG (.evar ⟨3⟩) (.evar ⟨4⟩) dItem
def xsL (i : Nat) : EVar := if i = 0 then ⟨1⟩ else ⟨2⟩
def xsR (_ : Nat) : EVar := ⟨5⟩
def topP : P := sym (.sort "SortGeneratedTopCell")
def expP : P := sym (.sort "SortExp")
def bodyG : P := sAnd (RG.atVars xsR 0) (sAnd (sTop topP)
    (sOr topP (sIn expP topP (.evar ⟨5⟩) (.evar ⟨1⟩)) (sIn expP topP (.evar ⟨5⟩) (.evar ⟨2⟩))))
def rhsP : P := sExists ⟨5⟩ expP bodyG

theorem tr_g : (trAxiom [] [] (kAx gPat)).pat =
    (conjList [guardOf tblG k0, guardOf tblG k1, guardOf tblG k2, guardOf tblG k3] ⇒
      (sRewrites topP (sAnd (LG.atVars xsL 0) (sAnd (sTop topP) (sCeil topP topP rhsP))) rhsP ≡ inhOf topP)) := rfl

theorem tr_t : (trAxiom [] [] U.ax104).pat =
    (conjList [guardOf tblT (svarKey S), guardOf tblT (.evar "Var'Unds'DotVar1" (srt "K")),
        guardOf tblT (.evar "Var'Unds'DotVar0" (srt "GeneratedCounterCell"))] ⇒
      (sRewrites topP (LT.atSet X) (RT.atSet X) ≡ inhOf topP)) := by
  unfold trAxiom; rw [ax_text]; rfl


theorem cItem_same {M : Type} {I : Interpretation KoreAML.Sym M} (e e' : Valuation M) : Same I e e' cItem cItem :=
  .app (.app (.side fun _ => Iff.rfl) .hole) .hole

theorem dItem_same {M : Type} {I : Interpretation KoreAML.Sym M} (e e' : Valuation M) : Same I e e' dItem dItem :=
  .app (.side fun _ => Iff.rfl) .hole

/-- The valuation the sentence's two element variables are read at: Γ's item's values of its own
two (the sentence's table holds them one place before the item's). -/
def eT {M : Type} (e : Valuation M) : Valuation M := ⟨fun x => e.evalEvar ⟨x.val + 1⟩, e.evalSvar⟩

/-- The sentence's configuration read at `eT e` and Γ's item's read at `e` are of one shape, with
the same elements at their side patterns. -/
theorem cfg_same {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) {item : SvCtx}
    (h : Same I (eT e) e item item) :
    Same I (eT e) e (cfgCtx tblT (tr ⟨tblT, []⟩ dv1) (tr ⟨tblT, []⟩ dv0) item)
      (cfgCtx tblG (.evar ⟨3⟩) (.evar ⟨4⟩) item) :=
  .app (.app (.side fun _ => Iff.rfl) (.app (.side fun _ => Iff.rfl)
    (.app (.app (.side fun _ => Iff.rfl) (.app (.side fun _ => Iff.rfl) h)) (.side fun _ => Iff.rfl))))
    (.side fun _ => Iff.rfl)

/-- The side patterns of Γ's item's configuration do not read the bound variable. -/
theorem cfgG_agree {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (z : M) :
    RG.SidesAgree I e (updE e ⟨5⟩ z) := by
  have h3 : ∀ m, (Pattern.evar ⟨3⟩ : P).interpret I (updE e ⟨5⟩ z) m ↔ (Pattern.evar ⟨3⟩ : P).interpret I e m :=
    fun m => by simp [Function.update]
  have h4 : ∀ m, (Pattern.evar ⟨4⟩ : P).interpret I (updE e ⟨5⟩ z) m ↔ (Pattern.evar ⟨4⟩ : P).interpret I e m :=
    fun m => by simp [Function.update]
  exact ⟨⟨fun _ => Iff.rfl, fun _ => Iff.rfl, ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, trivial⟩, h3⟩, h4⟩

theorem sidesAgree_refl {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) :
    ∀ C : SvCtx, C.SidesAgree I e e
  | .hole => trivial
  | .side _ => fun _ => Iff.rfl
  | .app C D => ⟨sidesAgree_refl e C, sidesAgree_refl e D⟩
  | .andSide C _ => ⟨sidesAgree_refl e C, fun _ => Iff.rfl⟩

/-- **Γ's item holds where sentence 104 does**, in an interpretation with definedness, `\ceil`'s
definition and the sorts Exp and GeneratedTopCell each one sort. At a valuation `e` of the item
and an element of its left side `c(a₀, a₁)`, the sentence at the set `{a₀, a₁}` gives a successor in
`d(S)`, an element of `d(z)` for a z of the set: the item's right side at `Z = z`. -/
theorem item_of_sentence {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) {σe σt : M}
    (hE : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σe)
    (hT : ∀ a, I.evalSymb (.sort "SortGeneratedTopCell") a ↔ a = σt)
    (hσe : IsSort I σe) (hσt : IsSort I σt)
    (h : I ⊧ᴵ (trAxiom [] [] U.ax104).pat) : I ⊧ᴵ (trAxiom [] [] (kAx gPat)).pat := by
  intro e m
  rw [tr_g, interpret_impl]
  intro hg
  simp only [conjList, interpret_conj] at hg
  obtain ⟨g0, g1, g2, g3⟩ := hg
  have g0 := (interp_guard_evar hD (t := tblG) (n := "VarV0") (s := expS)).mp g0
  have g1 := (interp_guard_evar hD (t := tblG) (n := "VarV1") (s := expS)).mp g1
  have g2 := (interp_guard_evar hD (t := tblG) (n := "VarV2") (s := srt "K")).mp g2
  have g3 := (interp_guard_evar hD (t := tblG) (n := "VarV3") (s := srt "GeneratedCounterCell")).mp g3
  have hEP : ∀ (e : Valuation M) a, expP.interpret I e a ↔ a = σe := fun _ a => hE a
  have hTP : ∀ (e : Valuation M) a, topP.interpret I e a ↔ a = σt := fun _ a => hT a
  have hTop : ∀ (e : Valuation M) b, (sTop topP).interpret I e b ↔ Inh I σt b := fun e b => by
    rw [interp_sTop hD (by decide) b, interp_inhOf_of (hTP e)]
  have ha0 : Inh I σe (e.evalEvar ⟨1⟩) := (interp_inhOf_of (hEP e)).mp g0
  have ha1 : Inh I σe (e.evalEvar ⟨2⟩) := (interp_inhOf_of (hEP e)).mp g1
  rw [interp_equal hD]
  intro a
  unfold sRewrites
  rw [interp_sImp]
  refine ⟨fun hh => hh.1, fun ha => ⟨ha, fun hL => ?_⟩⟩
  have haT : Inh I σt a := (interp_inhOf_of (hTP e)).mp ha
  let af : Nat → M := fun i => e.evalEvar (xsL i)
  let A : Set M := fun x => x = e.evalEvar ⟨1⟩ ∨ x = e.evalEvar ⟨2⟩
  have hAE : ∀ x, A x → Inh I σe x := by
    rintro x (rfl | rfl)
    · exact ha0
    · exact ha1
  have hLden : LG.den I e af 0 a :=
    (SvCtx.atVars_iff xsL e e af LG 0 (sidesAgree_refl e LG) (fun _ _ => rfl) a).mp (interp_sAnd.mp hL).1
  -- the sentence, at the set of the two left elements
  have hax := h (svarAt_svin (eT e) X A) a
  rw [tr_t, interpret_impl] at hax
  have hgT : (conjList [guardOf tblT (svarKey S), guardOf tblT (.evar "Var'Unds'DotVar1" (srt "K")),
      guardOf tblT (.evar "Var'Unds'DotVar0" (srt "GeneratedCounterCell"))]).interpret I
        (svarAt_svin (eT e) X A) a := by
    simp only [conjList, interpret_conj]
    refine ⟨?_, ?_, ?_⟩
    · show (Pattern.svar X ⊆⊆ inhOf (trSort tblT expS) : P).interpret I (svarAt_svin (eT e) X A) a
      rw [interp_included hD]
      intro x hx
      have hx' : A x := by
        have : Function.update (eT e).evalSvar X A X x := hx
        simpa using this
      exact (interp_inhOf_of (hEP _)).mpr (hAE x hx')
    · rw [interp_guard_evar hD]; exact g2
    · rw [interp_guard_evar hD]; exact g3
  have h3 := ((interp_equal hD).mp (hax hgT) a).mpr ha
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  have h4 := h3.2 ((SvCtx.atSet_iff X (eT e) A LT sidesT.1 0 a).mpr ⟨af, fun i _ => by
      by_cases hi : i = 0
      · subst hi; exact Or.inl rfl
      · exact Or.inr (by simp [af, xsL, hi]),
    ((cfg_same e (cItem_same _ _)).den af 0 a).mpr hLden, (hTop (eT e) a).mpr haT⟩)
  unfold sNext at h4 ⊢
  obtain ⟨nx, b, hnx, hb, happ⟩ := interp_app.mp h4
  obtain ⟨z, hz, hRz⟩ := (SvCtx.atSet_iff X (eT e) A RT sidesT.2 0 b).mp hb
  have hz0 : A (z 0) := hz 0 (by decide)
  have hbT : Inh I σt b := (hTop (eT e) b).mp hRz.2
  refine interp_app.mpr ⟨nx, b, hnx, ?_, happ⟩
  unfold rhsP
  rw [interp_sExists_elem hD]
  have e55 : (updE e ⟨5⟩ (z 0)).evalEvar ⟨5⟩ = z 0 := by simp
  have e51 : (updE e ⟨5⟩ (z 0)).evalEvar ⟨1⟩ = e.evalEvar ⟨1⟩ := by simp [Function.update]
  have e52 : (updE e ⟨5⟩ (z 0)).evalEvar ⟨2⟩ = e.evalEvar ⟨2⟩ := by simp [Function.update]
  refine ⟨z 0, (interp_inhOf_of (hEP _)).mpr (hAE _ hz0), ?_⟩
  unfold bodyG
  rw [interp_sAnd, interp_sAnd]
  refine ⟨?_, (hTop _ b).mpr hbT, ?_⟩
  · refine (SvCtx.atVars_iff xsR e (updE e ⟨5⟩ (z 0)) z RG 0 (cfgG_agree e (z 0)) (fun i hi => ?_) b).mpr
      (((cfg_same e (dItem_same _ _)).den z 0 b).mp hRz.1)
    have hi0 : i = 0 := by
      have h1 : RG.holes = 1 := rfl
      omega
    subst hi0
    exact e55
  · rw [interp_sOr]
    refine ⟨(interp_inhOf_of (hTP _)).mpr hbT, ?_⟩
    rw [interp_sIn_evar_svin hD hc (hEP _) (hTP _) hσe hσt (e55 ▸ hAE _ hz0) b,
      interp_sIn_evar_svin hD hc (hEP _) (hTP _) hσe hσt (e55 ▸ hAE _ hz0) b, e55, e51, e52]
    rcases hz0 with h0 | h0
    · exact Or.inl ⟨h0, hbT⟩
    · exact Or.inr ⟨h0, hbT⟩

end SvR

/-- **W1 for rule 0, over the signature**: Γ's item is a consequence of sentence 104 and Γ's
signature, for every H. -/
theorem rule0_from_text_sig (H : HookParams) :
    itemsPremises [trS U.ax104] ∪ ΓSig (cH H) ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inr ⟨x, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σe, hE, hσe⟩ := TieRhs.sortSing_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
  obtain ⟨σt, hT, hσt⟩ := TieRhs.sortSing_sig hD hSig (s := topCellSort)
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
  rw [show (cH H).sortName 32 = "Exp" from (by decide +kernel : c.sortName 32 = "Exp")] at hE
  rw [show (cH H).sortName topCellSort = "GeneratedTopCell" from
    (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")] at hT
  rw [SvR.g_eq]
  refine SvR.item_of_sentence hD hc hE hT hσe hσt ?_
  rw [← SvR.ax_trS]
  exact hI _ (Or.inl (Or.inl ⟨trS U.ax104, List.mem_singleton_self _, rfl⟩))

/-- **W1 for the rules, over the signature, and the converse for `ruleItems`**: each of Γ's rule
items is a consequence of a text sentence of `ruleText` and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl
  exact ⟨U.ax104, List.mem_cons_self, rule0_from_text_sig H⟩

/-- The priority the rule sentence's attributes state is the rule's. -/
theorem rule_prios : ruleText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) = c.rules.map (·.prio) := by
  decide +kernel

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
    ∀ ad ∈ [U.ax93, U.ax99, U.ax102], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax103).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 47 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax47).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE3SetvarRewrite

#check @KCore.TieE3SetvarRewrite.noRaw
#check @KCore.TieE3SetvarRewrite.readsConfined_c
#check @KCore.TieE3SetvarRewrite.userAxioms_eq
#check @KCore.TieE3SetvarRewrite.coreOK
#check @KCore.TieE3SetvarRewrite.wf_defn
#check @KCore.TieE3SetvarRewrite.account
#check @KCore.TieE3SetvarRewrite.account_sizes
#check @KCore.TieE3SetvarRewrite.account_classes
#check @KCore.TieE3SetvarRewrite.account_absent
#check @KCore.TieE3SetvarRewrite.absent_closed
#check @KCore.TieE3SetvarRewrite.absent_proj_below_c
#check @KCore.TieE3SetvarRewrite.absent_proj_below
#check @KCore.TieE3SetvarRewrite.lists_in_account
#check @KCore.TieE3SetvarRewrite.attrs_agree
#check @KCore.TieE3SetvarRewrite.sig_origin
#check @KCore.TieE3SetvarRewrite.decls_entailed
#check @KCore.TieE3SetvarRewrite.consistent
#check @KCore.TieE3SetvarRewrite.fnFun_indices
#check @KCore.TieE3SetvarRewrite.fnFun_account
#check @KCore.TieE3SetvarRewrite.fnFun_checked
#check @KCore.TieE3SetvarRewrite.fnFun_trS
#check @KCore.TieE3SetvarRewrite.fnFun_at_values
#check @KCore.TieE3SetvarRewrite.fnFun_at_values_step
#check @KCore.TieE3SetvarRewrite.fn_shape
#check @KCore.TieE3SetvarRewrite.fns_account
#check @KCore.TieE3SetvarRewrite.fns_entailed
#check @KCore.TieE3SetvarRewrite.fns_from_text
#check @KCore.TieE3SetvarRewrite.fn_prios
#check @KCore.TieE3SetvarRewrite.nojunk_trivial_entailed
#check @KCore.TieE3SetvarRewrite.nojunk_items_entailed
#check @KCore.TieE3SetvarRewrite.nojunk_kitem_entailed
#check @KCore.TieE3SetvarRewrite.cons_entailed
#check @KCore.TieE3SetvarRewrite.idem_refuted
#check @KCore.TieE3SetvarRewrite.owed_rules
#check @KCore.TieE3SetvarRewrite.owed_clauses
#check @KCore.TieE3SetvarRewrite.openDecidedH
#check @KCore.TieE3SetvarRewrite.gammaCl_eq
#check @KCore.TieE3SetvarRewrite.decls_entailed_c
#check @KCore.TieE3SetvarRewrite.fns_entailed_c
#check @KCore.TieE3SetvarRewrite.nojunk_trivial_entailed_c
#check @KCore.TieE3SetvarRewrite.nojunk_items_entailed_c
#check @KCore.TieE3SetvarRewrite.nojunk_kitem_entailed_c
#check @KCore.TieE3SetvarRewrite.cons_entailed_c
#check @KCore.TieE3SetvarRewrite.idem_refuted_c
#print axioms KCore.TieE3SetvarRewrite.noRaw
#print axioms KCore.TieE3SetvarRewrite.readsConfined_c
#print axioms KCore.TieE3SetvarRewrite.userAxioms_eq
#print axioms KCore.TieE3SetvarRewrite.coreOK
#print axioms KCore.TieE3SetvarRewrite.wf_defn
#print axioms KCore.TieE3SetvarRewrite.account
#print axioms KCore.TieE3SetvarRewrite.account_sizes
#print axioms KCore.TieE3SetvarRewrite.account_classes
#print axioms KCore.TieE3SetvarRewrite.account_absent
#print axioms KCore.TieE3SetvarRewrite.absent_closed
#print axioms KCore.TieE3SetvarRewrite.absent_proj_below_c
#print axioms KCore.TieE3SetvarRewrite.absent_proj_below
#print axioms KCore.TieE3SetvarRewrite.lists_in_account
#print axioms KCore.TieE3SetvarRewrite.attrs_agree
#print axioms KCore.TieE3SetvarRewrite.sig_origin
#print axioms KCore.TieE3SetvarRewrite.decls_entailed
#print axioms KCore.TieE3SetvarRewrite.consistent
#print axioms KCore.TieE3SetvarRewrite.fnFun_indices
#print axioms KCore.TieE3SetvarRewrite.fnFun_account
#print axioms KCore.TieE3SetvarRewrite.fnFun_checked
#print axioms KCore.TieE3SetvarRewrite.fnFun_trS
#print axioms KCore.TieE3SetvarRewrite.fnFun_at_values
#print axioms KCore.TieE3SetvarRewrite.fnFun_at_values_step
#print axioms KCore.TieE3SetvarRewrite.fn_shape
#print axioms KCore.TieE3SetvarRewrite.fns_account
#print axioms KCore.TieE3SetvarRewrite.fns_entailed
#print axioms KCore.TieE3SetvarRewrite.fns_from_text
#print axioms KCore.TieE3SetvarRewrite.fn_prios
#print axioms KCore.TieE3SetvarRewrite.nojunk_trivial_entailed
#print axioms KCore.TieE3SetvarRewrite.nojunk_items_entailed
#print axioms KCore.TieE3SetvarRewrite.nojunk_kitem_entailed
#print axioms KCore.TieE3SetvarRewrite.cons_entailed
#print axioms KCore.TieE3SetvarRewrite.idem_refuted
#print axioms KCore.TieE3SetvarRewrite.owed_rules
#print axioms KCore.TieE3SetvarRewrite.owed_clauses
#print axioms KCore.TieE3SetvarRewrite.openDecidedH
#print axioms KCore.TieE3SetvarRewrite.gammaCl_eq
#print axioms KCore.TieE3SetvarRewrite.decls_entailed_c
#print axioms KCore.TieE3SetvarRewrite.fns_entailed_c
#print axioms KCore.TieE3SetvarRewrite.nojunk_trivial_entailed_c
#print axioms KCore.TieE3SetvarRewrite.nojunk_items_entailed_c
#print axioms KCore.TieE3SetvarRewrite.nojunk_kitem_entailed_c
#print axioms KCore.TieE3SetvarRewrite.cons_entailed_c
#print axioms KCore.TieE3SetvarRewrite.idem_refuted_c
#check @KCore.TieE3SetvarRewrite.rules_account
#check @KCore.TieE3SetvarRewrite.SvR.item_of_sentence
#check @KCore.TieE3SetvarRewrite.rule0_from_text_sig
#check @KCore.TieE3SetvarRewrite.rule_from_text_sig
#check @KCore.TieE3SetvarRewrite.rule_prios
#print axioms KCore.TieE3SetvarRewrite.rules_account
#print axioms KCore.TieE3SetvarRewrite.rule_from_text_sig
#print axioms KCore.TieE3SetvarRewrite.rule_prios
