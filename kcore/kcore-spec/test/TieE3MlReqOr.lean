/-
  The tie (C14) on `f2-examples/e3-ml-req-or.kompile.kore`, the kompiled text of construct fixture e3-ml-req-or
  (`test/constructs/fixtures/e3-ml-req-or`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-req-or`, its rules section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlReqOr.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 264 sentences of the user module E3-ML-REQ-OR, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 208 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (157), by hand, in the section `The rules` (`Rules`): each of Γ's rule items is a
    consequence of its text sentence with the text's sentences 138 (library), 49 (hooked functional)
    (`Rules.ruleAux`), the item of the text's signature `nonemptyItem ⟨"SortInt", [], true⟩`
    (`Rules.ruleSigAux`; each an item of `(Theory.ofDefinition kore).signature`,
    `Rules.ruleSigAux_text`) and the text's signature (`ΓSig`), `Rules.ruleText` in `ruleItems`'
    order (`Rules.rule_from_text_aux`, W1, every H; `Rules.rules_account`). `ΓSig` holds the items
    of the text's declarations or surplus ones, the sort constant of a registry sort or the arity of
    a hooked symbol that the text does not declare at that shape (`sig_origin`), and the arity of
    every literal (`dvArityAll`). Two limits, argued and not proved: that a surplus item of a name
    the text declares with sort parameters adds no consequence in the text's symbols; and that
    `dvArityAll` at a literal no axiom of the text writes, no item of the text, adds none either.
    The section's other headline statements (its comment says what each states): `Rules.text_item`,
    `Rules.gamma_item0`, `Rules.sents_true`.
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
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlReqOr

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-req-or.kompile.kore"
definition_of defn from "f2-examples/e3-ml-req-or.kompile.kore"
user_axioms U from "f2-examples/e3-ml-req-or.kompile.kore" module "E3-ML-REQ-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-REQ-OR")

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


/-! ## The rules (157): W1 from the sentence, sentences 138 and 49, Int's G-nonempty item and the text's signature, for every H (by hand)

The sentence's `requires` is
`\equals{SortBool{}, C}(\and{SortBool{}}(\or{SortBool{}}(X >Int 0, X <Int -5), _Gen0), true)`
with `_Gen0:Bool` a free variable of the sentence that Γ's items do not have. Γ holds two rule
items of one priority, one per disjunct: `requires` `X >Int 0` and `requires` `X <Int -5`. The
sentence and Γ's two items are the items of `\rewrites{C}(L, r)` at one variable table with one
right side (`text_item`, `gamma_item0`, `gamma_item1`, kernel). Sentence 138
(`INT-KORE.eq-int-true-left`, `{K1 ==Int K2 #Equals true} = {K1 #Equals K2}` over element variables
of Int, with no condition) and sentence 49 (the functional sentence of `_==Int_`), at an element of
Int given to both variables (the text's G-nonempty item of Int, `ruleSigAux_text`), state that
`true` denotes one element of Bool (`true_one`). The sentence at `_Gen0 := true`, where
`(A ∨ B) ∧ true` equals `true` as soon as one disjunct does (`gamma_sub_text`), gives each of Γ's
items, which do not read `_Gen0` (`item_of_text`). No item of `ΓDomains` is among the premises
(`rule_from_text_aux`). -/

deriving instance DecidableEq for KoreAML.SortDecl

namespace Rules

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

/-- Γ's axioms of the two rules. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
noncomputable def p1 : Kore.Pattern := prioRuleK c r1

/-- Their parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by
  kernel_rfl

/-- Γ's variables: X, the rest of the K cell, the counter cell; and a variable for the
sentence's `_Gen0`, which Γ's axioms do not have. -/
def xX : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Int")
def xG : Kore.EVar := KoreAML.evar "VarG" (KoreAML.srt "Bool")

/-- The two disjuncts: `X >Int 0` and `X <Int -5`. -/
def atomA : Kore.Pattern := .app ⟨⟨"Lbl'Unds-GT-'Int'Unds'"⟩⟩ [] [.var (.evar xX), .dv (KoreAML.srt "Int") "0"]
def atomB : Kore.Pattern := .app ⟨⟨"Lbl'Unds-LT-'Int'Unds'"⟩⟩ [] [.var (.evar xX), .dv (KoreAML.srt "Int") "-5"]

/-- The left side's term. -/
noncomputable def hd : Kore.Pattern := TieRuleLhs.andHead q0.2.1

/-- `\equals{SortBool{}, C}(p, true)`. -/
noncomputable def eqT (p : Kore.Pattern) : Kore.Pattern :=
  .equals (KoreAML.srt "Bool") q0.1 p (.dv (KoreAML.srt "Bool") "true")

/-- Γ's left side of the rule with the `requires` `p`: the term, `p = true`, and `⌈r⌉`. -/
noncomputable def LG (p : Kore.Pattern) : Kore.Pattern := .and q0.1 [hd, eqT p, .ceil q0.1 q0.1 q0.2.2]

/-- The left side as the text writes it: the term, and the `requires`
`\and{SortBool{}}(\or{SortBool{}}(A, B), _Gen0)` equated with `true`. -/
noncomputable def Ltext : Kore.Pattern :=
  .and q0.1 [hd, eqT (.and (KoreAML.srt "Bool") [.or (KoreAML.srt "Bool") [atomA, atomB], .var (.evar xG)])]

/-- The one variable table: the sentence's variables, Γ's three first. -/
noncomputable def tb : VarTable := tableOf [] (.rewrites q0.1 Ltext q0.2.2)
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups
noncomputable def f0 : List VarKey := (freeOf [] p0).eraseDups
noncomputable def f1 : List VarKey := (freeOf [] p1).eraseDups

/-- **The rule sentence is the item of `\rewrites{C}(Ltext, r)`** (kernel). -/
theorem text_item : (trS U.ax157).pat = TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2 := by
  have h : TiePair.renSeq (TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2) [] = some (trS U.ax157).pat := by
    decide +kernel
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **Γ's two rule items are the items of `\rewrites{C}(LG A, r)` and `\rewrites{C}(LG B, r)` at
the same table** (kernel). -/
theorem gamma_item0 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat = TieRuleLhs.itemAt tb f0 q0.1 (LG atomA) q0.2.2 := by
  decide +kernel
theorem gamma_item1 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩).pat = TieRuleLhs.itemAt tb f1 q0.1 (LG atomB) q0.2.2 := by
  decide +kernel

/-- The sentence's free variables are Γ's and `_Gen0`. -/
theorem free_more0 : ∀ k ∈ fT, k ∈ f0 ∨ k = evarKey xG := by decide +kernel
theorem free_more1 : ∀ k ∈ fT, k ∈ f1 ∨ k = evarKey xG := by decide +kernel

/-- Γ's items do not read `_Gen0`. -/
theorem item0_noG : (TieRuleLhs.itemAt tb f0 q0.1 (LG atomA) q0.2.2).isFreeEvar (tb.ev (evarKey xG)) = false := by
  decide +kernel
theorem item1_noG : (TieRuleLhs.itemAt tb f1 q0.1 (LG atomB) q0.2.2).isFreeEvar (tb.ev (evarKey xG)) = false := by
  decide +kernel

kernel_rfl C_eq : q0.1 = KoreAML.srt "GeneratedTopCell"
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel

theorem tr_dv {t : VarTable} (n : String) :
    tr ⟨t, []⟩ (.dv (KoreAML.srt "Bool") n) = KoreAML.sym (.dv n) ⬝ KoreAML.sym (.sort "SortBool") := by
  rw [tr, trSort_srt]; rfl

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

/-- **Sentences 138 and 49 are `INT-KORE.eq-int-true-left` and the functional sentence of
`_==Int_`**, as `TieReqBool` writes them (kernel). -/
theorem sents_true : (trS U.ax138).pat = TieReqBool.sentPat TieReqBool.eqIntTrueLeftAx ∧
    (trS U.ax49).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.eqIntName) := by
  constructor <;> decide +kernel

/-- `true` is one element of Bool, in a model of definedness and the signature in which Int has an
element and sentences 138 and 49 hold. -/
theorem true_one (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat)
    (h1 : I ⊧ᴵ (trS U.ax138).pat) (hf1 : I ⊧ᴵ (trS U.ax49).pat) (e : Valuation M) :
    ∃ σB aT, (∀ x, (trSort tb (KoreAML.srt "Bool")).interpret I e x ↔ x = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e m ↔ m = aT) ∧ Inh I σB aT := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact TieReqBool.boolTrue_of_text_sig hD hSig (int_numbered H) (int_name H) hN
    (sents_true.1 ▸ h1) (sents_true.2 ▸ hf1) tb e

/-- Where `_Gen0` is `true`, every element of Γ's left side of a disjunct's rule is one of the
text's left side, at every valuation: where the disjunct `p` equals `true`,
`(A ∨ B) ∧ _Gen0` holds, of the elements of Bool, exactly `true`. -/
theorem gamma_sub_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H)) (hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat)
    (h1 : I ⊧ᴵ (trS U.ax138).pat) (hf1 : I ⊧ᴵ (trS U.ax49).pat) (e : Valuation M)
    (hG : (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e (e.evalEvar (tb.ev (evarKey xG))))
    {p : Kore.Pattern} (hp : p = atomA ∨ p = atomB) (a : M)
    (h : (tr ⟨tb, []⟩ (LG p)).interpret I e a) : (tr ⟨tb, []⟩ Ltext).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσC1
  have hSC : ∀ b, (trSort tb q0.1).interpret I e b ↔ b = σC := by
    rw [C_eq, trSort_srt]; exact hσC1
  obtain ⟨σB, aT, hSB, hσB, hat, -⟩ := true_one H hD hSig hN h1 hf1 e
  have hg : e.evalEvar (tb.ev (evarKey xG)) = aT := (hat _).mp hG
  have hTe : ∀ (p q : Kore.Pattern), tr ⟨tb, []⟩ (.equals (KoreAML.srt "Bool") q0.1 p q) =
      sEquals (trSort tb (KoreAML.srt "Bool")) (trSort tb q0.1) (tr ⟨tb, []⟩ p) (tr ⟨tb, []⟩ q) := fun p q => by rw [tr]
  unfold LG at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hterm := h _ (List.mem_cons_self ..)
  have heq := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold eqT at heq
  rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2] at heq
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hterm
  rw [List.mem_singleton.mp hq]
  unfold eqT
  rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2]
  refine ⟨heq.1, fun x hx => ?_⟩
  rw [tr_and2, interp_sAnd, Model.tr_or2Stdi, interp_sOr, interp_inhOf_of hSB]
  have hv : (tr ⟨tb, []⟩ (.var (.evar xG))).interpret I e x ↔ x = aT := by
    rw [tr, interp_evar, hg]
  rw [hv, hat x]
  constructor
  · exact fun h' => h'.2
  · intro hxT
    refine ⟨⟨hx, ?_⟩, hxT⟩
    have hpx := (heq.2 x hx).mpr ((hat x).mpr hxT)
    rcases hp with rfl | rfl
    · exact Or.inl hpx
    · exact Or.inr hpx

/-- Γ's item of a disjunct's rule from the sentence's item, at one valuation: the sentence at
`_Gen0 := true`, which Γ's item does not read. -/
theorem item_of_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H)) (hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat)
    (h1 : I ⊧ᴵ (trS U.ax138).pat) (hf1 : I ⊧ᴵ (trS U.ax49).pat)
    (hT : I ⊧ᴵ TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2) {fG : List VarKey} {p : Kore.Pattern}
    (hp : p = atomA ∨ p = atomB) (hmore : ∀ k ∈ fT, k ∈ fG ∨ k = evarKey xG)
    (hno : (TieRuleLhs.itemAt tb fG q0.1 (LG p) q0.2.2).isFreeEvar (tb.ev (evarKey xG)) = false) :
    I ⊧ᴵ TieRuleLhs.itemAt tb fG q0.1 (LG p) q0.2.2 := by
  intro e m
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, aT, hSB, hσB, hat, hit⟩ := true_one H hD hSig hN h1 hf1 e
  let e' : Valuation M := ⟨Function.update e.evalEvar (tb.ev (evarKey xG)) aT, e.evalSvar⟩
  rw [← interp_evarAt_svin (a := aT) hno m]
  obtain ⟨σB', aT', hSB', hσB', hat', hit'⟩ := true_one H hD hSig hN h1 hf1 e'
  have hgv : e'.evalEvar (tb.ev (evarKey xG)) = aT := by simp [e']
  have hTT : aT' = aT := by
    have h1 : (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e aT := (hat aT).mpr rfl
    rw [tr_dv, ← den_true H] at h1
    have h2 := ((den_closed (cH H) (KCore.bool true)).interp e e' aT).mp h1
    rw [den_true H, ← tr_dv (t := tb)] at h2
    exact ((hat' aT).mp h2).symm
  have hG : (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e' (e'.evalEvar (tb.ev (evarKey xG))) := by
    rw [hgv]; exact (hat' aT).mpr hTT.symm
  have h1' := TieRuleLhs.lhs_entails hD (fT := fT) (fG := fT) (C := q0.1) (L := Ltext) (L' := LG p) (r := q0.2.2)
    (fun _ hk => hk) hT e' m (fun _ a ha => gamma_sub_text H hD hSig hN h1 hf1 e' hG hp a ha)
  show (TieRuleLhs.itemAt tb fG q0.1 (LG p) q0.2.2).interpret I e' m
  unfold TieRuleLhs.itemAt at h1' ⊢
  rw [interpret_impl] at h1' ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  refine h1' (TieUnion.interp_conjListAll.mpr fun φ hφ => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
  rcases hmore k hk with hk | rfl
  · exact hg _ (List.mem_map_of_mem hk)
  · show (guardOf tb (.evar _ _)).interpret I e' m
    rw [interp_guard_evar hD]
    have hin : (inhOf (trSort tb (KoreAML.srt "Bool"))).interpret I e' aT' := (interp_inhOf_of hSB').mpr hit'
    rw [hTT] at hin
    show (inhOf (trSort tb (KoreAML.srt "Bool"))).interpret I e' (e'.evalEvar (tb.ev (evarKey xG)))
    rw [hgv]; exact hin

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

/-- The other sentences of the text the statement reads: 138 and 49. -/
noncomputable def ruleAux : List AxiomDecl := [U.ax138, U.ax49]

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

/-- **W1 for the rule sentence, and the converse for `ruleItems`**, from the text: each of Γ's two
rule items is a consequence of the sentence 157 with sentences 138 and 49, Int's G-nonempty item
and the signature, for every H. No item of `ΓDomains` is among the premises. -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  refine ⟨U.ax157, List.mem_singleton_self _, ?_⟩
  intro M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2 := by
    rw [← text_item]; exact hI _ (Or.inl (Or.inl (List.mem_cons_self ..)))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have h1 : I ⊧ᴵ (trS U.ax138).pat := hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have hf1 : I ⊧ᴵ (trS U.ax49).pat :=
    hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat :=
    hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  rcases List.mem_cons.mp hit with rfl | hit
  · rw [gamma_item0]
    exact item_of_text H hD hSig hN h1 hf1 hT (Or.inl rfl) free_more0 item0_noG
  · rw [List.mem_singleton.mp hit, gamma_item1]
    exact item_of_text H hD hSig hN h1 hf1 hT (Or.inr rfl) free_more1 item1_noG

end Rules

end KCore.TieE3MlReqOr

#check @KCore.TieE3MlReqOr.noRaw
#check @KCore.TieE3MlReqOr.readsConfined_c
#check @KCore.TieE3MlReqOr.userAxioms_eq
#check @KCore.TieE3MlReqOr.coreOK
#check @KCore.TieE3MlReqOr.wf_defn
#check @KCore.TieE3MlReqOr.account
#check @KCore.TieE3MlReqOr.account_sizes
#check @KCore.TieE3MlReqOr.account_classes
#check @KCore.TieE3MlReqOr.account_absent
#check @KCore.TieE3MlReqOr.absent_closed
#check @KCore.TieE3MlReqOr.absent_proj_below_c
#check @KCore.TieE3MlReqOr.absent_proj_below
#check @KCore.TieE3MlReqOr.lists_in_account
#check @KCore.TieE3MlReqOr.attrs_agree
#check @KCore.TieE3MlReqOr.sig_origin
#check @KCore.TieE3MlReqOr.decls_entailed
#check @KCore.TieE3MlReqOr.consistent
#check @KCore.TieE3MlReqOr.fnFun_indices
#check @KCore.TieE3MlReqOr.fnFun_account
#check @KCore.TieE3MlReqOr.fnFun_checked
#check @KCore.TieE3MlReqOr.fnFun_trS
#check @KCore.TieE3MlReqOr.fnFun_at_values
#check @KCore.TieE3MlReqOr.fnFun_at_values_step
#check @KCore.TieE3MlReqOr.fn_shape
#check @KCore.TieE3MlReqOr.fns_account
#check @KCore.TieE3MlReqOr.fns_entailed
#check @KCore.TieE3MlReqOr.fns_from_text
#check @KCore.TieE3MlReqOr.fn_prios
#check @KCore.TieE3MlReqOr.nojunk_trivial_entailed
#check @KCore.TieE3MlReqOr.nojunk_items_entailed
#check @KCore.TieE3MlReqOr.nojunk_kitem_entailed
#check @KCore.TieE3MlReqOr.cons_entailed
#check @KCore.TieE3MlReqOr.idem_refuted
#check @KCore.TieE3MlReqOr.lib166
#check @KCore.TieE3MlReqOr.lib166_at_values
#check @KCore.TieE3MlReqOr.Rules.rules_account
#check @KCore.TieE3MlReqOr.Rules.rule_from_text_aux
#check @KCore.TieE3MlReqOr.Rules.ruleSigAux_text
#check @KCore.TieE3MlReqOr.Rules.text_item
#check @KCore.TieE3MlReqOr.Rules.gamma_item0
#check @KCore.TieE3MlReqOr.Rules.sents_true
#print axioms KCore.TieE3MlReqOr.noRaw
#print axioms KCore.TieE3MlReqOr.readsConfined_c
#print axioms KCore.TieE3MlReqOr.userAxioms_eq
#print axioms KCore.TieE3MlReqOr.coreOK
#print axioms KCore.TieE3MlReqOr.wf_defn
#print axioms KCore.TieE3MlReqOr.account
#print axioms KCore.TieE3MlReqOr.account_sizes
#print axioms KCore.TieE3MlReqOr.account_classes
#print axioms KCore.TieE3MlReqOr.account_absent
#print axioms KCore.TieE3MlReqOr.absent_closed
#print axioms KCore.TieE3MlReqOr.absent_proj_below_c
#print axioms KCore.TieE3MlReqOr.absent_proj_below
#print axioms KCore.TieE3MlReqOr.lists_in_account
#print axioms KCore.TieE3MlReqOr.attrs_agree
#print axioms KCore.TieE3MlReqOr.sig_origin
#print axioms KCore.TieE3MlReqOr.decls_entailed
#print axioms KCore.TieE3MlReqOr.consistent
#print axioms KCore.TieE3MlReqOr.fnFun_indices
#print axioms KCore.TieE3MlReqOr.fnFun_account
#print axioms KCore.TieE3MlReqOr.fnFun_checked
#print axioms KCore.TieE3MlReqOr.fnFun_trS
#print axioms KCore.TieE3MlReqOr.fnFun_at_values
#print axioms KCore.TieE3MlReqOr.fnFun_at_values_step
#print axioms KCore.TieE3MlReqOr.fn_shape
#print axioms KCore.TieE3MlReqOr.fns_account
#print axioms KCore.TieE3MlReqOr.fns_entailed
#print axioms KCore.TieE3MlReqOr.fns_from_text
#print axioms KCore.TieE3MlReqOr.fn_prios
#print axioms KCore.TieE3MlReqOr.nojunk_trivial_entailed
#print axioms KCore.TieE3MlReqOr.nojunk_items_entailed
#print axioms KCore.TieE3MlReqOr.nojunk_kitem_entailed
#print axioms KCore.TieE3MlReqOr.cons_entailed
#print axioms KCore.TieE3MlReqOr.idem_refuted
#print axioms KCore.TieE3MlReqOr.lib166
#print axioms KCore.TieE3MlReqOr.lib166_at_values
#print axioms KCore.TieE3MlReqOr.Rules.rules_account
#print axioms KCore.TieE3MlReqOr.Rules.rule_from_text_aux
#print axioms KCore.TieE3MlReqOr.Rules.ruleSigAux_text
#print axioms KCore.TieE3MlReqOr.Rules.text_item
#print axioms KCore.TieE3MlReqOr.Rules.gamma_item0
#print axioms KCore.TieE3MlReqOr.Rules.sents_true
