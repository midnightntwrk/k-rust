/-
  The tie (C14) on `f2-examples/e5-ovl-fun-partial.kompile.kore`, the kompiled text of construct fixture e5-ovl-fun-partial
  (`test/constructs/fixtures/e5-ovl-fun-partial`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e5-ovl-fun-partial`, its ovlfn section by hand; run from the package root:
  `lake env lean -j1 test/TieE5OvlFunPartial.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists and the two sentences of a function-overloaded symbol, listed apart
    (`ovlFnApart`), partition the 152 sentences of the user module E5-OVL-FUN-PARTIAL, the classes
    in `tieClassesOvl`' order (`account`, `account_sizes`, `account_classes`); the no-direction
    class holds exactly the sentences that apply a symbol Γ lacks (`account_absent`,
    `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 211 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes
    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's
    condition (`owed_rules`, `owed_clauses`), so Γ with the step's closure has a model for every
    H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (32): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (30): entailed by Γ (`cons_entailed`).
  - Overload axioms (101): entailed by Γ, whose overload equation states each at every
    element (`ovleq_entailed`).
  - Sentences of a function-overloaded symbol (57, the `functional` sentence of `LblcapGas`; 58, the
    same-constructor sentence of `LblcapGas`), weaker under overloadFunction, listed apart
    (`ovlFnApart`): Γ holds each at the arguments no overload covers only. Part 1, for every H: in a
    model of Γ the sentence, with the `functional` sentence it is joint with, entails Γ's item at
    uncovered arguments (`ovlfn_text_<i>`, `ovlfn_entails_item_<i>`), which is Γ's
    (`ovlfn_item_in_gamma_<i>`). Part 2, what it says at covered arguments, by hand: owed under a
    hypothesis on H (57, 58; `OvlFnHyp<i>`, `ovlfn_hyp_at_values_<i>`, with an H at which it holds,
    `ovlfn_hyp_holds_<i>`, and one at which it fails, `ovlfn_hyp_fails_<i>`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 8 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (49): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (21);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunPartial

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-partial.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-partial.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-partial.kompile.kore" module "E5-OVL-FUN-PARTIAL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E5-OVL-FUN-PARTIAL")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 152 := by decide +kernel

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

/-- Per class of the tie (`tieClassesOvl`: `tieClasses` with the class overload equation), the
indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [103, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
      125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [24, 26, 28, 30, 78, 79, 86, 88]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]),
   ("injectivity", [25, 27, 29, 31]),
   ("distinctness", [87]),
   ("no junk", [89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]),
   ("function functional", [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]),
   ("hooked functional", [21, 22, 23, 32, 33, 34, 35, 36, 37, 40, 44, 52, 53, 54, 55, 56, 60, 77, 80, 81, 82, 83, 84]),
   ("collection law", [41, 42, 43, 45, 46, 47, 48, 50, 51]),
   ("library", [102, 154]),
   ("set idempotence", [49]),
   ("set-variable lemma", [155]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("overload equation", [101]),
   ("no direction", [38, 39, 59, 85, 104, 105, 106, 107, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
      150, 151, 152, 153])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences of a function-overloaded symbol (its `functional` sentence and its no-confusion
sentences), which Γ holds at the arguments no overload covers only: weaker under overloadFunction,
in no class. -/
def ovlFnApart : List Nat := [57, 58]

/-- **The account**: the class lists and the sentences of a function-overloaded symbol partition the
user module's sentences. Their concatenation is a permutation of the sentences' indices, which are
distinct, so each sentence is in one class or among those of a function-overloaded symbol, and there
once. -/
theorem account : (classes.flatMap (·.2) ++ ovlFnApart).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 32), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 8), ("subsort", 17), ("injectivity", 4), ("distinctness", 1), ("no junk", 12), ("function functional", 16), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("overload equation", 1), ("no direction", 23)] := by
  decide +kernel

/-- The classes are the tie's for a text with a sentence of an overloading symbol (`tieClassesOvl`,
which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClassesOvl.map (·.1) := by decide +kernel

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
  [(139, "Bool"), (140, "Gas"), (141, "GeneratedCounterCell"), (142, "GeneratedCounterCellOpt"),
   (143, "GeneratedTopCell"), (144, "GeneratedTopCellFragment"), (145, "Int"), (146, "K"),
   (147, "KCell"), (148, "KCellOpt"), (149, "KItem"), (150, "List"), (151, "Map"), (152, "N"),
   (153, "Set")]

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
  [(14, "subsort"), (16, "subsort"), (19, "subsort"), (62, "function functional"),
   (75, "function functional"), (86, "constructor functional"), (87, "distinctness"),
   (88, "constructor functional"), (90, "no junk"), (99, "no junk"), (100, "no junk"),
   (101, "overload equation"), (103, "function equation"), (107, "no direction"),
   (110, "function equation"), (111, "function equation"), (135, "function equation"),
   (136, "function equation"), (140, "no direction"), (152, "no direction"),
   (155, "set-variable lemma")]

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

/-- Next's arity at the configuration sort, which Γ states whatever the text. -/
noncomputable def nextItem : Item := KoreAML.nextArityItem [] (srtOf c topCellSort)

/-- No sentence of the text has a `\rewrites` or a `\next`, so the text's signature states the
arity of next at no sort. -/
theorem text_nextless : kore.axiomDecls.all (fun ad => (nextSortsOf ad.ax.pattern).isEmpty) = true := by
  decide +kernel

/-- The item has an origin in the text, or is next's arity at the configuration sort. -/
noncomputable def sigFromN (it : Item) : Bool := sigFrom it || it.pat == nextItem.pat

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFromN = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 13).all sigFromN = true := by decide +kernel
theorem sigE_47 : (((sigItems c).drop 47).take 13).all sigFromN = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFromN = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFromN = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFromN = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFromN = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFromN = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFromN = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFromN = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFromN = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFromN = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFromN = true := by decide +kernel
theorem sigE_190 : (((sigItems c).drop 190).take 13).all sigFromN = true := by decide +kernel
theorem sigE_203 : ((sigItems c).drop 203).all sigFromN = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 211 := by decide +kernel

/-- **Every item of Γ's signature but next's arity has its origin**: the item of a declaration of
the text, or the sort constant of a registry sort or the arity of an interpreted hooked symbol that
the text does not declare at that shape. Next's arity at the configuration sort has none: the
text has no rule (`text_nextless`). -/
theorem sig_origin_but_next : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it ||
      it.pat == nextItem.pat) = true :=
  tieAllE_whole (p := sigFromN) <|
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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 91, 60, 4, 27) := by
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

/-! ## Consistency for every H -/

def callOrder : List Nat := [
388]

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
def fnFunIdx : List Nat := [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]

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

/-! ## Function equations (32 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 32 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax103, U.ax122, U.ax130, U.ax129, U.ax128, U.ax127, U.ax134, U.ax133, U.ax138, U.ax137,
   U.ax132, U.ax131, U.ax109, U.ax108, U.ax121, U.ax120, U.ax117, U.ax116, U.ax119, U.ax118,
   U.ax124, U.ax123, U.ax126, U.ax125, U.ax113, U.ax112, U.ax115, U.ax114, U.ax111, U.ax110,
   U.ax136, U.ax135]

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

theorem nj89 : (trS U.ax89).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj95 : (trS U.ax95).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj98 : (trS U.ax98).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax89, U.ax95, U.ax98], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj89]; exact orTopBot_valid hD rfl
  · rw [nj95]; exact orTopBot_valid hD rfl
  · rw [nj98]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax90, U.ax91, U.ax92, U.ax93, U.ax94, U.ax96, U.ax97, U.ax100],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax90, U.ax91, U.ax92, U.ax93, U.ax94, U.ax96, U.ax97, U.ax100],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax99).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (99)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax99).pat := by
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
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30,
   U.ax31, U.ax78, U.ax79, U.ax86, U.ax87, U.ax88]

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

/-! ## The overload axioms -/

/-- The sentences of the class overload equation, in text order. -/
noncomputable def ovlEqText : List AxiomDecl :=
  [U.ax101]

theorem ovleq_account : (classOf "overload equation").isPerm (ovlEqText.map (·.index)) = true := by
  decide +kernel

/-- Each is an overload axiom of the semantics: of an overloading symbol over a symbol it overloads,
in the form `tieOvlEq_entailed` reads (`tieOvlEqB`; kernel). -/
theorem ovleq_checked : ovlEqText.all (fun ad => tieOvlEqB c ad.ax) = true := by decide +kernel

theorem ovleq_trS : ovlEqText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the overload axioms**: Γ entails each, for every H. Γ's overload equation states, at
every element of the overloaded symbol's argument sorts, that the overloading symbol applied to
their lifts is the lift of the overloaded symbol applied to them (`tieOvlEq_entailed`). -/
theorem ovleq_entailed (H : HookParams) : ∀ ad ∈ ovlEqText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp ovleq_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieOvlEq_entailed (c := cH H) (a := ad.ax)
    ((tieOvlEqB_withHooks c H ad.ax).trans (List.all_eq_true.mp ovleq_checked ad had)) ad.index ad.module hI

/-! ## Sentences of a function-overloaded symbol (57, 58): weaker under
overloadFunction, listed apart

Γ holds each sentence at the arguments no overload of its generator covers only (Γ's items
`funUncItem`, `injUncItem`, `distUncItem`). This section states what holds for every H on every
text: the sentence entails that item in a model of Γ, the same-constructor and
different-constructors sentences with the `functional` sentence of their function-overloaded
generator. What a sentence says at covered arguments is the next section's, by hand. -/

/-- The sentences of `ovlFnApart`, in text order. -/
noncomputable def ovlFnText : List AxiomDecl :=
  [U.ax57, U.ax58]

theorem ovlfn_index : ovlFnText.map (·.index) = ovlFnApart := by decide +kernel

/-- The generator `LblcapGas`. -/
def ovlFnGen0 : Gen := .ctor ⟨389, [32], 32⟩

/-- The sorts of these generators are the semantics' sorts, named: -/
theorem ovlfn_sorts : 32 < nRegSorts + c.sortNames.length := by decide +kernel
theorem ovlfn_sort_names : c.sortName 32 = "Gas" := by decide +kernel

/-- Γ holds the G-arity item of each generator whose `functional` sentence the others are joint
with (`tieOvlFnArityB`). -/
theorem ovlfn_arity_0 : tieOvlFnArityB c 32 ovlFnGen0 = true := by decide +kernel

/-- Sentence 57 is the `functional` sentence of `LblcapGas` of Gas. -/
theorem ovlfn_text_57 : tieOvlFnFunAtB c 32 ovlFnGen0 U.ax57.ax = true := by decide +kernel
theorem ovlfn_trS_57 : (trS U.ax57).pat = (trAxiom [] [] U.ax57).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_57 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnFun_item_withHooks ovlfn_text_57 H

/-- **In a model of Γ, sentence 57 entails that item**, for every H. -/
theorem ovlfn_entails_item_57 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (h : I ⊧ᴵ (trS U.ax57).pat) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_57] at h
  exact tieOvlFnFun_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57) ovlfn_sorts
    ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) h _

/-- Sentence 58 is the same-constructor sentence of `LblcapGas` of Gas, joint with the `functional` sentence 57. -/
theorem ovlfn_text_58 : tieOvlFnInjAtB c 32 ovlFnGen0 U.ax58.ax = true := by decide +kernel
theorem ovlfn_trS_58 : (trS U.ax58).pat = (trAxiom [] [] U.ax58).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_58 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnInj_item_withHooks ovlfn_text_58 H

/-- **In a model of Γ, sentence 58 with sentence 57 entails that item**, for every H. -/
theorem ovlfn_entails_item_58 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax57).pat) (h : I ⊧ᴵ (trS U.ax58).pat) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_57] at hf
  rw [ovlfn_trS_58] at h
  exact tieOvlFnInj_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57)
    ((tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_58) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _

/-! ## Sentences of a function-overloaded symbol: the covered part (by hand)

The text: `N ::= z | y`, `Gas ::= N | cap(Gas) [symbol(capGas), overload(cap)]`,
`N ::= cap(N) [function, symbol(capN), overload(cap)]` (not total), `rule cap(z) => z`. `capN`'s
one clause fails at `y`, so `capN(y)` is its rest, the interpretation's value, and
`capGas(inj y)` is that value lifted. What the two sentences say at the covered arguments is
therefore a condition on H, and neither holds nor fails for every H:

- sentence 57 is owed under `OvlFnHyp57` (`OvlFnTotal`: `capN` has a value at `y`). It holds at
  every H whose rest gives `capN` a value at `[y]` (`ofp_total`; `ofpHy`, `ofpHz`) and fails at
  `HookParams.none`, where no model of Γ satisfies the sentence;
- sentence 58 is owed under `OvlFnHyp58` (`OvlFnInj`: the values of `capGas(inj z)` and
  `capGas(inj y)` differ). It holds at `ofpHy`, whose rest is `y`, and fails at `ofpHz`, whose
  rest is `z`: there `capGas(inj y)` and `capGas(inj z)` are both `inj z`, and no model of Γ
  satisfies the sentence.

Under each hypothesis its sentence holds at values in every model of Γ, which is the theory of
the statements here: the definition reads no confined sort (`readsConfined_c`). Γ has a model at
every H (`consistent`), so no refutation below is vacuous. -/

def ofpGasS : Srt := 32
def ofpNS : Srt := 33
def ofpYS : Sym := 386
def ofpZS : Sym := 387
def ofpCapN : Sym := 388
def ofpCapGas : Sym := 389

theorem ofp_names : c.sortName ofpGasS = "Gas" ∧ c.sortName ofpNS = "N" ∧ c.symName ofpYS = "Lbly" ∧
    c.symName ofpZS = "Lblz" ∧ c.symName ofpCapN = "LblcapN" ∧ c.symName ofpCapGas = "LblcapGas" := by decide +kernel

/-- `capN(z #as G0) = G0`. -/
def ofpCl : Clause := { vars := [ofpNS], pats := [.as (.app ofpZS []) 0], req := none, rhs := .var 0, ens := none }
/-- `capN : N → N`, not total. -/
def ofpCapNFn : Fn := ⟨ofpCapN, [ofpNS], ofpNS, [ofpCl], false⟩
def ofpCapNSig : CtorSig := ⟨ofpCapN, [ofpNS], ofpNS⟩
def ofpZSig : CtorSig := ⟨ofpZS, [], ofpNS⟩
def ofpYSig : CtorSig := ⟨ofpYS, [], ofpNS⟩
/-- `capGas` overloads `capN`. -/
def ofpCap : OvlSig := ⟨⟨ofpCapGas, [ofpGasS], ofpGasS⟩, [ofpCapN]⟩

def ofpZT : GroundTerm := .ctor ofpZS []
def ofpYT : GroundTerm := .ctor ofpYS []
/-- `inj{N, Gas}(z)` -/
def ofpInjZ : GroundTerm := .inj ofpNS ofpGasS ofpZT
/-- `inj{N, Gas}(y)` -/
def ofpInjY : GroundTerm := .inj ofpNS ofpGasS ofpYT

/-- The interpretation whose rest of `capN` is `y`. -/
def ofpHy : HookParams := ⟨fun f _ => if f = ofpCapN then some ofpYT else none⟩
/-- The interpretation whose rest of `capN` is `z`. -/
def ofpHz : HookParams := ⟨fun f _ => if f = ofpCapN then some ofpZT else none⟩

kernel_rfl ofp_fns : c.fns = [ofpCapNFn]
kernel_rfl ofp_ovls : c.ovls = [ofpCap]
kernel_rfl ofp_lookup : ∀ H : HookParams, (cH H).lookupOvl ofpCap.sig.name = some ofpCap
kernel_rfl ofp_lookupFn : ∀ H : HookParams, (cH H).lookupFn ofpCapN = some ofpCapNFn
kernel_rfl ofp_over : ∀ H : HookParams, (cH H).ovlOver ofpCap = [ofpCapNSig]
kernel_rfl ofp_lifted : ∀ H : HookParams,
  ((cH H).ovlOver ofpCap).all (fun kg => (cH H).ovlByFn kg && kg.result != ofpCap.sig.result) = true
kernel_rfl ofp_toK : ∀ H : HookParams, Gen.toK (cH H) (.ctor ofpCap.sig) = Gen.toK c ovlFnGen0
kernel_rfl ofp_isCtor_z : ∀ H : HookParams, (cH H).isCtor ofpZS = true
kernel_rfl ofp_sort_z : ∀ H : HookParams, (cH H).sortOf ofpZT = some ofpNS
kernel_rfl ofp_sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [ofpInjZ] = some ofpCap.sig.args
kernel_rfl ofp_sorts_injY : ∀ H : HookParams, (cH H).sortsOf [ofpInjY] = some ofpCap.sig.args
-- `capN` covers `inj z` and `inj y`.
kernel_rfl ofp_cover_z : ∀ H : HookParams, (cH H).fnCover ofpCap.sig.name [ofpInjZ] = some ofpCapNSig
kernel_rfl ofp_cover_y : ∀ H : HookParams, (cH H).fnCover ofpCap.sig.name [ofpInjY] = some ofpCapNSig
kernel_rfl ofp_rest_Hy : (cH ofpHy).fnRest ofpCapNFn [ofpYT] = some ofpYT
kernel_rfl ofp_rest_Hz : (cH ofpHz).fnRest ofpCapNFn [ofpYT] = some ofpZT

/-- The theory of every H is Γ. -/
theorem ofp_plain (H : HookParams) : Γc (cH H) = Γ (cH H) :=
  Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)

/-- Evaluation is functional, for every H. -/
theorem ofp_coherent (H : HookParams) : CoherentAll (cH H) := CoherentAll_of (hyp_of_fnHyp (coreOKH H) (fnHypH H))

theorem ofp_fun_shape (H : HookParams) :
    tieOvlFnFunShapeB (cH H) ofpCap.sig.result (Gen.toK (cH H) (.ctor ofpCap.sig)) U.ax57.ax = true := by
  have h := ovlfn_text_57
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  rw [ofp_toK H]
  exact (tieOvlFnFunShapeB_withHooks c H _ _ _).trans h.1.2

theorem ofp_inj_shape (H : HookParams) :
    tieOvlFnInjShapeB (cH H) ofpCap.sig.result (Gen.toK (cH H) (.ctor ofpCap.sig)) U.ax58.ax = true := by
  have h := ovlfn_text_58
  simp only [tieOvlFnInjAtB, Bool.and_eq_true] at h
  rw [ofp_toK H]
  exact (tieOvlFnInjShapeB_withHooks c H _ _ _).trans h.1.2

/-! ### The values of N, and `capN` at them -/

/-- A sort that is no carrier of literals has none. -/
theorem ofp_noLit {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

/-- A sort whose generators are two constants holds those two only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem ofp_twoConst {c : Semantics} {s : Srt} {k0 k1 : CtorSig} (ha0 : k0.args = []) (ha1 : k1.args = [])
    (hk : ∀ k ∈ c.ctorSigs, k.result = s → k = k0 ∨ k = k1)
    (ho : ∀ o ∈ c.ovls, o.sig.result ≠ s)
    (hp : ∀ k ∈ c.params, k.raw = false)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s)
    (hdv : ∀ lit, dvOK c.lib s lit = false)
    (hcoll : c.collOf s = none)
    {v : GroundTerm} (h : c.sortOf v = some s) : v = .ctor k0.name [] ∨ v = .ctor k1.name [] := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk', hs, hr⟩ | ⟨-, o, hlo, -, -, hr⟩ | ⟨-, -, k, hko, -⟩
    · obtain ⟨hm, hn⟩ := lookupSig_spec hk'
      rcases hk k hm hr.symm with rfl | rfl
      · rw [ha0] at hs
        rw [sortsOf_inv_nil hs, hn]; exact .inl rfl
      · rw [ha1] at hs
        rw [sortsOf_inv_nil hs, hn]; exact .inr rfl
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec hlo
      exact absurd hr.symm (ho o (he ▸ List.getElem_mem hi))
    · obtain ⟨hm, hraw, -⟩ := Semantics.lookupOpen_spec _ hko
      rw [hp k hm] at hraw; cases hraw
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact absurd rfl (hsub _ (List.contains_iff_mem.mp hc.1.1))
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc; cases h; rw [hdv lit] at hc; cases hc
    · cases h
  | map s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_map_sort h
    rw [hcoll] at hc; cases hc
  | set s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_set_sort h
    rw [hcoll] at hc; cases hc
  | list s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_list_sort h
    rw [hcoll] at hc; cases hc

/-- **N holds `z` and `y` only**, for every H. -/
theorem ofp_val_N (H : HookParams) {v : GroundTerm} (h : (cH H).sortOf v = some ofpNS) : v = ofpZT ∨ v = ofpYT := by
  rw [Semantics.sortOf_withHooks _ _ noRaw] at h
  exact ofp_twoConst (k0 := ofpZSig) (k1 := ofpYSig) rfl rfl (by decide +kernel) (by decide +kernel) noRaw
    (by decide +kernel) (ofp_noLit (by decide +kernel)) (by decide +kernel) h

/-- **`capN(z)` evaluates to `z`**, by its one clause, for every H. -/
theorem ofp_eval_z (H : HookParams) : Eval (cH H) ofpCapN [ofpZT] (some ofpZT) :=
  .clause (fn := ofpCapNFn) (cl := ofpCl) (σ := [(0, ofpZT)]) (ofp_lookupFn H) (List.mem_singleton_self _)
    (fun i s' h => by
      cases i with
      | zero => cases h; exact ⟨ofpZT, rfl, ofp_sort_z H⟩
      | succ i => simp [ofpCl] at h)
    (.cons (.as (.ctor (ofp_isCtor_z H) .nil) rfl) .nil) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      rw [show ofpCapNFn.clauses = [ofpCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => by cases ht) .top

theorem ofp_hook_z : patternHooks.contains ofpZS = false := by decide

/-- The pattern of `z` denotes `z` only. -/
theorem ofp_patVal_z {H : HookParams} {σ : Subst} {v : GroundTerm} (h : PatVal (cH H) σ (.app ofpZS []) v) :
    v = ofpZT := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => rw [ofp_hook_z] at hp; cases hp
  | coll hc _ _ _ => rw [ofp_isCtor_z H] at hc; cases hc
  | ovl hc _ _ _ => rw [ofp_isCtor_z H] at hc; cases hc

/-- `capN`'s one clause fails at `y`: its pattern `z #as G0` does not denote `y`. -/
theorem ofp_fails_y (H : HookParams) : ∀ cl ∈ ofpCapNFn.clauses, Fails (cH H) [ofpYT] cl := by
  intro cl hcl
  rw [show ofpCapNFn.clauses = [ofpCl] from rfl, List.mem_singleton] at hcl
  subst hcl
  exact .intro fun σ _ hp => by
    cases hp with
    | cons h _ =>
      cases h with
      | as h' _ => exact absurd (ofp_patVal_z h') (by simp [ofpYT, ofpZT, ofpYS, ofpZS])

/-- **`capN(y)` is its rest**, the interpretation's value, for every H. -/
theorem ofp_eval_y (H : HookParams) : Eval (cH H) ofpCapN [ofpYT] ((cH H).fnRest ofpCapNFn [ofpYT]) :=
  .rest (ofp_lookupFn H) (ofp_fails_y H)

/-- **A value list `capN` covers is `[inj z]` or `[inj y]`**: the covering function is `capN`, and
the list is the lift of its stripped argument, a value of N. -/
theorem ofp_covered (H : HookParams) {us : List GroundTerm} {kg : CtorSig}
    (hus : (cH H).sortsOf us = some ofpCap.sig.args) (hc : (cH H).fnCover ofpCap.sig.name us = some kg) :
    kg = ofpCapNSig ∧ ∃ x, (x = ofpZT ∨ x = ofpYT) ∧ stripAll ofpCapNSig.args ofpCap.sig.args us = [x] ∧
      us = [lift ofpNS ofpGasS x] := by
  obtain ⟨o', ho', hkg, -, hcv⟩ := OvlLaws.fnCover_some_parts hc
  rw [ofp_lookup H] at ho'
  cases ho'
  rw [ofp_over H, List.mem_singleton] at hkg
  subst hkg
  obtain ⟨u, us', rfl, hu, hnil⟩ := sortsOf_inv_cons hus
  cases sortsOf_inv_nil hnil
  have hl : (cH H).lies ofpNS ofpGasS u = true := by
    have := (OvlLaws.covers_iff.mp hcv).2.2
    simpa [ofpCap, ofpCapNSig] using this
  exact ⟨rfl, strip ofpNS ofpGasS u, ofp_val_N H (OvlLaws.sortOf_strip hu hl), rfl,
    by rw [OvlLaws.lift_strip hu hl]⟩

/-! ### Sentence 57, the `functional` sentence of `capGas` -/

/-- **The hypothesis sentence 57 is owed under**: at every value list of Gas that `capN` covers,
`capN` has a value at the stripped arguments. -/
def OvlFnHyp57 (H : HookParams) : Prop := OvlFnTotal (cH H) ofpCap

/-- **Under `OvlFnHyp57`, sentence 57 holds at values** in every model of Γ. -/
theorem ovlfn_hyp_at_values_57 (H : HookParams) (h : OvlFnHyp57 H) :
    EntailsAtValues (cH H) U.ax57 (trS U.ax57).pat := by
  intro M inst I hI
  rw [ovlfn_trS_57]
  exact ovlFnTotal_atValues (coreOKH H) (fnHypH H) (ofp_lookup H) h (ofp_fun_shape H) M inst I
    (by rw [ofp_plain H]; exact hI)

/-- `OvlFnHyp57` at every H whose rest gives `capN` a value at `[y]`: `capN` has the value `z` at
`z`, the other value of N. -/
theorem ofp_total (H : HookParams) {w : GroundTerm} (hr : (cH H).fnRest ofpCapNFn [ofpYT] = some w) :
    OvlFnHyp57 H := by
  intro vs kg hvs hcov
  obtain ⟨rfl, x, hx, hst, -⟩ := ofp_covered H hvs hcov
  rw [hst]
  rcases hx with rfl | rfl
  · exact ⟨_, ofp_eval_z H⟩
  · exact ⟨w, hr ▸ ofp_eval_y H⟩

/-- **`OvlFnHyp57` holds at `ofpHy`**, where Γ has a model. -/
theorem ovlfn_hyp_holds_57 : OvlFnHyp57 ofpHy ∧ Consistent (cH ofpHy) := ⟨ofp_total _ ofp_rest_Hy, consistent _⟩

/-- At `HookParams.none`, `capGas(inj y)` has no value: `capN` covers `inj y` and has none at `y`. -/
theorem ofp_res_none : OvlFnRes (cH HookParams.none) ofpCap [ofpInjY] none := by
  have h := OvlFnRes.fn (ofp_cover_y HookParams.none) (ofp_eval_y HookParams.none)
  rw [Semantics.fnRest_withHooks_none] at h
  exact h

/-- **`OvlFnHyp57` fails at `HookParams.none`**, where Γ has a model and no model of Γ satisfies
sentence 57: read at `K0 := inj y`, the sentence makes `capGas(inj y)` one element of Gas, which
Γ leaves empty. -/
theorem ovlfn_hyp_fails_57 : ¬ OvlFnHyp57 HookParams.none ∧ Consistent (cH HookParams.none) ∧
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH HookParams.none) → ¬ (I ⊧ᴵ (trS U.ax57).pat) := by
  refine ⟨fun h => ?_, consistent _, fun M inst I hI => ?_⟩
  · obtain ⟨v, hv⟩ := h [ofpInjY] _ (ofp_sorts_injY _) (ofp_cover_y _)
    have h2 := ofp_eval_y HookParams.none
    rw [Semantics.fnRest_withHooks_none] at h2
    cases Eval.functional (ofp_coherent _) hv h2
  · rw [ovlfn_trS_57]
    exact ovlFnTotal_refuted (coreOKH _) (fnHypH _) (ofp_lookup _) (ofp_fun_shape _) (ofp_sorts_injY _)
      ofp_res_none (ofp_sort_z _) M inst I (by rw [ofp_plain]; exact hI)

/-! ### Sentence 58, the same-constructor sentence of `capGas` -/

/-- **The hypothesis sentence 58 is owed under**: two value lists of Gas at which the application
of `capGas` has one and the same value are equal. -/
def OvlFnHyp58 (H : HookParams) : Prop := OvlFnInj (cH H) ofpCap

/-- **Under `OvlFnHyp58`, sentence 58 holds at values** in every model of Γ. -/
theorem ovlfn_hyp_at_values_58 (H : HookParams) (h : OvlFnHyp58 H) :
    EntailsAtValues (cH H) U.ax58 (trS U.ax58).pat := by
  intro M inst I hI
  rw [ovlfn_trS_58]
  exact ovlFnInj_atValues (coreOKH H) (fnHypH H) (ofp_lookup H) h (ofp_inj_shape H) M inst I
    (by rw [ofp_plain H]; exact hI)

/-- At `ofpHy`, `capN` is the identity at the values of N. -/
theorem ofp_id_Hy {x v : GroundTerm} (hx : x = ofpZT ∨ x = ofpYT) (he : Eval (cH ofpHy) ofpCapN [x] (some v)) :
    v = x := by
  rcases hx with rfl | rfl
  · exact Option.some.inj (Eval.functional (ofp_coherent _) he (ofp_eval_z _))
  · have h2 := ofp_eval_y ofpHy
    rw [ofp_rest_Hy] at h2
    exact Option.some.inj (Eval.functional (ofp_coherent _) he h2)

/-- **`OvlFnHyp58` holds at `ofpHy`**, where Γ has a model: an uncovered application is its own
value, no injection, and the value of a covered one is its argument, `capN` being the identity. -/
theorem ovlfn_hyp_holds_58 : OvlFnHyp58 ofpHy ∧ Consistent (cH ofpHy) :=
  ⟨ovlFnInj_of_cov (ofp_lookup _) (ofp_lifted _) fun us vs kg kg' v v' hus hvs hc hc' he he' hl => by
    obtain ⟨rfl, x, hx, hst, rfl⟩ := ofp_covered _ hus hc
    obtain ⟨rfl, x', hx', hst', rfl⟩ := ofp_covered _ hvs hc'
    rw [hst] at he
    rw [hst'] at he'
    cases ofp_id_Hy hx he
    cases ofp_id_Hy hx' he'
    exact congrArg (fun t => [t]) hl, consistent _⟩

/-- At `ofpHz`, `capGas(inj z)` has the value `inj z`: `capN(z)` is `z`. -/
theorem ofp_res_injZ : OvlFnRes (cH ofpHz) ofpCap [ofpInjZ] (some ofpInjZ) :=
  OvlFnRes.fn (ofp_cover_z ofpHz) (ofp_eval_z ofpHz)

/-- At `ofpHz`, `capGas(inj y)` has the value `inj z` too: `capN(y)` is its rest, `z`. -/
theorem ofp_res_injY : OvlFnRes (cH ofpHz) ofpCap [ofpInjY] (some ofpInjZ) := by
  have h := OvlFnRes.fn (ofp_cover_y ofpHz) (ofp_eval_y ofpHz)
  rw [ofp_rest_Hz] at h
  exact h

/-- **`OvlFnHyp58` fails at `ofpHz`**, where Γ has a model and no model of Γ satisfies sentence
58: `capGas(inj z)` and `capGas(inj y)` hold one element, and the sentence then makes `inj z` and
`inj y` equal. -/
theorem ovlfn_hyp_fails_58 : ¬ OvlFnHyp58 ofpHz ∧ Consistent (cH ofpHz) ∧
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH ofpHz) → ¬ (I ⊧ᴵ (trS U.ax58).pat) := by
  have hne : [ofpInjZ] ≠ [ofpInjY] := by simp [ofpInjZ, ofpInjY, ofpZT, ofpYT, ofpZS, ofpYS]
  refine ⟨fun h => hne (h _ _ _ (ofp_sorts_injZ _) (ofp_sorts_injY _) ofp_res_injZ ofp_res_injY), consistent _,
    fun M inst I hI => ?_⟩
  rw [ovlfn_trS_58]
  exact ovlFnInj_refuted (coreOKH _) (fnHypH _) (ofp_lookup _) (ofp_inj_shape _) (ofp_sorts_injZ _)
    (ofp_sorts_injY _) hne ofp_res_injZ ofp_res_injY M inst I (by rw [ofp_plain]; exact hI)

/-! ### The two interpretations -/

/-- **At `ofpHy`, whose rest gives `capN(y) = y`, Γ has a model and both sentences hold at values**
in every model of Γ. -/
theorem ovlfn_holds_Hy : (cH ofpHy).fnRest ofpCapNFn [ofpYT] = some ofpYT ∧ Consistent (cH ofpHy) ∧
    EntailsAtValues (cH ofpHy) U.ax57 (trS U.ax57).pat ∧ EntailsAtValues (cH ofpHy) U.ax58 (trS U.ax58).pat :=
  ⟨ofp_rest_Hy, consistent _, ovlfn_hyp_at_values_57 _ ovlfn_hyp_holds_57.1,
    ovlfn_hyp_at_values_58 _ ovlfn_hyp_holds_58.1⟩

/-- **At `ofpHz`, whose rest gives `capN(y) = z`, Γ has a model, sentence 57 holds at values and no
model of Γ satisfies sentence 58**: the two hypotheses are independent. -/
theorem ovlfn_against_Hz : (cH ofpHz).fnRest ofpCapNFn [ofpYT] = some ofpZT ∧ Consistent (cH ofpHz) ∧
    EntailsAtValues (cH ofpHz) U.ax57 (trS U.ax57).pat ∧
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH ofpHz) → ¬ (I ⊧ᴵ (trS U.ax58).pat) :=
  ⟨ofp_rest_Hz, consistent _, ovlfn_hyp_at_values_57 _ (ofp_total _ ofp_rest_Hz), ovlfn_hyp_fails_58.2.2⟩

/-- info: 'KCore.TieE5OvlFunPartial.ovlfn_holds_Hy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovlfn_holds_Hy
/-- info: 'KCore.TieE5OvlFunPartial.ovlfn_against_Hz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovlfn_against_Hz
/-- info: 'KCore.TieE5OvlFunPartial.ovlfn_hyp_fails_57' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovlfn_hyp_fails_57

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax49.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax49).pat = (trAxiom [] [] U.ax49).pat := by decide +kernel

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
theorem idem_vars : (U.ax49.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax49.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax49.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 49 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax49).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax49.ax.sortVars U.ax49.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax49.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax49.ax.pattern).eraseDups,
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


/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; the text has no rule, so Γ has no rule item; everything else is one of the five parts
defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl ⟨ad, had, he⟩))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))

end KCore.TieE5OvlFunPartial

#check @KCore.TieE5OvlFunPartial.noRaw
#check @KCore.TieE5OvlFunPartial.readsConfined_c
#check @KCore.TieE5OvlFunPartial.userAxioms_eq
#check @KCore.TieE5OvlFunPartial.coreOK
#check @KCore.TieE5OvlFunPartial.wf_defn
#check @KCore.TieE5OvlFunPartial.account
#check @KCore.TieE5OvlFunPartial.account_sizes
#check @KCore.TieE5OvlFunPartial.account_classes
#check @KCore.TieE5OvlFunPartial.account_absent
#check @KCore.TieE5OvlFunPartial.absent_closed
#check @KCore.TieE5OvlFunPartial.absent_proj_below_c
#check @KCore.TieE5OvlFunPartial.absent_proj_below
#check @KCore.TieE5OvlFunPartial.lists_in_account
#check @KCore.TieE5OvlFunPartial.attrs_agree
#check @KCore.TieE5OvlFunPartial.sig_origin_but_next
#check @KCore.TieE5OvlFunPartial.decls_entailed
#check @KCore.TieE5OvlFunPartial.consistent
#check @KCore.TieE5OvlFunPartial.fnFun_indices
#check @KCore.TieE5OvlFunPartial.fnFun_account
#check @KCore.TieE5OvlFunPartial.fnFun_checked
#check @KCore.TieE5OvlFunPartial.fnFun_trS
#check @KCore.TieE5OvlFunPartial.fnFun_at_values
#check @KCore.TieE5OvlFunPartial.fnFun_at_values_step
#check @KCore.TieE5OvlFunPartial.text_nextless
#check @KCore.TieE5OvlFunPartial.fn_shape
#check @KCore.TieE5OvlFunPartial.fns_account
#check @KCore.TieE5OvlFunPartial.fns_entailed
#check @KCore.TieE5OvlFunPartial.fns_from_text
#check @KCore.TieE5OvlFunPartial.fn_prios
#check @KCore.TieE5OvlFunPartial.nojunk_trivial_entailed
#check @KCore.TieE5OvlFunPartial.nojunk_items_entailed
#check @KCore.TieE5OvlFunPartial.nojunk_kitem_entailed
#check @KCore.TieE5OvlFunPartial.cons_entailed
#check @KCore.TieE5OvlFunPartial.ovleq_account
#check @KCore.TieE5OvlFunPartial.ovleq_entailed
#check @KCore.TieE5OvlFunPartial.ovlfn_index
#check @KCore.TieE5OvlFunPartial.ovlfn_text_57
#check @KCore.TieE5OvlFunPartial.ovlfn_item_in_gamma_57
#check @KCore.TieE5OvlFunPartial.ovlfn_entails_item_57
#check @KCore.TieE5OvlFunPartial.ovlfn_text_58
#check @KCore.TieE5OvlFunPartial.ovlfn_item_in_gamma_58
#check @KCore.TieE5OvlFunPartial.ovlfn_entails_item_58
#check @KCore.TieE5OvlFunPartial.OvlFnHyp57
#check @KCore.TieE5OvlFunPartial.ovlfn_hyp_at_values_57
#check @KCore.TieE5OvlFunPartial.ovlfn_hyp_holds_57
#check @KCore.TieE5OvlFunPartial.ovlfn_hyp_fails_57
#check @KCore.TieE5OvlFunPartial.OvlFnHyp58
#check @KCore.TieE5OvlFunPartial.ovlfn_hyp_at_values_58
#check @KCore.TieE5OvlFunPartial.ovlfn_hyp_holds_58
#check @KCore.TieE5OvlFunPartial.ovlfn_hyp_fails_58
#check @KCore.TieE5OvlFunPartial.idem_refuted
#check @KCore.TieE5OvlFunPartial.gamma_origin
#check @KCore.TieE5OvlFunPartial.gamma_from
#check @KCore.TieE5OvlFunPartial.owed_rules
#check @KCore.TieE5OvlFunPartial.owed_clauses
#check @KCore.TieE5OvlFunPartial.openDecidedH
#print axioms KCore.TieE5OvlFunPartial.noRaw
#print axioms KCore.TieE5OvlFunPartial.readsConfined_c
#print axioms KCore.TieE5OvlFunPartial.userAxioms_eq
#print axioms KCore.TieE5OvlFunPartial.coreOK
#print axioms KCore.TieE5OvlFunPartial.wf_defn
#print axioms KCore.TieE5OvlFunPartial.account
#print axioms KCore.TieE5OvlFunPartial.account_sizes
#print axioms KCore.TieE5OvlFunPartial.account_classes
#print axioms KCore.TieE5OvlFunPartial.account_absent
#print axioms KCore.TieE5OvlFunPartial.absent_closed
#print axioms KCore.TieE5OvlFunPartial.absent_proj_below_c
#print axioms KCore.TieE5OvlFunPartial.absent_proj_below
#print axioms KCore.TieE5OvlFunPartial.lists_in_account
#print axioms KCore.TieE5OvlFunPartial.attrs_agree
#print axioms KCore.TieE5OvlFunPartial.sig_origin_but_next
#print axioms KCore.TieE5OvlFunPartial.decls_entailed
#print axioms KCore.TieE5OvlFunPartial.consistent
#print axioms KCore.TieE5OvlFunPartial.fnFun_indices
#print axioms KCore.TieE5OvlFunPartial.fnFun_account
#print axioms KCore.TieE5OvlFunPartial.fnFun_checked
#print axioms KCore.TieE5OvlFunPartial.fnFun_trS
#print axioms KCore.TieE5OvlFunPartial.fnFun_at_values
#print axioms KCore.TieE5OvlFunPartial.fnFun_at_values_step
#print axioms KCore.TieE5OvlFunPartial.text_nextless
#print axioms KCore.TieE5OvlFunPartial.fn_shape
#print axioms KCore.TieE5OvlFunPartial.fns_account
#print axioms KCore.TieE5OvlFunPartial.fns_entailed
#print axioms KCore.TieE5OvlFunPartial.fns_from_text
#print axioms KCore.TieE5OvlFunPartial.fn_prios
#print axioms KCore.TieE5OvlFunPartial.nojunk_trivial_entailed
#print axioms KCore.TieE5OvlFunPartial.nojunk_items_entailed
#print axioms KCore.TieE5OvlFunPartial.nojunk_kitem_entailed
#print axioms KCore.TieE5OvlFunPartial.cons_entailed
#print axioms KCore.TieE5OvlFunPartial.ovleq_account
#print axioms KCore.TieE5OvlFunPartial.ovleq_entailed
#print axioms KCore.TieE5OvlFunPartial.ovlfn_index
#print axioms KCore.TieE5OvlFunPartial.ovlfn_text_57
#print axioms KCore.TieE5OvlFunPartial.ovlfn_item_in_gamma_57
#print axioms KCore.TieE5OvlFunPartial.ovlfn_entails_item_57
#print axioms KCore.TieE5OvlFunPartial.ovlfn_text_58
#print axioms KCore.TieE5OvlFunPartial.ovlfn_item_in_gamma_58
#print axioms KCore.TieE5OvlFunPartial.ovlfn_entails_item_58
#print axioms KCore.TieE5OvlFunPartial.OvlFnHyp57
#print axioms KCore.TieE5OvlFunPartial.ovlfn_hyp_at_values_57
#print axioms KCore.TieE5OvlFunPartial.ovlfn_hyp_holds_57
#print axioms KCore.TieE5OvlFunPartial.ovlfn_hyp_fails_57
#print axioms KCore.TieE5OvlFunPartial.OvlFnHyp58
#print axioms KCore.TieE5OvlFunPartial.ovlfn_hyp_at_values_58
#print axioms KCore.TieE5OvlFunPartial.ovlfn_hyp_holds_58
#print axioms KCore.TieE5OvlFunPartial.ovlfn_hyp_fails_58
#print axioms KCore.TieE5OvlFunPartial.idem_refuted
#print axioms KCore.TieE5OvlFunPartial.gamma_origin
#print axioms KCore.TieE5OvlFunPartial.gamma_from
#print axioms KCore.TieE5OvlFunPartial.owed_rules
#print axioms KCore.TieE5OvlFunPartial.owed_clauses
#print axioms KCore.TieE5OvlFunPartial.openDecidedH
