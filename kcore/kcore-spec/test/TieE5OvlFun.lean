/-
  The tie (C14) on `f2-examples/e5-ovl-fun.kompile.kore`, the kompiled text of construct fixture e5-ovl-fun
  (`test/constructs/fixtures/e5-ovl-fun`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e5-ovl-fun`, its ovlfn section by hand; run from the package root:
  `lake env lean -j1 test/TieE5OvlFun.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists and the two sentences of a function-overloaded symbol, listed apart
    (`ovlFnApart`), partition the 261 sentences of the user module E5-OVL-FUN, the classes in
    `tieClassesOvl`' order (`account`, `account_sizes`, `account_classes`); the no-direction class
    holds exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 207 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes
    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's
    condition (`owed_rules`, `owed_clauses`), so Γ with the step's closure has a model for every
    H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (26): entailed by Γ (`cons_entailed`).
  - Overload axioms (124): entailed by Γ, whose overload equation states each at every
    element (`ovleq_entailed`).
  - Sentences of a function-overloaded symbol (104, the `functional` sentence of `LblplusExp`; 105,
    the same-constructor sentence of `LblplusExp`), weaker under overloadFunction, listed apart
    (`ovlFnApart`): Γ holds each at the arguments no overload covers only. Part 1, for every H: in a
    model of Γ the sentence, with the `functional` sentence it is joint with, entails Γ's item at
    uncovered arguments (`ovlfn_text_<i>`, `ovlfn_entails_item_<i>`), which is Γ's
    (`ovlfn_item_in_gamma_<i>`). Part 2, what it says at covered arguments, by hand: at values for
    every H (104; `ovlfn_at_values_<i>`); refuted for every H (105; `ovlFnRefuted`,
    `ovlfn_refuted_<i>`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (62): Γ with it has no model (`idem_refuted`).
  - Library sample, 164 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (11);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFun

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun.kompile.kore" module "E5-OVL-FUN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E5-OVL-FUN")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 261 := by decide +kernel

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
  [("function equation", [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
      230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 247]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 101, 102]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30]),
   ("distinctness", []),
   ("no junk", [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]),
   ("function functional", [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      57, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 77, 78, 79, 81, 98, 99, 100, 103, 106, 107, 108,
      109, 110]),
   ("collection law", [54, 55, 56, 58, 59, 60, 61, 63, 64]),
   ("library", [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
      148, 149, 150, 151, 152, 153, 154, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166,
      167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
      185, 186, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
      204, 205, 206, 207, 243, 244, 245, 246, 262, 263]),
   ("set idempotence", [62]),
   ("set-variable lemma", [125, 126, 127, 128, 129, 264]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("overload equation", [124]),
   ("no direction", [37, 41, 43, 74, 76, 80, 97, 111, 112, 155, 187, 208, 209, 210, 211, 241, 242, 248, 249, 250,
      251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences of a function-overloaded symbol (its `functional` sentence and its no-confusion
sentences), which Γ holds at the arguments no overload covers only: weaker under overloadFunction,
in no class. -/
def ovlFnApart : List Nat := [104, 105]

/-- **The account**: the class lists and the sentences of a function-overloaded symbol partition the
user module's sentences. Their concatenation is a permutation of the sentences' indices, which are
distinct, so each sentence is in one class or among those of a function-overloaded symbol, and there
once. -/
theorem account : (classes.flatMap (·.2) ++ ovlFnApart).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 30), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 16), ("injectivity", 4), ("distinctness", 0), ("no junk", 11), ("function functional", 15), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("overload equation", 1), ("no direction", 31)] := by
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
  [(248, "Bool"), (249, "Exp"), (250, "GeneratedCounterCell"), (251, "GeneratedCounterCellOpt"),
   (252, "GeneratedTopCell"), (253, "GeneratedTopCellFragment"), (254, "Int"), (255, "K"),
   (256, "KCell"), (257, "KCellOpt"), (258, "KItem"), (259, "List"), (260, "Map"), (261, "Set")]

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
  [(14, "subsort"), (18, "subsort"), (83, "function functional"), (114, "no junk"),
   (123, "no junk"), (124, "overload equation"), (211, "no direction"), (214, "function equation"),
   (215, "function equation"), (247, "function equation"), (249, "no direction")]

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

theorem sig_sizes : (sigItems c).length = 207 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 130, 92, 5, 33) := by
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

def callOrder : List Nat := [
385]

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
def fnFunIdx : List Nat := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]

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

/-! ## Function equations (30 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 30 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax247, U.ax226, U.ax234, U.ax233, U.ax232, U.ax231, U.ax238, U.ax237, U.ax240, U.ax239,
   U.ax236, U.ax235, U.ax213, U.ax212, U.ax225, U.ax224, U.ax221, U.ax220, U.ax223, U.ax222,
   U.ax228, U.ax227, U.ax230, U.ax229, U.ax217, U.ax216, U.ax219, U.ax218, U.ax215, U.ax214]

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

theorem nj113 : (trS U.ax113).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj119 : (trS U.ax119).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj122 : (trS U.ax122).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax113, U.ax119, U.ax122], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj113]; exact orTopBot_valid hD rfl
  · rw [nj119]; exact orTopBot_valid hD rfl
  · rw [nj122]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax120, U.ax121],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax120, U.ax121],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax123).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (123)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax123).pat := by
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
   U.ax101, U.ax102]

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
  [U.ax124]

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

/-! ## Sentences of a function-overloaded symbol (104, 105): weaker under
overloadFunction, listed apart

Γ holds each sentence at the arguments no overload of its generator covers only (Γ's items
`funUncItem`, `injUncItem`, `distUncItem`). This section states what holds for every H on every
text: the sentence entails that item in a model of Γ, the same-constructor and
different-constructors sentences with the `functional` sentence of their function-overloaded
generator. What a sentence says at covered arguments is the next section's, by hand. -/

/-- The sentences of `ovlFnApart`, in text order. -/
noncomputable def ovlFnText : List AxiomDecl :=
  [U.ax104, U.ax105]

theorem ovlfn_index : ovlFnText.map (·.index) = ovlFnApart := by decide +kernel

/-- The generator `LblplusExp`. -/
def ovlFnGen0 : Gen := .ctor ⟨386, [32, 32], 32⟩

/-- The sorts of these generators are the semantics' sorts, named: -/
theorem ovlfn_sorts : 32 < nRegSorts + c.sortNames.length := by decide +kernel
theorem ovlfn_sort_names : c.sortName 32 = "Exp" := by decide +kernel

/-- Γ holds the G-arity item of each generator whose `functional` sentence the others are joint
with (`tieOvlFnArityB`). -/
theorem ovlfn_arity_0 : tieOvlFnArityB c 32 ovlFnGen0 = true := by decide +kernel

/-- Sentence 104 is the `functional` sentence of `LblplusExp` of Exp. -/
theorem ovlfn_text_104 : tieOvlFnFunAtB c 32 ovlFnGen0 U.ax104.ax = true := by decide +kernel
theorem ovlfn_trS_104 : (trS U.ax104).pat = (trAxiom [] [] U.ax104).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_104 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnFun_item_withHooks ovlfn_text_104 H

/-- **In a model of Γ, sentence 104 entails that item**, for every H. -/
theorem ovlfn_entails_item_104 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (h : I ⊧ᴵ (trS U.ax104).pat) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_104] at h
  exact tieOvlFnFun_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_104) ovlfn_sorts
    ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) h _

/-- Sentence 105 is the same-constructor sentence of `LblplusExp` of Exp, joint with the `functional` sentence 104. -/
theorem ovlfn_text_105 : tieOvlFnInjAtB c 32 ovlFnGen0 U.ax105.ax = true := by decide +kernel
theorem ovlfn_trS_105 : (trS U.ax105).pat = (trAxiom [] [] U.ax105).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_105 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnInj_item_withHooks ovlfn_text_105 H

/-- **In a model of Γ, sentence 105 with sentence 104 entails that item**, for every H. -/
theorem ovlfn_entails_item_105 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax104).pat) (h : I ⊧ᴵ (trS U.ax105).pat) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_104] at hf
  rw [ovlfn_trS_105] at h
  exact tieOvlFnInj_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_104)
    ((tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_105) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _

/-! ## Sentences of a function-overloaded symbol: the covered part (by hand) -/

/- `plusExp : Exp × Exp → Exp` overloads the function `plusInt : Int × Int → Int`, Int below Exp,
and `plusInt(I1, I2)` is `I1 +Int I2`. A value list `plusInt` covers is a pair of injections of
integers, where `+Int` has a value. So, for every H:
- `plusInt` has a value at every covered value list (`ovlFnTotal_ofr`: the stripped arguments are
  two integers, `eval_plus_ofr`), and the `functional` sentence of `plusExp` (104) holds at values
  (`ovlfn_at_values_104`);
- `plusExp(inj 1, inj 2)` and `plusExp(inj 2, inj 1)` have the one value `inj 3` (`res12_ofr`,
  `res21_ofr`), so `OvlFnInj plusExp` fails (`not_ovlFnInj_ofr`), and no model of Γ satisfies the
  same-constructor sentence of `plusExp` (105) as the text writes it (`ovlfn_refuted_105`): in a
  model of Γ both applications hold the element of `inj 3`, and the sentence then makes the
  elements of `inj 1` and `inj 2`, different values, one.
The definition reads no confined sort (`readsConfined_c`), so `Γc` is `Γ`: 104 is in every model of
Γ at every valuation sending the sentence's variables to values' elements, and the refutation of
105 is against Γ. Each statement has `FnHyp`, which holds for every H (`fnHypH`). -/

def expS : Srt := 32
def plusInt : Sym := 385
def plusExp : Sym := 386

theorem syms_named : c.sortName expS = "Exp" ∧ c.symName intAdd = "Lbl'UndsPlus'Int'Unds'" ∧
    c.symName plusInt = "LblplusInt" ∧ c.symName plusExp = "LblplusExp" := by decide +kernel

/-- `plusInt(I1, I2) = I1 +Int I2`. -/
def plusCl : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0, .var 1], req := none, rhs := .app intAdd [.var 0, .var 1], ens := none }
/-- `plusInt : Int × Int → Int`, not declared total. -/
def plusIntFn : Fn := ⟨plusInt, [Srt.int, Srt.int], Srt.int, [plusCl], false⟩
def plusIntSig : CtorSig := ⟨plusInt, [Srt.int, Srt.int], Srt.int⟩
def plusExpSig : CtorSig := ⟨plusExp, [expS, expS], expS⟩
/-- `plusExp` overloads `plusInt`. -/
def oPlus : OvlSig := ⟨plusExpSig, [plusInt]⟩

kernel_rfl fns_c : c.fns = [plusIntFn]
kernel_rfl ovls_c : c.ovls = [oPlus]

/-- **The reading**: `plusInt`'s one clause, `plusExp` overloading it, `plusExp` function-overloaded. -/
theorem reading : c.fns = [plusIntFn] ∧ c.ovls = [oPlus] ∧ c.fnOvlSyms = [plusExp] :=
  ⟨fns_c, ovls_c, by decide +kernel⟩

/-- `inj{Int, Exp}(n)` -/
def injI (n : Int) : GroundTerm := .inj Srt.int expS (int n)

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oPlus.sig.name = some oPlus
kernel_rfl fns_H : ∀ H : HookParams, (cH H).fns = [plusIntFn]
kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn plusInt = some plusIntFn
kernel_rfl isCtor_H : ∀ H : HookParams, (cH H).isCtor intAdd = false
kernel_rfl sort_int_H : ∀ (H : HookParams) (n : Int), (cH H).sortOf (int n) = some Srt.int
kernel_rfl sorts_12 : ∀ H : HookParams, (cH H).sortsOf [injI 1, injI 2] = some oPlus.sig.args
kernel_rfl sorts_21 : ∀ H : HookParams, (cH H).sortsOf [injI 2, injI 1] = some oPlus.sig.args
-- `plusInt` covers `(inj 1, inj 2)` and `(inj 2, inj 1)`.
kernel_rfl cover_12 : ∀ H : HookParams, (cH H).fnCover oPlus.sig.name [injI 1, injI 2] = some plusIntSig
kernel_rfl cover_21 : ∀ H : HookParams, (cH H).fnCover oPlus.sig.name [injI 2, injI 1] = some plusIntSig

/-- **`plusInt(a, b)` evaluates to the value of `a +Int b`**, by its one clause, under every H. -/
theorem eval_plus_ofr (H : HookParams) {a b : Int} {v : GroundTerm}
    (hh : hook intAdd [int a, int b] = some (some v)) : Eval (cH H) plusInt [int a, int b] (some v) :=
  .clause (cl := plusCl) (σ := [(0, int a), (1, int b)]) (lookupFn_H H) (List.mem_singleton_self _)
    (fun i s' h => by
      match i, h with
      | 0, h => cases h; exact ⟨_, rfl, sort_int_H H a⟩
      | 1, h => cases h; exact ⟨_, rfl, sort_int_H H b⟩
      | i + 2, h => simp [plusCl] at h)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      rw [show plusIntFn.clauses = [plusCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl
    (.hook (rs := [some (int a), some (int b)]) (isCtor_H H) rfl
      (.cons .var (.cons .var .nil))
      (fun vs h => by cases h; exact Semantics.hookRes_of_value hh)
      (fun h => by cases h))
    (fun t ht => by cases ht) .top

/-- `+Int` has a value at every pair of integers: their sum. -/
theorem add_at_ofr (a b : Int) : hook intAdd [int a, int b] = some (some (int (a + b))) := by
  rw [show hook intAdd [int a, int b] = some (int2 [int a, int b] fun x y => some (int (x + y))) from rfl]
  simp [int2, asInt, int]

theorem shapesOK_ofr : c.shapesOK = true := by decide +kernel

/-- **`OvlFnTotal`**, for every H: the arguments `plusInt` covers, stripped, are two integers, at
which its one clause gives the sum. -/
theorem ovlFnTotal_ofr (H : HookParams) : OvlFnTotal (cH H) oPlus := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx (Semantics.coreOK_iff_ex.mp (coreOKH H))
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have HO : OvlLaws.OvlHyp (cH H) := hno.hyp hsc.trans
  intro vs kg hvs hcov
  obtain ⟨fn, hfn, -, hsig, -, -, -, hus⟩ := OvlLaws.fnCover_fn_ovlF HO.fnFacts (lookup_H H) hvs hcov
  rw [fns_H H, List.mem_singleton] at hfn
  subst hfn
  subst hsig
  rw [show plusIntFn.args = [Srt.int, Srt.int] from rfl, Semantics.sortsOf_withHooks _ _ noRaw] at hus
  obtain ⟨w₁, w₂, he, h₁, h₂⟩ := sortsOf_two hus
  obtain ⟨a, rfl⟩ := shape_int shapesOK_ofr h₁
  obtain ⟨b, rfl⟩ := shape_int shapesOK_ofr h₂
  have he' : stripAll plusIntSig.args oPlus.sig.args vs = [int a, int b] := he
  refine ⟨int (a + b), ?_⟩
  show Eval (cH H) plusInt (stripAll plusIntSig.args oPlus.sig.args vs) (some (int (a + b)))
  rw [he']
  exact eval_plus_ofr H (add_at_ofr a b)

theorem fun_shape_ofr (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oPlus.sig.result (Gen.toK (cH H) (.ctor oPlus.sig)) U.ax104.ax = true := by
  have h := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_104
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem inj_shape_ofr (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oPlus.sig.result (Gen.toK (cH H) (.ctor oPlus.sig)) U.ax105.ax = true := by
  have h := (tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_105
  simp only [tieOvlFnInjAtB, Bool.and_eq_true] at h
  exact h.1.2

/-- **The `functional` sentence of `plusExp` (104) holds at values, for every H**, in every model
of `Γc`, which is Γ here. -/
theorem ovlfn_at_values_104 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax104 (trS U.ax104).pat := by
  rw [ovlfn_trS_104]
  exact ovlFnTotal_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnTotal_ofr H) (fun_shape_ofr H)

/-- **`plusExp(inj 1, inj 2)` has the value `inj 3`**: `plusInt` covers the arguments, and
`plusInt(1, 2)` is `3`. -/
theorem res12_ofr (H : HookParams) : OvlFnRes (cH H) oPlus [injI 1, injI 2] (some (injI 3)) :=
  OvlFnRes.fn (cover_12 H) (eval_plus_ofr H (a := 1) (b := 2) (v := int 3) (by decide +kernel))

/-- **`plusExp(inj 2, inj 1)` has the same value `inj 3`.** -/
theorem res21_ofr (H : HookParams) : OvlFnRes (cH H) oPlus [injI 2, injI 1] (some (injI 3)) :=
  OvlFnRes.fn (cover_21 H) (eval_plus_ofr H (a := 2) (b := 1) (v := int 3) (by decide +kernel))

theorem args_ne_ofr : [injI 1, injI 2] ≠ [injI 2, injI 1] := by simp [injI, int]

/-- **`OvlFnInj plusExp` fails**, for every H. -/
theorem not_ovlFnInj_ofr (H : HookParams) : ¬ OvlFnInj (cH H) oPlus :=
  fun h => args_ne_ofr (h _ _ _ (sorts_12 H) (sorts_21 H) (res12_ofr H) (res21_ofr H))

/-- The sentences of `ovlFnApart` refuted for every H. -/
def ovlFnRefuted : List Nat := [105]

/-- **No model of Γ satisfies the same-constructor sentence of `plusExp`**
(`plusExp(X0, X1) ∧ plusExp(Y0, Y1) → plusExp(X0 ∧ Y0, X1 ∧ Y1)`, sentence 105), for every H:
`plusExp(inj 1, inj 2)` and `plusExp(inj 2, inj 1)` are both `inj 3`. -/
theorem ovlfn_refuted_105 (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax105).pat) := by
  intro M inst I hI
  rw [ovlfn_trS_105]
  have hIc : I ⊧ᴵP Γc (cH H) := by
    rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI
  exact ovlFnInj_refuted (coreOKH H) (fnHypH H) (lookup_H H) (inj_shape_ofr H) (sorts_12 H) (sorts_21 H)
    args_ne_ofr (res12_ofr H) (res21_ofr H) M inst I hIc

/-! ## The refuted sentences of a function-overloaded symbol -/

/-- The sentences the hand section refutes for every H are sentences of `ovlFnApart`, in its order. -/
theorem ovlfn_refuted_sub : ovlFnRefuted.isSublist ovlFnApart = true := by decide +kernel

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


/-! ## Library sample: sentence 164, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax164).pat = (trAxiom [] [] U.ax164).pat := by decide +kernel
theorem s166_pattern : U.ax164.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax164.ax.sortVars.map sortVarKey ++ freeOf [] U.ax164.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax164.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 164 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax164.ax.sortVars U.ax164.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax164).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax164.ax.sortVars U.ax164.ax.pattern = t at he ⊢
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
/-- **Sentence 164 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax164 (trS U.ax164).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


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

end KCore.TieE5OvlFun

#check @KCore.TieE5OvlFun.noRaw
#check @KCore.TieE5OvlFun.readsConfined_c
#check @KCore.TieE5OvlFun.userAxioms_eq
#check @KCore.TieE5OvlFun.coreOK
#check @KCore.TieE5OvlFun.wf_defn
#check @KCore.TieE5OvlFun.account
#check @KCore.TieE5OvlFun.account_sizes
#check @KCore.TieE5OvlFun.account_classes
#check @KCore.TieE5OvlFun.account_absent
#check @KCore.TieE5OvlFun.absent_closed
#check @KCore.TieE5OvlFun.absent_proj_below_c
#check @KCore.TieE5OvlFun.absent_proj_below
#check @KCore.TieE5OvlFun.lists_in_account
#check @KCore.TieE5OvlFun.attrs_agree
#check @KCore.TieE5OvlFun.sig_origin_but_next
#check @KCore.TieE5OvlFun.decls_entailed
#check @KCore.TieE5OvlFun.consistent
#check @KCore.TieE5OvlFun.fnFun_indices
#check @KCore.TieE5OvlFun.fnFun_account
#check @KCore.TieE5OvlFun.fnFun_checked
#check @KCore.TieE5OvlFun.fnFun_trS
#check @KCore.TieE5OvlFun.fnFun_at_values
#check @KCore.TieE5OvlFun.fnFun_at_values_step
#check @KCore.TieE5OvlFun.text_nextless
#check @KCore.TieE5OvlFun.fn_shape
#check @KCore.TieE5OvlFun.fns_account
#check @KCore.TieE5OvlFun.fns_entailed
#check @KCore.TieE5OvlFun.fns_from_text
#check @KCore.TieE5OvlFun.fn_prios
#check @KCore.TieE5OvlFun.nojunk_trivial_entailed
#check @KCore.TieE5OvlFun.nojunk_items_entailed
#check @KCore.TieE5OvlFun.nojunk_kitem_entailed
#check @KCore.TieE5OvlFun.cons_entailed
#check @KCore.TieE5OvlFun.ovleq_account
#check @KCore.TieE5OvlFun.ovleq_entailed
#check @KCore.TieE5OvlFun.ovlfn_index
#check @KCore.TieE5OvlFun.ovlfn_text_104
#check @KCore.TieE5OvlFun.ovlfn_item_in_gamma_104
#check @KCore.TieE5OvlFun.ovlfn_entails_item_104
#check @KCore.TieE5OvlFun.ovlfn_text_105
#check @KCore.TieE5OvlFun.ovlfn_item_in_gamma_105
#check @KCore.TieE5OvlFun.ovlfn_entails_item_105
#check @KCore.TieE5OvlFun.ovlFnRefuted
#check @KCore.TieE5OvlFun.ovlfn_at_values_104
#check @KCore.TieE5OvlFun.ovlfn_refuted_105
#check @KCore.TieE5OvlFun.ovlfn_refuted_sub
#check @KCore.TieE5OvlFun.idem_refuted
#check @KCore.TieE5OvlFun.lib166
#check @KCore.TieE5OvlFun.lib166_at_values
#check @KCore.TieE5OvlFun.gamma_origin
#check @KCore.TieE5OvlFun.gamma_from
#check @KCore.TieE5OvlFun.owed_rules
#check @KCore.TieE5OvlFun.owed_clauses
#check @KCore.TieE5OvlFun.openDecidedH
#print axioms KCore.TieE5OvlFun.noRaw
#print axioms KCore.TieE5OvlFun.readsConfined_c
#print axioms KCore.TieE5OvlFun.userAxioms_eq
#print axioms KCore.TieE5OvlFun.coreOK
#print axioms KCore.TieE5OvlFun.wf_defn
#print axioms KCore.TieE5OvlFun.account
#print axioms KCore.TieE5OvlFun.account_sizes
#print axioms KCore.TieE5OvlFun.account_classes
#print axioms KCore.TieE5OvlFun.account_absent
#print axioms KCore.TieE5OvlFun.absent_closed
#print axioms KCore.TieE5OvlFun.absent_proj_below_c
#print axioms KCore.TieE5OvlFun.absent_proj_below
#print axioms KCore.TieE5OvlFun.lists_in_account
#print axioms KCore.TieE5OvlFun.attrs_agree
#print axioms KCore.TieE5OvlFun.sig_origin_but_next
#print axioms KCore.TieE5OvlFun.decls_entailed
#print axioms KCore.TieE5OvlFun.consistent
#print axioms KCore.TieE5OvlFun.fnFun_indices
#print axioms KCore.TieE5OvlFun.fnFun_account
#print axioms KCore.TieE5OvlFun.fnFun_checked
#print axioms KCore.TieE5OvlFun.fnFun_trS
#print axioms KCore.TieE5OvlFun.fnFun_at_values
#print axioms KCore.TieE5OvlFun.fnFun_at_values_step
#print axioms KCore.TieE5OvlFun.text_nextless
#print axioms KCore.TieE5OvlFun.fn_shape
#print axioms KCore.TieE5OvlFun.fns_account
#print axioms KCore.TieE5OvlFun.fns_entailed
#print axioms KCore.TieE5OvlFun.fns_from_text
#print axioms KCore.TieE5OvlFun.fn_prios
#print axioms KCore.TieE5OvlFun.nojunk_trivial_entailed
#print axioms KCore.TieE5OvlFun.nojunk_items_entailed
#print axioms KCore.TieE5OvlFun.nojunk_kitem_entailed
#print axioms KCore.TieE5OvlFun.cons_entailed
#print axioms KCore.TieE5OvlFun.ovleq_account
#print axioms KCore.TieE5OvlFun.ovleq_entailed
#print axioms KCore.TieE5OvlFun.ovlfn_index
#print axioms KCore.TieE5OvlFun.ovlfn_text_104
#print axioms KCore.TieE5OvlFun.ovlfn_item_in_gamma_104
#print axioms KCore.TieE5OvlFun.ovlfn_entails_item_104
#print axioms KCore.TieE5OvlFun.ovlfn_text_105
#print axioms KCore.TieE5OvlFun.ovlfn_item_in_gamma_105
#print axioms KCore.TieE5OvlFun.ovlfn_entails_item_105
#print axioms KCore.TieE5OvlFun.ovlFnRefuted
#print axioms KCore.TieE5OvlFun.ovlfn_at_values_104
#print axioms KCore.TieE5OvlFun.ovlfn_refuted_105
#print axioms KCore.TieE5OvlFun.ovlfn_refuted_sub
#print axioms KCore.TieE5OvlFun.idem_refuted
#print axioms KCore.TieE5OvlFun.lib166
#print axioms KCore.TieE5OvlFun.lib166_at_values
#print axioms KCore.TieE5OvlFun.gamma_origin
#print axioms KCore.TieE5OvlFun.gamma_from
#print axioms KCore.TieE5OvlFun.owed_rules
#print axioms KCore.TieE5OvlFun.owed_clauses
#print axioms KCore.TieE5OvlFun.openDecidedH
