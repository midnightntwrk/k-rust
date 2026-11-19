/-
  The tie (C14) on `f2-examples/e3-setvar-nonlinear.kompile.kore`, the kompiled text of construct fixture e3-setvar-nonlinear
  (`test/constructs/fixtures/e3-setvar-nonlinear`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-setvar-nonlinear`; run from the package root: `lake env lean -j1 test/TieE3SetvarNonlinear.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 145 sentences of the user module E3-SETVAR-NONLINEAR, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 209 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (99) is the equation whose sentence binds two arguments by
    memberships in one set variable where Γ's item binds them by two element variables
    (`setVarInDropped`; test/NoteSetVarIn.lean's `nsvAxS`, `nsvAxG`): the two hold in the same
    models of definedness, of the definition of `\ceil` and of the sort constant `SortExp`
    (`sv<j>_iff`, `nsv_iff`), items of Γ (`sv_sig_pats`), so Γ entails the sentence
    (`sv<j>_entailed`), and the sentence with those two items gives the item (`sv<j>_w1`), which
    `fns_from_text` leaves out. `fns_from_text` (the converse), `fn_prios` (the priorities the
    sentences state are the clauses').
  - Constructor sentences (31): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (47): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence gives it with the definition of `\ceil` and the sort constant `SortExp`:
    `sv<j>_w1`), Γ's rule items, the five parts Γ defines by predicates, or definedness
    (`gamma_from`).
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

namespace KCore.TieE3SetvarNonlinear

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-setvar-nonlinear.kompile.kore"
definition_of defn from "f2-examples/e3-setvar-nonlinear.kompile.kore"
user_axioms U from "f2-examples/e3-setvar-nonlinear.kompile.kore" module "E3-SETVAR-NONLINEAR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-SETVAR-NONLINEAR")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 145 := by decide +kernel

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
  [("function equation", [99, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
      122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 55, 58, 78, 79, 81]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29]),
   ("distinctness", [56, 57, 59]),
   ("no junk", [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]),
   ("function functional", [62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 38, 42, 50, 51, 52, 53, 54, 61, 77, 80, 82, 83, 84, 85]),
   ("collection law", [39, 40, 41, 43, 44, 45, 46, 48, 49]),
   ("library", [98, 147]),
   ("set idempotence", [47]),
   ("set-variable lemma", [148]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 37, 60, 86, 100, 101, 102, 103, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143,
      144, 145, 146])]

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
    [("function equation", 30), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 9), ("subsort", 15), ("injectivity", 4), ("distinctness", 3), ("no junk", 11), ("function functional", 15), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 22)] := by
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
  [(133, "Bool"), (134, "Exp"), (135, "GeneratedCounterCell"), (136, "GeneratedCounterCellOpt"),
   (137, "GeneratedTopCell"), (138, "GeneratedTopCellFragment"), (139, "Int"), (140, "K"),
   (141, "KCell"), (142, "KCellOpt"), (143, "KItem"), (144, "List"), (145, "Map"), (146, "Set")]

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
   (58, "constructor functional"), (59, "distinctness"), (63, "function functional"),
   (81, "constructor functional"), (88, "no junk"), (97, "no junk"), (99, "function equation"),
   (103, "no direction"), (106, "function equation"), (107, "function equation"),
   (134, "no direction"), (148, "set-variable lemma")]

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

theorem sig_sizes : (sigItems c).length = 209 := by decide +kernel

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

def callOrder : List Nat := [
388]

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
def fnFunIdx : List Nat := [62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]

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

theorem nj87 : (trS U.ax87).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj93 : (trS U.ax93).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj96 : (trS U.ax96).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax87, U.ax93, U.ax96], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj87]; exact orTopBot_valid hD rfl
  · rw [nj93]; exact orTopBot_valid hD rfl
  · rw [nj96]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax88, U.ax89, U.ax90, U.ax91, U.ax92, U.ax94, U.ax95],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax88, U.ax89, U.ax90, U.ax91, U.ax92, U.ax94, U.ax95],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax97).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (97)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax97).pat := by
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
   U.ax56, U.ax57, U.ax58, U.ax59, U.ax78, U.ax79, U.ax81]

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


/-! ## Function equations (30 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 99) is test/NoteSetVarIn.lean's `nsvAxG`, `X0 ∈ V0 ∧ X1 ∈ V1 → f(X0, X1) = r`
with V0 and V1 element variables, and its sentence is `nsvAxS`, `X0 ∈ @S ∧ X1 ∈ @S → f(X0, X1) = r`
with the set variable `@S` free (`setVarInDropped`; `sv<j>_text`, kernel). Each holds exactly where
`f(X0, X1) = r` holds at every pair of elements of `SortExp`, the sentence by `KCore.setvar_in_drop`
(the set of the two elements holds both), the item by `nsv_evar_in_drop`: the two hold in the same
models of definedness, of the definition of `\ceil` and of the sort constant `SortExp` (`sv<j>_iff`,
`nsv_iff`, the section `Bridge` as test/NoteSetVarIn.lean writes it). Those two items are Γ's
(`sv_sig_pats`), so Γ entails the sentence (`sv<j>_entailed`), and the sentence with them gives the
item (`sv<j>_w1`), which `fns_from_text` leaves out (its premise set is the sentence alone). It is
not the item (`sv<j>_differs`).

Every other item is the translation of its function sentence (`shape`). -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

section Bridge
open Kore (KSort Pattern)

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-! ### The two forms of the equation, on the translated patterns

The sentence `X0 ∈ @S ∧ X1 ∈ @S → f(X0, X1) = r` (`svinAx`, KcoreSpec/SetVarIn.lean) and Γ's item
`X0 ∈ V0 ∧ X1 ∈ V1 → f(X0, X1) = r` (`nsvItem`) each hold exactly where `f(X0, X1) = r` holds at
every pair of elements of `SortExp` (`NsvRead`): the sentence by `KCore.setvar_in_drop` (the set
`{x₀, x₁}` holds both elements), the item by `nsv_evar_in_drop` (`V0` at `x₀`, `V1` at `x₁`). -/

theorem nsv_upd2 {e : Valuation M} {v₀ v₁ x : EVar} {a₀ a₁ : M} (h0 : x ≠ v₀) (h1 : x ≠ v₁) :
    Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x = e.evalEvar x := by
  rw [Function.update_noteq h1, Function.update_noteq h0]

theorem nsv_upd_self {α β : Type} [DecidableEq α] (f : α → β) (x : α) : Function.update f x (f x) = f := by
  funext y
  by_cases h : y = x
  · subst h; exact Function.update_same _ _ _
  · exact Function.update_noteq h _ _

theorem nsv_upd2_fst {e : Valuation M} {v₀ v₁ : EVar} {a₀ a₁ : M} (hv : v₀ ≠ v₁) :
    Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₀ = a₀ := by
  rw [Function.update_noteq hv, Function.update_same]

theorem nsv_upd2_snd {e : Valuation M} {v₀ v₁ : EVar} {a₀ a₁ : M} :
    Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₁ = a₁ := Function.update_same _ _ _

/-- **Memberships in two distinct element variables that stand nowhere else are dropped.** A sentence
`Q ∧ (x₀ ∈ v₀ ∧ (x₁ ∈ v₁ ∧ T)) → φ` of the result sort `R` holds at a point for every pair of
elements `v₀`, `v₁` of the sort `S` exactly where `Q ∧ T → φ` holds there, when `v₀` and `v₁` are
distinct, neither is `x₀` or `x₁` or free in `S`, `R`, `Q`, `T`, `φ`, and `x₀`, `x₁` are elements
of `S`. -/
theorem nsv_evar_in_drop [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R Q T φ : P} {σ ρ : M} {x₀ x₁ v₀ v₁ : EVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar x₀)) (h₁ : Inh I σ (e.evalEvar x₁))
    (hv : v₀ ≠ v₁) (h00 : x₀ ≠ v₀) (h01 : x₀ ≠ v₁) (h10 : x₁ ≠ v₀) (h11 : x₁ ≠ v₁)
    (hS0 : S.isFreeEvar v₀ = false) (hS1 : S.isFreeEvar v₁ = false)
    (hR0 : R.isFreeEvar v₀ = false) (hR1 : R.isFreeEvar v₁ = false)
    (hQ0 : Q.isFreeEvar v₀ = false) (hQ1 : Q.isFreeEvar v₁ = false)
    (hT0 : T.isFreeEvar v₀ = false) (hT1 : T.isFreeEvar v₁ = false)
    (hφ0 : φ.isFreeEvar v₀ = false) (hφ1 : φ.isFreeEvar v₁ = false) (m : M) :
    (∀ a₀ a₁ : M, Inh I σ a₀ → Inh I σ a₁ →
      (sImp R (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar v₀)) (sAnd (sIn S R (.evar x₁) (.evar v₁)) T)))
        φ).interpret I ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m) ↔
    (sImp R (sAnd Q T) φ).interpret I e m := by
  have inv : ∀ {ψ : P}, ψ.isFreeEvar v₀ = false → ψ.isFreeEvar v₁ = false → ∀ (a₀ a₁ b : M),
      ψ.interpret I ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ b ↔
        ψ.interpret I e b := fun {ψ} g0 g1 a₀ a₁ b =>
    (interp_evarAt_svin (I := I) (e := ⟨Function.update e.evalEvar v₀ a₀, e.evalSvar⟩) (a := a₁) g1 b).trans
      (interp_evarAt_svin (I := I) (e := e) (a := a₀) g0 b)
  have hS' := fun a₀ a₁ b => (inv hS0 hS1 a₀ a₁ b).trans (hS b)
  have hR' := fun a₀ a₁ b => (inv hR0 hR1 a₀ a₁ b).trans (hR b)
  have hin0 : ∀ a₀ a₁ : M, (sIn S R (.evar x₀) (.evar v₀)).interpret I
      ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m ↔ (e.evalEvar x₀ = a₀ ∧ Inh I ρ m) := by
    intro a₀ a₁
    rw [interp_sIn_evar_svin hD hc (hS' a₀ a₁) (hR' a₀ a₁) hσ hρ
      (by show Inh I σ (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₀); rw [nsv_upd2 h00 h01]; exact h₀) m]
    show (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₀ =
      Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₀ ∧ _) ↔ _
    rw [nsv_upd2 h00 h01, Function.update_noteq hv, Function.update_same]
  have hin1 : ∀ a₀ a₁ : M, (sIn S R (.evar x₁) (.evar v₁)).interpret I
      ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m ↔ (e.evalEvar x₁ = a₁ ∧ Inh I ρ m) := by
    intro a₀ a₁
    rw [interp_sIn_evar_svin hD hc (hS' a₀ a₁) (hR' a₀ a₁) hσ hρ
      (by show Inh I σ (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₁); rw [nsv_upd2 h10 h11]; exact h₁) m]
    show (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₁ =
      Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₁ ∧ _) ↔ _
    rw [nsv_upd2 h10 h11, Function.update_same]
  have hinh : ∀ a₀ a₁ : M, (inhOf R).interpret I
      ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m ↔ Inh I ρ m :=
    fun a₀ a₁ => interp_inhOf_of (hR' a₀ a₁)
  simp only [interp_sImp, interp_sAnd, hinh, interp_inhOf_of hR]
  constructor
  · intro h
    have := h _ _ h₀ h₁
    rw [hin0, hin1, inv hQ0 hQ1, inv hT0 hT1, inv hφ0 hφ1] at this
    exact ⟨this.1, fun ⟨hq, ht⟩ => this.2 ⟨hq, ⟨rfl, this.1⟩, ⟨rfl, this.1⟩, ht⟩⟩
  · rintro ⟨hm, hf⟩ a₀ a₁ _ _
    rw [hin0, hin1, inv hQ0 hQ1, inv hT0 hT1, inv hφ0 hφ1]
    exact ⟨hm, fun ⟨hq, _, _, ht⟩ => hf ⟨hq, ht⟩⟩

def nsvRv : Kore.SortVar := ⟨⟨⟨"R"⟩⟩⟩
def nsvV0 : Kore.EVar := ⟨⟨⟨"VarV0"⟩⟩, svinExp⟩
def nsvV1 : Kore.EVar := ⟨⟨⟨"VarV1"⟩⟩, svinExp⟩

/-- Γ's axiom of the clause read from `rule f(@S, @S) => r()`: two distinct element variables. -/
def nsvItem : Pattern :=
  .implies svinR
    (.and svinR [.top svinR,
      .and svinR [.in svinExp svinR (.var (.evar svinX0)) (.var (.evar nsvV0)),
        .and svinR [.in svinExp svinR (.var (.evar svinX1)) (.var (.evar nsvV1)), .top svinR]]])
    svinEq

def nsvAxS : Kore.Axiom := ⟨[nsvRv], svinAx, []⟩
def nsvAxG : Kore.Axiom := ⟨[nsvRv], nsvItem, []⟩
def nsvCtxG : Ctx := ⟨tableOf [nsvRv] nsvItem, []⟩

/-- `nsv_evar_in_drop` at Γ's item. -/
theorem nsv_item_drop [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort nsvCtxG.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort nsvCtxG.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX1)))) (m : M) :
    (∀ a₀ a₁ : M, Inh I σ a₀ → Inh I σ a₁ →
      (tr nsvCtxG nsvItem).interpret I
        ⟨Function.update (Function.update e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0)) a₀)
          (nsvCtxG.vars.ev (evarKey nsvV1)) a₁, e.evalSvar⟩ m) ↔
    (tr nsvCtxG svinRead).interpret I e m :=
  nsv_evar_in_drop hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m

/-- The element variables of the sort variable `R` and of `X0`, `X1`, in the sentence's table. -/
def nsvKR : EVar := svinCtx.vars.ev (.sortVar "R")
def nsvK0 : EVar := svinCtx.vars.ev (evarKey svinX0)
def nsvK1 : EVar := svinCtx.vars.ev (evarKey svinX1)

/-- The sentence with its memberships dropped, at every valuation meeting the guards of `R`, `X0`
and `X1`: `f(X0, X1) = r` at every pair of elements of `SortExp`. -/
def NsvRead (I : Interpretation KoreAML.Sym M) (σ : M) : Prop :=
  ∀ e : Valuation M, IsSort I (e.evalEvar nsvKR) → Inh I σ (e.evalEvar nsvK0) → Inh I σ (e.evalEvar nsvK1) →
    ∀ m, Inh I (e.evalEvar nsvKR) m → (tr svinCtx svinRead).interpret I e m

theorem nsv_imp_inh {t : VarTable} {R : KSort} {prem φ : Pattern} {e : Valuation M} {b : M}
    (h : (tr ⟨t, []⟩ (.implies R prem φ)).interpret I e b) : (inhOf (trSort t R)).interpret I e b := by
  simp only [tr, interp_sImp] at h; exact h.1

theorem nsv_trSort_exp {σ : M} (hσ1 : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σ) (t : VarTable)
    (e : Valuation M) (a : M) : (trSort t svinExp).interpret I e a ↔ a = σ := by
  have : trSort t svinExp = sym (.sort "SortExp") := by simp [svinExp, trSort, trSortApp]
  rw [this]; exact hσ1 a

theorem nsv_trSort_R (t : VarTable) (e : Valuation M) (a : M) :
    (trSort t svinR).interpret I e a ↔ a = e.evalEvar (t.ev (.sortVar "R")) := by
  have : trSort t svinR = .evar (t.ev (.sortVar "R")) := by simp [svinR, trSort, sortVarKey]
  rw [this, interp_evar]

theorem nsv_freeS : (nsvAxS.sortVars.map sortVarKey ++ freeOf [] nsvAxS.pattern).eraseDups =
    [.sortVar "R", evarKey svinX0, svarKey svinS, evarKey svinX1] := by decide
theorem nsv_freeG : (nsvAxG.sortVars.map sortVarKey ++ freeOf [] nsvAxG.pattern).eraseDups =
    [.sortVar "R", evarKey svinX0, evarKey nsvV0, evarKey svinX1, evarKey nsvV1] := by decide

/-- **The sentence holds exactly where `f(X0, X1) = r` holds at every pair of elements of `SortExp`.** -/
theorem nsv_sentence_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σ : M}
    (hσ1 : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σ) (hσ : IsSort I σ) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxS⟩).pat) ↔ NsvRead I σ := by
  constructor
  · intro h e hR0 h0 h1 m hm
    refine (setvar_in_drop_e3 hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 m).mp fun A hA => ?_
    refine (trAxiom_at hD h (svarAt_svin e (svinCtx.vars.sv (svarKey svinS)) A) (fun k hk b => ?_) m).mpr ?_
    · rw [nsv_freeS] at hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact (interp_guard_sortVar hD).mpr hR0
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr h0)
      · refine (interp_included hD).mpr fun a ha => (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr (hA a ?_)
        change Function.update e.evalSvar (svinCtx.vars.sv (svarKey svinS)) A (svinCtx.vars.sv (svarKey svinS)) a at ha
        rwa [Function.update_same] at ha
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr h1)
    · show (inhOf (trSort _ svinR)).interpret I _ m
      exact (interp_inhOf_of (nsv_trSort_R _ _)).mpr hm
  · intro hMid e m
    unfold trAxiom
    dsimp only
    rw [interpret_impl]
    intro hgd
    have hg : ∀ k ∈ [VarKey.sortVar "R", evarKey svinX0, svarKey svinS, evarKey svinX1],
        (guardOf (tableOf nsvAxS.sortVars nsvAxS.pattern) k).interpret I e m := fun k hk =>
      conjList_mem hgd _ (List.mem_map.mpr ⟨k, by rw [nsv_freeS]; exact hk, rfl⟩)
    have hR0 : IsSort I (e.evalEvar nsvKR) := (interp_guard_sortVar hD).mp (hg _ (by decide))
    have h0 : Inh I σ (e.evalEvar nsvK0) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX0) (by decide)))
    have h1 : Inh I σ (e.evalEvar nsvK1) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX1) (by decide)))
    have hX : ∀ a, e.evalSvar (svinCtx.vars.sv (svarKey svinS)) a → Inh I σ a := fun a ha =>
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_included hD).mp (hg (svarKey svinS) (by decide)) a ha)
    rw [interp_equal hD]
    intro b
    show (tr svinCtx svinAx).interpret I e b ↔ (inhOf (trSort svinCtx.vars svinR)).interpret I e b
    refine ⟨nsv_imp_inh, fun hb => ?_⟩
    have hb' : Inh I (e.evalEvar nsvKR) b := (interp_inhOf_of (nsv_trSort_R _ _)).mp hb
    have := (setvar_in_drop_e3 hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 b).mpr
      (hMid e hR0 h0 h1 b hb') _ hX
    have he : svarAt_svin e (svinCtx.vars.sv (svarKey svinS)) (e.evalSvar (svinCtx.vars.sv (svarKey svinS))) = e := by
      cases e; simp [svarAt_svin, nsv_upd_self]
    rw [he] at this; exact this

theorem nsv_keys : nsvCtxG.vars.ev (.sortVar "R") = nsvKR ∧ nsvCtxG.vars.ev (evarKey svinX0) = nsvK0 ∧
    nsvCtxG.vars.ev (evarKey svinX1) = nsvK1 ∧ tr nsvCtxG svinRead = tr svinCtx svinRead := by decide

/-- **Γ's item holds exactly where `f(X0, X1) = r` holds at every pair of elements of `SortExp`.** -/
theorem nsv_item_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σ : M}
    (hσ1 : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σ) (hσ : IsSort I σ) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxG⟩).pat) ↔ NsvRead I σ := by
  obtain ⟨kR, k0, k1, kT⟩ := nsv_keys
  have hne : nsvCtxG.vars.ev (.sortVar "R") ≠ nsvCtxG.vars.ev (evarKey nsvV0) ∧
      nsvCtxG.vars.ev (.sortVar "R") ≠ nsvCtxG.vars.ev (evarKey nsvV1) ∧
      nsvCtxG.vars.ev (evarKey svinX0) ≠ nsvCtxG.vars.ev (evarKey nsvV0) ∧
      nsvCtxG.vars.ev (evarKey svinX0) ≠ nsvCtxG.vars.ev (evarKey nsvV1) ∧
      nsvCtxG.vars.ev (evarKey svinX1) ≠ nsvCtxG.vars.ev (evarKey nsvV0) ∧
      nsvCtxG.vars.ev (evarKey svinX1) ≠ nsvCtxG.vars.ev (evarKey nsvV1) ∧
      nsvCtxG.vars.ev (evarKey nsvV0) ≠ nsvCtxG.vars.ev (evarKey nsvV1) := by decide
  obtain ⟨nR0, nR1, n00, n01, n10, n11, nv⟩ := hne
  constructor
  · intro h e hR0 h0 h1 m hm
    rw [← kR] at hR0 hm; rw [← k0] at h0; rw [← k1] at h1
    rw [← kT]
    refine (nsv_item_drop hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 m).mp fun a₀ a₁ ha₀ ha₁ => ?_
    refine (trAxiom_at hD h _ (fun k hk b => ?_) m).mpr ?_
    · rw [nsv_freeG] at hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact (interp_guard_sortVar hD).mpr
          ((congrArg (IsSort I) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) nR0 nR1)).mpr hR0)
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) n00 n01)).mpr h0))
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2_fst (e := e) (a₀ := a₀) (a₁ := a₁) nv)).mpr ha₀))
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) n10 n11)).mpr h1))
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2_snd (e := e) (a₀ := a₀) (a₁ := a₁) (v₀ := nsvCtxG.vars.ev (evarKey nsvV0)) (v₁ := nsvCtxG.vars.ev (evarKey nsvV1)))).mpr ha₁))
    · show (inhOf (trSort _ svinR)).interpret I _ m
      exact (interp_inhOf_of (nsv_trSort_R _ _)).mpr
        ((congrArg (fun r => Inh I r m) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) nR0 nR1)).mpr hm)
  · intro hMid e m
    unfold trAxiom
    dsimp only
    rw [interpret_impl]
    intro hgd
    have hg : ∀ k ∈ [VarKey.sortVar "R", evarKey svinX0, evarKey nsvV0, evarKey svinX1, evarKey nsvV1],
        (guardOf (tableOf nsvAxG.sortVars nsvAxG.pattern) k).interpret I e m := fun k hk =>
      conjList_mem hgd _ (List.mem_map.mpr ⟨k, by rw [nsv_freeG]; exact hk, rfl⟩)
    have hR0 : IsSort I (e.evalEvar (nsvCtxG.vars.ev (.sortVar "R"))) := (interp_guard_sortVar hD).mp (hg _ (by decide))
    have h0 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX0))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX0) (by decide)))
    have h1 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX1))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX1) (by decide)))
    have hv0 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey nsvV0) (by decide)))
    have hv1 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV1))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey nsvV1) (by decide)))
    rw [interp_equal hD]
    intro b
    show (tr nsvCtxG nsvItem).interpret I e b ↔ (inhOf (trSort nsvCtxG.vars svinR)).interpret I e b
    refine ⟨nsv_imp_inh, fun hb => ?_⟩
    have hb' : Inh I (e.evalEvar (nsvCtxG.vars.ev (.sortVar "R"))) b := (interp_inhOf_of (nsv_trSort_R _ _)).mp hb
    have hr : (tr nsvCtxG svinRead).interpret I e b := by
      rw [kT]; exact hMid e (kR ▸ hR0) (k0 ▸ h0) (k1 ▸ h1) b (kR ▸ hb')
    have := (nsv_item_drop hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 b).mpr hr _ _ hv0 hv1
    have he : (⟨Function.update (Function.update e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0))
        (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0)))) (nsvCtxG.vars.ev (evarKey nsvV1))
        (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV1))), e.evalSvar⟩ : Valuation M) = e := by
      cases e; simp [nsv_upd_self]
    rw [he] at this; exact this

/-- **The sentence and Γ's item hold in the same models** of definedness, of the definition of
`\ceil` and of the sort constant `SortExp`. -/
theorem nsv_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (hE : I ⊧ᴵ (sortConstantItem ⟨"SortExp", [], false⟩).pat) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxS⟩).pat) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxG⟩).pat) := by
  obtain ⟨σ, hσ1, hσ⟩ := sortConst_of hD hE
  exact (nsv_sentence_iff hD hc hσ1 hσ).trans (nsv_item_iff hD hc hσ1 hσ).symm

end Bridge

/-- A model of Γ satisfies each of Γ's equations. -/
theorem fnItem_sat {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    {j : Nat} {g : P} (hg : (TiePair.gammaPats c)[j]? = some g) : I ⊧ᴵ g := by
  obtain ⟨it, hit, rfl⟩ : ∃ it ∈ fnItems c, it.pat = g := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[j]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))

/-- The two signature items `nsv_iff` reads: the definition of `\ceil` and the sort constant `SortExp`. -/
noncomputable def svSigPats : List P := [ceilDefItem.pat, (sortConstantItem ⟨"SortExp", [], false⟩).pat]

kernel_rfl sv_sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

theorem sv_sig_exp : (sigItems c).any
    (fun it => decide (it.pat = (sortConstantItem ⟨"SortExp", [], false⟩).pat)) = true := by decide +kernel

/-- **The two signature items are items of Γ** (`ΓSig`; kernel for the sort constant). -/
theorem sv_sig_pats (H : HookParams) : ∀ φ ∈ svSigPats, ΓSig (cH H) φ := by
  intro φ hφ
  simp only [svSigPats, List.mem_cons, List.mem_nil_iff, or_false] at hφ
  refine Or.inl (Or.inl ?_)
  rw [sv_sigItems_withHooks]
  rcases hφ with rfl | rfl
  · exact ⟨_, sig_ceilDef, rfl⟩
  · obtain ⟨it, hit, h⟩ := List.any_eq_true.mp sv_sig_exp
    exact ⟨it, hit, of_decide_eq_true h⟩

/-- **Γ's axiom of item 0 (sentence 99) is `nsvAxG`**, the clause with two distinct variables (kernel). -/
theorem svAx0_at : (TiePair.fnAxioms c)[0]? = some nsvAxG := by decide +kernel
noncomputable def svItem0 : P := (trAxiom [] [] ⟨0, "kernel", nsvAxG⟩).pat
theorem svItem0_at : (TiePair.gammaPats c)[0]? = some svItem0 := TiePair.gammaPats_at svAx0_at
kernel_rfl fnText_at0 : fnText[0]? = some U.ax99
/-- **The translation of the text's sentence 99 is that of `nsvAxS`**, the axiom with the two memberships
in the set variable `@VarS` (kernel), and the sentence is not Γ's item. -/
theorem sv0_text : (trS U.ax99).pat = (trAxiom [] [] ⟨0, "kernel", nsvAxS⟩).pat := by decide +kernel
theorem sv0_differs : svItem0 ≠ (trS U.ax99).pat := by decide +kernel
/-- **Sentence 99 and Γ's item 0 hold in the same models** of definedness, of the definition of
`\ceil` and of the sort constant `SortExp`. -/
theorem sv0_iff {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (hE : I ⊧ᴵ (sortConstantItem ⟨"SortExp", [], false⟩).pat) :
    (I ⊧ᴵ (trS U.ax99).pat) ↔ (I ⊧ᴵ svItem0) := by
  rw [sv0_text]; exact nsv_iff hD hc hE
/-- **W1**: the sentence, with the definition of `\ceil` and the sort constant `SortExp`, entails
Γ's item 0. -/
theorem sv0_w1 : TiePair.Texts ((trS U.ax99).pat :: svSigPats) ⊧ svItem0 :=
  fun {M} _ {I} hI => (sv0_iff (TiePair.defOK_texts hI)
    (hI _ (Or.inl (by simp [svSigPats]))) (hI _ (Or.inl (by simp [svSigPats])))).mp
    (hI _ (Or.inl (List.mem_cons_self ..)))

/-- **E for sentence 99**: Γ entails it, for every H (`sv0_iff`, `sv_sig_pats`). -/
theorem sv0_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax99).pat := by
  intro M _ I hI
  have hs : ∀ φ ∈ svSigPats, I ⊧ᴵ φ := fun φ hφ =>
    hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (sv_sig_pats H φ hφ)))))))
  exact (sv0_iff (defOK hI) (hs _ (by simp [svSigPats])) (hs _ (by simp [svSigPats]))).mpr
    (fnItem_sat hI svItem0_at)

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 0. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 svItem0

/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def pairSetAt : List Nat := [0]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have h0 := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h0), List.getElem?_map, hj]
  rfl

/-- **E for the function equations**: Γ entails each sentence of `fnText`, for every H; item 0 by `sv0_entailed`. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  by_cases h0 : j = 0
  · subst h0
    rw [fnText_at0] at hj
    rw [← Option.some.inj hj]
    exact sv0_entailed H
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))

/-- **The converse for `fnItems`**: each item but the set-variable ones given with two signature items (items 0) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([0] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h0 : j = 0
  · subst h0; simp at hu
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_set_ne (Ne.symm h0), List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to
Γ's through their sentences), Γ's rule items and the five parts Γ defines by predicates
(`TiePair.Pre`), for every H. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → TiePair.Pre (cH H) textPats ⊧ φ :=
  TiePair.gamma_from (shapeH H)


end KCore.TieE3SetvarNonlinear

#check @KCore.TieE3SetvarNonlinear.noRaw
#check @KCore.TieE3SetvarNonlinear.readsConfined_c
#check @KCore.TieE3SetvarNonlinear.userAxioms_eq
#check @KCore.TieE3SetvarNonlinear.coreOK
#check @KCore.TieE3SetvarNonlinear.wf_defn
#check @KCore.TieE3SetvarNonlinear.account
#check @KCore.TieE3SetvarNonlinear.account_sizes
#check @KCore.TieE3SetvarNonlinear.account_classes
#check @KCore.TieE3SetvarNonlinear.account_absent
#check @KCore.TieE3SetvarNonlinear.absent_closed
#check @KCore.TieE3SetvarNonlinear.absent_proj_below_c
#check @KCore.TieE3SetvarNonlinear.absent_proj_below
#check @KCore.TieE3SetvarNonlinear.lists_in_account
#check @KCore.TieE3SetvarNonlinear.attrs_agree
#check @KCore.TieE3SetvarNonlinear.sig_origin_but_next
#check @KCore.TieE3SetvarNonlinear.decls_entailed
#check @KCore.TieE3SetvarNonlinear.consistent
#check @KCore.TieE3SetvarNonlinear.fnFun_indices
#check @KCore.TieE3SetvarNonlinear.fnFun_account
#check @KCore.TieE3SetvarNonlinear.fnFun_checked
#check @KCore.TieE3SetvarNonlinear.fnFun_trS
#check @KCore.TieE3SetvarNonlinear.fnFun_at_values
#check @KCore.TieE3SetvarNonlinear.fnFun_at_values_step
#check @KCore.TieE3SetvarNonlinear.text_nextless
#check @KCore.TieE3SetvarNonlinear.nojunk_trivial_entailed
#check @KCore.TieE3SetvarNonlinear.nojunk_items_entailed
#check @KCore.TieE3SetvarNonlinear.nojunk_kitem_entailed
#check @KCore.TieE3SetvarNonlinear.cons_entailed
#check @KCore.TieE3SetvarNonlinear.idem_refuted
#print axioms KCore.TieE3SetvarNonlinear.noRaw
#print axioms KCore.TieE3SetvarNonlinear.readsConfined_c
#print axioms KCore.TieE3SetvarNonlinear.userAxioms_eq
#print axioms KCore.TieE3SetvarNonlinear.coreOK
#print axioms KCore.TieE3SetvarNonlinear.wf_defn
#print axioms KCore.TieE3SetvarNonlinear.account
#print axioms KCore.TieE3SetvarNonlinear.account_sizes
#print axioms KCore.TieE3SetvarNonlinear.account_classes
#print axioms KCore.TieE3SetvarNonlinear.account_absent
#print axioms KCore.TieE3SetvarNonlinear.absent_closed
#print axioms KCore.TieE3SetvarNonlinear.absent_proj_below_c
#print axioms KCore.TieE3SetvarNonlinear.absent_proj_below
#print axioms KCore.TieE3SetvarNonlinear.lists_in_account
#print axioms KCore.TieE3SetvarNonlinear.attrs_agree
#print axioms KCore.TieE3SetvarNonlinear.sig_origin_but_next
#print axioms KCore.TieE3SetvarNonlinear.decls_entailed
#print axioms KCore.TieE3SetvarNonlinear.consistent
#print axioms KCore.TieE3SetvarNonlinear.fnFun_indices
#print axioms KCore.TieE3SetvarNonlinear.fnFun_account
#print axioms KCore.TieE3SetvarNonlinear.fnFun_checked
#print axioms KCore.TieE3SetvarNonlinear.fnFun_trS
#print axioms KCore.TieE3SetvarNonlinear.fnFun_at_values
#print axioms KCore.TieE3SetvarNonlinear.fnFun_at_values_step
#print axioms KCore.TieE3SetvarNonlinear.text_nextless
#print axioms KCore.TieE3SetvarNonlinear.nojunk_trivial_entailed
#print axioms KCore.TieE3SetvarNonlinear.nojunk_items_entailed
#print axioms KCore.TieE3SetvarNonlinear.nojunk_kitem_entailed
#print axioms KCore.TieE3SetvarNonlinear.cons_entailed
#print axioms KCore.TieE3SetvarNonlinear.idem_refuted
#check @KCore.TieE3SetvarNonlinear.fns_account
#check @KCore.TieE3SetvarNonlinear.nsv_iff
#check @KCore.TieE3SetvarNonlinear.sv_sig_pats
#check @KCore.TieE3SetvarNonlinear.sv0_text
#check @KCore.TieE3SetvarNonlinear.sv0_differs
#check @KCore.TieE3SetvarNonlinear.sv0_iff
#check @KCore.TieE3SetvarNonlinear.sv0_w1
#check @KCore.TieE3SetvarNonlinear.sv0_entailed
#check @KCore.TieE3SetvarNonlinear.shape
#check @KCore.TieE3SetvarNonlinear.fns_entailed
#check @KCore.TieE3SetvarNonlinear.fns_from_text
#check @KCore.TieE3SetvarNonlinear.fn_prios
#check @KCore.TieE3SetvarNonlinear.gamma_from
#print axioms KCore.TieE3SetvarNonlinear.fns_account
#print axioms KCore.TieE3SetvarNonlinear.nsv_iff
#print axioms KCore.TieE3SetvarNonlinear.sv_sig_pats
#print axioms KCore.TieE3SetvarNonlinear.sv0_text
#print axioms KCore.TieE3SetvarNonlinear.sv0_differs
#print axioms KCore.TieE3SetvarNonlinear.sv0_iff
#print axioms KCore.TieE3SetvarNonlinear.sv0_w1
#print axioms KCore.TieE3SetvarNonlinear.sv0_entailed
#print axioms KCore.TieE3SetvarNonlinear.shape
#print axioms KCore.TieE3SetvarNonlinear.fns_entailed
#print axioms KCore.TieE3SetvarNonlinear.fns_from_text
#print axioms KCore.TieE3SetvarNonlinear.fn_prios
#print axioms KCore.TieE3SetvarNonlinear.gamma_from
