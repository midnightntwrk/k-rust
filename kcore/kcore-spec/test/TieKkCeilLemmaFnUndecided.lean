/-
  The tie (C14) on `f2-examples/kk-ceil-lemma-fn-undecided.kompile.kore`, the kompiled text of construct fixture kk-ceil-lemma-fn-undecided
  (`test/constructs/fixtures/kk-ceil-lemma-fn-undecided`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py kk-ceil-lemma-fn-undecided --reads-h 123`; run from the package root: `lake env lean -j1 test/TieKkCeilLemmaFnUndecided.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 252 sentences of the user module T243-CEIL-LEMMA-FN-UNDECIDED, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 204 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (28): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 158 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); parameter lemma: a
    hypothesis on H, at values, shown at one H and refuted at another (`paramlemma_account`,
    `paramlemma_heads`, `paramlemma_reads_h`, `ParamLemmaWitnessAtValues`, `kkclfu_witness`,
    `kkclfu_not_entailed`, `kkclfu_reads_rest`); no direction: `absent_closed`.

  The parameter lemmas (123) are lemmas whose truth at values reads a value the interpretation
  gives. 123, named by `--reads-h`, applies no such parameter: each applies, at a head Γ has, a
  symbol through which evaluation may read the interpretation (`paramlemma_reads_h`,
  `appliesHRead`), a function at argument lists none of its clauses decides, whose rest Γ states
  from the interpretation (`ΓFallback`), or a hook at a point its text leaves open. Each is owed as
  a hypothesis on H, at the valuations sending its variables to values (`EntailsAtValues (cH H) ad
  (trS ad).pat`), since Γ states a parameter's graph, a function's rest and a hook's open point at
  values only. The account holds them in the class `parameter lemma`, of the direction `hypothesis`.
  A hypothesis no H satisfies would tie a text without a model, so the tie owes one H at which the
  functions' obligations hold and every parameter lemma holds at values
  (`ParamLemmaWitnessAtValues`). Proved here, by hand: at `HookParams.none` the obligations hold and
  the lemma holds in every model of Γ at the valuations sending its variables to values
  (`kkclfu_witness`); at `H7`, which gives 7 at every point, it fails in a model of Γ at `A = 1`,
  `B = 0` (`kkclfu_not_entailed`), so no statement of it for every H holds and its class is no `user
  lemma`; the evaluator that reads nothing of the interpretation has no result of d at `(1, 0)`
  (`kkclfu_reads_rest`): the value there is d's rest. Every `simplification` equation of the user
  module whose left side's head is a parameter symbol without `impl` is one of them
  (`paramlemma_heads`).

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (4);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKkCeilLemmaFnUndecided

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/kk-ceil-lemma-fn-undecided.kompile.kore"
definition_of defn from "f2-examples/kk-ceil-lemma-fn-undecided.kompile.kore"
user_axioms U from "f2-examples/kk-ceil-lemma-fn-undecided.kompile.kore" module "T243-CEIL-LEMMA-FN-UNDECIDED"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "T243-CEIL-LEMMA-FN-UNDECIDED")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 252 := by decide +kernel

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
  [("function equation", [201, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
      224, 225, 226, 227, 228, 229, 230, 231, 232, 233]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 98, 99]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [108, 109, 110, 111, 112, 113, 114, 115, 116, 117]),
   ("function functional", [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      55, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 95, 96, 97, 100, 101, 102, 103,
      104, 105]),
   ("collection law", [52, 53, 54, 56, 57, 58, 59, 61, 62]),
   ("library", [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141,
      142, 143, 144, 145, 146, 147, 148, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
      161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
      179, 180, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197,
      198, 199, 200, 202, 236, 237, 238, 239, 253, 254]),
   ("set idempotence", [60]),
   ("set-variable lemma", [118, 119, 120, 121, 122, 255]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", [123]),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 39, 41, 72, 74, 78, 94, 106, 107, 149, 181, 203, 204, 205, 206, 234, 235, 240, 241, 242,
      243, 244, 245, 246, 247, 248, 249, 250, 251, 252])]

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
    [("function equation", 28), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 1), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 30)] := by
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
  [(240, "Bool"), (241, "GeneratedCounterCell"), (242, "GeneratedCounterCellOpt"),
   (243, "GeneratedTopCell"), (244, "GeneratedTopCellFragment"), (245, "Int"), (246, "K"),
   (247, "KCell"), (248, "KCellOpt"), (249, "KItem"), (250, "List"), (251, "Map"), (252, "Set")]

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
  [(117, "no junk"), (123, "parameter lemma"), (201, "function equation"), (206, "no direction")]

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

theorem sig_sizes : (sigItems c).length = 204 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 127, 90, 5, 32) := by
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
384]

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

/-! ## Function functional (14): the sort predicates' `functional` sentences, at values in every model of Γc -/

/- The class holds the `functional` sentences of 14 sort predicates `isX`,
`\exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val:SortBool{}, LblisX{}(K0:SortK{})))`. KCore builds
the sort predicates (`Semantics.sortPreds`): each has a value at every K, and a model of `Γc` reads
its application at a value's element as that value's element (`LibEv.sortPredFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and no condition over a
variable the patterns leave open). So each sentence holds in every model of `Γc`, and of `Γc` with
the step's closure, at every valuation sending K0 to a value, for every H, from the sort predicates'
own results and without `FnHyp`. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]

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

/-- None of the 14 reads a declaration or an alias. -/
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

/-! ## Function equations (28 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 28 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax201, U.ax219, U.ax227, U.ax226, U.ax225, U.ax224, U.ax231, U.ax230, U.ax233, U.ax232,
   U.ax229, U.ax228, U.ax208, U.ax207, U.ax218, U.ax217, U.ax214, U.ax213, U.ax216, U.ax215,
   U.ax221, U.ax220, U.ax223, U.ax222, U.ax210, U.ax209, U.ax212, U.ax211]

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

theorem nj108 : (trS U.ax108).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj113 : (trS U.ax113).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj116 : (trS U.ax116).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax108, U.ax113, U.ax116], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj108]; exact orTopBot_valid hD rfl
  · rw [nj113]; exact orTopBot_valid hD rfl
  · rw [nj116]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax109, U.ax110, U.ax111, U.ax112, U.ax114, U.ax115],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax109, U.ax110, U.ax111, U.ax112, U.ax114, U.ax115],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax117).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (117)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax117).pat := by
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax98, U.ax99]

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

theorem idem_pattern : U.ax60.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax60).pat = (trAxiom [] [] U.ax60).pat := by decide +kernel

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
theorem idem_vars : (U.ax60.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax60.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax60.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 60 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax60).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax60.ax.sortVars U.ax60.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax60.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax60.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 158, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax158).pat = (trAxiom [] [] U.ax158).pat := by decide +kernel
theorem s166_pattern : U.ax158.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax158.ax.sortVars.map sortVarKey ++ freeOf [] U.ax158.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax158.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 158 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax158.ax.sortVars U.ax158.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax158).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax158.ax.sortVars U.ax158.ax.pattern = t at he ⊢
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
/-- **Sentence 158 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax158 (trS U.ax158).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The parameter lemmas (123): owed as a hypothesis on H -/

/-- The text's lemmas whose truth at values reads a value the interpretation gives: those that apply
a parameter symbol no registry hook interprets (`isParamLemma`, or a `simplification` sentence of
K's builtin library applying one), and those `--reads-h` names (123), which apply a symbol
through which evaluation may read the interpretation (`paramlemma_reads_h`). -/
noncomputable def paramLemmaText : List AxiomDecl := [U.ax123]

/-- The parameter lemmas are the account's class `parameter lemma`, of the direction `hypothesis`
(Γ does not hold the sentence; at the member `cH H` it is owed at values). -/
theorem paramlemma_account : paramLemmaText.map (·.index) = classOf "parameter lemma" := by
  decide +kernel

/-- **What the tie owes of the parameter lemmas**: one interpretation `H` at which the functions'
obligations hold and every parameter lemma holds in every model of Γ at the valuations sending its
free element variables to values (`EntailsAtValues`), so that the text with its hypotheses has a
model. Γ states a parameter's graph at values only (`ΓDomains`), so the lemma is owed there. Proved
by hand: `kkclfu_witness`. -/
def ParamLemmaWitnessAtValues : Prop :=
  ∃ H : HookParams, FnObligations (cH H) callOrder [] ∧
    ∀ ad ∈ paramLemmaText, EntailsAtValues (cH H) ad (trS ad).pat

/-- Every sentence of the user module that carries `simplification`, is an equation
(`AttrsAgree.eqnHead`) and has at the head of its left side a parameter symbol no registry hook
interprets (`impl = none`) is of the class `parameter lemma`: the sentences `attrsAgree` does not
count as equations of such a parameter are held by the account as hypotheses on `H`. -/
theorem paramlemma_heads : userAxioms.all (fun ad =>
    !(AttrsAgree.has ad.ax.attributes "simplification" &&
      (AttrsAgree.eqnHead ad.ax.pattern).any (fun n =>
        c.params.any fun k => k.impl.isNone && c.symName k.sig.name == n)) ||
    (classOf "parameter lemma").contains ad.index) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- The lemmas `--reads-h` names (123) apply, at a head Γ has, a symbol through which evaluation may
read the interpretation (`appliesHRead`): the necessary condition of their class. -/
theorem paramlemma_reads_h : [U.ax123].all (fun ad => appliesHRead c ad.ax.pattern) = true := by
  decide +kernel

/-! ## The parameter lemma 123, by hand: `#Ceil(d(_A, B)) => {(B =/=Int 0) #Equals true}`

d's one clause is `d(A, B) => A requires B =/=Int 0`. Where `B` is not 0 it applies and `d(a, b)` is
`a` under every H (`d_clause_kkclfu`, `TiePair.eval_some_sound`). Where `B` is 0 it fails at every
`A` (`d_fails_kkclfu`), and `d(a, 0)` is d's rest, the interpretation's value (`Eval.rest`,
`Semantics.fnRest`): nothing at `HookParams.none` (`Faithful.eval_none_sound_core`), 7 at `H7`, which
gives 7 at every point. So at `HookParams.none` the two sides of the sentence agree at every pair of
integers, both the whole sort `Q0` where `B` is not 0 and both empty where it is (`kkclfu_witness`),
and at `H7` the left side at `(1, 0)` is the whole sort while the right side is empty, `false` and
`true` being two elements (`kkclfu_not_entailed`). The sentence holds under one interpretation and
fails under another: no statement of it for every H is true, and it is a hypothesis on H.
`kkclfu_reads_rest`: the evaluator that reads nothing of the interpretation (`Cert.evalFC`) has no
result at `(1, 0)`, where the value is the rest's. -/

/-- d. -/
def dSym : Sym := 384

/-- The function numbered `dSym`, as `lookupFn` finds it. -/
noncomputable def dFn : Fn := (c.lookupFn dSym).getD ⟨0, [], 0, [], false⟩

theorem dFn_lookup : c.lookupFn dSym = some dFn := by
  have h : (c.lookupFn dSym).isSome = true := by decide +kernel
  unfold dFn; cases hl : c.lookupFn dSym with
  | none => rw [hl] at h; cases h
  | some fn => rfl

theorem dFn_lookupH (H : HookParams) : (cH H).lookupFn dSym = some dFn := by
  rw [Semantics.lookupFn_withHooks]; exact dFn_lookup

theorem dFn_args : dFn.args = [Srt.int, Srt.int] := by decide +kernel
theorem dFn_result : dFn.result = Srt.int := by decide +kernel
theorem dFn_label : dFn.label = dSym := by decide +kernel
theorem dFn_len : dFn.clauses.length = 1 := by decide +kernel

/-- d's clause. -/
noncomputable def dCl : Clause := dFn.clauses[0]'(by rw [dFn_len]; decide)

theorem dFn_clauses : dFn.clauses = [dCl] := by kernel_rfl

theorem dCl_facts : dCl.vars = [Srt.int, Srt.int] ∧ dCl.pats = [.var 0, .var 1] ∧
    dCl.req = some (.app intNe [.var 1, .dv Srt.int (.int 0)]) ∧ dCl.pre = .top ∧ dCl.post = .top ∧
    dCl.exs = [] ∧ dCl.ens = none ∧ dCl.rhs = .var 0 :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl,
    by kernel_rfl⟩

theorem sorts_kkclfu (H : HookParams) (a b : Int) : (cH H).sortsOf [KCore.int a, KCore.int b] = some dFn.args := by
  rw [dFn_args]; rfl

theorem preTop_kkclfu (H : HookParams) : (cH H).clausesPreTop = true :=
  (Semantics.clausesPreTop_withHooks c H).trans (by decide +kernel)

theorem binds_kkclfu (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true :=
  (by decide +kernel : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)

/-- `_=/=Int_` at two integers. -/
theorem hook_ne_kkclfu (x y : Int) :
    hook intNe [KCore.int x, KCore.int y] = some (some (KCore.bool (decide (x ≠ y)))) := rfl

/-- The `requires` of d's clause, `B =/=Int 0`, under a substitution sending `B` to `b`. -/
theorem req_kkclfu (H : HookParams) {σ : Subst} {b : Int} (hσ : σ.lookup 1 = some (KCore.int b)) :
    EvalTerm (cH H) σ (.app intNe [.var 1, .dv Srt.int (.int 0)]) (some (KCore.bool (decide (b ≠ 0)))) :=
  EvalTerm.hook (rs := [σ.lookup 1, some (KCore.int 0)]) (by show c.isCtor intNe = false; decide +kernel) rfl
    (.cons EvalTerm.var (.cons EvalTerm.dv .nil))
    (fun vs hvs => by
      rw [hσ] at hvs
      cases hvs
      exact Semantics.hookRes_of_value (hook_ne_kkclfu b 0))
    (fun h => by rw [hσ] at h; cases h)

/-- **Where `B` is not 0, d's clause applies**: `d(a, b)` is `a`, under every H. -/
theorem d_clause_kkclfu (H : HookParams) (a b : Int) (hb : b ≠ 0) :
    Eval (cH H) dSym [KCore.int a, KCore.int b] (some (KCore.int a)) := by
  obtain ⟨hv, hp, hr, hpre, hpost, hexs, hens, hrhs⟩ := dCl_facts
  refine Eval.clause (cl := dCl) (σ := [(0, KCore.int a), (1, KCore.int b)]) (dFn_lookupH H)
    (by rw [dFn_clauses]; exact List.mem_singleton_self _) ?_ ?_ ?_ ?_ ?_ hexs ?_ ?_ ?_
  · intro i t hi
    rw [hv] at hi
    match i, hi with
    | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨KCore.int a, rfl, rfl⟩
    | 1, hi => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨KCore.int b, rfl, rfl⟩
    | _ + 2, hi => simp at hi
  · rw [hp]; exact .cons (.var rfl) (.cons (.var rfl) .nil)
  · intro t ht
    rw [hr] at ht; cases ht
    have h := req_kkclfu H (σ := [(0, KCore.int a), (1, KCore.int b)]) (b := b) rfl
    rwa [decide_eq_true hb] at h
  · rw [hpre]; exact .top
  · intro cl' hcl' _ hlt
    rw [dFn_clauses, List.mem_singleton] at hcl'
    subst hcl'; exact absurd hlt (Nat.lt_irrefl _)
  · rw [hrhs]; exact EvalTerm.var (σ := [(0, KCore.int a), (1, KCore.int b)]) (i := 0)
  · intro t ht; rw [hens] at ht; cases ht
  · rw [hpost]; exact .top

/-- **Where `B` is 0, d's clause fails**, at every `A` and under every H: its `requires` is `false`. -/
theorem d_fails_kkclfu (H : HookParams) (a : Int) : ∀ cl ∈ dFn.clauses, Fails (cH H) [KCore.int a, KCore.int 0] cl := by
  obtain ⟨-, hp, hr, -⟩ := dCl_facts
  intro cl hcl
  rw [dFn_clauses, List.mem_singleton] at hcl
  subst hcl
  refine Fails.intro fun σ _ hpv => ?_
  rw [hp] at hpv
  cases hpv with
  | cons _ hs =>
    cases hs with
    | cons h1 _ =>
      cases h1 with
      | var h1 => exact ReqFails.intro hr (req_kkclfu H h1) (by decide)

/-- **At `B = 0`, d has its rest**, under every H. -/
theorem d_rest_kkclfu (H : HookParams) (a : Int) :
    Eval (cH H) dSym [KCore.int a, KCore.int 0] ((cH H).fnRest dFn [KCore.int a, KCore.int 0]) :=
  .rest (dFn_lookupH H) (d_fails_kkclfu H a)

/-- The interpretation giving 7 at every point. -/
def H7 : HookParams := ⟨fun _ _ => some (KCore.int 7)⟩

theorem rest_none_kkclfu (a : Int) : (cH HookParams.none).fnRest dFn [KCore.int a, KCore.int 0] = none := rfl

theorem rest_H7_kkclfu : (cH H7).fnRest dFn [KCore.int 1, KCore.int 0] = some (KCore.int 7) := by
  unfold Semantics.fnRest
  rw [sorts_kkclfu, dFn_result]
  rfl

/-- **The point the sentence reads at `B = 0` is d's rest**: the evaluator that has no result where it
would read the interpretation (`Cert.evalFC`) has none at `(1, 0)`. -/
theorem kkclfu_reads_rest : Cert.evalFC c 60 dSym [KCore.int 1, KCore.int 0] = none := by
  decide +kernel

/-! ### The sentence's parts in a model -/

def vA : Kore.Pattern := KoreAML.ev "Var'Unds'A" (KoreAML.srt "Int")
def vB : Kore.Pattern := KoreAML.ev "VarB" (KoreAML.srt "Int")
def kA : VarKey := .evar "Var'Unds'A" (KoreAML.srt "Int")
def kB : VarKey := .evar "VarB" (KoreAML.srt "Int")
def Q0s : Kore.KSort := .var ⟨⟨⟨"Q0"⟩⟩⟩
def dName : String := "Lbld'LParUndsCommUndsRParUnds'T243-CEIL-LEMMA-FN-UNDECIDED'Unds'Int'Unds'Int'Unds'Int"
/-- `d(A, B)`. -/
def dAB : Kore.Pattern := .app ⟨⟨dName⟩⟩ [] [vA, vB]
/-- `B =/=Int 0`. -/
def neB : Kore.Pattern := .app ⟨⟨"Lbl'UndsEqlsSlshEqls'Int'Unds'"⟩⟩ [] [vB, .dv (KoreAML.srt "Int") "0"]
/-- `true`. -/
def tB : Kore.Pattern := .dv (KoreAML.srt "Bool") "true"

/-- The variable table of sentence 123. -/
def keys123 : VarTable := [.sortVar "R", .sortVar "Q0", kA, kB]

theorem s123_pattern : U.ax123.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0s KoreAML.R (.ceil (KoreAML.srt "Int") Q0s dAB)
      (.and Q0s [.equals (KoreAML.srt "Bool") Q0s neB tB, .top Q0s])) := by decide +kernel

theorem s123_text : (trS U.ax123).pat = (trAxiom [] [] U.ax123).pat ∧
    tableOf U.ax123.ax.sortVars U.ax123.ax.pattern = keys123 ∧
    (U.ax123.ax.sortVars.map sortVarKey ++ freeOf [] U.ax123.ax.pattern).eraseDups =
      .sortVar "R" :: [.sortVar "Q0", kA, kB] ∧
    (freeOf [] U.ax123.ax.pattern).eraseDups = [kA, kB] := by decide +kernel

theorem d_name_kkclfu (H : HookParams) : (cH H).symName dSym = dName ∧ instDecode? dName = none :=
  (by decide +kernel : c.symName dSym = dName ∧ instDecode? dName = none)
theorem ne_name_kkclfu (H : HookParams) :
    (cH H).symName intNe = "Lbl'UndsEqlsSlshEqls'Int'Unds'" ∧ instDecode? "Lbl'UndsEqlsSlshEqls'Int'Unds'" = none :=
  (by decide +kernel : c.symName intNe = "Lbl'UndsEqlsSlshEqls'Int'Unds'" ∧
    instDecode? "Lbl'UndsEqlsSlshEqls'Int'Unds'" = none)
theorem den_true_kkclfu (H : HookParams) :
    den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel
theorem bool_numbered_kkclfu (H : HookParams) : Srt.bool < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.bool < nRegSorts + c.sortNames.length)
theorem bool_name_kkclfu (H : HookParams) : (cH H).sortName Srt.bool = "Bool" :=
  (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem bool_apart_kkclfu (H : HookParams) : apartSort (cH H) Srt.bool = true :=
  (by decide +kernel : apartSort c Srt.bool = true)

section model
variable {H : HookParams} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- An integer's element is an element of Int. -/
theorem int_elem_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI)
    (n : Int) : Inh I σI (elemOf (cH H) I (KCore.int n)) := by
  have h := (elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0).2
  rw [int_name] at h
  exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσI1).mp h

/-- A Bool's element is an element of Bool. -/
theorem bool_elem_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {σB : M} (hσB1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Bool")) a ↔ a = σB)
    (x : Bool) : Inh I σB (elemOf (cH H) I (KCore.bool x)) := by
  have h := (elemOf_spec hI (show (cH H).sortOf (KCore.bool x) = some Srt.bool from rfl) KoreAML.val0).2
  rw [bool_name_kkclfu] at h
  exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσB1).mp h

/-- `false` and `true` are two elements. -/
theorem false_ne_true_kkclfu (hI : I ⊧ᴵP Γ (cH H)) :
    elemOf (cH H) I (KCore.bool false) ≠ elemOf (cH H) I (KCore.bool true) := by
  intro he
  obtain ⟨hsok, hsr', -, hg, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have := values_apart hI hg htr (bool_apart_kkclfu H) (show (cH H).sortOf (KCore.bool false) = some Srt.bool from rfl)
    (show (cH H).sortOf (KCore.bool true) = some Srt.bool from rfl) he
  exact absurd this (by decide)

/-- `d(A, B)` at a valuation sending `A`, `B` to the integers `a`, `b`: the application of d to them. -/
theorem dAB_den_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {a b : Int} {e : Valuation M}
    (hA : e.evalEvar (keys123.ev kA) = elemOf (cH H) I (KCore.int a))
    (hB : e.evalEvar (keys123.ev kB) = elemOf (cH H) I (KCore.int b)) (y : M) :
    (KoreAML.tr ⟨keys123, []⟩ dAB).interpret I e y ↔
      (KoreAML.den (symApp (cH H) dSym (GroundTerm.koreList (cH H) [KCore.int a, KCore.int b]))).interpret I e y := by
  obtain ⟨hesA, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int a) = some Srt.int from rfl) e
  obtain ⟨hesB, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int b) = some Srt.int from rfl) e
  have h1 : KoreAML.tr ⟨keys123, []⟩ dAB =
      (KoreAML.sym (.symbol dName) ⬝ .evar (keys123.ev kA)) ⬝ .evar (keys123.ev kB) := rfl
  have h2 : KoreAML.den (symApp (cH H) dSym (GroundTerm.koreList (cH H) [KCore.int a, KCore.int b])) =
      (KoreAML.sym (.symbol dName) ⬝ den (cH H) (KCore.int a)) ⬝ den (cH H) (KCore.int b) := by
    rw [symApp_noInst (c := cH H) (f := dSym) (by rw [(d_name_kkclfu H).1]; exact (d_name_kkclfu H).2),
      (d_name_kkclfu H).1]; rfl
  rw [h1, h2]
  refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) y
  · rw [interp_evar, hA, hesA]
  · rw [interp_evar, hB, hesB]

/-- `B =/=Int 0` at a valuation sending `B` to the integer `b`: the element of `b ≠ 0`. -/
theorem neB_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {b : Int} {e : Valuation M}
    (hB : e.evalEvar (keys123.ev kB) = elemOf (cH H) I (KCore.int b)) (y : M) :
    (KoreAML.tr ⟨keys123, []⟩ neB).interpret I e y ↔ y = elemOf (cH H) I (KCore.bool (decide (b ≠ 0))) := by
  have hD := defOK hI
  obtain ⟨hesB, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int b) = some Srt.int from rfl) e
  obtain ⟨hesV, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.bool (decide (b ≠ 0))) = some Srt.bool from rfl) e
  have hgraph := sat_dom hI (Or.inl ⟨⟨intNe, [Srt.int, Srt.int], Srt.bool⟩, [KCore.int b, KCore.int 0],
    some (KCore.bool (decide (b ≠ 0))), by decide +kernel, rfl, hook_ne_kkclfu b 0, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  have h1 : KoreAML.tr ⟨keys123, []⟩ neB =
      (KoreAML.sym (.symbol "Lbl'UndsEqlsSlshEqls'Int'Unds'") ⬝ .evar (keys123.ev kB)) ⬝
        (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt")) := rfl
  have h2 : KoreAML.den (symApp (cH H) intNe (GroundTerm.koreList (cH H) [KCore.int b, KCore.int 0])) =
      (KoreAML.sym (.symbol "Lbl'UndsEqlsSlshEqls'Int'Unds'") ⬝ den (cH H) (KCore.int b)) ⬝ den (cH H) (KCore.int 0) := by
    rw [symApp_noInst (c := cH H) (f := intNe) (by rw [(ne_name_kkclfu H).1]; exact (ne_name_kkclfu H).2),
      (ne_name_kkclfu H).1]; rfl
  have hL : (KoreAML.tr ⟨keys123, []⟩ neB).interpret I e y ↔
      (KoreAML.den (symApp (cH H) intNe (GroundTerm.koreList (cH H) [KCore.int b, KCore.int 0]))).interpret I e y := by
    rw [h1, h2]
    refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) y
    · rw [interp_evar, hB, hesB]
    · rw [den_int0]
  rw [hL, hg2 y, hesV y]

/-- `true`: the element of `true`. -/
theorem tB_kkclfu (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (y : M) :
    (KoreAML.tr ⟨keys123, []⟩ tB).interpret I e y ↔ y = elemOf (cH H) I (KCore.bool true) := by
  obtain ⟨hes, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.bool true) = some Srt.bool from rfl) e
  rw [← hes y, den_true_kkclfu]; exact Iff.rfl

omit [Inhabited M] in
/-- `⊤` at a sort variable denoting the sort `σQ`: the sort. -/
theorem top_var_kkclfu (hD : DefOK I) {e : Valuation M}
    {t : VarTable} {α : Kore.SortVar} {σQ : M} (hQv : ∀ b, (KoreAML.trSort t (.var α)).interpret I e b ↔ b = σQ)
    (b : M) : (KoreAML.tr ⟨t, []⟩ (.top (.var α))).interpret I e b ↔ Inh I σQ b := by
  rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [KoreAML.trSort]; simp [Pattern.isFreeEvar]; exact fun h => ev_ne_top h.symm),
    KoreAML.interp_inhOf_of hQv]

/-- **The right side**, `{B =/=Int 0 #Equals true} #And #Top`, at an element `x` of the sort `Q0`
denotes: it holds exactly where `b` is not 0. -/
theorem rhs_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {b : Int} {e : Valuation M}
    (hB : e.evalEvar (keys123.ev kB) = elemOf (cH H) I (KCore.int b)) {σQ : M}
    (hQv : ∀ y, (KoreAML.trSort keys123 Q0s).interpret I e y ↔ y = σQ) (hQ : IsSort I σQ) (x : M) (hx : Inh I σQ x) :
    (KoreAML.tr ⟨keys123, []⟩ (.and Q0s [.equals (KoreAML.srt "Bool") Q0s neB tB, .top Q0s])).interpret I e x ↔ b ≠ 0 := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered_kkclfu H)
  rw [bool_name_kkclfu] at hσB1
  have hSB : ∀ y, (KoreAML.trSort keys123 (KoreAML.srt "Bool")).interpret I e y ↔ y = σB := fun y => by
    rw [trSort_srt]; exact hσB1 y
  have hT : (KoreAML.tr ⟨keys123, []⟩ (.top Q0s)).interpret I e x ↔ Inh I σQ x := top_var_kkclfu hD hQv x
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]
  rw [KoreAML.interp_sAnd, hT, KoreAML.tr, KoreAML.interp_sEquals hD hc hSB hQv hσB2 hQ]
  constructor
  · rintro ⟨⟨-, h⟩, -⟩ hb0
    subst hb0
    have hf := (h _ (bool_elem_kkclfu hI hσB1 false)).mp ((neB_kkclfu hI hB _).mpr rfl)
    exact false_ne_true_kkclfu hI ((tB_kkclfu hI e _).mp hf)
  · intro hb
    refine ⟨⟨hx, fun y _ => ?_⟩, hx⟩
    rw [neB_kkclfu hI hB y, tB_kkclfu hI e y, decide_eq_true hb]

/-- **The left side**, `#Ceil(d(A, B))`, at an element `x` of the sort `Q0`: it holds exactly where
`d(A, B)` has an element, given that its elements are integers'. -/
theorem lhs_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {e : Valuation M} {σQ : M}
    (hQv : ∀ y, (KoreAML.trSort keys123 Q0s).interpret I e y ↔ y = σQ) (hQ : IsSort I σQ) (x : M) (hx : Inh I σQ x)
    {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI) (hσI2 : IsSort I σI)
    (hd : ∀ y, (KoreAML.tr ⟨keys123, []⟩ dAB).interpret I e y → Inh I σI y) :
    (KoreAML.tr ⟨keys123, []⟩ (.ceil (KoreAML.srt "Int") Q0s dAB)).interpret I e x ↔
      ∃ y, (KoreAML.tr ⟨keys123, []⟩ dAB).interpret I e y := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hS : ∀ y, (KoreAML.trSort keys123 (KoreAML.srt "Int")).interpret I e y ↔ y = σI := fun y => by
    rw [trSort_srt]; exact hσI1 y
  rw [KoreAML.tr, KoreAML.interp_sCeil hD hc hS hQv hσI2 hQ hd x]
  exact ⟨And.left, fun h => ⟨h, hx⟩⟩

/-- d at `(a, b)` with `b ≠ 0`, in a model: `a`. -/
theorem d_val_kkclfu (hI : I ⊧ᴵP Γ (cH H)) {a b : Int} (hb : b ≠ 0) {e : Valuation M}
    (hA : e.evalEvar (keys123.ev kA) = elemOf (cH H) I (KCore.int a))
    (hB : e.evalEvar (keys123.ev kB) = elemOf (cH H) I (KCore.int b)) (y : M) :
    (KoreAML.tr ⟨keys123, []⟩ dAB).interpret I e y ↔ y = elemOf (cH H) I (KCore.int a) := by
  have hs : Γ (cH H) ⊧ (KoreAML.den (symApp (cH H) dSym (GroundTerm.koreList (cH H) [KCore.int a, KCore.int b])) ≡
      den (cH H) (KCore.int a)) := TiePair.eval_some_sound (hpreTop := preTop_kkclfu H) (cH H) (hypSound_of_core (coreOKH H))
    (binds_kkclfu H) (d_clause_kkclfu H a b hb) (dFn_lookupH H) (sorts_kkclfu H a b)
  obtain ⟨hes, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int a) = some Srt.int from rfl) e
  rw [dAB_den_kkclfu hI hA hB y]
  exact ((KoreAML.interp_equal (defOK hI)).mp (hs hI e default) y).trans (hes y)

/-- d at `(a, 0)` at `HookParams.none`, in a model: nothing. -/
theorem d_none_kkclfu {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH HookParams.none)) {a : Int} {e : Valuation M}
    (hA : e.evalEvar (keys123.ev kA) = elemOf (cH HookParams.none) I (KCore.int a))
    (hB : e.evalEvar (keys123.ev kB) = elemOf (cH HookParams.none) I (KCore.int 0)) (y : M) :
    ¬ (KoreAML.tr ⟨keys123, []⟩ dAB).interpret I e y := by
  have hE := d_rest_kkclfu HookParams.none a
  rw [rest_none_kkclfu] at hE
  have hs : Γ (cH HookParams.none) ⊧ (KoreAML.den (symApp (cH HookParams.none) dSym
      (GroundTerm.koreList (cH HookParams.none) [KCore.int a, KCore.int 0])) ≡ ⊥) :=
    eval_none_sound_core (cH HookParams.none) (preTop_kkclfu _) (hypSound_of_core (coreOKH _))
    (binds_kkclfu _) hE (dFn_lookupH _) (sorts_kkclfu _ a 0)
  rw [dAB_den_kkclfu hI hA hB y, (KoreAML.interp_equal (defOK hI)).mp (hs hI e default) y]
  simp [Pattern.interpret]

/-- d at `(1, 0)` at `H7`, in a model: 7. -/
theorem d_seven_kkclfu {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H7)) {e : Valuation M}
    (hA : e.evalEvar (keys123.ev kA) = elemOf (cH H7) I (KCore.int 1))
    (hB : e.evalEvar (keys123.ev kB) = elemOf (cH H7) I (KCore.int 0)) (y : M) :
    (KoreAML.tr ⟨keys123, []⟩ dAB).interpret I e y ↔ y = elemOf (cH H7) I (KCore.int 7) := by
  have hE := d_rest_kkclfu H7 1
  rw [rest_H7_kkclfu] at hE
  have hs : Γ (cH H7) ⊧ (KoreAML.den (symApp (cH H7) dSym (GroundTerm.koreList (cH H7) [KCore.int 1, KCore.int 0])) ≡
      den (cH H7) (KCore.int 7)) := TiePair.eval_some_sound (hpreTop := preTop_kkclfu H7) (cH H7) (hypSound_of_core (coreOKH H7))
    (binds_kkclfu H7) hE (dFn_lookupH H7) (sorts_kkclfu H7 1 0)
  obtain ⟨hes, -⟩ := elemOf_spec hI (show (cH H7).sortOf (KCore.int 7) = some Srt.int from rfl) e
  rw [dAB_den_kkclfu hI hA hB y]
  exact ((KoreAML.interp_equal (defOK hI)).mp (hs hI e default) y).trans (hes y)

end model

/-- **A sentence `⊤_R → (L =_{S,R} Rt)` at one valuation**: it holds where its guards give a sort
`σS` for `S` on whose elements `L` and `Rt` agree. -/
theorem frame_kkclfu {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (ad : AxiomDecl) (T : VarTable) (ks : List VarKey) (S : Kore.KSort)
    (L Rt : Kore.Pattern)
    (hpat : ad.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals S KoreAML.R L Rt))
    (htab : tableOf ad.ax.sortVars ad.ax.pattern = T)
    (hfree : (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups = .sortVar "R" :: ks)
    (e : Valuation M) (m : M)
    (hmain : (∀ k ∈ ks, (guardOf T k).interpret I e m) → ∃ σS : M,
      (∀ b, (KoreAML.trSort T S).interpret I e b ↔ b = σS) ∧ IsSort I σS ∧
      ∀ b, Inh I σS b → ((KoreAML.tr ⟨T, []⟩ L).interpret I e b ↔ (KoreAML.tr ⟨T, []⟩ Rt).interpret I e b)) :
    (trAxiom [] [] ad).pat.interpret I e m := by
  unfold trAxiom
  dsimp only
  rw [hfree, htab, hpat]
  rw [interpret_impl]
  intro hg
  have hall := conjList_mem hg
  have hR := (interp_guard_sortVar hD).mp (hall _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩))
  obtain ⟨σS, hSv, hσS, hm⟩ := hmain fun k hk => hall _ (List.mem_map.mpr ⟨k, List.mem_cons_of_mem _ hk, rfl⟩)
  have hRv : ∀ b, (KoreAML.trSort T KoreAML.R).interpret I e b ↔ b = e.evalEvar (T.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [interp_equal hD]
  intro a
  simp only [sortOf]
  rw [KoreAML.tr, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hRv]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hSv hRv hσS hR]
    exact ⟨ha, hm⟩

/-- At a valuation sending the sentence's variables to values: they are integers' elements. -/
theorem atAB_kkclfu {H : HookParams} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {e : Valuation M} (hat : AtValues (cH H) I e U.ax123.ax) (k : String)
    (hk : VarKey.evar k (KoreAML.srt "Int") ∈ (freeOf [] U.ax123.ax.pattern).eraseDups) :
    ∃ n : Int, e.evalEvar (keys123.ev (.evar k (KoreAML.srt "Int"))) = elemOf (cH H) I (KCore.int n) := by
  obtain ⟨v, S, hS, hv, hden⟩ := hat k (KoreAML.srt "Int") hk
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  refine ⟨n, ((elemOf_spec hI hv e).1 _).mp ?_⟩
  rw [← s123_text.2.1]; exact hden

/-- **Sentence 123 holds at values at `HookParams.none`**: at `A = a`, `B = b`, where `b` is not 0 both
sides are the whole sort `Q0` (`d(a, b)` is `a`, `b =/=Int 0` is `true`), and where it is 0 both are
empty (`d(a, 0)` is nothing, `0 =/=Int 0` is `false`, no `true`). -/
theorem s123_at_values : EntailsAtValues (cH HookParams.none) U.ax123 (trS U.ax123).pat := by
  intro M _ I hI e hat m
  obtain ⟨h1, h2, h3, h4⟩ := s123_text
  rw [h1]
  haveI : OvlOK (cH HookParams.none) := ovlOK_of_core (coreOKH _)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH HookParams.none))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered HookParams.none)
  rw [int_name] at hσI1
  obtain ⟨a, hA⟩ := atAB_kkclfu hI hat "Var'Unds'A" (by rw [h4]; exact List.mem_cons_self)
  obtain ⟨b, hB⟩ := atAB_kkclfu hI hat "VarB" (by rw [h4]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine frame_kkclfu hD hc U.ax123 keys123 _ _ _ _ s123_pattern h2 h3 e m fun hgs => ?_
  have hQ : IsSort I (e.evalEvar (keys123.ev (.sortVar "Q0"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (hgs _ List.mem_cons_self)
  have hQv : ∀ y, (KoreAML.trSort keys123 Q0s).interpret I e y ↔ y = e.evalEvar (keys123.ev (.sortVar "Q0")) :=
    fun y => Iff.rfl
  refine ⟨_, hQv, hQ, fun x hx => ?_⟩
  rw [rhs_kkclfu hI hB hQv hQ x hx]
  by_cases hb : b = 0
  · subst hb
    have hn := d_none_kkclfu hI hA hB
    rw [lhs_kkclfu hI hQv hQ x hx hσI1 hσI2 (fun y hy => absurd hy (hn y))]
    exact ⟨fun ⟨y, hy⟩ => absurd hy (hn y), fun h => absurd rfl h⟩
  · have hv := d_val_kkclfu hI hb hA hB
    rw [lhs_kkclfu hI hQv hQ x hx hσI1 hσI2 (fun y hy => by rw [(hv y).mp hy]; exact int_elem_kkclfu hI hσI1 a)]
    exact ⟨fun _ => hb, fun _ => ⟨_, (hv _).mpr rfl⟩⟩

/-- **The witness**: at `HookParams.none` the obligations hold (`obl_nil`) and the parameter lemma
holds at values (`s123_at_values`). -/
theorem kkclfu_witness : ParamLemmaWitnessAtValues := by
  refine ⟨HookParams.none, obl_nil HookParams.none, fun ad had => ?_⟩
  simp only [paramLemmaText, List.mem_cons, List.not_mem_nil, or_false] at had
  subst had
  exact s123_at_values

/-- **The sentence fails at `H7`, which gives 7 at every point** (the record that it is no `user
lemma`): in a model of Γ (cH H7), which `consistent` gives, at `A = 1`, `B = 0` and with `R` and `Q0`
sent to Int, `d(1, 0)` denotes 7, so the left side is the whole sort, while `0 =/=Int 0` is `false`
and the right side is empty. -/
theorem kkclfu_not_entailed : ¬ EntailsAtValues (cH H7) U.ax123 (trS U.ax123).pat := by
  intro hent
  obtain ⟨M, inst, I, hI'⟩ := consistent H7
  have hI : I ⊧ᴵP Γ (cH H7) := fun φ hφ => hI' φ (Or.inl (Or.inl hφ))
  obtain ⟨h1, h2, h3, h4⟩ := s123_text
  haveI : OvlOK (cH H7) := ovlOK_of_core (coreOKH _)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H7))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H7)
  rw [int_name] at hσI1
  let x1 := elemOf (cH H7) I (KCore.int 1)
  let x0 := elemOf (cH H7) I (KCore.int 0)
  let f0 : EVar → M := Function.update (fun _ => σI) (keys123.ev kB) x0
  let e : Valuation M := ⟨Function.update f0 (keys123.ev kA) x1, KoreAML.val0.evalSvar⟩
  have hAB : keys123.ev kB ≠ keys123.ev kA := by decide
  have hRA : keys123.ev (.sortVar "R") ≠ keys123.ev kA := by decide
  have hRB : keys123.ev (.sortVar "R") ≠ keys123.ev kB := by decide
  have hQA : keys123.ev (.sortVar "Q0") ≠ keys123.ev kA := by decide
  have hQB : keys123.ev (.sortVar "Q0") ≠ keys123.ev kB := by decide
  have hA : e.evalEvar (keys123.ev kA) = x1 := Function.update_same (keys123.ev kA) x1 f0
  have hB : e.evalEvar (keys123.ev kB) = x0 :=
    (Function.update_noteq hAB x1 f0).trans (Function.update_same (keys123.ev kB) x0 (fun _ => σI))
  have hR : e.evalEvar (keys123.ev (.sortVar "R")) = σI :=
    (Function.update_noteq hRA x1 f0).trans (Function.update_noteq hRB x0 (fun _ => σI))
  have hQ0 : e.evalEvar (keys123.ev (.sortVar "Q0")) = σI :=
    (Function.update_noteq hQA x1 f0).trans (Function.update_noteq hQB x0 (fun _ => σI))
  have hx1 := int_elem_kkclfu hI hσI1 1
  have hx0 := int_elem_kkclfu hI hσI1 0
  have hS : ∀ y, (KoreAML.trSort keys123 (KoreAML.srt "Int")).interpret I e y ↔ y = σI := fun y => by
    rw [trSort_srt]; exact hσI1 y
  -- the valuation sends the sentence's variables to values
  have hat : AtValues (cH H7) I e U.ax123.ax := by
    intro n s hmem
    rw [h4] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, kA, kB, VarKey.evar.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨KCore.int 1, Srt.int, by decide +kernel, rfl, ?_⟩
      rw [h2]; exact ((elemOf_spec hI (show (cH H7).sortOf (KCore.int 1) = some Srt.int from rfl) e).1 _).mpr hA
    · refine ⟨KCore.int 0, Srt.int, by decide +kernel, rfl, ?_⟩
      rw [h2]; exact ((elemOf_spec hI (show (cH H7).sortOf (KCore.int 0) = some Srt.int from rfl) e).1 _).mpr hB
  have hsat := hent M inst I hI e hat x0
  rw [h1] at hsat
  unfold trAxiom at hsat
  dsimp only at hsat
  rw [h3, h2, s123_pattern, interpret_impl] at hsat
  have hRv : ∀ y, (KoreAML.trSort keys123 KoreAML.R).interpret I e y ↔ y = σI :=
    fun y => by rw [trSort_R, KoreAML.interp_evar, hR]
  have hQv : ∀ y, (KoreAML.trSort keys123 Q0s).interpret I e y ↔ y = σI := fun y => by
    show y = e.evalEvar (keys123.ev (.sortVar "Q0")) ↔ _; rw [hQ0]
  -- the guards hold
  have hg := interp_conjList (ws := (VarKey.sortVar "R" :: [VarKey.sortVar "Q0", kA, kB]).map
      (guardOf keys123)) (I := I) (e := e) (m := x0) fun w hw => by
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (KoreAML.interp_guard_sortVar hD).mpr (by rw [hR]; exact hσI2)
    · exact (KoreAML.interp_guard_sortVar hD).mpr (by rw [hQ0]; exact hσI2)
    · refine (KoreAML.interp_guard_evar hD).mpr ?_
      rw [KoreAML.interp_inhOf_of hS]; change Inh I σI (e.evalEvar (keys123.ev kA)); rw [hA]; exact hx1
    · refine (KoreAML.interp_guard_evar hD).mpr ?_
      rw [KoreAML.interp_inhOf_of hS]; change Inh I σI (e.evalEvar (keys123.ev kB)); rw [hB]; exact hx0
  have h5 := (KoreAML.interp_equal hD).mp (hsat hg) x0
  simp only [sortOf] at h5
  rw [KoreAML.tr, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hRv] at h5
  have hX : (KoreAML.tr ⟨keys123, []⟩ (.top KoreAML.R)).interpret I e x0 := (top_var_kkclfu hD hRv x0).mpr hx0
  have h6 := (h5.mpr hx0).2 hX
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hQv hRv hσI2 hσI2] at h6
  have h7 := (h6.2 x0 hx0)
  have h7v := d_seven_kkclfu hI hA hB
  rw [lhs_kkclfu hI hQv hσI2 x0 hx0 hσI1 hσI2 (fun y hy => by rw [(h7v y).mp hy]; exact int_elem_kkclfu hI hσI1 7),
    rhs_kkclfu hI hB hQv hσI2 x0 hx0] at h7
  exact (h7.mp ⟨_, (h7v _).mpr rfl⟩) rfl

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

end KCore.TieKkCeilLemmaFnUndecided

#check @KCore.TieKkCeilLemmaFnUndecided.noRaw
#check @KCore.TieKkCeilLemmaFnUndecided.readsConfined_c
#check @KCore.TieKkCeilLemmaFnUndecided.userAxioms_eq
#check @KCore.TieKkCeilLemmaFnUndecided.coreOK
#check @KCore.TieKkCeilLemmaFnUndecided.wf_defn
#check @KCore.TieKkCeilLemmaFnUndecided.account
#check @KCore.TieKkCeilLemmaFnUndecided.account_sizes
#check @KCore.TieKkCeilLemmaFnUndecided.account_classes
#check @KCore.TieKkCeilLemmaFnUndecided.account_absent
#check @KCore.TieKkCeilLemmaFnUndecided.absent_closed
#check @KCore.TieKkCeilLemmaFnUndecided.absent_proj_below_c
#check @KCore.TieKkCeilLemmaFnUndecided.absent_proj_below
#check @KCore.TieKkCeilLemmaFnUndecided.lists_in_account
#check @KCore.TieKkCeilLemmaFnUndecided.attrs_agree
#check @KCore.TieKkCeilLemmaFnUndecided.sig_origin_but_next
#check @KCore.TieKkCeilLemmaFnUndecided.decls_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.consistent
#check @KCore.TieKkCeilLemmaFnUndecided.fnFun_indices
#check @KCore.TieKkCeilLemmaFnUndecided.fnFun_account
#check @KCore.TieKkCeilLemmaFnUndecided.fnFun_checked
#check @KCore.TieKkCeilLemmaFnUndecided.fnFun_trS
#check @KCore.TieKkCeilLemmaFnUndecided.fnFun_at_values
#check @KCore.TieKkCeilLemmaFnUndecided.fnFun_at_values_step
#check @KCore.TieKkCeilLemmaFnUndecided.text_nextless
#check @KCore.TieKkCeilLemmaFnUndecided.fn_shape
#check @KCore.TieKkCeilLemmaFnUndecided.fns_account
#check @KCore.TieKkCeilLemmaFnUndecided.fns_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.fns_from_text
#check @KCore.TieKkCeilLemmaFnUndecided.fn_prios
#check @KCore.TieKkCeilLemmaFnUndecided.nojunk_trivial_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.nojunk_items_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.nojunk_kitem_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.cons_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.idem_refuted
#check @KCore.TieKkCeilLemmaFnUndecided.lib166
#check @KCore.TieKkCeilLemmaFnUndecided.lib166_at_values
#check @KCore.TieKkCeilLemmaFnUndecided.gamma_origin
#check @KCore.TieKkCeilLemmaFnUndecided.gamma_from
#check @KCore.TieKkCeilLemmaFnUndecided.paramlemma_account
#check @KCore.TieKkCeilLemmaFnUndecided.paramlemma_heads
#check @KCore.TieKkCeilLemmaFnUndecided.paramlemma_reads_h
#check @KCore.TieKkCeilLemmaFnUndecided.ParamLemmaWitnessAtValues
#check @KCore.TieKkCeilLemmaFnUndecided.kkclfu_witness
#check @KCore.TieKkCeilLemmaFnUndecided.kkclfu_not_entailed
#check @KCore.TieKkCeilLemmaFnUndecided.kkclfu_reads_rest
#print axioms KCore.TieKkCeilLemmaFnUndecided.noRaw
#print axioms KCore.TieKkCeilLemmaFnUndecided.readsConfined_c
#print axioms KCore.TieKkCeilLemmaFnUndecided.userAxioms_eq
#print axioms KCore.TieKkCeilLemmaFnUndecided.coreOK
#print axioms KCore.TieKkCeilLemmaFnUndecided.wf_defn
#print axioms KCore.TieKkCeilLemmaFnUndecided.account
#print axioms KCore.TieKkCeilLemmaFnUndecided.account_sizes
#print axioms KCore.TieKkCeilLemmaFnUndecided.account_classes
#print axioms KCore.TieKkCeilLemmaFnUndecided.account_absent
#print axioms KCore.TieKkCeilLemmaFnUndecided.absent_closed
#print axioms KCore.TieKkCeilLemmaFnUndecided.absent_proj_below_c
#print axioms KCore.TieKkCeilLemmaFnUndecided.absent_proj_below
#print axioms KCore.TieKkCeilLemmaFnUndecided.lists_in_account
#print axioms KCore.TieKkCeilLemmaFnUndecided.attrs_agree
#print axioms KCore.TieKkCeilLemmaFnUndecided.sig_origin_but_next
#print axioms KCore.TieKkCeilLemmaFnUndecided.decls_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.consistent
#print axioms KCore.TieKkCeilLemmaFnUndecided.fnFun_indices
#print axioms KCore.TieKkCeilLemmaFnUndecided.fnFun_account
#print axioms KCore.TieKkCeilLemmaFnUndecided.fnFun_checked
#print axioms KCore.TieKkCeilLemmaFnUndecided.fnFun_trS
#print axioms KCore.TieKkCeilLemmaFnUndecided.fnFun_at_values
#print axioms KCore.TieKkCeilLemmaFnUndecided.fnFun_at_values_step
#print axioms KCore.TieKkCeilLemmaFnUndecided.text_nextless
#print axioms KCore.TieKkCeilLemmaFnUndecided.fn_shape
#print axioms KCore.TieKkCeilLemmaFnUndecided.fns_account
#print axioms KCore.TieKkCeilLemmaFnUndecided.fns_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.fns_from_text
#print axioms KCore.TieKkCeilLemmaFnUndecided.fn_prios
#print axioms KCore.TieKkCeilLemmaFnUndecided.nojunk_trivial_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.nojunk_items_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.nojunk_kitem_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.cons_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.idem_refuted
#print axioms KCore.TieKkCeilLemmaFnUndecided.lib166
#print axioms KCore.TieKkCeilLemmaFnUndecided.lib166_at_values
#print axioms KCore.TieKkCeilLemmaFnUndecided.gamma_origin
#print axioms KCore.TieKkCeilLemmaFnUndecided.gamma_from
#print axioms KCore.TieKkCeilLemmaFnUndecided.paramlemma_account
#print axioms KCore.TieKkCeilLemmaFnUndecided.paramlemma_heads
#print axioms KCore.TieKkCeilLemmaFnUndecided.paramlemma_reads_h
#print axioms KCore.TieKkCeilLemmaFnUndecided.ParamLemmaWitnessAtValues
#print axioms KCore.TieKkCeilLemmaFnUndecided.kkclfu_witness
#print axioms KCore.TieKkCeilLemmaFnUndecided.kkclfu_not_entailed
#print axioms KCore.TieKkCeilLemmaFnUndecided.kkclfu_reads_rest
