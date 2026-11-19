/-
  The tie (C14) on `f2-examples/e6-param-int.kompile.kore`, the kompiled text of construct fixture e6-param-int
  (`test/constructs/fixtures/e6-param-int`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e6-param-int`, except the section `WitnessE6pi` (the witness of the
  parameter lemma 156), written by hand; run from the package root: `lake env lean -j1 test/TieE6ParamInt.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 258 sentences of the user module E6-PARAM-INT, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 211 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (27, and two sentences of the text's prelude modules, 1 (KSEQ), 2 (KSEQ),
    which no user sentence is): each of Γ's items is the translation of one sentence, in the order
    `fnText` lists them (`fn_shape`); its user-module sentences are the class, the others those
    prelude sentences (`fns_account`, and `preludeKseq_eq`: they are the text's); `fns_entailed`
    (E), `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Rewrite rules (6): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (26): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 165 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); parameter functional:
    owed as `ParamsTotal` (`total_params`, `paramfunctional_account`, `paramfunctional_heads`);
    parameter lemma: owed as a hypothesis on H, at values (`paramlemma_account`, `paramlemma_heads`,
    `ParamLemmaWitnessAtValues`, `e6pi_witness`); no direction: `absent_closed`.

  The parameter functional sentences (35, 72, 74, 109) are the `functional` sentence of a parameter
  symbol no registry hook interprets that the text declares total (`Definition.totalParams`,
  `total_params`), which the reader reads as that declaration. Γ states the parameter's graph at
  values from the interpretation (`ΓDomains`: its application to values denotes `paramVal`'s value,
  or nothing), so the sentence holds at values where H gives the parameter a value of its sort at
  every argument list of its sorts: the hypothesis on H the statements take (`ParamsTotal`). The
  account holds them in the class `parameter functional`, of the direction `hypothesis`
  (`paramfunctional_account`), and every such sentence of the user module is in it
  (`paramfunctional_heads`).

  The parameter lemmas (156) apply a parameter symbol no registry hook interprets, whose value the
  interpretation gives: each is owed as a hypothesis on H, at the valuations sending its variables
  to values (`EntailsAtValues (cH H) ad (trS ad).pat`), since Γ states the parameter's graph at
  values only (`ΓDomains`). The account holds them in the class `parameter lemma`, of the direction
  `hypothesis`. A hypothesis no H satisfies would tie a text without a model, so the tie owes one H
  at which the functions' obligations hold and every parameter lemma holds at values
  (`ParamLemmaWitnessAtValues`, proved by hand: `e6pi_witness`, at `HAndE6pi`, which gives `&Int`
  bitwise and at Int values). Every `simplification`
  equation of the user module whose left side's head is a parameter symbol without `impl` is one of
  them (`paramlemma_heads`).

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (15);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamInt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-int.kompile.kore"
definition_of defn from "f2-examples/e6-param-int.kompile.kore"
user_axioms U from "f2-examples/e6-param-int.kompile.kore" module "E6-PARAM-INT"
user_axioms PreludeKseq from "f2-examples/e6-param-int.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E6-PARAM-INT")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 258 := by decide +kernel

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
  [("function equation", [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
      231, 232, 233, 234, 235, 236, 237, 238, 239]),
   ("rewrite rule", [149, 150, 151, 152, 153, 154]),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 78, 100, 101]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28, 79]),
   ("distinctness", []),
   ("no junk", [110, 111, 112, 113, 114, 115, 116, 117, 118, 119]),
   ("function functional", [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      55, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 81, 97, 98, 99, 102, 103, 104, 105,
      106, 107]),
   ("collection law", [52, 53, 54, 56, 57, 58, 59, 61, 62]),
   ("library", [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142,
      143, 144, 145, 146, 147, 148, 155, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167,
      168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185,
      186, 187, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
      205, 206, 207, 208, 242, 243, 244, 245, 259, 260]),
   ("set idempotence", [60]),
   ("set-variable lemma", [120, 121, 122, 123, 124, 261]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", [35, 72, 74, 109]),
   ("parameter lemma", [156]),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [39, 41, 80, 96, 108, 188, 209, 210, 211, 212, 240, 241, 246, 247, 248, 249, 250, 251, 252,
      253, 254, 255, 256, 257, 258])]

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
    [("function equation", 27), ("rewrite rule", 6), ("priority equation", 0), ("constructor functional", 7), ("subsort", 14), ("injectivity", 5), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 4), ("parameter lemma", 1), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 25)] := by
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
  [(246, "Bool"), (247, "GeneratedCounterCell"), (248, "GeneratedCounterCellOpt"),
   (249, "GeneratedTopCell"), (250, "GeneratedTopCellFragment"), (251, "Int"), (252, "K"),
   (253, "KCell"), (254, "KCellOpt"), (255, "KItem"), (256, "List"), (257, "Map"), (258, "Set")]

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
  [(35, "parameter functional"), (72, "parameter functional"), (74, "parameter functional"),
   (78, "constructor functional"), (79, "injectivity"), (109, "parameter functional"),
   (119, "no junk"), (149, "rewrite rule"), (150, "rewrite rule"), (151, "rewrite rule"),
   (152, "rewrite rule"), (153, "rewrite rule"), (154, "rewrite rule"), (156, "parameter lemma"),
   (212, "no direction")]

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

theorem sig_sizes : (sigItems c).length = 211 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 127, 97, 5, 25) := by
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
def fnFunIdx : List Nat := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

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

/-! ## Function equations (27 sentences, and two of the prelude) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [PreludeKseq.ax1, PreludeKseq.ax2, U.ax225, U.ax233, U.ax232, U.ax231, U.ax230, U.ax237, U.ax236,
   U.ax239, U.ax238, U.ax235, U.ax234, U.ax214, U.ax213, U.ax224, U.ax223, U.ax220, U.ax219,
   U.ax222, U.ax221, U.ax227, U.ax226, U.ax229, U.ax228, U.ax216, U.ax215, U.ax218, U.ax217]

set_option maxHeartbeats 1000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel
decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- The axioms of the prelude module KSEQ, in text order. -/
theorem preludeKseq_eq : kore.axiomDecls.filter (·.module == "KSEQ") = PreludeKseq.all := by kernel_rfl

/-- **`fnText`'s user-module sentences are the account's function-equation class**: the same
indices, each once; its other sentences are the prelude's, which no user sentence is. -/
theorem fns_account :
    (classOf "function equation").isPerm ((fnText.filter (·.module == "E6-PARAM-INT")).map (·.index)) = true ∧
    (fnText.filter (·.module != "E6-PARAM-INT")).map (fun ad => (ad.index, ad.module)) =
      [(1, "KSEQ"), (2, "KSEQ")] := by decide +kernel

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

/-! ## The rules (6 sentences): W1 -/

/-- A rule axiom `\rewrites{C}(\and{C}(l, t, x), r)`, read as its parts. -/
def ruleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none

/-- The rule axiom without its left side's third conjunct. -/
def dropThird (p : Kore.Pattern) : Kore.Pattern :=
  match ruleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p

theorem ruleParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t x r : Kore.Pattern}
    (h : ruleParts p = some (C, l, t, x, r)) : ∃ C', p = .rewrites C (.and C' [l, t, x]) r ∧ dropThird p = .rewrites C (.and C [l, t]) r := by
  unfold dropThird; rw [h]
  unfold ruleParts at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- **A conjunct more on a rule's left side gives a consequence**: in a model of definedness, the
rule axiom with the left side `l ∧ t` entails the one with the left side `l ∧ t ∧ x`, where the
two have one variable table and one list of free variables. -/
theorem rewrite_weaken {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {p : Kore.Pattern}
    {C : Kore.KSort} {l t x r : Kore.Pattern} (hq : ruleParts p = some (C, l, t, x, r))
    (ht : tableOf [] p = tableOf [] (dropThird p))
    (hf : (freeOf [] p).eraseDups = (freeOf [] (dropThird p)).eraseDups)
    (h : I ⊧ᴵ (trAxiom [] [] (kAx (dropThird p))).pat) : I ⊧ᴵ (trAxiom [] [] (kAx p)).pat := by
  obtain ⟨C', hp, hd⟩ := ruleParts_eq hq
  intro e m
  have h1 := h e m
  simp only [trAxiom, kAx, List.map_nil, List.nil_append] at h1 ⊢
  rw [ht, hf]
  rw [hd] at h1 ⊢
  rw [hp] at ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  simp only [sortOf, tr, trAndList, sRewrites, interp_sImp, interp_sAnd] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 ⟨hl.1, hl.2.1⟩⟩⟩


noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
noncomputable def r2 : Rule := c.rules[2]'(by decide +kernel)
noncomputable def r3 : Rule := c.rules[3]'(by decide +kernel)
noncomputable def r4 : Rule := c.rules[4]'(by decide +kernel)
noncomputable def r5 : Rule := c.rules[5]'(by decide +kernel)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0)),
    trAxiom [] [] (kAx (prioRuleK c r1)),
    trAxiom [] [] (kAx (prioRuleK c r2)),
    trAxiom [] [] (kAx (prioRuleK c r3)),
    trAxiom [] [] (kAx (prioRuleK c r4)),
    trAxiom [] [] (kAx (prioRuleK c r5))] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax149, U.ax150, U.ax151, U.ax152, U.ax153, U.ax154]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

theorem rule0_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule0_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule0_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 0 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 149. -/
theorem rule0_text : (trS U.ax149).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel
/-- **W1 for rule 0**: Γ's item is a consequence of sentence 149. -/
theorem rule0_from_text : itemsPremises [trS U.ax149] ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule0_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule0_table rule0_free ?_
  rw [← rule0_text]
  exact hI _ (Or.inl ⟨trS U.ax149, List.mem_singleton_self _, rfl⟩)

theorem rule1_parts : (ruleParts (prioRuleK c r1)).isSome = true := by decide +kernel
theorem rule1_table : tableOf [] (prioRuleK c r1) = tableOf [] (dropThird (prioRuleK c r1)) := by decide +kernel
theorem rule1_free : (freeOf [] (prioRuleK c r1)).eraseDups = (freeOf [] (dropThird (prioRuleK c r1))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 1 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 150. -/
theorem rule1_text : (trS U.ax150).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r1)))).pat := by decide +kernel
/-- **W1 for rule 1**: Γ's item is a consequence of sentence 150. -/
theorem rule1_from_text : itemsPremises [trS U.ax150] ⊧ (trAxiom [] [] (kAx (prioRuleK c r1))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule1_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule1_table rule1_free ?_
  rw [← rule1_text]
  exact hI _ (Or.inl ⟨trS U.ax150, List.mem_singleton_self _, rfl⟩)

theorem rule2_parts : (ruleParts (prioRuleK c r2)).isSome = true := by decide +kernel
theorem rule2_table : tableOf [] (prioRuleK c r2) = tableOf [] (dropThird (prioRuleK c r2)) := by decide +kernel
theorem rule2_free : (freeOf [] (prioRuleK c r2)).eraseDups = (freeOf [] (dropThird (prioRuleK c r2))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 2 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 151. -/
theorem rule2_text : (trS U.ax151).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r2)))).pat := by decide +kernel
/-- **W1 for rule 2**: Γ's item is a consequence of sentence 151. -/
theorem rule2_from_text : itemsPremises [trS U.ax151] ⊧ (trAxiom [] [] (kAx (prioRuleK c r2))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule2_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule2_table rule2_free ?_
  rw [← rule2_text]
  exact hI _ (Or.inl ⟨trS U.ax151, List.mem_singleton_self _, rfl⟩)

theorem rule3_parts : (ruleParts (prioRuleK c r3)).isSome = true := by decide +kernel
theorem rule3_table : tableOf [] (prioRuleK c r3) = tableOf [] (dropThird (prioRuleK c r3)) := by decide +kernel
theorem rule3_free : (freeOf [] (prioRuleK c r3)).eraseDups = (freeOf [] (dropThird (prioRuleK c r3))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 3 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 152. -/
theorem rule3_text : (trS U.ax152).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r3)))).pat := by decide +kernel
/-- **W1 for rule 3**: Γ's item is a consequence of sentence 152. -/
theorem rule3_from_text : itemsPremises [trS U.ax152] ⊧ (trAxiom [] [] (kAx (prioRuleK c r3))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule3_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule3_table rule3_free ?_
  rw [← rule3_text]
  exact hI _ (Or.inl ⟨trS U.ax152, List.mem_singleton_self _, rfl⟩)

theorem rule4_parts : (ruleParts (prioRuleK c r4)).isSome = true := by decide +kernel
theorem rule4_table : tableOf [] (prioRuleK c r4) = tableOf [] (dropThird (prioRuleK c r4)) := by decide +kernel
theorem rule4_free : (freeOf [] (prioRuleK c r4)).eraseDups = (freeOf [] (dropThird (prioRuleK c r4))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 4 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 153. -/
theorem rule4_text : (trS U.ax153).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r4)))).pat := by decide +kernel
/-- **W1 for rule 4**: Γ's item is a consequence of sentence 153. -/
theorem rule4_from_text : itemsPremises [trS U.ax153] ⊧ (trAxiom [] [] (kAx (prioRuleK c r4))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule4_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule4_table rule4_free ?_
  rw [← rule4_text]
  exact hI _ (Or.inl ⟨trS U.ax153, List.mem_singleton_self _, rfl⟩)

theorem rule5_parts : (ruleParts (prioRuleK c r5)).isSome = true := by decide +kernel
theorem rule5_table : tableOf [] (prioRuleK c r5) = tableOf [] (dropThird (prioRuleK c r5)) := by decide +kernel
theorem rule5_free : (freeOf [] (prioRuleK c r5)).eraseDups = (freeOf [] (dropThird (prioRuleK c r5))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 5 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 154. -/
theorem rule5_text : (trS U.ax154).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r5)))).pat := by decide +kernel
/-- **W1 for rule 5**: Γ's item is a consequence of sentence 154. -/
theorem rule5_from_text : itemsPremises [trS U.ax154] ⊧ (trAxiom [] [] (kAx (prioRuleK c r5))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule5_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule5_table rule5_free ?_
  rw [← rule5_text]
  exact hI _ (Or.inl ⟨trS U.ax154, List.mem_singleton_self _, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨U.ax149, List.mem_cons_self, rule0_from_text⟩
  · exact ⟨U.ax150, List.mem_cons_of_mem _ (List.mem_cons_self), rule1_from_text⟩
  · exact ⟨U.ax151, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)), rule2_from_text⟩
  · exact ⟨U.ax152, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))), rule3_from_text⟩
  · exact ⟨U.ax153, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))), rule4_from_text⟩
  · exact ⟨U.ax154, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))), rule5_from_text⟩

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

theorem nj110 : (trS U.ax110).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj115 : (trS U.ax115).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj118 : (trS U.ax118).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax110, U.ax115, U.ax118], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj110]; exact orTopBot_valid hD rfl
  · rw [nj115]; exact orTopBot_valid hD rfl
  · rw [nj118]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax111, U.ax112, U.ax113, U.ax114, U.ax116, U.ax117],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax111, U.ax112, U.ax113, U.ax114, U.ax116, U.ax117],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax119).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (119)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax119).pat := by
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax78, U.ax79,
   U.ax100, U.ax101]

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


/-! ## Library sample: sentence 165, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax165).pat = (trAxiom [] [] U.ax165).pat := by decide +kernel
theorem s166_pattern : U.ax165.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax165.ax.sortVars.map sortVarKey ++ freeOf [] U.ax165.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax165.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 165 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax165.ax.sortVars U.ax165.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax165).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax165.ax.sortVars U.ax165.ax.pattern = t at he ⊢
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
/-- **Sentence 165 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax165 (trS U.ax165).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The parameter functional sentences (35, 72, 74, 109): owed as `ParamsTotal` -/

/-- The parameter symbols no registry hook interprets that the text declares total
(`Definition.totalParams`): the statements take `ParamsTotal c defn.totalParams H`, that `H` gives
each a value of its result sort at every argument list of its argument sorts. -/
theorem total_params : defn.totalParams.map c.symName = ["Lbl'Tild'Int'Unds'", "Lbl'UndsAnd-'Int'Unds'", "Lbl'Unds'xorInt'Unds'", "Lbl'UndsPipe'Int'Unds'"] := by decide +kernel

/-- The text's `functional` sentences of those parameters (`isParamFunctional`). -/
noncomputable def paramFunctionalText : List AxiomDecl := [U.ax35, U.ax72, U.ax74, U.ax109]

/-- The parameter functional sentences are the account's class `parameter functional`, of the
direction `hypothesis`: Γ states a parameter's graph at values from the interpretation (`ΓDomains`),
so it holds the sentence at values exactly where `H` gives the parameter a value at the values of its
argument sorts, which is `ParamsTotal` at that parameter. -/
theorem paramfunctional_account : paramFunctionalText.map (·.index) = classOf "parameter functional" ∧
    paramFunctionalText.all (fun ad => functionalOfNamed ["Lbl'Tild'Int'Unds'", "Lbl'UndsAnd-'Int'Unds'", "Lbl'Unds'xorInt'Unds'", "Lbl'UndsPipe'Int'Unds'"] ad.ax) = true := by
  decide +kernel

/-- Every `functional` sentence of the user module of a parameter the text declares total
(`total_params`) is of the class `parameter functional`. -/
theorem paramfunctional_heads : userAxioms.all (fun ad => !functionalOfNamed ["Lbl'Tild'Int'Unds'", "Lbl'UndsAnd-'Int'Unds'", "Lbl'Unds'xorInt'Unds'", "Lbl'UndsPipe'Int'Unds'"] ad.ax || (classOf "parameter functional").contains ad.index) = true := by
  rw [userAxioms_eq]; decide +kernel

/-! ## The parameter lemmas (156): owed as a hypothesis on H -/

/-- The text's lemmas that apply a parameter symbol no registry hook interprets (`isParamLemma`, or a
`simplification` sentence of K's builtin library applying one). -/
noncomputable def paramLemmaText : List AxiomDecl := [U.ax156]

/-- The parameter lemmas are the account's class `parameter lemma`, of the direction `hypothesis`
(Γ does not hold the sentence; at the member `cH H` it is owed at values). -/
theorem paramlemma_account : paramLemmaText.map (·.index) = classOf "parameter lemma" := by
  decide +kernel

/-- **What the tie owes of the parameter lemmas**: one interpretation `H` at which the functions'
obligations hold and every parameter lemma holds in every model of Γ at the valuations sending its
free element variables to values (`EntailsAtValues`), so that the text with its hypotheses has a
model. Γ states a parameter's graph at values only (`ΓDomains`), so the lemma is owed there. Proved
by hand: `e6pi_witness`. -/
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

/-! ## The converse over Γ's content -/

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, Γ's rule items (each a consequence of its
text sentence, `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; a rule item is a consequence of a text sentence of `ruleText`; everything else is one of
the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ φ) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))

/-! ## The witness of the parameter lemma 156, by hand

156 is INT-KORE's lemma `I1 &Int (I2 &Int C) = (I1 &Int I2) &Int C` (domains.md 1428). `&Int`
(symbol 213) is a parameter of the reading without `impl`, applied by a rule, so Γ states its graph
at values from the interpretation (`ΓDomains`, `Semantics.paramVal`). At `HAndE6pi`, which gives
`&Int` bitwise and at Int values (`landE6pi`), every model of Γ applies `&Int` to values as bitwise
and, which is associative, so 156 holds there at values; the functions' obligations hold at every
H (`obl_nil`). -/

section WitnessE6pi

open LibEv

/-- `&Int`'s declaration: a parameter of `Int Int → Int` no hook implements. -/
def kAndE6pi : ParamSig := ⟨⟨213, [Srt.int, Srt.int], Srt.int⟩, none, false, false, false⟩

/-- `&Int`'s signature. -/
def andSigE6pi : CtorSig := ⟨213, [Srt.int, Srt.int], Srt.int⟩

theorem andFactsE6pi : c.lookupParam 213 = some kAndE6pi ∧ c.symName 213 = "Lbl'UndsAnd-'Int'Unds'" ∧
    isHook 213 = false := by
  decide +kernel

theorem lookupAndE6pi (H : HookParams) : (cH H).lookupParam 213 = some kAndE6pi := andFactsE6pi.1

theorem sortOfHE6pi (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H noRaw

theorem shapesOKHE6pi (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- `m` with the bits of `n` cleared. -/
def ldiffE6pi (m n : Nat) : Nat := Nat.bitwise (fun a b => a && !b) m n

/-- Bitwise and on Int in two's complement, where `-[n+1]` is the complement of `n`. -/
def landE6pi : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (ldiffE6pi m n)
  | .negSucc m, .ofNat n => .ofNat (ldiffE6pi n m)
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

/-- The bit `i` of an Int in two's complement. -/
def bitE6pi : Int → Nat → Bool
  | .ofNat m, i => m.testBit i
  | .negSucc m, i => !m.testBit i

theorem testBit_ldiffE6pi (m n i : Nat) : (ldiffE6pi m n).testBit i = (m.testBit i && !n.testBit i) :=
  Nat.testBit_bitwise rfl m n i

/-- Each bit of `landE6pi x y` is the and of `x`'s and `y`'s. -/
theorem bitE6pi_land (x y : Int) (i : Nat) : bitE6pi (landE6pi x y) i = (bitE6pi x i && bitE6pi y i) := by
  cases x <;> cases y <;> simp [landE6pi, bitE6pi, testBit_ldiffE6pi, Bool.and_comm]

/-- An Int is its bits: a natural number and a negative one differ at a bit above both. -/
theorem bitE6pi_ext {x y : Int} (h : ∀ i, bitE6pi x i = bitE6pi y i) : x = y := by
  have hhi : ∀ m n : Nat, m.testBit (m + n) = false ∧ n.testBit (m + n) = false := fun m n =>
    ⟨Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_right m n))),
     Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left n m)))⟩
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact congrArg _ (Nat.eq_of_testBit_eq h)
    | negSucc n =>
      have := h (m + n)
      simp only [bitE6pi, (hhi m n).1, (hhi m n).2] at this
      cases this
  | negSucc m =>
    cases y with
    | ofNat n =>
      have := h (m + n)
      simp only [bitE6pi, (hhi m n).1, (hhi m n).2] at this
      cases this
    | negSucc n =>
      exact congrArg _ (Nat.eq_of_testBit_eq fun i => by simpa [bitE6pi] using h i)

/-- **Bitwise and is associative.** -/
theorem landE6pi_assoc (x y z : Int) : landE6pi (landE6pi x y) z = landE6pi x (landE6pi y z) :=
  bitE6pi_ext fun i => by simp only [bitE6pi_land, Bool.and_assoc]

/-- `landE6pi` at a few values: 12 & 10 = 8, -1 & 10 = 10, -4 & -3 = -4, -6 & 7 = 2. -/
theorem landE6pi_values : landE6pi 12 10 = 8 ∧ landE6pi (-1) 10 = 10 ∧ landE6pi (-4) (-3) = -4 ∧
    landE6pi (-6) 7 = 2 := by
  decide +kernel

/-- The interpretation giving `&Int` bitwise and at Int values, and nothing elsewhere. -/
def HAndE6pi : HookParams := ⟨fun f ws => if f = 213 then
  (match ws with
    | [a, b] => (asInt a).bind fun x => (asInt b).map fun y => int (landE6pi x y)
    | _ => none) else none⟩

theorem paramValAndE6pi (x y : Int) :
    (cH HAndE6pi).paramVal 213 [int x, int y] = some (int (landE6pi x y)) := by
  unfold Semantics.paramVal
  rw [lookupAndE6pi]
  simp only [kAndE6pi, HAndE6pi, Semantics.withHooks]
  rfl

/-- **In every model of Γ, `&Int` at values denotes its value under the interpretation**: Γ's graph
of the parameter (`ΓDomains`), read as `LackedDen` at Γ's own value `paramVal`. -/
theorem andDenE6pi (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : LackedDen (cH H) [andSigE6pi] (fun f ws => (cH H).paramVal f ws) I := by
  intro k hk ws hws
  simp only [List.mem_singleton] at hk
  subst hk
  have hmem : kAndE6pi ∈ (cH H).params := (lookupParam_some_paramP (lookupAndE6pi H)).1
  refine ⟨fun e m => ?_, fun v hv => ?_⟩
  · have hax := sat_dom hI (Or.inr (Or.inl ⟨kAndE6pi, ws, hmem, hws, rfl⟩))
    have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
    rw [show (cH H).paramVal kAndE6pi.sig.name ws = (cH H).paramVal 213 ws from rfl] at hgr
    refine hgr.trans ?_
    show _ ↔ Res (cH H) I e ((cH H).paramVal 213 ws) m
    cases (cH H).paramVal 213 ws with
    | none => simp [Res, Pattern.interpret]
    | some v => rfl
  · obtain ⟨k', hk', hs'⟩ := (cH H).paramVal_sorted hv
    have hk2 : some kAndE6pi = some k' := (lookupAndE6pi H).symm.trans hk'
    cases hk2
    exact hs'

/-- 156 (domains.md 1428): `I1 &Int (I2 &Int C) = (I1 &Int I2) &Int C`. -/
def e156E6pi : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int), ("VarC", Srt.int)], Srt.int, none,
    .app 213 [.var 0, .app 213 [.var 1, .var 2]], .app 213 [.app 213 [.var 0, .var 1], .var 2]⟩

theorem e156E6pi_text : U.ax156.ax.pattern = e156E6pi.patR ∧ U.ax156.ax.sortVars = [KoreAML.Rv] ∧
    e156E6pi.regular = true ∧ e156E6pi.typedLk c.sortOf [andSigE6pi] = true ∧
    (trS U.ax156).pat = (trAxiom [] [] U.ax156).pat := by
  decide +kernel

/-- **156 holds under bitwise and**: its two sides are bitwise and's two bracketings. -/
theorem holds156E6pi : e156E6pi.HoldsLk (cH HAndE6pi) (fun f ws => (cH HAndE6pi).paramVal f ws) := by
  intro σ hσ _
  obtain ⟨v0, h0, s0⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, s1⟩ := hσ 1 _ rfl
  obtain ⟨v2, h2, s2⟩ := hσ 2 _ rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKHE6pi HAndE6pi) s0
  obtain ⟨y, rfl⟩ := shape_int (shapesOKHE6pi HAndE6pi) s1
  obtain ⟨z, rfl⟩ := shape_int (shapesOKHE6pi HAndE6pi) s2
  have hh : isHook 213 = false := andFactsE6pi.2.2
  simp only [e156E6pi, valLk, valListLk, allSome, h0, h1, h2, hh, Bool.false_eq_true, ↓reduceIte,
    Option.bind_some, Option.map_some, paramValAndE6pi, landE6pi_assoc]

/-- **156 holds at values at `HAndE6pi`**, in every model of Γ. -/
theorem s156_at_valuesE6pi : EntailsAtValues (cH HAndE6pi) U.ax156 (trS U.ax156).pat := by
  intro M _ I hI e hat m
  obtain ⟨hp, hsv, hr, ht, htr⟩ := e156E6pi_text
  rw [htr]
  exact Eqn.entailedLk_reg (coreOKH HAndE6pi) hI (andDenE6pi HAndE6pi hI) e156E6pi hr
    (by rw [sortOfHE6pi]; exact ht) holds156E6pi U.ax156 hp hsv e hat m

/-- **The witness**: at `HAndE6pi` (`&Int` is bitwise and at values) the functions' obligations hold
(`obl_nil`) and the parameter lemma 156 holds at values. -/
theorem e6pi_witness : ParamLemmaWitnessAtValues := by
  refine ⟨HAndE6pi, obl_nil HAndE6pi, fun ad had => ?_⟩
  simp only [paramLemmaText, List.mem_cons, List.not_mem_nil, or_false] at had
  subst had
  exact s156_at_valuesE6pi

end WitnessE6pi

end KCore.TieE6ParamInt

#check @KCore.TieE6ParamInt.noRaw
#check @KCore.TieE6ParamInt.readsConfined_c
#check @KCore.TieE6ParamInt.userAxioms_eq
#check @KCore.TieE6ParamInt.coreOK
#check @KCore.TieE6ParamInt.wf_defn
#check @KCore.TieE6ParamInt.account
#check @KCore.TieE6ParamInt.account_sizes
#check @KCore.TieE6ParamInt.account_classes
#check @KCore.TieE6ParamInt.account_absent
#check @KCore.TieE6ParamInt.absent_closed
#check @KCore.TieE6ParamInt.absent_proj_below_c
#check @KCore.TieE6ParamInt.absent_proj_below
#check @KCore.TieE6ParamInt.lists_in_account
#check @KCore.TieE6ParamInt.attrs_agree
#check @KCore.TieE6ParamInt.sig_origin
#check @KCore.TieE6ParamInt.decls_entailed
#check @KCore.TieE6ParamInt.consistent
#check @KCore.TieE6ParamInt.fnFun_indices
#check @KCore.TieE6ParamInt.fnFun_account
#check @KCore.TieE6ParamInt.fnFun_checked
#check @KCore.TieE6ParamInt.fnFun_trS
#check @KCore.TieE6ParamInt.fnFun_at_values
#check @KCore.TieE6ParamInt.fnFun_at_values_step
#check @KCore.TieE6ParamInt.preludeKseq_eq
#check @KCore.TieE6ParamInt.fn_shape
#check @KCore.TieE6ParamInt.fns_account
#check @KCore.TieE6ParamInt.fns_entailed
#check @KCore.TieE6ParamInt.fns_from_text
#check @KCore.TieE6ParamInt.fn_prios
#check @KCore.TieE6ParamInt.nojunk_trivial_entailed
#check @KCore.TieE6ParamInt.nojunk_items_entailed
#check @KCore.TieE6ParamInt.nojunk_kitem_entailed
#check @KCore.TieE6ParamInt.cons_entailed
#check @KCore.TieE6ParamInt.rules_account
#check @KCore.TieE6ParamInt.rule_from_text
#check @KCore.TieE6ParamInt.idem_refuted
#check @KCore.TieE6ParamInt.lib166
#check @KCore.TieE6ParamInt.lib166_at_values
#check @KCore.TieE6ParamInt.gamma_origin
#check @KCore.TieE6ParamInt.gamma_from
#check @KCore.TieE6ParamInt.total_params
#check @KCore.TieE6ParamInt.paramfunctional_account
#check @KCore.TieE6ParamInt.paramfunctional_heads
#check @KCore.TieE6ParamInt.paramlemma_account
#check @KCore.TieE6ParamInt.paramlemma_heads
#check @KCore.TieE6ParamInt.ParamLemmaWitnessAtValues
#check @KCore.TieE6ParamInt.e6pi_witness
#print axioms KCore.TieE6ParamInt.noRaw
#print axioms KCore.TieE6ParamInt.readsConfined_c
#print axioms KCore.TieE6ParamInt.userAxioms_eq
#print axioms KCore.TieE6ParamInt.coreOK
#print axioms KCore.TieE6ParamInt.wf_defn
#print axioms KCore.TieE6ParamInt.account
#print axioms KCore.TieE6ParamInt.account_sizes
#print axioms KCore.TieE6ParamInt.account_classes
#print axioms KCore.TieE6ParamInt.account_absent
#print axioms KCore.TieE6ParamInt.absent_closed
#print axioms KCore.TieE6ParamInt.absent_proj_below_c
#print axioms KCore.TieE6ParamInt.absent_proj_below
#print axioms KCore.TieE6ParamInt.lists_in_account
#print axioms KCore.TieE6ParamInt.attrs_agree
#print axioms KCore.TieE6ParamInt.sig_origin
#print axioms KCore.TieE6ParamInt.decls_entailed
#print axioms KCore.TieE6ParamInt.consistent
#print axioms KCore.TieE6ParamInt.fnFun_indices
#print axioms KCore.TieE6ParamInt.fnFun_account
#print axioms KCore.TieE6ParamInt.fnFun_checked
#print axioms KCore.TieE6ParamInt.fnFun_trS
#print axioms KCore.TieE6ParamInt.fnFun_at_values
#print axioms KCore.TieE6ParamInt.fnFun_at_values_step
#print axioms KCore.TieE6ParamInt.preludeKseq_eq
#print axioms KCore.TieE6ParamInt.fn_shape
#print axioms KCore.TieE6ParamInt.fns_account
#print axioms KCore.TieE6ParamInt.fns_entailed
#print axioms KCore.TieE6ParamInt.fns_from_text
#print axioms KCore.TieE6ParamInt.fn_prios
#print axioms KCore.TieE6ParamInt.nojunk_trivial_entailed
#print axioms KCore.TieE6ParamInt.nojunk_items_entailed
#print axioms KCore.TieE6ParamInt.nojunk_kitem_entailed
#print axioms KCore.TieE6ParamInt.cons_entailed
#print axioms KCore.TieE6ParamInt.rules_account
#print axioms KCore.TieE6ParamInt.rule_from_text
#print axioms KCore.TieE6ParamInt.idem_refuted
#print axioms KCore.TieE6ParamInt.lib166
#print axioms KCore.TieE6ParamInt.lib166_at_values
#print axioms KCore.TieE6ParamInt.gamma_origin
#print axioms KCore.TieE6ParamInt.gamma_from
#print axioms KCore.TieE6ParamInt.total_params
#print axioms KCore.TieE6ParamInt.paramfunctional_account
#print axioms KCore.TieE6ParamInt.paramfunctional_heads
#print axioms KCore.TieE6ParamInt.paramlemma_account
#print axioms KCore.TieE6ParamInt.paramlemma_heads
#print axioms KCore.TieE6ParamInt.ParamLemmaWitnessAtValues
#print axioms KCore.TieE6ParamInt.e6pi_witness
