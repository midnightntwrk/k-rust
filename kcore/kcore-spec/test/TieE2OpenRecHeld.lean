/-
  The tie (C14) on `f2-examples/e2-open-rec-held.kompile.kore`, the kompiled text of construct fixture e2-open-rec-held
  (`test/constructs/fixtures/e2-open-rec-held`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e2-open-rec-held`; run from the package root: `lake env lean -j1 test/TieE2OpenRecHeld.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 146 sentences of the user module E2-OPEN-REC-HELD, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the open
    generator `and` is a parameter declared without `hook` and without `function`, of which the
    text states no equation.
  - `sig_origin`: each of the 209 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`); its one open generator is `and`
    (`params_raw`), of B. It owes no fact
    about its functions (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the
    step's closure has a model for every H that satisfies the open generator's laws (`facts`,
    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`); `and`
    has no law, so that is every H (`openLaws_any`, `consistent_any`).
    `lawHooks c H` is admitted by the library's sentences wherever H is (`libAdmitted_lawHooks`), so
    `lawHooks c HookParams.lib` satisfies the laws, the open generators' `functional` sentences and
    the library's sentences together (`lawHooks_lib`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (31): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (47): Γ with it has no model (`idem_refuted`).
  - Rewrite rule (1): Γ's rule is the text's read through the cut (`Parse.ovlCut`), the variable
    `Open0` in the place of `and(X, Y)` with `pre := Open0 ∈ and(X, Y)`. Γ's item is a
    consequence of sentence 99 (`rule_from_text`, W1, every H), and in a model of Γ the sentence
    and the item hold together (`rule_tie`, `rule_to_text`, W2, every H;
    `KCore.TieRuleCut.openCut_tie`): the conjunct `⌈r⌉` of every rule's item holds of every
    element of the text's left side (`RightDefined`, `right_defined`), the right side being built
    of X, the counter cell's variable and the constructors `d`, `kseq`, `dotk`, `<k>` and
    `<generatedTop>`, whose Cons-Fun items Γ has (`KCore.TieRuleCut.rightDefined_of_Γ`). This
    section is written by hand.
  - The rule's steps, by hand: `<k> c(v, x, y) </k>` steps exactly where H gives `and(x, y)` the
    value v, to `<k> d(x) </k>` (`orhStep_iff`, every H). From the sentences, where H gives
    `and(e, e)` the value v, `<k> c(v, e, e) </k>` has the successor `<k> d(e) </k>`
    (`orhStep_ee`; premises `orhPre`, with a model, `orhPre_model`); where H gives it no value or
    another one, the configuration has no successor (`orhNoStep_ee`); the text does not determine
    whether `<k> c(e, e, e) </k>` steps to `<k> d(e) </k>` (`orhStep_undetermined`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); open generator
    functional: owed as `OpenTotal` (`open_functional_not_item`); no direction: `absent_closed`.

  B's no junk (88) is entailed (`nojunk_b_entailed`): its item lists B's generators, `and` among
  them, in another order than `Semantics.gens`. `and`'s functional sentence (55) is no item of Γ and
  is owed at values as `OpenTotal` (`open_functional_not_item`); the account holds it in `open
  generator functional`, of the direction `hypothesis`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (17);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2OpenRecHeld

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-open-rec-held.kompile.kore"
definition_of defn from "f2-examples/e2-open-rec-held.kompile.kore"
user_axioms U from "f2-examples/e2-open-rec-held.kompile.kore" module "E2-OPEN-REC-HELD"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `and`, the text's one open generator (`raw`), and B, its sort. -/
def and : Sym := 388
def b : Srt := 32

theorem names : c.symName and = "Lbland" ∧ c.sortName b = "B" := by decide +kernel

/-- **The definition's one open generator is `and`**, of B, `assoc` false and `idem` false. -/
theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =
    [(and, [b, b], b, false, false)] := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-OPEN-REC-HELD")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 146 := by decide +kernel

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
  [("function equation", [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
      123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]),
   ("rewrite rule", [99]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 56, 59, 61, 80, 81]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 57, 60]),
   ("distinctness", [58]),
   ("no junk", [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]),
   ("function functional", [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 38, 42, 50, 51, 52, 53, 54, 63, 79, 82, 83, 84, 85, 86]),
   ("collection law", [39, 40, 41, 43, 44, 45, 46, 48, 49]),
   ("library", [100, 148]),
   ("set idempotence", [47]),
   ("set-variable lemma", [149]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", [55]),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 37, 62, 87, 101, 102, 103, 104, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
      145, 146, 147])]

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
    [("function equation", 29), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 9), ("subsort", 15), ("injectivity", 6), ("distinctness", 1), ("no junk", 11), ("function functional", 15), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 1), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 22)] := by
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
  [(134, "B"), (135, "Bool"), (136, "GeneratedCounterCell"), (137, "GeneratedCounterCellOpt"),
   (138, "GeneratedTopCell"), (139, "GeneratedTopCellFragment"), (140, "Int"), (141, "K"),
   (142, "KCell"), (143, "KCellOpt"), (144, "KItem"), (145, "List"), (146, "Map"), (147, "Set")]

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
  [(17, "subsort"), (55, "open generator functional"), (56, "constructor functional"),
   (57, "injectivity"), (58, "distinctness"), (59, "constructor functional"), (60, "injectivity"),
   (61, "constructor functional"), (64, "function functional"), (88, "no junk"), (98, "no junk"),
   (99, "rewrite rule"), (104, "no direction"), (105, "function equation"),
   (106, "function equation"), (134, "no direction"), (149, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. The open generator `and` is a parameter (`raw`) that no
registry hook interprets, declared without `hook` and without `function`, and the text states
no equation of it (`AttrsAgree.eqnsOf`), which `AttrsAgree.hooks` admits. -/
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

/-! ## Consistency for every H satisfying the open generator's laws -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- No function's fact is named: under every interpretation that satisfies the open generator's
laws, `FnFacts` holds. -/
theorem facts (H : HookParams) (hop : OpenLaws (cH H)) : FnFacts (cH H) callOrder [] :=
  FnFacts.of_nil_laws
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) hop

/-- **Γ with the step's closure has a model, for every H that satisfies the open generator's laws**
(`OpenLaws`). -/
theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hop)

/-- **`lawHooks c H` satisfies the laws and gives `and` a value at every pair of B values**,
for every H; so Γ with the step's closure has a model there. -/
theorem lawHooks_laws (H : HookParams) :
    OpenLaws (c.withHooks (lawHooks c H)) ∧ OpenTotal (c.withHooks (lawHooks c H)) :=
  ⟨openLaws_lawHooks c coreOK H, openTotal_lawHooks c coreOK H⟩

theorem consistent_lawHooks (H : HookParams) : Consistent (c.withHooks (lawHooks c H)) :=
  consistent (lawHooks c H) (lawHooks_laws H).1

/-- **`lawHooks c H` is admitted by the library's sentences wherever H is and gives `_RangeMap_`
no value**, for every H (`KCore.libAdmitted_lawHooks`). -/
theorem libAdmitted_lawHooks (H : HookParams) (ha : (c.withHooks H).libAdmitted)
    (hrm : ∀ vs, H.app rmConcat vs = none) : (c.withHooks (lawHooks c H)).libAdmitted :=
  KCore.libAdmitted_lawHooks c coreOK H ha hrm

/-- **`lawHooks c HookParams.lib` satisfies the laws, the open generators' `functional` sentences
and the library's sentences together.** -/
theorem lawHooks_lib :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted :=
  ⟨(lawHooks_laws HookParams.lib).1, (lawHooks_laws HookParams.lib).2,
    libAdmitted_lawHooks HookParams.lib (libAdmitted_lib_of_coreOK coreOK) lib_app_rmConcat_none⟩

/-- **`and` has no law: `OpenLaws` holds under every interpretation.** -/
theorem openLaws_any (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'
  rw [params_raw, List.mem_singleton] at hm
  simp only [Prod.mk.injEq] at hm
  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent_any (H : HookParams) : Consistent (cH H) := consistent H (openLaws_any H)

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
def fnFunIdx : List Nat := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]

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
  [U.ax119, U.ax127, U.ax126, U.ax125, U.ax124, U.ax131, U.ax130, U.ax133, U.ax132, U.ax129,
   U.ax128, U.ax108, U.ax107, U.ax118, U.ax117, U.ax114, U.ax113, U.ax116, U.ax115, U.ax121,
   U.ax120, U.ax123, U.ax122, U.ax110, U.ax109, U.ax112, U.ax111, U.ax106, U.ax105]

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
theorem nj94 : (trS U.ax94).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj97 : (trS U.ax97).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax89, U.ax94, U.ax97], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj89]; exact orTopBot_valid hD rfl
  · rw [nj94]; exact orTopBot_valid hD rfl
  · rw [nj97]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax98).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (98)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax98).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- B's generators in the order the text's no-junk sentence (88) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def bTextGens : List KoreAML.Gen :=
  match (c.gens b).map (Gen.toK c) with
  | [g0, g1] => [g1, g0]
  | gs => gs

/-- B's no-junk sentence (88) is the item over B's generators in the text's order. -/
theorem nojunk_b_order : (trS U.ax88).pat = (KoreAML.Cons.noJunkItem (c.sortName b) bTextGens).pat := by
  decide +kernel
theorem nojunk_b_members : bTextGens.isPerm ((c.gens b).map (Gen.toK c)) = true := by
  decide +kernel
theorem nojunk_b_and : ((c.gens b).map (Gen.toK c)).length = 2 ∧ c.isOpenGen (.ctor ⟨and, [b, b], b⟩) = true := by
  decide +kernel

/-- **E for B's no junk (88)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_b_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax88).pat := by
  intro M _ I hI
  rw [nojunk_b_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens b).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_b_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := b)
    (show b ∈ consSorts c by decide +kernel) (show (c.gens b).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax56,
   U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax80, U.ax81]

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

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  simp only [Semantics.sortsOf, s1_sort H]
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


/-! ## The functional sentence of `and` (55): owed as `OpenTotal` -/

/-- **Γ holds no item for `and`'s functional sentence**: the constructors' items state the
functionality of the generators that are no open generator only. The sentence is owed, at values,
as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : !(consItemsK c).any (·.pat == (trS U.ax55).pat) &&
    !(fnItems c).any (·.pat == (trS U.ax55).pat) &&
    (classOf "open generator functional" == [55]) = true := by
  decide +kernel

/-! ## The rule (sentence 99): W1 and W2, through the cut

Γ's rule is the text's read through the cut (`Parse.ovlCut`): its left side holds the variable
`Open0` (`V`) in the place of `and(X, Y)` (`φ`), and its `pre` is `Open0 ∈ and(X, Y)`. Γ's axiom is
`\rewrites(K[V] ∧ ⊤ ∧ V ∈ φ ∧ ⌈r⌉, r)` (`p0_parts`), and the text's sentence 99 is the item of
`\rewrites(K[φ] ∧ ⊤, r)` at the table of Γ's axiom, its variables renamed (`rule_text`).
`K[φ]` is the union of `K[b]` over the elements b of φ (`KoreAML.cut_sem`), so:
the sentence gives Γ's item (`rule_from_text`, W1, every H); and Γ's item gives the sentence in a
model of Γ (`rule_to_text`, W2, every H), every element of `and(X, Y)` being in B by `and`'s arity
item (`and_inB`) and `⌈r⌉` (the premise `⌈rhs ∧ ens⌉` every rule's item carries) holding of every
element of the text's left side (`RightDefined`, `right_defined`): the right side is
`<generatedTop>(<k>(kseq(d(X), dotk)), C) ∧ ⊤`, built of variables of the text and of constructors
whose Cons-Fun items Γ has, so it holds one element where the variables' guards hold
(`TieRuleCut.rightDefined_of_Γ`). `rule_tie`: the two as one statement. -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- The context of its left side's term around the first argument of `c`. -/
noncomputable def K : KoreCutCtx :=
  ((TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)).1

/-- The variable of the cut, `Open0` (the rule's fourth variable). -/
def V : Kore.EVar := ⟨⟨⟨"VarV3"⟩⟩, KoreAML.srt "B"⟩
/-- X and Y, the rule's first two variables. -/
def X : Kore.EVar := ⟨⟨⟨"VarV0"⟩⟩, KoreAML.srt "B"⟩
def Y : Kore.EVar := ⟨⟨⟨"VarV1"⟩⟩, KoreAML.srt "B"⟩

/-- The application the cut takes out, `and(X, Y)`. -/
def φ : Kore.Pattern := .app ⟨⟨"Lbland"⟩⟩ [] [.var (.evar X), .var (.evar Y)]

/-- The conjuncts Γ's left side holds after the membership: `⌈r⌉`. -/
noncomputable def extra : List Kore.Pattern := [.ceil q0.1 q0.1 q0.2.2]

theorem q0_sort : q0.1 = KoreAML.srt "GeneratedTopCell" := by decide +kernel

/-- **Γ's axiom is `\rewrites(K[V] ∧ ⊤ ∧ V ∈ φ ∧ ⌈r⌉, r)`** (kernel). -/
theorem p0_parts : TieRuleLhs.rwParts p0 = some (q0.1,
    .and q0.1 (K.fill (.var (.evar V)) :: ([.top q0.1] ++ .in V.sort q0.1 (.var (.evar V)) φ :: extra)), q0.2.2) := by
  decide +kernel

/-- The left side as the text writes it: `and(X, Y)` in the place of the variable, and no conjunct
after `\top`. -/
noncomputable def Ltext : Kore.Pattern := .and q0.1 (K.fill φ :: [.top q0.1])

/-- The free variables of the text's form: X, Y and the counter cell's. -/
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups

/-- **The text's sentence 99 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**,
its three variables renamed (kernel): in Γ's table the variable of the cut is the first. -/
theorem rule_text : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT q0.1 Ltext q0.2.2) [(2, 1), (3, 2), (4, 3)] =
    some (trS U.ax99).pat := by decide +kernel
theorem fT_free : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem fG_split : (freeOf [] p0).eraseDups.all (fun k => fT.contains k || k == evarKey V) = true := by decide +kernel
theorem K_noAlias : K.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
/-- The variable of the cut is free in nothing of the two items but its occurrence and its
membership (kernel). -/
theorem cut_fresh : TieRuleCut.cutFreshB (tableOf [] p0) fT q0.1 K V φ q0.2.2 [.top q0.1] extra = true := by
  decide +kernel

/-- **W1 for the rule, and the converse for `ruleItems`**: Γ's rule item is a consequence of the
text's sentence 99, for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), TiePair.Texts [(trS U.ax99).pat] ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rw [List.mem_singleton.mp hit]
  exact TieRuleCut.openCut_w1 (TiePair.defOK_texts hI) p0_parts K_noAlias rule_text fT_free
    (hI _ (Or.inl (List.mem_singleton_self _)))

def topSrt : Srt := 17
theorem b_numbered (H : HookParams) : b < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : b < nRegSorts + c.sortNames.length)
theorem b_name (H : HookParams) : (cH H).sortName b = "B" := names.2
theorem top_numbered (H : HookParams) : topSrt < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topSrt < nRegSorts + c.sortNames.length)
theorem top_name (H : HookParams) : (cH H).sortName topSrt = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topSrt = "GeneratedTopCell")

/-- `and`'s arity item: applied to elements of B it gives elements of B only. -/
def andArity : P :=
  ((sym (.symbol "Lbland") ⬝ inhOf (sym (.sort "SortB"))) ⬝ inhOf (sym (.sort "SortB"))) ⊆⊆ inhOf (sym (.sort "SortB"))

theorem andArity_sig : (sigItems c).any (fun it => decide (it.pat = andArity)) = true := by decide +kernel

theorem tr_φ : tr ⟨tableOf [] p0, []⟩ φ = (sym (.symbol "Lbland") ⬝ .evar ⟨2⟩) ⬝ .evar ⟨3⟩ := by decide +kernel
theorem X_free : evarKey X ∈ fT := by decide +kernel
theorem Y_free : evarKey Y ∈ fT := by decide +kernel
theorem X_idx : (tableOf [] p0).ev (evarKey X) = ⟨2⟩ := by decide +kernel
theorem Y_idx : (tableOf [] p0).ev (evarKey Y) = ⟨3⟩ := by decide +kernel
theorem sortB_tr : trSort (tableOf [] p0) (KoreAML.srt "B") = sym (.sort "SortB") := by decide +kernel
theorem sortTop_tr : trSort (tableOf [] p0) q0.1 = sym (.sort "SortGeneratedTopCell") := by decide +kernel

/-- **Every element of `and(X, Y)` is in B**, where X and Y are (`and`'s arity item, of the
signature). -/
theorem and_inB (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (a : M)
    (ha : (tr ⟨tableOf [] p0, []⟩ φ).interpret I e a) : (inhOf (sym (.sort "SortB")) : P).interpret I e a := by
  obtain ⟨it, hit, hpat⟩ := List.any_eq_true.mp andArity_sig
  have har : I ⊧ᴵ andArity := by
    rw [← of_decide_eq_true hpat]
    exact hSig _ (Or.inl (Or.inl ⟨it, by rw [sigItems_withHooks]; exact hit, rfl⟩))
  have hgX := (TieRuleLhs.guard_evarKey hD).mp (hg _ X_free)
  have hgY := (TieRuleLhs.guard_evarKey hD).mp (hg _ Y_free)
  rw [show X.sort = KoreAML.srt "B" from rfl, sortB_tr, X_idx] at hgX
  rw [show Y.sort = KoreAML.srt "B" from rfl, sortB_tr, Y_idx] at hgY
  rw [tr_φ] at ha
  obtain ⟨f1, y, hf1, hy, h2⟩ := interp_app.mp ha
  obtain ⟨f0, x, hf0, hx, h1⟩ := interp_app.mp hf1
  rw [interp_evar] at hx hy
  unfold andArity at har
  refine (interp_included hD).mp (har e default) a (interp_app.mpr ⟨f1, y, interp_app.mpr ⟨f0, x, hf0, ?_, h1⟩, ?_, h2⟩)
  · rw [hx]; exact hgX
  · rw [hy]; exact hgY

/-- The premise of W2: `⌈r⌉`, the definedness of the right side (the conjunct Γ's item of every
rule adds to the text's left side), holds of every element of the text's left side, where the
guards of the text's variables hold. -/
def RightDefined {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
    ∀ a, (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e a →
      (tr ⟨tableOf [] p0, []⟩ (.ceil q0.1 q0.1 q0.2.2)).interpret I e a

/-- The term of the right side, `<generatedTop>(<k>(kseq(d(X), dotk)), C)`. -/
noncomputable def rr : Kore.Pattern :=
  match q0.2.2 with
  | .and _ (p :: _) => p
  | p => p

/-- **The right side is `rr ∧ ⊤`**, of the sort of the top cell (kernel). -/
theorem right_parts : q0.1 = srtOf c topSrt ∧ q0.2.2 = .and (srtOf c topSrt) [rr, .top (srtOf c topSrt)] := by
  decide +kernel

/-- The constructors of the right side, each with the name of its sort. -/
def rightCtors : List (String × KoreAML.CtorSig) :=
  [("GeneratedTopCell", ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("K", ⟨"dotk", [], "K"⟩),
   ("KItem", ⟨"Lbld", ["B"], "KItem"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCut.funsInB c rightCtors = true := by decide +kernel

/-- The right side's term is built of the text's variables and of those constructors, at arguments
of their sorts (kernel). -/
theorem right_built : TieRuleCut.builtB rightCtors fT rr "GeneratedTopCell" = true := by decide +kernel

/-- **The premise of W2 holds in every model of Γ**, for every H: the right side holds one
element where the guards of the text's variables hold, by the Cons-Fun items of its constructors. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : RightDefined I := by
  intro e m hg a ha
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hb : TieRuleCut.builtB rightCtors fT rr ((cH H).sortName topSrt) = true := by
    rw [top_name]; exact right_built
  have haT : (inhOf (trSort (tableOf [] p0) (srtOf (cH H) topSrt))).interpret I e a := by
    have h1 := (interp_and (List.cons_ne_nil _ _)).mp ha (.top q0.1) (List.mem_cons_of_mem _ List.mem_cons_self)
    have h2 : tr ⟨tableOf [] p0, []⟩ (.top q0.1) = sTop (trSort (tableOf [] p0) q0.1) := by rw [tr]
    rw [h2, interp_sTop hD (by rw [sortTop_tr]; rfl)] at h1
    rw [right_parts.1] at h1
    exact h1
  have h := TieRuleCut.rightDefined_of_Γ hI (top_numbered H)
    ((TieRuleCut.funsInB_withHooks c H rightCtors).trans right_funs) hb e m hg a haT
  rw [right_parts.1, right_parts.2]
  exact h

/-- **The tie of the rule's sentence**: in a model of Γ, the text's sentence 99 and Γ's rule item
hold together, for every H. -/
theorem rule_tie (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    (I ⊧ᴵ (trS U.ax99).pat) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat) := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hdef := right_defined H hI
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (b_numbered H)
  obtain ⟨σT, hσT1, hσT2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered H)
  rw [b_name] at hσB1
  rw [top_name] at hσT1
  have hB : ∀ (e : Valuation M) a, (trSort (tableOf [] p0) V.sort).interpret I e a ↔ a = σB := fun e a => by
    rw [show V.sort = KoreAML.srt "B" from rfl, sortB_tr]; exact hσB1 a
  have hT : ∀ (e : Valuation M) a, (trSort (tableOf [] p0) q0.1).interpret I e a ↔ a = σT := fun e a => by
    rw [sortTop_tr]; exact hσT1 a
  refine TieRuleCut.openCut_tie hD hc p0_parts K_noAlias rule_text fT_free fG_split List.mem_cons_self cut_fresh
    hB hT hσB2 hσT2 (fun e m hg b hb => ?_) (fun e m hg a ha q hq => ?_)
  · have h1 := and_inB H hD hSig e m hg b hb
    rw [← sortB_tr] at h1
    exact (interp_inhOf_of (hB e)).mp h1
  · rw [List.mem_singleton.mp hq]; exact hdef e m hg a ha

/-- **W2 for the rule**: Γ's rule item gives the text's sentence 99 in a model of Γ, for every H. -/
theorem rule_to_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    ∀ it ∈ ruleItems (cH H), (I ⊧ᴵ it.pat) → (I ⊧ᴵ (trS U.ax99).pat) := by
  intro it hit hIt
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rw [List.mem_singleton.mp hit] at hIt
  exact (rule_tie H hI).mpr hIt

/-! ## The steps of the rule, for every H (written by hand)

The rule is read through the cut: `<k> c(Open0, X, Y) => d(X) </k>` with `pre := Open0 ∈ and(X, Y)`
(`orhR0`), whose term is the interpretation's value of `and` at the values of X and Y
(`EvalTerm.param`, `Semantics.paramVal`). So `<k> c(v, a, b) </k>` steps exactly where H gives
`and(a, b)` the value v, and then to `<k> d(a) </k>` alone (`orhStep_iff`).

- `orhStep_ee` (from the sentences): where H gives `and(e, e)` the value v, `<k> c(v, e, e) </k>`
  has the successor `<k> d(e) </k>`. The premises (`orhPre`) are the function sentences as written,
  Γ's rule item (a consequence of sentence 99, `rule_from_text`; the two hold together in a model of
  Γ, `rule_tie`) and the families of the reading; the value of `and(e, e)` is the family ΓDomains'
  (the parameter's graph at H), which no sentence states. They have a model with the step's
  closure (`orhPre_model`).
- `orhNoStep_ee` (through the reading): where H gives `and(e, e)` no value or another one than v,
  `<k> c(v, e, e) </k>` has no successor, with the step's closure.
- `orhStep_undetermined`: the text does not determine whether `<k> c(e, e, e) </k>` steps to
  `<k> d(e) </k>`: at `fstH`, where `and(e, e)` is `e`, it does; at `HookParams.none`, where
  `and(e, e)` is the application itself, it does not. Both theories have models. -/

def orhK : Sym := 383
def orhC : Sym := 385
def orhD : Sym := 386
def orhESym : Sym := 387

theorem orhNames : c.symName orhK = "Lbl'-LT-'k'-GT-'" ∧ c.symName orhC = "Lblc" ∧ c.symName orhD = "Lbld" ∧
    c.symName orhESym = "Lble" := by decide +kernel

def orhAndP : ParamSig := { sig := ⟨and, [b, b], b⟩, raw := true }

theorem orhR0_mem (H : HookParams) : r0 ∈ (cH H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem orhRule_eq (H : HookParams) {r : Rule} (hr : r ∈ (cH H).rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by change i < c.rules.length at hi; omega
  subst this
  rfl

/-- **The cut's reading of the rule**: variables X, Y (of B), the counter cell's and Open0 (of B);
no `requires` or `ensures`; `pre` the membership of Open0 in `and(X, Y)`; `post` true; no
existential variable. -/
theorem orhR0 : r0.vars = [b, b, 19, b] ∧
    r0.lhs = .app topLabel [.app orhK [.app kseq [.app orhC [.var 3, .var 0, .var 1], .app dotk []]], .var 2] ∧
    r0.rhs = .app topLabel [.app orhK [.app kseq [.app orhD [.var 0], .app dotk []]], .var 2] ∧
    r0.req = none ∧ r0.ens = none ∧ r0.pre = .mem b (.var 3) (.app and [.var 0, .var 1]) ∧ r0.post = .top ∧
    r0.exs = [] :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem orhFacts : r0.reqClosed = false ∧ c.fns = [] ∧ (∀ j ∈ varOccs r0.rhs, j < 4) := by decide +kernel

theorem orhSyms (H : HookParams) : (cH H).isCtor topLabel = true ∧ (cH H).isCtor orhK = true ∧
    (cH H).isCtor kseq = true ∧ (cH H).isCtor orhC = true ∧ (cH H).isCtor dotk = true ∧
    (cH H).isCtor orhD = true := by
  change c.isCtor topLabel = true ∧ c.isCtor orhK = true ∧ c.isCtor kseq = true ∧
    c.isCtor orhC = true ∧ c.isCtor dotk = true ∧ c.isCtor orhD = true
  decide +kernel

theorem orhHooks : patternHooks.contains topLabel = false ∧ patternHooks.contains orhK = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains orhC = false := by
  decide +kernel

/-- `and` is a parameter, neither a constructor nor a hooked symbol, read as the open generator
`orhAndP` with no registry hook. -/
theorem orhAnd (H : HookParams) : (cH H).isCtor and = false ∧ isHook and = false ∧
    (cH H).isParam and = true ∧ (cH H).lookupParam and = some orhAndP := by
  change c.isCtor and = false ∧ isHook and = false ∧ c.isParam and = true ∧ c.lookupParam and = some orhAndP
  decide +kernel

/-- **`FnHyp` holds at every H**: the text declares no function, the rule needs no witness (its
condition holds Open0, which the left side binds), and `and` has no law. -/
theorem orhFnHyp (H : HookParams) : FnHyp (cH H) :=
  have hn : ∀ fn, fn ∈ (cH H).fns → False := fun fn hfn => by
    change fn ∈ c.fns at hfn
    rw [orhFacts.2.1] at hfn
    cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain (fun r hr => by
        rw [orhRule_eq H hr]
        simp [Rule.needsWitness, orhFacts.1]) (fun fn hfn => (hn fn hfn).elim),
    openLaws_any H⟩

theorem orhFnDet (H : HookParams) : FnDet (cH H) := (fnModel_of_fnHyp (coreOKH H) (orhFnHyp H)).1

/-! ### The configurations -/

def orhCtr : GroundTerm := .ctor counterLabel [int 0]
def orhE : GroundTerm := .ctor orhESym []

/-- `<k> st ~> . </k>` with the counter 0. -/
def orhCfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor orhK [.ctor kseq [st, .ctor dotk []]], orhCtr]

theorem orhCtr_sort (H : HookParams) : (cH H).sortOf orhCtr = some 19 :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

theorem orhE_sort (H : HookParams) : (cH H).sortOf orhE = some b :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

/-- The substitution of the rule's variables X, Y, the counter and Open0. -/
def orhσ (x y v : GroundTerm) : Subst := [(0, x), (1, y), (2, orhCtr), (3, v)]

theorem orhMatch (H : HookParams) (x y v : GroundTerm) :
    PatVal (cH H) (orhσ x y v) r0.lhs (orhCfg (.ctor orhC [v, x, y])) := by
  rw [orhR0.2.1]
  have hs := orhSyms H
  exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
    (.cons (.ctor hs.2.2.2.1 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (.cons (.ctor hs.2.2.2.2.1 .nil) .nil))) .nil))
    (.cons (.var rfl) .nil))

theorem orhEvalD (H : HookParams) (x y v : GroundTerm) :
    EvalTerm (cH H) (orhσ x y v) r0.rhs (some (orhCfg (.ctor orhD [x]))) := by
  rw [orhR0.2.2.1]
  have hs := orhSyms H
  exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
    (.cons (.ctor hs.2.2.2.2.2 (.cons .var .nil)) (.cons (.ctor hs.2.2.2.2.1 .nil) .nil))) .nil))
    (.cons .var .nil))

/-- `pre` at any substitution: its truth value is whether the value of Open0 is the value
`paramVal` gives `and` at the values of X and Y. -/
theorem orhPre_at (H : HookParams) (τ : Subst) :
    Holds (cH H) r0.vars.length τ r0.pre ((τ.lookup 3).isSome &&
      sameResult (τ.lookup 3) ((allSome [τ.lookup 0, τ.lookup 1]).bind ((cH H).paramVal and))) := by
  rw [orhR0.2.2.2.2.2.1]
  have ha := orhAnd H
  exact .mem .var (.param ha.1 ha.2.1 ha.2.2.1 (.cons .var (.cons .var .nil)) rfl)

theorem orhSame_iff (v : GroundTerm) (r : Option GroundTerm) :
    sameResult (some v) r = true ↔ r = some v := by
  cases r with
  | none => simp [sameResult]
  | some w =>
    simp only [sameResult, beq_iff_eq, Option.some.injEq]
    exact ⟨fun h => (cmp_eq_iff.mp h).symm, fun h => cmp_eq_iff.mpr h.symm⟩

/-- The value `paramVal` gives `and` is of sort B. -/
theorem orhVal_sort (H : HookParams) {x y v : GroundTerm} (hv : (cH H).paramVal and [x, y] = some v) :
    (cH H).sortOf v = some b :=
  ((paramVal_raw_sorted (orhAnd H).2.2.2 rfl rfl).mp hv).2

/-- The step by the rule at `orhσ x y v`, where `and` is v at (x, y). -/
theorem orhStepBy (H : HookParams) {x y v : GroundTerm} (hx : (cH H).sortOf x = some b)
    (hy : (cH H).sortOf y = some b) (hv : (cH H).paramVal and [x, y] = some v)
    (X Y : Config (cH H)) (hX : X.val = orhCfg (.ctor orhC [v, x, y])) (hY : Y.val = orhCfg (.ctor orhD [x])) :
    StepBy (cH H) r0 (orhσ x y v) X Y where
  mem := orhR0_mem H
  hσ := fun j s hs => by
    rw [orhR0.1] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, hx⟩
    | 1, hs => cases hs; exact ⟨_, rfl, hy⟩
    | 2, hs => cases hs; exact ⟨_, rfl, orhCtr_sort H⟩
    | 3, hs => cases hs; exact ⟨_, rfl, orhVal_sort H hv⟩
  hmatch := hX ▸ orhMatch H x y v
  hreq := fun t ht => by rw [orhR0.2.2.2.1] at ht; cases ht
  hpre := by
    have hp := orhPre_at H (orhσ x y v)
    have h3 : (orhσ x y v).lookup 3 = some v := rfl
    have hab : (allSome [(orhσ x y v).lookup 0, (orhσ x y v).lookup 1]) = some [x, y] := rfl
    rw [h3, hab, Option.bind_some, hv] at hp
    have ht : ((some v).isSome && sameResult (some v) (some v)) = true := by
      simp [(orhSame_iff v (some v)).mpr rfl]
    exact ht ▸ hp
  heval := hY ▸ orhEvalD H x y v
  hens := fun t ht => by rw [orhR0.2.2.2.2.1] at ht; cases ht
  hpost := by rw [orhR0.2.2.2.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [orhRule_eq H hr'] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- A substitution under which the left side denotes `<k> c(v, x, y) </k>` gives Open0, X, Y and
the counter cell those values. -/
theorem orhLookups {H : HookParams} {τ : Subst} {x y v : GroundTerm}
    (hm : PatVal (cH H) τ r0.lhs (orhCfg (.ctor orhC [v, x, y]))) :
    τ.lookup 3 = some v ∧ τ.lookup 0 = some x ∧ τ.lookup 1 = some y ∧ τ.lookup 2 = some orhCtr := by
  rw [orhR0.2.1] at hm
  have hs := orhSyms H
  obtain ⟨-, vs, hv, hs1⟩ := PatVal.app_inv orhHooks.1 hm hs.1
  injection hv with _ hv
  subst hv
  cases hs1 with
  | cons hk hs2 =>
    cases hs2 with
    | cons h2 _ =>
      obtain ⟨-, vs, hv, hs3⟩ := PatVal.app_inv orhHooks.2.1 hk hs.2.1
      injection hv with _ hv
      subst hv
      cases hs3 with
      | cons hq _ =>
        obtain ⟨-, vs, hv, hs4⟩ := PatVal.app_inv orhHooks.2.2.1 hq hs.2.2.1
        injection hv with _ hv
        subst hv
        cases hs4 with
        | cons hcv _ =>
          obtain ⟨-, vs, hv, hs5⟩ := PatVal.app_inv orhHooks.2.2.2 hcv hs.2.2.2.1
          injection hv with _ hv
          subst hv
          cases hs5 with
          | cons h3 hs6 =>
            cases hs6 with
            | cons h0 hs7 =>
              cases hs7 with
              | cons h1 _ =>
                exact ⟨PatVal.var_inv h3, PatVal.var_inv h0, PatVal.var_inv h1, PatVal.var_inv h2⟩

/-- **For every interpretation H, `<k> c(v, x, y) </k>` steps to Y exactly when the
interpretation's `and` is v at (x, y) and Y is `<k> d(x) </k>`.** -/
theorem orhStep_iff (H : HookParams) (X Y : Config (cH H)) {x y v : GroundTerm}
    (hx : (cH H).sortOf x = some b) (hy : (cH H).sortOf y = some b)
    (hX : X.val = orhCfg (.ctor orhC [v, x, y])) :
    Step (cH H) X Y ↔ (cH H).paramVal and [x, y] = some v ∧ Y.val = orhCfg (.ctor orhD [x]) := by
  constructor
  · intro hs
    obtain ⟨r, τ, hst⟩ := step_iff_by.mp hs
    have hr := orhRule_eq H hst.mem
    subst hr
    have hm : PatVal (cH H) τ r0.lhs (orhCfg (.ctor orhC [v, x, y])) := hX ▸ hst.hmatch
    obtain ⟨h3, h0, h1, h2⟩ := orhLookups hm
    have hd := orhFnDet H
    have hp := Holds.functional_of_fnDet hd hst.hpre (orhPre_at H τ)
    rw [h3, h0, h1] at hp
    have hab : allSome [some x, some y] = some [x, y] := rfl
    rw [hab, Option.bind_some] at hp
    have hv : (cH H).paramVal and [x, y] = some v := by
      have : sameResult (some v) ((cH H).paramVal and [x, y]) = true := by
        simpa using hp.symm
      exact (orhSame_iff v _).mp this
    have hτ : ∀ j ∈ varOccs r0.rhs, (orhσ x y v).lookup j = τ.lookup j := fun j hj => by
      have hj4 := orhFacts.2.2 j hj
      match j, hj4 with
      | 0, _ => exact h0.symm
      | 1, _ => exact h1.symm
      | 2, _ => exact h2.symm
      | 3, _ => exact h3.symm
    have he := EvalTerm.functional_of_fnDet hd hst.heval
      (Exec.EvalTerm.congr (orhEvalD H x y v) hτ)
    exact ⟨hv, Option.some.inj he⟩
  · rintro ⟨hv, hY⟩
    exact step_iff_by.mpr ⟨r0, orhσ x y v, orhStepBy H hx hy hv X Y hX hY⟩

/-! ### The premises of the derivation -/

noncomputable def orhTextPats : List P := fnText.map (trS · |>.pat)

theorem orhShape : TiePair.shapeB (TiePair.gammaPats c) orhTextPats = true := by decide +kernel

theorem orhShapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) orhTextPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact orhShape

/-- The function sentences as written, Γ's rule item and the families of the reading. The
definition reads no confined sort, so the theory the statements are about is Γ. -/
def orhPre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) orhTextPats

/-- **Every premise of Γ is a consequence of `orhPre`.** -/
theorem orhGamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → orhPre H ⊧ φ :=
  TiePair.gamma_from (orhShapeH H)

/-- **`orhPre` with the step's closure has a model, for every H**: every model of Γ with it is one. -/
theorem orhPre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (orhPre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent_any H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with h | h
  · rcases h with ((h1 | h1) | h1)
    · rcases h1 with ht | ⟨x, rfl⟩
      · exact TiePair.entailed (orhShapeH H) φ ht hΓ
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
    · exact hΓ _ (Or.inl (Or.inr h1))
    · rcases h1 with (((h1 | h1) | h1) | h1) | h1
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
      · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inr h)

theorem orhReadsConfinedH (H : HookParams) : (cH H).readsConfined = false := readsConfined_c

/-! ### The expectations -/

/-- **Where H gives `and(x, y)` the value v, `<k> c(v, x, y) </k>` has the successor
`<k> d(x) </k>`, from the sentences**, for every H and all values x, y of B. -/
theorem orhStep (H : HookParams) {x y v : GroundTerm} (hx : (cH H).sortOf x = some b)
    (hy : (cH H).sortOf y = some b) (hv : (cH H).paramVal and [x, y] = some v)
    (X Y : Config (cH H)) (hX : X.val = orhCfg (.ctor orhC [v, x, y])) (hY : Y.val = orhCfg (.ctor orhD [x])) :
    orhPre H ⊧ (den (cH H) X.val ⇒ KoreAML.sNext (den (cH H) Y.val)) :=
  fun hT => sound_at_step (cH H) (coreOKH H) (orhReadsConfinedH H) X Y
    ((orhStep_iff H X Y hx hy hX).mpr ⟨hv, hY⟩) fun φ hφ => orhGamma_from H φ hφ hT

/-- **Where H gives `and(e, e)` the value v, `<k> c(v, e, e) </k>` steps to `<k> d(e) </k>`, from
the sentences**, for every H: sentence 99, the rule, at X := e, Y := e, where `and(X, Y)` is v. -/
theorem orhStep_ee (H : HookParams) {v : GroundTerm} (hv : (cH H).paramVal and [orhE, orhE] = some v)
    (X Y : Config (cH H)) (hX : X.val = orhCfg (.ctor orhC [v, orhE, orhE]))
    (hY : Y.val = orhCfg (.ctor orhD [orhE])) :
    orhPre H ⊧ (den (cH H) X.val ⇒ KoreAML.sNext (den (cH H) Y.val)) :=
  orhStep H (orhE_sort H) (orhE_sort H) hv X Y hX hY

/-- **Where H gives `and(e, e)` no value or another one than v, `<k> c(v, e, e) </k>` has no
successor**, for every H, with the step's closure: the one rule's membership fails at its one
match. -/
theorem orhNoStep_ee (H : HookParams) {v : GroundTerm} (hv : (cH H).paramVal and [orhE, orhE] ≠ some v)
    (X : Config (cH H)) (hX : X.val = orhCfg (.ctor orhC [v, orhE, orhE])) :
    (orhPre H ∪ Γstep (cH H)) ⊧ (den (cH H) X.val ⇒ KoreAML.allNext (KoreAML.disjList
      (([] : List GroundTerm).map (den (cH H))))) :=
  fun hT => complete_at_step (cH H) (coreOKH H) (orhReadsConfinedH H) X
    (stepDecided_of_fnHyp (coreOKH H) (orhFnHyp H) X) []
    (fun Y hs => absurd ((orhStep_iff H X Y (orhE_sort H) (orhE_sort H) hX).mp hs).1 hv)
    fun φ hφ => by
      rcases hφ with hφ | hφ
      · exact orhGamma_from H φ hφ (fun χ hχ => hT χ (Or.inl hχ))
      · exact hT φ (Or.inr hφ)

/-- `<k> c(e, e, e) </k>` and `<k> d(e) </k>`. -/
def orhA : GroundTerm := orhCfg (.ctor orhC [orhE, orhE, orhE])
def orhB : GroundTerm := orhCfg (.ctor orhD [orhE])

theorem orhA_sort (H : HookParams) : (cH H).sortOf orhA = some topCellSort :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)
theorem orhB_sort (H : HookParams) : (cH H).sortOf orhB = some topCellSort :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

/-- At `fstH`, `and(e, e)` is `e`; at `HookParams.none` it is the application, another value. -/
theorem orhAnd_values : (cH fstH).paramVal and [orhE, orhE] = some orhE ∧
    (cH HookParams.none).paramVal and [orhE, orhE] ≠ some orhE := by
  decide +kernel

/-- **The text does not determine whether `<k> c(e, e, e) </k>` steps to `<k> d(e) </k>`**: over
all H, the reading's theory with the step's closure entails neither that `<k> d(e) </k>` is not a
successor of `<k> c(e, e, e) </k>` nor that it is one. The first is refuted at `fstH`, where
`and(e, e)` is `e` and the step exists (in a model exactness gives); the second at
`HookParams.none`, where `and(e, e)` is the application itself, the configuration has no step, and
the theory has a model (`consistent_any`). -/
theorem orhStep_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) orhA ⇒ ∼ KoreAML.sNext (den (cH H) orhB))) ∧
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) orhA ⇒ KoreAML.sNext (den (cH H) orhB))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let X : Config (cH fstH) := ⟨orhA, orhA_sort fstH⟩
    let Y : Config (cH fstH) := ⟨orhB, orhB_sort fstH⟩
    have hs : Step (cH fstH) X Y :=
      (orhStep_iff fstH X Y (orhE_sort fstH) (orhE_sort fstH) rfl).mpr ⟨orhAnd_values.1, rfl⟩
    obtain ⟨M, hM, I, hI, hn⟩ := (exact_hyp (cH fstH) (coreOKH fstH) (orhFnHyp fstH) X Y).mp hs
    exact hn (h fstH hI)
  · let X : Config (cH HookParams.none) := ⟨orhA, orhA_sort _⟩
    let Y : Config (cH HookParams.none) := ⟨orhB, orhB_sort _⟩
    have hns : ¬ Step (cH HookParams.none) X Y := fun hs =>
      orhAnd_values.2 ((orhStep_iff _ X Y (orhE_sort _) (orhE_sort _) rfl).mp hs).1
    obtain ⟨M, hM, I, hI⟩ := consistent_any HookParams.none
    have hIΓ : I ⊧ᴵP Γ (cH HookParams.none) := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
    have hno : I ⊧ᴵ (den (cH HookParams.none) X.val ⇒ ∼ KoreAML.sNext (den (cH HookParams.none) Y.val)) :=
      Classical.not_not.mp fun hn =>
        hns ((exact_hyp _ (coreOKH _) (orhFnHyp _) X Y).mpr ⟨M, hM, I, hI, hn⟩)
    have hx := ((elemOf_spec hIΓ X.property KoreAML.val0).1 (elemOf (cH HookParams.none) I X.val)).mpr rfl
    have h1 := hno KoreAML.val0 (elemOf (cH HookParams.none) I X.val)
    have h2 := h HookParams.none hI KoreAML.val0 (elemOf (cH HookParams.none) I X.val)
    rw [interpret_impl] at h1 h2
    have h3 := h1 hx
    rw [interpret_neg] at h3
    exact h3 (h2 hx)

end KCore.TieE2OpenRecHeld

#check @KCore.TieE2OpenRecHeld.params_raw
#check @KCore.TieE2OpenRecHeld.readsConfined_c
#check @KCore.TieE2OpenRecHeld.userAxioms_eq
#check @KCore.TieE2OpenRecHeld.coreOK
#check @KCore.TieE2OpenRecHeld.wf_defn
#check @KCore.TieE2OpenRecHeld.account
#check @KCore.TieE2OpenRecHeld.account_sizes
#check @KCore.TieE2OpenRecHeld.account_classes
#check @KCore.TieE2OpenRecHeld.account_absent
#check @KCore.TieE2OpenRecHeld.absent_closed
#check @KCore.TieE2OpenRecHeld.absent_proj_below_c
#check @KCore.TieE2OpenRecHeld.absent_proj_below
#check @KCore.TieE2OpenRecHeld.lists_in_account
#check @KCore.TieE2OpenRecHeld.attrs_agree
#check @KCore.TieE2OpenRecHeld.sig_origin
#check @KCore.TieE2OpenRecHeld.decls_entailed
#check @KCore.TieE2OpenRecHeld.consistent
#check @KCore.TieE2OpenRecHeld.fnFun_indices
#check @KCore.TieE2OpenRecHeld.fnFun_account
#check @KCore.TieE2OpenRecHeld.fnFun_checked
#check @KCore.TieE2OpenRecHeld.fnFun_trS
#check @KCore.TieE2OpenRecHeld.fnFun_at_values
#check @KCore.TieE2OpenRecHeld.fnFun_at_values_step
#check @KCore.TieE2OpenRecHeld.fn_shape
#check @KCore.TieE2OpenRecHeld.fns_account
#check @KCore.TieE2OpenRecHeld.fns_entailed
#check @KCore.TieE2OpenRecHeld.fns_from_text
#check @KCore.TieE2OpenRecHeld.fn_prios
#check @KCore.TieE2OpenRecHeld.nojunk_trivial_entailed
#check @KCore.TieE2OpenRecHeld.nojunk_items_entailed
#check @KCore.TieE2OpenRecHeld.nojunk_kitem_entailed
#check @KCore.TieE2OpenRecHeld.cons_entailed
#check @KCore.TieE2OpenRecHeld.idem_refuted
#check @KCore.TieE2OpenRecHeld.names
#check @KCore.TieE2OpenRecHeld.facts
#check @KCore.TieE2OpenRecHeld.lawHooks_laws
#check @KCore.TieE2OpenRecHeld.consistent_lawHooks
#check @KCore.TieE2OpenRecHeld.libAdmitted_lawHooks
#check @KCore.TieE2OpenRecHeld.lawHooks_lib
#check @KCore.TieE2OpenRecHeld.openLaws_any
#check @KCore.TieE2OpenRecHeld.consistent_any
#check @KCore.TieE2OpenRecHeld.nojunk_b_order
#check @KCore.TieE2OpenRecHeld.nojunk_b_members
#check @KCore.TieE2OpenRecHeld.nojunk_b_and
#check @KCore.TieE2OpenRecHeld.nojunk_b_entailed
#check @KCore.TieE2OpenRecHeld.open_functional_not_item
#check @KCore.TieE2OpenRecHeld.ruleItems_eq
#check @KCore.TieE2OpenRecHeld.p0_parts
#check @KCore.TieE2OpenRecHeld.rule_text
#check @KCore.TieE2OpenRecHeld.cut_fresh
#check @KCore.TieE2OpenRecHeld.rule_from_text
#check @KCore.TieE2OpenRecHeld.and_inB
#check @KCore.TieE2OpenRecHeld.rule_tie
#check @KCore.TieE2OpenRecHeld.rule_to_text
#print axioms KCore.TieE2OpenRecHeld.params_raw
#print axioms KCore.TieE2OpenRecHeld.readsConfined_c
#print axioms KCore.TieE2OpenRecHeld.userAxioms_eq
#print axioms KCore.TieE2OpenRecHeld.coreOK
#print axioms KCore.TieE2OpenRecHeld.wf_defn
#print axioms KCore.TieE2OpenRecHeld.account
#print axioms KCore.TieE2OpenRecHeld.account_sizes
#print axioms KCore.TieE2OpenRecHeld.account_classes
#print axioms KCore.TieE2OpenRecHeld.account_absent
#print axioms KCore.TieE2OpenRecHeld.absent_closed
#print axioms KCore.TieE2OpenRecHeld.absent_proj_below_c
#print axioms KCore.TieE2OpenRecHeld.absent_proj_below
#print axioms KCore.TieE2OpenRecHeld.lists_in_account
#print axioms KCore.TieE2OpenRecHeld.attrs_agree
#print axioms KCore.TieE2OpenRecHeld.sig_origin
#print axioms KCore.TieE2OpenRecHeld.decls_entailed
#print axioms KCore.TieE2OpenRecHeld.consistent
#print axioms KCore.TieE2OpenRecHeld.fnFun_indices
#print axioms KCore.TieE2OpenRecHeld.fnFun_account
#print axioms KCore.TieE2OpenRecHeld.fnFun_checked
#print axioms KCore.TieE2OpenRecHeld.fnFun_trS
#print axioms KCore.TieE2OpenRecHeld.fnFun_at_values
#print axioms KCore.TieE2OpenRecHeld.fnFun_at_values_step
#print axioms KCore.TieE2OpenRecHeld.fn_shape
#print axioms KCore.TieE2OpenRecHeld.fns_account
#print axioms KCore.TieE2OpenRecHeld.fns_entailed
#print axioms KCore.TieE2OpenRecHeld.fns_from_text
#print axioms KCore.TieE2OpenRecHeld.fn_prios
#print axioms KCore.TieE2OpenRecHeld.nojunk_trivial_entailed
#print axioms KCore.TieE2OpenRecHeld.nojunk_items_entailed
#print axioms KCore.TieE2OpenRecHeld.nojunk_kitem_entailed
#print axioms KCore.TieE2OpenRecHeld.cons_entailed
#print axioms KCore.TieE2OpenRecHeld.idem_refuted
#print axioms KCore.TieE2OpenRecHeld.names
#print axioms KCore.TieE2OpenRecHeld.facts
#print axioms KCore.TieE2OpenRecHeld.lawHooks_laws
#print axioms KCore.TieE2OpenRecHeld.consistent_lawHooks
#print axioms KCore.TieE2OpenRecHeld.libAdmitted_lawHooks
#print axioms KCore.TieE2OpenRecHeld.lawHooks_lib
#print axioms KCore.TieE2OpenRecHeld.openLaws_any
#print axioms KCore.TieE2OpenRecHeld.consistent_any
#print axioms KCore.TieE2OpenRecHeld.nojunk_b_order
#print axioms KCore.TieE2OpenRecHeld.nojunk_b_members
#print axioms KCore.TieE2OpenRecHeld.nojunk_b_and
#print axioms KCore.TieE2OpenRecHeld.nojunk_b_entailed
#print axioms KCore.TieE2OpenRecHeld.open_functional_not_item
#print axioms KCore.TieE2OpenRecHeld.ruleItems_eq
#print axioms KCore.TieE2OpenRecHeld.p0_parts
#print axioms KCore.TieE2OpenRecHeld.rule_text
#print axioms KCore.TieE2OpenRecHeld.cut_fresh
#print axioms KCore.TieE2OpenRecHeld.rule_from_text
#print axioms KCore.TieE2OpenRecHeld.and_inB
#print axioms KCore.TieE2OpenRecHeld.rule_tie
#print axioms KCore.TieE2OpenRecHeld.rule_to_text
#check @KCore.TieE2OpenRecHeld.orhStep_iff
#check @KCore.TieE2OpenRecHeld.orhPre_model
#check @KCore.TieE2OpenRecHeld.orhStep
#check @KCore.TieE2OpenRecHeld.orhStep_ee
#check @KCore.TieE2OpenRecHeld.orhNoStep_ee
#check @KCore.TieE2OpenRecHeld.orhStep_undetermined
#print axioms KCore.TieE2OpenRecHeld.orhStep_iff
#print axioms KCore.TieE2OpenRecHeld.orhPre_model
#print axioms KCore.TieE2OpenRecHeld.orhStep_ee
#print axioms KCore.TieE2OpenRecHeld.orhNoStep_ee
#print axioms KCore.TieE2OpenRecHeld.orhStep_undetermined
