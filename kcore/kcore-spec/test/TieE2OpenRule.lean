/-
  The tie (C14) on `f2-examples/openrule.kompile.kore`, the kompiled text of construct fixture e2-open-rule
  (`test/constructs/fixtures/e2-open-rule`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e2-open-rule` (its text written there is `f2-examples/openrule.kompile.kore` byte for byte, which this test reads); run from the package root: `lake env lean -j1 test/TieE2OpenRule.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 203 sentences of the user module E2-OPEN-RULE, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the open
    generator `and` is a parameter declared without `hook` and without `function`, of which the
    text states no equation.
  - `sig_origin`: each of the 210 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`); its one open generator is `and`
    (`params_raw`), of Exp. It owes no fact
    about its functions (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the
    step's closure has a model for every H that satisfies the open generator's laws (`facts`,
    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`); `and`
    has no law, so that is every H (`openLaws_any`, `consistent_any`).
    `lawHooks c H` is admitted by the library's sentences wherever H is (`libAdmitted_lawHooks`), so
    `lawHooks c HookParams.lib` satisfies the laws, the open generators' `functional` sentences and
    the library's sentences together (`lawHooks_lib`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (1): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (29): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (51): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); open generator
    functional: owed as `OpenTotal` (`open_functional_not_item`); no direction: `absent_closed`.

  Exp's no junk (99) is entailed (`nojunk_exp_entailed`): its item lists Exp's generators, `and`
  among them, in another order than `Semantics.gens`. `and`'s functional sentence (65) is no item of
  Γ and is owed at values as `OpenTotal` (`open_functional_not_item`); the account holds it in `open
  generator functional`, of the direction `hypothesis`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (44);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2OpenRule

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/openrule.kompile.kore"
definition_of defn from "f2-examples/openrule.kompile.kore"
user_axioms U from "f2-examples/openrule.kompile.kore" module "E2-OPEN-RULE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `and`, the text's one open generator (`raw`), and Exp, its sort. -/
def and : Sym := 389
def exp : Srt := 32

theorem names : c.symName and = "Lbland" ∧ c.sortName exp = "Exp" := by decide +kernel

/-- **The definition's one open generator is `and`**, of Exp, `assoc` false and `idem` false. -/
theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =
    [(and, [exp, exp], exp, false, false)] := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-OPEN-RULE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 203 := by decide +kernel

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
  [("function equation", [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174,
      175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 205]),
   ("rewrite rule", [125]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 66, 86, 87, 95, 97]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29]),
   ("distinctness", [96]),
   ("no junk", [98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]),
   ("function functional", [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 38, 39, 40, 41, 42, 46, 54, 55, 56, 57, 58, 59, 60, 61,
      62, 63, 64, 68, 85, 88, 89, 90, 91, 92, 93]),
   ("collection law", [43, 44, 45, 47, 48, 49, 50, 52, 53]),
   ("library", [109, 110, 111, 112, 117, 118, 121, 122, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
      136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 188,
      189, 204]),
   ("set idempotence", [51]),
   ("set-variable lemma", [113, 114, 115, 116, 119, 120, 123, 124, 206]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", [65]),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 37, 67, 84, 94, 153, 154, 155, 156, 186, 187, 190, 191, 192, 193, 194, 195, 196, 197,
      198, 199, 200, 201, 202, 203])]

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
    [("function equation", 30), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 9), ("subsort", 15), ("injectivity", 4), ("distinctness", 1), ("no junk", 11), ("function functional", 15), ("hooked functional", 34), ("collection law", 9), ("library", 38), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 1), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 25)] := by
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
  [(190, "Bool"), (191, "Exp"), (192, "GeneratedCounterCell"), (193, "GeneratedCounterCellOpt"),
   (194, "GeneratedTopCell"), (195, "GeneratedTopCellFragment"), (196, "Int"), (197, "K"),
   (198, "KCell"), (199, "KCellOpt"), (200, "KItem"), (201, "List"), (202, "Map"), (203, "Set")]

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
  [(14, "subsort"), (65, "open generator functional"), (66, "constructor functional"),
   (70, "function functional"), (95, "constructor functional"), (96, "distinctness"),
   (97, "constructor functional"), (99, "no junk"), (108, "no junk"), (109, "library"),
   (110, "library"), (111, "library"), (112, "library"), (113, "set-variable lemma"),
   (114, "set-variable lemma"), (115, "set-variable lemma"), (116, "set-variable lemma"),
   (117, "library"), (118, "library"), (119, "set-variable lemma"), (120, "set-variable lemma"),
   (121, "library"), (122, "library"), (123, "set-variable lemma"), (124, "set-variable lemma"),
   (125, "rewrite rule"), (128, "library"), (130, "library"), (131, "library"), (134, "library"),
   (135, "library"), (137, "library"), (138, "library"), (141, "library"), (142, "library"),
   (145, "library"), (146, "library"), (150, "library"), (156, "no direction"),
   (159, "function equation"), (160, "function equation"), (191, "no direction"),
   (205, "function equation"), (206, "set-variable lemma")]

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

theorem sig_sizes : (sigItems c).length = 210 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 102, 71, 5, 26) := by
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

/-! ## Consistency for every H satisfying the open generator's laws -/

def callOrder : List Nat := [
388]

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

/-- **`lawHooks c H` satisfies the laws and gives `and` a value at every pair of Exp values**,
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

/-! ## Function equations (30 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 30 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax205, U.ax171, U.ax179, U.ax178, U.ax177, U.ax176, U.ax183, U.ax182, U.ax185, U.ax184,
   U.ax181, U.ax180, U.ax158, U.ax157, U.ax170, U.ax169, U.ax166, U.ax165, U.ax168, U.ax167,
   U.ax173, U.ax172, U.ax175, U.ax174, U.ax162, U.ax161, U.ax164, U.ax163, U.ax160, U.ax159]

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

/-! ## The rules (1 sentences): W1 -/

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

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax125]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

theorem rule0_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule0_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule0_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 0 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 125. -/
theorem rule0_text : (trS U.ax125).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel
/-- **W1 for rule 0**: Γ's item is a consequence of sentence 125. -/
theorem rule0_from_text : itemsPremises [trS U.ax125] ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule0_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule0_table rule0_free ?_
  rw [← rule0_text]
  exact hI _ (Or.inl ⟨trS U.ax125, List.mem_singleton_self _, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl
  · exact ⟨U.ax125, List.mem_cons_self, rule0_from_text⟩

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

theorem nj98 : (trS U.ax98).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj104 : (trS U.ax104).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj107 : (trS U.ax107).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax98, U.ax104, U.ax107], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj98]; exact orTopBot_valid hD rfl
  · rw [nj104]; exact orTopBot_valid hD rfl
  · rw [nj107]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax100, U.ax101, U.ax102, U.ax103, U.ax105, U.ax106],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax100, U.ax101, U.ax102, U.ax103, U.ax105, U.ax106],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax108).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (108)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax108).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- Exp's generators in the order the text's no-junk sentence (99) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def expTextGens : List KoreAML.Gen :=
  match (c.gens exp).map (Gen.toK c) with
  | [g0, g1, g2] => [g2, g0, g1]
  | gs => gs

/-- Exp's no-junk sentence (99) is the item over Exp's generators in the text's order. -/
theorem nojunk_exp_order : (trS U.ax99).pat = (KoreAML.Cons.noJunkItem (c.sortName exp) expTextGens).pat := by
  decide +kernel
theorem nojunk_exp_members : expTextGens.isPerm ((c.gens exp).map (Gen.toK c)) = true := by
  decide +kernel
theorem nojunk_exp_and : ((c.gens exp).map (Gen.toK c)).length = 3 ∧ c.isOpenGen (.ctor ⟨and, [exp, exp], exp⟩) = true := by
  decide +kernel

/-- **E for Exp's no junk (99)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_exp_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax99).pat := by
  intro M _ I hI
  rw [nojunk_exp_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens exp).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_exp_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := exp)
    (show exp ∈ consSorts c by decide +kernel) (show (c.gens exp).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax66,
   U.ax86, U.ax87, U.ax95, U.ax96, U.ax97]

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

theorem idem_pattern : U.ax51.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax51).pat = (trAxiom [] [] U.ax51).pat := by decide +kernel

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
theorem idem_vars : (U.ax51.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax51.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax51.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 51 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax51).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax51.ax.sortVars U.ax51.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax51.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax51.ax.pattern).eraseDups,
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


/-! ## The functional sentence of `and` (65): owed as `OpenTotal` -/

/-- **Γ holds no item for `and`'s functional sentence**: the constructors' items state the
functionality of the generators that are no open generator only. The sentence is owed, at values,
as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : !(consItemsK c).any (·.pat == (trS U.ax65).pat) &&
    !(fnItems c).any (·.pat == (trS U.ax65).pat) &&
    (classOf "open generator functional" == [65]) = true := by
  decide +kernel

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

end KCore.TieE2OpenRule

#check @KCore.TieE2OpenRule.params_raw
#check @KCore.TieE2OpenRule.readsConfined_c
#check @KCore.TieE2OpenRule.userAxioms_eq
#check @KCore.TieE2OpenRule.coreOK
#check @KCore.TieE2OpenRule.wf_defn
#check @KCore.TieE2OpenRule.account
#check @KCore.TieE2OpenRule.account_sizes
#check @KCore.TieE2OpenRule.account_classes
#check @KCore.TieE2OpenRule.account_absent
#check @KCore.TieE2OpenRule.absent_closed
#check @KCore.TieE2OpenRule.absent_proj_below_c
#check @KCore.TieE2OpenRule.absent_proj_below
#check @KCore.TieE2OpenRule.lists_in_account
#check @KCore.TieE2OpenRule.attrs_agree
#check @KCore.TieE2OpenRule.sig_origin
#check @KCore.TieE2OpenRule.decls_entailed
#check @KCore.TieE2OpenRule.consistent
#check @KCore.TieE2OpenRule.fnFun_indices
#check @KCore.TieE2OpenRule.fnFun_account
#check @KCore.TieE2OpenRule.fnFun_checked
#check @KCore.TieE2OpenRule.fnFun_trS
#check @KCore.TieE2OpenRule.fnFun_at_values
#check @KCore.TieE2OpenRule.fnFun_at_values_step
#check @KCore.TieE2OpenRule.fn_shape
#check @KCore.TieE2OpenRule.fns_account
#check @KCore.TieE2OpenRule.fns_entailed
#check @KCore.TieE2OpenRule.fns_from_text
#check @KCore.TieE2OpenRule.fn_prios
#check @KCore.TieE2OpenRule.nojunk_trivial_entailed
#check @KCore.TieE2OpenRule.nojunk_items_entailed
#check @KCore.TieE2OpenRule.nojunk_kitem_entailed
#check @KCore.TieE2OpenRule.cons_entailed
#check @KCore.TieE2OpenRule.rules_account
#check @KCore.TieE2OpenRule.rule_from_text
#check @KCore.TieE2OpenRule.idem_refuted
#check @KCore.TieE2OpenRule.gamma_origin
#check @KCore.TieE2OpenRule.gamma_from
#check @KCore.TieE2OpenRule.names
#check @KCore.TieE2OpenRule.facts
#check @KCore.TieE2OpenRule.lawHooks_laws
#check @KCore.TieE2OpenRule.consistent_lawHooks
#check @KCore.TieE2OpenRule.libAdmitted_lawHooks
#check @KCore.TieE2OpenRule.lawHooks_lib
#check @KCore.TieE2OpenRule.openLaws_any
#check @KCore.TieE2OpenRule.consistent_any
#check @KCore.TieE2OpenRule.nojunk_exp_order
#check @KCore.TieE2OpenRule.nojunk_exp_members
#check @KCore.TieE2OpenRule.nojunk_exp_and
#check @KCore.TieE2OpenRule.nojunk_exp_entailed
#check @KCore.TieE2OpenRule.open_functional_not_item
#print axioms KCore.TieE2OpenRule.params_raw
#print axioms KCore.TieE2OpenRule.readsConfined_c
#print axioms KCore.TieE2OpenRule.userAxioms_eq
#print axioms KCore.TieE2OpenRule.coreOK
#print axioms KCore.TieE2OpenRule.wf_defn
#print axioms KCore.TieE2OpenRule.account
#print axioms KCore.TieE2OpenRule.account_sizes
#print axioms KCore.TieE2OpenRule.account_classes
#print axioms KCore.TieE2OpenRule.account_absent
#print axioms KCore.TieE2OpenRule.absent_closed
#print axioms KCore.TieE2OpenRule.absent_proj_below_c
#print axioms KCore.TieE2OpenRule.absent_proj_below
#print axioms KCore.TieE2OpenRule.lists_in_account
#print axioms KCore.TieE2OpenRule.attrs_agree
#print axioms KCore.TieE2OpenRule.sig_origin
#print axioms KCore.TieE2OpenRule.decls_entailed
#print axioms KCore.TieE2OpenRule.consistent
#print axioms KCore.TieE2OpenRule.fnFun_indices
#print axioms KCore.TieE2OpenRule.fnFun_account
#print axioms KCore.TieE2OpenRule.fnFun_checked
#print axioms KCore.TieE2OpenRule.fnFun_trS
#print axioms KCore.TieE2OpenRule.fnFun_at_values
#print axioms KCore.TieE2OpenRule.fnFun_at_values_step
#print axioms KCore.TieE2OpenRule.fn_shape
#print axioms KCore.TieE2OpenRule.fns_account
#print axioms KCore.TieE2OpenRule.fns_entailed
#print axioms KCore.TieE2OpenRule.fns_from_text
#print axioms KCore.TieE2OpenRule.fn_prios
#print axioms KCore.TieE2OpenRule.nojunk_trivial_entailed
#print axioms KCore.TieE2OpenRule.nojunk_items_entailed
#print axioms KCore.TieE2OpenRule.nojunk_kitem_entailed
#print axioms KCore.TieE2OpenRule.cons_entailed
#print axioms KCore.TieE2OpenRule.rules_account
#print axioms KCore.TieE2OpenRule.rule_from_text
#print axioms KCore.TieE2OpenRule.idem_refuted
#print axioms KCore.TieE2OpenRule.gamma_origin
#print axioms KCore.TieE2OpenRule.gamma_from
#print axioms KCore.TieE2OpenRule.names
#print axioms KCore.TieE2OpenRule.facts
#print axioms KCore.TieE2OpenRule.lawHooks_laws
#print axioms KCore.TieE2OpenRule.consistent_lawHooks
#print axioms KCore.TieE2OpenRule.libAdmitted_lawHooks
#print axioms KCore.TieE2OpenRule.lawHooks_lib
#print axioms KCore.TieE2OpenRule.openLaws_any
#print axioms KCore.TieE2OpenRule.consistent_any
#print axioms KCore.TieE2OpenRule.nojunk_exp_order
#print axioms KCore.TieE2OpenRule.nojunk_exp_members
#print axioms KCore.TieE2OpenRule.nojunk_exp_and
#print axioms KCore.TieE2OpenRule.nojunk_exp_entailed
#print axioms KCore.TieE2OpenRule.open_functional_not_item
