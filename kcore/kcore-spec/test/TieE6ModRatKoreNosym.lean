/-
  The tie (C14) on `f2-examples/e6-mod-rat-kore-nosym.kompile.kore`, the kompiled text of construct fixture e6-mod-rat-kore-nosym
  (`test/constructs/fixtures/e6-mod-rat-kore-nosym`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e6-mod-rat-kore-nosym`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE6ModRatKoreNosym.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 222 sentences of the user module E6-MOD-RAT-KORE-NOSYM, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 222 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the totality of the `[total]` function `_*Rat_` and `_+Rat_` and `_-Rat_` and `_<=Rat_` and
    `_<Rat_` and `_>=Rat_` and `_>Rat_` and `_^Rat_` and `maxRat` and `minRat` (`total_named`), which no
    decider confirms. The consistency section, written by hand, proves that Γ with the step's closure
    has a model for every H (`consistent`), without `FnHyp`, which it does not state (its comment says
    why): the function functional sentences, owed as `FnHyp`, are not shown by this tie where `FnHyp`
    fails.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (33): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (1): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (31): entailed by Γ (`cons_entailed`).
  - No junk (4 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (64): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (not stated here; no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (63);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ModRatKoreNosym

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-mod-rat-kore-nosym.kompile.kore"
definition_of defn from "f2-examples/e6-mod-rat-kore-nosym.kompile.kore"
user_axioms U from "f2-examples/e6-mod-rat-kore-nosym.kompile.kore" module "E6-MOD-RAT-KORE-NOSYM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E6-MOD-RAT-KORE-NOSYM")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 222 := by decide +kernel

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
  [("function equation", [143, 145, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189,
      190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]),
   ("rewrite rule", [140]),
   ("priority equation", []),
   ("constructor functional", [24, 26, 28, 30, 32, 79, 103, 104]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]),
   ("injectivity", [25, 27, 29, 31, 33, 80]),
   ("distinctness", []),
   ("no junk", [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]),
   ("function functional", [40, 41, 43, 45, 47, 50, 53, 54, 55, 68, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
      96, 97, 98, 101, 102]),
   ("hooked functional", [21, 22, 23, 34, 35, 36, 37, 38, 39, 46, 48, 49, 51, 52, 59, 67, 69, 70, 71, 72, 73, 74, 75,
      76, 77, 78, 82, 100, 105, 106, 107, 108, 109, 110]),
   ("collection law", [56, 57, 58, 60, 61, 62, 63, 65, 66]),
   ("library", [124, 125, 126, 127, 132, 133, 136, 137, 141, 142, 144, 146, 147, 148, 149, 150, 151, 152,
      153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 207,
      208, 224]),
   ("set idempotence", [64]),
   ("set-variable lemma", [128, 129, 130, 131, 134, 135, 138, 139, 225]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [42, 44, 81, 99, 111, 170, 171, 172, 173, 205, 206, 209, 210, 211, 212, 213, 214, 215, 216,
      217, 218, 219, 220, 221, 222, 223])]

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
    [("function equation", 33), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 8), ("subsort", 17), ("injectivity", 6), ("distinctness", 0), ("no junk", 12), ("function functional", 28), ("hooked functional", 34), ("collection law", 9), ("library", 38), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 26)] := by
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
  [(209, "Bool"), (210, "Float"), (211, "GeneratedCounterCell"), (212, "GeneratedCounterCellOpt"),
   (213, "GeneratedTopCell"), (214, "GeneratedTopCellFragment"), (215, "Int"), (216, "K"),
   (217, "KCell"), (218, "KCellOpt"), (219, "KItem"), (220, "List"), (221, "Map"), (222, "Rat"),
   (223, "Set")]

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
  [(15, "subsort"), (18, "subsort"), (19, "subsort"), (24, "constructor functional"),
   (25, "injectivity"), (40, "function functional"), (41, "function functional"),
   (43, "function functional"), (45, "function functional"), (47, "function functional"),
   (50, "function functional"), (53, "function functional"), (54, "function functional"),
   (55, "function functional"), (68, "function functional"), (79, "constructor functional"),
   (80, "injectivity"), (84, "function functional"), (97, "function functional"),
   (101, "function functional"), (102, "function functional"), (113, "no junk"), (122, "no junk"),
   (123, "no junk"), (124, "library"), (125, "library"), (126, "library"), (127, "library"),
   (128, "set-variable lemma"), (129, "set-variable lemma"), (130, "set-variable lemma"),
   (131, "set-variable lemma"), (132, "library"), (133, "library"), (134, "set-variable lemma"),
   (135, "set-variable lemma"), (136, "library"), (137, "library"), (138, "set-variable lemma"),
   (139, "set-variable lemma"), (140, "rewrite rule"), (143, "function equation"),
   (144, "library"), (145, "function equation"), (147, "library"), (148, "library"),
   (151, "library"), (152, "library"), (154, "library"), (155, "library"), (158, "library"),
   (159, "library"), (162, "library"), (163, "library"), (167, "library"), (173, "no direction"),
   (176, "function equation"), (177, "function equation"), (201, "function equation"),
   (202, "function equation"), (210, "no direction"), (222, "no direction"),
   (225, "set-variable lemma")]

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
theorem sigE_203 : (((sigItems c).drop 203).take 13).all sigFrom = true := by decide +kernel
theorem sigE_216 : ((sigItems c).drop 216).all sigFrom = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 222 := by decide +kernel

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
    tieAllE_range (a := 203) (n := 13) sigE_203 <|
    sigE_216

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 115, 83, 5, 27) := by
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

/-- The symbol declarations of the text with a K builtin file's `Source`, without a `hook`
attribute and without sort parameters, that Γ has, by name. -/
def builtinDeclNames : List String :=
  ["Lbl'-LT-UndsCommUnds-GT-'Rat'Unds'RAT-COMMON'Unds'Rat'Unds'Int'Unds'Int",
   "Lbl'-LT-'k'-GT-'",
   "LblRat2Float'LParUndsCommUndsCommUndsRParUnds'RAT-SYNTAX'Unds'Float'Unds'Rat'Unds'Int'Unds'Int",
   "Lbl'UndsStar'Rat'Unds'",
   "Lbl'UndsPlus'Rat'Unds'",
   "Lbl'Unds'-Rat'Unds'",
   "Lbl'UndsSlsh'Rat'Unds'",
   "Lbl'Unds-LT-Eqls'Rat'Unds'",
   "Lbl'Unds-LT-'Rat'Unds'",
   "Lbl'UndsEqlsSlshEqls'Rat'Unds'",
   "Lbl'UndsEqlsEqls'Rat'Unds'",
   "Lbl'Unds-GT-Eqls'Rat'Unds'",
   "Lbl'Unds-GT-'Rat'Unds'",
   "Lbl'UndsXor-'Rat'Unds'",
   "LblmaxRat",
   "LblminRat"]

/-- Each names a symbol of Γ. -/
theorem builtinDeclNames_has : builtinDeclNames.all hasSym = true := by decide +kernel

/-- **E for the symbol declarations named in `builtinDeclNames`**: Γ entails the G-arity item
of each such declaration without sort parameters, for every H. -/
theorem builtin_decls_entailed (H : HookParams) :
    ∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ builtinDeclNames → Γ (cH H) ⊧ (arityItem sd).pat :=
  fun sd hsd hp hn => decls_entailed H _ (List.mem_append_right _ (List.mem_map_of_mem
    (List.mem_filter.mpr ⟨hsd, by
      simp only [hp, List.isEmpty_nil, Bool.true_and]; exact List.all_eq_true.mp builtinDeclNames_has _ hn⟩)))

/-! ## Consistency for every H: the totality of ten functions without an equation -/

/- The ten `[total]` functions `total_named` names (`_*Rat_`, `_+Rat_`, `_-Rat_`, `_<=Rat_`,
`_<Rat_`, `_>=Rat_`, `_>Rat_`, `_^Rat_`, `maxRat`, `minRat`) have no equation in the text: the
module stating them (RAT) is not imported. Each has, at every argument list of its sorts, its rest
(`Eval.rest`): the interpretation's value there (`Semantics.fnRest`), so its totality holds exactly
under the H that give it a value of its result sort at every such list. Under `HookParams.none`
`_+Rat_` has no value at `(0, 0)` (`plusRat_undefined_none`), so its totality fails there
(`not_total_none`) and so does `FnHyp` (`not_fnHyp_none`): the totality is a hypothesis on H.
Γ holds no functional axiom of a function, and the model `consistent_of` builds reads no totality:
every function has a result (the rank names no termination fact, `term_named`; no function is
held-named, `held_none`), the equations agree and each clause is match independent (`agree_named`,
`match_named`), so a function has one result at each argument list (`FnDet`) and evaluation solves
the equations (`FnSolves`); every clause's predicate has a truth value where it is read, and there
is no open generator. So Γ with the step's closure has a model for every H (`consistent`). -/

def callOrder : List Nat := [387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [387, 388, 389, 390, 391, 394, 395, 396, 397, 398] := by
  decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem held_none : c.heldObligations = [] := by decide +kernel

theorem consistent (H : HookParams) : Consistent (cH H) := by
  have h := coreOKH H
  have hnoEx : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))
  have hpreTop : (cH H).clausesPreTop = true := by simp only [Semantics.clausesPreTop_withHooks]; decide +kernel
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hheld : ∀ f ∈ (cH H).heldObligations, HeldOwed (cH H) f := by
    rw [Semantics.heldObligations_withHooks, held_none]; intro f hf; cases hf
  have hterm := terminates_of_rankLN hpreTop hnoEx hok hsr (Semantics.ovlCase_of_core h) callOrder hheld
    (fun g hg => by
      rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg
      cases hg)
  have hmc : Exec.MatchCtxO (cH H) := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩
  have hag := Det.clausesAgree_of_IO hok hnoEx hsr hmc (fun g hg => by
    rw [Det.Semantics.agreeObligationsI_withHooks _ H, agree_named] at hg; cases hg)
  have hmi := Det.matchIndependentAll_of_L hok hnoEx hmc (fun p hp => by
    rw [Det.Semantics.matchObligationsL_withHooks _ H, match_named] at hp; cases hp)
  have hco : CoherentAll (cH H) := coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp
  have hd := fnDet_of_coherent hco
  have hft : FnTerminates (cH H) := fun fn hfn vs hvs => hterm fn.label fn (lookupFn_of_core h hfn) vs hvs
  exact consistent_of (cH H) h hd
    (Faithful.Model.fnSolves_of_total (hypSound_of_core h) hd hft
      fun fn hfn cl hcl hne vs σ hdec =>
        (hmi fn.label fn (lookupFn_of_core h hfn) cl hcl).2 hne fn.label fn vs σ (lookupFn_of_core h hfn) hcl hdec)
    (Faithful.Model.clausePreDecided_of_terminates (hypSound_of_core h) hft)
    (clausePostDecided_of_top fun _ hfn _ hcl =>
      (Semantics.sortedOK_clauseEx (Semantics.coreOK_parts h).1 hfn hcl).2 (hnoEx _ hfn _ hcl))
    (openLaws_of_plain fun k hk => noRaw k hk)


/-- `_+Rat_`, one of the ten. -/
def plusRat : Sym := 388

theorem plusRat_named : c.symName plusRat = "Lbl'UndsPlus'Rat'Unds'" := by decide +kernel

theorem plusRat_lookup : (c.lookupFn plusRat).isSome = true := by decide +kernel

noncomputable def fnPlus : Fn := (c.lookupFn plusRat).get plusRat_lookup

theorem fnPlus_lookup (H : HookParams) : (cH H).lookupFn plusRat = some fnPlus := by
  rw [Semantics.lookupFn_withHooks]; exact (Option.some_get plusRat_lookup).symm

theorem fnPlus_shape : fnPlus.clauses = [] ∧ fnPlus.total = true ∧
    c.sortsOf [.inj Srt.int 32 (int 0), .inj Srt.int 32 (int 0)] = some fnPlus.args := by decide +kernel

/-- **Under `HookParams.none`, `_+Rat_` has no value at `(0, 0)`**: it has no equation, so its one
result is its rest, which that interpretation leaves undefined. -/
theorem plusRat_undefined_none (r : Option GroundTerm)
    (h : Eval (cH HookParams.none) plusRat [.inj Srt.int 32 (int 0), .inj Srt.int 32 (int 0)] r) : r = none := by
  have hno : ∀ {fn : Fn} {cl : Clause}, (cH HookParams.none).lookupFn plusRat = some fn →
      cl ∈ fn.clauses → False := fun hfn hmem => by
    rw [fnPlus_lookup, Option.some.injEq] at hfn; subst hfn
    rw [fnPlus_shape.1] at hmem; exact List.not_mem_nil hmem
  cases h with
  | @clauseEx _ fn' _ cl' σ' _ hfn' hmem _ _ _ _ _ _ _ _ _ => exact (hno hfn' hmem).elim
  | @exNone _ fn' _ cl' σ' hfn' hmem _ _ _ _ _ _ _ _ => exact (hno hfn' hmem).elim
  | @clause _ fn' _ cl' σ' _ hfn' hmem _ _ _ _ _ _ _ _ _ => exact (hno hfn' hmem).elim
  | @rest _ fn' _ hfn' _ => rfl
  | @ensFails _ fn' _ cl' σ' t w hfn' hmem _ _ _ _ _ _ _ _ _ => exact (hno hfn' hmem).elim

/-- **The totality `total_named` names is a hypothesis on H**: `_+Rat_` is not total under
`HookParams.none`, so `FnHyp` fails there. -/
theorem not_total_none : ¬ Total (cH HookParams.none) plusRat := fun ht => by
  obtain ⟨v, hv⟩ := ht fnPlus (fnPlus_lookup _) _ (by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact fnPlus_shape.2.2)
  cases plusRat_undefined_none _ hv

theorem not_fnHyp_none : ¬ FnHyp (cH HookParams.none) := fun hf =>
  not_total_none fun fn hfn vs hvs => by
    rw [fnPlus_lookup, Option.some.injEq] at hfn; subst hfn
    exact hf.2.1 fnPlus (by
      obtain ⟨hmem, hlab⟩ := lookupFn_spec (fnPlus_lookup HookParams.none)
      rcases List.mem_append.mp hmem with hu | hp
      · exact hu
      · have := List.all_eq_true.mp
          (by decide +kernel : (cH HookParams.none).sortPreds.all (·.label != plusRat) = true) _ hp
        rw [hlab] at this; simp at this) fnPlus_shape.2.1 vs hvs

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (33 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 33 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax143, U.ax145, U.ax188, U.ax196, U.ax195, U.ax194, U.ax193, U.ax200, U.ax199, U.ax204,
   U.ax203, U.ax198, U.ax197, U.ax175, U.ax174, U.ax187, U.ax186, U.ax177, U.ax176, U.ax183,
   U.ax182, U.ax185, U.ax184, U.ax190, U.ax189, U.ax192, U.ax191, U.ax179, U.ax178, U.ax181,
   U.ax180, U.ax202, U.ax201]

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
  [U.ax140]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

theorem rule0_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule0_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule0_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 0 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 140. -/
theorem rule0_text : (trS U.ax140).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel
/-- **W1 for rule 0**: Γ's item is a consequence of sentence 140. -/
theorem rule0_from_text : itemsPremises [trS U.ax140] ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule0_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule0_table rule0_free ?_
  rw [← rule0_text]
  exact hI _ (Or.inl ⟨trS U.ax140, List.mem_singleton_self _, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl
  · exact ⟨U.ax140, List.mem_cons_self, rule0_from_text⟩

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

theorem nj112 : (trS U.ax112).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj113 : (trS U.ax113).pat = orTopBot (sym (.sort "SortFloat")) := by decide +kernel
theorem nj118 : (trS U.ax118).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj121 : (trS U.ax121).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax112, U.ax113, U.ax118, U.ax121], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl
  · rw [nj112]; exact orTopBot_valid hD rfl
  · rw [nj113]; exact orTopBot_valid hD rfl
  · rw [nj118]; exact orTopBot_valid hD rfl
  · rw [nj121]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax114, U.ax115, U.ax116, U.ax117, U.ax119, U.ax120, U.ax123],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax114, U.ax115, U.ax116, U.ax117, U.ax119, U.ax120, U.ax123],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax122).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (122)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax122).pat := by
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
   U.ax31, U.ax32, U.ax33, U.ax79, U.ax80, U.ax103, U.ax104]

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

theorem idem_pattern : U.ax64.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax64).pat = (trAxiom [] [] U.ax64).pat := by decide +kernel

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
theorem idem_vars : (U.ax64.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax64.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax64.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 64 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax64).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax64.ax.sortVars U.ax64.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax64.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax64.ax.pattern).eraseDups,
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

end KCore.TieE6ModRatKoreNosym

#check @KCore.TieE6ModRatKoreNosym.noRaw
#check @KCore.TieE6ModRatKoreNosym.readsConfined_c
#check @KCore.TieE6ModRatKoreNosym.userAxioms_eq
#check @KCore.TieE6ModRatKoreNosym.coreOK
#check @KCore.TieE6ModRatKoreNosym.wf_defn
#check @KCore.TieE6ModRatKoreNosym.account
#check @KCore.TieE6ModRatKoreNosym.account_sizes
#check @KCore.TieE6ModRatKoreNosym.account_classes
#check @KCore.TieE6ModRatKoreNosym.account_absent
#check @KCore.TieE6ModRatKoreNosym.absent_closed
#check @KCore.TieE6ModRatKoreNosym.absent_proj_below_c
#check @KCore.TieE6ModRatKoreNosym.absent_proj_below
#check @KCore.TieE6ModRatKoreNosym.lists_in_account
#check @KCore.TieE6ModRatKoreNosym.attrs_agree
#check @KCore.TieE6ModRatKoreNosym.sig_origin
#check @KCore.TieE6ModRatKoreNosym.decls_entailed
#check @KCore.TieE6ModRatKoreNosym.consistent
#check @KCore.TieE6ModRatKoreNosym.total_named
#check @KCore.TieE6ModRatKoreNosym.builtin_decls_entailed
#check @KCore.TieE6ModRatKoreNosym.fn_shape
#check @KCore.TieE6ModRatKoreNosym.fns_account
#check @KCore.TieE6ModRatKoreNosym.fns_entailed
#check @KCore.TieE6ModRatKoreNosym.fns_from_text
#check @KCore.TieE6ModRatKoreNosym.fn_prios
#check @KCore.TieE6ModRatKoreNosym.nojunk_trivial_entailed
#check @KCore.TieE6ModRatKoreNosym.nojunk_items_entailed
#check @KCore.TieE6ModRatKoreNosym.nojunk_kitem_entailed
#check @KCore.TieE6ModRatKoreNosym.cons_entailed
#check @KCore.TieE6ModRatKoreNosym.rules_account
#check @KCore.TieE6ModRatKoreNosym.rule_from_text
#check @KCore.TieE6ModRatKoreNosym.idem_refuted
#check @KCore.TieE6ModRatKoreNosym.gamma_origin
#check @KCore.TieE6ModRatKoreNosym.gamma_from
#print axioms KCore.TieE6ModRatKoreNosym.noRaw
#print axioms KCore.TieE6ModRatKoreNosym.readsConfined_c
#print axioms KCore.TieE6ModRatKoreNosym.userAxioms_eq
#print axioms KCore.TieE6ModRatKoreNosym.coreOK
#print axioms KCore.TieE6ModRatKoreNosym.wf_defn
#print axioms KCore.TieE6ModRatKoreNosym.account
#print axioms KCore.TieE6ModRatKoreNosym.account_sizes
#print axioms KCore.TieE6ModRatKoreNosym.account_classes
#print axioms KCore.TieE6ModRatKoreNosym.account_absent
#print axioms KCore.TieE6ModRatKoreNosym.absent_closed
#print axioms KCore.TieE6ModRatKoreNosym.absent_proj_below_c
#print axioms KCore.TieE6ModRatKoreNosym.absent_proj_below
#print axioms KCore.TieE6ModRatKoreNosym.lists_in_account
#print axioms KCore.TieE6ModRatKoreNosym.attrs_agree
#print axioms KCore.TieE6ModRatKoreNosym.sig_origin
#print axioms KCore.TieE6ModRatKoreNosym.decls_entailed
#print axioms KCore.TieE6ModRatKoreNosym.consistent
#print axioms KCore.TieE6ModRatKoreNosym.total_named
#print axioms KCore.TieE6ModRatKoreNosym.builtin_decls_entailed
#print axioms KCore.TieE6ModRatKoreNosym.fn_shape
#print axioms KCore.TieE6ModRatKoreNosym.fns_account
#print axioms KCore.TieE6ModRatKoreNosym.fns_entailed
#print axioms KCore.TieE6ModRatKoreNosym.fns_from_text
#print axioms KCore.TieE6ModRatKoreNosym.fn_prios
#print axioms KCore.TieE6ModRatKoreNosym.nojunk_trivial_entailed
#print axioms KCore.TieE6ModRatKoreNosym.nojunk_items_entailed
#print axioms KCore.TieE6ModRatKoreNosym.nojunk_kitem_entailed
#print axioms KCore.TieE6ModRatKoreNosym.cons_entailed
#print axioms KCore.TieE6ModRatKoreNosym.rules_account
#print axioms KCore.TieE6ModRatKoreNosym.rule_from_text
#print axioms KCore.TieE6ModRatKoreNosym.idem_refuted
#print axioms KCore.TieE6ModRatKoreNosym.gamma_origin
#print axioms KCore.TieE6ModRatKoreNosym.gamma_from
