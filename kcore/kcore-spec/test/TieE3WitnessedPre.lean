/-
  The tie (C14) on `f2-examples/e3-witnessed-pre.kompile.kore`, the kompiled text of construct fixture e3-witnessed-pre
  (`test/constructs/fixtures/e3-witnessed-pre`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-witnessed-pre`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3WitnessedPre.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate (`wfFailing`).
  - The account: the class lists partition the 275 sentences of the user module E3-WITNESSED-PRE, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 213 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the match independence of a clause (`match_named`); the condition of a rule or clause
    (`owed_rules`, `owed_clauses`); `FnHyp` itself: a clause's predicate is not `\top`
    (`Semantics.clausesPreTop` false), so the named facts do not give it and `kcore gen --core` takes it
    as the hypothesis of its statements, which no decider confirms. The consistency section, written by
    hand, proves that `Γc` with the step's closure has a model for every H (`consistent`), through
    `FnHyp` for every H (`fnHypH`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (35) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (215) is the equation whose premise Γ writes through a cut
    of the clause's `requires` (`andUnderAppCut`, `notAsCondition`): each sentence is its item with
    the premise as the text writes it (`cut<j>_same`, `TieCutEq.textItem`, up to the names of its
    variables). Item 0: the sentence gives the item in every model of definedness
    (`cut0_from_text`), and Γc entails the sentence (`cut0_entailed`, its models having the
    constructors' facts). `fns_from_text` (the converse), `fn_prios` (the priorities the sentences
    state are the clauses').
  - Rewrite rules (1): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (34): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (62): Γ with it has no model (`idem_refuted`).
  - Library sample, 172 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences (215
    through `cut0_from_text`), Γ's rule items, the five parts Γ defines by predicates, or
    definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.
  - `f(0) = 1`, by hand, for every H: `Eval` gives it by the clause at H := d (`wpEval_f0`), every
    model of `Γc` reads it (`wpF0_c`, the clause's owed condition by `openDecidedH`), and it is
    derived from the function sentences (215 through Γ's item, `cut0_from_text`), Γ's rule item,
    the families of the reading and `Γcl` (`wpPre`, `wpF0_is_1`), premises that have a model with
    the step's closure (`wpPre_model`).

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (32);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3WitnessedPre

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-witnessed-pre.kompile.kore"
definition_of defn from "f2-examples/e3-witnessed-pre.kompile.kore"
user_axioms U from "f2-examples/e3-witnessed-pre.kompile.kore" module "E3-WITNESSED-PRE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-WITNESSED-PRE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 275 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The conjuncts of `wf` that fail on this text (`kcore account`); `coreOK` holds. -/
def wfFailing : List String := ["clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate"]

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [215, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237,
      238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]),
   ("rewrite rule", [161]),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 78, 82, 85, 87, 111, 112]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30, 83]),
   ("distinctness", [79, 80, 84]),
   ("no junk", [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]),
   ("function functional", [90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      57, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 77, 81, 86, 89, 108, 109, 110, 113, 114, 115,
      116, 117, 118]),
   ("collection law", [54, 55, 56, 58, 59, 60, 61, 63, 64]),
   ("library", [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
      155, 156, 157, 158, 159, 160, 162, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174,
      175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
      193, 194, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
      212, 213, 214, 216, 257, 258, 259, 260, 276, 277]),
   ("set idempotence", [62]),
   ("set-variable lemma", [132, 133, 134, 135, 136, 278]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [37, 41, 43, 74, 76, 88, 107, 119, 120, 163, 195, 217, 218, 219, 220, 255, 256, 261, 262, 263,
      264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275])]

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
    [("function equation", 35), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 10), ("subsort", 16), ("injectivity", 5), ("distinctness", 3), ("no junk", 11), ("function functional", 17), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 32)] := by
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
  [(261, "Bool"), (262, "Empty"), (263, "GeneratedCounterCell"), (264, "GeneratedCounterCellOpt"),
   (265, "GeneratedTopCell"), (266, "GeneratedTopCellFragment"), (267, "Int"), (268, "K"),
   (269, "KCell"), (270, "KCellOpt"), (271, "KItem"), (272, "List"), (273, "Map"), (274, "S"),
   (275, "Set")]

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
  [(14, "subsort"), (18, "subsort"), (78, "constructor functional"), (79, "distinctness"),
   (80, "distinctness"), (82, "constructor functional"), (83, "injectivity"), (84, "distinctness"),
   (85, "constructor functional"), (87, "constructor functional"), (91, "function functional"),
   (92, "function functional"), (105, "function functional"), (130, "no junk"), (131, "no junk"),
   (161, "rewrite rule"), (215, "function equation"), (220, "no direction"),
   (223, "function equation"), (224, "function equation"), (225, "function equation"),
   (226, "function equation"), (227, "function equation"), (236, "function equation"),
   (239, "function equation"), (247, "function equation"), (249, "function equation"),
   (251, "function equation"), (252, "function equation"), (253, "function equation"),
   (262, "no direction"), (274, "no direction")]

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

theorem sig_sizes : (sigItems c).length = 213 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 136, 97, 5, 34) := by
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

/-! ## Consistency for every H: `f(_) => 1 requires isC(H:S #And d)`, witnessed at H := d -/

/- The clause of `f` has the `requires` `isC(H)` and the predicate `H ∈ d` in its premise
(`andUnderAppCut`), so `Semantics.clausesPreTop` is false (`clausesPreTop_false`). Termination: the
order `callOrder` places `isC` before `f`, whose predicate applies no function (`term_named`: none
named). Totality: `isC`, whose own clauses have the predicate `\top` (`total_isCH`). The agreement
names no function (`agree_named`); the match independence names `f`'s clause, whose right side has
no variable (`matchG`); `OpenDecided` is `openDecidedH`: the clause of `f` is `Witnessed` at H := d
under every H (`witnessedH`), so its condition, which the account lists as owed, is decided.
`OpenLaws` holds, the text having no open generator (`noRaw`). `FnHyp` holds for every H (`fnHypH`,
by `fnHyp_of_decidedPre_withHooks`), so `Γc` with the step's closure has a model for every H
(`consistent`). -/

def fS : Sym := 390
def isCS : Sym := 391
def dS : Sym := 388
def cS : Sym := 387
def aS : Sym := 386
def sS : Srt := 32

theorem names : c.symName fS = "Lblf" ∧ c.symName isCS = "LblisC" ∧ c.symName dS = "Lbld" ∧
    c.symName cS = "Lblc" ∧ c.symName aS = "Lbla" ∧ c.sortName sS = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-! ### The clauses -/

/-- `f(X) => 1 requires isC(H) ∧ H ∈ d`, X:Int, H:S -/
def clG : Clause :=
  { vars := [Srt.int, sS], pats := [.var 0], req := some (.app isCS [.var 1]), rhs := .dv Srt.int (.int 1),
    ens := none, pre := .mem sS (.var 1) (.app dS []) }
def fG : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clG] }
/-- `isC(c(_)) => true` -/
def ic1 : Clause := { vars := [33], pats := [.app cS [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(a) => false` -/
def ica : Clause := { vars := [], pats := [.app aS []], req := none, rhs := .dv Srt.bool (.bool false), ens := none }
/-- `isC(d) => true` -/
def icd : Clause := { vars := [], pats := [.app dS []], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
def fIsC : Fn := { label := isCS, args := [sS], result := Srt.bool, clauses := [ica, ic1, icd], total := true }

theorem text : c.fns = [fG, fIsC] := by rfl
theorem fG_mem : fG ∈ c.fns := by rw [text]; exact List.mem_cons_self ..
theorem fIsC_mem : fIsC ∈ c.fns := by rw [text]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- A clause's predicate is not `\top`. -/
theorem clausesPreTop_false : c.clausesPreTop = false := by decide +kernel

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fG := by rfl
theorem lookupIsCH (H : HookParams) : (cH H).lookupFn isCS = some fIsC := by rfl

def dv : GroundTerm := .ctor dS []

theorem sorts : c.sortOf dv = some sS := by decide +kernel
theorem sortsH (H : HookParams) : (cH H).sortOf dv = some sS := by
  show (c.withHooks H).sortOf dv = some sS
  rw [Semantics.sortOf_withHooks c H noRaw]; exact sorts

theorem syms : c.isCtor dS = true ∧ c.isCtor isCS = false ∧ isHook isCS = false ∧ c.isParam isCS = false := by
  decide +kernel

/-! ### The facts the deciders name -/

/-- `isC`, then `f`. -/
def callOrder : List Sym := [isCS, fS]

/-- No function's termination is named: each applies, in its clauses' terms and predicates, only
functions placed before it. -/
theorem term_named : c.preRankObligationsFP callOrder = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = [(fS, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [(0, 0)] := by decide +kernel
/-- The totality check accepts `isC`. -/
theorem total_isC : c.totalOK fIsC = true ∧ c.totalBefore fIsC = [] := by decide +kernel

/-! ### Match independence and coherence, for every H -/

/-- The clause of `f` is match independent: its right side has no variable. -/
theorem matchG (H : HookParams) : MatchIndependent (cH H) clG := by
  have hx : clG.exs = [] := rfl
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  cases hi

/-- The match independences the deciders leave, for every H: the clause of `f`. -/
theorem matchOblH (H : HookParams) : Det.MatchObligationsL (cH H) := by
  intro p hp fn hfn cl hcl
  rw [Det.Semantics.matchObligationsL_withHooks, match_named, List.mem_singleton] at hp
  subst hp
  rw [lookupFH] at hfn
  cases hfn
  simp only [fG, List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact matchG H

open Det in
/-- **The clauses that compete are coherent, for every H.** No termination fact and no fact on the
clauses' predicates is read. -/
theorem coherentH (H : HookParams) : CoherentAll (cH H) := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  have hmc : Exec.MatchCtxO (cH H) := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls (coreOKH H)⟩
  have hnoEx : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr noExs
  have hag := clausesAgree_of_IO hok hnoEx hsr hmc (fun f hf => by
    rw [Det.Semantics.agreeObligationsI_withHooks, agree_named] at hf; exact absurd hf List.not_mem_nil)
  have hmi := matchIndependentAll_of_L hok hnoEx hmc (matchOblH H)
  exact coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp

/-! ### The clause of `f` is `Witnessed` at H := d, for every H -/

/-- **`isC(d)` is `true`**, by `isC(d) => true`: no clause of a smaller priority. -/
theorem isC_d (H : HookParams) : Eval (cH H) isCS [dv] (some (bool true)) :=
  .clause (cl := icd) (σ := []) (lookupIsCH H) (by simp [fIsC]) (fun i s hs => by simp [icd] at hs)
    (.cons (.ctor syms.1 .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `H ↦ d`. -/
def σd : Subst := [(1, dv)]

/-- The `requires` `isC(H)` at H := d: `true`. -/
theorem req_d (H : HookParams) : EvalTerm (cH H) σd (.app isCS [.var 1]) (some (bool true)) :=
  .call (vs := [dv]) syms.2.1 syms.2.2.1 (.cons .var .nil) rfl (isC_d H) syms.2.2.2

/-- The predicate `H ∈ d` at H := d: true. -/
theorem pre_d (H : HookParams) : Holds (cH H) clG.vars.length σd clG.pre true := by
  have h := Holds.mem (c := cH H) (n := clG.vars.length) (σ := σd) (s := sS) (EvalTerm.var (i := 1))
    (EvalTerm.ctor (ts := []) syms.1 .nil)
  have e : ((σd.lookup 1).isSome &&
      sameResult (σd.lookup 1) ((allSome ([] : List (Option GroundTerm))).map (GroundTerm.ctor dS))) = true := by
    decide +kernel
  rw [e] at h
  exact h

/-- **The clause of `f` is `Witnessed`** at H := d, under every interpretation: its `requires`
`isC(d)` is `true` and its predicate `d ∈ d` true, and under `coherentH` neither has another
result. -/
theorem witnessedH (H : HookParams) : clG.Witnessed (cH H) := by
  refine Clause.witnessed_of_coherent (coherentH H) (σ := σd) (fun j hj s hs => ?_) (fun t ht => ?_) (pre_d H)
  · have hj1 : j = 1 := by
      have : clG.condVars = [1, 1] := by decide +kernel
      rw [this] at hj; simpa using hj
    subst hj1
    cases (show some sS = some s from hs)
    exact ⟨dv, rfl, sortsH H⟩
  · cases ht
    exact ⟨req_d H, fun r hr => EvalTerm.functional (coherentH H) hr (req_d H)⟩

/-- **`OpenDecided` for every H**: no rule's condition is owed, and the one clause owed, `f`'s, is
`Witnessed`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by
    intro p hp fn hfn cl hcl
    rw [Semantics.owedClauses_withHooks, owed_clauses, List.mem_singleton] at hp
    subst hp
    have hfn' : c.fns[0]? = some fn := hfn
    rw [text] at hfn'
    cases hfn'
    cases hcl
    exact .inl (witnessedH H))⟩

/-! ### Totality of `isC`, for every H -/

/-- **`isC` is total under every H**, given that every function terminates: its own clauses have
the predicate `\top`, and the totality check accepts it (`total_isC`). -/
theorem total_isCH (H : HookParams) (hterm : ∀ g, Terminates (cH H) g) : Total (cH H) isCS :=
  total_of_totalOKFP (c := cH H) (fn := fIsC) (coreOKH H) ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) hterm
    fIsC_mem
    ((Semantics.rightHeld_withHooks rightHeld H noRaw).heldFn fIsC_mem)
    (show c.totalOK fIsC = true from total_isC.1)
    (fun cl hcl => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl <;> rfl)
    (fun g hg => by
      have : g ∈ c.totalBefore fIsC := hg
      rw [total_isC.2] at this
      cases this)

/-! ### `FnHyp` and consistency, for every H -/

/-- **Every function terminates under every H**: by the order `callOrder`, which names none. The
predicate of `f`'s clause is decided at each match, its terms applying no function. -/
theorem terminatesH (H : HookParams) : ∀ g, Terminates (cH H) g := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  exact terminates_of_preRankFP (sortCtx_of_all hok hsr (Semantics.ovlCase_of_core (coreOKH H))) hok
    ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) (Semantics.rightHeld_withHooks rightHeld H noRaw)
    fnOvl_none callOrder (fun g hg => by
      rw [Semantics.preRankObligationsFP_withHooks, term_named] at hg; cases hg)

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [term_named] at hg; cases hg)
    (fun fn hfn ht => by
      rw [text] at hfn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
      rcases hfn with rfl | rfl
      · cases ht
      · exact total_isCH H (terminatesH H))
    (fun f hf => by rw [agree_named] at hf; cases hf)
    (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

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
  [U.ax161]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

theorem rule0_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule0_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule0_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 0 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 161. -/
theorem rule0_text : (trS U.ax161).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel
/-- **W1 for rule 0**: Γ's item is a consequence of sentence 161. -/
theorem rule0_from_text : itemsPremises [trS U.ax161] ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule0_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule0_table rule0_free ?_
  rw [← rule0_text]
  exact hI _ (Or.inl ⟨trS U.ax161, List.mem_singleton_self _, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl
  · exact ⟨U.ax161, List.mem_cons_self, rule0_from_text⟩

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

theorem nj121 : (trS U.ax121).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj126 : (trS U.ax126).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj129 : (trS U.ax129).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax121, U.ax126, U.ax129], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj121]; exact orTopBot_valid hD rfl
  · rw [nj126]; exact orTopBot_valid hD rfl
  · rw [nj129]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax122, U.ax123, U.ax124, U.ax125, U.ax127, U.ax128, U.ax131],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax122, U.ax123, U.ax124, U.ax125, U.ax127, U.ax128, U.ax131],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax130).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (130)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax130).pat := by
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
   U.ax78, U.ax79, U.ax80, U.ax82, U.ax83, U.ax84, U.ax85, U.ax87, U.ax111, U.ax112]

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


/-! ## Library sample: sentence 172, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax172).pat = (trAxiom [] [] U.ax172).pat := by decide +kernel
theorem s166_pattern : U.ax172.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax172.ax.sortVars.map sortVarKey ++ freeOf [] U.ax172.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax172.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 172 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax172.ax.sortVars U.ax172.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax172).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax172.ax.sortVars U.ax172.ax.pattern = t at he ⊢
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
/-- **Sentence 172 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax172 (trS U.ax172).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## Function equations (35 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 215, `andUnderAppCut`) is the equation whose premise Γ writes through a cut of
the clause's `requires` (`KcoreSpec/TieCutEq.lean`): `andUnderAppCut` reads `K[\and{S}(x, u)]` as
`K[x]` with the membership `x ∈ u`, and `notAsCondition` reads `\not{SortBool{}}(b)` as `b = false`.
The sentence is the item with the premise as the text writes it (`cut<j>_same`: `TieCutEq.textItem`,
up to the names of its variables, free and bound), and it is not the item (`cut<j>_differs`). Of the
two premises, Γ's is inside the text's in every model; the text's is inside Γ's where definedness is
read and, for `notAsCondition`, every element of Bool is `true` or `false`; under a competitor's
negation the inclusions swap sides. So for `andUnderAppCut` one direction reads definedness only and
the other the constructors' facts (`HoldsShape.NodeFacts`, which a model of Γc has:
`cut_nodeFacts`), and for `notAsCondition` both read the constructors' facts and the closure of Bool
(`boolClosed`), a premise named in `cut<j>_iff` and `cut<j>_entailed`, not Γ's.

Every other item is the translation of its function sentence (`shape`). -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

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

theorem cut_sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- A model of Γc has the constructors' facts. -/
theorem cut_nodeFacts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) : HoldsShape.NodeFacts (cH H) I :=
  HoldsShape.nodeFacts_of_core (coreOKH H) hI

/-- Γ's axiom of item 0 (sentence 215). -/
noncomputable def cutAx0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem cutAx0_at : (TiePair.fnAxioms c)[0]? = some cutAx0 := by decide +kernel
noncomputable def cutItem0 : P := (trAxiom [] [] ⟨0, "kernel", cutAx0⟩).pat
theorem cutItem0_at : (TiePair.gammaPats c)[0]? = some cutItem0 := TiePair.gammaPats_at cutAx0_at
kernel_rfl fnText_at0 : fnText[0]? = some U.ax215
/-- The text's form of item 0: the conjunction at the argument path [0] of the `requires`. -/
noncomputable def cutText0 : P := (TieCutEq.textItem (.andApp [0]) .own cutAx0).getD .bottom
kernel_rfl cut0_text_eq : TieCutEq.textItem (.andApp [0]) .own cutAx0 = some cutText0
/-- The two forms have the same free variables, and the cut premise is of the form the converse
inclusions read (kernel). -/
theorem cut0_shape : TieCutEq.shapeOK (.andApp [0]) .own cutAx0 = true := by decide +kernel
theorem cut0_facts : TieCutEq.factsOK c (.andApp [0]) .own cutAx0 = true := by decide +kernel
/-- **Sentence 215 is the text's form of item 0** up to the names of the variables (kernel), and
is not the item. -/
theorem cut0_same : TieAlpha.acEqB cutText0 (trS U.ax215).pat = true := by decide +kernel
theorem cut0_differs : cutItem0 ≠ (trS U.ax215).pat := by decide +kernel

/-- **Sentence 215 gives Γ's item 0** in every model of definedness. -/
theorem cut0_from_text {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (h : I ⊧ᴵ (trS U.ax215).pat) : I ⊧ᴵ cutItem0 :=
  TieCutEq.cutEq_from_text_pure hD cut0_text_eq cut0_shape ((TieAlpha.acEqB_sat cut0_same).mpr h)

/-- **E for sentence 215**: Γc entails it, for every H (`cut_nodeFacts`). -/
theorem cut0_entailed (H : HookParams) : Γc (cH H) ⊧ (trS U.ax215).pat := by
  intro M _ I hI
  exact (TieAlpha.acEqB_sat cut0_same).mp (TieCutEq.cutEq_entailed (k := (.andApp [0])) (cut_nodeFacts H hI)
    (cut_sortOf_true H) (fun h => nomatch h) cut0_text_eq cut0_shape ((TieCutEq.factsOK_withHooks c H _ _ _).trans cut0_facts)
    (fnItem_sat (fun φ hφ => hI φ (Or.inl hφ)) cutItem0_at))

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 0. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 cutItem0

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

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the cut ones whose entailment reads more than Γ (items 0), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([0] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of `fnText`; item 0 by `cut0_from_text`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  have hg : (TiePair.gammaPats c)[j]? = some it.pat := by
    rw [← TiePair.gammaPats_withHooks c H]
    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
  have pick : ∀ {i : Nat} {g : P} {ad : AxiomDecl}, (TiePair.gammaPats c)[i]? = some g → fnText[i]? = some ad →
      (TiePair.Texts [(trS ad).pat] ⊧ g) → j = i →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
    intro i g ad hgi hti hent hji
    subst hji
    rw [hgi] at hg
    exact ⟨ad, hti, (Option.some.inj hg) ▸ hent⟩
  by_cases h0 : j = 0
  · exact pick cutItem0_at fnText_at0
      (fun {M} _ {I} hI => cut0_from_text (TiePair.defOK_texts hI)
        (hI _ (Or.inl (List.mem_singleton_self _)))) h0
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
theorem nojunk_trivial_entailed_c (H : HookParams) :
    ∀ ad ∈ [U.ax121, U.ax126, U.ax129], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax122, U.ax123, U.ax124, U.ax125, U.ax127, U.ax128, U.ax131],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax130).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 62 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax62).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

/-! ## `f(0) = 1`, from the sentences, for every H (written by hand) -/

def wpI0 : GroundTerm := .dv Srt.int (.int 0)
def wpI1 : GroundTerm := .dv Srt.int (.int 1)

theorem wpInt_sorts (H : HookParams) :
    (cH H).sortOf wpI0 = some Srt.int ∧ (cH H).sortOf wpI1 = some Srt.int := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- `X ↦ 0`, `H ↦ d`. -/
def wpσG : Subst := [(0, wpI0), (1, dv)]

theorem wpWs_G (H : HookParams) : (cH H).WellSorted clG.vars wpσG := fun i s hs => by
  match i, hs with
  | 0, hs => cases (show some Srt.int = some s from hs); exact ⟨wpI0, rfl, (wpInt_sorts H).1⟩
  | 1, hs => cases (show some sS = some s from hs); exact ⟨dv, rfl, sortsH H⟩
  | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)

/-- The predicate `H ∈ d` at X := 0, H := d: true. -/
theorem wpPre_G (H : HookParams) : Holds (cH H) clG.vars.length wpσG clG.pre true := by
  have h := Holds.mem (c := cH H) (n := clG.vars.length) (σ := wpσG) (s := sS) (EvalTerm.var (i := 1))
    (EvalTerm.ctor (ts := []) syms.1 .nil)
  have e : ((wpσG.lookup 1).isSome &&
      sameResult (wpσG.lookup 1) ((allSome ([] : List (Option GroundTerm))).map (GroundTerm.ctor dS))) = true := by
    decide +kernel
  rw [e] at h
  exact h

/-- **`f(0)` is 1, for every H**, by the clause of `f` at X := 0, H := d: its `requires` `isC(d)`
is `true` (`isC_d`) and its predicate `d ∈ d` true. -/
theorem wpEval_f0 (H : HookParams) : Eval (cH H) fS [wpI0] (some wpI1) :=
  .clause (cl := clG) (σ := wpσG) (lookupFH H) (by simp [fG]) (wpWs_G H) (.cons (.var rfl) .nil)
    (fun t ht => by
      cases ht
      exact .call (vs := [dv]) syms.2.1 syms.2.2.1 (.cons .var .nil) rfl (isC_d H) syms.2.2.2)
    (wpPre_G H)
    (fun cl' hcl' _ hlt => by
      simp only [fG, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      subst hcl'
      exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `⟦f(0)⟧`. -/
noncomputable abbrev wpF0 (H : HookParams) : P := TiePair.app (cH H) fS [wpI0]

/-- **Every model of `Γc` reads `f(0)` as 1, for every H**: `Eval`'s result, the clause's owed
condition (`openDecidedH`, by `witnessedH`) giving the exclusions the reading of a clause needs. -/
theorem wpF0_c (H : HookParams) : Γc (cH H) ⊧ (wpF0 H ≡ den (cH H) wpI1) := by
  intro M _ I hIc e m
  have hI : I ⊧ᴵP Γ (cH H) := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hokCl := Semantics.sortedOKCl_of_sortedOK_noExs hok ((Semantics.fnsNoExs_withHooks c H).mpr noExs)
  have hpreR := HoldsShape.preReadAll_of_core (coreOKH H) hIc
  have hneg := neg_of_coreCl hIc hokCl hsr (Semantics.coreOK_parts (coreOKH H)).2.1 hph (openDecidedH H).2 hpreR
  have h0 := eval_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl hokCl)
    hneg hpreR (wpEval_f0 H) (lookupFH H)
    (sortsOf_cons.mpr ⟨_, _, (wpInt_sorts H).1, sortsOf_nil, rfl⟩)
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  exact h0 e a

/-- The sentences of `fnText`'s first four items: 215 is `f(_) => 1 requires isC(H:S #And d)`,
223, 224 and 225 are `isC(a) => false`, `isC(c(_)) => true` and `isC(d) => true`. -/
theorem wpFnText_index : (fnText.map (·.index)).take 4 = [215, 223, 224, 225] := by decide +kernel

/-- The premises of the derivation: the function sentences as written, but Γ's item in the place
of sentence 215 (`textPats`; the sentence gives the item, `cut0_from_text`), Γ's rule item, the
families of the reading, and `Γcl` (`boolClosed`, a family of the reading of a definition that
reads a confined sort). -/
def wpPre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats ∪ Γcl (cH H)

/-- **Every premise of `Γc` is a consequence of `wpPre`.** -/
theorem wpGamma_from (H : HookParams) : ∀ φ, Γc (cH H) φ → wpPre H ⊧ φ := by
  intro φ h M _ I hI
  rcases h with h | h
  · exact gamma_from H φ h (I := I) fun ψ hψ => hI ψ (Or.inl hψ)
  · exact hI φ (Or.inr h)

/-- **`wpPre` with the step's closure has a model, for every H**: every model of `Γc` with it is one. -/
theorem wpPre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (wpPre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with (h | h) | h
  · rcases h with ((h1 | h1) | h1)
    · rcases h1 with ht | ⟨x, rfl⟩
      · exact TiePair.entailed (shapeH H) φ ht hΓ
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
    · exact hΓ _ (Or.inl (Or.inr h1))
    · rcases h1 with (((h1 | h1) | h1) | h1) | h1
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
      · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inl (Or.inr h))
  · exact hI _ (Or.inr h)

/-- **`f(0) = 1`, derived from `wpPre`, for every H**: sentence 215, the equation of `f`, holds H
universal over S, so it holds at H := d, where `isC(d) => true` (225) makes `isC(H #And d)` true;
`wpPre` with the step's closure has a model (`wpPre_model`). -/
theorem wpF0_is_1 (H : HookParams) : wpPre H ⊧ (wpF0 H ≡ den (cH H) wpI1) :=
  fun hT => wpF0_c H fun φ hφ => wpGamma_from H φ hφ hT


end KCore.TieE3WitnessedPre

#check @KCore.TieE3WitnessedPre.noRaw
#check @KCore.TieE3WitnessedPre.readsConfined_c
#check @KCore.TieE3WitnessedPre.userAxioms_eq
#check @KCore.TieE3WitnessedPre.coreOK
#check @KCore.TieE3WitnessedPre.account
#check @KCore.TieE3WitnessedPre.account_sizes
#check @KCore.TieE3WitnessedPre.account_classes
#check @KCore.TieE3WitnessedPre.account_absent
#check @KCore.TieE3WitnessedPre.absent_closed
#check @KCore.TieE3WitnessedPre.absent_proj_below_c
#check @KCore.TieE3WitnessedPre.absent_proj_below
#check @KCore.TieE3WitnessedPre.lists_in_account
#check @KCore.TieE3WitnessedPre.attrs_agree
#check @KCore.TieE3WitnessedPre.sig_origin
#check @KCore.TieE3WitnessedPre.decls_entailed
#check @KCore.TieE3WitnessedPre.consistent
#check @KCore.TieE3WitnessedPre.fnHypH
#check @KCore.TieE3WitnessedPre.nojunk_trivial_entailed
#check @KCore.TieE3WitnessedPre.nojunk_items_entailed
#check @KCore.TieE3WitnessedPre.nojunk_kitem_entailed
#check @KCore.TieE3WitnessedPre.cons_entailed
#check @KCore.TieE3WitnessedPre.rules_account
#check @KCore.TieE3WitnessedPre.rule_from_text
#check @KCore.TieE3WitnessedPre.idem_refuted
#check @KCore.TieE3WitnessedPre.lib166
#check @KCore.TieE3WitnessedPre.lib166_at_values
#check @KCore.TieE3WitnessedPre.gammaCl_eq
#check @KCore.TieE3WitnessedPre.decls_entailed_c
#check @KCore.TieE3WitnessedPre.nojunk_trivial_entailed_c
#check @KCore.TieE3WitnessedPre.nojunk_items_entailed_c
#check @KCore.TieE3WitnessedPre.nojunk_kitem_entailed_c
#check @KCore.TieE3WitnessedPre.cons_entailed_c
#check @KCore.TieE3WitnessedPre.idem_refuted_c
#print axioms KCore.TieE3WitnessedPre.noRaw
#print axioms KCore.TieE3WitnessedPre.readsConfined_c
#print axioms KCore.TieE3WitnessedPre.userAxioms_eq
#print axioms KCore.TieE3WitnessedPre.coreOK
#print axioms KCore.TieE3WitnessedPre.account
#print axioms KCore.TieE3WitnessedPre.account_sizes
#print axioms KCore.TieE3WitnessedPre.account_classes
#print axioms KCore.TieE3WitnessedPre.account_absent
#print axioms KCore.TieE3WitnessedPre.absent_closed
#print axioms KCore.TieE3WitnessedPre.absent_proj_below_c
#print axioms KCore.TieE3WitnessedPre.absent_proj_below
#print axioms KCore.TieE3WitnessedPre.lists_in_account
#print axioms KCore.TieE3WitnessedPre.attrs_agree
#print axioms KCore.TieE3WitnessedPre.sig_origin
#print axioms KCore.TieE3WitnessedPre.decls_entailed
#print axioms KCore.TieE3WitnessedPre.consistent
#print axioms KCore.TieE3WitnessedPre.fnHypH
#print axioms KCore.TieE3WitnessedPre.nojunk_trivial_entailed
#print axioms KCore.TieE3WitnessedPre.nojunk_items_entailed
#print axioms KCore.TieE3WitnessedPre.nojunk_kitem_entailed
#print axioms KCore.TieE3WitnessedPre.cons_entailed
#print axioms KCore.TieE3WitnessedPre.rules_account
#print axioms KCore.TieE3WitnessedPre.rule_from_text
#print axioms KCore.TieE3WitnessedPre.idem_refuted
#print axioms KCore.TieE3WitnessedPre.lib166
#print axioms KCore.TieE3WitnessedPre.lib166_at_values
#print axioms KCore.TieE3WitnessedPre.gammaCl_eq
#print axioms KCore.TieE3WitnessedPre.decls_entailed_c
#print axioms KCore.TieE3WitnessedPre.nojunk_trivial_entailed_c
#print axioms KCore.TieE3WitnessedPre.nojunk_items_entailed_c
#print axioms KCore.TieE3WitnessedPre.nojunk_kitem_entailed_c
#print axioms KCore.TieE3WitnessedPre.cons_entailed_c
#print axioms KCore.TieE3WitnessedPre.idem_refuted_c
#check @KCore.TieE3WitnessedPre.fns_account
#check @KCore.TieE3WitnessedPre.cut0_shape
#check @KCore.TieE3WitnessedPre.cut0_facts
#check @KCore.TieE3WitnessedPre.cut0_same
#check @KCore.TieE3WitnessedPre.cut0_differs
#check @KCore.TieE3WitnessedPre.cut0_from_text
#check @KCore.TieE3WitnessedPre.cut0_entailed
#check @KCore.TieE3WitnessedPre.shape
#check @KCore.TieE3WitnessedPre.fns_entailed
#check @KCore.TieE3WitnessedPre.fns_from_text
#check @KCore.TieE3WitnessedPre.fn_prios
#check @KCore.TieE3WitnessedPre.gamma_from
#print axioms KCore.TieE3WitnessedPre.fns_account
#print axioms KCore.TieE3WitnessedPre.cut0_shape
#print axioms KCore.TieE3WitnessedPre.cut0_facts
#print axioms KCore.TieE3WitnessedPre.cut0_same
#print axioms KCore.TieE3WitnessedPre.cut0_differs
#print axioms KCore.TieE3WitnessedPre.cut0_from_text
#print axioms KCore.TieE3WitnessedPre.cut0_entailed
#print axioms KCore.TieE3WitnessedPre.shape
#print axioms KCore.TieE3WitnessedPre.fns_entailed
#print axioms KCore.TieE3WitnessedPre.fns_from_text
#print axioms KCore.TieE3WitnessedPre.fn_prios
#print axioms KCore.TieE3WitnessedPre.gamma_from
#check @KCore.TieE3WitnessedPre.wpEval_f0
#check @KCore.TieE3WitnessedPre.wpF0_c
#check @KCore.TieE3WitnessedPre.wpFnText_index
#check @KCore.TieE3WitnessedPre.wpPre_model
#check @KCore.TieE3WitnessedPre.wpF0_is_1
#print axioms KCore.TieE3WitnessedPre.wpF0_is_1
#print axioms KCore.TieE3WitnessedPre.wpPre_model
