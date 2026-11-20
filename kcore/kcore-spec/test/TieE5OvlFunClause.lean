/-
  The tie (C14) on `f2-examples/e5-ovl-fun-clause.kompile.kore`, the kompiled text of construct fixture e5-ovl-fun-clause
  (`test/constructs/fixtures/e5-ovl-fun-clause`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e5-ovl-fun-clause`, its consistency, ovlfn section by hand; run from the package root:
  `lake env lean -j1 test/TieE5OvlFunClause.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate (`wfFailing`).
  - The account: the class lists and the three sentences of a function-overloaded symbol, listed
    apart (`ovlFnApart`), partition the 154 sentences of the user module E5-OVL-FUN-CLAUSE, the
    classes in `tieClassesOvl`' order (`account`, `account_sizes`, `account_classes`); the
    no-direction class holds exactly the sentences that apply a symbol Γ lacks (`account_absent`,
    `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 212 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the totality of the `[total]` function `capN` (`total_named`); the match independence of a
    clause (`match_named`); `FnHyp` itself: a clause's predicate is not `\top`
    (`Semantics.clausesPreTop` false), so the named facts do not give it and `kcore gen --core` takes it
    as the hypothesis of its statements, which no decider confirms. The consistency section, written by
    hand, proves that `Γc` with the step's closure has a model for every H (`consistent`), through
    `FnHyp` for every H (`fnHypH`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (33) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 1 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 1 (156) is not its sentence (`un<j>_differs`) and no reading
    here ties it: the sentence is `uncovered`, and `fns_entailed` and `fns_from_text` leave it out.
    `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Constructor sentences (29): entailed by Γ (`cons_entailed`).
  - Overload axioms (102): entailed by Γ, whose overload equation states each at every
    element (`ovleq_entailed`).
  - Sentences of a function-overloaded symbol (57, the `functional` sentence of `LblcapGas`; 58, the
    same-constructor sentence of `LblcapGas`; 59, a different-constructors sentence of `LblcapGas`
    and `Lblinf`), weaker under overloadFunction, listed apart (`ovlFnApart`): Γ holds each at the
    arguments no overload covers only. Part 1, for every H: in a model of Γ the sentence, with the
    `functional` sentence it is joint with, entails Γ's item at uncovered arguments
    (`ovlfn_text_<i>`, `ovlfn_entails_item_<i>`), which is Γ's (`ovlfn_item_in_gamma_<i>`). Part 2,
    what it says at covered arguments, by hand: at values for every H (57, 58, 59;
    `ovlfn_at_values_<i>`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (49): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 1 (whose sentence is uncovered), Γ's rule items, the five parts Γ defines by predicates, or
    definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  Gas's no junk (91) is entailed (`nojunk_gas_entailed`): its item lists Gas's generators in another
  order than `Semantics.gens`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (22);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunClause

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-clause.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-clause.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-clause.kompile.kore" module "E5-OVL-FUN-CLAUSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E5-OVL-FUN-CLAUSE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 154 := by decide +kernel

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

/-- Per class of the tie (`tieClassesOvl`: `tieClasses` with the class overload equation), the
indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [104, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
      126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 156]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [24, 26, 28, 30, 61, 81, 82, 89]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]),
   ("injectivity", [25, 27, 29, 31]),
   ("distinctness", []),
   ("no junk", [90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]),
   ("function functional", [60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]),
   ("hooked functional", [21, 22, 23, 32, 33, 34, 35, 36, 37, 40, 44, 52, 53, 54, 55, 56, 63, 80, 83, 84, 85, 86, 87]),
   ("collection law", [41, 42, 43, 45, 46, 47, 48, 50, 51]),
   ("library", [103, 155]),
   ("set idempotence", [49]),
   ("set-variable lemma", [157]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("overload equation", [102]),
   ("no direction", [38, 39, 62, 88, 105, 106, 107, 108, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
      151, 152, 153, 154])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences of a function-overloaded symbol (its `functional` sentence and its no-confusion
sentences), which Γ holds at the arguments no overload covers only: weaker under overloadFunction,
in no class. -/
def ovlFnApart : List Nat := [57, 58, 59]

/-- **The account**: the class lists and the sentences of a function-overloaded symbol partition the
user module's sentences. Their concatenation is a permutation of the sentences' indices, which are
distinct, so each sentence is in one class or among those of a function-overloaded symbol, and there
once. -/
theorem account : (classes.flatMap (·.2) ++ ovlFnApart).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 33), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 8), ("subsort", 17), ("injectivity", 4), ("distinctness", 0), ("no junk", 12), ("function functional", 17), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("overload equation", 1), ("no direction", 23)] := by
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
  [(140, "Bool"), (141, "Gas"), (142, "GeneratedCounterCell"), (143, "GeneratedCounterCellOpt"),
   (144, "GeneratedTopCell"), (145, "GeneratedTopCellFragment"), (146, "Int"), (147, "K"),
   (148, "KCell"), (149, "KCellOpt"), (150, "KItem"), (151, "List"), (152, "Map"), (153, "N"),
   (154, "Set")]

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
  [(14, "subsort"), (16, "subsort"), (19, "subsort"), (60, "function functional"),
   (61, "constructor functional"), (65, "function functional"), (78, "function functional"),
   (89, "constructor functional"), (91, "no junk"), (100, "no junk"), (101, "no junk"),
   (102, "overload equation"), (104, "function equation"), (108, "no direction"),
   (111, "function equation"), (112, "function equation"), (136, "function equation"),
   (137, "function equation"), (141, "no direction"), (153, "no direction"),
   (156, "function equation"), (157, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(156, "function equation")]

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

theorem sig_sizes : (sigItems c).length = 212 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 92, 61, 4, 27) := by
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

/-! ## Consistency for every H: `uncap` through the membership in `capGas(G)`, and the totality of `capN` -/

/- The text has two functions. `capN : N → N` is `[total]` with the one equation `capN(z #as X) = X`.
`uncap : Gas → Gas` has the one equation `uncap(capGas(G)) = G`, read as the clause `uncapCl`: its
pattern is a variable X (V1) and its predicate `pre` the membership `X ∈ capGas(G)` (G is V0, a
variable the pattern does not bind). `capGas : Gas → Gas` overloads `capN`, N below Gas. That
predicate is not `\top`, so the named facts do not give `FnHyp` (`clausesPreTop` false), and it is
proved here for every H (`fnHypH`):
- A result at every argument. N holds `z` only (`val_N_oft`), and `capN(z)` is `z` under every H
  (`eval_z_oft`), so `capN` is total (`total_capN_oft`). The one value list of Gas that `capN`
  covers is `[inj{N,Gas}(z)]` (`cov_inv_oft`), so `capGas(G)` has a value at every value of G
  (`ovlFnTotal_oft`, `capRes_some_ofc`). At a value g of Gas, where some value u of Gas has
  `capGas(u)` with the value g, the clause applies with G := u and gives u (`uncap_of_res_ofc`);
  where none has, the membership is false at every match, the clause fails and `uncap(g)` is its
  rest, the interpretation's value (`uncap_rest_ofc`).
- Totality: `capN`, the one `[total]` function (`total_named`).
- Agreement: each function has one clause (`agree_one_ofc`).
- Match independence: `capN`'s pattern gives X the argument (`coh_capCl_ofc`); two matches of
  `uncapCl` at one argument g give G values u, u' at which `capGas` has the value g, and `capGas` is
  injective at values (`ovlFnInj_oft`: a covered application's value is an injection, an uncovered
  one's the raw application), so u = u' and both give that value (`coh_uncapCl_ofc`).
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`: G is open but
  the membership also reads X, which the pattern binds).
- `OpenLaws`: the text has no open generator (`noRaw`).
So `Γc` with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).
The values of `uncap`, for every H: `uncap(inj z)` is `inj z` (`uncap_injZ`), `uncap(capGas(u))`
is u at every value u of Gas at which `capGas(u)` has a value of Gas (`uncap_of_res_ofc`), and
`uncap(inf)` is the interpretation's value (`uncap_inf`: no value of `capGas` is `inf`). -/

def gasS : Srt := 32
def nS : Srt := 33
def infS : Sym := 386
def zS : Sym := 387
def capN : Sym := 388
def uncapS : Sym := 389
def capGas : Sym := 390

theorem syms_named : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName infS = "Lblinf" ∧
    c.symName zS = "Lblz" ∧ c.symName capN = "LblcapN" ∧ c.symName uncapS = "Lbluncap" ∧
    c.symName capGas = "LblcapGas" := by decide +kernel

/-- `capN(z #as X) = X`. -/
def capCl : Clause := { vars := [nS], pats := [.as (.app zS []) 0], req := none, rhs := .var 0, ens := none }
/-- `capN : N → N`, declared total. -/
def capNFn : Fn := ⟨capN, [nS], nS, [capCl], true⟩
/-- `uncap(X) = G` where `X ∈ capGas(G)`: X is V1, G is V0. -/
def uncapCl : Clause :=
  { vars := [gasS, gasS], pats := [.var 1], req := none, rhs := .var 0, ens := none,
    pre := .mem gasS (.var 1) (.app capGas [.var 0]) }
/-- `uncap : Gas → Gas`, not declared total. -/
def uncapFn : Fn := ⟨uncapS, [gasS], gasS, [uncapCl], false⟩
def capNSig : CtorSig := ⟨capN, [nS], nS⟩
def capGasSig : CtorSig := ⟨capGas, [gasS], gasS⟩
def infSig : CtorSig := ⟨infS, [], gasS⟩
def zSig : CtorSig := ⟨zS, [], nS⟩
/-- `capGas` overloads `capN`. -/
def oCap : OvlSig := ⟨capGasSig, [capN]⟩

kernel_rfl fns_c : c.fns = [capNFn, uncapFn]
kernel_rfl ovls_c : c.ovls = [oCap]

/-- **The reading**: the functions are `capN` and `uncap`, whose one clause reads the argument
pattern `capGas(G)` as the membership of the argument in it; the one overloading symbol is
`capGas`, over `capN`. -/
theorem reading : c.fns = [capNFn, uncapFn] ∧ c.ovls = [oCap] ∧ c.fnOvlSyms = [capGas] ∧
    c.clausesPreTop = false :=
  ⟨fns_c, ovls_c, by decide +kernel, by decide +kernel⟩

def zT : GroundTerm := .ctor zS []
def infT : GroundTerm := .ctor infS []
/-- `inj{N, Gas}(z)` -/
def injZ : GroundTerm := .inj nS gasS zT

kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn capN = some capNFn
kernel_rfl lookupUncap_H : ∀ H : HookParams, (cH H).lookupFn uncapS = some uncapFn
kernel_rfl isCtor_H : ∀ H : HookParams, (cH H).isCtor zS = true
kernel_rfl sort_z_H : ∀ H : HookParams, (cH H).sortOf zT = some nS
kernel_rfl fns_H : ∀ H : HookParams, (cH H).fns = [capNFn, uncapFn]

/-- A sort whose one generator is a constant holds that constant only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem onlyConst_oft {c : Semantics} {s : Srt} {k0 : CtorSig} (ha : k0.args = [])
    (hk : ∀ k ∈ c.ctorSigs, k.result = s → k = k0)
    (ho : ∀ o ∈ c.ovls, o.sig.result ≠ s)
    (hp : ∀ k ∈ c.params, k.raw = false)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s)
    (hdv : ∀ lit, dvOK c.lib s lit = false)
    (hcoll : c.collOf s = none)
    {v : GroundTerm} (h : c.sortOf v = some s) : v = .ctor k0.name [] := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk', hs, hr⟩ | ⟨-, o, hlo, -, -, hr⟩ | ⟨-, -, k, hko, -⟩
    · obtain ⟨hm, hn⟩ := lookupSig_spec hk'
      have := hk k hm hr.symm
      subst this
      rw [ha] at hs
      rw [sortsOf_inv_nil hs, hn]
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

/-- A sort that is no carrier of literals has none. -/
theorem noLit_oft {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

/-- **N holds `z` only.** -/
theorem val_N_oft {v : GroundTerm} (h : c.sortOf v = some nS) : v = zT :=
  onlyConst_oft (k0 := zSig) rfl (by decide +kernel) (by decide +kernel) noRaw (by decide +kernel)
    (noLit_oft (by decide +kernel)) (by decide +kernel) h

/-- **`capN(z)` evaluates to `z`**, by its one clause, under every H. -/
theorem eval_z_oft (H : HookParams) : Eval (cH H) capN [zT] (some zT) :=
  .clause (fn := capNFn) (cl := capCl) (σ := [(0, zT)]) (lookupFn_H H) (List.mem_singleton_self _)
    (fun i s h => by
      cases i with
      | zero => cases h; exact ⟨zT, rfl, sort_z_H H⟩
      | succ i => simp [capCl] at h)
    (.cons (.as (.ctor (isCtor_H H) .nil) rfl) .nil) (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      rw [show capNFn.clauses = [capCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t h => by cases h) .top

/-- **`capN` is `Total`, for every H**: its one clause decides at `z`, the one value of N. -/
theorem total_capN_oft (H : HookParams) : Total (cH H) capN := fun fn' hfn' vs hvs => by
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans (lookupFn_H H))
  rw [show capNFn.args = [nS] from rfl, Semantics.sortsOf_withHooks _ _ noRaw] at hvs
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
  cases sortsOf_inv_nil hws
  cases val_N_oft hw
  exact ⟨_, eval_z_oft H⟩

/-! ### `capGas(G)` at a value of G -/

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
-- `capGas`'s one overload is a function, of the result sort N.
kernel_rfl lifted_H : ∀ H : HookParams,
  (((cH H).ovlOver oCap).all fun kg => (cH H).ovlByFn kg && kg.result != oCap.sig.result) = true
kernel_rfl over_H : ∀ H : HookParams, (cH H).ovlOver oCap = [capNSig]
kernel_rfl sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [injZ] = some oCap.sig.args
kernel_rfl cover_H : ∀ H : HookParams, (cH H).fnCover oCap.sig.name [injZ] = some capNSig
kernel_rfl sort_injZ_H : ∀ H : HookParams, (cH H).sortOf injZ = some gasS

/-- The one sort directly below Gas is N. -/
theorem below_gas_oft : ∀ p ∈ c.subsorts, p.2 = gasS → p.1 = nS := by decide +kernel

/-- **The one value list of `capGas`'s argument sort a function overload covers is `[inj z]`**,
covered by `capN`: a covered value is an injection into Gas, from N, of a value of N. -/
theorem cov_inv_oft (H : HookParams) {us : List GroundTerm} {kg : CtorSig}
    (hus : (cH H).sortsOf us = some oCap.sig.args) (hc : (cH H).fnCover oCap.sig.name us = some kg) :
    us = [injZ] ∧ kg = capNSig := by
  obtain ⟨o', ho', hkg, -, hcv⟩ := OvlLaws.fnCover_some_parts hc
  rw [lookup_H H] at ho'; cases ho'
  rw [over_H H, List.mem_singleton] at hkg
  subst hkg
  rw [Semantics.sortsOf_withHooks _ _ noRaw] at hus
  obtain ⟨u, us', rfl, hu, hus'⟩ := sortsOf_inv_cons (show c.sortsOf us = some [gasS] from hus)
  cases sortsOf_inv_nil hus'
  refine ⟨?_, rfl⟩
  have hl : (cH H).lies nS gasS u = true := by
    simpa [Semantics.ovlCovers, capNSig, oCap, capGasSig] using hcv
  cases u with
  | inj C B w =>
    obtain ⟨hsub, -, hw, hB⟩ := OvlLaws.sortOf_inj_iff.mp hu
    cases hB
    obtain rfl : C = nS := below_gas_oft _ hsub rfl
    rw [val_N_oft hw]; rfl
  | ctor f ts => simp [Semantics.lies, nS, gasS] at hl
  | dv s l => simp [Semantics.lies, nS, gasS] at hl
  | map s es => simp [Semantics.lies, nS, gasS] at hl
  | set s es => simp [Semantics.lies, nS, gasS] at hl
  | list s es => simp [Semantics.lies, nS, gasS] at hl

/-- **`capGas(inj z)` has the value `inj z`**, for every H: `capN` covers `inj z`, and `capN(z)` is
`z`, lifted to Gas. -/
theorem res_injZ_oft (H : HookParams) : OvlFnRes (cH H) oCap [injZ] (some injZ) :=
  OvlFnRes.fn (cover_H H) (eval_z_oft H)

/-- **`OvlFnTotal`**, for every H: at the one covered value list `capN` has the value `z`. -/
theorem ovlFnTotal_oft (H : HookParams) : OvlFnTotal (cH H) oCap := fun vs kg hvs hc => by
  obtain ⟨rfl, rfl⟩ := cov_inv_oft H hvs hc
  exact ⟨zT, eval_z_oft H⟩

/-- **`OvlFnInj`**, for every H: one value list is covered. -/
theorem ovlFnInj_oft (H : HookParams) : OvlFnInj (cH H) oCap :=
  ovlFnInj_of_cov (lookup_H H) (lifted_H H) fun _ _ _ _ _ _ hus hvs h1 h2 _ _ _ =>
    (cov_inv_oft H hus h1).1.trans (cov_inv_oft H hvs h2).1.symm

/-- **`OvlFnDist capGas inf`**, for every H: `capGas`'s one overload is a function of the result
sort N, so a covered application's value is an injection. -/
theorem ovlFnDist_oft (H : HookParams) : OvlFnDist (cH H) oCap infSig :=
  ovlFnDist_of_lifted (lookup_H H) (lifted_H H) (by decide)

section CapGas
variable (H : HookParams)

theorem syms_ok_ofc : (cH H).isCtor capGas = false ∧ (cH H).isOvl capGas = true ∧
    (cH H).isParam capGas = false ∧ isHook capGas = false ∧ (cH H).isCtor infS = true :=
  (by decide +kernel : c.isCtor capGas = false ∧ c.isOvl capGas = true ∧ c.isParam capGas = false ∧
    isHook capGas = false ∧ c.isCtor infS = true)

theorem sortsOf_one_ofc {g : GroundTerm} (hg : (cH H).sortOf g = some gasS) :
    (cH H).sortsOf [g] = some oCap.sig.args := by
  simp only [Semantics.sortsOf, hg]; rfl

/-- **The result of `capGas(G)` under σ is the application's at G's value** (`OvlFnRes`): the
normal form where `capN` does not cover it, `capN`'s result lifted to Gas where it does. -/
theorem evalCap_res_ofc {σ : Subst} {g : GroundTerm} {r' : Option GroundTerm}
    (h : EvalTerm (cH H) σ (.app capGas [.var 0]) r') (hg : σ.lookup 0 = some g) :
    OvlFnRes (cH H) oCap [g] r' := by
  generalize ht : Term.app capGas [.var 0] = t at h
  cases h with
  | ctor hc _ => cases ht; rw [(syms_ok_ofc H).1] at hc; cases hc
  | hook _ hhk _ _ _ => cases ht; rw [(syms_ok_ofc H).2.2.2.1] at hhk; cases hhk
  | param _ _ hp _ _ => cases ht; rw [(syms_ok_ofc H).2.2.1] at hp; cases hp
  | call _ _ _ _ hf _ =>
    cases ht
    have h' := hf.isOvl_false
    rw [(syms_ok_ofc H).2.1] at h'
    cases h'
  | callUndef _ _ hts hvs _ =>
    cases ht
    obtain ⟨r0, rs', rfl, h0, hn⟩ := EvalTerms.cons_inv hts
    cases EvalTerms.nil_inv hn
    rw [EvalTerm.var_inv h0, hg] at hvs
    simp [allSome] at hvs
  | ovl _ _ hts hnf =>
    cases ht
    obtain ⟨r0, rs', rfl, h0, hn⟩ := EvalTerms.cons_inv hts
    cases EvalTerms.nil_inv hn
    rw [EvalTerm.var_inv h0, hg] at hnf ⊢
    exact .norm (hnf [g] rfl)
  | ovlFn _ _ hts hvs hlo hcov hf =>
    cases ht
    obtain ⟨r0, rs', rfl, h0, hn⟩ := EvalTerms.cons_inv hts
    cases EvalTerms.nil_inv hn
    rw [EvalTerm.var_inv h0, hg] at hvs
    cases hvs
    obtain rfl := Option.some.inj ((lookup_H H).symm.trans hlo)
    exact .fn hcov hf
  | _ => cases ht

/-- **`capGas(G)` under σ has the application's result at G's value.** -/
theorem evalCap_of_res_ofc {σ : Subst} {g : GroundTerm} {r : Option GroundTerm}
    (hg : σ.lookup 0 = some g) (h : OvlFnRes (cH H) oCap [g] r) :
    EvalTerm (cH H) σ (.app capGas [.var 0]) r := by
  cases h with
  | norm hnf =>
    exact EvalTerm.ovl (rs := [some g]) (syms_ok_ofc H).1 (syms_ok_ofc H).2.1 (.cons (hg ▸ .var) .nil)
      (fun vs hvs => by
        obtain rfl : [g] = vs := Option.some.inj hvs
        exact hnf)
  | fn hcov hev =>
    exact EvalTerm.ovlFn (rs := [some g]) (vs := [g]) (o := oCap) (syms_ok_ofc H).1 (syms_ok_ofc H).2.1
      (.cons (hg ▸ .var) .nil) rfl (lookup_H H) hcov hev

/-- **`capGas(u)` has a value at every value u of Gas.** -/
theorem capRes_some_ofc {u : GroundTerm} (hu : (cH H).sortOf u = some gasS) :
    ∃ v, OvlFnRes (cH H) oCap [u] (some v) :=
  OvlFnTotal.res (ovlFnTotal_oft H) (sortsOf_one_ofc H hu)

end CapGas

/-! ### `uncap` -/

/-- A membership whose two sides have one value holds. -/
theorem holds_mem_ofc {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {v : GroundTerm}
    (h : EvalTerm c σ t (some v)) (h' : EvalTerm c σ u (some v)) : Holds c n σ (.mem s t u) true := by
  have := Holds.mem (n := n) (s := s) h h'
  simpa [sameResult, cmp_eq_iff.mpr rfl] using this

/-- What a membership's truth value is made of. -/
theorem holds_mem_inv_ofc {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.mem s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = (r.isSome && sameResult r r') := by
  generalize hp : Cond.mem s t u = p at h
  cases h with
  | mem h h' => cases hp; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hp

/-- A result the same as a value's is that value. -/
theorem sameResult_inv_ofc {v : GroundTerm} {r : Option GroundTerm}
    (h : true = ((some v).isSome && sameResult (some v) r)) : r = some v := by
  cases r with
  | none => simp [sameResult] at h
  | some w =>
    have h' : sameResult (some v) (some w) = true := by simpa using h.symm
    have hvw : v = w := cmp_eq_iff.mp (by simpa [sameResult] using h')
    rw [hvw]

section Uncap
variable (H : HookParams)

theorem uncap_clauses_ofc {cl : Clause} (h : cl ∈ uncapFn.clauses) : cl = uncapCl := by
  simpa [uncapFn] using h

/-- Where `uncapCl` applies at `[g]` under σ, G's value u is of Gas and `capGas(u)` has the value g. -/
theorem uncap_applies_ofc {σ : Subst} {vs : List GroundTerm} (h : uncapCl.AppliesAt (cH H) σ vs) :
    ∃ u g, vs = [g] ∧ σ.lookup 0 = some u ∧ (cH H).sortOf u = some gasS ∧ OvlFnRes (cH H) oCap [u] (some g) := by
  obtain ⟨hws, hpv, -, hpre⟩ := h
  obtain ⟨u, hu0, hu⟩ := hws 0 (by decide) gasS rfl
  obtain ⟨g, vs', rfl, hg, hn⟩ := PatVals.cons_inv hpv
  cases PatVals.nil_inv hn
  have hg1 := PatVal.var_inv hg
  obtain ⟨r, r', hr, hr', hb⟩ := holds_mem_inv_ofc hpre
  rw [EvalTerm.var_inv hr, hg1] at hb
  rw [sameResult_inv_ofc hb] at hr'
  exact ⟨u, g, rfl, hu0, hu, evalCap_res_ofc H hr' hu0⟩

/-- **`uncap(g)` is u where `capGas(u)` has the value g**, u and g of Gas, for every H: the
clause applies with G := u. -/
theorem uncap_of_res_ofc {u g : GroundTerm} (hu : (cH H).sortOf u = some gasS)
    (hg : (cH H).sortOf g = some gasS) (h : OvlFnRes (cH H) oCap [u] (some g)) :
    Eval (cH H) uncapS [g] (some u) :=
  .clause (fn := uncapFn) (cl := uncapCl) (σ := [(0, u), (1, g)]) (lookupUncap_H H) (List.mem_singleton_self _)
    (fun i s hs => by
      match i, hs with
      | 0, hs => cases hs; exact ⟨u, rfl, hu⟩
      | 1, hs => cases hs; exact ⟨g, rfl, hg⟩
      | i + 2, hs => simp [uncapCl] at hs)
    (.cons (.var rfl) .nil) (fun t ht => by cases ht)
    (holds_mem_ofc (v := g) (.var : EvalTerm (cH H) [(0, u), (1, g)] (.var 1) _) (evalCap_of_res_ofc H rfl h))
    (fun cl' h _ hlt => by
      obtain rfl := uncap_clauses_ofc h
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => by cases ht) .top

/-- **Where no value of Gas has `capGas` with the value g, `uncap(g)` is its rest**, for every H:
the membership is false at every match. -/
theorem uncap_rest_ofc {g : GroundTerm}
    (hn : ¬ ∃ u, (cH H).sortOf u = some gasS ∧ OvlFnRes (cH H) oCap [u] (some g)) :
    Eval (cH H) uncapS [g] ((cH H).fnRest uncapFn [g]) :=
  .rest (lookupUncap_H H) fun cl hcl => by
    obtain rfl := uncap_clauses_ofc hcl
    refine .intro fun σ hws hpv => ?_
    obtain ⟨u, hu0, hu⟩ := hws 0 (by decide) gasS rfl
    obtain ⟨g', vs', he, hg, hn'⟩ := PatVals.cons_inv hpv
    cases PatVals.nil_inv hn'
    obtain ⟨rfl, -⟩ := List.cons.inj he
    have hg1 := PatVal.var_inv hg
    obtain ⟨v, hv⟩ := capRes_some_ofc H hu
    have hb : ((σ.lookup 1).isSome && sameResult (σ.lookup 1) (some v)) = false := by
      rw [hg1]
      cases hs : ((some g).isSome && sameResult (some g) (some v)) with
      | false => rfl
      | true =>
        have := sameResult_inv_ofc hs.symm
        obtain rfl : v = g := Option.some.inj this
        exact absurd ⟨u, hu, hv⟩ hn
    exact .pre (hb ▸ Holds.mem (n := 2) (s := gasS) .var (evalCap_of_res_ofc H hu0 hv))

/-- **`uncap` has a result at every value of Gas**, for every H. -/
theorem uncap_terminates_ofc {g : GroundTerm} (hg : (cH H).sortOf g = some gasS) :
    ∃ r, Eval (cH H) uncapS [g] r := by
  by_cases hex : ∃ u, (cH H).sortOf u = some gasS ∧ OvlFnRes (cH H) oCap [u] (some g)
  · obtain ⟨u, hu, h⟩ := hex
    exact ⟨_, uncap_of_res_ofc H hu hg h⟩
  · exact ⟨_, uncap_rest_ofc H hex⟩

/-- **`uncapCl` is coherent with itself**, for every H: two matches at one argument give G
values at which `capGas` has that argument as value, which are equal (`ovlFnInj_oft`). -/
theorem coh_uncapCl_ofc : Coherent (cH H) uncapCl uncapCl := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨u, g, rfl, hu0, hu, hr⟩ := uncap_applies_ofc H ha
  obtain ⟨u', g', he, hu0', hu', hr'⟩ := uncap_applies_ofc H ha'
  obtain ⟨rfl, -⟩ := List.cons.inj he
  have e : [u] = [u'] := ovlFnInj_oft H [u] [u'] g (sortsOf_one_ofc H hu) (sortsOf_one_ofc H hu') hr hr'
  obtain ⟨rfl, -⟩ := List.cons.inj e
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have : i = 0 := by simpa [uncapCl, varOccs] using hi
  subst this
  rw [hu0, hu0']

/-- **`capCl` is coherent with itself**, for every H: its pattern gives X the argument. -/
theorem coh_capCl_ofc : Coherent (cH H) capCl capCl := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨w, vs', rfl, hw, hn⟩ := PatVals.cons_inv ha.2.1
  cases PatVals.nil_inv hn
  obtain ⟨w', vs'', he, hw', -⟩ := PatVals.cons_inv ha'.2.1
  obtain ⟨rfl, -⟩ := List.cons.inj he
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have : i = 0 := by simpa [capCl, varOccs] using hi
  subst this
  rw [(PatVal.as_inv hw).2, (PatVal.as_inv hw').2]

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one_ofc {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree (cH H) fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

end Uncap

/-! ### The facts the deciders name -/

def callOrder : List Nat := [capN, uncapS]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `uncap`'s (`coh_uncapCl_ofc`). -/
theorem match_named : c.matchObligationsL = [(uncapS, 0)] := by decide +kernel
/-- The `[total]` function whose totality no decider confirms: `capN` (`total_capN_oft`). -/
theorem total_named : c.totalObligationsRP callOrder [] = [capN] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### `FnHyp` and consistency, for every H -/

/-- **`FnHyp` holds, for every H**: `capN` and `uncap` have a result at every argument list,
`capN` a value; one clause each; both clauses match independent; nothing owed; no open generator. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) := by
  have hmem : ∀ {fn}, fn ∈ (cH H).fns → fn = capNFn ∨ fn = uncapFn := fun h => by
    rw [fns_H H] at h
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf ht vs hvs => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecidedH H, openLaws_of_plain (c := cH H) noRaw⟩
  · rcases hmem hf with rfl | rfl
    · obtain ⟨v, hv⟩ := total_capN_oft H capNFn (lookupFn_H H) vs hvs
      exact ⟨_, hv⟩
    · obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
      cases sortsOf_inv_nil hws
      exact uncap_terminates_ofc H hw
  · rcases hmem hf with rfl | rfl
    · exact total_capN_oft H capNFn (lookupFn_H H) vs hvs
    · cases ht
  · rcases hmem hf with rfl | rfl
    · exact agree_one_ofc H rfl
    · exact agree_one_ofc H rfl
  · rcases hmem hf with rfl | rfl
    · obtain rfl : cl = capCl := by simpa [capNFn] using hcl
      exact ⟨coh_capCl_ofc H, fun h => absurd rfl h⟩
    · obtain rfl := uncap_clauses_ofc hcl
      exact ⟨coh_uncapCl_ofc H, fun h => absurd rfl h⟩

/-- **The clause `match_named` names is match independent, for every H.** -/
theorem matchUncap (H : HookParams) : MatchIndependent (cH H) uncapCl :=
  (fnHypH H).2.2.2.1 uncapFn (by rw [fns_H H]; exact .tail _ (.head _)) uncapCl (List.mem_singleton_self _)

/-- **`uncap(inj{N,Gas}(z))` is `inj{N,Gas}(z)`, for every H**: `capGas(inj z)` is `inj z`, by
`capN`. -/
theorem uncap_injZ (H : HookParams) : Eval (cH H) uncapS [injZ] (some injZ) :=
  uncap_of_res_ofc H (sort_injZ_H H) (sort_injZ_H H) (res_injZ_oft H)

/-- **`uncap(inf)` is the interpretation's value, for every H**: no value of `capGas` is `inf`
(`ovlFnDist_oft`), so the clause fails there. -/
theorem uncap_inf (H : HookParams) : Eval (cH H) uncapS [infT] ((cH H).fnRest uncapFn [infT]) :=
  uncap_rest_ofc H fun ⟨u, hu, h⟩ => ovlFnDist_oft H [u] [] (sortsOf_one_ofc H hu) rfl h

/-- **`uncap` has at each argument at most one result, for every H.** -/
theorem uncap_det (H : HookParams) {vs : List GroundTerm} {r r' : Option GroundTerm}
    (h : Eval (cH H) uncapS vs r) (h' : Eval (cH H) uncapS vs r') : r = r' :=
  fnDet_of_coherent (Faithful.CoherentAll_of (hyp_of_fnHyp (coreOKH H) (fnHypH H))) _ _ _ _ h h'

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

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

theorem nj90 : (trS U.ax90).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj96 : (trS U.ax96).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj99 : (trS U.ax99).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax90, U.ax96, U.ax99], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj90]; exact orTopBot_valid hD rfl
  · rw [nj96]; exact orTopBot_valid hD rfl
  · rw [nj99]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax92, U.ax93, U.ax94, U.ax95, U.ax97, U.ax98, U.ax101],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax92, U.ax93, U.ax94, U.ax95, U.ax97, U.ax98, U.ax101],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax100).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (100)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax100).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- Gas, a sort with generators. -/
def gas : Srt := 32

theorem gas_name : c.sortName gas = "Gas" := by decide +kernel

/-- Gas's generators in the order the text's no-junk sentence (91) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def gasTextGens : List KoreAML.Gen :=
  match (c.gens gas).map (Gen.toK c) with
  | [g0, g1, g2] => [g1, g0, g2]
  | gs => gs

/-- Gas's no-junk sentence (91) is the item over Gas's generators in the text's order. -/
theorem nojunk_gas_order : (trS U.ax91).pat = (KoreAML.Cons.noJunkItem (c.sortName gas) gasTextGens).pat := by
  decide +kernel
theorem nojunk_gas_members : gasTextGens.isPerm ((c.gens gas).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for Gas's no junk (91)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_gas_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax91).pat := by
  intro M _ I hI
  rw [nojunk_gas_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens gas).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_gas_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := gas)
    (show gas ∈ consSorts c by decide +kernel) (show (c.gens gas).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30,
   U.ax31, U.ax61, U.ax81, U.ax82, U.ax89]

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
  [U.ax102]

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

/-! ## Sentences of a function-overloaded symbol (57, 58, 59): weaker under
overloadFunction, listed apart

Γ holds each sentence at the arguments no overload of its generator covers only (Γ's items
`funUncItem`, `injUncItem`, `distUncItem`). This section states what holds for every H on every
text: the sentence entails that item in a model of Γ, the same-constructor and
different-constructors sentences with the `functional` sentence of their function-overloaded
generator. What a sentence says at covered arguments is the next section's, by hand. -/

/-- The sentences of `ovlFnApart`, in text order. -/
noncomputable def ovlFnText : List AxiomDecl :=
  [U.ax57, U.ax58, U.ax59]

theorem ovlfn_index : ovlFnText.map (·.index) = ovlFnApart := by decide +kernel

/-- The generator `LblcapGas`. -/
def ovlFnGen0 : Gen := .ctor ⟨390, [32], 32⟩

/-- The generator `Lblinf`. -/
def ovlFnGen1 : Gen := .ctor ⟨386, [], 32⟩

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

/-- Sentence 59 is a different-constructors sentence of `LblcapGas` and `Lblinf` of Gas, joint with the `functional` sentence 57. -/
theorem ovlfn_text_59 : tieOvlFnDistAtB c 32 ovlFnGen0 ovlFnGen1 U.ax59.ax = true := by decide +kernel
theorem ovlfn_trS_59 : (trS U.ax59).pat = (trAxiom [] [] U.ax59).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H (in one of the two orders). -/
theorem ovlfn_item_in_gamma_59 (H : HookParams) :
    (∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∨
    (∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) :=
  tieOvlFnDist_item_withHooks ovlfn_text_59 H

/-- **In a model of Γ, sentence 59 with sentence 57 entails that item**, in both orders, for every H. -/
theorem ovlfn_entails_item_59 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax57).pat) (h : I ⊧ᴵ (trS U.ax59).pat) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) := by
  rw [ovlfn_trS_57] at hf
  rw [ovlfn_trS_59] at h
  have hfa := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at hfa
  exact tieOvlFnDist_weaker_Γ hI (gf := ovlFnGen0) (.inl rfl) hfa.1.2
    ((tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_59) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _ _

/-! ## Sentences of a function-overloaded symbol: the covered part (by hand) -/

/- `capGas : Gas → Gas` overloads the function `capN : N → N`, N below Gas, and `capN(z)` is `z`.
The one value list `capN` covers is `[inj{N, Gas}(z)]` (`cov_inv_oft`: N holds `z` only), where the
application `capGas(inj z)` has the value `inj z` (`res_injZ_oft`). So, for every H:
- `capN` has a value at every covered value list (`ovlFnTotal_oft`), and the `functional` sentence
  of `capGas` (57) holds at values (`ovlfn_at_values_57`);
- two value lists at which `capGas` has one value are equal (`ovlFnInj_oft`: one covered list, a
  covered application's value is an injection and an uncovered one's the raw application), and the
  same-constructor sentence (58) holds at values (`ovlfn_at_values_58`);
- no value of an application of `capGas` is `inf` (`ovlFnDist_oft`), and the different-constructors
  sentence of `capGas` and `inf` (59) holds at values (`ovlfn_at_values_59`).
Each is in every model of `Γc`, at every valuation sending the sentence's variables to values'
elements (`EntailsAtValuesΓc`), with `FnHyp` proved for every H (`fnHypH`). -/

kernel_rfl inf_H : ∀ H : HookParams, lookupSig (cH H).ctorSigs infSig.name = some infSig

theorem fun_shape_oft (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax57.ax = true := by
  have h := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem inj_shape_oft (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax58.ax = true := by
  have h := (tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_58
  simp only [tieOvlFnInjAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem dist_shape_oft (H : HookParams) :
    tieOvlFnDistShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) (Gen.toK (cH H) (.ctor infSig))
      U.ax59.ax = true := by
  have h := (tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_59
  simp only [tieOvlFnDistAtB, Bool.and_eq_true] at h
  exact h.1.2

/-- **The `functional` sentence of `capGas` (57) holds at values, for every H**, in every model of
`Γc`. -/
theorem ovlfn_at_values_57 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax57 (trS U.ax57).pat := by
  rw [ovlfn_trS_57]
  exact ovlFnTotal_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnTotal_oft H) (fun_shape_oft H)

/-- **The same-constructor sentence of `capGas` (58) holds at values, for every H**, in every model
of `Γc`. -/
theorem ovlfn_at_values_58 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax58 (trS U.ax58).pat := by
  rw [ovlfn_trS_58]
  exact ovlFnInj_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnInj_oft H) (inj_shape_oft H)

/-- **The different-constructors sentence of `capGas` and `inf` (59) holds at values, for every H**,
in every model of `Γc`. -/
theorem ovlfn_at_values_59 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax59 (trS U.ax59).pat := by
  rw [ovlfn_trS_59]
  exact ovlFnDist_atValues (coreOKH H) (fnHypH H) (lookup_H H) (inf_H H) rfl (ovlFnDist_oft H) (dist_shape_oft H)

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


/-! ## Function equations (33 sentences) and priority equations (0 sentences)

Γ's item 1 (sentence 156) is not its sentence (`un<j>_differs`), and no reading here gives it from
the sentence or the sentence from it: the sentence is uncovered, `fns_entailed` and `fns_from_text`
leave it out, and the premise set of `gamma_from` holds Γ's item there.

Every other item is the translation of its function sentence (`shape`). -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

/-- Γ's item 1 (sentence 156): no reading here ties it. -/
noncomputable def unItem1 : P := (TiePair.gammaPats c).getD 1 ⊥
theorem unItem1_at : (TiePair.gammaPats c)[1]? = some unItem1 := by decide +kernel
kernel_rfl fnText_at1 : fnText[1]? = some U.ax156
/-- **Γ's item 1 is not the text's sentence 156** (kernel): the sentence is uncovered. -/
theorem un1_differs : unItem1 ≠ (trS U.ax156).pat := by decide +kernel

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 1. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 1 unItem1

/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def pairSetAt : List Nat := [1]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have h1 := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_map, hj]
  rfl

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the untied ones (items 1), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([1] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item but the untied ones (items 1) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([1] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h1 : j = 1
  · subst h1; simp at hu
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to
Γ's through their sentences, the untied ones as Γ's own), Γ's rule items and the five parts Γ defines by predicates
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
    ∀ ad ∈ [U.ax90, U.ax96, U.ax99], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax92, U.ax93, U.ax94, U.ax95, U.ax97, U.ax98, U.ax101],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax100).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 49 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax49).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)
theorem ovleq_entailed_c (H : HookParams) : ∀ ad ∈ ovlEqText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (ovleq_entailed H ad had)
/-- **Over `Γc`, sentence 57 entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/
theorem ovlfn_entails_item_57_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) (h : I ⊧ᴵ (trS U.ax57).pat) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  ovlfn_entails_item_57 H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)) h
/-- **Over `Γc`, sentence 58 with sentence 57 entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/
theorem ovlfn_entails_item_58_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) (hf : I ⊧ᴵ (trS U.ax57).pat) (h : I ⊧ᴵ (trS U.ax58).pat) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  ovlfn_entails_item_58 H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)) hf h
/-- **Over `Γc`, sentence 59 with sentence 57 entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/
theorem ovlfn_entails_item_59_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) (hf : I ⊧ᴵ (trS U.ax57).pat) (h : I ⊧ᴵ (trS U.ax59).pat) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) :=
  ovlfn_entails_item_59 H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)) hf h

end KCore.TieE5OvlFunClause

#check @KCore.TieE5OvlFunClause.noRaw
#check @KCore.TieE5OvlFunClause.readsConfined_c
#check @KCore.TieE5OvlFunClause.userAxioms_eq
#check @KCore.TieE5OvlFunClause.coreOK
#check @KCore.TieE5OvlFunClause.account
#check @KCore.TieE5OvlFunClause.account_sizes
#check @KCore.TieE5OvlFunClause.account_classes
#check @KCore.TieE5OvlFunClause.account_absent
#check @KCore.TieE5OvlFunClause.absent_closed
#check @KCore.TieE5OvlFunClause.absent_proj_below_c
#check @KCore.TieE5OvlFunClause.absent_proj_below
#check @KCore.TieE5OvlFunClause.lists_in_account
#check @KCore.TieE5OvlFunClause.attrs_agree
#check @KCore.TieE5OvlFunClause.sig_origin_but_next
#check @KCore.TieE5OvlFunClause.decls_entailed
#check @KCore.TieE5OvlFunClause.consistent
#check @KCore.TieE5OvlFunClause.total_named
#check @KCore.TieE5OvlFunClause.fnHypH
#check @KCore.TieE5OvlFunClause.text_nextless
#check @KCore.TieE5OvlFunClause.nojunk_trivial_entailed
#check @KCore.TieE5OvlFunClause.nojunk_items_entailed
#check @KCore.TieE5OvlFunClause.nojunk_kitem_entailed
#check @KCore.TieE5OvlFunClause.cons_entailed
#check @KCore.TieE5OvlFunClause.ovleq_account
#check @KCore.TieE5OvlFunClause.ovleq_entailed
#check @KCore.TieE5OvlFunClause.ovlfn_index
#check @KCore.TieE5OvlFunClause.ovlfn_text_57
#check @KCore.TieE5OvlFunClause.ovlfn_item_in_gamma_57
#check @KCore.TieE5OvlFunClause.ovlfn_entails_item_57
#check @KCore.TieE5OvlFunClause.ovlfn_text_58
#check @KCore.TieE5OvlFunClause.ovlfn_item_in_gamma_58
#check @KCore.TieE5OvlFunClause.ovlfn_entails_item_58
#check @KCore.TieE5OvlFunClause.ovlfn_text_59
#check @KCore.TieE5OvlFunClause.ovlfn_item_in_gamma_59
#check @KCore.TieE5OvlFunClause.ovlfn_entails_item_59
#check @KCore.TieE5OvlFunClause.ovlfn_at_values_57
#check @KCore.TieE5OvlFunClause.ovlfn_at_values_58
#check @KCore.TieE5OvlFunClause.ovlfn_at_values_59
#check @KCore.TieE5OvlFunClause.idem_refuted
#check @KCore.TieE5OvlFunClause.nojunk_gas_order
#check @KCore.TieE5OvlFunClause.nojunk_gas_members
#check @KCore.TieE5OvlFunClause.nojunk_gas_entailed
#check @KCore.TieE5OvlFunClause.gammaCl_eq
#check @KCore.TieE5OvlFunClause.decls_entailed_c
#check @KCore.TieE5OvlFunClause.nojunk_trivial_entailed_c
#check @KCore.TieE5OvlFunClause.nojunk_items_entailed_c
#check @KCore.TieE5OvlFunClause.nojunk_kitem_entailed_c
#check @KCore.TieE5OvlFunClause.cons_entailed_c
#check @KCore.TieE5OvlFunClause.idem_refuted_c
#check @KCore.TieE5OvlFunClause.ovleq_entailed_c
#check @KCore.TieE5OvlFunClause.ovlfn_entails_item_57_c
#check @KCore.TieE5OvlFunClause.ovlfn_entails_item_58_c
#check @KCore.TieE5OvlFunClause.ovlfn_entails_item_59_c
#print axioms KCore.TieE5OvlFunClause.noRaw
#print axioms KCore.TieE5OvlFunClause.readsConfined_c
#print axioms KCore.TieE5OvlFunClause.userAxioms_eq
#print axioms KCore.TieE5OvlFunClause.coreOK
#print axioms KCore.TieE5OvlFunClause.account
#print axioms KCore.TieE5OvlFunClause.account_sizes
#print axioms KCore.TieE5OvlFunClause.account_classes
#print axioms KCore.TieE5OvlFunClause.account_absent
#print axioms KCore.TieE5OvlFunClause.absent_closed
#print axioms KCore.TieE5OvlFunClause.absent_proj_below_c
#print axioms KCore.TieE5OvlFunClause.absent_proj_below
#print axioms KCore.TieE5OvlFunClause.lists_in_account
#print axioms KCore.TieE5OvlFunClause.attrs_agree
#print axioms KCore.TieE5OvlFunClause.sig_origin_but_next
#print axioms KCore.TieE5OvlFunClause.decls_entailed
#print axioms KCore.TieE5OvlFunClause.consistent
#print axioms KCore.TieE5OvlFunClause.total_named
#print axioms KCore.TieE5OvlFunClause.fnHypH
#print axioms KCore.TieE5OvlFunClause.text_nextless
#print axioms KCore.TieE5OvlFunClause.nojunk_trivial_entailed
#print axioms KCore.TieE5OvlFunClause.nojunk_items_entailed
#print axioms KCore.TieE5OvlFunClause.nojunk_kitem_entailed
#print axioms KCore.TieE5OvlFunClause.cons_entailed
#print axioms KCore.TieE5OvlFunClause.ovleq_account
#print axioms KCore.TieE5OvlFunClause.ovleq_entailed
#print axioms KCore.TieE5OvlFunClause.ovlfn_index
#print axioms KCore.TieE5OvlFunClause.ovlfn_text_57
#print axioms KCore.TieE5OvlFunClause.ovlfn_item_in_gamma_57
#print axioms KCore.TieE5OvlFunClause.ovlfn_entails_item_57
#print axioms KCore.TieE5OvlFunClause.ovlfn_text_58
#print axioms KCore.TieE5OvlFunClause.ovlfn_item_in_gamma_58
#print axioms KCore.TieE5OvlFunClause.ovlfn_entails_item_58
#print axioms KCore.TieE5OvlFunClause.ovlfn_text_59
#print axioms KCore.TieE5OvlFunClause.ovlfn_item_in_gamma_59
#print axioms KCore.TieE5OvlFunClause.ovlfn_entails_item_59
#print axioms KCore.TieE5OvlFunClause.ovlfn_at_values_57
#print axioms KCore.TieE5OvlFunClause.ovlfn_at_values_58
#print axioms KCore.TieE5OvlFunClause.ovlfn_at_values_59
#print axioms KCore.TieE5OvlFunClause.idem_refuted
#print axioms KCore.TieE5OvlFunClause.nojunk_gas_order
#print axioms KCore.TieE5OvlFunClause.nojunk_gas_members
#print axioms KCore.TieE5OvlFunClause.nojunk_gas_entailed
#print axioms KCore.TieE5OvlFunClause.gammaCl_eq
#print axioms KCore.TieE5OvlFunClause.decls_entailed_c
#print axioms KCore.TieE5OvlFunClause.nojunk_trivial_entailed_c
#print axioms KCore.TieE5OvlFunClause.nojunk_items_entailed_c
#print axioms KCore.TieE5OvlFunClause.nojunk_kitem_entailed_c
#print axioms KCore.TieE5OvlFunClause.cons_entailed_c
#print axioms KCore.TieE5OvlFunClause.idem_refuted_c
#print axioms KCore.TieE5OvlFunClause.ovleq_entailed_c
#print axioms KCore.TieE5OvlFunClause.ovlfn_entails_item_57_c
#print axioms KCore.TieE5OvlFunClause.ovlfn_entails_item_58_c
#print axioms KCore.TieE5OvlFunClause.ovlfn_entails_item_59_c
#check @KCore.TieE5OvlFunClause.fns_account
#check @KCore.TieE5OvlFunClause.un1_differs
#check @KCore.TieE5OvlFunClause.shape
#check @KCore.TieE5OvlFunClause.fns_entailed
#check @KCore.TieE5OvlFunClause.fns_from_text
#check @KCore.TieE5OvlFunClause.fn_prios
#check @KCore.TieE5OvlFunClause.gamma_from
#print axioms KCore.TieE5OvlFunClause.fns_account
#print axioms KCore.TieE5OvlFunClause.un1_differs
#print axioms KCore.TieE5OvlFunClause.shape
#print axioms KCore.TieE5OvlFunClause.fns_entailed
#print axioms KCore.TieE5OvlFunClause.fns_from_text
#print axioms KCore.TieE5OvlFunClause.fn_prios
#print axioms KCore.TieE5OvlFunClause.gamma_from
