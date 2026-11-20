/-
  The tie (C14) on `f2-examples/e3-eq-exists-ml-under-app.kompile.kore`, the kompiled text of construct fixture e3-eq-exists-ml-under-app
  (`test/constructs/fixtures/e3-eq-exists-ml-under-app`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-eq-exists-ml-under-app`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3EqExistsMlUnderApp.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate (`wfFailing`).
  - The account: the class lists partition the 179 sentences of the user module E3-EQ-EXISTS-ML-UNDER-APP, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_parts`, `attrs_prios_false`, `attrs_prios_but`: the attributes the translation does not
    read agree with `defn` but for the priorities (`attrsAgree` is false by `prios` alone): an
    equation read as several clauses states one priority, which `prios` counts once against the
    clauses counted each. With every clause of such a run but its first left out
    (`AttrsAgree.priosBut`) the priorities agree, and each clause left out is aligned with the run's
    sentence at the priority that sentence states (Lblf 1: sentence 133, `prios_split_at1`, Lblf 2:
    sentence 133, `prios_split_at2`; `fn_prios` states it of every clause). That is a fact of
    priorities: the clause's item is not tied to its sentence, which is uncovered.
  - `sig_origin_but_next`: each of the 205 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the totality of the `[total]` function `f` (`total_named`); the agreement of `f`
    (`agree_named`); `FnHyp` itself: a clause's predicate is not `\top` (`Semantics.clausesPreTop`
    false), so the named facts do not give it and `kcore gen --core` takes it as the hypothesis of its
    statements, which no decider confirms. The consistency section, written by hand, proves that `Γc`
    with the step's closure has a model for every H (`consistent`), through `FnHyp` for every H
    (`fnHypH`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0, 1, 2 is the translation of one sentence (`shape`), so
    Γ entails it (`fns_entailed`). Items 0 to 2 are the 3 clauses sentence 133 is read as (`fnPins`:
    the alignment holds the sentence at each of those positions, `TiePair.fnTextMany`, `fnPins_ok`,
    `fnText_all`). No such item is its sentence (`sp<j>_differs`); the sentence gives an item only
    with the function's functional sentence, and Γ gives the sentence only from all the items of the
    run together, which no form here states: the sentence is `uncovered`, and `fns_entailed` and
    `fns_from_text` leave those items out. `fns_from_text` (the converse), `fn_prios` (the
    priorities the sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (48): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    items 0, 1, 2 (the clauses one sentence is read as, whose sentence is uncovered), Γ's rule
    items, the five parts Γ defines by predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (26);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsMlUnderApp

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-ml-under-app.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-under-app.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-under-app.kompile.kore" module "E3-EQ-EXISTS-ML-UNDER-APP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-EQ-EXISTS-ML-UNDER-APP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 179 := by decide +kernel

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
  [("function equation", [133, 134, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
      155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 81, 82]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [90, 91, 92, 93, 94, 95, 96, 97, 98, 99]),
   ("function functional", [62, 63, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 37, 38, 39, 43, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
      61, 65, 80, 83, 84, 85, 86, 87, 88]),
   ("collection law", [40, 41, 42, 44, 45, 46, 47, 49, 50]),
   ("library", [108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
      126, 127, 128, 129, 130, 131, 132, 166, 167, 181]),
   ("set idempotence", [48]),
   ("set-variable lemma", [100, 101, 102, 103, 104, 105, 106, 107, 182]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 36, 64, 89, 135, 136, 137, 138, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
      179, 180])]

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
    [("function equation", 29), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 16), ("hooked functional", 32), ("collection law", 9), ("library", 28), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 21)] := by
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
  [(168, "Bool"), (169, "GeneratedCounterCell"), (170, "GeneratedCounterCellOpt"),
   (171, "GeneratedTopCell"), (172, "GeneratedTopCellFragment"), (173, "Int"), (174, "K"),
   (175, "KCell"), (176, "KCellOpt"), (177, "KItem"), (178, "List"), (179, "Map"), (180, "Set")]

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
  [(62, "function functional"), (63, "function functional"), (99, "no junk"),
   (100, "set-variable lemma"), (101, "set-variable lemma"), (102, "set-variable lemma"),
   (103, "set-variable lemma"), (104, "set-variable lemma"), (105, "set-variable lemma"),
   (106, "set-variable lemma"), (107, "set-variable lemma"), (110, "library"), (111, "library"),
   (114, "library"), (115, "library"), (117, "library"), (118, "library"), (121, "library"),
   (122, "library"), (125, "library"), (126, "library"), (130, "library"),
   (133, "function equation"), (134, "function equation"), (138, "no direction"),
   (182, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(133, "function equation")]

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn` but for the priorities**: constructors, functions,
hooks and collection symbols agree (`attrs_parts`), and `prios` is false (`attrs_prios_false`). -/
theorem attrs_parts : AttrsAgree.ctors kore defn.sem = true ∧ AttrsAgree.fns kore defn.sem = true ∧
    AttrsAgree.hooks kore defn.sem = true ∧ AttrsAgree.colls kore defn.sem = true := by decide +kernel
theorem attrs_prios_false : AttrsAgree.prios kore defn = false ∧ attrsAgree kore defn = false := by
  decide +kernel

/-- The clauses left out, by (function, position): of each run of clauses one equation is read as,
every clause but the first (the equation states one priority, the clauses are counted each). No
sentence is left out. -/
def priosOutCl : List (String × Nat) := [("Lblf", 1), ("Lblf", 2)]
def priosOutAx : List Nat := []

/-- **With those clauses left out of the clause side, the priorities agree**
(`AttrsAgree.priosBut`). Each clause of a run left out is aligned with the run's sentence at the
priority it states: `prios_split_at1`, `prios_split_at2`. -/
theorem attrs_prios_but : AttrsAgree.priosBut priosOutAx priosOutCl kore defn = true := by decide +kernel


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

theorem sig_sizes : (sigItems c).length = 205 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 94, 65, 4, 25) := by
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

/-! ## Consistency for every H: `f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))`, read by cases -/

/- The text's functions are `f` and `g`, both `[total]` (`ExUaH.read`). `g` has its one clause
`g(B) => notBool B`. `f` has the three clauses `Parse.exClauses` writes for the equation with the
binder moved to the top of the right side: at the literal b, `pre ⌈g(b)⌉ ∧ b = X` and `rhs g(b)`,
for b = true, false; and the last, `pre ¬∃B:Bool. (⌈g(B)⌉ ∧ B = X)`, `rhs g(true)`, `ens false`,
all of one priority. A clause's predicate is not `\top`, so `FnHyp` is shown here for every H
(`fnHypH`), by `fnHyp_of_decidedPre_withHooks`:
- Termination: `g` is placed before `f`, whose clauses apply it in their terms and predicates, and
  `g`'s clause applies a hook only (`preRank_named`).
- Totality of `f` (`total_named`; `g`'s the checker confirms, and it also follows here,
  `ExUaH.g_value`): a value of Bool is a literal x; `g(x)` is `notBool x`, so the clause of the
  literal x applies at x, its predicate `⌈g(x)⌉ ∧ x = x` true (`ExUaH.f_value`).
- Agreement of `f` (`agree_named`): two clauses that apply at one argument list are one clause.
  At a literal x, `g` of a literal has the one result `notBool` of it (`ExUaH.g_inv`), so the clause
  of the literal b applies only where `b = x`, and the last clause applies nowhere: B := x gives its
  binder's body (`ExUaH.applies`, `ExUaH.coherent`).
- No match independence, rule condition or clause condition is owed (`match_named`, `owed_rules`,
  `owed_clauses`), and the text has no open generator (`noRaw`).
So Γc with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).
`ExUaH` holds the proofs, over any semantics `d` that reads the clauses (`ExUaH.Reads`); the
statements after it are on `cH H`. -/

namespace ExUaH

def Fs : Sym := 384
def Gs : Sym := 385
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def notX : Term := .app boolNot [.var 0]

/-- A clause of f over `[X:Bool]`, of priority 50. -/
def clX (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs, ens, prio := 50, aside := false, pre }

/-- `⌈g(b)⌉ ∧ (b = X)`. -/
def preI (b : Bool) : Cond := .and (.ceil Srt.bool (.app Gs [litT b])) (.equals Srt.bool (litT b) (.var 0))
/-- `⌈g(B)⌉ ∧ (B = X)`, B the binder's variable, the index 1. -/
def bodyC : Cond := .and (.ceil Srt.bool (.app Gs [.var 1])) (.equals Srt.bool (.var 1) (.var 0))
def lastPre : Cond := .not (.ex Srt.bool bodyC)

def clI (b : Bool) : Clause := clX (.app Gs [litT b]) none (preI b)
def clL : Clause := clX (.app Gs [litT true]) (some (litT false)) lastPre
def clG : Clause := clX notX none .top

def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool, [clI true, clI false, clL], true⟩
def gFn : Fn := ⟨Gs, [Srt.bool], Srt.bool, [clG], true⟩

/-- **The reading**: the text's functions are `f` and `g`, with these clauses (kernel). -/
theorem read : c.fns = [fFn, gFn] := by kernel_rfl

theorem names : c.symName Fs = "Lblf" ∧ c.symName Gs = "Lblg" ∧ c.symName boolNot = "LblnotBool'Unds'" := by
  decide +kernel
theorem lookupF : c.lookupFn Fs = some fFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn Gs = some gFn := by rw [Semantics.lookupFn_eq]; rfl
theorem kinds : c.isCtor boolNot = false ∧ c.isCtor Gs = false ∧ c.isParam Gs = false ∧ c.isOvl Gs = false := by
  decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-- What the proofs read of a semantics: the kinds of `notBool` and `g`, the two functions, and
that the values of Bool are its literals. -/
structure Reads (d : Semantics) : Prop where
  notCtor : d.isCtor boolNot = false
  gCtor : d.isCtor Gs = false
  gParam : d.isParam Gs = false
  gOvl : d.isOvl Gs = false
  lkF : d.lookupFn Fs = some fFn
  lkG : d.lookupFn Gs = some gFn
  shapes : d.shapesOK = true

section Clause

variable {d : Semantics} {σ : Subst}

theorem notHook : isHook boolNot = true := by decide +kernel
theorem gHook : isHook Gs = false := by decide +kernel

theorem hook_inv {f : Sym} {ts : List Term} {r : Option GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = true) (h : EvalTerm d σ (.app f ts) r) :
    ∃ rs, EvalTerms d σ ts rs ∧ (∀ vs, allSome rs = some vs → d.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | hook _ _ hts hh hund => cases ht; exact ⟨_, hts, hh, hund⟩
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | param _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hk] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | ovl _ ho _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | _ => cases ht

theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

theorem notX_mk (hc : d.isCtor boolNot = false) {x : Bool} (h0 : σ.lookup 0 = some (bool x)) :
    EvalTerm d σ notX (some (bool (!x))) :=
  .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot x)
    (fun hn => by rw [h0] at hn; cases hn)

theorem notX_inv (hc : d.isCtor boolNot = false) {x : Bool} (h0 : σ.lookup 0 = some (bool x))
    {r : Option GroundTerm} (h : EvalTerm d σ notX r) : r = some (bool (!x)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  have := hh [bool x] (by rw [h0]; rfl)
  rw [hookNot] at this
  exact (Option.some.inj this).symm

/-- The substitution that gives X the value v. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sorted (x : Bool) : d.WellSorted [Srt.bool] (sg (bool x)) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨bool x, rfl, rmS_sortOf_bool d _⟩
  | succ i => simp at hs

theorem sg_match (v : GroundTerm) : PatVals d (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem match0 {vs : List GroundTerm} (h : PatVals d σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- **`g(b)` is `notBool b`**, by its one clause. -/
theorem g_value (R : Reads d) (b : Bool) : Eval d Gs [bool b] (some (bool !b)) :=
  .clause (cl := clG) R.lkG (List.mem_singleton_self _) (sg_sorted b) (sg_match _)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [gFn, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (notX_mk R.notCtor rfl) (fun t ht => nomatch ht) .top

/-- **`g(b)` has no other result.** -/
theorem g_inv (R : Reads d) {b : Bool} {r : Option GroundTerm} (h : Eval d Gs [bool b] r) :
    r = some (bool !b) := by
  have hcl : (d.lookupFn Gs).bind (·.clauses[0]?) = some clG := by rw [R.lkG]; rfl
  obtain ⟨σ', -, hm, hr⟩ := Eval.inv_of_clause_bind (σ := sg (bool b)) hcl
    (fun j hj cl' h' _ => by
      rw [R.lkG] at h'
      match j, hj, h' with
      | j + 1, _, h' => simp [gFn] at h')
    rfl (sg_sorted b) (sg_match _) h
  obtain ⟨v, hv, hl⟩ := match0 hm
  cases hv
  exact notX_inv R.notCtor hl hr

/-- `g(t)` is `notBool b` where t has the one result b. -/
theorem callG_mk (R : Reads d) {t : Term} {b : Bool} (ht : EvalTerm d σ t (some (bool b))) :
    EvalTerm d σ (.app Gs [t]) (some (bool !b)) :=
  .call (vs := [bool b]) R.gCtor gHook (.cons ht .nil) rfl (g_value R b) R.gParam

theorem callG_inv (R : Reads d) {t : Term} {b : Bool} (ht : ∀ r0, EvalTerm d σ t r0 → r0 = some (bool b))
    {r : Option GroundTerm} (h : EvalTerm d σ (.app Gs [t]) r) : r = some (bool !b) := by
  obtain ⟨rs, hts, hres⟩ := EvalTerm.call_inv R.gCtor gHook R.gParam R.gOvl h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := ht _ h1
  rcases hres with ⟨vs, hvs, hf⟩ | ⟨hn, -⟩
  · cases hvs
    exact g_inv R hf
  · cases hn

/-- The truth value of `b = x`. -/
def bEq (b x : Bool) : Bool := sameResult (some (bool b)) (some (bool x))

theorem bEq_iff (b x : Bool) : bEq b x = true ↔ b = x := by cases b <;> cases x <;> decide

theorem preI_mk (R : Reads d) {x : Bool} (h0 : σ.lookup 0 = some (bool x)) (b : Bool) :
    Holds d 1 σ (preI b) (bEq b x) := by
  have hx : EvalTerm d σ (.var 0) (some (bool x)) := h0 ▸ EvalTerm.var
  have h := Holds.and (n := 1) (Holds.ceil (s := Srt.bool) (callG_mk R (σ := σ) (EvalTerm.dv (s := Srt.bool) (lit := .bool b))))
    (Holds.equals (s := Srt.bool) (EvalTerm.dv (c := d) (σ := σ) (s := Srt.bool) (lit := .bool b)) hx)
  exact h

theorem preI_inv (R : Reads d) {x b r : Bool} (h0 : σ.lookup 0 = some (bool x)) (h : Holds d 1 σ (preI b) r) :
    r = bEq b x := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [callG_inv R (fun _ h => EvalTerm.dv_inv h) e1, EvalTerm.dv_inv e2, EvalTerm.var_inv e3, h0]
        rfl

/-- The binder's body at a σ' giving B the value b' and X the value x is `b' = x`. -/
theorem bodyC_inv (R : Reads d) {σ' : Subst} {x b' r : Bool} (h1 : σ'.lookup 1 = some (bool b'))
    (h0 : σ'.lookup 0 = some (bool x)) (h : Holds d 2 σ' bodyC r) : r = bEq b' x := by
  cases h with
  | and ha hb =>
    cases ha with
    | ceil e1 =>
      cases hb with
      | equals e2 e3 =>
        rw [callG_inv R (fun _ h => (EvalTerm.var_inv h).trans h1) e1, EvalTerm.var_inv e2, EvalTerm.var_inv e3,
          h1, h0]
        rfl

/-- The extension of σ by B := x. -/
def ext (x : Bool) (σ : Subst) : Subst := (1, bool x) :: σ

theorem ext_extends (x : Bool) (σ : Subst) : Extends d 1 [Srt.bool] σ (ext x σ) := by
  refine ⟨fun i hi => ?_, fun j s hs => ?_⟩
  · have : i = 0 := by omega
    subst this; rfl
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨bool x, rfl, rmS_sortOf_bool d _⟩
    | succ j => simp at hs

/-- **The last clause's premise is false where X is a literal**: B := x gives the body. -/
theorem last_inv (R : Reads d) {x r : Bool} (h0 : σ.lookup 0 = some (bool x)) (h : Holds d 1 σ lastPre r) :
    r = false := by
  cases h with
  | not h =>
    cases h with
    | ex g hb hr =>
      have hg := bodyC_inv R (σ' := ext x σ) rfl h0 (hb (ext x σ) (ext_extends x σ))
      have h1 : g (ext x σ) = true := by rw [hg]; exact (bEq_iff x x).mpr rfl
      have := hr.mpr ⟨_, ext_extends x σ, h1⟩
      subst this; rfl

theorem clX_of {cl : Clause} (h : cl ∈ fFn.clauses) : cl = clI true ∨ cl = clI false ∨ cl = clL := by
  simpa [fFn] using h

theorem prio_none {vs : List GroundTerm} {cl : Clause} (hcl : cl ∈ fFn.clauses) :
    ∀ cl' ∈ fFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails d vs cl' := by
  intro cl' hcl' _ hlt
  rcases clX_of hcl with rfl | rfl | rfl <;> rcases clX_of hcl' with rfl | rfl | rfl <;>
    exact absurd hlt (by decide)

theorem clI_mem (b : Bool) : clI b ∈ fFn.clauses := by
  cases b <;> simp [fFn]

/-- **`f(x)` is `g(x)`, that is `notBool x`**, by the clause of the literal x. -/
theorem f_value (R : Reads d) (x : Bool) : Eval d Fs [bool x] (some (bool !x)) := by
  have hp := preI_mk R (σ := sg (bool x)) (x := x) rfl x
  rw [(bEq_iff x x).mpr rfl] at hp
  exact .clause (cl := clI x) R.lkF (clI_mem _) (sg_sorted x) (sg_match _)
    (fun t ht => nomatch ht) hp (prio_none (clI_mem _)) rfl (callG_mk R .dv) (fun t ht => nomatch ht) .top

/-- **A clause of f that applies at an argument list**: the argument is a literal x, X is x, and
the clause is that of the literal x. -/
theorem applies (R : Reads d) {cl : Clause} (hcl : cl ∈ fFn.clauses) {vs : List GroundTerm}
    (h : cl.AppliesAt d σ vs) : ∃ x, vs = [bool x] ∧ σ.lookup 0 = some (bool x) ∧ cl = clI x := by
  obtain ⟨hws, hm, -, hpre⟩ := h
  have hp : cl.pats = [.var 0] := by rcases clX_of hcl with rfl | rfl | rfl <;> rfl
  rw [hp] at hm
  obtain ⟨v, rfl, hl⟩ := match0 hm
  have h0 : ∃ w, σ.lookup 0 = some w ∧ d.sortOf w = some Srt.bool := by
    rcases clX_of hcl with rfl | rfl | rfl <;> exact hws 0 (by decide) Srt.bool rfl
  obtain ⟨w, hw, hwsrt⟩ := h0
  rw [hl] at hw
  obtain rfl := Option.some.inj hw
  obtain ⟨x, rfl⟩ := shape_bool R.shapes hwsrt
  refine ⟨x, rfl, hl, ?_⟩
  rcases clX_of hcl with rfl | rfl | rfl
  · have := (bEq_iff true x).mp (preI_inv R hl hpre).symm
    rw [← this]
  · have := (bEq_iff false x).mp (preI_inv R hl hpre).symm
    rw [← this]
  · exact absurd (last_inv R hl hpre) (by simp)

/-- **Any two clauses of f are coherent**: where both apply at one argument list they are one
clause, whose right side holds no variable. -/
theorem coherent (R : Reads d) {cl cl' : Clause} (hcl : cl ∈ fFn.clauses) (hcl' : cl' ∈ fFn.clauses) :
    Coherent d cl cl' := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, hv, -, rfl⟩ := applies R hcl ha
  obtain ⟨x', hv', -, rfl⟩ := applies R hcl' ha'
  rw [hv] at hv'
  have : x' = x := by cases x <;> cases x' <;> first | rfl | exact absurd hv' (by decide)
  subst this
  left
  refine ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  cases x' <;> simp [clI, clX, litT, varOccs, varOccsList] at hi

end Clause

end ExUaH

/-! ### The facts the deciders name -/

def callOrder : List Nat := [385, 384]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
/-- No clause applies, in a term or its predicate, a function placed after it. -/
theorem preRank_named : c.preRankObligationsFP callOrder = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [384] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [384] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- A clause's predicate is not `\top`. -/
theorem clausesPreTop_false : c.clausesPreTop = false := by decide +kernel

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

/-! ### `FnHyp` and consistency, for every H -/

theorem readsH (H : HookParams) : ExUaH.Reads (cH H) :=
  ⟨ExUaH.kinds.1, ExUaH.kinds.2.1, ExUaH.kinds.2.2.1, ExUaH.kinds.2.2.2,
   by rw [Semantics.lookupFn_withHooks]; exact ExUaH.lookupF,
   by rw [Semantics.lookupFn_withHooks]; exact ExUaH.lookupG, ExUaH.shapes⟩

theorem matchOblH (H : HookParams) : Det.MatchObligationsL (cH H) := by
  intro p hp
  rw [Det.Semantics.matchObligationsL_withHooks, match_named] at hp
  cases hp

theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by
    intro p hp
    rw [Semantics.owedClauses_withHooks, owed_clauses] at hp
    cases hp)⟩

/-- **`f` and `g` are total under every H**: at a literal x, `g(x)` is `notBool x` and the clause
of f of the literal x applies. -/
theorem totalsH (H : HookParams) : ∀ fn ∈ c.fns, fn.total = true → Total (cH H) fn.label := by
  intro fn hfn _
  rw [ExUaH.read] at hfn
  intro fn' hfn' vs hvs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · rw [show ExUaH.fFn.label = ExUaH.Fs from rfl, (readsH H).lkF] at hfn'
    cases hfn'
    obtain ⟨v, rfl, hv⟩ := sortsOf_one hvs
    obtain ⟨x, rfl⟩ := shape_bool (readsH H).shapes hv
    exact ⟨_, ExUaH.f_value (readsH H) x⟩
  · rw [show ExUaH.gFn.label = ExUaH.Gs from rfl, (readsH H).lkG] at hfn'
    cases hfn'
    obtain ⟨v, rfl, hv⟩ := sortsOf_one hvs
    obtain ⟨x, rfl⟩ := shape_bool (readsH H).shapes hv
    exact ⟨_, ExUaH.g_value (readsH H) x⟩

/-- **The clauses of `f` agree under every H** (the function `agree_named` names). -/
theorem agreeH (H : HookParams) :
    ∀ f ∈ c.agreeObligationsI, ∀ fn, (cH H).lookupFn f = some fn → ClausesAgree (cH H) fn := by
  intro f hf fn hfn
  rw [agree_named] at hf
  obtain rfl := List.mem_singleton.mp hf
  rw [show (384 : Sym) = ExUaH.Fs from rfl, (readsH H).lkF] at hfn
  cases hfn
  intro cl cl' hp _
  obtain ⟨h1, h2⟩ := mem_of_mem_pairs hp
  exact ⟨ExUaH.coherent (readsH H) h1 h2, ExUaH.coherent (readsH H) h2 h1⟩

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [preRank_named] at hg; cases hg)
    (totalsH H) (agreeH H) (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **`f(b) = notBool b`, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) ExUaH.Fs [bool b] (some (bool (!b))) :=
  ExUaH.f_value (readsH H) b

/-- **Γc with the step's closure has a model, for every H.** -/
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
theorem nj95 : (trS U.ax95).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj98 : (trS U.ax98).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax90, U.ax95, U.ax98], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj90]; exact orTopBot_valid hD rfl
  · rw [nj95]; exact orTopBot_valid hD rfl
  · rw [nj98]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax91, U.ax92, U.ax93, U.ax94, U.ax96, U.ax97],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax91, U.ax92, U.ax93, U.ax94, U.ax96, U.ax97],
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax81, U.ax82]

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

theorem idem_pattern : U.ax48.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax48).pat = (trAxiom [] [] U.ax48).pat := by decide +kernel

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
theorem idem_vars : (U.ax48.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax48.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax48.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 48 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax48).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax48.ax.sortVars U.ax48.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax48.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax48.ax.pattern).eraseDups,
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


/-! ## Function equations (29 sentences) and priority equations (0 sentences)

One equation read as several clauses (items 0 to 2, sentence 133): the equation's right side holds
alternatives (an `\or`, or an `\exists` over a Bool, read case by case), and the reading gives a
clause for each alternative, with its condition, and one where none applies. The alignment holds the
sentence at each of the clauses' positions (`fnPins`, `TiePair.fnTextMany`: a pinned position holds
its sentence, every other position the first sentence of its function and priority; `fnPins_ok`,
`fnText_all`). No such item is its sentence (`sp<j>_differs`). The sentence gives an item only
together with the function's functional sentence (where an alternative applies, the sentence gives
the application every element that alternative holds, and the item one element), and the items give
the sentence only all together; no form here states either, so the sentence is uncovered,
`fns_entailed` and `fns_from_text` leave its items out, and the premise set of `gamma_from` holds
Γ's items there.

Every other item is the translation of its function sentence (`shape`). -/

/-- The pins of the alignment, `(item, sentence index)`: each clause of a run one equation is read
as, at that equation. -/
def fnPins : List (Nat × Nat) := [(0, 133), (1, 133), (2, 133)]

/-- The text sentences of Γ's equations, in `fnItems`'s order: a pinned position holds its
sentence, every other one the first sentence of its head symbol and priority that no earlier
position took (`TiePair.fnTextMany`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnTextO : List (Option AxiomDecl) := TiePair.fnTextMany c U.all fnPins

/-- **Each pin names a clause position and an equation of that clause's function, no position
twice, the positions of one sentence consecutive** (kernel). -/
theorem fnPins_ok : TiePair.pinsOK c U.all fnPins = true := by decide +kernel

/-- **Every position holds a sentence, one per item of `fnItems`** (kernel). -/
theorem fnText_all : TiePair.manyAllSomeB fnTextO = true ∧ TiePair.manyLengthB c fnTextO = true := by
  decide +kernel

noncomputable def fnText : List AxiomDecl := fnTextO.filterMap id

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once, a pinned sentence at each position of its run. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm
      (fnText.map (·.index)).eraseDups = true := by
  decide +kernel

/-- Γ's item 0, the clause 0 of the 3 that sentence 133 is read as. -/
noncomputable def spItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem spItem0_at : (TiePair.gammaPats c)[0]? = some spItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax133
/-- **Γ's item 0 is not the text's sentence 133** (kernel): the sentence is uncovered. -/
theorem sp0_differs : spItem0 ≠ (trS U.ax133).pat := by decide +kernel

/-- Γ's item 1, the clause 1 of the 3 that sentence 133 is read as. -/
noncomputable def spItem1 : P := (TiePair.gammaPats c).getD 1 ⊥
theorem spItem1_at : (TiePair.gammaPats c)[1]? = some spItem1 := by decide +kernel
kernel_rfl fnText_at1 : fnText[1]? = some U.ax133
/-- **Γ's item 1 is not the text's sentence 133** (kernel): the sentence is uncovered. -/
theorem sp1_differs : spItem1 ≠ (trS U.ax133).pat := by decide +kernel

/-- **The clause 1 of `Lblf`, which `attrs_prios_but` leaves out, is Γ's item 1**, aligned with
sentence 133, and its priority is the one that sentence states (kernel). -/
theorem prios_split_at1 : ((c.allFns.takeWhile (c.symName ·.label != "Lblf")).map (·.clauses.length)).sum + 1 = 1 ∧
    (fnText[1]?).map (·.index) = some 133 ∧
    (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))[1]? = some (AttrsAgree.prioOf U.ax133.ax.attributes) := by
  decide +kernel

/-- Γ's item 2, the clause 2 of the 3 that sentence 133 is read as. -/
noncomputable def spItem2 : P := (TiePair.gammaPats c).getD 2 ⊥
theorem spItem2_at : (TiePair.gammaPats c)[2]? = some spItem2 := by decide +kernel
kernel_rfl fnText_at2 : fnText[2]? = some U.ax133
/-- **Γ's item 2 is not the text's sentence 133** (kernel): the sentence is uncovered. -/
theorem sp2_differs : spItem2 ≠ (trS U.ax133).pat := by decide +kernel

/-- **The clause 2 of `Lblf`, which `attrs_prios_but` leaves out, is Γ's item 2**, aligned with
sentence 133, and its priority is the one that sentence states (kernel). -/
theorem prios_split_at2 : ((c.allFns.takeWhile (c.symName ·.label != "Lblf")).map (·.clauses.length)).sum + 2 = 2 ∧
    (fnText[2]?).map (·.index) = some 133 ∧
    (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))[2]? = some (AttrsAgree.prioOf U.ax133.ax.attributes) := by
  decide +kernel

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at positions 0, 1, 2. -/
noncomputable def textPats : List P := (((fnText.map (trS · |>.pat)).set 0 spItem0).set 1 spItem1).set 2 spItem2

/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def pairSetAt : List Nat := [0, 1, 2]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h0, h1, h2⟩ := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h0), List.getElem?_map, hj]
  rfl

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the clauses of one equation (items 0, 1, 2), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([0, 1, 2] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item but the clauses of one equation (items 0, 1, 2) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([0, 1, 2] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h0 : j = 0
  · subst h0; simp at hu
  by_cases h1 : j = 1
  · subst h1; simp at hu
  by_cases h2 : j = 2
  · subst h2; simp at hu
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h0), List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to
Γ's through their sentences, the clauses of one equation as Γ's own), Γ's rule items and the five parts Γ defines by predicates
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
    ∀ ad ∈ [U.ax90, U.ax95, U.ax98], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax91, U.ax92, U.ax93, U.ax94, U.ax96, U.ax97],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax99).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 48 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax48).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE3EqExistsMlUnderApp

#check @KCore.TieE3EqExistsMlUnderApp.noRaw
#check @KCore.TieE3EqExistsMlUnderApp.readsConfined_c
#check @KCore.TieE3EqExistsMlUnderApp.userAxioms_eq
#check @KCore.TieE3EqExistsMlUnderApp.coreOK
#check @KCore.TieE3EqExistsMlUnderApp.account
#check @KCore.TieE3EqExistsMlUnderApp.account_sizes
#check @KCore.TieE3EqExistsMlUnderApp.account_classes
#check @KCore.TieE3EqExistsMlUnderApp.account_absent
#check @KCore.TieE3EqExistsMlUnderApp.absent_closed
#check @KCore.TieE3EqExistsMlUnderApp.absent_proj_below_c
#check @KCore.TieE3EqExistsMlUnderApp.absent_proj_below
#check @KCore.TieE3EqExistsMlUnderApp.lists_in_account
#check @KCore.TieE3EqExistsMlUnderApp.attrs_parts
#check @KCore.TieE3EqExistsMlUnderApp.attrs_prios_false
#check @KCore.TieE3EqExistsMlUnderApp.attrs_prios_but
#check @KCore.TieE3EqExistsMlUnderApp.sig_origin_but_next
#check @KCore.TieE3EqExistsMlUnderApp.decls_entailed
#check @KCore.TieE3EqExistsMlUnderApp.consistent
#check @KCore.TieE3EqExistsMlUnderApp.total_named
#check @KCore.TieE3EqExistsMlUnderApp.fnHypH
#check @KCore.TieE3EqExistsMlUnderApp.text_nextless
#check @KCore.TieE3EqExistsMlUnderApp.nojunk_trivial_entailed
#check @KCore.TieE3EqExistsMlUnderApp.nojunk_items_entailed
#check @KCore.TieE3EqExistsMlUnderApp.nojunk_kitem_entailed
#check @KCore.TieE3EqExistsMlUnderApp.cons_entailed
#check @KCore.TieE3EqExistsMlUnderApp.idem_refuted
#check @KCore.TieE3EqExistsMlUnderApp.gammaCl_eq
#check @KCore.TieE3EqExistsMlUnderApp.decls_entailed_c
#check @KCore.TieE3EqExistsMlUnderApp.nojunk_trivial_entailed_c
#check @KCore.TieE3EqExistsMlUnderApp.nojunk_items_entailed_c
#check @KCore.TieE3EqExistsMlUnderApp.nojunk_kitem_entailed_c
#check @KCore.TieE3EqExistsMlUnderApp.cons_entailed_c
#check @KCore.TieE3EqExistsMlUnderApp.idem_refuted_c
#print axioms KCore.TieE3EqExistsMlUnderApp.noRaw
#print axioms KCore.TieE3EqExistsMlUnderApp.readsConfined_c
#print axioms KCore.TieE3EqExistsMlUnderApp.userAxioms_eq
#print axioms KCore.TieE3EqExistsMlUnderApp.coreOK
#print axioms KCore.TieE3EqExistsMlUnderApp.account
#print axioms KCore.TieE3EqExistsMlUnderApp.account_sizes
#print axioms KCore.TieE3EqExistsMlUnderApp.account_classes
#print axioms KCore.TieE3EqExistsMlUnderApp.account_absent
#print axioms KCore.TieE3EqExistsMlUnderApp.absent_closed
#print axioms KCore.TieE3EqExistsMlUnderApp.absent_proj_below_c
#print axioms KCore.TieE3EqExistsMlUnderApp.absent_proj_below
#print axioms KCore.TieE3EqExistsMlUnderApp.lists_in_account
#print axioms KCore.TieE3EqExistsMlUnderApp.attrs_parts
#print axioms KCore.TieE3EqExistsMlUnderApp.attrs_prios_false
#print axioms KCore.TieE3EqExistsMlUnderApp.attrs_prios_but
#print axioms KCore.TieE3EqExistsMlUnderApp.sig_origin_but_next
#print axioms KCore.TieE3EqExistsMlUnderApp.decls_entailed
#print axioms KCore.TieE3EqExistsMlUnderApp.consistent
#print axioms KCore.TieE3EqExistsMlUnderApp.total_named
#print axioms KCore.TieE3EqExistsMlUnderApp.fnHypH
#print axioms KCore.TieE3EqExistsMlUnderApp.text_nextless
#print axioms KCore.TieE3EqExistsMlUnderApp.nojunk_trivial_entailed
#print axioms KCore.TieE3EqExistsMlUnderApp.nojunk_items_entailed
#print axioms KCore.TieE3EqExistsMlUnderApp.nojunk_kitem_entailed
#print axioms KCore.TieE3EqExistsMlUnderApp.cons_entailed
#print axioms KCore.TieE3EqExistsMlUnderApp.idem_refuted
#print axioms KCore.TieE3EqExistsMlUnderApp.gammaCl_eq
#print axioms KCore.TieE3EqExistsMlUnderApp.decls_entailed_c
#print axioms KCore.TieE3EqExistsMlUnderApp.nojunk_trivial_entailed_c
#print axioms KCore.TieE3EqExistsMlUnderApp.nojunk_items_entailed_c
#print axioms KCore.TieE3EqExistsMlUnderApp.nojunk_kitem_entailed_c
#print axioms KCore.TieE3EqExistsMlUnderApp.cons_entailed_c
#print axioms KCore.TieE3EqExistsMlUnderApp.idem_refuted_c
#check @KCore.TieE3EqExistsMlUnderApp.fnPins_ok
#check @KCore.TieE3EqExistsMlUnderApp.fnText_all
#check @KCore.TieE3EqExistsMlUnderApp.fns_account
#check @KCore.TieE3EqExistsMlUnderApp.sp0_differs
#check @KCore.TieE3EqExistsMlUnderApp.sp1_differs
#check @KCore.TieE3EqExistsMlUnderApp.prios_split_at1
#check @KCore.TieE3EqExistsMlUnderApp.sp2_differs
#check @KCore.TieE3EqExistsMlUnderApp.prios_split_at2
#check @KCore.TieE3EqExistsMlUnderApp.shape
#check @KCore.TieE3EqExistsMlUnderApp.fns_entailed
#check @KCore.TieE3EqExistsMlUnderApp.fns_from_text
#check @KCore.TieE3EqExistsMlUnderApp.fn_prios
#check @KCore.TieE3EqExistsMlUnderApp.gamma_from
#print axioms KCore.TieE3EqExistsMlUnderApp.fnPins_ok
#print axioms KCore.TieE3EqExistsMlUnderApp.fnText_all
#print axioms KCore.TieE3EqExistsMlUnderApp.fns_account
#print axioms KCore.TieE3EqExistsMlUnderApp.sp0_differs
#print axioms KCore.TieE3EqExistsMlUnderApp.sp1_differs
#print axioms KCore.TieE3EqExistsMlUnderApp.prios_split_at1
#print axioms KCore.TieE3EqExistsMlUnderApp.sp2_differs
#print axioms KCore.TieE3EqExistsMlUnderApp.prios_split_at2
#print axioms KCore.TieE3EqExistsMlUnderApp.shape
#print axioms KCore.TieE3EqExistsMlUnderApp.fns_entailed
#print axioms KCore.TieE3EqExistsMlUnderApp.fns_from_text
#print axioms KCore.TieE3EqExistsMlUnderApp.fn_prios
#print axioms KCore.TieE3EqExistsMlUnderApp.gamma_from
