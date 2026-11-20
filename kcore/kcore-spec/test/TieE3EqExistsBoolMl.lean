/-
  The tie (C14) on `f2-examples/e3-eq-exists-bool-ml.kompile.kore`, the kompiled text of construct fixture e3-eq-exists-bool-ml
  (`test/constructs/fixtures/e3-eq-exists-bool-ml`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-eq-exists-bool-ml`, its consistency, runs section by hand; run from the package root:
  `lake env lean -j1 test/TieE3EqExistsBoolMl.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).
  But `sp0_entailed`, of a sentence read as several clauses: stated over `Γc` and not over Γ, from
  the facts of a model of `Γc`, `boolClosed` among them.

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate (`wfFailing`).
  - The account: the class lists partition the 177 sentences of the user module E3-EQ-EXISTS-BOOL-ML, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_parts`, `attrs_prios_false`, `attrs_prios_but`: the attributes the translation does not
    read agree with `defn` but for the priorities (`attrsAgree` is false by `prios` alone): an
    equation read as several clauses states one priority, which `prios` counts once against the
    clauses counted each. With every clause of such a run but its first left out
    (`AttrsAgree.priosBut`) the priorities agree, and each clause left out is aligned with the run's
    sentence at the priority that sentence states (Lblf 1: sentence 132, `prios_split_at1`, Lblf 2:
    sentence 132, `prios_split_at2`; `fn_prios` states it of every clause). That is a fact of
    priorities: the clause's item is not its sentence, which the run's items give together
    (`sp<j0>_entailed`).
  - `sig_origin_but_next`: each of the 204 items of `sigItems c` but one is a declaration's item
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
  - Function equations (28) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0, 1, 2 is the translation of one sentence (`shape`), so
    Γ entails it (`fns_entailed`). Items 0 to 2 are the 3 clauses sentence 132 is read as (`fnPins`:
    the alignment holds the sentence at each of those positions, `TiePair.fnTextMany`, `fnPins_ok`,
    `fnText_all`). No such item is its sentence (`sp<j>_differs`); the sentence gives an item only
    with the function's functional sentence, which is not stated here; in an interpretation with the
    facts of a model of the theory, and with `boolClosed`, the item of `Γcl`, for the run at 0 (the
    sentence's binder ranges over every element of Bool, the items' cases are `true`, `false` and
    none), all the items of a run together give its sentence (`sp<j0>_of_items`, in the section on
    the runs, by hand), so `Γc` entails sentence 132 for every H (`sp0_entailed`). `fns_entailed`
    and `fns_from_text` leave those items out. `fns_from_text` (the converse), `fn_prios` (the
    priorities the sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (48): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    items 0, 1, 2 (the clauses one sentence is read as, whose sentence the items of the run give
    together), Γ's rule items, the five parts Γ defines by predicates, or definedness
    (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (24);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsBoolMl

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-bool-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-bool-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-bool-ml.kompile.kore" module "E3-EQ-EXISTS-BOOL-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-EQ-EXISTS-BOOL-ML")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 177 := by decide +kernel

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
  [("function equation", [132, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
      154, 155, 156, 157, 158, 159, 160, 161, 162, 163]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 80, 81]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [89, 90, 91, 92, 93, 94, 95, 96, 97, 98]),
   ("function functional", [62, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 37, 38, 39, 43, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
      61, 64, 79, 82, 83, 84, 85, 86, 87]),
   ("collection law", [40, 41, 42, 44, 45, 46, 47, 49, 50]),
   ("library", [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
      125, 126, 127, 128, 129, 130, 131, 164, 165, 179]),
   ("set idempotence", [48]),
   ("set-variable lemma", [99, 100, 101, 102, 103, 104, 105, 106, 180]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 36, 63, 88, 133, 134, 135, 136, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
      177, 178])]

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
    [("function equation", 28), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 15), ("hooked functional", 32), ("collection law", 9), ("library", 28), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 21)] := by
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
  [(166, "Bool"), (167, "GeneratedCounterCell"), (168, "GeneratedCounterCellOpt"),
   (169, "GeneratedTopCell"), (170, "GeneratedTopCellFragment"), (171, "Int"), (172, "K"),
   (173, "KCell"), (174, "KCellOpt"), (175, "KItem"), (176, "List"), (177, "Map"), (178, "Set")]

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
  [(62, "function functional"), (98, "no junk"), (99, "set-variable lemma"),
   (100, "set-variable lemma"), (101, "set-variable lemma"), (102, "set-variable lemma"),
   (103, "set-variable lemma"), (104, "set-variable lemma"), (105, "set-variable lemma"),
   (106, "set-variable lemma"), (109, "library"), (110, "library"), (113, "library"),
   (114, "library"), (116, "library"), (117, "library"), (120, "library"), (121, "library"),
   (124, "library"), (125, "library"), (129, "library"), (132, "function equation"),
   (136, "no direction"), (180, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 93, 64, 4, 25) := by
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

/-! ## Consistency for every H: `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`, read by cases -/

/- The one function `f` (`[total]`) has the three clauses `Parse.exClauses` writes for the equation
(`ExBoolH.read`): at the literal b, `pre ⌈b⌉ ∧ b = notBool(X)` and `rhs b`, for b = true, false; and
the last, `pre ¬∃B:Bool. (⌈B⌉ ∧ B = notBool(X))`, `rhs true`, `ens false`, all of one priority. A
clause's predicate is not `\top`, so `FnHyp` is shown here for every H (`fnHypH`), by
`fnHyp_of_decidedPre_withHooks`:
- Termination: no clause applies a function, in a term or a predicate (`preRank_named`).
- Totality of `f` (`total_named`): a value of Bool is a literal x; the clause of the literal `!x`
  applies at x, its predicate `!x = notBool(x)` true, and no clause has a smaller priority
  (`ExBoolH.value`).
- Agreement of `f` (`agree_named`): two clauses that apply at one argument list are one clause.
  At a literal x the clause of the literal b applies only where `b = !x`, and the last clause
  applies nowhere: B := `notBool(x)` gives its binder's body (`ExBoolH.applies`, `ExBoolH.coherent`).
- No match independence, rule condition or clause condition is owed (`match_named`, `owed_rules`,
  `owed_clauses`), and the text has no open generator (`noRaw`).
So Γc with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).
`ExBoolH` holds the proofs, over any semantics `d` that reads the clauses; the statements after it
are on `cH H`. -/

namespace ExBoolH

def Fs : Sym := 384
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def notX : Term := .app boolNot [.var 0]

/-- A clause of f over `[X:Bool]`, of priority 50. -/
def clX (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs, ens, prio := 50, aside := false, pre }

/-- `⌈b⌉ ∧ (b = notBool(X))`. -/
def preI (b : Bool) : Cond := .and (.ceil Srt.bool (litT b)) (.equals Srt.bool (litT b) notX)
/-- `⌈B⌉ ∧ (B = notBool(X))`, B the binder's variable, the index 1. -/
def bodyC : Cond := .and (.ceil Srt.bool (.var 1)) (.equals Srt.bool (.var 1) notX)
def lastPre : Cond := .not (.ex Srt.bool bodyC)

def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool,
  [clX (litT true) none (preI true), clX (litT false) none (preI false), clX (litT true) (some (litT false)) lastPre], true⟩

/-- **The reading**: the text's one function is `f`, with these three clauses (kernel). -/
theorem read : c.fns = [fFn] := by kernel_rfl

theorem names : c.symName Fs = "Lblf" ∧ c.symName boolNot = "LblnotBool'Unds'" := by decide +kernel
theorem lookupF : c.lookupFn Fs = some fFn := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

section Clause

variable {d : Semantics} {σ : Subst}

theorem notHook : isHook boolNot = true := by decide +kernel

/-- An application of an interpreted hooked symbol has the value `hookRes` gives at its arguments'
results. -/
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

/-- `notBool` at a value of Bool, under every interpretation. -/
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

/-- The truth value of `b = !x`. -/
def bEq (b x : Bool) : Bool := sameResult (some (bool b)) (some (bool !x))

theorem bEq_iff (b x : Bool) : bEq b x = true ↔ b = !x := by cases b <;> cases x <;> decide

theorem preI_mk (hc : d.isCtor boolNot = false) {x : Bool} (h0 : σ.lookup 0 = some (bool x)) (b : Bool) :
    Holds d 1 σ (preI b) (bEq b x) :=
  Holds.and (n := 1) (Holds.ceil (s := Srt.bool) (EvalTerm.dv (c := d) (σ := σ) (s := Srt.bool) (lit := .bool b)))
    (Holds.equals (s := Srt.bool) (EvalTerm.dv (c := d) (σ := σ) (s := Srt.bool) (lit := .bool b)) (notX_mk hc h0))

theorem preI_inv (hc : d.isCtor boolNot = false) {x b r : Bool} (h0 : σ.lookup 0 = some (bool x))
    (h : Holds d 1 σ (preI b) r) : r = bEq b x := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [EvalTerm.dv_inv e1, EvalTerm.dv_inv e2, notX_inv hc h0 e3]
        rfl

/-- The binder's body under σ', B the index 1. -/
def gB (x : Bool) (σ' : Subst) : Bool := (σ'.lookup 1).isSome && sameResult (σ'.lookup 1) (some (bool !x))

theorem bodyC_mk (hc : d.isCtor boolNot = false) {σ' : Subst} {x : Bool} (h0 : σ'.lookup 0 = some (bool x)) :
    Holds d 2 σ' bodyC (gB x σ') :=
  Holds.and (Holds.ceil .var) (Holds.equals .var (notX_mk hc h0))

theorem bodyC_inv (hc : d.isCtor boolNot = false) {σ' : Subst} {x r : Bool} (h0 : σ'.lookup 0 = some (bool x))
    (h : Holds d 2 σ' bodyC r) : r = gB x σ' := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [EvalTerm.var_inv e1, EvalTerm.var_inv e2, notX_inv hc h0 e3]; rfl

/-- The extension of σ by B := `!x`. -/
def ext (x : Bool) (σ : Subst) : Subst := (1, bool !x) :: σ

theorem sameBool (b : Bool) : sameResult (some (bool b)) (some (bool b)) = true := by cases b <;> decide

theorem gB_ext (x : Bool) (σ : Subst) : gB x (ext x σ) = true := by
  have hlk : (ext x σ).lookup 1 = some (bool !x) := rfl
  simp only [gB, hlk, Option.isSome_some, Bool.true_and, sameBool]

theorem ext_extends (x : Bool) (σ : Subst) : Extends d 1 [Srt.bool] σ (ext x σ) := by
  refine ⟨fun i hi => ?_, fun j s hs => ?_⟩
  · have : i = 0 := by omega
    subst this; rfl
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨bool !x, rfl, rmS_sortOf_bool d _⟩
    | succ j => simp at hs

/-- **The last clause's premise is false where X is a literal**: B := `notBool(x)` gives the body. -/
theorem last_inv (hc : d.isCtor boolNot = false) {x r : Bool} (h0 : σ.lookup 0 = some (bool x))
    (h : Holds d 1 σ lastPre r) : r = false := by
  cases h with
  | not h =>
    cases h with
    | ex g hb hr =>
      have hg := bodyC_inv hc (σ' := ext x σ) h0 (hb (ext x σ) (ext_extends x σ))
      have h1 : g (ext x σ) = true := by rw [hg]; exact gB_ext x σ
      have := hr.mpr ⟨_, ext_extends x σ, h1⟩
      subst this; rfl

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

theorem clX_of {cl : Clause} (h : cl ∈ fFn.clauses) :
    cl = clX (litT true) none (preI true) ∨ cl = clX (litT false) none (preI false) ∨
      cl = clX (litT true) (some (litT false)) lastPre := by
  simpa [fFn] using h

theorem prio_none {vs : List GroundTerm} {cl : Clause} (hcl : cl ∈ fFn.clauses) :
    ∀ cl' ∈ fFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails d vs cl' := by
  intro cl' hcl' _ hlt
  rcases clX_of hcl with rfl | rfl | rfl <;> rcases clX_of hcl' with rfl | rfl | rfl <;>
    exact absurd hlt (by decide)

theorem litT_mem (b : Bool) : clX (litT b) none (preI b) ∈ fFn.clauses := by
  cases b <;> simp [fFn]

/-- **`f(x)` is `notBool(x)`**, by the clause of the literal `!x`. -/
theorem value (hc : d.isCtor boolNot = false) (hfn : d.lookupFn Fs = some fFn) (x : Bool) :
    Eval d Fs [bool x] (some (bool !x)) := by
  have hp := preI_mk hc (σ := sg (bool x)) (x := x) rfl (!x)
  rw [(bEq_iff (!x) x).mpr rfl] at hp
  exact .clause (cl := clX (litT !x) none (preI !x)) hfn (litT_mem _) (sg_sorted x) (sg_match _)
    (fun t ht => nomatch ht) hp (prio_none (litT_mem _)) rfl .dv (fun t ht => nomatch ht) .top

/-- **A clause of f that applies at an argument list**: the argument is a literal x, X is x, and
the clause is that of the literal `!x`. -/
theorem applies (hc : d.isCtor boolNot = false) (hs : d.shapesOK = true) {cl : Clause}
    (hcl : cl ∈ fFn.clauses) {vs : List GroundTerm} (h : cl.AppliesAt d σ vs) :
    ∃ x, vs = [bool x] ∧ σ.lookup 0 = some (bool x) ∧ cl = clX (litT !x) none (preI !x) := by
  obtain ⟨hws, hm, -, hpre⟩ := h
  have hp : cl.pats = [.var 0] := by rcases clX_of hcl with rfl | rfl | rfl <;> rfl
  rw [hp] at hm
  obtain ⟨v, rfl, hl⟩ := match0 hm
  have h0 : ∃ w, σ.lookup 0 = some w ∧ d.sortOf w = some Srt.bool := by
    rcases clX_of hcl with rfl | rfl | rfl <;> exact hws 0 (by decide) Srt.bool rfl
  obtain ⟨w, hw, hwsrt⟩ := h0
  rw [hl] at hw
  obtain rfl := Option.some.inj hw
  obtain ⟨x, rfl⟩ := shape_bool hs hwsrt
  refine ⟨x, rfl, hl, ?_⟩
  rcases clX_of hcl with rfl | rfl | rfl
  · have := (bEq_iff true x).mp (preI_inv hc hl hpre).symm
    rw [← this]
  · have := (bEq_iff false x).mp (preI_inv hc hl hpre).symm
    rw [← this]
  · exact absurd (last_inv hc hl hpre) (by simp)

/-- **Any two clauses of f are coherent**: where both apply at one argument list they are one
clause, whose right side is a literal. -/
theorem coherent (hc : d.isCtor boolNot = false) (hs : d.shapesOK = true) {cl cl' : Clause}
    (hcl : cl ∈ fFn.clauses) (hcl' : cl' ∈ fFn.clauses) : Coherent d cl cl' := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, hv, -, rfl⟩ := applies hc hs hcl ha
  obtain ⟨x', hv', -, rfl⟩ := applies hc hs hcl' ha'
  rw [hv] at hv'
  have : x' = x := by cases x <;> cases x' <;> first | rfl | exact absurd hv' (by decide)
  subst this
  left
  refine ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  cases x' <;> simp [clX, litT, varOccs] at hi

end Clause

end ExBoolH

/-! ### The facts the deciders name -/

def callOrder : List Nat := [384]

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

theorem notCtorH (H : HookParams) : (cH H).isCtor boolNot = false := ExBoolH.notCtor
theorem shapesH (H : HookParams) : (cH H).shapesOK = true := ExBoolH.shapes
theorem lookupFH (H : HookParams) : (cH H).lookupFn ExBoolH.Fs = some ExBoolH.fFn := by
  rw [Semantics.lookupFn_withHooks]; exact ExBoolH.lookupF

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

/-- **`f` is total under every H**: at a literal x, the clause of the literal `!x` applies. -/
theorem totalsH (H : HookParams) : ∀ fn ∈ c.fns, fn.total = true → Total (cH H) fn.label := by
  intro fn hfn _
  rw [ExBoolH.read] at hfn
  obtain rfl := List.mem_singleton.mp hfn
  intro fn' hfn' vs hvs
  rw [show ExBoolH.fFn.label = ExBoolH.Fs from rfl, lookupFH H] at hfn'
  cases hfn'
  obtain ⟨v, rfl, hv⟩ := sortsOf_one hvs
  obtain ⟨x, rfl⟩ := shape_bool (shapesH H) hv
  exact ⟨_, ExBoolH.value (notCtorH H) (lookupFH H) x⟩

/-- **The clauses of `f` agree under every H** (the function `agree_named` names). -/
theorem agreeH (H : HookParams) :
    ∀ f ∈ c.agreeObligationsI, ∀ fn, (cH H).lookupFn f = some fn → ClausesAgree (cH H) fn := by
  intro f hf fn hfn
  rw [agree_named] at hf
  obtain rfl := List.mem_singleton.mp hf
  rw [show (384 : Sym) = ExBoolH.Fs from rfl, lookupFH H] at hfn
  cases hfn
  intro cl cl' hp _
  obtain ⟨h1, h2⟩ := mem_of_mem_pairs hp
  exact ⟨ExBoolH.coherent (notCtorH H) (shapesH H) h1 h2, ExBoolH.coherent (notCtorH H) (shapesH H) h2 h1⟩

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [preRank_named] at hg; cases hg)
    (totalsH H) (agreeH H) (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **`f(b) = notBool b`, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) ExBoolH.Fs [bool b] (some (bool (!b))) :=
  ExBoolH.value (notCtorH H) (lookupFH H) b

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

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax80, U.ax81]

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


/-! ## Function equations (28 sentences) and priority equations (0 sentences)

One equation read as several clauses (items 0 to 2, sentence 132): the equation's right side holds
alternatives (an `\or`, or an `\exists` over a Bool, read case by case), and the reading gives a
clause for each alternative, with its condition, and one where none applies. The alignment holds the
sentence at each of the clauses' positions (`fnPins`, `TiePair.fnTextMany`: a pinned position holds
its sentence, every other position the first sentence of its function and priority; `fnPins_ok`,
`fnText_all`). No such item is its sentence (`sp<j>_differs`). The sentence gives an item only
together with the function's functional sentence (where an alternative applies, the sentence gives
the application every element that alternative holds, and the item one element), and the items give
the sentence only all together: the first is not stated here, and in an interpretation with the
facts of a model of the theory, and with `boolClosed`, the item of `Γcl`, for the run at 0 (the
sentence's binder ranges over every element of Bool, the items' cases are `true`, `false` and none),
all the items of a run together give its sentence (`sp<j0>_of_items`, in the section on the runs, by
hand), so `Γc` entails sentence 132 for every H (`sp0_entailed`); `fns_entailed` and `fns_from_text`
leave the items out, and the premise set of `gamma_from` holds Γ's items there.

Every other item is the translation of its function sentence (`shape`). -/

/-- The pins of the alignment, `(item, sentence index)`: each clause of a run one equation is read
as, at that equation. -/
def fnPins : List (Nat × Nat) := [(0, 132), (1, 132), (2, 132)]

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

/-- Γ's item 0, the clause 0 of the 3 that sentence 132 is read as. -/
noncomputable def spItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem spItem0_at : (TiePair.gammaPats c)[0]? = some spItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax132
/-- **Γ's item 0 is not the text's sentence 132** (kernel): the run's items give the sentence together (`sp0_entailed`). -/
theorem sp0_differs : spItem0 ≠ (trS U.ax132).pat := by decide +kernel

/-- Γ's item 1, the clause 1 of the 3 that sentence 132 is read as. -/
noncomputable def spItem1 : P := (TiePair.gammaPats c).getD 1 ⊥
theorem spItem1_at : (TiePair.gammaPats c)[1]? = some spItem1 := by decide +kernel
kernel_rfl fnText_at1 : fnText[1]? = some U.ax132
/-- **Γ's item 1 is not the text's sentence 132** (kernel): the run's items give the sentence together (`sp0_entailed`). -/
theorem sp1_differs : spItem1 ≠ (trS U.ax132).pat := by decide +kernel

/-- **The clause 1 of `Lblf`, which `attrs_prios_but` leaves out, is Γ's item 1**, aligned with
sentence 132, and its priority is the one that sentence states (kernel). -/
theorem prios_split_at1 : ((c.allFns.takeWhile (c.symName ·.label != "Lblf")).map (·.clauses.length)).sum + 1 = 1 ∧
    (fnText[1]?).map (·.index) = some 132 ∧
    (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))[1]? = some (AttrsAgree.prioOf U.ax132.ax.attributes) := by
  decide +kernel

/-- Γ's item 2, the clause 2 of the 3 that sentence 132 is read as. -/
noncomputable def spItem2 : P := (TiePair.gammaPats c).getD 2 ⊥
theorem spItem2_at : (TiePair.gammaPats c)[2]? = some spItem2 := by decide +kernel
kernel_rfl fnText_at2 : fnText[2]? = some U.ax132
/-- **Γ's item 2 is not the text's sentence 132** (kernel): the run's items give the sentence together (`sp0_entailed`). -/
theorem sp2_differs : spItem2 ≠ (trS U.ax132).pat := by decide +kernel

/-- **The clause 2 of `Lblf`, which `attrs_prios_but` leaves out, is Γ's item 2**, aligned with
sentence 132, and its priority is the one that sentence states (kernel). -/
theorem prios_split_at2 : ((c.allFns.takeWhile (c.symName ·.label != "Lblf")).map (·.clauses.length)).sum + 2 = 2 ∧
    (fnText[2]?).map (·.index) = some 132 ∧
    (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))[2]? = some (AttrsAgree.prioOf U.ax132.ax.attributes) := by
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
    ∀ ad ∈ [U.ax89, U.ax94, U.ax97], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax98).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 48 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax48).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

/-! ## The runs: sentence 132 from Γ's items 0, 1, 2 and `boolClosed`

`rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`: Γ's three items for f are `f(X) = b`
under `⌈b⌉ ∧ b = notBool(X)` at each literal b of Bool, and a last one where no element of Bool
gives the right side an element. `Run0`: the sentence is `eqnPat` of `(∃B:Bool. body) ∧ ⊤`
(`text_shape`); Γ's three items are `eqnPat` over the same guards, premise, sort and left side
(`gamma_shape`, `sp_items`); what the parts mean at a valuation is `TieEX.ExFacts`, from the decision
`exReadB_fun` (`facts`). `sp0_of_items`: the sentence's binder ranges over every element of Bool and
the items' cases are `true`, `false` and none, so the items give the sentence where every element of
Bool is the element of a literal, `boolClosed` (`TieEX.ex_text_of_split`). No `functional` sentence
is read. -/

namespace Run0

open KoreAML.TieFR KCore.TieEX KCore.TieEXReadB

def Fs : Sym := nRegSyms + 4
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def notX : Term := .app boolNot [.var 0]
/-- The alternative of the instance at the literal b: the term b, with `b = notBool(X)`. -/
def xLit (b : Bool) : Term × List Cond := (litT b, [.equals Srt.bool (litT b) notX])
/-- The alternative of the body with B the variable at index 1: B, with `B = notBool(X)`. -/
def jB : Term × List Cond := (.var 1, [.equals Srt.bool (.var 1) notX])

/-- f, declared `total`, with the clauses of the split. -/
def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool,
  Parse.exClauses Srt.bool [Srt.bool] [.var 0] none 50 false [xLit true, xLit false] [jB], true⟩

/-! **f is the first function of `defn`**, with these clauses (kernel). -/
kernel_rfl fFn_at : c.fns[0]? = some fFn

/-! ### The text's two sentences -/

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def vsF : List KoreAML.Var := [⟨"X", "Bool"⟩]
def Bv : KoreAML.Var := ⟨"B", "Bool"⟩

/-- The names the body is read with: the definition's sorts and symbols, f a function of the
definition with a `functional` sentence, Bool's literals its values. -/
def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    keyFns := [(nRegSyms + 4, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

theorem names_c : NT.syms = c.symNames ∧ NT.sorts = c.sortNames := by decide +kernel

/-- The binder's body `B ∧ (B = notBool(X))`. -/
def bodyK : Kore.Pattern := .and bS [Bp, .equals bS bS Bp (ap "LblnotBool'Unds'" [Xp])]

/-- The table of sentence 132, its guards, and the table of Γ's items for f: R, the argument, the
clause's variable and the binder. -/
noncomputable def tbl : VarTable := tableOf U.ax132.ax.sortVars U.ax132.ax.pattern
noncomputable def ws : List P := guardsOf U.ax132.ax
def tblG : VarTable := [.sortVar "R", .evar "X0" bS, .evar "VarV0" bS, .evar "VarV1" bS]
abbrev rG : EVar := tblG.ev (sortVarKey Rv)
noncomputable def prem : P := tr ⟨tbl, []⟩ (.and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]])
noncomputable def Ff : P := tr ⟨tbl, []⟩ (ap "Lblf" [ev "X0" bS])
noncomputable def xB : EVar := tbl.ev (evarKey Bv.kore)
noncomputable def bodyT : P := tr ⟨tbl, []⟩ bodyK
noncomputable def ensT : P := tr ⟨tbl, []⟩ (.top bS)


/-- **Sentence 132, translated as the text writes it, is the equation
`X0 ∈ X → f(X0) = (∃B:Bool. B ∧ (B = notBool(X))) ∧ ⊤`** (kernel). -/
theorem text_shape : (trS U.ax132).pat =
    eqnPat ws rG prem TieFRRead.boolP Ff (sAnd (sExists xB TieFRRead.boolP bodyT) ensT) := by decide +kernel

/-- The sort guard is one of the sentence's guards. -/
theorem idx_facts : sortGuard rG ∈ ws := by decide +kernel

/-- The variables read are of Bool, and the guards hold each in its sort. -/
theorem lit_facts : Parse.varSorts NT vsF = .ok [Srt.bool] ∧ TieFRVars.guardsHold ws tbl vsF = true :=
  ⟨by kernel_rfl, by decide +kernel⟩

/-! ### Γ's items for f -/

/-- The clauses' variables. -/
abbrev vsOf (C : Semantics) : List KoreAML.Var := Faithful.canonVars C [Srt.bool]

/-- The last clause's right side `true ∧ (false = true)`. -/
noncomputable def BNG (C : Semantics) : P := sAnd (altPC C tblG (vsOf C) (xLit true))
  (tr ⟨tblG, []⟩ (reqPat (srtOf C Srt.bool) (some (Term.kore C (vsOf C) (Parse.boolT false)))))

/-- The three equations: of the alternative at `true`, of the alternative at `false`, and the
last, over the sentence's guards and application of f. -/
noncomputable def gpats (C : Semantics) : List P :=
  [eqnPat ws rG (clauseQC C tblG (vsOf C) Srt.bool prem (xLit true)) TieFRRead.boolP Ff
     (sAnd (altPC C tblG (vsOf C) (xLit true)) (sTop TieFRRead.boolP)),
   eqnPat ws rG (clauseQC C tblG (vsOf C) Srt.bool prem (xLit false)) TieFRRead.boolP Ff
     (sAnd (altPC C tblG (vsOf C) (xLit false)) (sTop TieFRRead.boolP)),
   eqnPat ws rG (lastBQC C tblG (vsOf C) Srt.bool prem [jB]) TieFRRead.boolP Ff (BNG C)]

/-- The decisions on the semantics with any hook parameters: Γ's items for f are `gpats`, and
Bool's sort translates to Bool's pattern. -/
noncomputable def shapeB (C : Semantics) : Bool :=
  decide ((Faithful.kernelItems (Faithful.fnEquationsK C fFn)).map (·.pat) = gpats C) &&
    decide (trSort tblG (srtOf C Srt.bool) = TieFRRead.boolP)

/-- (kernel) As a function of the hook parameters, the constant `true`. -/
theorem shapeB_fun : (fun Hk : HookParams => shapeB (c.withHooks Hk)) = fun _ => true := by kernel_rfl

/-- **Γ's items for f are the three equations**, for every H. -/
theorem gamma_shape (H : HookParams) :
    (Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn)).map (·.pat) = gpats (cH H) := by
  have h : shapeB (cH H) = true := congrFun shapeB_fun H
  simp only [shapeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem boolSort_H (H : HookParams) : trSort tblG (srtOf (cH H) Srt.bool) = TieFRRead.boolP := by
  have h : shapeB (cH H) = true := congrFun shapeB_fun H
  simp only [shapeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem items_length (H : HookParams) :
    (Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn)).length = 3 := by
  have := congrArg List.length (gamma_shape H)
  rw [List.length_map] at this
  exact this

/-- **The decision of the readings** (`TieEXReadB.exReadB`), at the semantics with any hook
parameters (kernel): the function of the hook parameters is the constant `true`. -/
theorem exReadB_fun : (fun Hk : HookParams => exReadB NT (c.withHooks Hk) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK
    (.top bS) (xLit true) (xLit false) jB) = fun _ => true := by kernel_rfl

theorem exReadB_H (H : HookParams) : exReadB NT (cH H) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK
    (.top bS) (xLit true) (xLit false) jB = true := congrFun exReadB_fun H
/-! **Γ's items for f are the items 0, 1 and 2 of `fnItems`**, for every H (kernel). -/
kernel_rfl sp_items : ∀ H : HookParams,
  (Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn)).map (·.pat) = [spItem0, spItem1, spItem2]

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The readings** `TieEX`'s lemmas take, in a model with `NodeFacts` and `TermsInSort`, from the
decision. -/
theorem facts (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I) :
    ∃ β, IsSort I β ∧ (∀ (e : Valuation M) a, TieFRRead.boolP.interpret I e a ↔ a = β) ∧
      (∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β) ∧
      ExFacts I (cH H) tblG (vsOf (cH H)) ws β (xsOfB (xLit true) (xLit false)) [jB] bodyT ensT xB
        (CGof I (cH H) tblG (vsOf (cH H))) (CGof I (cH H) tblG (vsBof (cH H) [Srt.bool])) := by
  obtain ⟨β, hβ, hβd⟩ := TieFRRead.boolDen_of N
  have hσ : ∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β := fun e a => by
    rw [boolSort_H H]; exact hβd e a
  exact ⟨β, hβ, hβd, hσ, exFacts_of_exB N hTS names_c.1 names_c.2 (al := []) lit_facts.1 lit_facts.2
    idx_facts hσ hβ rfl rfl (exReadB_H H)⟩

end

end Run0

section
open KoreAML.TieFR KCore.TieEX KCore.TieEXReadB Run0

/-- **Γ's items 0, 1, 2 and `boolClosed` give sentence 132**, for every H, in a model with
`NodeFacts (cH H) I` and `TermsInSort (cH H) I`. -/
theorem sp0_of_items (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hcl : I ⊧ᴵ Faithful.boolClosed (cH H))
    (hs : ∀ φ ∈ [spItem0, spItem1, spItem2], I ⊧ᴵ φ) : I ⊧ᴵ (trS U.ax132).pat := by
  have hs' : ∀ φ ∈ gpats (cH H), I ⊧ᴵ φ := by
    rw [← gamma_shape H, sp_items H]; exact hs
  rw [text_shape]
  obtain ⟨β, hβ, hd, hσ, X⟩ := facts H N hTS
  have hSA : SortAt I TieFRRead.boolP β := ⟨hd, hβ, rfl⟩
  have hr := idx_facts
  have hk : ∀ x ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false,
      I ⊧ᴵ eqnPat ws rG (clauseQC (cH H) tblG (vsOf (cH H)) Srt.bool prem x) TieFRRead.boolP Ff
        (sAnd (altPC (cH H) tblG (vsOf (cH H)) x) (sTop TieFRRead.boolP)) := by
    intro x hx
    have hx' : x = xLit true ∨ x = xLit false := by
      rcases List.mem_append.mp hx with h | h
      · exact Or.inl (List.mem_singleton.mp h)
      · exact Or.inr (List.mem_singleton.mp h)
    rcases hx' with rfl | rfl
    · exact hs' _ (List.mem_cons_self ..)
    · exact hs' _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hn : I ⊧ᴵ eqnPat ws rG (lastBQC (cH H) tblG (vsOf (cH H)) Srt.bool prem [jB]) TieFRRead.boolP Ff
      (BNG (cH H)) :=
    hs' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact ex_text_of_split N hcl (tbl := tblG) (vs := vsOf (cH H)) (s := Srt.bool)
    (CG := CGof I (cH H) tblG (vsOf (cH H))) (CGB := CGof I (cH H) tblG (vsBof (cH H) [Srt.bool]))
    (body := bodyT) (ensT := ensT) (xB := xB) (SR := srtOf (cH H) Srt.bool)
    hSA (guardsOf_pred (I := I) N.defOK U.ax132.ax) hr hσ hσ X.hin X.hcond X.hbody X.hxr X.hinB X.hcondB
    X.hbodyB hk hn

end

/-! ## E for the sentences read as several clauses, from all the items of a run together

The items of a run are Γ's (`spItem<j>_at`), so a model of Γ satisfies each (`spItem_sat`); a model
of the theory has the constructors' facts (`HoldsShape.nodeFacts_of_core`) and its terms' elements
lie in their sorts (`Faithful.termsInSort_of_core`), and, where the statement takes it, `boolClosed`
is the item of `Γcl` (`gammaCl_eq`). With those, `sp<j0>_of_items` gives the sentence: sentence 132
over `Γc` (`sp0_entailed`, items 0 to 2). The converse is not stated: the sentence gives the
application every element of each alternative that applies, which is an item only where the
application is one element. -/

/-- A model of Γ satisfies each of Γ's equations, for every H. -/
theorem spItem_sat (H : HookParams) {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    {j : Nat} {φ : P} (h : (TiePair.gammaPats c)[j]? = some φ) : I ⊧ᴵ φ := by
  unfold TiePair.gammaPats at h
  rw [List.getElem?_map] at h
  cases hj : (fnItems c)[j]? with
  | none => rw [hj] at h; cases h
  | some it =>
    rw [hj] at h
    rw [← Option.some.inj h]
    exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact List.mem_of_getElem? hj, rfl⟩))

/-- **E for sentence 132**: `Γc` entails it, for every H, from Γ's items 0, 1, 2 together and `boolClosed` (`sp0_of_items`). -/
theorem sp0_entailed (H : HookParams) : Γc (cH H) ⊧ (trS U.ax132).pat := by
  intro M _ I hIc
  have hI : I ⊧ᴵP Γ (cH H) := fun φ hφ => hIc φ (Γ_sub_Γc _ hφ)
  refine sp0_of_items H (HoldsShape.nodeFacts_of_core (coreOKH H) hIc)
    (Faithful.termsInSort_of_core (coreOKH H) hI) (hIc _ (Or.inr ((gammaCl_eq H _).mpr rfl))) fun φ hφ => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · exact spItem_sat H hI spItem0_at
  · exact spItem_sat H hI spItem1_at
  · exact spItem_sat H hI spItem2_at

end KCore.TieE3EqExistsBoolMl

#check @KCore.TieE3EqExistsBoolMl.noRaw
#check @KCore.TieE3EqExistsBoolMl.readsConfined_c
#check @KCore.TieE3EqExistsBoolMl.userAxioms_eq
#check @KCore.TieE3EqExistsBoolMl.coreOK
#check @KCore.TieE3EqExistsBoolMl.account
#check @KCore.TieE3EqExistsBoolMl.account_sizes
#check @KCore.TieE3EqExistsBoolMl.account_classes
#check @KCore.TieE3EqExistsBoolMl.account_absent
#check @KCore.TieE3EqExistsBoolMl.absent_closed
#check @KCore.TieE3EqExistsBoolMl.absent_proj_below_c
#check @KCore.TieE3EqExistsBoolMl.absent_proj_below
#check @KCore.TieE3EqExistsBoolMl.lists_in_account
#check @KCore.TieE3EqExistsBoolMl.attrs_parts
#check @KCore.TieE3EqExistsBoolMl.attrs_prios_false
#check @KCore.TieE3EqExistsBoolMl.attrs_prios_but
#check @KCore.TieE3EqExistsBoolMl.sig_origin_but_next
#check @KCore.TieE3EqExistsBoolMl.decls_entailed
#check @KCore.TieE3EqExistsBoolMl.consistent
#check @KCore.TieE3EqExistsBoolMl.total_named
#check @KCore.TieE3EqExistsBoolMl.fnHypH
#check @KCore.TieE3EqExistsBoolMl.text_nextless
#check @KCore.TieE3EqExistsBoolMl.nojunk_trivial_entailed
#check @KCore.TieE3EqExistsBoolMl.nojunk_items_entailed
#check @KCore.TieE3EqExistsBoolMl.nojunk_kitem_entailed
#check @KCore.TieE3EqExistsBoolMl.cons_entailed
#check @KCore.TieE3EqExistsBoolMl.idem_refuted
#check @KCore.TieE3EqExistsBoolMl.gammaCl_eq
#check @KCore.TieE3EqExistsBoolMl.decls_entailed_c
#check @KCore.TieE3EqExistsBoolMl.nojunk_trivial_entailed_c
#check @KCore.TieE3EqExistsBoolMl.nojunk_items_entailed_c
#check @KCore.TieE3EqExistsBoolMl.nojunk_kitem_entailed_c
#check @KCore.TieE3EqExistsBoolMl.cons_entailed_c
#check @KCore.TieE3EqExistsBoolMl.idem_refuted_c
#check @KCore.TieE3EqExistsBoolMl.sp0_of_items
#check @KCore.TieE3EqExistsBoolMl.sp0_entailed
#print axioms KCore.TieE3EqExistsBoolMl.noRaw
#print axioms KCore.TieE3EqExistsBoolMl.readsConfined_c
#print axioms KCore.TieE3EqExistsBoolMl.userAxioms_eq
#print axioms KCore.TieE3EqExistsBoolMl.coreOK
#print axioms KCore.TieE3EqExistsBoolMl.account
#print axioms KCore.TieE3EqExistsBoolMl.account_sizes
#print axioms KCore.TieE3EqExistsBoolMl.account_classes
#print axioms KCore.TieE3EqExistsBoolMl.account_absent
#print axioms KCore.TieE3EqExistsBoolMl.absent_closed
#print axioms KCore.TieE3EqExistsBoolMl.absent_proj_below_c
#print axioms KCore.TieE3EqExistsBoolMl.absent_proj_below
#print axioms KCore.TieE3EqExistsBoolMl.lists_in_account
#print axioms KCore.TieE3EqExistsBoolMl.attrs_parts
#print axioms KCore.TieE3EqExistsBoolMl.attrs_prios_false
#print axioms KCore.TieE3EqExistsBoolMl.attrs_prios_but
#print axioms KCore.TieE3EqExistsBoolMl.sig_origin_but_next
#print axioms KCore.TieE3EqExistsBoolMl.decls_entailed
#print axioms KCore.TieE3EqExistsBoolMl.consistent
#print axioms KCore.TieE3EqExistsBoolMl.total_named
#print axioms KCore.TieE3EqExistsBoolMl.fnHypH
#print axioms KCore.TieE3EqExistsBoolMl.text_nextless
#print axioms KCore.TieE3EqExistsBoolMl.nojunk_trivial_entailed
#print axioms KCore.TieE3EqExistsBoolMl.nojunk_items_entailed
#print axioms KCore.TieE3EqExistsBoolMl.nojunk_kitem_entailed
#print axioms KCore.TieE3EqExistsBoolMl.cons_entailed
#print axioms KCore.TieE3EqExistsBoolMl.idem_refuted
#print axioms KCore.TieE3EqExistsBoolMl.gammaCl_eq
#print axioms KCore.TieE3EqExistsBoolMl.decls_entailed_c
#print axioms KCore.TieE3EqExistsBoolMl.nojunk_trivial_entailed_c
#print axioms KCore.TieE3EqExistsBoolMl.nojunk_items_entailed_c
#print axioms KCore.TieE3EqExistsBoolMl.nojunk_kitem_entailed_c
#print axioms KCore.TieE3EqExistsBoolMl.cons_entailed_c
#print axioms KCore.TieE3EqExistsBoolMl.idem_refuted_c
#print axioms KCore.TieE3EqExistsBoolMl.sp0_of_items
#print axioms KCore.TieE3EqExistsBoolMl.sp0_entailed
#check @KCore.TieE3EqExistsBoolMl.fnPins_ok
#check @KCore.TieE3EqExistsBoolMl.fnText_all
#check @KCore.TieE3EqExistsBoolMl.fns_account
#check @KCore.TieE3EqExistsBoolMl.sp0_differs
#check @KCore.TieE3EqExistsBoolMl.sp1_differs
#check @KCore.TieE3EqExistsBoolMl.prios_split_at1
#check @KCore.TieE3EqExistsBoolMl.sp2_differs
#check @KCore.TieE3EqExistsBoolMl.prios_split_at2
#check @KCore.TieE3EqExistsBoolMl.shape
#check @KCore.TieE3EqExistsBoolMl.fns_entailed
#check @KCore.TieE3EqExistsBoolMl.fns_from_text
#check @KCore.TieE3EqExistsBoolMl.fn_prios
#check @KCore.TieE3EqExistsBoolMl.gamma_from
#print axioms KCore.TieE3EqExistsBoolMl.fnPins_ok
#print axioms KCore.TieE3EqExistsBoolMl.fnText_all
#print axioms KCore.TieE3EqExistsBoolMl.fns_account
#print axioms KCore.TieE3EqExistsBoolMl.sp0_differs
#print axioms KCore.TieE3EqExistsBoolMl.sp1_differs
#print axioms KCore.TieE3EqExistsBoolMl.prios_split_at1
#print axioms KCore.TieE3EqExistsBoolMl.sp2_differs
#print axioms KCore.TieE3EqExistsBoolMl.prios_split_at2
#print axioms KCore.TieE3EqExistsBoolMl.shape
#print axioms KCore.TieE3EqExistsBoolMl.fns_entailed
#print axioms KCore.TieE3EqExistsBoolMl.fns_from_text
#print axioms KCore.TieE3EqExistsBoolMl.fn_prios
#print axioms KCore.TieE3EqExistsBoolMl.gamma_from
