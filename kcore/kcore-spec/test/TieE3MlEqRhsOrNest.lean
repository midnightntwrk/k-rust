/-
  The tie (C14) on `f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore`, the kompiled text of construct fixture e3-ml-eq-rhs-or-nest
  (`test/constructs/fixtures/e3-ml-eq-rhs-or-nest`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-eq-rhs-or-nest`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlEqRhsOrNest.lean`.

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate (`wfFailing`).
  - The account: the class lists partition the 258 sentences of the user module E3-ML-EQ-RHS-OR-NEST, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_parts`, `attrs_prios_false`, `attrs_prios_but`: the attributes the translation does not
    read agree with `defn` but for the priorities (`attrsAgree` is false by `prios` alone): an
    equation read as several clauses states one priority, which `prios` counts once against the
    clauses counted each. With every clause of such a run but its first left out
    (`AttrsAgree.priosBut`) the priorities agree, and each clause left out is aligned with the run's
    sentence at the priority that sentence states (Lblh 1: sentence 208, `prios_split_at3`, Lblh 2:
    sentence 208, `prios_split_at4`; `fn_prios` states it of every clause). That is a fact of
    priorities: the clause's item is not tied to its sentence, which is uncovered.
  - `sig_origin_but_next`: each of the 207 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the totality of the `[total]` function `h` (`total_named`); the agreement of `h`
    (`agree_named`); `FnHyp` itself: a clause's predicate is not `\top` (`Semantics.clausesPreTop`
    false), so the named facts do not give it and `kcore gen --core` takes it as the hypothesis of its
    statements, which no decider confirms. The consistency section, written by hand, proves that Γ with
    the step's closure has a model for every H (`consistent`), through `FnHyp` for every H (`fnHypH`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (31) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 2, 3, 4 is the translation of one sentence (`shape`), so
    Γ entails it (`fns_entailed`). Items 2 to 4 are the 3 clauses sentence 208 is read as (`fnPins`:
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
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 161 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    items 2, 3, 4 (the clauses one sentence is read as, whose sentence is uncovered), Γ's rule
    items, the five parts Γ defines by predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (10);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlEqRhsOrNest

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore" module "E3-ML-EQ-RHS-OR-NEST"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-OR-NEST")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 258 := by decide +kernel

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
  [("function equation", [204, 206, 208, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226,
      227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 241]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 102, 103]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [112, 113, 114, 115, 116, 117, 118, 119, 120, 121]),
   ("function functional", [77, 79, 80, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 98]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      55, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 78, 82, 99, 100, 101, 104, 105, 106, 107,
      108, 109]),
   ("collection law", [52, 53, 54, 56, 57, 58, 59, 61, 62]),
   ("library", [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
      145, 146, 147, 148, 149, 150, 151, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
      164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181,
      182, 183, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200,
      201, 202, 203, 205, 242, 243, 244, 245, 259, 260]),
   ("set idempotence", [60]),
   ("set-variable lemma", [122, 123, 124, 125, 126, 261]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 39, 41, 72, 74, 81, 97, 110, 111, 152, 184, 207, 209, 210, 211, 239, 240, 246, 247, 248,
      249, 250, 251, 252, 253, 254, 255, 256, 257, 258])]

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
    [("function equation", 31), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 18), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 30)] := by
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
  [(77, "function functional"), (79, "function functional"), (80, "function functional"),
   (98, "function functional"), (121, "no junk"), (204, "function equation"),
   (206, "function equation"), (208, "function equation"), (211, "no direction"),
   (241, "function equation")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(208, "function equation")]

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
def priosOutCl : List (String × Nat) := [("Lblh", 1), ("Lblh", 2)]
def priosOutAx : List Nat := []

/-- **With those clauses left out of the clause side, the priorities agree**
(`AttrsAgree.priosBut`). Each clause of a run left out is aligned with the run's sentence at the
priority it states: `prios_split_at3`, `prios_split_at4`. -/
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

theorem sig_sizes : (sigItems c).length = 207 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 130, 93, 5, 32) := by
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

/-! ## Consistency for every H: `h(X) => (k(f(X) #Or g(X)) #Or #Bottom) #And {X *Int X >=Int 0 #Equals true}`, read by cases -/

/- The text's functions are `f`, `g`, `h` and `k`, all `[total]` (`OrNestH.read`). `f`, `g` and `k`
have one clause each, `f(X) => X`, `g(X) => X +Int 0`, `k(X) => X +Int 1`. `h` has the three clauses
`Parse.frClauses` writes for its equation, the empty alternative dropped and the `\or` under `k`
read as two alternatives: `pre ⌈k(f(X))⌉ ∧ (X *Int X >=Int 0) = true`, `rhs k(f(X))`; the same with
`k(g(X))`; and the last, `pre` the conjunction of their negations, `rhs k(f(X))`, `ens false`, all of
one priority. A clause's predicate is not `\top`, so `FnHyp` is shown here for every H (`fnHypH`),
by `fnHyp_of_decidedPre_withHooks`:
- Termination: `f`, `g` and `k` are placed before `h`, whose clauses apply them in their terms and
  predicates, and their clauses apply hooks only (`preRank_named`).
- Totality (`total_named` names `h`; `f`, `g` and `k` also follow here): at an Int n, `f(n)` is n,
  `g(n)` is `n + 0` and `k(m)` is `m + 1`, each its function's one result (`OrNestH.one_value`), and
  `n *Int n >=Int 0` is `true` since `n * n ≥ 0`. So both predicates of the first two clauses are
  true at n, and the first clause gives `h(n) = n + 1` (`OrNestH.h_value`).
- Agreement of `h` (`agree_named`): the last clause applies nowhere, its predicate being false
  where the other two are true; the first two apply at every n and have one result each, `n + 1`
  and `n + 0 + 1`, which are one value (`OrNestH.coherent`).
- No match independence, rule condition or clause condition is owed (`match_named`, `owed_rules`,
  `owed_clauses`), and the text has no open generator (`noRaw`).
So Γ with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).
`OrNestH` holds the proofs, over any semantics `d` that reads the clauses (`OrNestH.Reads`); the
statements after it are on `cH H`. -/

namespace OrNestH

def fS : Sym := 384
def gS : Sym := 385
def hS : Sym := 386
def kS : Sym := 387

def kfX : Term := .app kS [.app fS [.var 0]]
def kgX : Term := .app kS [.app gS [.var 0]]
/-- `X *Int X >=Int 0`. -/
def bX : Term := .app intGe [.app intMul [.var 0, .var 0], .dv Srt.int (.int 0)]

/-- A clause over `[X:Int]`, of priority 50. -/
def clX (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs, ens, prio := 50, aside := false, pre }

/-- `⌈t⌉ ∧ (X *Int X >=Int 0) = true`. -/
def preA (t : Term) : Cond := .and (.ceil Srt.int t) (.equals Srt.bool bX (.dv Srt.bool (.bool true)))

def clA : Clause := clX kfX none (preA kfX)
def clB : Clause := clX kgX none (preA kgX)
def clC : Clause := clX kfX (some (.dv Srt.bool (.bool false))) (.and (.not (preA kfX)) (.not (preA kgX)))

/-- A function of one Int argument with the one clause `l(X) => rhs`. -/
def fnP (l : Sym) (rhs : Term) : Fn := ⟨l, [Srt.int], Srt.int, [clX rhs none .top], true⟩

def rhsG : Term := .app intAdd [.var 0, .dv Srt.int (.int 0)]
def rhsK : Term := .app intAdd [.var 0, .dv Srt.int (.int 1)]

def fFn : Fn := fnP fS (.var 0)
def gFn : Fn := fnP gS rhsG
def kFn : Fn := fnP kS rhsK
def hFn : Fn := ⟨hS, [Srt.int], Srt.int, [clA, clB, clC], true⟩

/-- **The reading**: the text's functions are `f`, `g`, `h` and `k`, with these clauses (kernel). -/
theorem read : c.fns = [fFn, gFn, hFn, kFn] := by kernel_rfl

theorem names : c.symName fS = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.symName hS = "Lblh" ∧
    c.symName kS = "Lblk" := by decide +kernel
theorem lookupF : c.lookupFn fS = some fFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn gS = some gFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupK : c.lookupFn kS = some kFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn hS = some hFn := by rw [Semantics.lookupFn_eq]; rfl
theorem kinds : c.isCtor intAdd = false ∧ c.isCtor intMul = false ∧ c.isCtor intGe = false ∧
    (∀ f ∈ [fS, gS, kS], c.isCtor f = false ∧ c.isParam f = false ∧ c.isOvl f = false) := by
  decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-- What the proofs read of a semantics: the kinds of the hooks and functions the clauses apply,
the four functions, and that the values of Int are its literals. -/
structure Reads (d : Semantics) : Prop where
  addCtor : d.isCtor intAdd = false
  mulCtor : d.isCtor intMul = false
  geCtor : d.isCtor intGe = false
  fns : ∀ f ∈ [fS, gS, kS], d.isCtor f = false ∧ d.isParam f = false ∧ d.isOvl f = false
  lkF : d.lookupFn fS = some fFn
  lkG : d.lookupFn gS = some gFn
  lkK : d.lookupFn kS = some kFn
  lkH : d.lookupFn hS = some hFn
  shapes : d.shapesOK = true

section Clause

variable {d : Semantics} {σ : Subst}

theorem hooks : isHook intAdd = true ∧ isHook intMul = true ∧ isHook intGe = true := by decide +kernel
theorem notHooks : ∀ f ∈ [fS, gS, kS], isHook f = false := by decide +kernel

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

/-- t has the one result v under σ. -/
def Val (d : Semantics) (σ : Subst) (t : Term) (v : GroundTerm) : Prop :=
  EvalTerm d σ t (some v) ∧ ∀ r, EvalTerm d σ t r → r = some v

theorem val_var {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) : Val d σ (.var i) v := by
  have e : EvalTerm d σ (.var i) (σ.lookup i) := .var
  exact ⟨h ▸ e, fun r hr => (EvalTerm.var_inv hr).trans h⟩

theorem val_dv {s : Srt} {l : Lit} : Val d σ (.dv s l) (.dv s l) := ⟨.dv, fun _ hr => EvalTerm.dv_inv hr⟩

theorem val_hook2 {f : Sym} {t1 t2 : Term} {v1 v2 w : GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = true) (h1 : Val d σ t1 v1) (h2 : Val d σ t2 v2)
    (hr : d.hookRes f [v1, v2] = some (some w)) : Val d σ (.app f [t1, t2]) w := by
  refine ⟨.hook hc hk (rs := [some v1, some v2]) (.cons h1.1 (.cons h2.1 .nil))
    (fun vs hvs => by cases hvs; exact hr) (fun hn => by cases hn), fun r h => ?_⟩
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc hk h
  obtain ⟨r1, rs1, rfl, e1, hs1⟩ := EvalTerms.cons_inv hts
  obtain ⟨r2, rs2, rfl, e2, hs2⟩ := EvalTerms.cons_inv hs1
  obtain rfl := EvalTerms.nil_inv hs2
  rw [h1.2 _ e1, h2.2 _ e2] at hh
  have := hh [v1, v2] rfl
  rw [hr] at this
  exact (Option.some.inj this).symm

theorem val_call1 {f : Sym} {t : Term} {v w : GroundTerm} (hc : d.isCtor f = false) (hk : isHook f = false)
    (hp : d.isParam f = false) (ho : d.isOvl f = false) (h1 : Val d σ t v)
    (he : Eval d f [v] (some w)) (hu : ∀ r, Eval d f [v] r → r = some w) : Val d σ (.app f [t]) w := by
  refine ⟨.call (vs := [v]) hc hk (.cons h1.1 .nil) rfl he hp, fun r h => ?_⟩
  obtain ⟨rs, hts, hres⟩ := EvalTerm.call_inv hc hk hp ho h
  obtain ⟨r0, rs', rfl, e0, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  rw [h1.2 _ e0] at hres
  rcases hres with ⟨vs, hvs, hf⟩ | ⟨hn, -⟩
  · cases hvs
    exact hu _ hf
  · cases hn

/-- The substitution that gives X the value v. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sorted (n : Int) : d.WellSorted [Srt.int] (sg (int n)) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨int n, rfl, rmS_sortOf_int d _⟩
  | succ i => simp at hs

theorem sg_match (v : GroundTerm) : PatVals d (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem match0 {vs : List GroundTerm} (h : PatVals d σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- **A function with one clause `l(X) => rhs`** has, at n, the one result rhs has where X is n. -/
theorem one_value {l : Sym} {rhs : Term} {n : Int} {w : GroundTerm} (hfn : d.lookupFn l = some (fnP l rhs))
    (hv : ∀ σ : Subst, σ.lookup 0 = some (int n) → Val d σ rhs w) :
    Eval d l [int n] (some w) ∧ ∀ r, Eval d l [int n] r → r = some w := by
  refine ⟨.clause (cl := clX rhs none .top) hfn (List.mem_singleton_self _) (sg_sorted n) (sg_match _)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnP, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (hv _ rfl).1 (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  have hcl : (d.lookupFn l).bind (·.clauses[0]?) = some (clX rhs none .top) := by rw [hfn]; rfl
  obtain ⟨σ', -, hm, hr⟩ := Eval.inv_of_clause_bind (σ := sg (int n)) hcl
    (fun j hj cl' h' _ => by
      rw [hfn] at h'
      match j, hj, h' with
      | j + 1, _, h' => simp [fnP] at h')
    rfl (sg_sorted n) (sg_match _) h
  obtain ⟨v, hv', hl⟩ := match0 hm
  cases hv'
  exact (hv σ' hl).2 _ hr

theorem hookAdd (a b : Int) : d.hookRes intAdd [int a, int b] = some (some (int (a + b))) :=
  Semantics.hookRes_of_value rfl
theorem hookMul (a b : Int) : d.hookRes intMul [int a, int b] = some (some (int (a * b))) :=
  Semantics.hookRes_of_value rfl
theorem hookGe (a b : Int) : d.hookRes intGe [int a, int b] = some (some (bool (decide (a ≥ b)))) :=
  Semantics.hookRes_of_value rfl

theorem f_one (R : Reads d) (n : Int) : Eval d fS [int n] (some (int n)) ∧ ∀ r, Eval d fS [int n] r → r = some (int n) :=
  one_value R.lkF (fun _ h0 => val_var h0)

theorem g_one (R : Reads d) (n : Int) :
    Eval d gS [int n] (some (int (n + 0))) ∧ ∀ r, Eval d gS [int n] r → r = some (int (n + 0)) :=
  one_value R.lkG (fun _ h0 => val_hook2 R.addCtor hooks.1 (val_var h0) val_dv (hookAdd n 0))

theorem k_one (R : Reads d) (n : Int) :
    Eval d kS [int n] (some (int (n + 1))) ∧ ∀ r, Eval d kS [int n] r → r = some (int (n + 1)) :=
  one_value R.lkK (fun _ h0 => val_hook2 R.addCtor hooks.1 (val_var h0) val_dv (hookAdd n 1))

theorem callOK (R : Reads d) {f : Sym} (hf : f ∈ [fS, gS, kS]) :
    d.isCtor f = false ∧ isHook f = false ∧ d.isParam f = false ∧ d.isOvl f = false :=
  ⟨(R.fns f hf).1, notHooks f hf, (R.fns f hf).2.1, (R.fns f hf).2.2⟩

theorem kf_val (R : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) : Val d σ kfX (int (n + 1)) :=
  have hk := callOK R (f := kS) (by decide)
  have hf := callOK R (f := fS) (by decide)
  val_call1 hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
    (val_call1 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 (val_var h0) (f_one R n).1 (f_one R n).2)
    (k_one R n).1 (k_one R n).2

theorem kg_val (R : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) : Val d σ kgX (int (n + 0 + 1)) :=
  have hk := callOK R (f := kS) (by decide)
  have hg := callOK R (f := gS) (by decide)
  val_call1 hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
    (val_call1 hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (val_var h0) (g_one R n).1 (g_one R n).2)
    (k_one R (n + 0)).1 (k_one R (n + 0)).2

theorem sq_nonneg (n : Int) : n * n ≥ 0 := by
  rcases Int.le_total 0 n with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

theorem b_val (R : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) : Val d σ bX (bool true) := by
  have h := val_hook2 R.geCtor hooks.2.2
    (val_hook2 R.mulCtor hooks.2.1 (val_var h0) (val_var h0) (hookMul n n)) val_dv (hookGe (n * n) 0)
  rwa [decide_eq_true (sq_nonneg n)] at h

theorem preA_true (R : Reads d) {n : Int} {t : Term} {w : GroundTerm} (h0 : σ.lookup 0 = some (int n))
    (ht : Val d σ t w) : Holds d 1 σ (preA t) true := by
  have h := Holds.and (n := 1) (Holds.ceil (s := Srt.int) ht.1)
    (Holds.equals (s := Srt.bool) (b_val R h0).1 (EvalTerm.dv (c := d) (σ := σ) (s := Srt.bool) (lit := .bool true)))
  exact h

theorem preA_inv (R : Reads d) {n : Int} {t : Term} {w : GroundTerm} (h0 : σ.lookup 0 = some (int n))
    (ht : Val d σ t w) {r : Bool} (h : Holds d 1 σ (preA t) r) : r = true := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [ht.2 _ e1, (b_val R h0).2 _ e2, EvalTerm.dv_inv e3]
        rfl

theorem preC_inv (R : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Bool}
    (h : Holds d 1 σ clC.pre r) : r = false := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | not h1 =>
      rw [preA_inv R h0 (kf_val R h0) h1]
      rfl

theorem cl_of {cl : Clause} (h : cl ∈ hFn.clauses) : cl = clA ∨ cl = clB ∨ cl = clC := by
  simpa [hFn] using h

/-- **`h(n)` is `n + 1`**, by its first clause. -/
theorem h_value (R : Reads d) (n : Int) : Eval d hS [int n] (some (int (n + 1))) :=
  .clause (cl := clA) R.lkH (by simp [hFn]) (sg_sorted n) (sg_match _)
    (fun t ht => nomatch ht) (preA_true R rfl (kf_val R rfl))
    (fun cl' hcl' _ hlt => by
      rcases cl_of hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide))
    rfl (kf_val R rfl).1 (fun t ht => nomatch ht) .top

/-- A clause of h that applies at an argument list: the argument is an Int n, X is n, and the
clause is not the last. -/
theorem applies (R : Reads d) {cl : Clause} (hcl : cl ∈ hFn.clauses) {vs : List GroundTerm}
    (h : cl.AppliesAt d σ vs) : ∃ n, vs = [int n] ∧ σ.lookup 0 = some (int n) ∧ (cl = clA ∨ cl = clB) := by
  obtain ⟨hws, hm, -, hpre⟩ := h
  have hp : cl.pats = [.var 0] := by rcases cl_of hcl with rfl | rfl | rfl <;> rfl
  rw [hp] at hm
  obtain ⟨v, rfl, hl⟩ := match0 hm
  have h0 : ∃ w, σ.lookup 0 = some w ∧ d.sortOf w = some Srt.int := by
    rcases cl_of hcl with rfl | rfl | rfl <;> exact hws 0 (by decide) Srt.int rfl
  obtain ⟨w, hw, hwsrt⟩ := h0
  rw [hl] at hw
  obtain rfl := Option.some.inj hw
  obtain ⟨n, rfl⟩ := shape_int R.shapes hwsrt
  refine ⟨n, rfl, hl, ?_⟩
  rcases cl_of hcl with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd (preC_inv R hl hpre) (by simp)

/-- A result of a clause without existential variables and `ensures` is its right-hand side's. -/
theorem res_rhs {cl : Clause} (hx : cl.exs = []) (he : cl.ens = none) {r : Option GroundTerm}
    (h : cl.Res d σ r) : EvalTerm d σ cl.rhs r := by
  rcases h with ⟨-, ⟨-, -, h⟩ | ⟨t, w, ht, -⟩⟩ | ⟨hne, -⟩
  · exact h
  · rw [he] at ht; cases ht
  · exact absurd hx hne

/-- The one result of h's first or second clause at a match giving X the value n. -/
theorem res_ab (R : Reads d) {cl : Clause} (hcl : cl = clA ∨ cl = clB) {n : Int}
    (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm} (h : cl.Res d σ r) : r = some (int (n + 1)) := by
  rcases hcl with rfl | rfl
  · exact (kf_val R h0).2 _ (res_rhs rfl rfl h)
  · rw [(kg_val R h0).2 _ (res_rhs rfl rfl h), Int.add_zero]

/-- **Any two clauses of h are coherent**: the last applies nowhere, and the first two have the one
result `n + 1` at n. -/
theorem coherent (R : Reads d) {cl cl' : Clause} (hcl : cl ∈ hFn.clauses) (hcl' : cl' ∈ hFn.clauses) :
    Coherent d cl cl' := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨n, hv, h0, hab⟩ := applies R hcl ha
  obtain ⟨n', hv', h0', hab'⟩ := applies R hcl' ha'
  rw [hv] at hv'
  have e : n = n' := by simpa [KCore.int] using hv'
  subst e
  right
  intro r r' hr hr'
  rw [res_ab R hab h0 hr, res_ab R hab' h0' hr']

end Clause

end OrNestH

/-! ### The facts the deciders name -/

def callOrder : List Nat := [384, 385, 387, 386]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
/-- No clause applies, in a term or its predicate, a function placed after it. -/
theorem preRank_named : c.preRankObligationsFP callOrder = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [386] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [386] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- A clause's predicate is not `\top`. -/
theorem clausesPreTop_false : c.clausesPreTop = false := by decide +kernel

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

/-! ### `FnHyp` and consistency, for every H -/

theorem readsH (H : HookParams) : OrNestH.Reads (cH H) :=
  ⟨OrNestH.kinds.1, OrNestH.kinds.2.1, OrNestH.kinds.2.2.1, OrNestH.kinds.2.2.2,
   by rw [Semantics.lookupFn_withHooks]; exact OrNestH.lookupF,
   by rw [Semantics.lookupFn_withHooks]; exact OrNestH.lookupG,
   by rw [Semantics.lookupFn_withHooks]; exact OrNestH.lookupK,
   by rw [Semantics.lookupFn_withHooks]; exact OrNestH.lookupH, OrNestH.shapes⟩

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

/-- **The four functions are total under every H**: each has a value at every Int. -/
theorem totalsH (H : HookParams) : ∀ fn ∈ c.fns, fn.total = true → Total (cH H) fn.label := by
  intro fn hfn _ fn' hfn' vs hvs
  rw [OrNestH.read] at hfn
  have R := readsH H
  have one : ∀ {l : Sym} {g : Fn}, (cH H).lookupFn l = some g → g.args = [Srt.int] →
      (∀ n : Int, ∃ v, Eval (cH H) l [int n] (some v)) → (cH H).lookupFn l = some fn' →
      ∃ v, Eval (cH H) l vs (some v) := fun hl ha hall hl' => by
    rw [hl] at hl'
    cases hl'
    rw [ha] at hvs
    obtain ⟨v, rfl, hv⟩ := sortsOf_one hvs
    obtain ⟨n, rfl⟩ := shape_int R.shapes hv
    exact hall n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl
  · exact one R.lkF rfl (fun n => ⟨_, (OrNestH.f_one R n).1⟩) hfn'
  · exact one R.lkG rfl (fun n => ⟨_, (OrNestH.g_one R n).1⟩) hfn'
  · exact one R.lkH rfl (fun n => ⟨_, OrNestH.h_value R n⟩) hfn'
  · exact one R.lkK rfl (fun n => ⟨_, (OrNestH.k_one R n).1⟩) hfn'

/-- **The clauses of `h` agree under every H** (the function `agree_named` names). -/
theorem agreeH (H : HookParams) :
    ∀ f ∈ c.agreeObligationsI, ∀ fn, (cH H).lookupFn f = some fn → ClausesAgree (cH H) fn := by
  intro f hf fn hfn
  rw [agree_named] at hf
  obtain rfl := List.mem_singleton.mp hf
  rw [show (386 : Sym) = OrNestH.hS from rfl, (readsH H).lkH] at hfn
  cases hfn
  intro cl cl' hp _
  obtain ⟨h1, h2⟩ := mem_of_mem_pairs hp
  exact ⟨OrNestH.coherent (readsH H) h1 h2, OrNestH.coherent (readsH H) h2 h1⟩

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [preRank_named] at hg; cases hg)
    (totalsH H) (agreeH H) (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **`h(n) = n + 1`, for every H.** -/
theorem h_value (H : HookParams) (n : Int) : Eval (cH H) OrNestH.hS [int n] (some (int (n + 1))) :=
  OrNestH.h_value (readsH H) n

/-- **Γ with the step's closure has a model, for every H.** -/
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

theorem nj112 : (trS U.ax112).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj117 : (trS U.ax117).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj120 : (trS U.ax120).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax112, U.ax117, U.ax120], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj112]; exact orTopBot_valid hD rfl
  · rw [nj117]; exact orTopBot_valid hD rfl
  · rw [nj120]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax113, U.ax114, U.ax115, U.ax116, U.ax118, U.ax119],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax113, U.ax114, U.ax115, U.ax116, U.ax118, U.ax119],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax121).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (121)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax121).pat := by
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax102,
   U.ax103]

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


/-! ## Library sample: sentence 161, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax161).pat = (trAxiom [] [] U.ax161).pat := by decide +kernel
theorem s166_pattern : U.ax161.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax161.ax.sortVars.map sortVarKey ++ freeOf [] U.ax161.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax161.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 161 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax161.ax.sortVars U.ax161.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax161).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax161.ax.sortVars U.ax161.ax.pattern = t at he ⊢
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
/-- **Sentence 161 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax161 (trS U.ax161).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## Function equations (31 sentences) and priority equations (0 sentences)

One equation read as several clauses (items 2 to 4, sentence 208): the equation's right side holds
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
def fnPins : List (Nat × Nat) := [(2, 208), (3, 208), (4, 208)]

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

/-- Γ's item 2, the clause 0 of the 3 that sentence 208 is read as. -/
noncomputable def spItem2 : P := (TiePair.gammaPats c).getD 2 ⊥
theorem spItem2_at : (TiePair.gammaPats c)[2]? = some spItem2 := by decide +kernel
kernel_rfl fnText_at2 : fnText[2]? = some U.ax208
/-- **Γ's item 2 is not the text's sentence 208** (kernel): the sentence is uncovered. -/
theorem sp2_differs : spItem2 ≠ (trS U.ax208).pat := by decide +kernel

/-- Γ's item 3, the clause 1 of the 3 that sentence 208 is read as. -/
noncomputable def spItem3 : P := (TiePair.gammaPats c).getD 3 ⊥
theorem spItem3_at : (TiePair.gammaPats c)[3]? = some spItem3 := by decide +kernel
kernel_rfl fnText_at3 : fnText[3]? = some U.ax208
/-- **Γ's item 3 is not the text's sentence 208** (kernel): the sentence is uncovered. -/
theorem sp3_differs : spItem3 ≠ (trS U.ax208).pat := by decide +kernel

/-- **The clause 1 of `Lblh`, which `attrs_prios_but` leaves out, is Γ's item 3**, aligned with
sentence 208, and its priority is the one that sentence states (kernel). -/
theorem prios_split_at3 : ((c.allFns.takeWhile (c.symName ·.label != "Lblh")).map (·.clauses.length)).sum + 1 = 3 ∧
    (fnText[3]?).map (·.index) = some 208 ∧
    (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))[3]? = some (AttrsAgree.prioOf U.ax208.ax.attributes) := by
  decide +kernel

/-- Γ's item 4, the clause 2 of the 3 that sentence 208 is read as. -/
noncomputable def spItem4 : P := (TiePair.gammaPats c).getD 4 ⊥
theorem spItem4_at : (TiePair.gammaPats c)[4]? = some spItem4 := by decide +kernel
kernel_rfl fnText_at4 : fnText[4]? = some U.ax208
/-- **Γ's item 4 is not the text's sentence 208** (kernel): the sentence is uncovered. -/
theorem sp4_differs : spItem4 ≠ (trS U.ax208).pat := by decide +kernel

/-- **The clause 2 of `Lblh`, which `attrs_prios_but` leaves out, is Γ's item 4**, aligned with
sentence 208, and its priority is the one that sentence states (kernel). -/
theorem prios_split_at4 : ((c.allFns.takeWhile (c.symName ·.label != "Lblh")).map (·.clauses.length)).sum + 2 = 4 ∧
    (fnText[4]?).map (·.index) = some 208 ∧
    (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))[4]? = some (AttrsAgree.prioOf U.ax208.ax.attributes) := by
  decide +kernel

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at positions 2, 3, 4. -/
noncomputable def textPats : List P := (((fnText.map (trS · |>.pat)).set 2 spItem2).set 3 spItem3).set 4 spItem4

/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def pairSetAt : List Nat := [2, 3, 4]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h2, h3, h4⟩ := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3), List.getElem?_set_ne (Ne.symm h2), List.getElem?_map, hj]
  rfl

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the clauses of one equation (items 2, 3, 4), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([2, 3, 4] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item but the clauses of one equation (items 2, 3, 4) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([2, 3, 4] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h2 : j = 2
  · subst h2; simp at hu
  by_cases h3 : j = 3
  · subst h3; simp at hu
  by_cases h4 : j = 4
  · subst h4; simp at hu
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3), List.getElem?_set_ne (Ne.symm h2), List.getElem?_map] at ht
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


end KCore.TieE3MlEqRhsOrNest

#check @KCore.TieE3MlEqRhsOrNest.noRaw
#check @KCore.TieE3MlEqRhsOrNest.readsConfined_c
#check @KCore.TieE3MlEqRhsOrNest.userAxioms_eq
#check @KCore.TieE3MlEqRhsOrNest.coreOK
#check @KCore.TieE3MlEqRhsOrNest.account
#check @KCore.TieE3MlEqRhsOrNest.account_sizes
#check @KCore.TieE3MlEqRhsOrNest.account_classes
#check @KCore.TieE3MlEqRhsOrNest.account_absent
#check @KCore.TieE3MlEqRhsOrNest.absent_closed
#check @KCore.TieE3MlEqRhsOrNest.absent_proj_below_c
#check @KCore.TieE3MlEqRhsOrNest.absent_proj_below
#check @KCore.TieE3MlEqRhsOrNest.lists_in_account
#check @KCore.TieE3MlEqRhsOrNest.attrs_parts
#check @KCore.TieE3MlEqRhsOrNest.attrs_prios_false
#check @KCore.TieE3MlEqRhsOrNest.attrs_prios_but
#check @KCore.TieE3MlEqRhsOrNest.sig_origin_but_next
#check @KCore.TieE3MlEqRhsOrNest.decls_entailed
#check @KCore.TieE3MlEqRhsOrNest.consistent
#check @KCore.TieE3MlEqRhsOrNest.total_named
#check @KCore.TieE3MlEqRhsOrNest.fnHypH
#check @KCore.TieE3MlEqRhsOrNest.text_nextless
#check @KCore.TieE3MlEqRhsOrNest.nojunk_trivial_entailed
#check @KCore.TieE3MlEqRhsOrNest.nojunk_items_entailed
#check @KCore.TieE3MlEqRhsOrNest.nojunk_kitem_entailed
#check @KCore.TieE3MlEqRhsOrNest.cons_entailed
#check @KCore.TieE3MlEqRhsOrNest.idem_refuted
#check @KCore.TieE3MlEqRhsOrNest.lib166
#check @KCore.TieE3MlEqRhsOrNest.lib166_at_values
#print axioms KCore.TieE3MlEqRhsOrNest.noRaw
#print axioms KCore.TieE3MlEqRhsOrNest.readsConfined_c
#print axioms KCore.TieE3MlEqRhsOrNest.userAxioms_eq
#print axioms KCore.TieE3MlEqRhsOrNest.coreOK
#print axioms KCore.TieE3MlEqRhsOrNest.account
#print axioms KCore.TieE3MlEqRhsOrNest.account_sizes
#print axioms KCore.TieE3MlEqRhsOrNest.account_classes
#print axioms KCore.TieE3MlEqRhsOrNest.account_absent
#print axioms KCore.TieE3MlEqRhsOrNest.absent_closed
#print axioms KCore.TieE3MlEqRhsOrNest.absent_proj_below_c
#print axioms KCore.TieE3MlEqRhsOrNest.absent_proj_below
#print axioms KCore.TieE3MlEqRhsOrNest.lists_in_account
#print axioms KCore.TieE3MlEqRhsOrNest.attrs_parts
#print axioms KCore.TieE3MlEqRhsOrNest.attrs_prios_false
#print axioms KCore.TieE3MlEqRhsOrNest.attrs_prios_but
#print axioms KCore.TieE3MlEqRhsOrNest.sig_origin_but_next
#print axioms KCore.TieE3MlEqRhsOrNest.decls_entailed
#print axioms KCore.TieE3MlEqRhsOrNest.consistent
#print axioms KCore.TieE3MlEqRhsOrNest.total_named
#print axioms KCore.TieE3MlEqRhsOrNest.fnHypH
#print axioms KCore.TieE3MlEqRhsOrNest.text_nextless
#print axioms KCore.TieE3MlEqRhsOrNest.nojunk_trivial_entailed
#print axioms KCore.TieE3MlEqRhsOrNest.nojunk_items_entailed
#print axioms KCore.TieE3MlEqRhsOrNest.nojunk_kitem_entailed
#print axioms KCore.TieE3MlEqRhsOrNest.cons_entailed
#print axioms KCore.TieE3MlEqRhsOrNest.idem_refuted
#print axioms KCore.TieE3MlEqRhsOrNest.lib166
#print axioms KCore.TieE3MlEqRhsOrNest.lib166_at_values
#check @KCore.TieE3MlEqRhsOrNest.fnPins_ok
#check @KCore.TieE3MlEqRhsOrNest.fnText_all
#check @KCore.TieE3MlEqRhsOrNest.fns_account
#check @KCore.TieE3MlEqRhsOrNest.sp2_differs
#check @KCore.TieE3MlEqRhsOrNest.sp3_differs
#check @KCore.TieE3MlEqRhsOrNest.prios_split_at3
#check @KCore.TieE3MlEqRhsOrNest.sp4_differs
#check @KCore.TieE3MlEqRhsOrNest.prios_split_at4
#check @KCore.TieE3MlEqRhsOrNest.shape
#check @KCore.TieE3MlEqRhsOrNest.fns_entailed
#check @KCore.TieE3MlEqRhsOrNest.fns_from_text
#check @KCore.TieE3MlEqRhsOrNest.fn_prios
#check @KCore.TieE3MlEqRhsOrNest.gamma_from
#print axioms KCore.TieE3MlEqRhsOrNest.fnPins_ok
#print axioms KCore.TieE3MlEqRhsOrNest.fnText_all
#print axioms KCore.TieE3MlEqRhsOrNest.fns_account
#print axioms KCore.TieE3MlEqRhsOrNest.sp2_differs
#print axioms KCore.TieE3MlEqRhsOrNest.sp3_differs
#print axioms KCore.TieE3MlEqRhsOrNest.prios_split_at3
#print axioms KCore.TieE3MlEqRhsOrNest.sp4_differs
#print axioms KCore.TieE3MlEqRhsOrNest.prios_split_at4
#print axioms KCore.TieE3MlEqRhsOrNest.shape
#print axioms KCore.TieE3MlEqRhsOrNest.fns_entailed
#print axioms KCore.TieE3MlEqRhsOrNest.fns_from_text
#print axioms KCore.TieE3MlEqRhsOrNest.fn_prios
#print axioms KCore.TieE3MlEqRhsOrNest.gamma_from
