/-
  The tie (C14) on `f2-examples/e3-eq-exists-ml-in-or-float.kompile.kore`, the kompiled text of construct fixture e3-eq-exists-ml-in-or-float
  (`test/constructs/fixtures/e3-eq-exists-ml-in-or-float`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-eq-exists-ml-in-or-float`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3EqExistsMlInOrFloat.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 201 sentences of the user module E3-EQ-EXISTS-ML-IN-OR-FLOAT, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 205 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator
    (`noRaw`). It owes the fact of the held-named function `f` (`held_named`, `HeldOwed`) and the match
    independence of a clause (`match_named`).
    The consistency section, written by hand, proves the fact of the held-named function for every H
    (`held`: the variables of its clauses are held, or it has a result at every argument list of its
    sorts), and refutes the match independence it owes: for the clause `(clO Srt.float tAdd)` it is
    false for every H (`not_matchIndependent`), and so is `FnHyp` (`not_fnHypH`). `OpenDecided` holds
    for every H (`openDecidedH`). `Γc` with the step's closure has a model for every H all the same
    (`consistent`), outside the value model, whose construction reads `FnHyp` (`consistent_of_fnHyp`) or
    the named facts (`consistent_of_fnFacts`), the refuted one among them.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (151) is not its sentence (`un<j>_differs`) and no reading
    here ties it: the sentence is `uncovered`, and `fns_entailed` and `fns_from_text` leave it out.
    `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Constructor sentences (25): entailed by Γ (`cons_entailed`).
  - No junk (4 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (51): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence is uncovered), Γ's rule items, the five parts Γ defines by predicates, or
    definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp`, which is false for every H (`not_fnHypH`): not shown by this tie; no
    direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (48);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsMlInOrFloat

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-ml-in-or-float.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-in-or-float.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-in-or-float.kompile.kore" module "E3-EQ-EXISTS-ML-IN-OR-FLOAT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-EQ-EXISTS-ML-IN-OR-FLOAT")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 201 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The conjuncts of `wf` that fail on this text (`kcore account`); `coreOK` holds. -/
def wfFailing : List String := ["clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither"]

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [151, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173,
      174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 93, 94]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [24, 26, 28, 30]),
   ("distinctness", []),
   ("no junk", [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]),
   ("function functional", [75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 91]),
   ("hooked functional", [19, 20, 21, 22, 32, 33, 34, 35, 36, 37, 40, 41, 42, 46, 54, 55, 56, 57, 58, 59, 60, 61, 62,
      63, 64, 65, 67, 70, 72, 74, 81, 90, 92, 95, 96, 97, 98, 101, 102, 103, 104]),
   ("collection law", [43, 44, 45, 47, 48, 49, 50, 52, 53]),
   ("library", [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142,
      143, 144, 145, 146, 147, 148, 149, 150, 168, 186, 187, 202]),
   ("set idempotence", [51]),
   ("set-variable lemma", [117, 118, 119, 120, 121, 122, 123, 124, 204]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [31, 38, 39, 66, 68, 69, 71, 73, 99, 100, 105, 152, 153, 154, 155, 188, 189, 190, 191, 192,
      193, 194, 195, 196, 197, 198, 199, 200, 201, 203])]

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
    [("function equation", 30), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 15), ("injectivity", 4), ("distinctness", 0), ("no junk", 11), ("function functional", 15), ("hooked functional", 41), ("collection law", 9), ("library", 30), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 30)] := by
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
  [(188, "Bool"), (189, "Float"), (190, "GeneratedCounterCell"), (191, "GeneratedCounterCellOpt"),
   (192, "GeneratedTopCell"), (193, "GeneratedTopCellFragment"), (194, "Int"), (195, "K"),
   (196, "KCell"), (197, "KCellOpt"), (198, "KItem"), (199, "List"), (200, "Map"), (201, "Set")]

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
  [(15, "subsort"), (19, "hooked functional"), (31, "no direction"), (65, "hooked functional"),
   (66, "no direction"), (67, "hooked functional"), (68, "no direction"), (69, "no direction"),
   (70, "hooked functional"), (71, "no direction"), (72, "hooked functional"),
   (76, "function functional"), (81, "hooked functional"), (90, "hooked functional"),
   (96, "hooked functional"), (99, "no direction"), (100, "no direction"),
   (104, "hooked functional"), (107, "no junk"), (116, "no junk"), (117, "set-variable lemma"),
   (118, "set-variable lemma"), (119, "set-variable lemma"), (120, "set-variable lemma"),
   (121, "set-variable lemma"), (122, "set-variable lemma"), (123, "set-variable lemma"),
   (124, "set-variable lemma"), (126, "library"), (128, "library"), (129, "library"),
   (132, "library"), (133, "library"), (135, "library"), (136, "library"), (139, "library"),
   (140, "library"), (143, "library"), (144, "library"), (148, "library"),
   (151, "function equation"), (155, "no direction"), (158, "function equation"),
   (159, "function equation"), (168, "library"), (189, "no direction"), (203, "no direction"),
   (204, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(151, "function equation")]

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 136, 90, 4, 42) := by
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

/-! ## Consistency for every H: `f(X) => X #Or (#Exists B:Float. (B #And {B #Equals X +Float 1.0}))`, its held fact proved, its match independence refuted -/

/- The one function `f` has the one clause `FnMany.clF = InOrFloatFx.clO Srt.float tAdd`:
`[X:Float, #Or0:Float]`, `exs [1]`, `rhs #Or0`,
`post (#Or0 ∈ X) ∨ ∃B:Float. ((#Or0 ∈ B) ∧ (B = X +Float 1.0))` (the binder kept in its alternative,
`Cond.ex`). `f` is not declared `total` and the text holds no functional sentence of it.
- `f` is held-named (`held_named`): #Or0 is outside the clause's patterns and conditions, of the sort
  Float, of which the package's search exhibits no value. The fact owed of it holds for every H
  (`held`): Float has a value, the double 1.0 (`FnMany.sort_oneH`), so the clause's variables are held
  (`HeldOwed`'s first alternative, `Semantics.HeldFn`).
- The match independence `match_named` names, of `f`'s clause, is false for every H
  (`not_matchIndependent`): at `[1.0]` the clause decides, and its instances at #Or0 := 1.0 and at
  #Or0 := 2.0 (the binder at `1.0 +Float 1.0`, the double 2.0 in the registry) give 1.0 and 2.0, so
  it has no result there (`InOrFloatFx.not_mi`). So `FnHyp` is false for every H (`not_fnHypH`: `f`
  has no result at 1.0, `FnMany.no_result_one`). The statement is at 1.0 and not at every Float:
  where `x +Float 1.0` is x, or has no value of Float, the instances agree.
- Every function has at most one result, for every H (`fnDetH`, by `fnDet_of_coherent`): at a match
  giving X the value x, the instance at #Or0 := x gives x, so every result of `f`'s clause there is x
  (`InOrFloatFx.resEx_x`), whatever `x +Float 1.0` is.
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `Γc` with the step's closure has a model for every H (`consistent`), by
  `Faithful.Model.consistent_of_fnMany_agree` at `f`: the value model with `f` read as the set of
  its instances' values. Its hypotheses, each for every H: every premise of the theory but `f`'s own
  items avoids `f`'s name (`FnMany.avoidsOffH`; `f`'s clause applies at every argument of Float, so
  the theory states no rest of `f`), two matches of `f`'s clause at one argument agree on X
  (`FnMany.agreeH`), `fnDetH`, and the right-side predicate has a truth value (`FnMany.postDecH`:
  `X +Float 1.0` has one result at each value of Float, a value or none, the interpretation's at a
  point where the registry gives none, so the binder's alternative is decided at each value of the
  binder).

`InOrFloatFx` and `FnMany` hold the proofs; the statements after them are on `cH H`. -/

/-! ### Common facts -/

namespace InOrFloatFx

open GroundTerm KCore.Parse

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem sameResult_self (v : GroundTerm) : sameResult (some v) (some v) = true := sameResult_some.mpr rfl

/-- The instances of a clause whose one existential variable is the variable 1: σ with it set. -/
theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

/-- A substitution giving the variables 0 and 1 values of the two sorts is well sorted. -/
theorem sorted2 {a b : Srt} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) : d.WellSorted [a, b] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp at hs

/-- An application of an interpreted hooked symbol has the value `hookRes` gives at its arguments'
results, and none where an argument has none. -/
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

/-- `f(X) => Z` with `exs = [Z]` and `post := (Z ∈ X) ∨ ∃B:s. ((Z ∈ B) ∧ (B = t))`, X and Z of the
sort s; the binder B is the index 2, bound in its alternative. -/
def clO (s : Srt) (t : Term) : Clause :=
  { vars := [s, s], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .or (.mem s (.var 1) (.var 0))
      (.ex s (.and (.mem s (.var 1) (.var 2)) (.equals s (.var 2) t))) }

def fnO (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clO s t] }

/-- Under every σ giving X the value x, the term t has no result but the value y. -/
def TermAt (d : Semantics) (t : Term) (x y : GroundTerm) : Prop :=
  ∀ (σ : Subst) (r : Option GroundTerm), σ.lookup 0 = some x → EvalTerm d σ t r → r = some y

section Shape

variable {s : Srt} {t : Term} {x y : GroundTerm} {f : Sym}

/-- Where Z is X's value, `post` has no truth value but true: its first alternative holds. -/
theorem post_at_x (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some x) {b : Bool}
    (h : Holds d 2 σ (clO s t).post b) : b = true := by
  cases h with
  | or h h' =>
    cases h with
    | mem a1 a0 =>
      obtain rfl := EvalTerm.var_inv a1
      obtain rfl := EvalTerm.var_inv a0
      rw [h0, h1]; simp [sameResult_self]

/-- σ with the binder's index given the value y of the sort s. -/
theorem extends_y (σ : Subst) (hy : d.sortOf y = some s) : Extends d 2 [s] σ ((2, y) :: σ) :=
  ⟨fun _ hi => lkNe y σ (Nat.ne_of_lt hi), fun j s' hj => by
    match j, hj with
    | 0, hj => cases hj; exact ⟨y, lkSelf _ _ _, hy⟩
    | j + 1, hj => simp at hj⟩

/-- Where Z is t's value y, `post` has no truth value but true: the second alternative holds, at
the binder's value y. -/
theorem post_at_y (ht : TermAt d t x y) (hy : d.sortOf y = some s) (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some y) {b : Bool} (h : Holds d 2 σ (clO s t).post b) : b = true := by
  cases h with
  | @or _ _ _ _ b1 b2 h h' =>
    cases h' with
    | ex g hb hr =>
      have l1 : ((2, y) :: σ : Subst).lookup 1 = some y := (lkNe y σ (by decide)).trans h1
      have l2 : ((2, y) :: σ : Subst).lookup 2 = some y := lkSelf _ _ _
      have hg : g ((2, y) :: σ) = true := by
        have hb' := hb _ (extends_y σ hy)
        generalize g ((2, y) :: σ) = gb at hb'
        cases hb' with
        | and hm he =>
          cases hm with
          | mem a1 a2 =>
            cases he with
            | equals e1 e2 =>
              obtain rfl := EvalTerm.var_inv a1
              obtain rfl := EvalTerm.var_inv a2
              obtain rfl := EvalTerm.var_inv e1
              obtain rfl := ht _ _ ((lkNe y σ (by decide)).trans h0) e2
              rw [l1, l2]; simp [sameResult_self]
      have e2 : b2 = true := hr.mpr ⟨_, extends_y σ hy, hg⟩
      rw [e2]; simp

theorem exsFree_clO : (clO s t).exsFree = [1] := rfl
theorem exs_clO : (clO s t).exs ≠ [] := List.cons_ne_nil 1 []

/-- An instance at which Z has the value w and `post` has no truth value but true gives w. -/
theorem inst_eq {σ' : Subst} {w : GroundTerm} {r : Option GroundTerm} (h1 : σ'.lookup 1 = some w)
    (hp : ∀ b, Holds d 2 σ' (clO s t).post b → b = true) (h : InstIs d σ' (clO s t) r) : r = some w := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp' => cases hp _ hp'
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- **The instances at Z := x and Z := y do not agree on one result**, where y is not x: no r is
the result of every instance of the clause at a match giving X the value x. -/
theorem two_insts (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (h0 : σ.lookup 0 = some x) {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff (clO s t).exsFree σ σ' → d.WellSorted (clO s t).vars σ' → InstIs d σ' (clO s t) r) :
    False := by
  have h0' : ∀ w, ((1, w) :: σ : Subst).lookup 0 = some x := fun w => (lkNe _ _ (by decide)).trans h0
  have hw : ∀ w, d.sortOf w = some s → d.WellSorted (clO s t).vars ((1, w) :: σ) := fun w hw =>
    sorted2 (h0' w) hx (lkSelf _ _ _) hw
  have e1 := inst_eq (lkSelf 1 x σ) (fun _ hb => post_at_x (h0' x) (lkSelf _ _ _) hb)
    (hall _ (agree_set1 σ _) (hw x hx))
  have e2 := inst_eq (lkSelf 1 y σ) (fun _ hb => post_at_y ht hy (h0' y) (lkSelf _ _ _) hb)
    (hall _ (agree_set1 σ _) (hw y hy))
  rw [e1] at e2
  exact hne (Option.some.inj e2).symm

theorem pat_x {σ : Subst} (hm : PatVals d σ (clO s t).pats [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

/-- **`f(x)` has no result**, where t's value y at x is not x. -/
theorem no_res (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnO f s t)) {r : Option GroundTerm} (h : Eval d f [x] r) : False := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clO s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnO] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clO
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone (clO s t) (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted (clO s t).vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clO
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall
  | exNone hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall

/-- **The clause is not match independent**: it decides at `[x]` and has no result there. -/
theorem not_mi (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnO f s t)) : MatchIndependent d (clO s t) → False := by
  intro hm
  have hs : d.WellSorted (clO s t).vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
  have hdec : (clO s t).Decides d (fnO f s t) [(1, x), (0, x)] [x] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnO, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 exs_clO f (fnO f s t) [x] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex exs_clO
  · exact two_insts (σ := [(1, x), (0, x)]) ht hne hx hy rfl hall
  · exact two_insts (σ := [(1, x), (0, x)]) ht hne hx hy rfl hall

/-- **Every result of the clause at a match giving X the value x is x**: the instance at Z := x
gives x (its first alternative holds), and a result is the result of every instance. -/
theorem resEx_x (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some s) {r : Option GroundTerm}
    (h : (clO s t).ResEx d σ r) : r = some x := by
  have h0' : ((1, x) :: σ : Subst).lookup 0 = some x := (lkNe _ _ (by decide)).trans h0
  have hag : AgreeOff (clO s t).exsFree σ ((1, x) :: σ) := agree_set1 σ x
  have hws : d.WellSorted (clO s t).vars ((1, x) :: σ) := sorted2 h0' hx (lkSelf _ _ _) hx
  have key : ∀ r, InstIs d ((1, x) :: σ) (clO s t) r → r = some x := fun r hi =>
    inst_eq (lkSelf 1 x σ) (fun _ hb => post_at_x h0' (lkSelf _ _ _) hb) hi
  rcases h with ⟨σ₁, v, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩
  · exact key _ (hall _ hag hws)
  · exact absurd (key _ (hall _ hag hws)) (by simp)

end Shape

end InOrFloatFx

namespace FnMany

open GroundTerm InOrFloatFx KCore.Parse

def fF : Sym := 384

/-- The doubles 1.0 (`0x3FF0000000000000`) and 2.0 (`0x4000000000000000`). -/
def one : GroundTerm := .dv Srt.float (.float 53 11 4607182418800017408)
def two : GroundTerm := .dv Srt.float (.float 53 11 4611686018427387904)

/-- The term the binder is equated with, `X +Float 1.0`. -/
def tAdd : Term := .app floatAdd [.var 0, .dv Srt.float (.float 53 11 4607182418800017408)]

/-- **The reading**: the text's one function is f, not `total`, with the one clause
`[X:Float, #Or0:Float]`, `exs [1]`, `rhs #Or0`,
`post (#Or0 ∈ X) ∨ ∃B:Float. ((#Or0 ∈ B) ∧ (B = X +Float 1.0))`: the binder kept in its alternative. -/
theorem read : c.fns = [fnO fF Srt.float tAdd] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧
    c.symName floatAdd = "Lbl'UndsPlus'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float" ∧
    c.sortName Srt.float = "Float" := by decide +kernel

/-- Float is not confined; each alternative fixes #Or0 (the second by the binder, which its body
equates with a term over X): `clausePlainEx` admits the clause. -/
theorem plainEx : c.confined Srt.float = false ∧ c.clausePlainEx (clO Srt.float tAdd) = true := by
  decide +kernel

theorem lookupF : c.lookupFn fF = some (fnO fF Srt.float tAdd) := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor floatAdd = false := by decide +kernel

theorem sort_one : c.sortOf one = some Srt.float := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩
theorem sort_two : c.sortOf two = some Srt.float := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩

section Terms

variable {d : Semantics}

theorem addHook : isHook floatAdd = true := by decide +kernel

/-- `1.0 +Float 1.0` is 2.0 in the registry, so under every interpretation. -/
theorem hookOneOne : d.hookRes floatAdd [one, one] = some (some two) :=
  Semantics.hookRes_of_value (by decide +kernel)

/-- `X +Float 1.0` where X is 1.0: 2.0, and no other result. -/
theorem tAdd_at (hc : d.isCtor floatAdd = false) : TermAt d tAdd one two := by
  intro σ r h0 h
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc addHook h
  obtain ⟨r1, rs1, rfl, h1, hs1⟩ := EvalTerms.cons_inv hts
  obtain ⟨r2, rs2, rfl, h2, hs2⟩ := EvalTerms.cons_inv hs1
  obtain rfl := EvalTerms.nil_inv hs2
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [one, one] (by rw [h0]; rfl)
  rw [hookOneOne] at this
  exact (Option.some.inj this).symm

theorem two_ne : two ≠ one := by decide

/-- `_+Float_` has a result at every argument list, a value or none: it is a hooked symbol of the
registry, and at a point the registry leaves without a value the result is the interpretation's,
or none. -/
theorem hookRes_some (vs : List GroundTerm) : ∃ r, d.hookRes floatAdd vs = some r := by
  have hk : (hook floatAdd vs).isSome = true := by
    have h := addHook
    unfold isHook at h
    unfold hook at h ⊢
    cases e : hookTrie.find floatAdd with
    | none => rw [e] at h; cases h
    | some g => rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hk
  unfold Semantics.hookRes
  split
  · exact ⟨_, by rw [hr]; rfl⟩
  · exact ⟨r, hr⟩

/-- `X +Float 1.0` where X is x: the result `hookRes` gives at `[x, 1.0]`. -/
theorem tAdd_ev (hc : d.isCtor floatAdd = false) {σ : Subst} {x : GroundTerm} {r : Option GroundTerm}
    (h0 : σ.lookup 0 = some x) (hr : d.hookRes floatAdd [x, one] = some r) : EvalTerm d σ tAdd r :=
  .hook hc addHook (rs := [σ.lookup 0, some one]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hr)
    (fun hn => by rw [h0] at hn; cases hn)

end Terms

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some (fnO fF Srt.float tAdd) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

theorem tAdd_atH (H : HookParams) : TermAt (cH H) tAdd one two := tAdd_at (d := cH H) notCtor

theorem sort_oneH (H : HookParams) : (cH H).sortOf one = some Srt.float := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_one
theorem sort_twoH (H : HookParams) : (cH H).sortOf two = some Srt.float := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_two

/-- **`f(1.0)` has no result, for every H**: neither a value nor none. Its instances at
#Or0 := 1.0 and at #Or0 := 2.0 give 1.0 and 2.0. -/
theorem no_result_one (H : HookParams) (r : Option GroundTerm) : ¬ Eval (cH H) fF [one] r :=
  fun h => no_res (tAdd_atH H) two_ne (sort_oneH H) (sort_twoH H) (lookupFH H) h

/-! ### The model with f read as its instances' values, for every H -/

section Model

open KCore.Faithful KCore.Faithful.Model

def nF : String := "Lblf"
def fnF : Fn := fnO fF Srt.float tAdd
def clF : Clause := clO Srt.float tAdd

theorem name_f : c.symName fF = nF := by decide +kernel
theorem plain_f : instDecode? nF = none := by decide +kernel
theorem spare_f : GenEqs.spareSymB c nF = true := by decide +kernel
theorem values_f : GenEqs.NameFree.valuesN c [nF] = true := by rw [GenEqs.NameFree.valuesN]; decide_cheap 40
theorem hooks_f : hookSigs.all (fun k => GenEqs.NameFree.appOKN c [nF] k.name) = true := by decide_cheap 40
theorem params_f : c.params.all (fun k => GenEqs.NameFree.appOKN c [nF] k.sig.name) = true := by decide_cheap 40
theorem fns_f : c.allFns.all (fun g => decide (g.label = fF) || GenEqs.NameFree.appOKN c [nF] g.label) = true := by
  decide_cheap 40
theorem lists_f : listsOffB c fF nF = true := by rw [listsOffB]; decide_cheap 40
theorem kok_f : ownKokB c fnF clF = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem f_one : (c.allFns.filter (fun g => decide (g.label = fF))).length = 1 := by decide +kernel

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) ((coreOKEx_withHooks_fm c H).trans coreEx)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- f's clause applies at every argument of Float. -/
theorem not_fails_f {d : Semantics} {x : GroundTerm} (hx : d.sortOf x = some Srt.float) : ¬ Fails d [x] clF := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : d.WellSorted clF.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **Every premise but f's own items avoids `Lblf`, for every H.** -/
theorem avoidsOffH (H : HookParams) : AvoidsOff (cH H) fF ((cH H).symName fF) := by
  have hn : (cH H).symName fF = nF := name_f
  rw [hn]
  refine avoidsOff_of_lists (rangeBelowH H) (listsOff_withHooks H lists_f) values_f
    (List.all_eq_true.mp hooks_f) (List.all_eq_true.mp params_f)
    (fun g hg hl => by
      have h1 : GenEqs.NameFree.appOKN c [nF] g.label = true := by
        have := List.all_eq_true.mp fns_f g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fF)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hH : fnF ∈ c.allFns.filter (fun g => decide (g.label = fF)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp [fnF]), by simp [fnF, fnO]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp f_one
  rw [hx, List.mem_singleton] at hfn' hH
  obtain rfl : fn = fnF := hfn'.trans hH.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.float := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails_f hx (hall clF (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnF, fnO])

/-- The value of X at a match of a clause whose pattern is X and whose X is of the sort s. -/
theorem match0 {d : Semantics} {cl : Clause} {s : Srt} (hp : cl.pats = [.var 0]) (hu : 0 ∈ cl.univ)
    (hv : cl.vars[0]? = some s) {σ : Subst} {vs : List GroundTerm} (ha : cl.AppliesAt d σ vs) :
    ∃ x, vs = [x] ∧ σ.lookup 0 = some x ∧ d.sortOf x = some s := by
  have hm : PatVals d σ [.var 0] vs := hp ▸ ha.2.1
  obtain ⟨x, vs', rfl, hx, hs⟩ := PatVals.cons_inv hm
  obtain rfl : vs' = [] := by cases hs; rfl
  obtain ⟨v, hv0, hvs⟩ := ha.1 0 hu s hv
  have e : some v = some x := hv0.symm.trans (PatVal.var_inv hx)
  obtain rfl := Option.some.inj e
  exact ⟨v, rfl, hv0, hvs⟩

/-- **Two matches of f's clause at one argument agree on X, for every H.** -/
theorem agreeH (H : HookParams) : ∀ ws σ₁ σ₂, clF.AppliesAt (cH H) σ₁ ws → clF.AppliesAt (cH H) σ₂ ws →
    ∀ i < clF.vars.length, i ∉ clF.exsFree → σ₁.lookup i = σ₂.lookup i := by
  intro ws σ₁ σ₂ h1 h2 i hi hx
  rw [show clF.exsFree = [1] from rfl] at hx
  have hi0 : i = 0 := by
    have hl : clF.vars.length = 2 := rfl
    simp only [List.mem_singleton] at hx
    omega
  subst hi0
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl h1
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl h2
  cases hx'
  rw [h0, h0']

/-- **f's clause is coherent with itself, for every H**: at two matches at one argument x, every
result of the clause is x (`resEx_x`). -/
theorem coh_clF (H : HookParams) : Coherent (cH H) clF clF := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl ha'
  cases hx'
  refine .inr fun r r' hr hr' => ?_
  rcases hr with ⟨he, -⟩ | ⟨-, hr⟩
  · exact absurd he exs_clO
  rcases hr' with ⟨he, -⟩ | ⟨-, hr'⟩
  · exact absurd he exs_clO
  rw [resEx_x (t := tAdd) h0 hx hr, resEx_x (t := tAdd) h0' hx hr']

/-- **f's right-side predicate has a truth value, for every H**, where X is a value of Float: its
binder's alternative is decided at each value of the binder, `X +Float 1.0` having one result. -/
theorem postDecH (H : HookParams) : ClausePostDecided (cH H) := by
  classical
  intro fn hfn cl hcl σ hσ
  have hfns : (cH H).fns = [fnO fF Srt.float tAdd] := read
  rw [hfns, List.mem_singleton] at hfn
  subst hfn
  simp only [fnO, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, h0, -⟩ := hσ 0 Srt.float rfl
  obtain ⟨r, hr⟩ := hookRes_some (d := cH H) [x, one]
  let g : Subst → Bool := fun σ' =>
    (σ'.lookup 1).isSome && sameResult (σ'.lookup 1) (σ'.lookup 2) && sameResult (σ'.lookup 2) r
  have hb : ∀ σ', Extends (cH H) 2 [Srt.float] σ σ' →
      Holds (cH H) (2 + 1) σ' (.and (.mem Srt.float (.var 1) (.var 2)) (.equals Srt.float (.var 2) tAdd)) (g σ') :=
    fun σ' hext => Holds.and (Holds.mem .var .var)
      (Holds.equals .var (tAdd_ev (d := cH H) notCtor ((hext.1 0 (by decide)).trans h0) hr))
  exact ⟨_, Holds.or (Holds.mem .var .var)
    (Holds.ex (b := decide (∃ σ', Extends (cH H) 2 [Srt.float] σ σ' ∧ g σ' = true))
      g hb decide_eq_true_iff)⟩

end Model

end FnMany

/-! ### The facts the deciders name -/

def callOrder : List Nat := [FnMany.fF]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `f`'s. -/
theorem match_named : c.matchObligationsL = [(FnMany.fF, 0)] := by decide +kernel
/-- The function whose clause holds a variable of a sort the package's search exhibits no value of
(#Or0, of Float): `f`. -/
theorem held_named : c.heldObligations = [FnMany.fF] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### The held fact proved, the owed match independence refuted, `FnHyp` false, and consistency, for every H -/

section Stated

open GroundTerm InOrFloatFx FnMany KCore.Parse KCore.Faithful KCore.Faithful.Model

/-- **The fact owed of the held-named function f holds, for every H**: f's clause's variables are
of the sort Float, which has the value 1.0 (`HeldOwed`'s first alternative). -/
theorem held (H : HookParams) : ∀ f ∈ c.heldObligations, HeldOwed (cH H) f := by
  intro f hf fn hfn
  rw [held_named, List.mem_singleton] at hf
  subst hf
  rw [lookupFH H] at hfn
  cases hfn
  refine .inl ?_
  intro cl hcl i s hs
  simp only [fnO, List.mem_singleton] at hcl
  subst hcl
  have hv : (clO Srt.float tAdd).vars = [Srt.float, Srt.float] := rfl
  rw [hv] at hs
  refine .inr ⟨one, ?_⟩
  match i, hs with
  | 0, hs => cases hs; exact sort_oneH H
  | 1, hs => cases hs; exact sort_oneH H
  | _ + 2, hs => simp at hs

/-- **The owed fact the package names for f's clause, `MatchIndependent`, is false, for every H.** -/
theorem not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) (clO Srt.float tAdd) :=
  not_mi (tAdd_atH H) two_ne (sort_oneH H) (sort_twoH H) (lookupFH H)

/-- **`FnHyp` is false, for every H**: f has no result at 1.0. -/
theorem not_fnHypH (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [one] = some (fnO fF Srt.float tAdd).args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
  obtain ⟨r, hr⟩ := hf.1 (fnO fF Srt.float tAdd)
    (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_singleton_self _) [one] hso
  exact no_result_one H r hr

/-- **Every function has at most one result, for every H**: every result of f's clause at a match
is the argument; sort predicates as in `Faithful.fnDet_of_agree`. -/
theorem fnDetH (H : HookParams) : FnDet (cH H) := by
  refine fnDet_of_coherent fun f fn hfn cl hcl cl' hcl' hprio => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · have hfns : (cH H).fns = [fnO fF Srt.float tAdd] := read
    rw [hfns, List.mem_singleton] at hu
    subst hu
    simp only [fnO, List.mem_singleton] at hcl hcl'; subst hcl hcl'
    exact coh_clF H
  · by_cases he : cl = cl'
    · subst he
      intro vs σ σ' _ _ _ _ _ _ _
      refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
        fun i hi => absurd hi ?_, fun t ht => ?_⟩
      · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
        rw [hr, varOccs]
        exact List.not_mem_nil
      · rw [sortPreds_ens hp cl hcl] at ht; cases ht
    · rcases mem_pairs_of_ne hcl hcl' he with hpr | hpr
      · exact (sortPreds_agree hp cl cl' hpr hprio).1
      · refine (sortPreds_agree hp cl' cl hpr ?_).2
        rcases hprio with h | h | h
        · exact .inl h.symm
        · exact .inr (.inr h)
        · exact .inr (.inl h)

/-- **Γc with the step's closure has a model, for every H** (`consistent_of_fnMany_agree` at f). -/
theorem consistent (H : HookParams) : Consistent (cH H) := by
  have hfns : (cH H).fns = [fnO fF Srt.float tAdd] := read
  refine consistent_of_fnMany_agree (f := fF) (fn := fnF) (cl := clF) (a := Srt.float)
    ((coreOKEx_withHooks_fm c H).trans coreEx) (by rw [hfns]; simp [fnF]) rfl rfl rfl exs_clO
    (by rw [show (cH H).symName fF = nF from name_f]; exact plain_f)
    (by rw [show (cH H).symName fF = nF from name_f, spareSymB_withHooks_fm]; exact spare_f)
    (avoidsOffH H) (by rw [ownKokB_withHooks]; exact kok_f) (fnDetH H) (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) (postDecH H) (openLaws_of_plain noRaw)
  rw [hfns, List.mem_singleton] at hg'
  subst hg'
  exact absurd rfl hl

end Stated

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

theorem nj106 : (trS U.ax106).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj107 : (trS U.ax107).pat = orTopBot (sym (.sort "SortFloat")) := by decide +kernel
theorem nj112 : (trS U.ax112).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj115 : (trS U.ax115).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax106, U.ax107, U.ax112, U.ax115], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl
  · rw [nj106]; exact orTopBot_valid hD rfl
  · rw [nj107]; exact orTopBot_valid hD rfl
  · rw [nj112]; exact orTopBot_valid hD rfl
  · rw [nj115]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax108, U.ax109, U.ax110, U.ax111, U.ax113, U.ax114],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax108, U.ax109, U.ax110, U.ax111, U.ax113, U.ax114],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax116).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (116)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax116).pat := by
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
   U.ax16, U.ax17, U.ax18, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30, U.ax93,
   U.ax94]

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

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
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


/-! ## Function equations (30 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 151) is not its sentence (`un<j>_differs`), and no reading here gives it from
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

/-- Γ's item 0 (sentence 151): no reading here ties it. -/
noncomputable def unItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem unItem0_at : (TiePair.gammaPats c)[0]? = some unItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax151
/-- **Γ's item 0 is not the text's sentence 151** (kernel): the sentence is uncovered. -/
theorem un0_differs : unItem0 ≠ (trS U.ax151).pat := by decide +kernel

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 0. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 unItem0

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

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the untied ones (items 0), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([0] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item but the untied ones (items 0) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([0] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h0 : j = 0
  · subst h0; simp at hu
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
    ∀ ad ∈ [U.ax106, U.ax107, U.ax112, U.ax115], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax108, U.ax109, U.ax110, U.ax111, U.ax113, U.ax114],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax116).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 51 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax51).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE3EqExistsMlInOrFloat

#check @KCore.TieE3EqExistsMlInOrFloat.noRaw
#check @KCore.TieE3EqExistsMlInOrFloat.readsConfined_c
#check @KCore.TieE3EqExistsMlInOrFloat.userAxioms_eq
#check @KCore.TieE3EqExistsMlInOrFloat.coreOK
#check @KCore.TieE3EqExistsMlInOrFloat.account
#check @KCore.TieE3EqExistsMlInOrFloat.account_sizes
#check @KCore.TieE3EqExistsMlInOrFloat.account_classes
#check @KCore.TieE3EqExistsMlInOrFloat.account_absent
#check @KCore.TieE3EqExistsMlInOrFloat.absent_closed
#check @KCore.TieE3EqExistsMlInOrFloat.absent_proj_below_c
#check @KCore.TieE3EqExistsMlInOrFloat.absent_proj_below
#check @KCore.TieE3EqExistsMlInOrFloat.lists_in_account
#check @KCore.TieE3EqExistsMlInOrFloat.attrs_agree
#check @KCore.TieE3EqExistsMlInOrFloat.sig_origin_but_next
#check @KCore.TieE3EqExistsMlInOrFloat.decls_entailed
#check @KCore.TieE3EqExistsMlInOrFloat.consistent
#check @KCore.TieE3EqExistsMlInOrFloat.held_named
#check @KCore.TieE3EqExistsMlInOrFloat.held
#check @KCore.TieE3EqExistsMlInOrFloat.not_matchIndependent
#check @KCore.TieE3EqExistsMlInOrFloat.not_fnHypH
#check @KCore.TieE3EqExistsMlInOrFloat.text_nextless
#check @KCore.TieE3EqExistsMlInOrFloat.nojunk_trivial_entailed
#check @KCore.TieE3EqExistsMlInOrFloat.nojunk_items_entailed
#check @KCore.TieE3EqExistsMlInOrFloat.nojunk_kitem_entailed
#check @KCore.TieE3EqExistsMlInOrFloat.cons_entailed
#check @KCore.TieE3EqExistsMlInOrFloat.idem_refuted
#check @KCore.TieE3EqExistsMlInOrFloat.owed_rules
#check @KCore.TieE3EqExistsMlInOrFloat.owed_clauses
#check @KCore.TieE3EqExistsMlInOrFloat.openDecidedH
#check @KCore.TieE3EqExistsMlInOrFloat.gammaCl_eq
#check @KCore.TieE3EqExistsMlInOrFloat.decls_entailed_c
#check @KCore.TieE3EqExistsMlInOrFloat.nojunk_trivial_entailed_c
#check @KCore.TieE3EqExistsMlInOrFloat.nojunk_items_entailed_c
#check @KCore.TieE3EqExistsMlInOrFloat.nojunk_kitem_entailed_c
#check @KCore.TieE3EqExistsMlInOrFloat.cons_entailed_c
#check @KCore.TieE3EqExistsMlInOrFloat.idem_refuted_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.noRaw
#print axioms KCore.TieE3EqExistsMlInOrFloat.readsConfined_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.userAxioms_eq
#print axioms KCore.TieE3EqExistsMlInOrFloat.coreOK
#print axioms KCore.TieE3EqExistsMlInOrFloat.account
#print axioms KCore.TieE3EqExistsMlInOrFloat.account_sizes
#print axioms KCore.TieE3EqExistsMlInOrFloat.account_classes
#print axioms KCore.TieE3EqExistsMlInOrFloat.account_absent
#print axioms KCore.TieE3EqExistsMlInOrFloat.absent_closed
#print axioms KCore.TieE3EqExistsMlInOrFloat.absent_proj_below_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.absent_proj_below
#print axioms KCore.TieE3EqExistsMlInOrFloat.lists_in_account
#print axioms KCore.TieE3EqExistsMlInOrFloat.attrs_agree
#print axioms KCore.TieE3EqExistsMlInOrFloat.sig_origin_but_next
#print axioms KCore.TieE3EqExistsMlInOrFloat.decls_entailed
#print axioms KCore.TieE3EqExistsMlInOrFloat.consistent
#print axioms KCore.TieE3EqExistsMlInOrFloat.held_named
#print axioms KCore.TieE3EqExistsMlInOrFloat.held
#print axioms KCore.TieE3EqExistsMlInOrFloat.not_matchIndependent
#print axioms KCore.TieE3EqExistsMlInOrFloat.not_fnHypH
#print axioms KCore.TieE3EqExistsMlInOrFloat.text_nextless
#print axioms KCore.TieE3EqExistsMlInOrFloat.nojunk_trivial_entailed
#print axioms KCore.TieE3EqExistsMlInOrFloat.nojunk_items_entailed
#print axioms KCore.TieE3EqExistsMlInOrFloat.nojunk_kitem_entailed
#print axioms KCore.TieE3EqExistsMlInOrFloat.cons_entailed
#print axioms KCore.TieE3EqExistsMlInOrFloat.idem_refuted
#print axioms KCore.TieE3EqExistsMlInOrFloat.owed_rules
#print axioms KCore.TieE3EqExistsMlInOrFloat.owed_clauses
#print axioms KCore.TieE3EqExistsMlInOrFloat.openDecidedH
#print axioms KCore.TieE3EqExistsMlInOrFloat.gammaCl_eq
#print axioms KCore.TieE3EqExistsMlInOrFloat.decls_entailed_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.nojunk_trivial_entailed_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.nojunk_items_entailed_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.nojunk_kitem_entailed_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.cons_entailed_c
#print axioms KCore.TieE3EqExistsMlInOrFloat.idem_refuted_c
#check @KCore.TieE3EqExistsMlInOrFloat.fns_account
#check @KCore.TieE3EqExistsMlInOrFloat.un0_differs
#check @KCore.TieE3EqExistsMlInOrFloat.shape
#check @KCore.TieE3EqExistsMlInOrFloat.fns_entailed
#check @KCore.TieE3EqExistsMlInOrFloat.fns_from_text
#check @KCore.TieE3EqExistsMlInOrFloat.fn_prios
#check @KCore.TieE3EqExistsMlInOrFloat.gamma_from
#print axioms KCore.TieE3EqExistsMlInOrFloat.fns_account
#print axioms KCore.TieE3EqExistsMlInOrFloat.un0_differs
#print axioms KCore.TieE3EqExistsMlInOrFloat.shape
#print axioms KCore.TieE3EqExistsMlInOrFloat.fns_entailed
#print axioms KCore.TieE3EqExistsMlInOrFloat.fns_from_text
#print axioms KCore.TieE3EqExistsMlInOrFloat.fn_prios
#print axioms KCore.TieE3EqExistsMlInOrFloat.gamma_from
