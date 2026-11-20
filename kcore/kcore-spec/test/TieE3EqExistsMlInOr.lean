/-
  The tie (C14) on `f2-examples/e3-eq-exists-ml-in-or.kompile.kore`, the kompiled text of construct fixture e3-eq-exists-ml-in-or
  (`test/constructs/fixtures/e3-eq-exists-ml-in-or`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-eq-exists-ml-in-or`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3EqExistsMlInOr.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 177 sentences of the user module E3-EQ-EXISTS-ML-IN-OR, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 205 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator
    (`noRaw`). It owes the match independence of a clause (`match_named`).
    The consistency section, written by hand, refutes the match independence it owes: for the clause
    `(clB Srt.bool tNot)` it is false for every H (`f_not_matchIndependent`), and so is `FnHyp`
    (`not_fnHypH`). Of the other clause `match_named` names, tiegen reads no statement. `OpenDecided`
    holds for every H (`openDecidedH`). `Γc` with the step's closure has a model for every H all the
    same (`consistent`), outside the value model, whose construction reads `FnHyp`
    (`consistent_of_fnHyp`) or the named facts (`consistent_of_fnFacts`), the refuted one among them.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0, 1 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Items 0 (131), 1 (132) are not their sentences (`un<j>_differs`)
    and no reading here ties them: those sentences are `uncovered`, and `fns_entailed` and
    `fns_from_text` leave them out. `fns_from_text` (the converse), `fn_prios` (the priorities the
    sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (48): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    items 0, 1 (whose sentences are uncovered), Γ's rule items, the five parts Γ defines by
    predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp`, which is false for every H (`not_fnHypH`): not shown by this tie; no
    direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (24);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (2).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsMlInOr

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore" module "E3-EQ-EXISTS-ML-IN-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-EQ-EXISTS-ML-IN-OR")

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
def wfFailing : List String := ["clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither"]

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [131, 132, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152,
      153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 79, 80]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [88, 89, 90, 91, 92, 93, 94, 95, 96, 97]),
   ("function functional", [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 37, 38, 39, 43, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
      61, 63, 78, 81, 82, 83, 84, 85, 86]),
   ("collection law", [40, 41, 42, 44, 45, 46, 47, 49, 50]),
   ("library", [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123,
      124, 125, 126, 127, 128, 129, 130, 164, 165, 179]),
   ("set idempotence", [48]),
   ("set-variable lemma", [98, 99, 100, 101, 102, 103, 104, 105, 180]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 36, 62, 87, 133, 134, 135, 136, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
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
    [("function equation", 29), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 32), ("collection law", 9), ("library", 28), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 21)] := by
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
  [(97, "no junk"), (98, "set-variable lemma"), (99, "set-variable lemma"),
   (100, "set-variable lemma"), (101, "set-variable lemma"), (102, "set-variable lemma"),
   (103, "set-variable lemma"), (104, "set-variable lemma"), (105, "set-variable lemma"),
   (108, "library"), (109, "library"), (112, "library"), (113, "library"), (115, "library"),
   (116, "library"), (119, "library"), (120, "library"), (123, "library"), (124, "library"),
   (128, "library"), (131, "function equation"), (132, "function equation"), (136, "no direction"),
   (180, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(131, "function equation"), (132, "function equation")]

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

/-! ## Consistency for every H: `f(X) => X #Or (#Exists B:Bool. (B #And {B #Equals notBool X}))`, its match independence refuted -/

/- The functions `f` and `fx` have one clause each, `FnMany.clF = InOrFx.clB Srt.bool tNot` and
`InOrFx.clB Srt.bool tX`: `[X:Bool, B:Bool, #Or0:Bool]`, `exs [1, 2]`, `rhs #Or0`,
`post (#Or0 ∈ X) ∨ ((#Or0 ∈ B) ∧ (B = t))`, t being `notBool X` for `f` and X for `fx` (the binder of
the confined Bool moved over the `\or`). Neither is declared `total` and the text holds no
functional sentence of either.
- The match independence `match_named` names for `f`'s clause is false for every H
  (`f_not_matchIndependent`): at `[true]` the clause decides, and its instances at B, #Or0 := true
  and at B, #Or0 := false give `true` and `false` (`notBool true` is `false`), so it has no result
  there (`InOrFx.not_mi`). So `FnHyp` is false for every H (`not_fnHypH`: `f` has no result at
  `true`, `FnMany.f_no_result`). Of `fx`'s clause, which `match_named` names too, nothing is stated
  here but its results: `fx(b)` is b alone (`FnMany.fx_value`, `FnMany.fx_alone`).
- Every function has at most one result, for every H (`fnDetH`, by `fnDet_of_coherent`): a result
  of either clause at a match giving X the value x is x (`FnMany.resEx_x`).
- Evaluation solves `fx`'s equation, for every H (`fx_solves`): `fx(x)` is x, the one value its
  instances give.
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `Γc` with the step's closure has a model for every H (`consistent`), by
  `Faithful.Model.consistent_of_fnMany_agree` at `f`: the value model with `f` read as the set of its
  instances' values. Its hypotheses, each for every H: every premise of the theory but `f`'s own
  items avoids `f`'s name (`FnMany.avoidsOffH`; `f`'s clause applies at every argument of Bool, so
  the theory states no rest of `f`), two matches of `f`'s clause at one argument agree on X
  (`FnMany.agreeH`), `fnDetH`, `fx_solves`, and the right-side predicates have truth values
  (`FnMany.postDecH`).

`InOrFx` and `FnMany` hold the proofs; the statements after them are on `cH H`. -/

/-! ### Common facts -/

namespace InOrFx

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

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

/-- The instances of a clause whose existential variables are the variables 1 and 2: σ with them
set. -/
theorem agree_set12 (σ : Subst) (w1 w2 : GroundTerm) : AgreeOff [1, 2] σ ((2, w2) :: (1, w1) :: σ) := fun i hi => by
  have h1 : i ≠ 1 := fun h => hi (by rw [h]; decide)
  have h2 : i ≠ 2 := fun h => hi (by rw [h]; decide)
  rw [lkNe _ _ h2, lkNe _ _ h1]

/-- A substitution giving the variables 0, 1 and 2 values of the three sorts is well sorted. -/
theorem sorted3 {a b e : Srt} {x w1 w2 : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w1) (hw1 : d.sortOf w1 = some b) (h2 : σ.lookup 2 = some w2)
    (hw2 : d.sortOf w2 = some e) : d.WellSorted [a, b, e] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w1, h1, hw1⟩
  | 2, hs => cases hs; exact ⟨w2, h2, hw2⟩
  | i + 3, hs => simp at hs

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

/-- `f(X) => Z` with `exs = [B, Z]` and `post := (Z ∈ X) ∨ ((Z ∈ B) ∧ (B = t))`, the three
variables of the sort s. -/
def clB (s : Srt) (t : Term) : Clause :=
  { vars := [s, s, s], pats := [.var 0], req := none, rhs := .var 2, ens := none, exs := [1, 2],
    post := .or (.mem s (.var 2) (.var 0)) (.and (.mem s (.var 2) (.var 1)) (.equals s (.var 1) t)) }

def fnB (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clB s t] }

/-- Under every σ giving X the value x, the term t has the value y and no other result. -/
structure TermIs (d : Semantics) (t : Term) (x y : GroundTerm) : Prop where
  ev : ∀ (σ : Subst), σ.lookup 0 = some x → EvalTerm d σ t (some y)
  inv : ∀ (σ : Subst) (r : Option GroundTerm), σ.lookup 0 = some x → EvalTerm d σ t r → r = some y

section Shape

variable {s : Srt} {t : Term} {x y : GroundTerm} {f : Sym}

/-- The truth value of `post` where B has the value w1 and Z the value w2. -/
def postVal (x y w1 w2 : GroundTerm) : Bool :=
  sameResult (some w2) (some x) || (sameResult (some w2) (some w1) && sameResult (some w1) (some y))

theorem post_holds (ht : TermIs d t x y) {w1 w2 : GroundTerm} (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some w1) (h2 : σ.lookup 2 = some w2) : Holds d 3 σ (clB s t).post (postVal x y w1 w2) :=
  holds_cast (Holds.or (Holds.mem .var .var) (Holds.and (Holds.mem .var .var) (Holds.equals .var (ht.ev σ h0))))
    (by rw [h0, h1, h2]; rfl)

theorem post_inv (ht : TermIs d t x y) {w1 w2 : GroundTerm} (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some w1) (h2 : σ.lookup 2 = some w2) {b : Bool} (h : Holds d 3 σ (clB s t).post b) :
    b = postVal x y w1 w2 := by
  cases h with
  | or h h' =>
    cases h with
    | mem a2 a0 =>
      cases h' with
      | and hm he =>
        cases hm with
        | mem c2 c1 =>
          cases he with
          | equals e1 e2 =>
            obtain rfl := EvalTerm.var_inv a2
            obtain rfl := EvalTerm.var_inv a0
            obtain rfl := EvalTerm.var_inv c2
            obtain rfl := EvalTerm.var_inv c1
            obtain rfl := EvalTerm.var_inv e1
            obtain rfl := ht.inv σ _ h0 e2
            rw [h0, h1, h2]; rfl

theorem postVal_x (x y w1 : GroundTerm) : postVal x y w1 x = true := by
  simp [postVal, sameResult_self]
theorem postVal_y (x y : GroundTerm) : postVal x y y y = true := by
  simp [postVal, sameResult_self]
/-- Where t's value at x is x, `post` is true exactly where Z is x. -/
theorem postVal_same {x w1 w2 : GroundTerm} (h : postVal x x w1 w2 = true) : w2 = x := by
  simp only [postVal, Bool.or_eq_true, Bool.and_eq_true, sameResult_some] at h
  rcases h with h | ⟨h, h'⟩
  · exact h
  · exact h.trans h'

theorem exsFree_clB : (clB s t).exsFree = [1, 2] := rfl
theorem exs_clB : (clB s t).exs ≠ [] := List.cons_ne_nil 1 [2]

theorem agree_x {σ' : Subst} (h : AgreeOff (clB s t).exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by rw [exsFree_clB]; decide)

theorem pat_x {σ : Subst} (hm : PatVals d σ (clB s t).pats [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

/-- An instance at which Z has the value w2 and `post` is true gives w2. -/
theorem inst_eq (ht : TermIs d t x y) {σ' : Subst} {w1 w2 : GroundTerm} {r : Option GroundTerm}
    (h0 : σ'.lookup 0 = some x) (h1 : σ'.lookup 1 = some w1) (h2 : σ'.lookup 2 = some w2)
    (hv : postVal x y w1 w2 = true) (h : InstIs d σ' (clB s t) r) : r = some w2 := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht' _ _ => cases ht'
    | post hp =>
      have e := post_inv ht h0 h1 h2 hp
      rw [hv] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h2] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h2] at e; exact e

/-- σ with B and Z given the value w. -/
def set12 (σ : Subst) (w : GroundTerm) : Subst := (2, w) :: (1, w) :: σ

theorem set12_0 (h0 : σ.lookup 0 = some x) (w : GroundTerm) : (set12 σ w).lookup 0 = some x :=
  (lkNe _ _ (by decide)).trans ((lkNe _ _ (by decide)).trans h0)
theorem set12_1 (σ : Subst) (w : GroundTerm) : (set12 σ w).lookup 1 = some w :=
  (lkNe _ _ (by decide)).trans (lkSelf _ _ _)
theorem set12_2 (σ : Subst) (w : GroundTerm) : (set12 σ w).lookup 2 = some w := lkSelf _ _ _
theorem set12_sorted (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some s) {w : GroundTerm}
    (hw : d.sortOf w = some s) : d.WellSorted (clB s t).vars (set12 σ w) :=
  sorted3 (set12_0 h0 w) hx (set12_1 σ w) hw (set12_2 σ w) hw

/-- **The instances at B, Z := x and at B, Z := y do not agree on one result**, where y is not x:
no r is the result of every instance of the clause at a match giving X the value x. -/
theorem two_insts (ht : TermIs d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (h0 : σ.lookup 0 = some x) {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff (clB s t).exsFree σ σ' → d.WellSorted (clB s t).vars σ' → InstIs d σ' (clB s t) r) :
    False := by
  have e1 := inst_eq ht (set12_0 h0 x) (set12_1 σ x) (set12_2 σ x) (postVal_x x y x)
    (hall _ (agree_set12 σ _ _) (set12_sorted h0 hx hx))
  have e2 := inst_eq ht (set12_0 h0 y) (set12_1 σ y) (set12_2 σ y) (postVal_y x y)
    (hall _ (agree_set12 σ _ _) (set12_sorted h0 hx hy))
  rw [e1] at e2
  exact hne (Option.some.inj e2).symm

theorem sorted_x (hx : d.sortOf x = some s) : d.WellSorted (clB s t).vars [(2, x), (1, x), (0, x)] :=
  sorted3 rfl hx rfl hx rfl hx

/-- The clause does not fail at `[x]`: it has no `requires` and its `pre` is `⊤`. -/
theorem not_fails (hx : d.sortOf x = some s) : ¬ Fails d [x] (clB s t) := fun h => by
  cases h with
  | intro hF =>
    cases hF _ ((sorted_x hx).at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **`f(x)` has no result**, where t's value y at x is not x. -/
theorem no_res (ht : TermIs d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnB f s t)) {r : Option GroundTerm} (h : Eval d f [x] r) : False := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clB s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnB] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact not_fails hx (hnone (clB s t) (List.mem_singleton_self _))
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall
  | exNone hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall

/-- **The clause is not match independent**, where t's value y at x is not x: it decides at `[x]`
and has no result there. -/
theorem not_mi (ht : TermIs d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnB f s t)) : MatchIndependent d (clB s t) → False := by
  intro hm
  have hdec : (clB s t).Decides d (fnB f s t) [(2, x), (1, x), (0, x)] [x] :=
    ⟨⟨(sorted_x hx).at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnB, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 exs_clB f (fnB f s t) [x] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex exs_clB
  · exact two_insts (σ := [(2, x), (1, x), (0, x)]) ht hne hx hy rfl hall
  · exact two_insts (σ := [(2, x), (1, x), (0, x)]) ht hne hx hy rfl hall

/-- **Every instance is decided and gives x or nothing**, where t's value at x is x. -/
theorem inst_all (ht : TermIs d t x x) (h0 : σ.lookup 0 = some x) (hw : d.WellSorted (clB s t).vars σ) :
    InstIs d σ (clB s t) (some x) := by
  obtain ⟨w1, h1, -⟩ := hw 1 s rfl
  obtain ⟨w2, h2, -⟩ := hw 2 s rfl
  cases hb : postVal x x w1 w2 with
  | true =>
    obtain rfl := postVal_same hb
    exact .gives (h2 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds ht h0 h1 h2) hb)
  | false => exact .fails (post_holds ht h0 h1 h2) (.post (holds_cast (post_holds ht h0 h1 h2) hb))

/-- **`f(x)` is x**, where t's value at x is x, by `Eval.clauseEx` at B := x and Z := x. -/
theorem value (ht : TermIs d t x x) (hfn : d.lookupFn f = some (fnB f s t)) (hx : d.sortOf x = some s) :
    Eval d f [x] (some x) :=
  have h0 : ([(2, x), (1, x), (0, x)] : Subst).lookup 0 = some x := rfl
  .clauseEx (fn := fnB f s t) (cl := clB s t) (σ := [(2, x), (1, x), (0, x)]) hfn (List.mem_singleton_self _)
    (sorted_x hx) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnB, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    exs_clB .var (fun t ht => nomatch ht)
    (holds_cast (post_holds ht h0 rfl rfl) (postVal_x x x x))
    (fun σ' ha hw => inst_all ht ((agree_x ha).trans h0) hw)

/-- **`f(x)` has no other result**, where t's value at x is x. -/
theorem alone (ht : TermIs d t x x) (hfn : d.lookupFn f = some (fnB f s t)) (hx : d.sortOf x = some s)
    {r : Option GroundTerm} (h : Eval d f [x] r) : r = some x := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clB s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnB] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hnone (clB s t) (List.mem_singleton_self _)) (not_fails hx)
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clB
  | clauseEx hfn' hmem hσ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨w1, h1, -⟩ := hσ 1 s rfl
    have h2 := (EvalTerm.var_inv hrhs).symm
    have e := post_inv ht (pat_x hmatch) h1 h2 hpost
    rw [postVal_same e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := pat_x hmatch
    have hi := hall _ (agree_set12 σ x x) (set12_sorted h0 hx hx)
    have e := inst_eq ht (set12_0 h0 x) (set12_1 σ x) (set12_2 σ x) (postVal_x x x x) hi
    cases e

end Shape

end InOrFx

namespace FnMany

open GroundTerm InOrFx KCore.Parse

def fF : Sym := 384
def fX : Sym := 385

/-- The term f's binder is equated with, `notBool X`. -/
def tNot : Term := .app boolNot [.var 0]
/-- The term fx's binder is equated with, X. -/
def tX : Term := .var 0

/-- **The reading**: the text's functions are f and fx, neither `total`, each with the one clause
`[X:Bool, B:Bool, #Or0:Bool]`, `exs [1, 2]`, `rhs #Or0`, `post (#Or0 ∈ X) ∨ ((#Or0 ∈ B) ∧ (B = t))`,
t being `notBool X` for f and X for fx: the binder moved over the `\or`. -/
theorem read : c.fns = [fnB fF Srt.bool tNot, fnB fX Srt.bool tX] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName fX = "Lblfx" ∧ c.symName boolNot = "LblnotBool'Unds'" ∧
    c.sortName Srt.bool = "Bool" := by decide +kernel

/-- Bool is confined: `clausePlainEx` admits both clauses. -/
theorem plainEx : c.confined Srt.bool = true ∧ c.clausePlainEx (clB Srt.bool tNot) = true ∧
    c.clausePlainEx (clB Srt.bool tX) = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some (fnB fF Srt.bool tNot) := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupX : c.lookupFn fX = some (fnB fX Srt.bool tX) := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel

section Terms

variable {d : Semantics}

theorem notHook : isHook boolNot = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation. -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

/-- `notBool X` where X is b: `!b`, and no other result. -/
theorem tNot_is (hc : d.isCtor boolNot = false) (b : Bool) : TermIs d tNot (bool b) (bool (!b)) where
  ev σ h0 := .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)
  inv σ r h0 h := by
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    have := hh [bool b] (by rw [h0]; rfl)
    rw [hookNot] at this
    exact (Option.some.inj this).symm

/-- X where X is x: x, and no other result. -/
theorem tX_is (x : GroundTerm) : TermIs d tX x x where
  ev _ h0 := h0 ▸ .var
  inv _ _ h0 h := (EvalTerm.var_inv h).trans h0

theorem not_ne (b : Bool) : bool (!b) ≠ bool b := by cases b <;> decide

end Terms

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some (fnB fF Srt.bool tNot) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupXH (H : HookParams) : (cH H).lookupFn fX = some (fnB fX Srt.bool tX) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupX
theorem tNot_isH (H : HookParams) (b : Bool) : TermIs (cH H) tNot (bool b) (bool (!b)) :=
  tNot_is (d := cH H) notCtor b

/-- **`fx(b) = b`, for every H.** -/
theorem fx_value (H : HookParams) (b : Bool) : Eval (cH H) fX [bool b] (some (bool b)) :=
  value (tX_is _) (lookupXH H) (rmS_sortOf_bool _ b)

/-- **`fx(b)` has no other result, for every H**: not the other value of Bool, and not none. -/
theorem fx_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fX [bool b] r) :
    r = some (bool b) :=
  alone (tX_is _) (lookupXH H) (rmS_sortOf_bool _ b) h

/-- **`fx(true) = true`, for every H.** -/
theorem fx_true (H : HookParams) : Eval (cH H) fX [bool true] (some (bool true)) := fx_value H true

/-- **`fx(true)` has no result but `true`, for every H.** -/
theorem fx_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fX [bool true] r) :
    r = some (bool true) := fx_alone H h

/-- **`f(b)` has no result, for every H and both values of Bool**: neither a value nor none. Its
instances at B, #Or0 := b and at B, #Or0 := notBool b give b and notBool b. -/
theorem f_no_result (H : HookParams) (b : Bool) (r : Option GroundTerm) : ¬ Eval (cH H) fF [bool b] r :=
  fun h => no_res (tNot_isH H b) (not_ne b) (rmS_sortOf_bool _ b) (rmS_sortOf_bool _ (!b)) (lookupFH H) h

/-! ### The model with f read as its instances' values, for every H -/

section Model

open KCore.Faithful KCore.Faithful.Model

def nF : String := "Lblf"
def fnF : Fn := fnB fF Srt.bool tNot
def clF : Clause := clB Srt.bool tNot

theorem name_f : c.symName fF = nF := by decide +kernel
theorem plain_f : instDecode? nF = none := by decide +kernel
theorem spare_f : GenEqs.spareSymB c nF = true := by decide +kernel
theorem values_f : GenEqs.NameFree.valuesN c [nF] = true := by rw [GenEqs.NameFree.valuesN]; decide_cheap 40
theorem hooks_f : hookSigs.all (fun k => GenEqs.NameFree.appOKN c [nF] k.name) = true := by decide_cheap 40
theorem params_f : c.params.all (fun k => GenEqs.NameFree.appOKN c [nF] k.sig.name) = true := by decide_cheap 40
theorem fns_f : c.allFns.all (fun g => decide (g.label = fF) || GenEqs.NameFree.appOKN c [nF] g.label) = true := by
  decide_cheap 40
theorem lists_f : Faithful.Model.listsOffB c fF nF = true := by rw [Faithful.Model.listsOffB]; decide_cheap 40
theorem kok_f : Faithful.Model.ownKokB c fnF clF = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem shapes : c.shapesOK = true := by decide_cheap
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem f_one : (c.allFns.filter (fun g => decide (g.label = fF))).length = 1 := by decide +kernel

theorem shapesH (H : HookParams) : (cH H).shapesOK = true := shapes

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) ((Faithful.Model.coreOKEx_withHooks_fm c H).trans coreEx)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- **Every premise but f's own items avoids `Lblf`, for every H.** -/
theorem avoidsOffH (H : HookParams) : Faithful.Model.AvoidsOff (cH H) fF ((cH H).symName fF) := by
  have hn : (cH H).symName fF = nF := name_f
  rw [hn]
  refine Faithful.Model.avoidsOff_of_lists (rangeBelowH H) (Faithful.Model.listsOff_withHooks H lists_f) values_f
    (List.all_eq_true.mp hooks_f) (List.all_eq_true.mp params_f)
    (fun g hg hl => by
      have h1 : GenEqs.NameFree.appOKN c [nF] g.label = true := by
        have := List.all_eq_true.mp fns_f g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fF)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hH : fnF ∈ c.allFns.filter (fun g => decide (g.label = fF)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp [fnF]), by simp [fnF, fnB]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp f_one
  rw [hx, List.mem_singleton] at hfn' hH
  obtain rfl : fn = fnF := hfn'.trans hH.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.bool := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails hx (hall clF (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnF, fnB])

theorem univ_clB {s : Srt} {t : Term} : (clB s t).univ = [0] := rfl

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
  rw [show clF.exsFree = [1, 2] from rfl] at hx
  have hi0 : i = 0 := by
    have hl : clF.vars.length = 3 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  subst hi0
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl h1
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl h2
  cases hx'
  rw [h0, h0']

/-- **A result of a clause `clB s t` at a match giving X the value x is x**: the instance at
B, #Or0 := x has `post` true and gives x alone, and a result agrees with every instance. -/
theorem resEx_x {d : Semantics} {s : Srt} {t : Term} {σ : Subst} {x y : GroundTerm} {r : Option GroundTerm}
    (ht : TermIs d t x y) (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some s)
    (h : (clB s t).ResEx d σ r) : r = some x := by
  have hag : AgreeOff (clB s t).exsFree σ (set12 σ x) := agree_set12 σ x x
  have hws := set12_sorted (t := t) h0 hx hx
  have key : ∀ r, InstIs d (set12 σ x) (clB s t) r → r = some x := fun r hi =>
    inst_eq ht (set12_0 h0 x) (set12_1 σ x) (set12_2 σ x) (postVal_x x y x) hi
  rcases h with ⟨σ₁, v, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩
  · exact key _ (hall _ hag hws)
  · exact absurd (key _ (hall _ hag hws)) (by simp)

/-- A term `t` over X with one value at each value of Bool, for every H: `notBool X` and X. -/
theorem termIs_bool (H : HookParams) {t : Term} (htt : t = tNot ∨ t = tX) (b : Bool) :
    ∃ y, TermIs (cH H) t (bool b) y := by
  rcases htt with rfl | rfl
  · exact ⟨_, tNot_isH H b⟩
  · exact ⟨_, tX_is _⟩

theorem coh_clB (H : HookParams) {t : Term} (htt : t = tNot ∨ t = tX) :
    Coherent (cH H) (clB Srt.bool t) (clB Srt.bool t) := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) (cl := clB Srt.bool t) rfl (by rw [univ_clB]; exact List.mem_singleton_self _) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) (cl := clB Srt.bool t) rfl (by rw [univ_clB]; exact List.mem_singleton_self _) rfl ha'
  cases hx'
  obtain ⟨b, rfl⟩ := shape_bool (shapesH H) hx
  obtain ⟨y, ht⟩ := termIs_bool H htt b
  refine .inr fun r r' hr hr' => ?_
  rcases hr with ⟨he, -⟩ | ⟨-, hr⟩
  · exact absurd he exs_clB
  rcases hr' with ⟨he, -⟩ | ⟨-, hr'⟩
  · exact absurd he exs_clB
  rw [resEx_x ht h0 hx hr, resEx_x ht h0' hx hr']

/-- **The right-side predicates have truth values, for every H.** -/
theorem postDecH (H : HookParams) : ClausePostDecided (cH H) := by
  intro fn hfn cl hcl σ hσ
  have hfns : (cH H).fns = [fnB fF Srt.bool tNot, fnB fX Srt.bool tX] := read
  rw [hfns] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  have hpost : ∀ {t : Term}, (t = tNot ∨ t = tX) → (cH H).WellSorted (clB Srt.bool t).vars σ →
      ∃ b, Holds (cH H) (clB Srt.bool t).vars.length σ (clB Srt.bool t).post b := fun htt hσ => by
    obtain ⟨x, h0, hx⟩ := hσ 0 Srt.bool rfl
    obtain ⟨w1, h1, -⟩ := hσ 1 Srt.bool rfl
    obtain ⟨w2, h2, -⟩ := hσ 2 Srt.bool rfl
    obtain ⟨b, rfl⟩ := shape_bool (shapesH H) hx
    obtain ⟨y, ht⟩ := termIs_bool H htt b
    exact ⟨_, post_holds ht h0 h1 h2⟩
  rcases hfn with rfl | rfl
  · simp only [fnB, List.mem_singleton] at hcl; subst hcl; exact hpost (.inl rfl) hσ
  · simp only [fnB, List.mem_singleton] at hcl; subst hcl; exact hpost (.inr rfl) hσ

end Model

end FnMany

/-! ### The facts the deciders name -/

def callOrder : List Nat := [FnMany.fF, FnMany.fX]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clauses whose match independence no decider confirms: `f`'s and `fx`'s. -/
theorem match_named : c.matchObligationsL = [(FnMany.fF, 0), (FnMany.fX, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### The owed fact refuted, `FnHyp` false, and consistency, for every H -/

section Stated

open GroundTerm InOrFx FnMany KCore.Parse KCore.Faithful KCore.Faithful.Model

/-- **The owed fact the package names for f's clause, `MatchIndependent`, is false, for every H.** -/
theorem f_not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) (clB Srt.bool tNot) :=
  not_mi (tNot_isH H true) (not_ne true) (rmS_sortOf_bool _ true) (rmS_sortOf_bool _ (!true)) (lookupFH H)

/-- **`FnHyp` is false, for every H**: f has no result at `true`. -/
theorem not_fnHypH (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [bool true] = some (fnB fF Srt.bool tNot).args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl
  obtain ⟨r, hr⟩ := hf.1 (fnB fF Srt.bool tNot)
    (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_cons_self ..) [bool true] hso
  exact f_no_result H true r hr

/-- **Every function has at most one result, for every H.** f's clause has no result at all and
fx's has X's value; a result of either at a match is X's value (`resEx_x`). -/
theorem fnDetH (H : HookParams) : FnDet (cH H) := by
  refine fnDet_of_coherent fun f fn hfn cl hcl cl' hcl' hprio => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · have hfns : (cH H).fns = [fnB fF Srt.bool tNot, fnB fX Srt.bool tX] := read
    rw [hfns] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · simp only [fnB, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clB H (.inl rfl)
    · simp only [fnB, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clB H (.inr rfl)
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

/-- **Evaluation solves fx's equation, for every H**: fx(x) is x, the one value its instances
give. -/
theorem fx_solves (H : HookParams) : FnSolvesAt (cH H) (fnB fX Srt.bool tX) := by
  intro vs _ cl hcl σ hdec v
  simp only [fnB, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) (cl := clB Srt.bool tX) rfl (by decide) rfl hdec.1
  constructor
  · intro he
    obtain rfl : v = x := Option.some.inj (alone (tX_is _) (lookupXH H) hx he)
    exact ⟨set12 σ v, agree_set12 σ v v, set12_sorted h0 hx hx, set12_2 σ v ▸ .var,
      (fun t ht => nomatch ht), holds_cast (post_holds (tX_is v) (set12_0 h0 v) (set12_1 σ v) (set12_2 σ v))
        (postVal_x v v v)⟩
  · rintro ⟨σ', hag, hw, hy, -, hpo⟩
    have h0' : σ'.lookup 0 = some x := (agree_x hag).trans h0
    obtain ⟨w1, h1, -⟩ := hw 1 Srt.bool rfl
    have h2 : σ'.lookup 2 = some v := (EvalTerm.var_inv hy).symm
    have e := post_inv (tX_is x) h0' h1 h2 hpo
    obtain rfl := postVal_same e.symm
    exact value (tX_is _) (lookupXH H) hx

/-- **Γc with the step's closure has a model, for every H** (`consistent_of_fnMany_agree` at f). -/
theorem consistent (H : HookParams) : Consistent (cH H) := by
  have hfns : (cH H).fns = [fnB fF Srt.bool tNot, fnB fX Srt.bool tX] := read
  refine Faithful.Model.consistent_of_fnMany_agree (f := fF) (fn := fnF) (cl := clF) (a := Srt.bool)
    ((Faithful.Model.coreOKEx_withHooks_fm c H).trans coreEx) (by rw [hfns]; simp [fnF]) rfl rfl rfl exs_clB
    (by rw [show (cH H).symName fF = nF from name_f]; exact plain_f)
    (by rw [show (cH H).symName fF = nF from name_f, Faithful.Model.spareSymB_withHooks_fm]; exact spare_f)
    (avoidsOffH H) (by rw [Faithful.Model.ownKokB_withHooks]; exact kok_f) (fnDetH H) (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) (postDecH H) (openLaws_of_plain noRaw)
  rw [hfns] at hg'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl
  · exact absurd rfl hl
  · exact fx_solves H

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

theorem nj88 : (trS U.ax88).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj93 : (trS U.ax93).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj96 : (trS U.ax96).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax88, U.ax93, U.ax96], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj88]; exact orTopBot_valid hD rfl
  · rw [nj93]; exact orTopBot_valid hD rfl
  · rw [nj96]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax89, U.ax90, U.ax91, U.ax92, U.ax94, U.ax95],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax89, U.ax90, U.ax91, U.ax92, U.ax94, U.ax95],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax97).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (97)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax97).pat := by
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax79, U.ax80]

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

Γ's items 0 (sentence 131), 1 (sentence 132) are not their sentences (`un<j>_differs`), and no
reading here gives them from the sentence or the sentence from them: the sentences are uncovered,
`fns_entailed` and `fns_from_text` leave them out, and the premise set of `gamma_from` holds Γ's
item there.

Every other item is the translation of its function sentence (`shape`). -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

/-- Γ's item 0 (sentence 131): no reading here ties it. -/
noncomputable def unItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem unItem0_at : (TiePair.gammaPats c)[0]? = some unItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax131
/-- **Γ's item 0 is not the text's sentence 131** (kernel): the sentence is uncovered. -/
theorem un0_differs : unItem0 ≠ (trS U.ax131).pat := by decide +kernel

/-- Γ's item 1 (sentence 132): no reading here ties it. -/
noncomputable def unItem1 : P := (TiePair.gammaPats c).getD 1 ⊥
theorem unItem1_at : (TiePair.gammaPats c)[1]? = some unItem1 := by decide +kernel
kernel_rfl fnText_at1 : fnText[1]? = some U.ax132
/-- **Γ's item 1 is not the text's sentence 132** (kernel): the sentence is uncovered. -/
theorem un1_differs : unItem1 ≠ (trS U.ax132).pat := by decide +kernel

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at positions 0, 1. -/
noncomputable def textPats : List P := ((fnText.map (trS · |>.pat)).set 0 unItem0).set 1 unItem1

/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def pairSetAt : List Nat := [0, 1]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h0, h1⟩ := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h0), List.getElem?_map, hj]
  rfl

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the untied ones (items 0, 1), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([0, 1] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item but the untied ones (items 0, 1) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([0, 1] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h0 : j = 0
  · subst h0; simp at hu
  by_cases h1 : j = 1
  · subst h1; simp at hu
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h0), List.getElem?_map] at ht
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
    ∀ ad ∈ [U.ax88, U.ax93, U.ax96], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax89, U.ax90, U.ax91, U.ax92, U.ax94, U.ax95],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax97).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 48 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax48).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE3EqExistsMlInOr

#check @KCore.TieE3EqExistsMlInOr.noRaw
#check @KCore.TieE3EqExistsMlInOr.readsConfined_c
#check @KCore.TieE3EqExistsMlInOr.userAxioms_eq
#check @KCore.TieE3EqExistsMlInOr.coreOK
#check @KCore.TieE3EqExistsMlInOr.account
#check @KCore.TieE3EqExistsMlInOr.account_sizes
#check @KCore.TieE3EqExistsMlInOr.account_classes
#check @KCore.TieE3EqExistsMlInOr.account_absent
#check @KCore.TieE3EqExistsMlInOr.absent_closed
#check @KCore.TieE3EqExistsMlInOr.absent_proj_below_c
#check @KCore.TieE3EqExistsMlInOr.absent_proj_below
#check @KCore.TieE3EqExistsMlInOr.lists_in_account
#check @KCore.TieE3EqExistsMlInOr.attrs_agree
#check @KCore.TieE3EqExistsMlInOr.sig_origin_but_next
#check @KCore.TieE3EqExistsMlInOr.decls_entailed
#check @KCore.TieE3EqExistsMlInOr.consistent
#check @KCore.TieE3EqExistsMlInOr.f_not_matchIndependent
#check @KCore.TieE3EqExistsMlInOr.not_fnHypH
#check @KCore.TieE3EqExistsMlInOr.text_nextless
#check @KCore.TieE3EqExistsMlInOr.nojunk_trivial_entailed
#check @KCore.TieE3EqExistsMlInOr.nojunk_items_entailed
#check @KCore.TieE3EqExistsMlInOr.nojunk_kitem_entailed
#check @KCore.TieE3EqExistsMlInOr.cons_entailed
#check @KCore.TieE3EqExistsMlInOr.idem_refuted
#check @KCore.TieE3EqExistsMlInOr.owed_rules
#check @KCore.TieE3EqExistsMlInOr.owed_clauses
#check @KCore.TieE3EqExistsMlInOr.openDecidedH
#check @KCore.TieE3EqExistsMlInOr.gammaCl_eq
#check @KCore.TieE3EqExistsMlInOr.decls_entailed_c
#check @KCore.TieE3EqExistsMlInOr.nojunk_trivial_entailed_c
#check @KCore.TieE3EqExistsMlInOr.nojunk_items_entailed_c
#check @KCore.TieE3EqExistsMlInOr.nojunk_kitem_entailed_c
#check @KCore.TieE3EqExistsMlInOr.cons_entailed_c
#check @KCore.TieE3EqExistsMlInOr.idem_refuted_c
#print axioms KCore.TieE3EqExistsMlInOr.noRaw
#print axioms KCore.TieE3EqExistsMlInOr.readsConfined_c
#print axioms KCore.TieE3EqExistsMlInOr.userAxioms_eq
#print axioms KCore.TieE3EqExistsMlInOr.coreOK
#print axioms KCore.TieE3EqExistsMlInOr.account
#print axioms KCore.TieE3EqExistsMlInOr.account_sizes
#print axioms KCore.TieE3EqExistsMlInOr.account_classes
#print axioms KCore.TieE3EqExistsMlInOr.account_absent
#print axioms KCore.TieE3EqExistsMlInOr.absent_closed
#print axioms KCore.TieE3EqExistsMlInOr.absent_proj_below_c
#print axioms KCore.TieE3EqExistsMlInOr.absent_proj_below
#print axioms KCore.TieE3EqExistsMlInOr.lists_in_account
#print axioms KCore.TieE3EqExistsMlInOr.attrs_agree
#print axioms KCore.TieE3EqExistsMlInOr.sig_origin_but_next
#print axioms KCore.TieE3EqExistsMlInOr.decls_entailed
#print axioms KCore.TieE3EqExistsMlInOr.consistent
#print axioms KCore.TieE3EqExistsMlInOr.f_not_matchIndependent
#print axioms KCore.TieE3EqExistsMlInOr.not_fnHypH
#print axioms KCore.TieE3EqExistsMlInOr.text_nextless
#print axioms KCore.TieE3EqExistsMlInOr.nojunk_trivial_entailed
#print axioms KCore.TieE3EqExistsMlInOr.nojunk_items_entailed
#print axioms KCore.TieE3EqExistsMlInOr.nojunk_kitem_entailed
#print axioms KCore.TieE3EqExistsMlInOr.cons_entailed
#print axioms KCore.TieE3EqExistsMlInOr.idem_refuted
#print axioms KCore.TieE3EqExistsMlInOr.owed_rules
#print axioms KCore.TieE3EqExistsMlInOr.owed_clauses
#print axioms KCore.TieE3EqExistsMlInOr.openDecidedH
#print axioms KCore.TieE3EqExistsMlInOr.gammaCl_eq
#print axioms KCore.TieE3EqExistsMlInOr.decls_entailed_c
#print axioms KCore.TieE3EqExistsMlInOr.nojunk_trivial_entailed_c
#print axioms KCore.TieE3EqExistsMlInOr.nojunk_items_entailed_c
#print axioms KCore.TieE3EqExistsMlInOr.nojunk_kitem_entailed_c
#print axioms KCore.TieE3EqExistsMlInOr.cons_entailed_c
#print axioms KCore.TieE3EqExistsMlInOr.idem_refuted_c
#check @KCore.TieE3EqExistsMlInOr.fns_account
#check @KCore.TieE3EqExistsMlInOr.un0_differs
#check @KCore.TieE3EqExistsMlInOr.un1_differs
#check @KCore.TieE3EqExistsMlInOr.shape
#check @KCore.TieE3EqExistsMlInOr.fns_entailed
#check @KCore.TieE3EqExistsMlInOr.fns_from_text
#check @KCore.TieE3EqExistsMlInOr.fn_prios
#check @KCore.TieE3EqExistsMlInOr.gamma_from
#print axioms KCore.TieE3EqExistsMlInOr.fns_account
#print axioms KCore.TieE3EqExistsMlInOr.un0_differs
#print axioms KCore.TieE3EqExistsMlInOr.un1_differs
#print axioms KCore.TieE3EqExistsMlInOr.shape
#print axioms KCore.TieE3EqExistsMlInOr.fns_entailed
#print axioms KCore.TieE3EqExistsMlInOr.fns_from_text
#print axioms KCore.TieE3EqExistsMlInOr.fn_prios
#print axioms KCore.TieE3EqExistsMlInOr.gamma_from
