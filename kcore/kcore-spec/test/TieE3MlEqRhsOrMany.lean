/-
  The tie (C14) on `f2-examples/e3-ml-eq-rhs-or-many.kompile.kore`, the kompiled text of construct fixture e3-ml-eq-rhs-or-many
  (`test/constructs/fixtures/e3-ml-eq-rhs-or-many`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-eq-rhs-or-many`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlEqRhsOrMany.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 252 sentences of the user module E3-ML-EQ-RHS-OR-MANY, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 204 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator
    (`noRaw`). It owes the match independence of a clause (`match_named`).
    The consistency section, written by hand, refutes the match independence it owes: for the clause
    `clK` it is false for every H (`not_matchIndependent`), and so is `FnHyp` (`not_fnHypH`).
    `OpenDecided` holds for every H (`openDecidedH`). `Γc` with the step's closure has a model for every
    H all the same (`consistent`), outside the value model, whose construction reads `FnHyp`
    (`consistent_of_fnHyp`) or the named facts (`consistent_of_fnFacts`), the refuted one among them.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (28) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (235) is not its sentence (`un<j>_differs`) and no reading
    here ties it: the sentence is `uncovered`, and `fns_entailed` and `fns_from_text` leave it out.
    `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 158 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence is uncovered), Γ's rule items, the five parts Γ defines by predicates, or
    definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp`, which is false for every H (`not_fnHypH`): not shown by this tie; no
    direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (4);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlEqRhsOrMany

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-eq-rhs-or-many.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or-many.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-many.kompile.kore" module "E3-ML-EQ-RHS-OR-MANY"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-OR-MANY")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 252 := by decide +kernel

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
  [("function equation", [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
      224, 225, 226, 227, 228, 229, 230, 231, 232, 235]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 99, 100]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [109, 110, 111, 112, 113, 114, 115, 116, 117, 118]),
   ("function functional", [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      55, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 96, 97, 98, 101, 102, 103, 104,
      105, 106]),
   ("collection law", [52, 53, 54, 56, 57, 58, 59, 61, 62]),
   ("library", [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141,
      142, 143, 144, 145, 146, 147, 148, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
      161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
      179, 180, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197,
      198, 199, 200, 201, 236, 237, 238, 239, 253, 254]),
   ("set idempotence", [60]),
   ("set-variable lemma", [119, 120, 121, 122, 123, 255]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 39, 41, 72, 74, 78, 94, 107, 108, 149, 181, 202, 203, 204, 205, 233, 234, 240, 241, 242,
      243, 244, 245, 246, 247, 248, 249, 250, 251, 252])]

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
    [("function equation", 28), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 15), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 30)] := by
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
  [(240, "Bool"), (241, "GeneratedCounterCell"), (242, "GeneratedCounterCellOpt"),
   (243, "GeneratedTopCell"), (244, "GeneratedTopCellFragment"), (245, "Int"), (246, "K"),
   (247, "KCell"), (248, "KCellOpt"), (249, "KItem"), (250, "List"), (251, "Map"), (252, "Set")]

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
  [(95, "function functional"), (118, "no junk"), (205, "no direction"),
   (235, "function equation")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(235, "function equation")]

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 127, 90, 5, 32) := by
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

/-! ## Consistency for every H: `k(_) => 1 #Or 2 #Or … #Or 9`, its match independence refuted -/

/- The one function `k`, declared `total`, has the one clause `CeOrM.clK`, read with the
existential variable #Or0 of Int (`exs [1]`, `rhs := #Or0`, `post` the nine memberships `#Or0 ∈ 1`,
…, `#Or0 ∈ 9`, nested as the text nests the disjunctions). Γ holds no functional axiom of a function: k's `total`
puts no item in Γ, and its functional sentence (95) is in no part of Γ.
- The match independence `match_named` names, of k's clause, is false for every H
  (`not_matchIndependent`): at `[0]` the clause decides, its instances at #Or0 := 1 and #Or0 := 2 give
  1 and 2 (`CeOrM.inst_eq`), so it has no result there (`CeOrM.two_insts`). So `FnHyp`, whose fourth
  conjunct is that fact, is false for every H (`not_fnHypH`).
- Every function has at most one result, for every H (`fnDetH`, by `fnDet_of_coherent`): k's clause
  has no result at any match (`CeOrM.coh_clK`), so it is coherent with itself.
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `Γc` with the step's closure has a model for every H (`consistent`), by
  `Faithful.Model.consistent_of_fnMany_agree` at k: the value model with k read as the set of its
  instances' values (at every argument, the nine literals). Its hypotheses, each for every H: every
  premise of the theory but k's own items avoids k's name (`CeOrM.avoidsOffH`; k's clause applies at
  every argument of Int, so the theory states no rest of k), two matches of k's clause at one argument
  agree on its pattern variable (`CeOrM.agreeH`), `fnDetH`, no function other than k (`CeOrM.read`), and
  the right-side predicate has a truth value (`CeOrM.postDecH`). The hypotheses read nothing of k's
  `total`.
- Sentence 95 (k's functional sentence, `∃Val. Val = k(K0)`) holds in no model of Γ, for every H
  (`s95_refuted`): Γ's item of k's clause puts the elements of 1 and 2 in k(1) (the instances at
  #Or0 := 1 and #Or0 := 2, `OrMS95.inK`), sentence 95 makes k(1) one element of Int (`OrMS95.fnl_read`),
  and 1 and 2 are distinct elements of Int (`ΓDomains`, through `values_apart`). The refutation reads
  two items of Γ that no sentence of the text states: that 1 and 2 are each one element of Int, and
  that they are distinct elements. So the sentence is against the reading, which has a model
  (`consistent`).

`OrMFx`, `CeOrM` and `OrMS95` hold the proofs; the statements after them are on `cH H`. -/

/-! ### Facts the proofs share -/

namespace OrMFx

open GroundTerm KCore.Parse

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem holds_cast {d : Semantics} {σ : Subst} {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b)
    (e : b = b') : Holds d n σ p b' :=
  e ▸ h

/-- The instances of a clause whose one existential variable is the variable 1: σ with it set. -/
theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

/-- A substitution giving the variables 0 and 1 values of the two sorts is well sorted. -/
theorem sorted2 {d : Semantics} {σ : Subst} {a b : Srt} {x w : GroundTerm} (h0 : σ.lookup 0 = some x)
    (hx : d.sortOf x = some a) (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) : d.WellSorted [a, b] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp at hs

/-- The predicate p has the truth value b under σ, and no other. -/
def DecM (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {d : Semantics} {σ : Subst} {n : Nat} {p q : Cond} {b b' : Bool} (hp : DecM d n σ p b)
    (hq : DecM d n σ q b') : DecM d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

end OrMFx

namespace CeOrM

open GroundTerm OrMFx KCore.Parse KCore.GenEqs KCore.Faithful.Model

def fK : Sym := 384
def nK : String := "Lblk"

/-- The membership `#Or0 ∈ k` of the disjunction's variable (the variable 1) in the literal k. -/
def memK (k : Int) : Cond := .mem Srt.int (.var 1) (.dv Srt.int (.int k))

/-- `((#Or0 ∈ 1 ∨ #Or0 ∈ 2) ∨ #Or0 ∈ 3) ∨ … ∨ #Or0 ∈ 9`, nested as the text nests the disjunctions. -/
def postK : Cond := [2, 3, 4, 5, 6, 7, 8, 9].foldl (fun p k => .or p (memK k)) (memK 1)

/-- `k(_Gen0) => #Or0` with `exs = [#Or0]` and `post := postK`, both variables of Int. -/
def clK : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postK }

def fnK : Fn := { label := fK, args := [Srt.int], result := Srt.int, clauses := [clK], total := true }

/-- **The reading**: the text's one function is `k`, `total`, with the one clause `clK`. -/
theorem read : c.fns = [fnK] := by kernel_rfl

theorem name_k : c.symName fK = nK := by decide +kernel
theorem int_name : c.sortName Srt.int = "Int" := by decide +kernel

/-- #Or0 is not of a confined sort; each alternative fixes it by a literal: `clausePlainEx` admits
the clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx clK = true := by decide +kernel

/-! ### The checks on the text -/

theorem plain_k : instDecode? nK = none := by decide +kernel
theorem spare_k : spareSymB c nK = true := by decide +kernel
theorem values_k : NameFree.valuesN c [nK] = true := by rw [NameFree.valuesN]; decide_cheap 40
theorem hooks_k : hookSigs.all (fun k => NameFree.appOKN c [nK] k.name) = true := by decide_cheap 40
theorem params_k : c.params.all (fun k => NameFree.appOKN c [nK] k.sig.name) = true := by decide_cheap 40
theorem fns_k : c.allFns.all (fun g => decide (g.label = fK) || NameFree.appOKN c [nK] g.label) = true := by
  decide_cheap 40
theorem lists_k : listsOffB c fK nK = true := by rw [listsOffB]; decide_cheap 40
theorem kok_k : ownKokB c fnK clK = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem fK_one : (c.allFns.filter (fun g => decide (g.label = fK))).length = 1 := by decide +kernel
theorem exsFree_k : clK.exsFree = [1] := by decide
theorem lower_k : lowerClauses fnK clK = [] := by decide
theorem pats_k : sortsOfTerms c.patCtxAll clK.vars clK.pats = some fnK.args := by decide +kernel
theorem preOK_k : c.condOK clK.vars clK.pre = true := by decide +kernel
theorem postOK_k : c.condOK clK.vars clK.post = true := by decide +kernel
theorem int_numbered : Srt.int < nRegSorts + c.sortNames.length := by decide +kernel
theorem int_apart : apartSort c Srt.int = true := by decide +kernel

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics} {σ : Subst}

/-- The truth value of `#Or0 ∈ k` where #Or0 has the value w. -/
def memVal (w : GroundTerm) (k : Int) : Bool := sameResult (some w) (some (int k))

theorem dec_mem {n : Nat} {w : GroundTerm} (h1 : σ.lookup 1 = some w) (k : Int) :
    DecM d n σ (memK k) (memVal w k) := by
  refine ⟨holds_cast (Holds.mem .var .dv) (by rw [h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := EvalTerm.dv_inv h'
    rw [h1]; rfl

theorem dec_fold {n : Nat} {w : GroundTerm} (h1 : σ.lookup 1 = some w) :
    ∀ (ks : List Int) (p : Cond) (b : Bool), DecM d n σ p b →
      DecM d n σ (ks.foldl (fun p k => .or p (memK k)) p) (ks.foldl (fun b k => b || memVal w k) b)
  | [], _, _, h => h
  | k :: ks, _, _, h => dec_fold h1 ks _ _ (dec_or h (dec_mem h1 k))

/-- The truth value of the clause's `post` where #Or0 has the value w: whether w is one of the nine
literals. -/
def postVal (w : GroundTerm) : Bool := [2, 3, 4, 5, 6, 7, 8, 9].foldl (fun b k => b || memVal w k) (memVal w 1)

theorem dec_post {n : Nat} {w : GroundTerm} (h1 : σ.lookup 1 = some w) : DecM d n σ postK (postVal w) :=
  dec_fold h1 _ _ _ (dec_mem h1 1)

theorem postVal_1 : postVal (int 1) = true := by decide +kernel
theorem postVal_2 : postVal (int 2) = true := by decide +kernel

/-- An instance at which #Or0 is one of the nine literals gives it: its `post` is true. -/
theorem inst_eq {σ' : Subst} {k : Int} {r : Option GroundTerm} (h1 : σ'.lookup 1 = some (int k))
    (hk : postVal (int k) = true) (h : InstIs d σ' clK r) : r = some (int k) := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := (dec_post (d := d) h1).2 _ hp
      rw [hk] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- **The instances at #Or0 := 1 and #Or0 := 2 do not agree on one result**: no r is the result of
every instance of the clause at a match giving `_Gen0` a value of Int. -/
theorem two_insts {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff clK.exsFree σ σ' → d.WellSorted clK.vars σ' → InstIs d σ' clK r) : False := by
  have hw : ∀ k : Int, d.WellSorted clK.vars ((1, int k) :: σ) := fun k =>
    sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) (rmS_sortOf_int d k)
  have e1 := inst_eq (lkSelf 1 (int 1) σ) postVal_1 (hall _ (agree_set1 σ _) (hw 1))
  have e2 := inst_eq (lkSelf 1 (int 2) σ) postVal_2 (hall _ (agree_set1 σ _) (hw 2))
  rw [e1] at e2
  exact absurd e2 (by decide)

/-- **The clause is not match independent**: it decides at `[0]` and has no result there. Stated
with `False` as its conclusion; `not_matchIndependent` is it at `cH H`. -/
theorem not_mi (hfn : d.lookupFn fK = some fnK) : MatchIndependent d clK → False := by
  intro hm
  have hs : d.WellSorted clK.vars [(1, int 0), (0, int 0)] :=
    sorted2 rfl (rmS_sortOf_int d 0) rfl (rmS_sortOf_int d 0)
  have hdec : clK.Decides d fnK [(1, int 0), (0, int 0)] [int 0] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnK, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 (by decide) fK fnK [int 0] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex (by decide)
  · exact two_insts (σ := [(1, int 0), (0, int 0)]) rfl (rmS_sortOf_int d 0) hall
  · exact two_insts (σ := [(1, int 0), (0, int 0)]) rfl (rmS_sortOf_int d 0) hall

end Clause

/-! ### For every H -/

theorem lookupK : c.lookupFn fK = some fnK := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupKH (H : HookParams) : (cH H).lookupFn fK = some fnK := by
  rw [Semantics.lookupFn_withHooks]; exact lookupK

theorem coreExH (H : HookParams) : (cH H).coreOKEx = true := (coreOKEx_withHooks_fm c H).trans coreEx

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) (coreExH H)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- k's clause applies at every argument of Int. -/
theorem not_fails_k (H : HookParams) {x : GroundTerm} (hx : (cH H).sortOf x = some Srt.int) :
    ¬ Fails (cH H) [x] clK := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : (cH H).WellSorted clK.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **Every premise but k's own items avoids `Lblk`, for every H.** -/
theorem avoidsOffH (H : HookParams) : AvoidsOff (cH H) fK ((cH H).symName fK) := by
  have hn : (cH H).symName fK = nK := name_k
  rw [hn]
  refine avoidsOff_of_lists (rangeBelowH H) (listsOff_withHooks H lists_k) values_k
    (List.all_eq_true.mp hooks_k) (List.all_eq_true.mp params_k)
    (fun g hg hl => by
      have h1 : NameFree.appOKN c [nK] g.label = true := by
        have := List.all_eq_true.mp fns_k g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fK)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hK : fnK ∈ c.allFns.filter (fun g => decide (g.label = fK)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp), by simp [fnK]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp fK_one
  rw [hx, List.mem_singleton] at hfn' hK
  obtain rfl : fn = fnK := hfn'.trans hK.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.int := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails_k H hx (hall clK (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnK])

/-- **Two matches of k's clause at one argument agree on `_Gen0`, for every H.** -/
theorem agreeH (H : HookParams) : ∀ ws σ₁ σ₂, clK.AppliesAt (cH H) σ₁ ws → clK.AppliesAt (cH H) σ₂ ws →
    ∀ i < clK.vars.length, i ∉ clK.exsFree → σ₁.lookup i = σ₂.lookup i := by
  intro ws σ₁ σ₂ h1 h2 i hi hx
  rw [exsFree_k] at hx
  have hi0 : i = 0 := by
    have hl : clK.vars.length = 2 := rfl
    simp only [List.mem_singleton] at hx
    omega
  subst hi0
  obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₁ [.var 0] ws from h1.2.1)
  obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₂ [.var 0] (v :: vs') from h2.2.1)
  cases hvs
  rw [PatVal.var_inv hv, PatVal.var_inv hv']

/-- **The theory has a model for every H** where evaluation has one result at most and the
right-side predicate has truth values. -/
theorem consistent_of_rest (H : HookParams) (hd : FnDet (cH H)) (hq : ClausePostDecided (cH H)) :
    Consistent (cH H) := by
  have hfns : (cH H).fns = [fnK] := read
  refine consistent_of_fnMany_agree (f := fK) (fn := fnK) (cl := clK) (a := Srt.int)
    (coreExH H) (by rw [hfns]; simp) rfl rfl rfl (by decide)
    (by rw [show (cH H).symName fK = nK from name_k]; exact plain_k)
    (by rw [show (cH H).symName fK = nK from name_k, spareSymB_withHooks_fm]; exact spare_k)
    (avoidsOffH H) (by rw [ownKokB_withHooks]; exact kok_k) hd (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) hq (openLaws_of_plain noRaw)
  rw [hfns, List.mem_singleton] at hg'
  subst hg'
  exact absurd rfl hl

/-- The value of X at a match of a clause whose pattern is X and whose X is of Int. -/
theorem match0 {d : Semantics} {cl : Clause} (hp : cl.pats = [.var 0]) (hu : 0 ∈ cl.univ)
    (hv : cl.vars[0]? = some Srt.int) {σ : Subst} {vs : List GroundTerm} (ha : cl.AppliesAt d σ vs) :
    ∃ x, vs = [x] ∧ σ.lookup 0 = some x ∧ d.sortOf x = some Srt.int := by
  have hm : PatVals d σ [.var 0] vs := hp ▸ ha.2.1
  obtain ⟨x, vs', rfl, hx, hs⟩ := PatVals.cons_inv hm
  obtain rfl : vs' = [] := by cases hs; rfl
  obtain ⟨v, hv0, hvs⟩ := ha.1 0 hu Srt.int hv
  have e : some v = some x := hv0.symm.trans (PatVal.var_inv hx)
  obtain rfl := Option.some.inj e
  exact ⟨v, rfl, hv0, hvs⟩

/-- **k's clause is coherent with itself, for every H**: it has no result at any match. -/
theorem coh_clK (H : HookParams) : Coherent (cH H) clK clK := by
  intro vs σ σ' ha _ _ _ _ _ _
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  refine .inr fun r r' hr _ => ?_
  exfalso
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ₁, v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex (by decide)
  · exact two_insts h0 hx hall
  · exact two_insts h0 hx hall

/-- **The right-side predicate has truth values, for every H**: at an instance giving #Or0 the value
w, whether w is one of the nine literals. -/
theorem postDecH (H : HookParams) : ClausePostDecided (cH H) := by
  intro fn hfn cl hcl σ hσ
  have hfns : (cH H).fns = [fnK] := read
  rw [hfns, List.mem_singleton] at hfn
  subst hfn
  simp only [fnK, List.mem_singleton] at hcl; subst hcl
  obtain ⟨w, h1, -⟩ := hσ 1 Srt.int rfl
  exact ⟨_, (dec_post h1).1⟩

end CeOrM

/-! ### Sentence 95 in a model of Γ -/

namespace OrMS95

open GroundTerm OrMFx CeOrM KCore.Parse

def sI : Kore.KSort := srt "Int"

theorem s95 : U.ax95.ax.pattern =
    .exist KoreAML.R (evar "Val" sI) (.equals sI KoreAML.R (ev "Val" sI) (ap "Lblk" [ev "K0" sI])) := by
  decide +kernel
theorem trS_plain : (trS U.ax95).pat = (trAxiom [] [] U.ax95).pat := by decide +kernel
theorem free95 : (U.ax95.ax.sortVars.map sortVarKey ++ freeOf [] U.ax95.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K0" sI] := by decide +kernel
theorem tab95 : (tableOf U.ax95.ax.sortVars U.ax95.ax.pattern).ev (.sortVar "R") = ⟨1⟩ ∧
    (tableOf U.ax95.ax.sortVars U.ax95.ax.pattern).ev (.evar "Val" sI) = ⟨2⟩ ∧
    (tableOf U.ax95.ax.sortVars U.ax95.ax.pattern).ev (.evar "K0" sI) = ⟨3⟩ := by decide +kernel

/-- The valuation sentence 95 is read at: the sort variable R (variable 1) is Int, every other
element variable the element m1. -/
def valAt {M : Type} [Inhabited M] (σI m1 : M) : Valuation M := ⟨Function.update (fun _ => m1) ⟨1⟩ σI, KoreAML.val0.evalSvar⟩

theorem valAt_1 {M : Type} [Inhabited M] (σI m1 : M) : (valAt σI m1).evalEvar ⟨1⟩ = σI := by
  simp [valAt]
theorem valAt_ne {M : Type} [Inhabited M] (σI m1 : M) {x : EVar} (h : x ≠ ⟨1⟩) : (valAt σI m1).evalEvar x = m1 := by
  simp [valAt, Function.update_noteq h]

/-- **k's functional sentence (95) read at `valAt`**: `k(m1)` is one element of Int. -/
theorem fnl_read {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI)
    (hT : I ⊧ᴵ (trAxiom [] [] U.ax95).pat) (m1 : M) (hm1 : Inh I σI m1) :
    ∃ y, ∀ b, Inh I σI b → ((sym (.symbol "Lblk") ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔ b = y) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [free95] at h
  generalize ht : tableOf U.ax95.ax.sortVars U.ax95.ax.pattern = t at h
  have htab := tab95
  rw [ht] at htab
  obtain ⟨h1, h2, h3⟩ := htab
  rw [s95] at h
  rw [interpret_impl] at h
  have hS : ∀ (e : Valuation M) b, (trSort t sI).interpret I e b ↔ b = σI := fun _ b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar "K0" sI)) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ([VarKey.sortVar "R", .evar "K0" sI].map (guardOf t))).interpret I (valAt σI m1) m1 := by
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_⟩
    exact (interp_guard_evar hD).mpr (by rw [h3v]; exact (interp_inhOf_of (hS _)).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sExists] at h5
  obtain ⟨y, -, h6⟩ := h5
  rw [show evarKey (evar "Val" sI) = VarKey.evar "Val" sI from rfl, h2] at h6
  generalize he' : (⟨Function.update (valAt σI m1).evalEvar ⟨2⟩ y, (valAt σI m1).evalSvar⟩ : Valuation M) = e' at h6
  have he'1 : e'.evalEvar ⟨1⟩ = σI := by
    rw [← he']; dsimp only; rw [Function.update_noteq (by decide), valAt_1]
  have he'2 : e'.evalEvar ⟨2⟩ = y := by
    rw [← he']; dsimp only; rw [Function.update_same]
  have he'3 : e'.evalEvar ⟨3⟩ = m1 := by
    rw [← he']; dsimp only; rw [Function.update_noteq (by decide), valAt_ne σI m1 (by decide)]
  have hR' : ∀ b, (trSort t KoreAML.R).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, he'1]
  rw [KoreAML.tr, interp_sEquals hD hc (hS e') hR' hσI2 hσI2] at h6
  refine ⟨y, fun b hb => ?_⟩
  have h7 := h6.2 b hb
  have hv : tr ⟨t, []⟩ (ev "Val" sI) = .evar ⟨2⟩ := by
    unfold ev; rw [KoreAML.tr, show evarKey (evar "Val" sI) = VarKey.evar "Val" sI from rfl, h2]
  have hF : tr ⟨t, []⟩ (ap "Lblk" [ev "K0" sI]) = sym (.symbol "Lblk") ⬝ .evar ⟨3⟩ := by
    unfold ap ev; rw [tr_app0, trArgs_cons, trArgs_nil, KoreAML.tr, show evarKey (evar "K0" sI) = VarKey.evar "K0" sI from rfl, h3]
  rw [hv, hF, interp_evar, he'2] at h7
  refine (interp_app_congr (e := valAt σI m1) (e' := e') (φ := sym (.symbol "Lblk")) (φ' := sym (.symbol "Lblk"))
    (ψ := .evar ⟨2⟩) (ψ' := .evar ⟨3⟩) (fun _ => Iff.rfl) (fun m => ?_) b).trans h7.symm
  rw [interp_evar, interp_evar, he'3, valAt_ne σI m1 (by decide)]

/-- The equation of a clause with existential variables and no clause of a smaller priority, read
in a model: the elements of `f(ws)` are the elements of the result sort in the right side. -/
theorem clause_rawEx {d : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ d) (hnn : NamesNumbered d) (hsc : SortCtx d) [OvlOK d]
    (hph : patHooksApart d = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    (hfn : d.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hlow' : lowerClauses fn cl = [])
    (hws : d.sortsOf ws = some fn.args) (hσ' : d.WellSorted cl.vars σ') (hmatch : PatVals d σ' cl.pats ws)
    (hpats : sortsOfTerms d.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : d.condOK cl.vars cl.pre = true) (hokQ : d.condOK cl.vars cl.post = true)
    (hne : cl.exs ≠ []) (hlt : ∀ i ∈ cl.exs, i < cl.vars.length)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreq : cl.req = none) (hpre : cl.pre.isTop = true)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (e0 : Valuation M) :
    ∃ (tbl : VarTable) (e' : Valuation M), Agrees d I tbl (canonVars d cl.vars) σ' e' ∧
      (∀ i < cl.vars.length, canonKey d cl.vars i ∈ tbl) ∧
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody d fn cl), k ∈ tbl) ∧
      ∀ m, (KoreAML.den (symApp d f (GroundTerm.koreList d ws))).interpret I e0 m ↔
        InS I (d.sortName fn.result) m ∧ (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx d fn cl)).interpret I e' m := by
  have hfnm := (lookupFn_spec hfn).1
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => by rw [hreq] at ht; cases ht
  have hpatsN := Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfnm hcl hpats
  have hv := premise_varsCl (c := d) hpats hreqv
  have htr := hsc.trans
  have hmem := clauseEquation_mem (c := d) hcl hlow'
  unfold clauseEquation at hmem
  rw [clauseRhs_eqEx hne hlt] at hmem
  have hP : ∀ k, k ∈ KoreAML.varsOf (withPre d (canonVars d cl.vars) cl (clausePrem d fn cl)) →
      k ∈ KoreAML.varsOf (withPre d (canonVars d cl.vars) cl (clausePrem d fn cl)) := fun _ h => h
  have hVin := clause_keys_inAxEx (prem := withPre d (canonVars d cl.vars) cl (clausePrem d fn cl)) hpats hreqv hocc hP
  obtain ⟨tbl, e', hk, -, hag, hiff⟩ := eqn_atRightEx hI hnn hfn (eqn_item_mem hfnm hmem) hws hσ'
    (fun j s hj => HoldsShape.varsOf_withPre_prem (hv.1 j s hj)) hVin
    (fun k hk => freeOf_withPreCl hpreOK hpats hreqv hk)
    (fun k hk => freeOf_clauseRightEx hrhsv hensv hokQ hk)
    (fun tbl e σr m0 hk hag hX hRv hσr2 hm0 =>
        withPre_holdsCl (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpatsN hag hX hRv hσr2 hm0
          (fun t ht => by rw [hreq] at ht; cases ht))
          hk (fun hpt => by rw [hpre] at hpt; cases hpt)) e0
  exact ⟨tbl, e', hag, fun i hi => hk _ (hVin i hi),
    fun k hk' => hk _ (varsOf_body_inAxEx (Model.varsOf_existsAll_bodyEx hk' _)), hiff⟩

/-- The key of #Or0 (the variable 1 of k's clause). -/
noncomputable abbrev keyZ (H : HookParams) : VarKey := canonKey (cH H) clK.vars 1

/-- **The body `#Or0 ∧ ⊤ ∧ post` of k's right side holds the element of the literal w** at a
valuation where #Or0 is that element, for w one of the nine literals. -/
theorem body_holds (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {tbl : VarTable} {e : Valuation M} {w : Int}
    (hw : w = 1 ∨ w ∈ [2, 3, 4, 5, 6, 7, 8, 9])
    (hB : e.evalEvar (tbl.ev (keyZ H)) = elemOf (cH H) I (int w)) :
    (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody (cH H) fnK clK)).interpret I e (elemOf (cH H) I (int w)) := by
  haveI : OvlOK (cH H) := (hypSoundEx_of_coreEx (coreExH H)).2.2.2.2.2.2.2.2
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (c := cH H) (s := Srt.int) int_numbered
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf (cH H) Srt.int)).interpret I e b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  have hst := elemOf_spec hI (show (cH H).sortOf (int w) = some Srt.int from rfl) e
  have hinT : InS I ((cH H).sortName Srt.int) (elemOf (cH H) I (int w)) := (inS_iff e).mp hst.2
  have hinh : Inh I σr (elemOf (cH H) I (int w)) :=
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e) hσr1).mp ((inS_iff e).mpr hinT)
  have hvar : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore (cH H) (canonVars (cH H) clK.vars) (.var 1))).interpret I e a ↔
      a = elemOf (cH H) I (int w) := fun a => (tr_var 1 a).trans (by rw [← hB]; exact Iff.rfl)
  have hdv : ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore (cH H) (canonVars (cH H) clK.vars) (.dv Srt.int (.int w)))).interpret I e m ↔
      (den (cH H) (.dv Srt.int (.int w))).interpret I e m := fun m => by
    rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf; rw [KoreAML.tr_dv, KoreAML.tr_dv]
  -- the reading of a condition at the element
  let P : Cond → Prop := fun q =>
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore (cH H) (canonVars (cH H) clK.vars) (srtOf (cH H) Srt.int) q)).interpret I e
      (elemOf (cH H) I (int w))
  have hmem : P (memK w) := by
    show (KoreAML.tr ⟨tbl, []⟩ (.in (srtOf (cH H) Srt.int) (srtOf (cH H) Srt.int)
      (Term.kore (cH H) (canonVars (cH H) clK.vars) (.var 1))
      (Term.kore (cH H) (canonVars (cH H) clK.vars) (.dv Srt.int (.int w))))).interpret I e _
    rw [KoreAML.tr, KoreAML.interp_sIn hD hc hS hS hσr2 hσr2 (fun a ha => by rw [(hvar a).mp ha]; exact hinh)]
    exact ⟨⟨_, (hvar _).mpr rfl, (hdv _).mpr ((hst.1 _).mpr rfl)⟩, hinh⟩
  have hor : ∀ p q, P p ∨ P q → P (.or p q) := fun p q h => by
    show (KoreAML.tr ⟨tbl, []⟩ (.or (srtOf (cH H) Srt.int)
      [Cond.kore (cH H) (canonVars (cH H) clK.vars) (srtOf (cH H) Srt.int) p,
       Cond.kore (cH H) (canonVars (cH H) clK.vars) (srtOf (cH H) Srt.int) q])).interpret I e _
    rw [KoreAML.tr]; simp only [trOrList]
    rw [interp_sOr]
    exact ⟨(interp_inhOf_of hS).mpr hinh, h⟩
  have hfold : ∀ (ks : List Int) (p : Cond), P p ∨ w ∈ ks → P (ks.foldl (fun p k => .or p (memK k)) p) := by
    intro ks
    induction ks with
    | nil => intro p h; rcases h with h | h; exact h; cases h
    | cons k ks ih =>
      intro p h
      refine ih _ ?_
      rcases h with h | h
      · exact .inl (hor _ _ (.inl h))
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl (hor _ _ (.inr hmem))
        · exact .inr h
  have hpost : P postK := by
    rcases hw with rfl | hw
    · exact hfold _ _ (.inl hmem)
    · exact hfold _ _ (.inr hw)
  have hb : clauseRhsBody (cH H) fnK clK = .and (srtOf (cH H) Srt.int)
      [Term.kore (cH H) (canonVars (cH H) clK.vars) (.var 1), reqPat (srtOf (cH H) Srt.int) none,
       Cond.kore (cH H) (canonVars (cH H) clK.vars) (srtOf (cH H) Srt.int) postK] := rfl
  rw [hb, tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
  refine ⟨(hvar _).mpr rfl, ?_, hpost⟩
  simp only [reqPat]
  rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
  exact hinh

/-- **Γ's item of k's clause puts the element of each of the nine literals in k(1)**, for every H
(here 1 and 2 are used): the instance at #Or0 := w gives w. -/
theorem inK (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {w : Int} (hw : w = 1 ∨ w ∈ [2, 3, 4, 5, 6, 7, 8, 9]) :
    (KoreAML.den (symApp (cH H) fK (GroundTerm.koreList (cH H) [int 1]))).interpret I KoreAML.val0
      (elemOf (cH H) I (int w)) := by
  obtain ⟨hok, hsr, hnn, hg, hph, -, -, -, hno⟩ := hypSoundEx_of_coreEx (coreExH H)
  haveI : OvlOK (cH H) := hno
  have hsc := sortCtx_of_allCEx hok hsr (Semantics.ovlCase_of_coreEx (coreExH H))
  have hD := defOK hI
  have hσ' : (cH H).WellSorted clK.vars [(1, int w), (0, int 1)] :=
    sorted2 rfl (rmS_sortOf_int _ 1) rfl (rmS_sortOf_int _ w)
  obtain ⟨tbl, e', hag, hkeys, -, hiff⟩ := clause_rawEx hI hnn hsc hph (f := fK) (fn := fnK) (cl := clK)
    (ws := [int 1]) (σ' := [(1, int w), (0, int 1)]) (lookupKH H) (List.mem_singleton_self _) lower_k
    (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl) hσ' (.cons (.var rfl) .nil)
    pats_k preOK_k postOK_k (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) KoreAML.val0
  have hst := elemOf_spec hI (show (cH H).sortOf (int w) = some Srt.int from rfl) e'
  have hinT : InS I ((cH H).sortName Srt.int) (elemOf (cH H) I (int w)) := (inS_iff e').mp hst.2
  have hBe : e'.evalEvar (tbl.ev (keyZ H)) = elemOf (cH H) I (int w) :=
    (hst.1 _).mp ((hag 1 (int w) (by rw [canonVars_length]; decide) rfl _).mp rfl)
  have hlt : ∀ i ∈ clK.exs, i < clK.vars.length := by decide
  have hndB := binders_nodupEx hkeys hlt (l := clK.exs) (by decide)
  have hsB := binders_sortEx (c := cH H) (vars := clK.vars) hlt
  have hsort : ∀ i ∈ clK.exs,
      ((canonVars (cH H) clK.vars).getD i default).kore.sort = KoreAML.srt ((cH H).sortName (clK.vars.getD i 0)) :=
    fun i hi => by rw [canonVars_getD (cH H) (hlt i hi)]; rfl
  refine (hiff _).mpr ⟨hinT, ?_⟩
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (c := cH H) (s := Srt.int) int_numbered
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf (cH H) Srt.int)).interpret I e' b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  unfold clauseRightEx
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨existsAll_intro_at hD (clauseExBinders (cH H) clK) e' e' _ hndB hsB (fun _ _ => rfl) rfl (fun b hb n hn => ?_)
    (body_holds H hI hw hBe), ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi1 : i = 1 := by simpa [clK] using hi
    subst hi1
    rw [hsort 1 (by decide)] at hn
    rw [← srt_inj hn]
    exact hBe ▸ hinT
  · show (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf (cH H) Srt.int) none)).interpret I e' _
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl)]
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf (cH H) Srt.int))).interpret I e' _
    rw [KoreAML.interp_inhOf_of hS]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e') hσr1).mp ((inS_iff e').mpr hinT)

/-- k's head is the symbol `Lblk`. -/
theorem symHead_k (H : HookParams) : symHead (cH H) fK = KoreAML.sym (.symbol "Lblk") := by
  unfold symHead; rw [show (cH H).symName fK = nK from name_k, plain_k]; rfl

end OrMS95

/-! ### The facts the deciders name -/

def callOrder : List Nat := [CeOrM.fK]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `k`'s. -/
theorem match_named : c.matchObligationsL = [(CeOrM.fK, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### The owed fact refuted, `FnHyp` false, consistency, and sentence 95, for every H -/

section Stated

open GroundTerm OrMFx CeOrM OrMS95 KCore.Parse KCore.GenEqs KCore.Faithful.Model

/-- **Every function has at most one result, for every H**: k's one clause is coherent with itself
(it has no result at any match), and a sort predicate's clauses as in `Faithful.fnDet_of_agree`. -/
theorem fnDetH (H : HookParams) : FnDet (cH H) := by
  refine fnDet_of_coherent fun f fn hfn cl hcl cl' hcl' hprio => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · have hfns : (cH H).fns = [fnK] := read
    rw [hfns, List.mem_singleton] at hu
    subst hu
    simp only [fnK, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clK H
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

/-- **k's clause is not match independent, for every H**: it decides at `[0]` and has no result
there (its instances at #Or0 := 1 and #Or0 := 2 give 1 and 2). -/
theorem not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) clK := not_mi (lookupKH H)

/-- **`FnHyp` is false, for every H**: its fourth conjunct is the match independence of k's clause. -/
theorem not_fnHypH (H : HookParams) : ¬ FnHyp (cH H) := fun hf =>
  not_matchIndependent H (hf.2.2.2.1 fnK
    (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_singleton_self _)
    clK (List.mem_singleton_self _))

/-- **Γc with the step's closure has a model, for every H** (`consistent_of_fnMany_agree` at k). -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of_rest H (fnDetH H) (postDecH H)

/-- **Sentence 95 (k's functional sentence) holds in no model of Γ, for every H**: Γ's item of k's
clause puts the elements of 1 and 2 in k(1) (`inK`), the sentence makes k(1) one element of Int
(`fnl_read`), and the values 1 and 2 of Int are distinct elements (`ΓDomains`, `values_apart`). -/
theorem s95_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax95).pat) := by
  intro M _ I hI h95
  obtain ⟨hsok, hsr, hnn, hg, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx (coreExH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_allCEx hsok hsr (Semantics.ovlCase_of_coreEx (coreExH H))).trans
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (c := cH H) (s := Srt.int) int_numbered
  have hσI1' : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI := fun a => by
    have h := hσI1 a; rwa [show (cH H).sortName Srt.int = "Int" from int_name] at h
  let m1 := elemOf (cH H) I (int 1)
  let m2 := elemOf (cH H) I (int 2)
  have hinh : ∀ (w : Int), Inh I σI (elemOf (cH H) I (int w)) := fun w => by
    have hst := elemOf_spec hI (show (cH H).sortOf (int w) = some Srt.int from rfl) KoreAML.val0
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := KoreAML.val0) hσI1).mp hst.2
  obtain ⟨y, hy⟩ := fnl_read hD hc hσI1' hσI2 (by rw [← trS_plain]; exact h95) m1 (hinh 1)
  have hden1 : ∀ m, (den (cH H) (int 1)).interpret I KoreAML.val0 m ↔ m = m1 :=
    (elemOf_spec hI (show (cH H).sortOf (int 1) = some Srt.int from rfl) KoreAML.val0).1
  have hF : ∀ b, (KoreAML.den (symApp (cH H) fK (GroundTerm.koreList (cH H) [int 1]))).interpret I KoreAML.val0 b ↔
      (sym (.symbol "Lblk") ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b := fun b => by
    show (KoreAML.tr ⟨[], []⟩ (symApp (cH H) fK [GroundTerm.kore (cH H) (int 1)])).interpret I KoreAML.val0 b ↔ _
    rw [tr_symApp, trArgs_cons, trArgs_nil, symHead_k]
    refine interp_app_congr (e := KoreAML.val0) (e' := valAt σI m1) (fun _ => Iff.rfl) (fun m => ?_) b
    rw [interp_evar, valAt_ne σI m1 (by decide)]
    exact hden1 m
  have e1 : m1 = y := (hy m1 (hinh 1)).mp ((hF _).mp (inK H hI (.inl rfl)))
  have e2 : m2 = y := (hy m2 (hinh 2)).mp ((hF _).mp (inK H hI (.inr (by decide))))
  exact absurd (values_apart hI hg htr int_apart (rmS_sortOf_int (cH H) 1) (rmS_sortOf_int (cH H) 2)
    (e1.trans e2.symm)) (by decide)

end Stated

#check @KCore.TieE3MlEqRhsOrMany.s95_refuted
#print axioms KCore.TieE3MlEqRhsOrMany.s95_refuted

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

theorem nj109 : (trS U.ax109).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj114 : (trS U.ax114).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj117 : (trS U.ax117).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax109, U.ax114, U.ax117], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj109]; exact orTopBot_valid hD rfl
  · rw [nj114]; exact orTopBot_valid hD rfl
  · rw [nj117]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax110, U.ax111, U.ax112, U.ax113, U.ax115, U.ax116],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax110, U.ax111, U.ax112, U.ax113, U.ax115, U.ax116],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax118).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (118)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax118).pat := by
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax99, U.ax100]

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


/-! ## Library sample: sentence 158, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax158).pat = (trAxiom [] [] U.ax158).pat := by decide +kernel
theorem s166_pattern : U.ax158.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax158.ax.sortVars.map sortVarKey ++ freeOf [] U.ax158.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax158.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 158 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax158.ax.sortVars U.ax158.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax158).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax158.ax.sortVars U.ax158.ax.pattern = t at he ⊢
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
/-- **Sentence 158 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax158 (trS U.ax158).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## Function equations (28 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 235) is not its sentence (`un<j>_differs`), and no reading here gives it from
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

/-- Γ's item 0 (sentence 235): no reading here ties it. -/
noncomputable def unItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem unItem0_at : (TiePair.gammaPats c)[0]? = some unItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax235
/-- **Γ's item 0 is not the text's sentence 235** (kernel): the sentence is uncovered. -/
theorem un0_differs : unItem0 ≠ (trS U.ax235).pat := by decide +kernel

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
    ∀ ad ∈ [U.ax109, U.ax114, U.ax117], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax110, U.ax111, U.ax112, U.ax113, U.ax115, U.ax116],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax118).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 60 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax60).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE3MlEqRhsOrMany

#check @KCore.TieE3MlEqRhsOrMany.noRaw
#check @KCore.TieE3MlEqRhsOrMany.readsConfined_c
#check @KCore.TieE3MlEqRhsOrMany.userAxioms_eq
#check @KCore.TieE3MlEqRhsOrMany.coreOK
#check @KCore.TieE3MlEqRhsOrMany.account
#check @KCore.TieE3MlEqRhsOrMany.account_sizes
#check @KCore.TieE3MlEqRhsOrMany.account_classes
#check @KCore.TieE3MlEqRhsOrMany.account_absent
#check @KCore.TieE3MlEqRhsOrMany.absent_closed
#check @KCore.TieE3MlEqRhsOrMany.absent_proj_below_c
#check @KCore.TieE3MlEqRhsOrMany.absent_proj_below
#check @KCore.TieE3MlEqRhsOrMany.lists_in_account
#check @KCore.TieE3MlEqRhsOrMany.attrs_agree
#check @KCore.TieE3MlEqRhsOrMany.sig_origin_but_next
#check @KCore.TieE3MlEqRhsOrMany.decls_entailed
#check @KCore.TieE3MlEqRhsOrMany.consistent
#check @KCore.TieE3MlEqRhsOrMany.not_matchIndependent
#check @KCore.TieE3MlEqRhsOrMany.not_fnHypH
#check @KCore.TieE3MlEqRhsOrMany.text_nextless
#check @KCore.TieE3MlEqRhsOrMany.nojunk_trivial_entailed
#check @KCore.TieE3MlEqRhsOrMany.nojunk_items_entailed
#check @KCore.TieE3MlEqRhsOrMany.nojunk_kitem_entailed
#check @KCore.TieE3MlEqRhsOrMany.cons_entailed
#check @KCore.TieE3MlEqRhsOrMany.idem_refuted
#check @KCore.TieE3MlEqRhsOrMany.lib166
#check @KCore.TieE3MlEqRhsOrMany.lib166_at_values
#check @KCore.TieE3MlEqRhsOrMany.owed_rules
#check @KCore.TieE3MlEqRhsOrMany.owed_clauses
#check @KCore.TieE3MlEqRhsOrMany.openDecidedH
#check @KCore.TieE3MlEqRhsOrMany.gammaCl_eq
#check @KCore.TieE3MlEqRhsOrMany.decls_entailed_c
#check @KCore.TieE3MlEqRhsOrMany.nojunk_trivial_entailed_c
#check @KCore.TieE3MlEqRhsOrMany.nojunk_items_entailed_c
#check @KCore.TieE3MlEqRhsOrMany.nojunk_kitem_entailed_c
#check @KCore.TieE3MlEqRhsOrMany.cons_entailed_c
#check @KCore.TieE3MlEqRhsOrMany.idem_refuted_c
#print axioms KCore.TieE3MlEqRhsOrMany.noRaw
#print axioms KCore.TieE3MlEqRhsOrMany.readsConfined_c
#print axioms KCore.TieE3MlEqRhsOrMany.userAxioms_eq
#print axioms KCore.TieE3MlEqRhsOrMany.coreOK
#print axioms KCore.TieE3MlEqRhsOrMany.account
#print axioms KCore.TieE3MlEqRhsOrMany.account_sizes
#print axioms KCore.TieE3MlEqRhsOrMany.account_classes
#print axioms KCore.TieE3MlEqRhsOrMany.account_absent
#print axioms KCore.TieE3MlEqRhsOrMany.absent_closed
#print axioms KCore.TieE3MlEqRhsOrMany.absent_proj_below_c
#print axioms KCore.TieE3MlEqRhsOrMany.absent_proj_below
#print axioms KCore.TieE3MlEqRhsOrMany.lists_in_account
#print axioms KCore.TieE3MlEqRhsOrMany.attrs_agree
#print axioms KCore.TieE3MlEqRhsOrMany.sig_origin_but_next
#print axioms KCore.TieE3MlEqRhsOrMany.decls_entailed
#print axioms KCore.TieE3MlEqRhsOrMany.consistent
#print axioms KCore.TieE3MlEqRhsOrMany.not_matchIndependent
#print axioms KCore.TieE3MlEqRhsOrMany.not_fnHypH
#print axioms KCore.TieE3MlEqRhsOrMany.text_nextless
#print axioms KCore.TieE3MlEqRhsOrMany.nojunk_trivial_entailed
#print axioms KCore.TieE3MlEqRhsOrMany.nojunk_items_entailed
#print axioms KCore.TieE3MlEqRhsOrMany.nojunk_kitem_entailed
#print axioms KCore.TieE3MlEqRhsOrMany.cons_entailed
#print axioms KCore.TieE3MlEqRhsOrMany.idem_refuted
#print axioms KCore.TieE3MlEqRhsOrMany.lib166
#print axioms KCore.TieE3MlEqRhsOrMany.lib166_at_values
#print axioms KCore.TieE3MlEqRhsOrMany.owed_rules
#print axioms KCore.TieE3MlEqRhsOrMany.owed_clauses
#print axioms KCore.TieE3MlEqRhsOrMany.openDecidedH
#print axioms KCore.TieE3MlEqRhsOrMany.gammaCl_eq
#print axioms KCore.TieE3MlEqRhsOrMany.decls_entailed_c
#print axioms KCore.TieE3MlEqRhsOrMany.nojunk_trivial_entailed_c
#print axioms KCore.TieE3MlEqRhsOrMany.nojunk_items_entailed_c
#print axioms KCore.TieE3MlEqRhsOrMany.nojunk_kitem_entailed_c
#print axioms KCore.TieE3MlEqRhsOrMany.cons_entailed_c
#print axioms KCore.TieE3MlEqRhsOrMany.idem_refuted_c
#check @KCore.TieE3MlEqRhsOrMany.fns_account
#check @KCore.TieE3MlEqRhsOrMany.un0_differs
#check @KCore.TieE3MlEqRhsOrMany.shape
#check @KCore.TieE3MlEqRhsOrMany.fns_entailed
#check @KCore.TieE3MlEqRhsOrMany.fns_from_text
#check @KCore.TieE3MlEqRhsOrMany.fn_prios
#check @KCore.TieE3MlEqRhsOrMany.gamma_from
#print axioms KCore.TieE3MlEqRhsOrMany.fns_account
#print axioms KCore.TieE3MlEqRhsOrMany.un0_differs
#print axioms KCore.TieE3MlEqRhsOrMany.shape
#print axioms KCore.TieE3MlEqRhsOrMany.fns_entailed
#print axioms KCore.TieE3MlEqRhsOrMany.fns_from_text
#print axioms KCore.TieE3MlEqRhsOrMany.fn_prios
#print axioms KCore.TieE3MlEqRhsOrMany.gamma_from
