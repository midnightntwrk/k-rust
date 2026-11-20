/-
  The tie (C14) on `f2-examples/e3-ml-eq-rhs-or.kompile.kore`, the kompiled text of construct fixture e3-ml-eq-rhs-or
  (`test/constructs/fixtures/e3-ml-eq-rhs-or`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-eq-rhs-or`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlEqRhsOr.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 253 sentences of the user module E3-ML-EQ-RHS-OR, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 13 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 206 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator
    (`noRaw`). It owes the match independence of a clause (`match_named`).
    The consistency section, written by hand, refutes the match independence it owes: for the clause
    `clH` it is false for every H (`h_not_matchIndependent`), and so is `FnHyp` (`not_fnHypH`).
    `OpenDecided` holds for every H (`openDecidedH`). `Γc` with the step's closure has a model for every
    H all the same (`consistent`), outside the value model, whose construction reads `FnHyp`
    (`consistent_of_fnHyp`) or the named facts (`consistent_of_fnFacts`), the refuted one among them.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 2 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 2 (204) is the equation read as a clause with existential
    variables (`existentialClause`), not its sentence (`ex<j>_differs`): the two hold in the same
    interpretations with the signature's facts (`ex<j>_iff`, by a lemma of
    KcoreSpec/TieExClause.lean), so Γ entails the sentence (`ex<j>_entailed`) and the sentence with
    `ΓSig` gives the item (`ex<j>_from_text`, W1), which `fns_from_text` leaves out. `fns_from_text`
    (the converse), `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 157 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 2 (whose sentence gives it with `ΓSig`: `ex<j>_from_text`), Γ's rule items, the five parts
    Γ defines by predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp`, which is false for every H (`not_fnHypH`): not shown by this tie; no
    direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (5);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlEqRhsOr

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or.kompile.kore" module "E3-ML-EQ-RHS-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-OR")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 253 := by decide +kernel

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
  [("function equation", [200, 202, 204, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
      223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [21, 23, 25, 27, 98, 99]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]),
   ("injectivity", [22, 24, 26, 28]),
   ("distinctness", []),
   ("no junk", [108, 109, 110, 111, 112, 113, 114, 115, 116, 117]),
   ("function functional", [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93]),
   ("hooked functional", [18, 19, 20, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      55, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 76, 77, 79, 95, 96, 97, 100, 101, 102, 103,
      104, 105]),
   ("collection law", [52, 53, 54, 56, 57, 58, 59, 61, 62]),
   ("library", [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140,
      141, 142, 143, 144, 145, 146, 147, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
      160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
      178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196,
      197, 198, 199, 201, 237, 238, 239, 240, 254, 255]),
   ("set idempotence", [60]),
   ("set-variable lemma", [118, 119, 120, 121, 122, 256]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 39, 41, 72, 74, 78, 94, 106, 107, 148, 180, 203, 205, 206, 207, 235, 236, 241, 242, 243,
      244, 245, 246, 247, 248, 249, 250, 251, 252, 253])]

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
    [("function equation", 30), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 30)] := by
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
  [(241, "Bool"), (242, "GeneratedCounterCell"), (243, "GeneratedCounterCellOpt"),
   (244, "GeneratedTopCell"), (245, "GeneratedTopCellFragment"), (246, "Int"), (247, "K"),
   (248, "KCell"), (249, "KCellOpt"), (250, "KItem"), (251, "List"), (252, "Map"), (253, "Set")]

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
  [(117, "no junk"), (200, "function equation"), (202, "function equation"),
   (204, "function equation"), (207, "no direction")]

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

theorem sig_sizes : (sigItems c).length = 206 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 129, 92, 5, 32) := by
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

/-! ## Consistency for every H: `h(X) => f(X) #Or g(X)`, its match independence refuted -/

/- The functions `f` (`f(X) => X`) and `g` (`g(X) => 0 -Int X`) have one clause each without an
existential variable; `h` has the one clause `FnMany.clH`, read with the existential variable #Or0 of
Int (`exs [1]`, `rhs := #Or0`, `post := #Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`). No function is declared `total`
and the text holds no functional sentence of `h`.
- The match independence `match_named` names, of `h`'s clause, is false for every H
  (`h_not_matchIndependent`): at `[1]` the clause decides, its instance at #Or0 := 1 gives 1 alone
  (`f(1)` is 1) and its instance at #Or0 := `0 - 1` gives `0 - 1` alone (`g(1)` is `0 - 1`), so it
  has no result there (`FnMany.resEx_h`, `FnMany.resEx_neg`). So `FnHyp`, whose fourth conjunct is
  that fact, is false for every H (`not_fnHypH`).
- Every function has at most one result, for every H (`fnDetH`, by `fnDet_of_coherent`): the clauses
  of `f` and `g` are coherent with themselves (one right side at matches agreeing on X), `h`'s
  through its results' agreement (a result of it at a match giving X the value x is x).
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `Γc` with the step's closure has a model for every H (`consistent`), by
  `Faithful.Model.consistent_of_fnMany_agree`
  at `h`: the value model with `h` read as the set of its instances' values. Its hypotheses, each for
  every H: every premise of the theory but `h`'s own items avoids `h`'s name (`FnMany.avoidsOffH`;
  `h`'s clause applies at every argument of Int, so the theory states no rest of `h`), two matches of
  `h`'s clause at one argument agree on X (`FnMany.agreeH`), `fnDetH`, `f` and `g` solve their
  equations (`FnMany.solvesF`, `FnMany.solvesG`: `f(x)` is x and `g(n)` is `0 - n`), and the
  right-side predicates have truth values (`FnMany.postDecH`).

`OrFx` and `FnMany` hold the proofs; the statements after them are on `cH H`. -/

/-! ### Facts the proofs share -/

namespace OrFx

open GroundTerm KCore.Parse KCore.GenEqs KCore.Faithful.Model

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

/-- A substitution giving the variable 0 a value of the sort is well sorted. -/
theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

/-- The predicate p has the truth value b under σ, and no other. -/
def Dec (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {n : Nat} {p q : Cond} {b b' : Bool} (hp : Dec d n σ p b) (hq : Dec d n σ q b') :
    Dec d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

/-- `f` is a function of d: no constructor, hook, parameter or overloading symbol, so an
application of it on defined arguments has `Eval`'s results. -/
def FnSym (d : Semantics) (f : Sym) : Prop :=
  d.isCtor f = false ∧ isHook f = false ∧ d.isParam f = false ∧ d.isOvl f = false

/-- `f` has at `[x]` the result r and no other. -/
def Only (d : Semantics) (f : Sym) (x : GroundTerm) (r : Option GroundTerm) : Prop :=
  Eval d f [x] r ∧ ∀ r', Eval d f [x] r' → r' = r

/-- The application `f(X)` of a function has `f`'s results at the value σ gives X. -/
theorem call_of {f : Sym} (hf : FnSym d f) {x : GroundTerm} (h0 : σ.lookup 0 = some x)
    {r : Option GroundTerm} (h : Eval d f [x] r) : EvalTerm d σ (.app f [.var 0]) r :=
  .call hf.1 hf.2.1 (rs := [σ.lookup 0]) (.cons .var .nil) (by rw [h0]; rfl) h hf.2.2.1

theorem call_inv {f : Sym} (hf : FnSym d f) {x : GroundTerm} (h0 : σ.lookup 0 = some x)
    {r : Option GroundTerm} (h : EvalTerm d σ (.app f [.var 0]) r) : Eval d f [x] r := by
  have hrs : ∀ {rs}, EvalTerms d σ [.var 0] rs → rs = [some x] := fun hts => by
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    rw [h0]
  generalize ht : Term.app f [.var 0] = t at h
  cases h with
  | hook _ hk _ _ _ => cases ht; rw [hf.2.1] at hk; cases hk
  | ctor hc _ => cases ht; rw [hf.1] at hc; cases hc
  | param _ _ hp _ _ => cases ht; rw [hf.2.2.1] at hp; cases hp
  | call _ _ hts hvs he _ =>
    cases ht
    rw [hrs hts] at hvs
    cases hvs
    exact he
  | callUndef _ _ hts hvs _ => cases ht; rw [hrs hts] at hvs; cases hvs
  | ovl _ ho _ _ => cases ht; rw [hf.2.2.2] at ho; cases ho
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [hf.2.2.2] at ho; cases ho
  | _ => cases ht

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

end OrFx

namespace FnMany

open GroundTerm OrFx KCore.Parse KCore.GenEqs KCore.Faithful.Model

def fF : Sym := 384
def fG : Sym := 385
def fH : Sym := 386
def nH : String := "Lblh"

/-- `f(X) => X`. -/
def clF : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }

/-- `g(X) => 0 -Int X`. -/
def clG : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intSub [.dv Srt.int (.int 0), .var 0],
    ens := none }

/-- `#Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`. -/
def postH : Cond :=
  .or (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app fG [.var 0]))

/-- `h(X) => #Or0` with `exs = [#Or0]` and `post := postH`. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postH }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clF] }
def fnG : Fn := { label := fG, args := [Srt.int], result := Srt.int, clauses := [clG] }
def fnH : Fn := { label := fH, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, `h` with the one clause `clH`. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem name_h : c.symName fH = nH := by decide +kernel

/-! ### The checks on the text -/

theorem plain_h : instDecode? nH = none := by decide +kernel
theorem spare_h : spareSymB c nH = true := by decide +kernel
theorem values_h : NameFree.valuesN c [nH] = true := by rw [NameFree.valuesN]; decide_cheap 40
theorem hooks_h : hookSigs.all (fun k => NameFree.appOKN c [nH] k.name) = true := by decide_cheap 40
theorem params_h : c.params.all (fun k => NameFree.appOKN c [nH] k.sig.name) = true := by decide_cheap 40
theorem fns_h : c.allFns.all (fun g => decide (g.label = fH) || NameFree.appOKN c [nH] g.label) = true := by
  decide_cheap 40
theorem lists_h : listsOffB c fH nH = true := by rw [listsOffB]; decide_cheap 40
theorem kok_h : ownKokB c fnH clH = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem fH_one : (c.allFns.filter (fun g => decide (g.label = fH))).length = 1 := by decide +kernel
theorem exsFree_h : clH.exsFree = [1] := by decide

/-! ### For every H -/

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) ((coreOKEx_withHooks_fm c H).trans coreEx)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- h's clause applies at every argument of Int. -/
theorem not_fails_h (H : HookParams) {x : GroundTerm} (hx : (cH H).sortOf x = some Srt.int) :
    ¬ Fails (cH H) [x] clH := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : (cH H).WellSorted clH.vars [(1, x), (0, x)] := by
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨x, rfl, hx⟩
      | 1, hs => cases hs; exact ⟨x, rfl, hx⟩
      | i + 2, hs => simp [clH] at hs
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **Every premise but h's own items avoids `Lblh`, for every H.** -/
theorem avoidsOffH (H : HookParams) : AvoidsOff (cH H) fH ((cH H).symName fH) := by
  have hn : (cH H).symName fH = nH := name_h
  rw [hn]
  refine avoidsOff_of_lists (rangeBelowH H) (listsOff_withHooks H lists_h) values_h
    (List.all_eq_true.mp hooks_h) (List.all_eq_true.mp params_h)
    (fun g hg hl => by
      have h1 : NameFree.appOKN c [nH] g.label = true := by
        have := List.all_eq_true.mp fns_h g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fH)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hH : fnH ∈ c.allFns.filter (fun g => decide (g.label = fH)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp), by simp [fnH]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp fH_one
  rw [hx, List.mem_singleton] at hfn' hH
  obtain rfl : fn = fnH := hfn'.trans hH.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.int := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails_h H hx (hall clH (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnH])

/-- **Two matches of h's clause at one argument agree on X, for every H.** -/
theorem agreeH (H : HookParams) : ∀ ws σ₁ σ₂, clH.AppliesAt (cH H) σ₁ ws → clH.AppliesAt (cH H) σ₂ ws →
    ∀ i < clH.vars.length, i ∉ clH.exsFree → σ₁.lookup i = σ₂.lookup i := by
  intro ws σ₁ σ₂ h1 h2 i hi hx
  rw [exsFree_h] at hx
  have hi0 : i = 0 := by
    have hl : clH.vars.length = 2 := rfl
    simp only [List.mem_singleton] at hx
    omega
  subst hi0
  obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₁ [.var 0] ws from h1.2.1)
  obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₂ [.var 0] (v :: vs') from h2.2.1)
  cases hvs
  rw [PatVal.var_inv hv, PatVal.var_inv hv']

/-- **The theory has a model for every H** where evaluation has one result at most, `f` and `g`
solve their equations and the right-side predicates have truth values. -/
theorem consistent_of_rest (H : HookParams) (hd : FnDet (cH H)) (hf : FnSolvesAt (cH H) fnF)
    (hg : FnSolvesAt (cH H) fnG) (hq : ClausePostDecided (cH H)) : Consistent (cH H) := by
  have hfns : (cH H).fns = [fnF, fnG, fnH] := read
  refine consistent_of_fnMany_agree (f := fH) (fn := fnH) (cl := clH) (a := Srt.int)
    ((coreOKEx_withHooks_fm c H).trans coreEx) (by rw [hfns]; simp) rfl rfl rfl (by decide)
    (by rw [show (cH H).symName fH = nH from name_h]; exact plain_h)
    (by rw [show (cH H).symName fH = nH from name_h, spareSymB_withHooks_fm]; exact spare_h)
    (avoidsOffH H) (by rw [ownKokB_withHooks]; exact kok_h) hd (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) hq (openLaws_of_plain noRaw)
  rw [hfns] at hg'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl
  · exact hf
  · exact hg
  · exact absurd rfl hl

/-! ### The clauses of f, g and h, for every H -/

theorem kinds : (c.isCtor fF = false ∧ isHook fF = false ∧ c.isParam fF = false ∧ c.isOvl fF = false) ∧
    (c.isCtor fG = false ∧ isHook fG = false ∧ c.isParam fG = false ∧ c.isOvl fG = false) ∧
    c.isCtor intSub = false := by decide +kernel
theorem shapes : c.shapesOK = true := by decide_cheap

section Clause

variable {d : Semantics} {σ : Subst}

/-- The truth value of `postH` where #Or0 has the value w, `f` the result rf and `g` the result rg
at X's value. -/
def postVal (w : GroundTerm) (rf rg : Option GroundTerm) : Bool :=
  sameResult (some w) rf || sameResult (some w) rg

theorem dec_mem {f : Sym} (hf : FnSym d f) {n : Nat} {x w : GroundTerm} {r : Option GroundTerm}
    (ho : Only d f x r) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d n σ (.mem Srt.int (.var 1) (.app f [.var 0])) (sameResult (some w) r) := by
  refine ⟨holds_cast (Holds.mem .var (call_of hf h0 ho.1)) (by rw [h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := ho.2 _ (call_inv hf h0 h')
    rw [h1]; rfl

/-- **`post` is decided** where `f` and `g` each have one result at X's value. -/
theorem dec_post (hF : FnSym d fF) (hG : FnSym d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d 2 σ postH (postVal w rf rg) :=
  dec_or (dec_mem hF hf h0 h1) (dec_mem hG hg h0 h1)

/-- An instance whose `post` is true gives #Or0's value, and agrees with no other result. -/
theorem inst_true (hF : FnSym d fF) (hG : FnSym d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w)
    (hp : postVal w rf rg = true) : InstIs d σ clH (some w) ∧ ∀ r, InstIs d σ clH r → r = some w := by
  have hd := dec_post hF hG hf hg h0 h1
  refine ⟨.gives (h1 ▸ .var) (fun t ht => nomatch ht) (holds_cast hd.1 hp), fun r h => ?_⟩
  cases h with
  | fails _ hfl =>
    cases hfl with
    | ens ht _ _ => cases ht
    | post hq => have e := hd.2 _ hq; rw [hp] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- An instance whose `post` is false gives nothing: it agrees with every result. -/
theorem inst_false (hF : FnSym d fF) (hG : FnSym d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w)
    (hp : postVal w rf rg = false) (r : Option GroundTerm) : InstIs d σ clH r :=
  have hd := dec_post hF hG hf hg h0 h1
  .fails hd.1 (.post (holds_cast hd.1 hp))

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- σ with #Or0 := w is an instance of the clause at σ, well sorted where σ gives X a value of Int
and w is of Int. -/
theorem ext_sorted {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    (hw : d.sortOf w = some Srt.int) : d.WellSorted clH.vars ((1, w) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) hw

theorem ext_x {x : GroundTerm} (h0 : σ.lookup 0 = some x) (w : GroundTerm) :
    ((1, w) :: σ : Subst).lookup 0 = some x := (lkNe _ _ (by decide)).trans h0

end Clause

/-! ### `f` and `g` in a semantics that reads their clauses -/

section FG

variable {d : Semantics}

/-- **`f(x)` is x and nothing else**, at an argument of Int. -/
theorem f_only (hfn : d.lookupFn fF = some fnF) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) :
    Only d fF x (some x) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnF] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clF.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  have hs : d.WellSorted clF.vars [(0, x)] := sorted1 rfl hx
  refine ⟨.clause (fn := fnF) (cl := clF) (σ := [(0, x)]) hfn (List.mem_singleton_self _) hs
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    rw [EvalTerm.var_inv hrhs, hx0 hmatch]
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

theorem subHook : isHook intSub = true := by decide +kernel

/-- `0 -Int n`, under every interpretation: the hook's value on Int values. -/
theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value rfl

theorem evalSub (hc : d.isCtor intSub = false) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ clG.rhs (some (int (0 - n))) :=
  .hook hc subHook (rs := [some (int 0), σ.lookup 0]) (.cons .dv (.cons .var .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookSub n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalSub_inv (hc : d.isCtor intSub = false) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n))
    {r : Option GroundTerm} (h : EvalTerm d σ clG.rhs r) : r = some (int (0 - n)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc subHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain ⟨r1, rs'', rfl, h2, hs'⟩ := EvalTerms.cons_inv hs
  obtain rfl := EvalTerms.nil_inv hs'
  obtain rfl := EvalTerm.dv_inv h1
  obtain rfl := EvalTerm.var_inv h2
  have := hh [int 0, int n] (by rw [h0]; rfl)
  rw [hookSub] at this
  exact (Option.some.inj this).symm

/-- **`g(n)` is `0 - n` and nothing else.** -/
theorem g_only (hc : d.isCtor intSub = false) (hfn : d.lookupFn fG = some fnG) (n : Int) :
    Only d fG (int n) (some (int (0 - n))) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fG = some fn' → cl ∈ fn'.clauses → cl = clG := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnG] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clG.pats [int n] → σ.lookup 0 = some (int n) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  have hs : d.WellSorted clG.vars [(0, int n)] := sorted1 rfl (rmS_sortOf_int d n)
  refine ⟨.clause (fn := fnG) (cl := clG) (σ := [(0, int n)]) hfn (List.mem_singleton_self _) hs
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evalSub hc rfl) (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    exact evalSub_inv hc (hx0 hmatch) hrhs
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clG (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

end FG

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn fG = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn fH = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some fnF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupGH (H : HookParams) : (cH H).lookupFn fG = some fnG := by
  rw [Semantics.lookupFn_withHooks]; exact lookupG
theorem lookupHH (H : HookParams) : (cH H).lookupFn fH = some fnH := by
  rw [Semantics.lookupFn_withHooks]; exact lookupH
theorem funF (H : HookParams) : FnSym (cH H) fF := kinds.1
theorem funG (H : HookParams) : FnSym (cH H) fG := kinds.2.1
theorem subNotCtor (H : HookParams) : (cH H).isCtor intSub = false := kinds.2.2
theorem shapesH (H : HookParams) : (cH H).shapesOK = true := shapes

/-- f and g have one result each at an argument of Int, for every H. -/
theorem fg_only (H : HookParams) {x : GroundTerm} (hx : (cH H).sortOf x = some Srt.int) :
    ∃ rg, Only (cH H) fF x (some x) ∧ Only (cH H) fG x rg := by
  obtain ⟨n, rfl⟩ := shape_int (shapesH H) hx
  exact ⟨_, f_only (lookupFH H) hx, g_only (subNotCtor H) (lookupGH H) n⟩

/-- **A result of h's clause at a match giving X the value x is x, for every H**: the instance at
#Or0 := x has `post` true (`f(x)` is x), so it gives x and agrees with no other result; a result
of the clause agrees with every instance. -/
theorem resEx_h (H : HookParams) {σ : Subst} {x : GroundTerm} {r : Option GroundTerm}
    (h0 : σ.lookup 0 = some x) (hx : (cH H).sortOf x = some Srt.int) (h : clH.ResEx (cH H) σ r) :
    r = some x := by
  obtain ⟨rg, hf, hg⟩ := fg_only H hx
  have hp : postVal x (some x) rg = true := by simp [postVal, sameResult_self]
  have ht := inst_true (funF H) (funG H) hf hg (ext_x h0 x) (lkSelf _ _ _) hp
  have hag : AgreeOff clH.exsFree σ ((1, x) :: σ) := agree_set1 σ x
  have hws := ext_sorted h0 hx hx
  rcases h with ⟨σ₁, v, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩
  · exact ht.2 _ (hall _ hag hws)
  · exact absurd (ht.2 _ (hall _ hag hws)) (by simp)

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

theorem coh_clF (H : HookParams) : Coherent (cH H) clF clF := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) rfl (by decide) rfl ha'
  cases hx'
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  simp [clF, varOccs] at hi
  subst hi; rw [h0, h0']

theorem coh_clG (H : HookParams) : Coherent (cH H) clG clG := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) rfl (by decide) rfl ha'
  cases hx'
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  simp [clG, varOccs, varOccsList] at hi
  subst hi; rw [h0, h0']

theorem coh_clH (H : HookParams) : Coherent (cH H) clH clH := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) rfl (by decide) rfl ha'
  cases hx'
  refine .inr fun r r' hr hr' => ?_
  have hne : clH.exs ≠ [] := by decide
  rcases hr with ⟨he, -⟩ | ⟨-, hr⟩
  · exact absurd he hne
  rcases hr' with ⟨he, -⟩ | ⟨-, hr'⟩
  · exact absurd he hne
  rw [resEx_h H h0 hx hr, resEx_h H h0' hx hr']



/-- **The right-side predicates have truth values, for every H**: f's and g's are `\top`, h's is
decided where f and g each have one result. -/
theorem postDecH (H : HookParams) : ClausePostDecided (cH H) := by
  intro fn hfn cl hcl σ hσ
  have hfns : (cH H).fns = [fnF, fnG, fnH] := read
  rw [hfns] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl
  · simp only [fnF, List.mem_singleton] at hcl; subst hcl; exact ⟨true, .top⟩
  · simp only [fnG, List.mem_singleton] at hcl; subst hcl; exact ⟨true, .top⟩
  · simp only [fnH, List.mem_singleton] at hcl; subst hcl
    obtain ⟨x, h0, hx⟩ := hσ 0 Srt.int rfl
    obtain ⟨w, h1, -⟩ := hσ 1 Srt.int rfl
    obtain ⟨rg, hf, hg⟩ := fg_only H hx
    exact ⟨_, (dec_post (funF H) (funG H) hf hg h0 h1).1⟩

/-- **Evaluation solves f's equation, for every H.** -/
theorem solvesF (H : HookParams) : FnSolvesAt (cH H) fnF := by
  intro vs _ cl hcl σ hdec v
  simp only [fnF, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl hdec.1
  have hf := f_only (lookupFH H) hx
  have hws : (cH H).WellSorted clF.vars σ := (wellSortedAt_univ rfl).mp hdec.1.1
  constructor
  · intro he
    obtain rfl : v = x := Option.some.inj (hf.2 _ he)
    exact ⟨σ, fun _ _ => rfl, hws, h0 ▸ .var, (fun t ht => nomatch ht), .top⟩
  · rintro ⟨σ', hag, -, hy, -, -⟩
    have h0' : σ'.lookup 0 = σ.lookup 0 := hag 0 (by simp [Clause.exsFree, clF])
    have e := EvalTerm.var_inv hy
    rw [h0', h0] at e
    cases e
    exact hf.1

/-- **Evaluation solves g's equation, for every H.** -/
theorem solvesG (H : HookParams) : FnSolvesAt (cH H) fnG := by
  intro vs _ cl hcl σ hdec v
  simp only [fnG, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl hdec.1
  obtain ⟨n, rfl⟩ := shape_int (shapesH H) hx
  have hg := g_only (subNotCtor H) (lookupGH H) n
  have hws : (cH H).WellSorted clG.vars σ := (wellSortedAt_univ rfl).mp hdec.1.1
  constructor
  · intro he
    obtain rfl : v = int (0 - n) := Option.some.inj (hg.2 _ he)
    exact ⟨σ, fun _ _ => rfl, hws, evalSub (subNotCtor H) h0, (fun t ht => nomatch ht), .top⟩
  · rintro ⟨σ', hag, -, hy, -, -⟩
    have h0' : σ'.lookup 0 = some (int n) := (hag 0 (by simp [Clause.exsFree, clG])).trans h0
    obtain rfl := Option.some.inj (evalSub_inv (subNotCtor H) h0' hy)
    exact hg.1

/-- A result of h's clause at a match giving X the value n is `0 - n`: the instance at
#Or0 := `0 - n` has `post` true (`g(n)` is `0 - n`) and gives `0 - n` alone. -/
theorem resEx_neg (H : HookParams) {σ : Subst} {n : Int} {r : Option GroundTerm}
    (h0 : σ.lookup 0 = some (int n)) (h : clH.ResEx (cH H) σ r) : r = some (int (0 - n)) := by
  have hx := rmS_sortOf_int (cH H) n
  have hf := f_only (lookupFH H) hx
  have hg := g_only (subNotCtor H) (lookupGH H) n
  have hp : postVal (int (0 - n)) (some (int n)) (some (int (0 - n))) = true := by
    simp [postVal, sameResult_self]
  have ht := inst_true (funF H) (funG H) hf hg (ext_x h0 _) (lkSelf _ _ _) hp
  have hag : AgreeOff clH.exsFree σ ((1, int (0 - n)) :: σ) := agree_set1 σ _
  have hws := ext_sorted h0 hx (rmS_sortOf_int _ (0 - n))
  rcases h with ⟨σ₁, v, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩
  · exact ht.2 _ (hall _ hag hws)
  · exact absurd (ht.2 _ (hall _ hag hws)) (by simp)

end FnMany

/-! ### The facts the deciders name -/

def callOrder : List Nat := [FnMany.fF, FnMany.fG, FnMany.fH]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `h`'s. -/
theorem match_named : c.matchObligationsL = [(FnMany.fH, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### The owed fact refuted, `FnHyp` false, and consistency, for every H -/

section Stated

open GroundTerm OrFx FnMany KCore.Parse KCore.GenEqs KCore.Faithful.Model

/-- **Every function has at most one result, for every H**: f's, g's and h's one clause is
coherent with itself (h's by `resEx_h`: its result at a match is X's value), and a sort
predicate's clauses as in `Faithful.fnDet_of_agree`. -/
theorem fnDetH (H : HookParams) : FnDet (cH H) := by
  refine fnDet_of_coherent fun f fn hfn cl hcl cl' hcl' hprio => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · have hfns : (cH H).fns = [fnF, fnG, fnH] := read
    rw [hfns] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · simp only [fnF, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clF H
    · simp only [fnG, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clG H
    · simp only [fnH, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clH H
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

/-- **h's clause is not match independent, for every H**: it decides at `[1]` and has no result
there (a result would be 1, `resEx_h`, and `0 - 1`, `resEx_neg`). -/
theorem h_not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) clH := by
  intro hm
  have hx := rmS_sortOf_int (cH H) 1
  have hs : (cH H).WellSorted clH.vars [(1, int 1), (0, int 1)] := sorted2 rfl hx rfl hx
  have hdec : clH.Decides (cH H) fnH [(1, int 1), (0, int 1)] [int 1] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 (by decide) fH fnH [int 1] _ (lookupHH H) (List.mem_singleton_self _) hdec
  rcases hr with ⟨he, -⟩ | ⟨-, hr⟩
  · exact absurd he (by decide)
  have e1 := resEx_h H (σ := [(1, int 1), (0, int 1)]) rfl hx hr
  have e2 := resEx_neg H (σ := [(1, int 1), (0, int 1)]) rfl hr
  rw [e1] at e2
  have : (1 : Int) = 0 - 1 := by simpa [KCore.int] using e2
  omega

/-- **`FnHyp` is false, for every H**: its fourth conjunct is the match independence of `h`'s clause. -/
theorem not_fnHypH (H : HookParams) : ¬ FnHyp (cH H) := fun hf =>
  h_not_matchIndependent H (hf.2.2.2.1 fnH
    (by rw [show (cH H).fns = c.fns from rfl, read]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    clH (List.mem_singleton_self _))

/-- **Γc with the step's closure has a model, for every H** (`consistent_of_fnMany_agree` at h). -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of_rest H (fnDetH H) (solvesF H) (solvesG H) (postDecH H)

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

theorem nj108 : (trS U.ax108).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj113 : (trS U.ax113).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj116 : (trS U.ax116).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax108, U.ax113, U.ax116], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj108]; exact orTopBot_valid hD rfl
  · rw [nj113]; exact orTopBot_valid hD rfl
  · rw [nj116]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax109, U.ax110, U.ax111, U.ax112, U.ax114, U.ax115],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax109, U.ax110, U.ax111, U.ax112, U.ax114, U.ax115],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax117).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (117)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax117).pat := by
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
   U.ax16, U.ax17, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax98, U.ax99]

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


/-! ## Library sample: sentence 157, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax157).pat = (trAxiom [] [] U.ax157).pat := by decide +kernel
theorem s166_pattern : U.ax157.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax157.ax.sortVars.map sortVarKey ++ freeOf [] U.ax157.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax157.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 157 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax157).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax157.ax.sortVars U.ax157.ax.pattern = t at he ⊢
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
/-- **Sentence 157 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## Function equations (30 sentences) and priority equations (0 sentences)

Γ's item 2 (sentence 204, `cutOr`) is the equation read as a clause with existential variables
(`existentialClause`): Γ's right side binds the clause's variables under `\exists` with `\top`
beside the term, where the text writes its own right side, so the item is not the sentence
(`ex<j>_differs`). Both are `eqnPat` over one guard list, premise, sort and left side
(`ex<j>_text_shape`, `ex<j>_gamma_shape`, read off the sentence by KcoreSpec/TieExClause.lean's
parts), and the two right sides hold the same elements of the sort, by the lemma of
KcoreSpec/TieExClause.lean each item's comment names, so the two hold in the same interpretations
among those with the signature's facts (`ex<j>_iff`; `TieFRSig.SigFacts`: definedness, the item of
`⌈_⌉`, each numbered sort one sort): Γ entails the sentence (`ex<j>_entailed`) and the sentence with
definedness and `ΓSig` gives the item (`ex<j>_from_text`, W1), which `fns_from_text` leaves out.

Every other item is the translation of its function sentence (`shape`). -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

section

open KoreAML.TieFR KCore.TieExClause

/-- Γ's item 2 (sentence 204): an existential clause, `t ∨ u` against `∃z. z ∧ (⊤ ∧ (z ∈ t ∨ z ∈ u))` (`cutOr_body`). -/
noncomputable def exItem2 : P := (TiePair.gammaPats c).getD 2 ⊥
theorem exItem2_at : (TiePair.gammaPats c)[2]? = some exItem2 := by decide +kernel
kernel_rfl fnText_at2 : fnText[2]? = some U.ax204
/-- **Γ's item 2 is not the text's sentence 204** (kernel). -/
theorem ex2_differs : exItem2 ≠ (trS U.ax204).pat := by decide +kernel

noncomputable def ex2tbl : VarTable := tableOf U.ax204.ax.sortVars U.ax204.ax.pattern
noncomputable abbrev ex2ctx : Ctx := ⟨ex2tbl, kore.aliasNames⟩
noncomputable def ex2ws : List P := guardsOf U.ax204.ax
noncomputable def ex2r : EVar := ex2tbl.ev (sortVarKey Rv)
noncomputable def ex2prem : P := tr ex2ctx (premK U.ax204.ax.pattern)
noncomputable def ex2S : P := trSort ex2tbl (srt "Int")
noncomputable def ex2F : P := tr ex2ctx (lhsK U.ax204.ax.pattern)
noncomputable def ex2ens : P := tr ex2ctx (ensK U.ax204.ax.pattern)
noncomputable def ex2K : Kore.Pattern := rhsK U.ax204.ax.pattern
noncomputable def ex2z : EVar := ⟨4⟩
noncomputable def ex2t : P := tr ex2ctx (argK 0 ex2K)
noncomputable def ex2u : P := tr ex2ctx (argK 1 ex2K)

/-- The translated sentence 204 is `eqnPat` with the right side the text writes (kernel). -/
theorem ex2_text_shape : (trS U.ax204).pat = eqnPat ex2ws ex2r ex2prem ex2S ex2F (sAnd (sOr ex2S ex2t ex2u) ex2ens) := by
  decide +kernel

/-- Γ's item 2 is `eqnPat` over the same guards, premise, sort and left side, with the clause's right
side (kernel). -/
theorem ex2_gamma_shape : (TiePair.gammaPats c)[2]? = some (eqnPat ex2ws ex2r ex2prem ex2S ex2F (sAnd (sExists ex2z ex2S (sAnd (.evar ex2z) (sAnd (sTop ex2S) (sOr ex2S (sIn ex2S ex2S (.evar ex2z) ex2t) (sIn ex2S ex2S (.evar ex2z) ex2u))))) ex2ens)) := by
  decide +kernel

theorem ex2_guard_r : sortGuard ex2r ∈ ex2ws := by decide +kernel
theorem ex2_t_free : ex2t.isFreeEvar ex2z = false := by decide +kernel
theorem ex2_u_free : ex2u.isFreeEvar ex2z = false := by decide +kernel
theorem ex2_nameS (H : HookParams) : (cH H).sortName (3 : Srt) = "Int" :=
  (by decide +kernel : c.sortName (3 : Srt) = "Int")
theorem ex2_ltS (H : HookParams) : (3 : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (3 : Srt) < nRegSorts + c.sortNames.length)

/-- **Sentence 204 and Γ's item 2 hold in the same interpretations** among those with the
signature's facts (definedness, the item of `⌈_⌉`, each numbered sort one sort), for every H. -/
theorem ex2_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ex2ws ex2r ex2prem ex2S ex2F (sAnd (sExists ex2z ex2S (sAnd (.evar ex2z) (sAnd (sTop ex2S) (sOr ex2S (sIn ex2S ex2S (.evar ex2z) ex2t) (sIn ex2S ex2S (.evar ex2z) ex2u))))) ex2ens)) ↔ (I ⊧ᴵ (trS U.ax204).pat) := by
  rw [ex2_text_shape]
  obtain ⟨σ, hS⟩ := sortAtN F (ex2_nameS H) (ex2_ltS H) ex2tbl
  exact eqnPat_of_body F.defOK F.ceilDef hS ex2_guard_r (guardsOf_pred F.defOK U.ax204.ax) fun e m hat a ha =>
    cutOr_body F.defOK F.ceilDef hS ex2_t_free ex2_u_free ha

/-- **W1**: Γ's item 2 is a consequence of sentence 204 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex2_from_text (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[2]? = some it →
    (TiePair.Texts [(trS U.ax204).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex2_gamma_shape)
    (fun F _ => ex2_iff H F)).1

/-- **E**: Γ entails sentence 204, for every H. -/
theorem ex2_entailed (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax204).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex2_gamma_shape)
    (fun F _ => ex2_iff H F)).2

end

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 2. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 2 exItem2

/-- **Each of Γ's equations is the translation of its text sentence**, but the ones set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def pairSetAt : List Nat := [2]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ pairSetAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have h2 := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_map, hj]
  rfl

/-- **E for the function equations**: Γ entails each sentence of `fnText`, for every H; item 2 by `ex2_entailed`. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  by_cases h2 : j = 2
  · subst h2
    rw [fnText_at2] at hj
    rw [← Option.some.inj hj]
    exact ex2_entailed H
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))

/-- **The converse for `fnItems`**: each item but the existential clauses given with `ΓSig` (items 2) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it → j ∉ ([2] : List Nat) →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj hu
  by_cases h2 : j = 2
  · subst h2; simp at hu
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to
Γ's through their sentences, the existential clauses as Γ's own, which their sentences give with `ΓSig`), Γ's rule items and the five parts Γ defines by predicates
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
    ∀ ad ∈ [U.ax108, U.ax113, U.ax116], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax109, U.ax110, U.ax111, U.ax112, U.ax114, U.ax115],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax117).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 60 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax60).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE3MlEqRhsOr

#check @KCore.TieE3MlEqRhsOr.noRaw
#check @KCore.TieE3MlEqRhsOr.readsConfined_c
#check @KCore.TieE3MlEqRhsOr.userAxioms_eq
#check @KCore.TieE3MlEqRhsOr.coreOK
#check @KCore.TieE3MlEqRhsOr.account
#check @KCore.TieE3MlEqRhsOr.account_sizes
#check @KCore.TieE3MlEqRhsOr.account_classes
#check @KCore.TieE3MlEqRhsOr.account_absent
#check @KCore.TieE3MlEqRhsOr.absent_closed
#check @KCore.TieE3MlEqRhsOr.absent_proj_below_c
#check @KCore.TieE3MlEqRhsOr.absent_proj_below
#check @KCore.TieE3MlEqRhsOr.lists_in_account
#check @KCore.TieE3MlEqRhsOr.attrs_agree
#check @KCore.TieE3MlEqRhsOr.sig_origin_but_next
#check @KCore.TieE3MlEqRhsOr.decls_entailed
#check @KCore.TieE3MlEqRhsOr.consistent
#check @KCore.TieE3MlEqRhsOr.h_not_matchIndependent
#check @KCore.TieE3MlEqRhsOr.not_fnHypH
#check @KCore.TieE3MlEqRhsOr.text_nextless
#check @KCore.TieE3MlEqRhsOr.nojunk_trivial_entailed
#check @KCore.TieE3MlEqRhsOr.nojunk_items_entailed
#check @KCore.TieE3MlEqRhsOr.nojunk_kitem_entailed
#check @KCore.TieE3MlEqRhsOr.cons_entailed
#check @KCore.TieE3MlEqRhsOr.idem_refuted
#check @KCore.TieE3MlEqRhsOr.lib166
#check @KCore.TieE3MlEqRhsOr.lib166_at_values
#check @KCore.TieE3MlEqRhsOr.owed_rules
#check @KCore.TieE3MlEqRhsOr.owed_clauses
#check @KCore.TieE3MlEqRhsOr.openDecidedH
#check @KCore.TieE3MlEqRhsOr.gammaCl_eq
#check @KCore.TieE3MlEqRhsOr.decls_entailed_c
#check @KCore.TieE3MlEqRhsOr.nojunk_trivial_entailed_c
#check @KCore.TieE3MlEqRhsOr.nojunk_items_entailed_c
#check @KCore.TieE3MlEqRhsOr.nojunk_kitem_entailed_c
#check @KCore.TieE3MlEqRhsOr.cons_entailed_c
#check @KCore.TieE3MlEqRhsOr.idem_refuted_c
#print axioms KCore.TieE3MlEqRhsOr.noRaw
#print axioms KCore.TieE3MlEqRhsOr.readsConfined_c
#print axioms KCore.TieE3MlEqRhsOr.userAxioms_eq
#print axioms KCore.TieE3MlEqRhsOr.coreOK
#print axioms KCore.TieE3MlEqRhsOr.account
#print axioms KCore.TieE3MlEqRhsOr.account_sizes
#print axioms KCore.TieE3MlEqRhsOr.account_classes
#print axioms KCore.TieE3MlEqRhsOr.account_absent
#print axioms KCore.TieE3MlEqRhsOr.absent_closed
#print axioms KCore.TieE3MlEqRhsOr.absent_proj_below_c
#print axioms KCore.TieE3MlEqRhsOr.absent_proj_below
#print axioms KCore.TieE3MlEqRhsOr.lists_in_account
#print axioms KCore.TieE3MlEqRhsOr.attrs_agree
#print axioms KCore.TieE3MlEqRhsOr.sig_origin_but_next
#print axioms KCore.TieE3MlEqRhsOr.decls_entailed
#print axioms KCore.TieE3MlEqRhsOr.consistent
#print axioms KCore.TieE3MlEqRhsOr.h_not_matchIndependent
#print axioms KCore.TieE3MlEqRhsOr.not_fnHypH
#print axioms KCore.TieE3MlEqRhsOr.text_nextless
#print axioms KCore.TieE3MlEqRhsOr.nojunk_trivial_entailed
#print axioms KCore.TieE3MlEqRhsOr.nojunk_items_entailed
#print axioms KCore.TieE3MlEqRhsOr.nojunk_kitem_entailed
#print axioms KCore.TieE3MlEqRhsOr.cons_entailed
#print axioms KCore.TieE3MlEqRhsOr.idem_refuted
#print axioms KCore.TieE3MlEqRhsOr.lib166
#print axioms KCore.TieE3MlEqRhsOr.lib166_at_values
#print axioms KCore.TieE3MlEqRhsOr.owed_rules
#print axioms KCore.TieE3MlEqRhsOr.owed_clauses
#print axioms KCore.TieE3MlEqRhsOr.openDecidedH
#print axioms KCore.TieE3MlEqRhsOr.gammaCl_eq
#print axioms KCore.TieE3MlEqRhsOr.decls_entailed_c
#print axioms KCore.TieE3MlEqRhsOr.nojunk_trivial_entailed_c
#print axioms KCore.TieE3MlEqRhsOr.nojunk_items_entailed_c
#print axioms KCore.TieE3MlEqRhsOr.nojunk_kitem_entailed_c
#print axioms KCore.TieE3MlEqRhsOr.cons_entailed_c
#print axioms KCore.TieE3MlEqRhsOr.idem_refuted_c
#check @KCore.TieE3MlEqRhsOr.fns_account
#check @KCore.TieE3MlEqRhsOr.ex2_differs
#check @KCore.TieE3MlEqRhsOr.ex2_text_shape
#check @KCore.TieE3MlEqRhsOr.ex2_gamma_shape
#check @KCore.TieE3MlEqRhsOr.ex2_guard_r
#check @KCore.TieE3MlEqRhsOr.ex2_t_free
#check @KCore.TieE3MlEqRhsOr.ex2_u_free
#check @KCore.TieE3MlEqRhsOr.ex2_nameS
#check @KCore.TieE3MlEqRhsOr.ex2_ltS
#check @KCore.TieE3MlEqRhsOr.ex2_iff
#check @KCore.TieE3MlEqRhsOr.ex2_from_text
#check @KCore.TieE3MlEqRhsOr.ex2_entailed
#check @KCore.TieE3MlEqRhsOr.shape
#check @KCore.TieE3MlEqRhsOr.fns_entailed
#check @KCore.TieE3MlEqRhsOr.fns_from_text
#check @KCore.TieE3MlEqRhsOr.fn_prios
#check @KCore.TieE3MlEqRhsOr.gamma_from
#print axioms KCore.TieE3MlEqRhsOr.fns_account
#print axioms KCore.TieE3MlEqRhsOr.ex2_differs
#print axioms KCore.TieE3MlEqRhsOr.ex2_text_shape
#print axioms KCore.TieE3MlEqRhsOr.ex2_gamma_shape
#print axioms KCore.TieE3MlEqRhsOr.ex2_guard_r
#print axioms KCore.TieE3MlEqRhsOr.ex2_t_free
#print axioms KCore.TieE3MlEqRhsOr.ex2_u_free
#print axioms KCore.TieE3MlEqRhsOr.ex2_nameS
#print axioms KCore.TieE3MlEqRhsOr.ex2_ltS
#print axioms KCore.TieE3MlEqRhsOr.ex2_iff
#print axioms KCore.TieE3MlEqRhsOr.ex2_from_text
#print axioms KCore.TieE3MlEqRhsOr.ex2_entailed
#print axioms KCore.TieE3MlEqRhsOr.shape
#print axioms KCore.TieE3MlEqRhsOr.fns_entailed
#print axioms KCore.TieE3MlEqRhsOr.fns_from_text
#print axioms KCore.TieE3MlEqRhsOr.fn_prios
#print axioms KCore.TieE3MlEqRhsOr.gamma_from
