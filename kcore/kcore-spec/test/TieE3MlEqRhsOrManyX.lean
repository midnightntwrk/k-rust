/-
  The tie (C14) on `f2-examples/e3-ml-eq-rhs-or-many-x.kompile.kore`, the kompiled text of construct fixture e3-ml-eq-rhs-or-many-x
  (`test/constructs/fixtures/e3-ml-eq-rhs-or-many-x`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-eq-rhs-or-many-x`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlEqRhsOrManyX.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 252 sentences of the user module E3-ML-EQ-RHS-OR-MANY-X, in
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
    The consistency section, written by hand, proves what it owes for every H (`openDecidedH`),
    so `Γc` with the step's closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (28) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (235) is the equation read as a clause with existential
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
  - Library sample, 158 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence gives it with `ΓSig`: `ex<j>_from_text`), Γ's rule items, the five parts
    Γ defines by predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (4);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlEqRhsOrManyX

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-eq-rhs-or-many-x.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or-many-x.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-many-x.kompile.kore" module "E3-ML-EQ-RHS-OR-MANY-X"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-OR-MANY-X")

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

/-! ## Consistency for every H: `k(X) => X #Or X #Or … #Or X`, the instance at X's value gives the value -/

/- The one function `k`, declared `total`, has the one clause `CeOrX.clX`, read with the existential
variable #Or0 of Int (`exs [1]`, `rhs := #Or0`, `post` the nine memberships `#Or0 ∈ X`, nested as the
text nests the disjunctions): `Semantics.FnsNoExs` is false, so neither `consistent_of_fnFacts` nor
the step from `FnObligations` to `FnHyp` applies, and `FnHyp` is proved here for every H (`fnHypH`).
- A result at every argument, which is also k's totality: `k(x)` is x, by the instance #Or0 := x
  (`CeOrX.value`).
- Agreement: one clause (`CeOrX.agree_one`).
- Match independence of the clause `match_named` names (`matchK`): at a match giving X the value x
  the clause's one result is x (`CeOrX.res_eq`, `CeOrX.res_some`); every other instance has `post`
  false and gives nothing (`CeOrX.inst_all`).
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `OpenLaws`: the text has no open generator (`noRaw`).
So Γc with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).

`CeOrX` holds the proofs, over any semantics `d` that reads the clause; the statements after it are on
`cH H`. -/

namespace CeOrX

open GroundTerm KCore.Parse

/-! ### Facts shared by the texts of one clause with one existential variable -/

/-- What a semantics reads of its functions, parameters and rules does not depend on the hook
interpretation. -/
theorem fns_wh (d : Semantics) (H : HookParams) : (d.withHooks H).fns = d.fns := rfl
theorem params_wh (d : Semantics) (H : HookParams) : (d.withHooks H).params = d.params := rfl
theorem rules_wh (d : Semantics) (H : HookParams) : (d.withHooks H).rules = d.rules := rfl

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

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-- The predicate p has the truth value b under σ, and no other. -/
def DecX (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {n : Nat} {p q : Cond} {b b' : Bool} (hp : DecX d n σ p b) (hq : DecX d n σ q b') :
    DecX d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

/-! ### The reading of this text -/

def fK : Sym := 384

/-- The membership `#Or0 ∈ X` (the variable 1 in the variable 0). -/
def memX : Cond := .mem Srt.int (.var 1) (.var 0)

/-- `((#Or0 ∈ X ∨ #Or0 ∈ X) ∨ #Or0 ∈ X) ∨ … ∨ #Or0 ∈ X`, nine memberships nested as the text
nests the disjunctions. -/
def postX : Cond := [0, 0, 0, 0, 0, 0, 0, 0].foldl (fun p (_ : Nat) => .or p memX) memX

/-- `k(X) => #Or0` with `exs = [#Or0]` and `post := postX`, both variables of Int. -/
def clX : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postX }

def fnK : Fn := { label := fK, args := [Srt.int], result := Srt.int, clauses := [clX], total := true }

/-- **The reading**: the text's one function is `k`, `total`, with the one clause `clX`. -/
theorem read : c.fns = [fnK] := by kernel_rfl

theorem names : c.symName fK = "Lblk" ∧ c.sortName Srt.int = "Int" := by decide +kernel

/-- #Or0 is of the unconfined Int and fixed by X in every alternative: `clausePlainEx` admits the
clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx clX = true := by decide +kernel

theorem lookupK : c.lookupFn fK = some fnK := by rw [Semantics.lookupFn_eq]; rfl
theorem noRules : c.rules = [] := by decide +kernel

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics} {σ : Subst}

theorem dec_mem {n : Nat} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    DecX d n σ memX (sameResult (some w) (some x)) := by
  refine ⟨holds_cast (Holds.mem .var .var) (by rw [h0, h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := EvalTerm.var_inv h'
    rw [h0, h1]; rfl

theorem dec_fold {n : Nat} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    ∀ (ks : List Nat) (p : Cond), DecX d n σ p (sameResult (some w) (some x)) →
      DecX d n σ (ks.foldl (fun p (_ : Nat) => .or p memX) p) (sameResult (some w) (some x))
  | [], _, h => h
  | _ :: ks, _, h => dec_fold h0 h1 ks _ (by
      have := dec_or h (dec_mem (d := d) (n := n) h0 h1)
      rwa [Bool.or_self] at this)

/-- **The clause's `post`** at a match giving X the value x: whether #Or0 is x. -/
theorem dec_post {n : Nat} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    DecX d n σ postX (sameResult (some w) (some x)) :=
  dec_fold h0 h1 _ _ (dec_mem h0 h1)

/-- **Every instance is decided and gives x or nothing.** -/
theorem inst_all {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hw : d.WellSorted clX.vars σ) :
    InstIs d σ clX (some x) := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.int rfl
  cases hb : sameResult (some w) (some x) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (dec_post h0 hw1).1 hb)
  | false => exact .fails (dec_post h0 hw1).1 (.post (holds_cast (dec_post h0 hw1).1 hb))

/-- The instance at #Or0 := x does not give nothing. -/
theorem inst_not_none {x : GroundTerm} (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some x) :
    ¬ InstIs d σ clX none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := (dec_post (d := d) h0 h1).2 _ hp
      rw [sameResult_self] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e

theorem ext_sorted {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int) :
    d.WellSorted clX.vars ((1, x) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) hx

theorem agree_x {σ' : Subst} (h : AgreeOff clX.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

/-- **The clause has the one result x at a match giving X the value x.** -/
theorem res_eq {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Clause.Res d clX σ r) : r = some x := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, ha, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · have h0' := (agree_x ha).trans h0
    have h1 : σ'.lookup 1 = some v := (EvalTerm.var_inv hrhs).symm
    have e := (dec_post h0' h1).2 _ hpost
    rw [sameResult_some.mp e.symm]
  · exact absurd (hall _ (agree_set1 σ _) (ext_sorted h0 hx))
      (inst_not_none ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

theorem res_some {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int) :
    Clause.Res d clX σ (some x) :=
  have h0' : ((1, x) :: σ : Subst).lookup 0 = some x := (lkNe _ _ (by decide)).trans h0
  .inr ⟨by decide, .inl ⟨(1, x) :: σ, x, agree_set1 σ _, ext_sorted h0 hx,
    ⟨(lkSelf 1 x σ) ▸ .var, (fun t ht => nomatch ht),
      holds_cast (dec_post h0' (lkSelf _ _ _)).1 (sameResult_self _)⟩,
    fun σ'' ha hw => inst_all ((agree_x ha).trans h0) hw, rfl⟩⟩

/-- **`k(x)` is x**, by `Eval.clauseEx` at #Or0 := x. -/
theorem value (hfn : d.lookupFn fK = some fnK) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) :
    Eval d fK [x] (some x) :=
  have h0 : ([(1, x), (0, x)] : Subst).lookup 0 = some x := rfl
  .clauseEx (fn := fnK) (cl := clX) (σ := [(1, x), (0, x)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl hx rfl hx) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnK, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (dec_post h0 rfl).1 (sameResult_self _))
    (fun σ' ha hw => inst_all ((agree_x ha).trans h0) hw)

/-- **`k(x)` has no other result.** -/
theorem alone (hfn : d.lookupFn fK = some fnK) {x : GroundTerm} (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Eval d fK [x] r) : r = some x := by
  have hcl : ∀ {cl fn'}, d.lookupFn fK = some fn' → cl ∈ fn'.clauses → cl = clX := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnK] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clX.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clX (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clX.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have h1 := (EvalTerm.var_inv hrhs).symm
    have e := (dec_post (hx0 hmatch) h1).2 _ hpost
    rw [sameResult_some.mp e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx0 hmatch
    exact absurd (hall _ (agree_set1 σ _) (ext_sorted h0 hx))
      (inst_not_none ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-- The value a match of the clause gives X is a value of Int. -/
theorem applies_x {vs : List GroundTerm} (h : clX.AppliesAt d σ vs) :
    ∃ x, σ.lookup 0 = some x ∧ d.sortOf x = some Srt.int :=
  h.1 0 (by decide) Srt.int rfl

/-- **`FnHyp`** of a semantics whose one function is `k` with the clause `clX`, without rules and
open generators. -/
theorem fnHyp_of (hfns : d.fns = [fnK]) (hfn : d.lookupFn fK = some fnK)
    (hrules : d.rules = []) (hraw : ∀ k ∈ d.params, k.raw = false) : FnHyp d := by
  have hmem : ∀ {fn}, fn ∈ d.fns → fn = fnK := fun h => by rw [hfns] at h; simpa using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf _ vs hvs => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecided_of_plain (fun r hr => by rw [hrules] at hr; cases hr) (fun fn hf cl hcl => ?_),
    openLaws_of_plain hraw⟩
  · obtain rfl := hmem hf
    obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
    exact ⟨_, value hfn hw⟩
  · obtain rfl := hmem hf
    obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
    exact ⟨_, value hfn hw⟩
  · obtain rfl := hmem hf; exact agree_one rfl
  · obtain rfl := hmem hf
    obtain rfl : cl = clX := by simpa [fnK] using hcl
    refine ⟨fun vs σ σ' ha ha' _ _ _ _ _ => .inr fun r r' hr hr' => ?_, fun _ _ _ _ σ _ _ hdec => ?_⟩
    · obtain ⟨x, hx0, hx⟩ := applies_x ha
      obtain ⟨x', hx0', hx'⟩ := applies_x ha'
      obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv ha.2.1
      obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv ha'.2.1
      cases hvs
      have e : x = x' := Option.some.inj
        (hx0.symm.trans ((PatVal.var_inv hv).trans ((PatVal.var_inv hv').symm.trans hx0')))
      subst e
      rw [res_eq hx0 hx hr, res_eq hx0' hx' hr']
    · obtain ⟨x, hx0, hx⟩ := applies_x hdec.1
      exact ⟨_, res_some hx0 hx⟩
  · obtain rfl := hmem hf
    obtain rfl : cl = clX := by simpa [fnK] using hcl
    rfl

end Clause

end CeOrX

/-! ### The facts the deciders name -/

def callOrder : List Nat := [CeOrX.fK]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `k`'s. -/
theorem match_named : c.matchObligationsL = [(CeOrX.fK, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### `FnHyp` and consistency, for every H -/

theorem lookupKH (H : HookParams) : (cH H).lookupFn CeOrX.fK = some CeOrX.fnK := by
  rw [Semantics.lookupFn_withHooks]; exact CeOrX.lookupK

/-- **`FnHyp` holds, for every H.** -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  CeOrX.fnHyp_of ((CeOrX.fns_wh c H).trans CeOrX.read) (lookupKH H)
    ((CeOrX.rules_wh c H).trans CeOrX.noRules) (fun k hk => noRaw k ((CeOrX.params_wh c H) ▸ hk))

/-- **The clause `match_named` names is match independent, for every H.** -/
theorem matchK (H : HookParams) : MatchIndependent (cH H) CeOrX.clX :=
  (fnHypH H).2.2.2.1 CeOrX.fnK (by rw [(CeOrX.fns_wh c H).trans CeOrX.read]; exact List.mem_singleton_self _)
    CeOrX.clX (List.mem_singleton_self _)

/-- **`k(n) = n` and no other result, for every H.** -/
theorem k_value (H : HookParams) (n : Int) : Eval (cH H) CeOrX.fK [KCore.int n] (some (KCore.int n)) :=
  CeOrX.value (lookupKH H) (rmS_sortOf_int _ n)
theorem k_alone (H : HookParams) {n : Int} {r : Option GroundTerm} (h : Eval (cH H) CeOrX.fK [KCore.int n] r) :
    r = some (KCore.int n) :=
  CeOrX.alone (lookupKH H) (rmS_sortOf_int _ n) h

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

Γ's item 0 (sentence 235, `orMany`) is the equation read as a clause with existential variables
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

/-- Γ's item 0 (sentence 235): an existential clause, `t₁ ∨ … ∨ tₖ` against `∃z. z ∧ (⊤ ∧ (z ∈ t₁ ∨ … ∨ z ∈ tₖ))` (`cutOf_body, cutOf_or, cutOf_mem`). -/
noncomputable def exItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem exItem0_at : (TiePair.gammaPats c)[0]? = some exItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax235
/-- **Γ's item 0 is not the text's sentence 235** (kernel). -/
theorem ex0_differs : exItem0 ≠ (trS U.ax235).pat := by decide +kernel

noncomputable def ex0tbl : VarTable := tableOf U.ax235.ax.sortVars U.ax235.ax.pattern
noncomputable abbrev ex0ctx : Ctx := ⟨ex0tbl, kore.aliasNames⟩
noncomputable def ex0ws : List P := guardsOf U.ax235.ax
noncomputable def ex0r : EVar := ex0tbl.ev (sortVarKey Rv)
noncomputable def ex0prem : P := tr ex0ctx (premK U.ax235.ax.pattern)
noncomputable def ex0S : P := trSort ex0tbl (srt "Int")
noncomputable def ex0F : P := tr ex0ctx (lhsK U.ax235.ax.pattern)
noncomputable def ex0ens : P := tr ex0ctx (ensK U.ax235.ax.pattern)
noncomputable def ex0K : Kore.Pattern := rhsK U.ax235.ax.pattern
noncomputable def ex0z : EVar := ⟨4⟩
noncomputable def ex0t1_ : P := tr ex0ctx (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 ex0K))))))))
noncomputable def ex0t2_ : P := tr ex0ctx (argK 1 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 ex0K))))))))
noncomputable def ex0t3_ : P := tr ex0ctx (argK 1 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 ex0K)))))))
noncomputable def ex0t4_ : P := tr ex0ctx (argK 1 (argK 0 (argK 0 (argK 0 (argK 0 (argK 0 ex0K))))))
noncomputable def ex0t5_ : P := tr ex0ctx (argK 1 (argK 0 (argK 0 (argK 0 (argK 0 ex0K)))))
noncomputable def ex0t6_ : P := tr ex0ctx (argK 1 (argK 0 (argK 0 (argK 0 ex0K))))
noncomputable def ex0t7_ : P := tr ex0ctx (argK 1 (argK 0 (argK 0 ex0K)))
noncomputable def ex0t8_ : P := tr ex0ctx (argK 1 (argK 0 ex0K))
noncomputable def ex0t9_ : P := tr ex0ctx (argK 1 ex0K)

/-- The translated sentence 235 is `eqnPat` with the right side the text writes (kernel). -/
theorem ex0_text_shape : (trS U.ax235).pat = eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (ex0t1_) ex0t2_) ex0t3_) ex0t4_) ex0t5_) ex0t6_) ex0t7_) ex0t8_) ex0t9_) ex0ens) := by
  decide +kernel

/-- Γ's item 0 is `eqnPat` over the same guards, premise, sort and left side, with the clause's right
side (kernel). -/
theorem ex0_gamma_shape : (TiePair.gammaPats c)[0]? = some (eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0z ex0S (sAnd (.evar ex0z) (sAnd (sTop ex0S) (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sIn ex0S ex0S (.evar ex0z) ex0t1_) (sIn ex0S ex0S (.evar ex0z) ex0t2_)) (sIn ex0S ex0S (.evar ex0z) ex0t3_)) (sIn ex0S ex0S (.evar ex0z) ex0t4_)) (sIn ex0S ex0S (.evar ex0z) ex0t5_)) (sIn ex0S ex0S (.evar ex0z) ex0t6_)) (sIn ex0S ex0S (.evar ex0z) ex0t7_)) (sIn ex0S ex0S (.evar ex0z) ex0t8_)) (sIn ex0S ex0S (.evar ex0z) ex0t9_))))) ex0ens)) := by
  decide +kernel

theorem ex0_guard_r : sortGuard ex0r ∈ ex0ws := by decide +kernel
theorem ex0_t1_free : ex0t1_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t2_free : ex0t2_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t3_free : ex0t3_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t4_free : ex0t4_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t5_free : ex0t5_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t6_free : ex0t6_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t7_free : ex0t7_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t8_free : ex0t8_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_t9_free : ex0t9_.isFreeEvar ex0z = false := by decide +kernel
theorem ex0_nameS (H : HookParams) : (cH H).sortName (3 : Srt) = "Int" :=
  (by decide +kernel : c.sortName (3 : Srt) = "Int")
theorem ex0_ltS (H : HookParams) : (3 : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (3 : Srt) < nRegSorts + c.sortNames.length)

/-- **Sentence 235 and Γ's item 0 hold in the same interpretations** among those with the
signature's facts (definedness, the item of `⌈_⌉`, each numbered sort one sort), for every H. -/
theorem ex0_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0z ex0S (sAnd (.evar ex0z) (sAnd (sTop ex0S) (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sOr ex0S (sIn ex0S ex0S (.evar ex0z) ex0t1_) (sIn ex0S ex0S (.evar ex0z) ex0t2_)) (sIn ex0S ex0S (.evar ex0z) ex0t3_)) (sIn ex0S ex0S (.evar ex0z) ex0t4_)) (sIn ex0S ex0S (.evar ex0z) ex0t5_)) (sIn ex0S ex0S (.evar ex0z) ex0t6_)) (sIn ex0S ex0S (.evar ex0z) ex0t7_)) (sIn ex0S ex0S (.evar ex0z) ex0t8_)) (sIn ex0S ex0S (.evar ex0z) ex0t9_))))) ex0ens)) ↔ (I ⊧ᴵ (trS U.ax235).pat) := by
  rw [ex0_text_shape]
  obtain ⟨σ, hS⟩ := sortAtN F (ex0_nameS H) (ex0_ltS H) ex0tbl
  exact eqnPat_of_body F.defOK F.ceilDef hS ex0_guard_r (guardsOf_pred F.defOK U.ax235.ax) fun e m hat a ha =>
    cutOf_body F.defOK hS
      (cutOf_or hS (cutOf_or hS (cutOf_or hS (cutOf_or hS (cutOf_or hS (cutOf_or hS (cutOf_or hS (cutOf_or hS (cutOf_mem F.defOK F.ceilDef hS ex0_t1_free)
      (cutOf_mem F.defOK F.ceilDef hS ex0_t2_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t3_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t4_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t5_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t6_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t7_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t8_free))
      (cutOf_mem F.defOK F.ceilDef hS ex0_t9_free)) ha

/-- **W1**: Γ's item 0 is a consequence of sentence 235 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex0_from_text (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax235).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex0_gamma_shape)
    (fun F _ => ex0_iff H F)).1

/-- **E**: Γ entails sentence 235, for every H. -/
theorem ex0_entailed (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax235).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex0_gamma_shape)
    (fun F _ => ex0_iff H F)).2

end

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 0. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 exItem0

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

/-- **E for the function equations**: Γ entails each sentence of `fnText`, for every H; item 0 by `ex0_entailed`. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  by_cases h0 : j = 0
  · subst h0
    rw [fnText_at0] at hj
    rw [← Option.some.inj hj]
    exact ex0_entailed H
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))

/-- **The converse for `fnItems`**: each item but the existential clauses given with `ΓSig` (items 0) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
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

end KCore.TieE3MlEqRhsOrManyX

#check @KCore.TieE3MlEqRhsOrManyX.noRaw
#check @KCore.TieE3MlEqRhsOrManyX.readsConfined_c
#check @KCore.TieE3MlEqRhsOrManyX.userAxioms_eq
#check @KCore.TieE3MlEqRhsOrManyX.coreOK
#check @KCore.TieE3MlEqRhsOrManyX.account
#check @KCore.TieE3MlEqRhsOrManyX.account_sizes
#check @KCore.TieE3MlEqRhsOrManyX.account_classes
#check @KCore.TieE3MlEqRhsOrManyX.account_absent
#check @KCore.TieE3MlEqRhsOrManyX.absent_closed
#check @KCore.TieE3MlEqRhsOrManyX.absent_proj_below_c
#check @KCore.TieE3MlEqRhsOrManyX.absent_proj_below
#check @KCore.TieE3MlEqRhsOrManyX.lists_in_account
#check @KCore.TieE3MlEqRhsOrManyX.attrs_agree
#check @KCore.TieE3MlEqRhsOrManyX.sig_origin_but_next
#check @KCore.TieE3MlEqRhsOrManyX.decls_entailed
#check @KCore.TieE3MlEqRhsOrManyX.consistent
#check @KCore.TieE3MlEqRhsOrManyX.text_nextless
#check @KCore.TieE3MlEqRhsOrManyX.nojunk_trivial_entailed
#check @KCore.TieE3MlEqRhsOrManyX.nojunk_items_entailed
#check @KCore.TieE3MlEqRhsOrManyX.nojunk_kitem_entailed
#check @KCore.TieE3MlEqRhsOrManyX.cons_entailed
#check @KCore.TieE3MlEqRhsOrManyX.idem_refuted
#check @KCore.TieE3MlEqRhsOrManyX.lib166
#check @KCore.TieE3MlEqRhsOrManyX.lib166_at_values
#check @KCore.TieE3MlEqRhsOrManyX.owed_rules
#check @KCore.TieE3MlEqRhsOrManyX.owed_clauses
#check @KCore.TieE3MlEqRhsOrManyX.openDecidedH
#check @KCore.TieE3MlEqRhsOrManyX.gammaCl_eq
#check @KCore.TieE3MlEqRhsOrManyX.decls_entailed_c
#check @KCore.TieE3MlEqRhsOrManyX.nojunk_trivial_entailed_c
#check @KCore.TieE3MlEqRhsOrManyX.nojunk_items_entailed_c
#check @KCore.TieE3MlEqRhsOrManyX.nojunk_kitem_entailed_c
#check @KCore.TieE3MlEqRhsOrManyX.cons_entailed_c
#check @KCore.TieE3MlEqRhsOrManyX.idem_refuted_c
#print axioms KCore.TieE3MlEqRhsOrManyX.noRaw
#print axioms KCore.TieE3MlEqRhsOrManyX.readsConfined_c
#print axioms KCore.TieE3MlEqRhsOrManyX.userAxioms_eq
#print axioms KCore.TieE3MlEqRhsOrManyX.coreOK
#print axioms KCore.TieE3MlEqRhsOrManyX.account
#print axioms KCore.TieE3MlEqRhsOrManyX.account_sizes
#print axioms KCore.TieE3MlEqRhsOrManyX.account_classes
#print axioms KCore.TieE3MlEqRhsOrManyX.account_absent
#print axioms KCore.TieE3MlEqRhsOrManyX.absent_closed
#print axioms KCore.TieE3MlEqRhsOrManyX.absent_proj_below_c
#print axioms KCore.TieE3MlEqRhsOrManyX.absent_proj_below
#print axioms KCore.TieE3MlEqRhsOrManyX.lists_in_account
#print axioms KCore.TieE3MlEqRhsOrManyX.attrs_agree
#print axioms KCore.TieE3MlEqRhsOrManyX.sig_origin_but_next
#print axioms KCore.TieE3MlEqRhsOrManyX.decls_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.consistent
#print axioms KCore.TieE3MlEqRhsOrManyX.text_nextless
#print axioms KCore.TieE3MlEqRhsOrManyX.nojunk_trivial_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.nojunk_items_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.nojunk_kitem_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.cons_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.idem_refuted
#print axioms KCore.TieE3MlEqRhsOrManyX.lib166
#print axioms KCore.TieE3MlEqRhsOrManyX.lib166_at_values
#print axioms KCore.TieE3MlEqRhsOrManyX.owed_rules
#print axioms KCore.TieE3MlEqRhsOrManyX.owed_clauses
#print axioms KCore.TieE3MlEqRhsOrManyX.openDecidedH
#print axioms KCore.TieE3MlEqRhsOrManyX.gammaCl_eq
#print axioms KCore.TieE3MlEqRhsOrManyX.decls_entailed_c
#print axioms KCore.TieE3MlEqRhsOrManyX.nojunk_trivial_entailed_c
#print axioms KCore.TieE3MlEqRhsOrManyX.nojunk_items_entailed_c
#print axioms KCore.TieE3MlEqRhsOrManyX.nojunk_kitem_entailed_c
#print axioms KCore.TieE3MlEqRhsOrManyX.cons_entailed_c
#print axioms KCore.TieE3MlEqRhsOrManyX.idem_refuted_c
#check @KCore.TieE3MlEqRhsOrManyX.fns_account
#check @KCore.TieE3MlEqRhsOrManyX.ex0_differs
#check @KCore.TieE3MlEqRhsOrManyX.ex0_text_shape
#check @KCore.TieE3MlEqRhsOrManyX.ex0_gamma_shape
#check @KCore.TieE3MlEqRhsOrManyX.ex0_guard_r
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t1_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t2_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t3_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t4_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t5_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t6_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t7_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t8_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_t9_free
#check @KCore.TieE3MlEqRhsOrManyX.ex0_nameS
#check @KCore.TieE3MlEqRhsOrManyX.ex0_ltS
#check @KCore.TieE3MlEqRhsOrManyX.ex0_iff
#check @KCore.TieE3MlEqRhsOrManyX.ex0_from_text
#check @KCore.TieE3MlEqRhsOrManyX.ex0_entailed
#check @KCore.TieE3MlEqRhsOrManyX.shape
#check @KCore.TieE3MlEqRhsOrManyX.fns_entailed
#check @KCore.TieE3MlEqRhsOrManyX.fns_from_text
#check @KCore.TieE3MlEqRhsOrManyX.fn_prios
#check @KCore.TieE3MlEqRhsOrManyX.gamma_from
#print axioms KCore.TieE3MlEqRhsOrManyX.fns_account
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_differs
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_text_shape
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_gamma_shape
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_guard_r
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t1_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t2_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t3_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t4_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t5_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t6_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t7_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t8_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_t9_free
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_nameS
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_ltS
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_iff
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_from_text
#print axioms KCore.TieE3MlEqRhsOrManyX.ex0_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.shape
#print axioms KCore.TieE3MlEqRhsOrManyX.fns_entailed
#print axioms KCore.TieE3MlEqRhsOrManyX.fns_from_text
#print axioms KCore.TieE3MlEqRhsOrManyX.fn_prios
#print axioms KCore.TieE3MlEqRhsOrManyX.gamma_from
