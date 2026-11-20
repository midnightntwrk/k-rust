/-
  The tie (C14) on `f2-examples/e3-eq-exists-twice-ml.kompile.kore`, the kompiled text of construct fixture e3-eq-exists-twice-ml
  (`test/constructs/fixtures/e3-eq-exists-twice-ml`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-eq-exists-twice-ml`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3EqExistsTwiceMl.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 176 sentences of the user module E3-EQ-EXISTS-TWICE-ML, in
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
    entails it (`fns_entailed`). Item 0 (164) is the equation read as a clause with existential
    variables (`existentialClause`), not its sentence (`ex<j>_differs`): the two hold in the same
    interpretations with the signature's facts (`ex<j>_iff`, by a lemma of
    KcoreSpec/TieExClause.lean), so Γ entails the sentence (`ex<j>_entailed`) and the sentence with
    `ΓSig` gives the item (`ex<j>_from_text`, W1), which `fns_from_text` leaves out. `fns_from_text`
    (the converse), `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (48): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence gives it with `ΓSig`: `ex<j>_from_text`), Γ's rule items, the five parts
    Γ defines by predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (23);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsTwiceMl

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-twice-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-twice-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-twice-ml.kompile.kore" module "E3-EQ-EXISTS-TWICE-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-EQ-EXISTS-TWICE-ML")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 176 := by decide +kernel

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
  [("function equation", [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152,
      153, 154, 155, 156, 157, 158, 159, 160, 161, 164]),
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
      124, 125, 126, 127, 128, 129, 130, 162, 163, 178]),
   ("set idempotence", [48]),
   ("set-variable lemma", [98, 99, 100, 101, 102, 103, 104, 105, 179]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 36, 62, 87, 131, 132, 133, 134, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
      176, 177])]

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
    [("function equation", 28), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 32), ("collection law", 9), ("library", 28), ("set idempotence", 1), ("set-variable lemma", 9), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 21)] := by
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
  [(165, "Bool"), (166, "GeneratedCounterCell"), (167, "GeneratedCounterCellOpt"),
   (168, "GeneratedTopCell"), (169, "GeneratedTopCellFragment"), (170, "Int"), (171, "K"),
   (172, "KCell"), (173, "KCellOpt"), (174, "KItem"), (175, "List"), (176, "Map"), (177, "Set")]

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
   (128, "library"), (134, "no direction"), (164, "function equation"),
   (179, "set-variable lemma")]

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

/-! ## Consistency for every H: `p(X) => #Exists B. #Exists B. (B #And {B #Equals notBool X})`, one instance gives the value -/

/- The one function `p` has the one clause `clF`, read with the existential variable B (`exs [1]`,
`post := B = notBool X`): of the two binders of B the inner one alone, the outer one binding no
occurrence (`existsBindsNothing`). `Semantics.FnsNoExs` is false, so neither `consistent_of_fnFacts` nor the
step from `FnObligations` to `FnHyp` applies, and `FnHyp` is proved here for every H (`fnHypH`).
- A result at every argument: `p(b)` is `notBool b`, by the instance B := `notBool b` (`CeEx.value`).
- Agreement: one clause (`CeEx.agree_one`).
- Match independence of the clause `match_named` names (`matchF`): at a match giving X the value b
  the clause's one result is `notBool b` (`CeEx.res_eq`, `CeEx.res_some`); the instance at the other
  value of Bool has `post` false and gives nothing (`CeEx.inst_all`).
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `OpenLaws`: the text has no open generator (`noRaw`).
So Γc with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).

`CeEx` holds the proofs, over any semantics `d` that reads the clause; the statements after it are on
`cH H`. -/

namespace CeEx

open GroundTerm KCore.Parse

/-! ### Facts shared by the texts of one clause with one existential variable -/

/-- What a semantics reads of its symbols and sorts does not depend on the hook interpretation. -/
theorem isCtor_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isCtor f = d.isCtor f := rfl
theorem shapesOK_wh (d : Semantics) (H : HookParams) : (d.withHooks H).shapesOK = d.shapesOK := rfl
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

theorem sameResult_eq_some {r : Option GroundTerm} {v : GroundTerm} (h : sameResult r (some v) = true) :
    r = some v := by
  cases r with
  | none => cases h
  | some w => rw [sameResult_some.mp h]

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

/-- The results of two terms. -/
theorem terms2_inv {t u : Term} {rs : List (Option GroundTerm)} (h : EvalTerms d σ [t, u] rs) :
    ∃ r r', rs = [r, r'] ∧ EvalTerm d σ t r ∧ EvalTerm d σ u r' := by
  obtain ⟨r, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv h
  obtain ⟨r', rs'', rfl, h2, hs'⟩ := EvalTerms.cons_inv hs
  obtain rfl := EvalTerms.nil_inv hs'
  exact ⟨r, r', rfl, h1, h2⟩

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-! ### The reading of this text -/

def fF : Sym := 384

/-- `p(X) => B` with `exs = [B]` and `post := B = notBool X`, X and B of Bool. -/
def clF : Clause :=
  { vars := [Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.bool (.var 1) (.app boolNot [.var 0]) }

def fnF : Fn := { label := fF, args := [Srt.bool], result := Srt.bool, clauses := [clF] }

/-- **The reading**: the text's one function is `p`, with the one clause `clF`. -/
theorem read : c.fns = [fnF] := by kernel_rfl

theorem names : c.symName fF = "Lblp" ∧ c.symName boolNot = "LblnotBool'Unds'" ∧
    c.sortName Srt.bool = "Bool" := by decide +kernel

/-- B is of the confined sort Bool: the clause is one `clausePlainEx` admits. -/
theorem plainEx : c.confined Srt.bool = true ∧ c.clausePlainEx clF = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel
theorem noRules : c.rules = [] := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics} {σ : Subst}

theorem notHook : isHook boolNot = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation (domains.md 1138, 1139). -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

theorem evalNot (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    EvalTerm d σ (.app boolNot [.var 0]) (some (bool (!b))) :=
  .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalNot_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : EvalTerm d σ (.app boolNot [.var 0]) r) : r = some (bool (!b)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  have := hh [bool b] (by rw [h0]; rfl)
  rw [hookNot] at this
  exact (Option.some.inj this).symm

/-- The clause's `post` at a match giving X the value b: whether B's value is `notBool b`. -/
theorem post_holds (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    Holds d 2 σ clF.post (sameResult (σ.lookup 1) (some (bool (!b)))) :=
  Holds.equals .var (evalNot hc h0)

theorem post_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) {t : Bool}
    (h : Holds d 2 σ clF.post t) : t = sameResult (σ.lookup 1) (some (bool (!b))) := by
  cases h with
  | equals h1 h2 =>
    obtain rfl := EvalTerm.var_inv h1
    obtain rfl := evalNot_inv hc h0 h2
    rfl

/-- **Every instance is decided and gives `notBool b` or nothing**: at B := `notBool b` it gives
it, at the other value of Bool its `post` is false. -/
theorem inst_all (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (hw : d.WellSorted clF.vars σ) : InstIs d σ clF (some (bool (!b))) := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.bool rfl
  cases hb : sameResult (some w) (some (bool (!b))) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds hc h0) (by rw [hw1, hb]))
  | false => exact .fails (post_holds hc h0) (.post (holds_cast (post_holds hc h0) (by rw [hw1, hb])))

/-- The instance at B := `notBool b` does not give nothing. -/
theorem inst_not_none (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (h1 : σ.lookup 1 = some (bool (!b))) : ¬ InstIs d σ clF none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := post_inv hc h0 hp
      rw [h1, sameResult_self] at e
      cases e
    | rhs h => have := EvalTerm.var_inv h; rw [h1] at this; cases this

/-- σ with B := `notBool b` is an instance of the clause at σ, well sorted where σ gives X the
value b. -/
theorem ext_sorted {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    d.WellSorted clF.vars ((1, bool (!b)) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (rmS_sortOf_bool d b) (lkSelf _ _ _) (rmS_sortOf_bool d (!b))

theorem ext_agree (σ : Subst) (w : GroundTerm) : AgreeOff clF.exsFree σ ((1, w) :: σ) := agree_set1 σ w

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff clF.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- **The clause has the one result `notBool b` at a match giving X the value b.** -/
theorem res_eq (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : Clause.Res d clF σ r) : r = some (bool (!b)) := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, ha, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · have h0' := (agree_x ha).trans h0
    have e := post_inv hc h0' hpost
    rw [← EvalTerm.var_inv hrhs] at e
    rw [sameResult_some.mp e.symm]
  · exact absurd (hall _ (ext_agree σ _) (ext_sorted h0))
      (inst_not_none hc ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

theorem res_some (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    Clause.Res d clF σ (some (bool (!b))) :=
  have h0' : ((1, bool (!b)) :: σ : Subst).lookup 0 = some (bool b) := (lkNe _ _ (by decide)).trans h0
  .inr ⟨by decide, .inl ⟨(1, bool (!b)) :: σ, bool (!b), ext_agree σ _, ext_sorted h0,
    ⟨(lkSelf 1 (bool (!b)) σ) ▸ .var, (fun t ht => nomatch ht),
      holds_cast (post_holds hc h0') (by rw [lkSelf, sameResult_self])⟩,
    fun σ'' ha hw => inst_all hc ((agree_x ha).trans h0) hw, rfl⟩⟩

/-- **`p(b)` is `notBool b`**, by `Eval.clauseEx` at B := `notBool b`. -/
theorem value (hc : d.isCtor boolNot = false) (hfn : d.lookupFn fF = some fnF) (b : Bool) :
    Eval d fF [bool b] (some (bool (!b))) :=
  have h0 : ([(1, bool (!b)), (0, bool b)] : Subst).lookup 0 = some (bool b) := rfl
  .clauseEx (fn := fnF) (cl := clF) (σ := [(1, bool (!b)), (0, bool b)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d (!b))) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (post_holds hc h0) (sameResult_self _))
    (fun σ' ha hw => inst_all hc ((agree_x ha).trans h0) hw)

/-- **`p(b)` has no other result.** -/
theorem alone (hc : d.isCtor boolNot = false) (hfn : d.lookupFn fF = some fnF) {b : Bool}
    {r : Option GroundTerm} (h : Eval d fF [bool b] r) : r = some (bool (!b)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnF] using h2
  have hx : ∀ {σ : Subst}, PatVals d σ clF.pats [bool b] → σ.lookup 0 = some (bool b) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clF.vars [(1, bool b), (0, bool b)] :=
        sorted2 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d b)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have e := post_inv hc (hx hmatch) hpost
    rw [← EvalTerm.var_inv hrhs] at e
    rw [sameResult_some.mp e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx hmatch
    exact absurd (hall _ (ext_agree σ _) (ext_sorted h0))
      (inst_not_none hc ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-- The value a match of the clause gives X is a value of Bool, in a semantics where the values of
Bool are its literals. -/
theorem applies_x (hs : d.shapesOK = true) {vs : List GroundTerm} (h : clF.AppliesAt d σ vs) :
    ∃ b, σ.lookup 0 = some (bool b) := by
  obtain ⟨w, hw, hws⟩ := h.1 0 (by decide) Srt.bool rfl
  obtain ⟨b, rfl⟩ := shape_bool hs hws
  exact ⟨b, hw⟩

/-- **`FnHyp`** of a semantics whose one function is `p` with the clause `clF`, without rules and
open generators, where the values of Bool are its literals. -/
theorem fnHyp_of (hc : d.isCtor boolNot = false) (hfns : d.fns = [fnF]) (hfn : d.lookupFn fF = some fnF)
    (hs : d.shapesOK = true) (hrules : d.rules = []) (hraw : ∀ k ∈ d.params, k.raw = false) : FnHyp d := by
  have hmem : ∀ {fn}, fn ∈ d.fns → fn = fnF := fun h => by rw [hfns] at h; simpa using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf ht => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecided_of_plain (fun r hr => by rw [hrules] at hr; cases hr) (fun fn hf cl hcl => ?_),
    openLaws_of_plain hraw⟩
  · obtain rfl := hmem hf
    obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
    obtain ⟨b, rfl⟩ := shape_bool hs hw
    exact ⟨_, value hc hfn b⟩
  · obtain rfl := hmem hf; cases ht
  · obtain rfl := hmem hf; exact agree_one rfl
  · obtain rfl := hmem hf
    obtain rfl : cl = clF := by simpa [fnF] using hcl
    refine ⟨fun vs σ σ' ha ha' _ _ _ _ _ => .inr fun r r' hr hr' => ?_, fun _ _ _ _ σ _ _ hdec => ?_⟩
    · obtain ⟨b, hb⟩ := applies_x hs ha
      obtain ⟨b', hb'⟩ := applies_x hs ha'
      obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv ha.2.1
      obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv ha'.2.1
      cases hvs
      have e : bool b = bool b' := Option.some.inj
        (hb.symm.trans ((PatVal.var_inv hv).trans ((PatVal.var_inv hv').symm.trans hb')))
      obtain rfl : b = b' := by simpa [KCore.bool] using e
      rw [res_eq hc hb hr, res_eq hc hb' hr']
    · obtain ⟨b, hb⟩ := applies_x hs hdec.1
      exact ⟨_, res_some hc hb⟩
  · obtain rfl := hmem hf
    obtain rfl : cl = clF := by simpa [fnF] using hcl
    rfl

end Clause

end CeEx

/-! ### The facts the deciders name -/

def callOrder : List Nat := [CeEx.fF]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `p`'s. -/
theorem match_named : c.matchObligationsL = [(CeEx.fF, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### `FnHyp` and consistency, for every H -/

theorem notCtorH (H : HookParams) : (cH H).isCtor boolNot = false := (CeEx.isCtor_wh c H _).trans CeEx.notCtor
theorem lookupFH (H : HookParams) : (cH H).lookupFn CeEx.fF = some CeEx.fnF := by
  rw [Semantics.lookupFn_withHooks]; exact CeEx.lookupF

/-- **`FnHyp` holds, for every H.** -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  CeEx.fnHyp_of (notCtorH H) ((CeEx.fns_wh c H).trans CeEx.read) (lookupFH H) ((CeEx.shapesOK_wh c H).trans CeEx.shapes)
    ((CeEx.rules_wh c H).trans CeEx.noRules) (fun k hk => noRaw k ((CeEx.params_wh c H) ▸ hk))

/-- **The clause `match_named` names is match independent, for every H.** -/
theorem matchF (H : HookParams) : MatchIndependent (cH H) CeEx.clF :=
  (fnHypH H).2.2.2.1 CeEx.fnF (by rw [(CeEx.fns_wh c H).trans CeEx.read]; exact List.mem_singleton_self _)
    CeEx.clF (List.mem_singleton_self _)

/-- **`p(b) = notBool b` and no other result, for every H.** -/
theorem p_value (H : HookParams) (b : Bool) : Eval (cH H) CeEx.fF [bool b] (some (bool (!b))) :=
  CeEx.value (notCtorH H) (lookupFH H) b
theorem p_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) CeEx.fF [bool b] r) :
    r = some (bool (!b)) :=
  CeEx.alone (notCtorH H) (lookupFH H) h

/-- **`p(true) = false`, for every H.** -/
theorem p_true (H : HookParams) : Eval (cH H) CeEx.fF [bool true] (some (bool false)) := p_value H true

/-- **`p(true)` has no result but `false`, for every H**: not `true`, and not none. -/
theorem p_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) CeEx.fF [bool true] r) :
    r = some (bool false) := p_alone H h

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


/-! ## Function equations (28 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 164, `twice`) is the equation read as a clause with existential variables
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

/-- Γ's item 0 (sentence 164): an existential clause, `∃x. ∃x. (x ∧ ψ)` against `∃x. x ∧ (⊤ ∧ ψ)` (`ensTop_ex_body, exVac_body`). -/
noncomputable def exItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem exItem0_at : (TiePair.gammaPats c)[0]? = some exItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax164
/-- **Γ's item 0 is not the text's sentence 164** (kernel). -/
theorem ex0_differs : exItem0 ≠ (trS U.ax164).pat := by decide +kernel

noncomputable def ex0tbl : VarTable := tableOf U.ax164.ax.sortVars U.ax164.ax.pattern
noncomputable abbrev ex0ctx : Ctx := ⟨ex0tbl, kore.aliasNames⟩
noncomputable def ex0ws : List P := guardsOf U.ax164.ax
noncomputable def ex0r : EVar := ex0tbl.ev (sortVarKey Rv)
noncomputable def ex0prem : P := tr ex0ctx (premK U.ax164.ax.pattern)
noncomputable def ex0S : P := trSort ex0tbl (srt "Bool")
noncomputable def ex0F : P := tr ex0ctx (lhsK U.ax164.ax.pattern)
noncomputable def ex0ens : P := tr ex0ctx (ensK U.ax164.ax.pattern)
noncomputable def ex0K : Kore.Pattern := rhsK U.ax164.ax.pattern
noncomputable def ex0x : EVar := exVK ex0tbl ex0K
noncomputable def ex0psi : P := tr ex0ctx (argK 1 (exBK (exBK ex0K)))

/-- The translated sentence 164 is `eqnPat` with the right side the text writes (kernel). -/
theorem ex0_text_shape : (trS U.ax164).pat = eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0x ex0S (sExists ex0x ex0S (sAnd (.evar ex0x) ex0psi))) ex0ens) := by
  decide +kernel

/-- Γ's item 0 is `eqnPat` over the same guards, premise, sort and left side, with the clause's right
side (kernel). -/
theorem ex0_gamma_shape : (TiePair.gammaPats c)[0]? = some (eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0x ex0S (sAnd (.evar ex0x) (sAnd (sTop ex0S) ex0psi))) ex0ens)) := by
  decide +kernel

theorem ex0_guard_r : sortGuard ex0r ∈ ex0ws := by decide +kernel
theorem ex0_inner_free : (sExists ex0x ex0S (sAnd (.evar ex0x) ex0psi)).isFreeEvar ex0x = false := by decide +kernel
theorem ex0_nameS (H : HookParams) : (cH H).sortName (2 : Srt) = "Bool" :=
  (by decide +kernel : c.sortName (2 : Srt) = "Bool")
theorem ex0_ltS (H : HookParams) : (2 : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (2 : Srt) < nRegSorts + c.sortNames.length)

/-- **Sentence 164 and Γ's item 0 hold in the same interpretations** among those with the
signature's facts (definedness, the item of `⌈_⌉`, each numbered sort one sort), for every H. -/
theorem ex0_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0x ex0S (sAnd (.evar ex0x) (sAnd (sTop ex0S) ex0psi))) ex0ens)) ↔ (I ⊧ᴵ (trS U.ax164).pat) := by
  rw [ex0_text_shape]
  obtain ⟨σ, hS⟩ := sortAtN F (ex0_nameS H) (ex0_ltS H) ex0tbl
  exact eqnPat_of_body F.defOK F.ceilDef hS ex0_guard_r (guardsOf_pred F.defOK U.ax164.ax) fun e m hat a ha =>
    (ensTop_ex_body F.defOK hS ha).trans (exVac_body F.defOK hS ex0_inner_free ha).symm

/-- **W1**: Γ's item 0 is a consequence of sentence 164 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex0_from_text (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax164).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex0_gamma_shape)
    (fun F _ => ex0_iff H F)).1

/-- **E**: Γ entails sentence 164, for every H. -/
theorem ex0_entailed (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax164).pat :=
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

end KCore.TieE3EqExistsTwiceMl

#check @KCore.TieE3EqExistsTwiceMl.noRaw
#check @KCore.TieE3EqExistsTwiceMl.readsConfined_c
#check @KCore.TieE3EqExistsTwiceMl.userAxioms_eq
#check @KCore.TieE3EqExistsTwiceMl.coreOK
#check @KCore.TieE3EqExistsTwiceMl.account
#check @KCore.TieE3EqExistsTwiceMl.account_sizes
#check @KCore.TieE3EqExistsTwiceMl.account_classes
#check @KCore.TieE3EqExistsTwiceMl.account_absent
#check @KCore.TieE3EqExistsTwiceMl.absent_closed
#check @KCore.TieE3EqExistsTwiceMl.absent_proj_below_c
#check @KCore.TieE3EqExistsTwiceMl.absent_proj_below
#check @KCore.TieE3EqExistsTwiceMl.lists_in_account
#check @KCore.TieE3EqExistsTwiceMl.attrs_agree
#check @KCore.TieE3EqExistsTwiceMl.sig_origin_but_next
#check @KCore.TieE3EqExistsTwiceMl.decls_entailed
#check @KCore.TieE3EqExistsTwiceMl.consistent
#check @KCore.TieE3EqExistsTwiceMl.text_nextless
#check @KCore.TieE3EqExistsTwiceMl.nojunk_trivial_entailed
#check @KCore.TieE3EqExistsTwiceMl.nojunk_items_entailed
#check @KCore.TieE3EqExistsTwiceMl.nojunk_kitem_entailed
#check @KCore.TieE3EqExistsTwiceMl.cons_entailed
#check @KCore.TieE3EqExistsTwiceMl.idem_refuted
#check @KCore.TieE3EqExistsTwiceMl.owed_rules
#check @KCore.TieE3EqExistsTwiceMl.owed_clauses
#check @KCore.TieE3EqExistsTwiceMl.openDecidedH
#check @KCore.TieE3EqExistsTwiceMl.gammaCl_eq
#check @KCore.TieE3EqExistsTwiceMl.decls_entailed_c
#check @KCore.TieE3EqExistsTwiceMl.nojunk_trivial_entailed_c
#check @KCore.TieE3EqExistsTwiceMl.nojunk_items_entailed_c
#check @KCore.TieE3EqExistsTwiceMl.nojunk_kitem_entailed_c
#check @KCore.TieE3EqExistsTwiceMl.cons_entailed_c
#check @KCore.TieE3EqExistsTwiceMl.idem_refuted_c
#print axioms KCore.TieE3EqExistsTwiceMl.noRaw
#print axioms KCore.TieE3EqExistsTwiceMl.readsConfined_c
#print axioms KCore.TieE3EqExistsTwiceMl.userAxioms_eq
#print axioms KCore.TieE3EqExistsTwiceMl.coreOK
#print axioms KCore.TieE3EqExistsTwiceMl.account
#print axioms KCore.TieE3EqExistsTwiceMl.account_sizes
#print axioms KCore.TieE3EqExistsTwiceMl.account_classes
#print axioms KCore.TieE3EqExistsTwiceMl.account_absent
#print axioms KCore.TieE3EqExistsTwiceMl.absent_closed
#print axioms KCore.TieE3EqExistsTwiceMl.absent_proj_below_c
#print axioms KCore.TieE3EqExistsTwiceMl.absent_proj_below
#print axioms KCore.TieE3EqExistsTwiceMl.lists_in_account
#print axioms KCore.TieE3EqExistsTwiceMl.attrs_agree
#print axioms KCore.TieE3EqExistsTwiceMl.sig_origin_but_next
#print axioms KCore.TieE3EqExistsTwiceMl.decls_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.consistent
#print axioms KCore.TieE3EqExistsTwiceMl.text_nextless
#print axioms KCore.TieE3EqExistsTwiceMl.nojunk_trivial_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.nojunk_items_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.nojunk_kitem_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.cons_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.idem_refuted
#print axioms KCore.TieE3EqExistsTwiceMl.owed_rules
#print axioms KCore.TieE3EqExistsTwiceMl.owed_clauses
#print axioms KCore.TieE3EqExistsTwiceMl.openDecidedH
#print axioms KCore.TieE3EqExistsTwiceMl.gammaCl_eq
#print axioms KCore.TieE3EqExistsTwiceMl.decls_entailed_c
#print axioms KCore.TieE3EqExistsTwiceMl.nojunk_trivial_entailed_c
#print axioms KCore.TieE3EqExistsTwiceMl.nojunk_items_entailed_c
#print axioms KCore.TieE3EqExistsTwiceMl.nojunk_kitem_entailed_c
#print axioms KCore.TieE3EqExistsTwiceMl.cons_entailed_c
#print axioms KCore.TieE3EqExistsTwiceMl.idem_refuted_c
#check @KCore.TieE3EqExistsTwiceMl.fns_account
#check @KCore.TieE3EqExistsTwiceMl.ex0_differs
#check @KCore.TieE3EqExistsTwiceMl.ex0_text_shape
#check @KCore.TieE3EqExistsTwiceMl.ex0_gamma_shape
#check @KCore.TieE3EqExistsTwiceMl.ex0_guard_r
#check @KCore.TieE3EqExistsTwiceMl.ex0_inner_free
#check @KCore.TieE3EqExistsTwiceMl.ex0_nameS
#check @KCore.TieE3EqExistsTwiceMl.ex0_ltS
#check @KCore.TieE3EqExistsTwiceMl.ex0_iff
#check @KCore.TieE3EqExistsTwiceMl.ex0_from_text
#check @KCore.TieE3EqExistsTwiceMl.ex0_entailed
#check @KCore.TieE3EqExistsTwiceMl.shape
#check @KCore.TieE3EqExistsTwiceMl.fns_entailed
#check @KCore.TieE3EqExistsTwiceMl.fns_from_text
#check @KCore.TieE3EqExistsTwiceMl.fn_prios
#check @KCore.TieE3EqExistsTwiceMl.gamma_from
#print axioms KCore.TieE3EqExistsTwiceMl.fns_account
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_differs
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_text_shape
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_gamma_shape
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_guard_r
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_inner_free
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_nameS
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_ltS
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_iff
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_from_text
#print axioms KCore.TieE3EqExistsTwiceMl.ex0_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.shape
#print axioms KCore.TieE3EqExistsTwiceMl.fns_entailed
#print axioms KCore.TieE3EqExistsTwiceMl.fns_from_text
#print axioms KCore.TieE3EqExistsTwiceMl.fn_prios
#print axioms KCore.TieE3EqExistsTwiceMl.gamma_from
