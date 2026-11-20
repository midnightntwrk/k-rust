/-
  The tie (C14) on `f2-examples/e3-eq-exists-ml-and-terms.kompile.kore`, the kompiled text of construct fixture e3-eq-exists-ml-and-terms
  (`test/constructs/fixtures/e3-eq-exists-ml-and-terms`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-eq-exists-ml-and-terms`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3EqExistsMlAndTerms.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 252 sentences of the user module E3-EQ-EXISTS-ML-AND-TERMS, in
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
    The consistency section, written by hand, proves what it owes for every H (`openDecidedH`),
    so `Γc` with the step's closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0, 1 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Items 0 (200), 1 (235) are equations read as a clause with
    existential variables (`existentialClause`), not their sentences (`ex<j>_differs`): the two hold
    in the same interpretations with the signature's facts (`ex<j>_iff`, by a lemma of
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
    items 0, 1 (whose sentences give it with `ΓSig`: `ex<j>_from_text`), Γ's rule items, the five
    parts Γ defines by predicates, or definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (4);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsMlAndTerms

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore" module "E3-EQ-EXISTS-ML-AND-TERMS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-EQ-EXISTS-ML-AND-TERMS")

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
  [("function equation", [200, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
      223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 235]),
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
      197, 198, 199, 201, 236, 237, 238, 239, 253, 254]),
   ("set idempotence", [60]),
   ("set-variable lemma", [118, 119, 120, 121, 122, 255]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [35, 39, 41, 72, 74, 78, 94, 106, 107, 148, 180, 202, 203, 204, 205, 233, 234, 240, 241, 242,
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
    [("function equation", 29), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 30)] := by
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
  [(117, "no junk"), (200, "function equation"), (205, "no direction"), (235, "function equation")]

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (15, 14, 128, 91, 5, 32) := by
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

/-! ## Consistency for every H: `f(X) => #Exists B. (B #And notBool X)`, `k(X) => #Exists Z. (Z #And (X +Int 1))`, one instance of each gives the value -/

/- The functions `f` and `k` have one clause each, read with an existential variable (`exs [1]`)
holding the position and `post` its membership in the other conjunct (`clM`: B ∈ `notBool X`,
Z ∈ `X +Int 1`): `Semantics.FnsNoExs` is false, so neither `consistent_of_fnFacts` nor the step
from `FnObligations` to `FnHyp` applies, and `FnHyp` is proved here for every H (`fnHypH`).
- A result at every argument: `f(b)` is `notBool b`, by the instance B := `notBool b`; `k(n)` is
  `n +Int 1`, by the instance Z := `n +Int 1` (`CeEx.value`).
- Agreement: one clause each (`CeEx.agree_one`).
- Match independence of the clauses `match_named` names (`matchF`, `matchK`): at a match giving X
  a value the clause's one result is the other conjunct's value there (`CeEx.res_eq`,
  `CeEx.res_some`); every other instance has `post` false and gives nothing (`CeEx.inst_all`).
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `OpenLaws`: the text has no open generator (`noRaw`).
So Γc with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).

`CeEx` holds the proofs, over any semantics `d` that reads the clauses; the two clauses have one
shape, `clM s t`, and the facts on that shape are stated once, from what the term t evaluates to
(`TermOK`) and what the values of the sort s are (`ValsOK`). The statements after it are on `cH H`. -/

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

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-! ### The clause `f(X) => V` with `post := V ∈ t` -/

/-- `f(X) => V` with `exs = [V]` and `post := V ∈ t`, X and V of the sort s. -/
def clM (s : Srt) (t : Term) : Clause :=
  { vars := [s, s], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .mem s (.var 1) t }

def fnM (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clM s t] }

/-- The term t at a σ giving X the value `emb a` has the one result `F a`. -/
structure TermOK (d : Semantics) (t : Term) {α : Type} (emb F : α → GroundTerm) : Prop where
  ev : ∀ (σ : Subst) a, σ.lookup 0 = some (emb a) → EvalTerm d σ t (some (F a))
  inv : ∀ (σ : Subst) a r, σ.lookup 0 = some (emb a) → EvalTerm d σ t r → r = some (F a)

/-- The values of the sort s are the `emb a`, and each `F a` is one. -/
structure ValsOK (d : Semantics) (s : Srt) {α : Type} (emb F : α → GroundTerm) : Prop where
  shape : ∀ w, d.sortOf w = some s → ∃ a, w = emb a
  sx : ∀ a, d.sortOf (emb a) = some s
  sy : ∀ a, d.sortOf (F a) = some s

section Shape

variable {s : Srt} {t : Term} {α : Type} {emb F : α → GroundTerm} {f : Sym}

theorem post_holds (ht : TermOK d t emb F) {a : α} {w : GroundTerm} (h0 : σ.lookup 0 = some (emb a))
    (h1 : σ.lookup 1 = some w) : Holds d 2 σ (clM s t).post (sameResult (some w) (some (F a))) :=
  holds_cast (Holds.mem .var (ht.ev σ a h0)) (by rw [h1]; rfl)

theorem post_inv (ht : TermOK d t emb F) {a : α} {w : GroundTerm} (h0 : σ.lookup 0 = some (emb a))
    (h1 : σ.lookup 1 = some w) {b : Bool} (h : Holds d 2 σ (clM s t).post b) :
    b = sameResult (some w) (some (F a)) := by
  cases h with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := ht.inv σ a _ h0 h'
    rw [h1]; rfl

theorem exsFree_clM : (clM s t).exsFree = [1] := rfl
theorem univ_clM : (clM s t).univ = [0] := rfl
theorem exs_clM : (clM s t).exs ≠ [] := List.cons_ne_nil 1 []

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff (clM s t).exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by rw [exsFree_clM]; decide)

theorem ext_agree (σ : Subst) (w : GroundTerm) : AgreeOff (clM s t).exsFree σ ((1, w) :: σ) := agree_set1 σ w

/-- σ with V := `F a` is well sorted where σ gives X the value `emb a`. -/
theorem ext_sorted (hv : ValsOK d s emb F) {a : α} (h0 : σ.lookup 0 = some (emb a)) :
    d.WellSorted (clM s t).vars ((1, F a) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (hv.sx a) (lkSelf _ _ _) (hv.sy a)

/-- **Every instance is decided and gives `F a` or nothing**: at V := `F a` it gives it, at every
other value its `post` is false. -/
theorem inst_all (ht : TermOK d t emb F) {a : α} (h0 : σ.lookup 0 = some (emb a))
    (hw : d.WellSorted (clM s t).vars σ) : InstIs d σ (clM s t) (some (F a)) := by
  obtain ⟨w, hw1, -⟩ := hw 1 s rfl
  cases hb : sameResult (some w) (some (F a)) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds ht h0 hw1) hb)
  | false => exact .fails (post_holds ht h0 hw1) (.post (holds_cast (post_holds ht h0 hw1) hb))

/-- The instance at V := `F a` does not give nothing. -/
theorem inst_not_none (ht : TermOK d t emb F) {a : α} (h0 : σ.lookup 0 = some (emb a))
    (h1 : σ.lookup 1 = some (F a)) : ¬ InstIs d σ (clM s t) none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht' _ _ => cases ht'
    | post hp =>
      have e := post_inv ht h0 h1 hp
      rw [sameResult_self] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e

/-- **The clause has the one result `F a` at a match giving X the value `emb a`.** -/
theorem res_eq (ht : TermOK d t emb F) (hv : ValsOK d s emb F) {a : α} (h0 : σ.lookup 0 = some (emb a))
    {r : Option GroundTerm} (h : Clause.Res d (clM s t) σ r) : r = some (F a) := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, ha, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex exs_clM
  · have h0' := (agree_x ha).trans h0
    have e := post_inv ht h0' (EvalTerm.var_inv hrhs).symm hpost
    rw [sameResult_some.mp e.symm]
  · exact absurd (hall _ (ext_agree σ _) (ext_sorted hv h0))
      (inst_not_none ht ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

theorem res_some (ht : TermOK d t emb F) (hv : ValsOK d s emb F) {a : α} (h0 : σ.lookup 0 = some (emb a)) :
    Clause.Res d (clM s t) σ (some (F a)) :=
  have h0' : ((1, F a) :: σ : Subst).lookup 0 = some (emb a) := (lkNe _ _ (by decide)).trans h0
  .inr ⟨exs_clM, .inl ⟨(1, F a) :: σ, F a, ext_agree σ _, ext_sorted hv h0,
    ⟨(lkSelf 1 (F a) σ) ▸ .var, (fun t ht => nomatch ht),
      holds_cast (post_holds ht h0' (lkSelf _ _ _)) (sameResult_self _)⟩,
    fun σ'' ha hw => inst_all ht ((agree_x ha).trans h0) hw, rfl⟩⟩

/-- **`f(emb a)` is `F a`**, by `Eval.clauseEx` at V := `F a`. -/
theorem value (ht : TermOK d t emb F) (hv : ValsOK d s emb F) (hfn : d.lookupFn f = some (fnM f s t))
    (a : α) : Eval d f [emb a] (some (F a)) :=
  have h0 : ([(1, F a), (0, emb a)] : Subst).lookup 0 = some (emb a) := rfl
  .clauseEx (fn := fnM f s t) (cl := clM s t) (σ := [(1, F a), (0, emb a)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl (hv.sx a) rfl (hv.sy a)) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnM, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    exs_clM .var (fun t ht => nomatch ht)
    (holds_cast (post_holds ht h0 rfl) (sameResult_self _))
    (fun σ' ha hw => inst_all ht ((agree_x ha).trans h0) hw)

/-- **`f(emb a)` has no other result.** -/
theorem alone (ht : TermOK d t emb F) (hv : ValsOK d s emb F) (hfn : d.lookupFn f = some (fnM f s t))
    {a : α} {r : Option GroundTerm} (h : Eval d f [emb a] r) : r = some (F a) := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clM s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnM] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ (clM s t).pats [emb a] → σ.lookup 0 = some (emb a) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clM
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone (clM s t) (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted (clM s t).vars [(1, emb a), (0, emb a)] := sorted2 rfl (hv.sx a) rfl (hv.sx a)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clM
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have h1 := (EvalTerm.var_inv hrhs).symm
    have e := post_inv ht (hx0 hmatch) h1 hpost
    rw [sameResult_some.mp e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx0 hmatch
    exact absurd (hall _ (ext_agree σ _) (ext_sorted hv h0))
      (inst_not_none ht ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-- The value a match of the clause gives X is a value of the sort s. -/
theorem applies_x (hv : ValsOK d s emb F) {vs : List GroundTerm} (h : (clM s t).AppliesAt d σ vs) :
    ∃ a, σ.lookup 0 = some (emb a) := by
  obtain ⟨w, hw, hws⟩ := h.1 0 (by rw [univ_clM]; exact List.mem_singleton_self _) s rfl
  obtain ⟨a, rfl⟩ := hv.shape w hws
  exact ⟨a, hw⟩

/-- **The clause is match independent**: two matches at one argument list give X one value, so
one result; where it decides, it has a result. -/
theorem matchInd (ht : TermOK d t emb F) (hv : ValsOK d s emb F) : MatchIndependent d (clM s t) := by
  refine ⟨fun vs σ σ' ha ha' _ _ _ _ _ => .inr fun r r' hr hr' => ?_, fun _ _ _ _ σ _ _ hdec => ?_⟩
  · obtain ⟨a, hb⟩ := applies_x hv ha
    obtain ⟨v, vs', rfl, hv0, -⟩ := PatVals.cons_inv ha.2.1
    obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv ha'.2.1
    cases hvs
    have hb' : σ'.lookup 0 = some (emb a) :=
      (PatVal.var_inv hv').trans ((PatVal.var_inv hv0).symm.trans hb)
    rw [res_eq ht hv hb hr, res_eq ht hv hb' hr']
  · obtain ⟨a, hb⟩ := applies_x hv hdec.1
    exact ⟨_, res_some ht hv hb⟩

/-- The function of the clause has a result at every argument list of its sorts. -/
theorem has_result (ht : TermOK d t emb F) (hv : ValsOK d s emb F) (hfn : d.lookupFn f = some (fnM f s t))
    {vs : List GroundTerm} (hvs : d.sortsOf vs = some [s]) : ∃ r, Eval d f vs r := by
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  obtain ⟨a, rfl⟩ := hv.shape w hw
  exact ⟨_, value ht hv hfn a⟩

end Shape

/-! ### The reading of this text -/

def fF : Sym := 384
def fK : Sym := 385

/-- f's right side's other conjunct, `notBool X`. -/
def tF : Term := .app boolNot [.var 0]
/-- k's right side's other conjunct, `X +Int 1`. -/
def tK : Term := .app intAdd [.var 0, .dv Srt.int (.int 1)]

/-- `f(X) => B` with `exs = [B]` and `post := B ∈ notBool X`, X and B of Bool. -/
def clF : Clause := clM Srt.bool tF
/-- `k(X) => Z` with `exs = [Z]` and `post := Z ∈ X +Int 1`, X and Z of Int. -/
def clK : Clause := clM Srt.int tK

def fnF : Fn := fnM fF Srt.bool tF
def fnK : Fn := fnM fK Srt.int tK

/-- **The reading**: the text's functions are `f`, with the one clause `clF`, and `k`, with the one
clause `clK`. -/
theorem read : c.fns = [fnF, fnK] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName fK = "Lblk" ∧ c.symName boolNot = "LblnotBool'Unds'" ∧
    c.symName intAdd = "Lbl'UndsPlus'Int'Unds'" ∧ c.sortName Srt.bool = "Bool" ∧
    c.sortName Srt.int = "Int" := by decide +kernel

/-- B is of the confined Bool, Z of the unconfined Int and fixed by its membership: `clausePlainEx`
admits both clauses. -/
theorem plainEx : c.clausePlainEx clF = true ∧ c.confined Srt.int = false ∧ c.clausePlainEx clK = true := by
  decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupK : c.lookupFn fK = some fnK := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false ∧ c.isCtor intAdd = false := by decide +kernel
theorem noRules : c.rules = [] := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-! ### The clauses in a semantics that reads them -/

section Clause

variable {d : Semantics}

theorem notHook : isHook boolNot = true := by decide +kernel
theorem addHook : isHook intAdd = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation (domains.md 1138, 1139). -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

/-- `_+Int_` at two values of Int, under every interpretation (the sum of the two integers). -/
theorem hookAdd (n : Int) : d.hookRes intAdd [int n, int 1] = some (some (int (n + 1))) :=
  Semantics.hookRes_of_value rfl

theorem tF_ok (hc : d.isCtor boolNot = false) : TermOK d tF bool (fun b => bool (!b)) where
  ev σ b h0 := .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)
  inv σ b r h0 h := by
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    have := hh [bool b] (by rw [h0]; rfl)
    rw [hookNot] at this
    exact (Option.some.inj this).symm

theorem tK_ok (hc : d.isCtor intAdd = false) : TermOK d tK int (fun n => int (n + 1)) where
  ev σ n h0 := .hook hc addHook (rs := [σ.lookup 0, some (int 1)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookAdd n)
    (fun hn => by rw [h0] at hn; cases hn)
  inv σ n r h0 h := by
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hc addHook h
    obtain ⟨r1, rs1, rfl, h1, hs1⟩ := EvalTerms.cons_inv hts
    obtain ⟨r2, rs2, rfl, h2, hs2⟩ := EvalTerms.cons_inv hs1
    obtain rfl := EvalTerms.nil_inv hs2
    obtain rfl := EvalTerm.var_inv h1
    obtain rfl := EvalTerm.dv_inv h2
    have := hh [int n, int 1] (by rw [h0]; rfl)
    rw [hookAdd] at this
    exact (Option.some.inj this).symm

/-- The values of Bool are its literals, in a semantics whose sorts have their shapes. -/
theorem valsF (hs : d.shapesOK = true) : ValsOK d Srt.bool bool (fun b => bool (!b)) where
  shape _ hw := shape_bool hs hw
  sx b := rmS_sortOf_bool d b
  sy b := rmS_sortOf_bool d (!b)

/-- The values of Int are its literals, in a semantics whose sorts have their shapes. -/
theorem valsK (hs : d.shapesOK = true) : ValsOK d Srt.int int (fun n => int (n + 1)) where
  shape _ hw := shape_int hs hw
  sx n := rmS_sortOf_int d n
  sy n := rmS_sortOf_int d (n + 1)

/-- **`FnHyp`** of a semantics whose functions are `f` with the clause `clF` and `k` with the
clause `clK`, without rules and open generators, where the values of Bool and of Int are their
literals. -/
theorem fnHyp_of (hcF : d.isCtor boolNot = false) (hcK : d.isCtor intAdd = false) (hfns : d.fns = [fnF, fnK])
    (hfnF : d.lookupFn fF = some fnF) (hfnK : d.lookupFn fK = some fnK)
    (hs : d.shapesOK = true) (hrules : d.rules = []) (hraw : ∀ k ∈ d.params, k.raw = false) : FnHyp d := by
  have hmem : ∀ {fn}, fn ∈ d.fns → fn = fnF ∨ fn = fnK := fun h => by rw [hfns] at h; simpa using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf ht => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecided_of_plain (fun r hr => by rw [hrules] at hr; cases hr) (fun fn hf cl hcl => ?_),
    openLaws_of_plain hraw⟩
  · rcases hmem hf with rfl | rfl
    · exact has_result (tF_ok hcF) (valsF hs) hfnF hvs
    · exact has_result (tK_ok hcK) (valsK hs) hfnK hvs
  · rcases hmem hf with rfl | rfl <;> cases ht
  · rcases hmem hf with rfl | rfl <;> exact agree_one rfl
  · rcases hmem hf with rfl | rfl
    · obtain rfl : cl = clF := List.mem_singleton.mp hcl
      exact matchInd (tF_ok hcF) (valsF hs)
    · obtain rfl : cl = clK := List.mem_singleton.mp hcl
      exact matchInd (tK_ok hcK) (valsK hs)
  · rcases hmem hf with rfl | rfl
    · obtain rfl : cl = clF := List.mem_singleton.mp hcl
      rfl
    · obtain rfl : cl = clK := List.mem_singleton.mp hcl
      rfl

end Clause

end CeEx

/-! ### The facts the deciders name -/

def callOrder : List Nat := [CeEx.fF, CeEx.fK]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clauses whose match independence no decider confirms: `f`'s and `k`'s. -/
theorem match_named : c.matchObligationsL = [(CeEx.fF, 0), (CeEx.fK, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### `FnHyp` and consistency, for every H -/

theorem notCtorFH (H : HookParams) : (cH H).isCtor boolNot = false := (CeEx.isCtor_wh c H _).trans CeEx.notCtor.1
theorem notCtorKH (H : HookParams) : (cH H).isCtor intAdd = false := (CeEx.isCtor_wh c H _).trans CeEx.notCtor.2
theorem lookupFH (H : HookParams) : (cH H).lookupFn CeEx.fF = some CeEx.fnF := by
  rw [Semantics.lookupFn_withHooks]; exact CeEx.lookupF
theorem lookupKH (H : HookParams) : (cH H).lookupFn CeEx.fK = some CeEx.fnK := by
  rw [Semantics.lookupFn_withHooks]; exact CeEx.lookupK
theorem shapesH (H : HookParams) : (cH H).shapesOK = true := (CeEx.shapesOK_wh c H).trans CeEx.shapes

/-- **`FnHyp` holds, for every H.** -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  CeEx.fnHyp_of (notCtorFH H) (notCtorKH H) ((CeEx.fns_wh c H).trans CeEx.read) (lookupFH H) (lookupKH H)
    (shapesH H) ((CeEx.rules_wh c H).trans CeEx.noRules) (fun k hk => noRaw k ((CeEx.params_wh c H) ▸ hk))

/-- **The clause of `f` that `match_named` names is match independent, for every H.** -/
theorem matchF (H : HookParams) : MatchIndependent (cH H) CeEx.clF :=
  (fnHypH H).2.2.2.1 CeEx.fnF (by rw [(CeEx.fns_wh c H).trans CeEx.read]; exact List.mem_cons_self ..)
    CeEx.clF (List.mem_singleton_self _)

/-- **The clause of `k` that `match_named` names is match independent, for every H.** -/
theorem matchK (H : HookParams) : MatchIndependent (cH H) CeEx.clK :=
  (fnHypH H).2.2.2.1 CeEx.fnK
    (by rw [(CeEx.fns_wh c H).trans CeEx.read]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
    CeEx.clK (List.mem_singleton_self _)

/-- **`f(b) = notBool b` and no other result, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) CeEx.fF [bool b] (some (bool (!b))) :=
  CeEx.value (CeEx.tF_ok (notCtorFH H)) (CeEx.valsF (shapesH H)) (lookupFH H) b
theorem f_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) CeEx.fF [bool b] r) :
    r = some (bool (!b)) :=
  CeEx.alone (CeEx.tF_ok (notCtorFH H)) (CeEx.valsF (shapesH H)) (lookupFH H) h

/-- **`k(n) = n +Int 1` and no other result, for every H.** -/
theorem k_value (H : HookParams) (n : Int) : Eval (cH H) CeEx.fK [int n] (some (int (n + 1))) :=
  CeEx.value (CeEx.tK_ok (notCtorKH H)) (CeEx.valsK (shapesH H)) (lookupKH H) n
theorem k_alone (H : HookParams) {n : Int} {r : Option GroundTerm} (h : Eval (cH H) CeEx.fK [int n] r) :
    r = some (int (n + 1)) :=
  CeEx.alone (CeEx.tK_ok (notCtorKH H)) (CeEx.valsK (shapesH H)) (lookupKH H) h

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


/-! ## Function equations (29 sentences) and priority equations (0 sentences)

Γ's items 0 (sentence 200, `memTerm`), 1 (sentence 235, `memTerm`) are equations read as a clause
with existential variables (`existentialClause`): Γ's right side binds the clause's variables under
`\exists` with `\top` beside the term, where the text writes its own right side, so the item is not
the sentence (`ex<j>_differs`). Both are `eqnPat` over one guard list, premise, sort and left side
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

/-- Γ's item 0 (sentence 200): an existential clause, `∃x. x ∧ t` against `∃x. x ∧ (⊤ ∧ x ∈ t)` (`memTerm_body`). -/
noncomputable def exItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem exItem0_at : (TiePair.gammaPats c)[0]? = some exItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax200
/-- **Γ's item 0 is not the text's sentence 200** (kernel). -/
theorem ex0_differs : exItem0 ≠ (trS U.ax200).pat := by decide +kernel

noncomputable def ex0tbl : VarTable := tableOf U.ax200.ax.sortVars U.ax200.ax.pattern
noncomputable abbrev ex0ctx : Ctx := ⟨ex0tbl, kore.aliasNames⟩
noncomputable def ex0ws : List P := guardsOf U.ax200.ax
noncomputable def ex0r : EVar := ex0tbl.ev (sortVarKey Rv)
noncomputable def ex0prem : P := tr ex0ctx (premK U.ax200.ax.pattern)
noncomputable def ex0S : P := trSort ex0tbl (srt "Bool")
noncomputable def ex0F : P := tr ex0ctx (lhsK U.ax200.ax.pattern)
noncomputable def ex0ens : P := tr ex0ctx (ensK U.ax200.ax.pattern)
noncomputable def ex0K : Kore.Pattern := rhsK U.ax200.ax.pattern
noncomputable def ex0x : EVar := exVK ex0tbl ex0K
noncomputable def ex0t : P := tr ex0ctx (argK 1 (exBK ex0K))

/-- The translated sentence 200 is `eqnPat` with the right side the text writes (kernel). -/
theorem ex0_text_shape : (trS U.ax200).pat = eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0x ex0S (sAnd (.evar ex0x) ex0t)) ex0ens) := by
  decide +kernel

/-- Γ's item 0 is `eqnPat` over the same guards, premise, sort and left side, with the clause's right
side (kernel). -/
theorem ex0_gamma_shape : (TiePair.gammaPats c)[0]? = some (eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0x ex0S (sAnd (.evar ex0x) (sAnd (sTop ex0S) (sIn ex0S ex0S (.evar ex0x) ex0t)))) ex0ens)) := by
  decide +kernel

theorem ex0_guard_r : sortGuard ex0r ∈ ex0ws := by decide +kernel
theorem ex0_nameS (H : HookParams) : (cH H).sortName (2 : Srt) = "Bool" :=
  (by decide +kernel : c.sortName (2 : Srt) = "Bool")
theorem ex0_ltS (H : HookParams) : (2 : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (2 : Srt) < nRegSorts + c.sortNames.length)

/-- **Sentence 200 and Γ's item 0 hold in the same interpretations** among those with the
signature's facts (definedness, the item of `⌈_⌉`, each numbered sort one sort), for every H. -/
theorem ex0_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ex0ws ex0r ex0prem ex0S ex0F (sAnd (sExists ex0x ex0S (sAnd (.evar ex0x) (sAnd (sTop ex0S) (sIn ex0S ex0S (.evar ex0x) ex0t)))) ex0ens)) ↔ (I ⊧ᴵ (trS U.ax200).pat) := by
  rw [ex0_text_shape]
  obtain ⟨σ, hS⟩ := sortAtN F (ex0_nameS H) (ex0_ltS H) ex0tbl
  exact eqnPat_of_body F.defOK F.ceilDef hS ex0_guard_r (guardsOf_pred F.defOK U.ax200.ax) fun e m hat a ha =>
    memTerm_body F.defOK F.ceilDef hS ha

/-- **W1**: Γ's item 0 is a consequence of sentence 200 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex0_from_text (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax200).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex0_gamma_shape)
    (fun F _ => ex0_iff H F)).1

/-- **E**: Γ entails sentence 200, for every H. -/
theorem ex0_entailed (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax200).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex0_gamma_shape)
    (fun F _ => ex0_iff H F)).2

/-- Γ's item 1 (sentence 235): an existential clause, `∃x. x ∧ t` against `∃x. x ∧ (⊤ ∧ x ∈ t)` (`memTerm_body`). -/
noncomputable def exItem1 : P := (TiePair.gammaPats c).getD 1 ⊥
theorem exItem1_at : (TiePair.gammaPats c)[1]? = some exItem1 := by decide +kernel
kernel_rfl fnText_at1 : fnText[1]? = some U.ax235
/-- **Γ's item 1 is not the text's sentence 235** (kernel). -/
theorem ex1_differs : exItem1 ≠ (trS U.ax235).pat := by decide +kernel

noncomputable def ex1tbl : VarTable := tableOf U.ax235.ax.sortVars U.ax235.ax.pattern
noncomputable abbrev ex1ctx : Ctx := ⟨ex1tbl, kore.aliasNames⟩
noncomputable def ex1ws : List P := guardsOf U.ax235.ax
noncomputable def ex1r : EVar := ex1tbl.ev (sortVarKey Rv)
noncomputable def ex1prem : P := tr ex1ctx (premK U.ax235.ax.pattern)
noncomputable def ex1S : P := trSort ex1tbl (srt "Int")
noncomputable def ex1F : P := tr ex1ctx (lhsK U.ax235.ax.pattern)
noncomputable def ex1ens : P := tr ex1ctx (ensK U.ax235.ax.pattern)
noncomputable def ex1K : Kore.Pattern := rhsK U.ax235.ax.pattern
noncomputable def ex1x : EVar := exVK ex1tbl ex1K
noncomputable def ex1t : P := tr ex1ctx (argK 1 (exBK ex1K))

/-- The translated sentence 235 is `eqnPat` with the right side the text writes (kernel). -/
theorem ex1_text_shape : (trS U.ax235).pat = eqnPat ex1ws ex1r ex1prem ex1S ex1F (sAnd (sExists ex1x ex1S (sAnd (.evar ex1x) ex1t)) ex1ens) := by
  decide +kernel

/-- Γ's item 1 is `eqnPat` over the same guards, premise, sort and left side, with the clause's right
side (kernel). -/
theorem ex1_gamma_shape : (TiePair.gammaPats c)[1]? = some (eqnPat ex1ws ex1r ex1prem ex1S ex1F (sAnd (sExists ex1x ex1S (sAnd (.evar ex1x) (sAnd (sTop ex1S) (sIn ex1S ex1S (.evar ex1x) ex1t)))) ex1ens)) := by
  decide +kernel

theorem ex1_guard_r : sortGuard ex1r ∈ ex1ws := by decide +kernel
theorem ex1_nameS (H : HookParams) : (cH H).sortName (3 : Srt) = "Int" :=
  (by decide +kernel : c.sortName (3 : Srt) = "Int")
theorem ex1_ltS (H : HookParams) : (3 : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (3 : Srt) < nRegSorts + c.sortNames.length)

/-- **Sentence 235 and Γ's item 1 hold in the same interpretations** among those with the
signature's facts (definedness, the item of `⌈_⌉`, each numbered sort one sort), for every H. -/
theorem ex1_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ex1ws ex1r ex1prem ex1S ex1F (sAnd (sExists ex1x ex1S (sAnd (.evar ex1x) (sAnd (sTop ex1S) (sIn ex1S ex1S (.evar ex1x) ex1t)))) ex1ens)) ↔ (I ⊧ᴵ (trS U.ax235).pat) := by
  rw [ex1_text_shape]
  obtain ⟨σ, hS⟩ := sortAtN F (ex1_nameS H) (ex1_ltS H) ex1tbl
  exact eqnPat_of_body F.defOK F.ceilDef hS ex1_guard_r (guardsOf_pred F.defOK U.ax235.ax) fun e m hat a ha =>
    memTerm_body F.defOK F.ceilDef hS ha

/-- **W1**: Γ's item 1 is a consequence of sentence 235 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex1_from_text (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[1]? = some it →
    (TiePair.Texts [(trS U.ax235).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex1_gamma_shape)
    (fun F _ => ex1_iff H F)).1

/-- **E**: Γ entails sentence 235, for every H. -/
theorem ex1_entailed (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax235).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact ex1_gamma_shape)
    (fun F _ => ex1_iff H F)).2

end

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at positions 0, 1. -/
noncomputable def textPats : List P := ((fnText.map (trS · |>.pat)).set 0 exItem0).set 1 exItem1

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

/-- **E for the function equations**: Γ entails each sentence of `fnText`, for every H; item 0 by `ex0_entailed`, item 1 by `ex1_entailed`. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  by_cases h0 : j = 0
  · subst h0
    rw [fnText_at0] at hj
    rw [← Option.some.inj hj]
    exact ex0_entailed H
  by_cases h1 : j = 1
  · subst h1
    rw [fnText_at1] at hj
    rw [← Option.some.inj hj]
    exact ex1_entailed H
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))

/-- **The converse for `fnItems`**: each item but the existential clauses given with `ΓSig` (items 0, 1) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
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

end KCore.TieE3EqExistsMlAndTerms

#check @KCore.TieE3EqExistsMlAndTerms.noRaw
#check @KCore.TieE3EqExistsMlAndTerms.readsConfined_c
#check @KCore.TieE3EqExistsMlAndTerms.userAxioms_eq
#check @KCore.TieE3EqExistsMlAndTerms.coreOK
#check @KCore.TieE3EqExistsMlAndTerms.account
#check @KCore.TieE3EqExistsMlAndTerms.account_sizes
#check @KCore.TieE3EqExistsMlAndTerms.account_classes
#check @KCore.TieE3EqExistsMlAndTerms.account_absent
#check @KCore.TieE3EqExistsMlAndTerms.absent_closed
#check @KCore.TieE3EqExistsMlAndTerms.absent_proj_below_c
#check @KCore.TieE3EqExistsMlAndTerms.absent_proj_below
#check @KCore.TieE3EqExistsMlAndTerms.lists_in_account
#check @KCore.TieE3EqExistsMlAndTerms.attrs_agree
#check @KCore.TieE3EqExistsMlAndTerms.sig_origin_but_next
#check @KCore.TieE3EqExistsMlAndTerms.decls_entailed
#check @KCore.TieE3EqExistsMlAndTerms.consistent
#check @KCore.TieE3EqExistsMlAndTerms.text_nextless
#check @KCore.TieE3EqExistsMlAndTerms.nojunk_trivial_entailed
#check @KCore.TieE3EqExistsMlAndTerms.nojunk_items_entailed
#check @KCore.TieE3EqExistsMlAndTerms.nojunk_kitem_entailed
#check @KCore.TieE3EqExistsMlAndTerms.cons_entailed
#check @KCore.TieE3EqExistsMlAndTerms.idem_refuted
#check @KCore.TieE3EqExistsMlAndTerms.lib166
#check @KCore.TieE3EqExistsMlAndTerms.lib166_at_values
#check @KCore.TieE3EqExistsMlAndTerms.owed_rules
#check @KCore.TieE3EqExistsMlAndTerms.owed_clauses
#check @KCore.TieE3EqExistsMlAndTerms.openDecidedH
#check @KCore.TieE3EqExistsMlAndTerms.gammaCl_eq
#check @KCore.TieE3EqExistsMlAndTerms.decls_entailed_c
#check @KCore.TieE3EqExistsMlAndTerms.nojunk_trivial_entailed_c
#check @KCore.TieE3EqExistsMlAndTerms.nojunk_items_entailed_c
#check @KCore.TieE3EqExistsMlAndTerms.nojunk_kitem_entailed_c
#check @KCore.TieE3EqExistsMlAndTerms.cons_entailed_c
#check @KCore.TieE3EqExistsMlAndTerms.idem_refuted_c
#print axioms KCore.TieE3EqExistsMlAndTerms.noRaw
#print axioms KCore.TieE3EqExistsMlAndTerms.readsConfined_c
#print axioms KCore.TieE3EqExistsMlAndTerms.userAxioms_eq
#print axioms KCore.TieE3EqExistsMlAndTerms.coreOK
#print axioms KCore.TieE3EqExistsMlAndTerms.account
#print axioms KCore.TieE3EqExistsMlAndTerms.account_sizes
#print axioms KCore.TieE3EqExistsMlAndTerms.account_classes
#print axioms KCore.TieE3EqExistsMlAndTerms.account_absent
#print axioms KCore.TieE3EqExistsMlAndTerms.absent_closed
#print axioms KCore.TieE3EqExistsMlAndTerms.absent_proj_below_c
#print axioms KCore.TieE3EqExistsMlAndTerms.absent_proj_below
#print axioms KCore.TieE3EqExistsMlAndTerms.lists_in_account
#print axioms KCore.TieE3EqExistsMlAndTerms.attrs_agree
#print axioms KCore.TieE3EqExistsMlAndTerms.sig_origin_but_next
#print axioms KCore.TieE3EqExistsMlAndTerms.decls_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.consistent
#print axioms KCore.TieE3EqExistsMlAndTerms.text_nextless
#print axioms KCore.TieE3EqExistsMlAndTerms.nojunk_trivial_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.nojunk_items_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.nojunk_kitem_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.cons_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.idem_refuted
#print axioms KCore.TieE3EqExistsMlAndTerms.lib166
#print axioms KCore.TieE3EqExistsMlAndTerms.lib166_at_values
#print axioms KCore.TieE3EqExistsMlAndTerms.owed_rules
#print axioms KCore.TieE3EqExistsMlAndTerms.owed_clauses
#print axioms KCore.TieE3EqExistsMlAndTerms.openDecidedH
#print axioms KCore.TieE3EqExistsMlAndTerms.gammaCl_eq
#print axioms KCore.TieE3EqExistsMlAndTerms.decls_entailed_c
#print axioms KCore.TieE3EqExistsMlAndTerms.nojunk_trivial_entailed_c
#print axioms KCore.TieE3EqExistsMlAndTerms.nojunk_items_entailed_c
#print axioms KCore.TieE3EqExistsMlAndTerms.nojunk_kitem_entailed_c
#print axioms KCore.TieE3EqExistsMlAndTerms.cons_entailed_c
#print axioms KCore.TieE3EqExistsMlAndTerms.idem_refuted_c
#check @KCore.TieE3EqExistsMlAndTerms.fns_account
#check @KCore.TieE3EqExistsMlAndTerms.ex0_differs
#check @KCore.TieE3EqExistsMlAndTerms.ex0_text_shape
#check @KCore.TieE3EqExistsMlAndTerms.ex0_gamma_shape
#check @KCore.TieE3EqExistsMlAndTerms.ex0_guard_r
#check @KCore.TieE3EqExistsMlAndTerms.ex0_nameS
#check @KCore.TieE3EqExistsMlAndTerms.ex0_ltS
#check @KCore.TieE3EqExistsMlAndTerms.ex0_iff
#check @KCore.TieE3EqExistsMlAndTerms.ex0_from_text
#check @KCore.TieE3EqExistsMlAndTerms.ex0_entailed
#check @KCore.TieE3EqExistsMlAndTerms.ex1_differs
#check @KCore.TieE3EqExistsMlAndTerms.ex1_text_shape
#check @KCore.TieE3EqExistsMlAndTerms.ex1_gamma_shape
#check @KCore.TieE3EqExistsMlAndTerms.ex1_guard_r
#check @KCore.TieE3EqExistsMlAndTerms.ex1_nameS
#check @KCore.TieE3EqExistsMlAndTerms.ex1_ltS
#check @KCore.TieE3EqExistsMlAndTerms.ex1_iff
#check @KCore.TieE3EqExistsMlAndTerms.ex1_from_text
#check @KCore.TieE3EqExistsMlAndTerms.ex1_entailed
#check @KCore.TieE3EqExistsMlAndTerms.shape
#check @KCore.TieE3EqExistsMlAndTerms.fns_entailed
#check @KCore.TieE3EqExistsMlAndTerms.fns_from_text
#check @KCore.TieE3EqExistsMlAndTerms.fn_prios
#check @KCore.TieE3EqExistsMlAndTerms.gamma_from
#print axioms KCore.TieE3EqExistsMlAndTerms.fns_account
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_differs
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_text_shape
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_gamma_shape
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_guard_r
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_nameS
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_ltS
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_iff
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_from_text
#print axioms KCore.TieE3EqExistsMlAndTerms.ex0_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_differs
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_text_shape
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_gamma_shape
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_guard_r
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_nameS
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_ltS
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_iff
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_from_text
#print axioms KCore.TieE3EqExistsMlAndTerms.ex1_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.shape
#print axioms KCore.TieE3EqExistsMlAndTerms.fns_entailed
#print axioms KCore.TieE3EqExistsMlAndTerms.fns_from_text
#print axioms KCore.TieE3EqExistsMlAndTerms.fn_prios
#print axioms KCore.TieE3EqExistsMlAndTerms.gamma_from
