/-
  The tie (C14) on `f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore`, the kompiled text of construct fixture e3-ml-eq-rhs-ceil-and
  (`test/constructs/fixtures/e3-ml-eq-rhs-ceil-and`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-eq-rhs-ceil-and`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE3MlEqRhsCeilAnd.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses without an existential variable or a right-side predicate (clausesNoExsTop): the checks outside coreOK read neither (`wfFailing`).
  - The account: the class lists partition the 253 sentences of the user module E3-ML-EQ-RHS-CEIL-AND, in
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
    The consistency section, written by hand, proves what it owes for every H (`openDecidedH`),
    so `Γc` with the step's closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 2 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 2 (204) is not its sentence (`un<j>_differs`) and no reading
    here ties it: the sentence is `uncovered`, and `fns_entailed` and `fns_from_text` leave it out.
    `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 157 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 2 (whose sentence is uncovered), Γ's rule items, the five parts Γ defines by predicates, or
    definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (5);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlEqRhsCeilAnd

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore" module "E3-ML-EQ-RHS-CEIL-AND"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-CEIL-AND")

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
  [(204, "function equation")]

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

/-! ## Consistency for every H: `h(X) => X #And #Ceil(f(X) #And g(X))`, every instance gives X or nothing -/

/- The functions `f` (`f(X) => X requires X >Int 0`) and `g` (`g(X) => 0 -Int X requires X <Int 5`)
have one clause each without an existential variable; `h` has the one clause `clH`, read with the
existential variable #Cut0 of Int (`exs [1]`, `rhs := X`,
`post := ⌈#Cut0⌉ ∧ #Cut0 ∈ f(X) ∧ #Cut0 ∈ g(X)`). `Semantics.FnsNoExs` is false, so neither
`consistent_of_fnFacts` nor the step from `FnObligations` to `FnHyp` applies, and `FnHyp` is proved
here for every H (`fnHypH`).
- A result at every argument: `f(n)` is n at 0 < n and its rest elsewhere (`Semantics.fnRest`, the
  interpretation's value, where the `requires` is false), `g(n)` is `0 -Int n` at n < 5 and its
  rest elsewhere (`CeEx.valF`, `CeEx.valG`, `CeEx.resF`, `CeEx.resG`); `h(n)` is n where some
  integer is both results, and none elsewhere (`CeEx.valueH`).
- Agreement: one clause each (`CeEx.agree_one`).
- Match independence of h's clause, whatever f and g are where their `requires` is false: the right
  side is X, which every instance at a match gives the one value the match gives X, so every
  instance is decided and gives that value (where its `post` is true) or nothing (`CeEx.inst_all`),
  and its `post` is a function of #Cut0's value and the one results of `f(X)` and `g(X)`
  (`CeEx.post_holds`, `CeEx.post_inv`). The clause's one result at a match is that value where one
  instance's `post` holds and none where none does (`CeEx.res_cases`, `CeEx.res_some`). The clauses
  of `f` and `g` have no existential variable and a right side whose one variable is X
  (`CeEx.cohF`, `CeEx.cohG`).
- `OpenDecided` (`openDecidedH`): no condition is owed (`owed_rules`, `owed_clauses`).
- `OpenLaws`: the text has no open generator (`noRaw`).
So Γc with the step's closure has a model for every H (`consistent`, by `consistent_of_fnHyp`).

`CeEx` holds the proofs, over any semantics `d` that reads the clauses (`CeEx.Reads`); the
statements after it are on `cH H`. -/

namespace CeEx

open GroundTerm KCore.Parse

/-! ### Facts shared by the texts of one clause with one existential variable -/

/-- What a semantics reads of its symbols and sorts does not depend on the hook interpretation. -/
theorem isCtor_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isCtor f = d.isCtor f := rfl
theorem isParam_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isParam f = d.isParam f := rfl
theorem isOvl_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isOvl f = d.isOvl f := rfl
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

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

/-- The instances of a clause whose one existential variable is the variable 1: σ with it set. -/
theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

/-- A substitution giving the variable 0 a value of the sort is well sorted. -/
theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

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

/-- A call of a function of the definition at the value of a variable has the function's result there. -/
theorem call_var {f : Sym} (hc : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {i : Nat} {w : GroundTerm} (hl : σ.lookup i = some w) {r : Option GroundTerm} (h : Eval d f [w] r) :
    EvalTerm d σ (.app f [.var i]) r :=
  .call (vs := [w]) hc hh (.cons .var .nil) (by rw [hl]; rfl) h hp

/-- A result of such a call is a result of the function at the variable's value. -/
theorem call_var_inv {f : Sym} (hc : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    (ho : d.isOvl f = false) {i : Nat} {w : GroundTerm} (hl : σ.lookup i = some w) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app f [.var i]) r) : Eval d f [w] r := by
  obtain ⟨rs, hts, hcase⟩ := EvalTerm.call_inv hc hh hp ho h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  rw [hl] at hcase
  rcases hcase with ⟨vs, hvs, hf⟩ | ⟨hn, -⟩
  · obtain rfl : [w] = vs := Option.some.inj hvs
    exact hf
  · cases hn

/-- The value a match of a clause whose one pattern is the variable 0 gives it. -/
theorem pat0 {v : GroundTerm} (hm : PatVals d σ [.var 0] [v]) : σ.lookup 0 = some v := by
  obtain ⟨v', vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

/-- Two matches of patterns `[X]` at one argument list give X one value. -/
theorem pat0_same {σ' : Subst} {vs : List GroundTerm} (hm : PatVals d σ [.var 0] vs)
    (hm' : PatVals d σ' [.var 0] vs) : σ.lookup 0 = σ'.lookup 0 := by
  obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv hm
  obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv hm'
  cases hvs
  exact (PatVal.var_inv hv).trans (PatVal.var_inv hv').symm

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-! ### The reading of this text -/

def fF : Sym := 384
def gS : Sym := 385
def hS : Sym := 386

/-- `f(X) => X requires X >Int 0`. -/
def clFf : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := some (.app intGt [.var 0, .dv Srt.int (.int 0)]),
    rhs := .var 0, ens := none }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clFf] }

/-- `g(X) => 0 -Int X requires X <Int 5`. -/
def clGg : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := some (.app intLt [.var 0, .dv Srt.int (.int 5)]),
    rhs := .app intSub [.dv Srt.int (.int 0), .var 0], ens := none }

def fnG : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clGg] }

/-- `h(X) => X` with `exs = [#Cut0]` and `post := ⌈#Cut0⌉ ∧ #Cut0 ∈ f(X) ∧ #Cut0 ∈ g(X)`, X and #Cut0
of Int. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none, exs := [1],
    post := .and (.ceil Srt.int (.var 1))
      (.and (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app gS [.var 0]))) }

def fnH : Fn := { label := hS, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, each with its one clause. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.symName hS = "Lblh" ∧
    c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" ∧ c.symName intLt = "Lbl'Unds-LT-'Int'Unds'" ∧
    c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ c.sortName Srt.int = "Int" := by decide +kernel

/-- #Cut0 is of the unconfined Int and fixed by `post`: `clausePlainEx` admits h's clause. -/
theorem plainEx : c.clausePlainEx clH = true ∧ c.confined Srt.int = false := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn hS = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem ctors : c.isCtor intGt = false ∧ c.isCtor intLt = false ∧ c.isCtor intSub = false ∧
    c.isCtor fF = false ∧ c.isCtor gS = false := by decide +kernel
theorem fnsPlain : c.isParam fF = false ∧ c.isOvl fF = false ∧ c.isParam gS = false ∧ c.isOvl gS = false := by
  decide +kernel
theorem noRules : c.rules = [] := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-- What a semantics must give for the three clauses to be read in it: `>Int`, `<Int` and `-Int`
the hooks, `f`, `g` and `h` the functions with the clauses `clFf`, `clGg` and `clH`, and the values
of Int its literals. -/
structure Reads (d : Semantics) : Prop where
  gt : d.isCtor intGt = false
  lt : d.isCtor intLt = false
  sub : d.isCtor intSub = false
  fC : d.isCtor fF = false
  fP : d.isParam fF = false
  fO : d.isOvl fF = false
  gC : d.isCtor gS = false
  gP : d.isParam gS = false
  gO : d.isOvl gS = false
  lookF : d.lookupFn fF = some fnF
  lookG : d.lookupFn gS = some fnG
  lookH : d.lookupFn hS = some fnH
  shapes : d.shapesOK = true

/-! ### The clauses in a semantics that reads them -/

section Clause

theorem hooks : isHook intGt = true ∧ isHook intLt = true ∧ isHook intSub = true ∧ isHook fF = false ∧
    isHook gS = false := by decide +kernel

/-- `>Int`, `<Int` and `-Int` at two values of Int, under every interpretation (the comparisons and
the difference of the two integers). -/
theorem hookGt (n : Int) : d.hookRes intGt [int n, int 0] = some (some (bool (decide (n > 0)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl)

theorem hookLt (n : Int) : d.hookRes intLt [int n, int 5] = some (some (bool (decide (n < 5)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intLt]; rfl)

theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value (by rw [hook_intSub]; rfl)

theorem evalGt (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool (decide (n > 0)))) :=
  .hook hd.gt hooks.1 (rs := [σ.lookup 0, some (int 0)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookGt n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalGt_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) r) : r = some (bool (decide (n > 0))) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.gt hooks.1 h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [int n, int 0] (by rw [h0]; rfl)
  rw [hookGt] at this
  exact (Option.some.inj this).symm

theorem evalLt (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intLt [.var 0, .dv Srt.int (.int 5)]) (some (bool (decide (n < 5)))) :=
  .hook hd.lt hooks.2.1 (rs := [σ.lookup 0, some (int 5)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookLt n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalLt_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intLt [.var 0, .dv Srt.int (.int 5)]) r) : r = some (bool (decide (n < 5))) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.lt hooks.2.1 h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [int n, int 5] (by rw [h0]; rfl)
  rw [hookLt] at this
  exact (Option.some.inj this).symm

theorem evalSub (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ (.app intSub [.dv Srt.int (.int 0), .var 0]) (some (int (0 - n))) :=
  .hook hd.sub hooks.2.2.1 (rs := [some (int 0), σ.lookup 0]) (.cons .dv (.cons .var .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookSub n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalSub_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ (.app intSub [.dv Srt.int (.int 0), .var 0]) r) : r = some (int (0 - n)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.sub hooks.2.2.1 h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain rfl := EvalTerm.dv_inv h1
  obtain rfl := EvalTerm.var_inv h2
  have := hh [int 0, int n] (by rw [h0]; rfl)
  rw [hookSub] at this
  exact (Option.some.inj this).symm

theorem bool_ne : (some (bool false) : Option GroundTerm) ≠ some (bool true) := by simp [bool]

/-! #### f and g -/

/-- The one result of `f(n)`: n where 0 < n, and its rest where its `requires` is false. -/
noncomputable def resF (d : Semantics) (n : Int) : Option GroundTerm :=
  if 0 < n then some (int n) else d.fnRest fnF [int n]

/-- The one result of `g(n)`: `0 -Int n` where n < 5, and its rest where its `requires` is false. -/
noncomputable def resG (d : Semantics) (n : Int) : Option GroundTerm :=
  if n < 5 then some (int (0 - n)) else d.fnRest fnG [int n]

theorem clFf_eq {cl : Clause} {fn : Fn} (hd : Reads d) (h1 : d.lookupFn fF = some fn) (h2 : cl ∈ fn.clauses) :
    cl = clFf := by
  rw [hd.lookF] at h1; cases h1; simpa [fnF] using h2

theorem clGg_eq {cl : Clause} {fn : Fn} (hd : Reads d) (h1 : d.lookupFn gS = some fn) (h2 : cl ∈ fn.clauses) :
    cl = clGg := by
  rw [hd.lookG] at h1; cases h1; simpa [fnG] using h2

/-- **`f(n)` has the result `resF d n`.** -/
theorem valF (hd : Reads d) (n : Int) : Eval d fF [int n] (resF d n) := by
  unfold resF
  split
  · next hn =>
    exact .clause (fn := fnF) (cl := clFf) (σ := [(0, int n)]) hd.lookF (List.mem_singleton_self _)
      (sorted1 rfl (rmS_sortOf_int d n)) (.cons (.var rfl) .nil)
      (fun t ht => by
        cases ht
        have h := evalGt hd (σ := [(0, int n)]) (n := n) rfl
        rw [decide_eq_true (show n > 0 from hn)] at h
        exact h)
      .top
      (fun cl' hcl' _ hlt => by
        simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
      rfl .var (fun t ht => nomatch ht) .top
  · next hn =>
    exact .rest hd.lookF fun cl hcl => by
      obtain rfl : cl = clFf := List.mem_singleton.mp hcl
      exact .intro fun σ _ hm => .intro rfl (evalGt hd (pat0 hm))
        (by rw [decide_eq_false (show ¬ n > 0 from hn)]; exact bool_ne)

/-- **`f(n)` has no other result.** -/
theorem aloneF (hd : Reads d) {n : Int} {r : Option GroundTerm} (h : Eval d fF [int n] r) : r = resF d n := by
  unfold resF
  split
  · next hn =>
    cases h with
    | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
      obtain rfl := clFf_eq hd hfn' hmem
      exact (EvalTerm.var_inv hrhs).trans (pat0 hmatch)
    | rest hfn' hnone =>
      rw [hd.lookF] at hfn'; cases hfn'
      cases hnone clFf (List.mem_singleton_self _) with
      | intro hF =>
        have hs : d.WellSorted clFf.vars [(0, int n)] := sorted1 rfl (rmS_sortOf_int d n)
        cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
        | intro ht he hr =>
          cases ht
          exact absurd (by rw [evalGt_inv hd rfl he, decide_eq_true (show n > 0 from hn)]) hr
        | pre hp => cases hp
    | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := clFf_eq hd hfn' hmem; cases ht
    | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := clFf_eq hd hfn' hmem; exact absurd rfl hne
    | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := clFf_eq hd hfn' hmem; exact absurd rfl hne
  · next hn =>
    cases h with
    | clause hfn' hmem _ hmatch hreq _ _ _ _ _ _ =>
      obtain rfl := clFf_eq hd hfn' hmem
      have e := evalGt_inv hd (pat0 hmatch) (hreq _ rfl)
      rw [decide_eq_false (show ¬ n > 0 from hn)] at e
      exact absurd e.symm bool_ne
    | rest hfn' _ => rw [hd.lookF] at hfn'; cases hfn'; rfl
    | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := clFf_eq hd hfn' hmem; cases ht
    | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := clFf_eq hd hfn' hmem; exact absurd rfl hne
    | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := clFf_eq hd hfn' hmem; exact absurd rfl hne

/-- **`g(n)` has the result `resG d n`.** -/
theorem valG (hd : Reads d) (n : Int) : Eval d gS [int n] (resG d n) := by
  unfold resG
  split
  · next hn =>
    exact .clause (fn := fnG) (cl := clGg) (σ := [(0, int n)]) hd.lookG (List.mem_singleton_self _)
      (sorted1 rfl (rmS_sortOf_int d n)) (.cons (.var rfl) .nil)
      (fun t ht => by
        cases ht
        have h := evalLt hd (σ := [(0, int n)]) (n := n) rfl
        rw [decide_eq_true hn] at h
        exact h)
      .top
      (fun cl' hcl' _ hlt => by
        simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
      rfl (evalSub hd rfl) (fun t ht => nomatch ht) .top
  · next hn =>
    exact .rest hd.lookG fun cl hcl => by
      obtain rfl : cl = clGg := List.mem_singleton.mp hcl
      exact .intro fun σ _ hm => .intro rfl (evalLt hd (pat0 hm))
        (by rw [decide_eq_false hn]; exact bool_ne)

/-- **`g(n)` has no other result.** -/
theorem aloneG (hd : Reads d) {n : Int} {r : Option GroundTerm} (h : Eval d gS [int n] r) : r = resG d n := by
  unfold resG
  split
  · next hn =>
    cases h with
    | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
      obtain rfl := clGg_eq hd hfn' hmem
      exact evalSub_inv hd (pat0 hmatch) hrhs
    | rest hfn' hnone =>
      rw [hd.lookG] at hfn'; cases hfn'
      cases hnone clGg (List.mem_singleton_self _) with
      | intro hF =>
        have hs : d.WellSorted clGg.vars [(0, int n)] := sorted1 rfl (rmS_sortOf_int d n)
        cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
        | intro ht he hr =>
          cases ht
          exact absurd (by rw [evalLt_inv hd rfl he, decide_eq_true hn]) hr
        | pre hp => cases hp
    | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := clGg_eq hd hfn' hmem; cases ht
    | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := clGg_eq hd hfn' hmem; exact absurd rfl hne
    | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := clGg_eq hd hfn' hmem; exact absurd rfl hne
  · next hn =>
    cases h with
    | clause hfn' hmem _ hmatch hreq _ _ _ _ _ _ =>
      obtain rfl := clGg_eq hd hfn' hmem
      have e := evalLt_inv hd (pat0 hmatch) (hreq _ rfl)
      rw [decide_eq_false hn] at e
      exact absurd e.symm bool_ne
    | rest hfn' _ => rw [hd.lookG] at hfn'; cases hfn'; rfl
    | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := clGg_eq hd hfn' hmem; cases ht
    | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := clGg_eq hd hfn' hmem; exact absurd rfl hne
    | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := clGg_eq hd hfn' hmem; exact absurd rfl hne

/-- **`clFf` is coherent with itself**: two matches at one argument give X, its right side, one value. -/
theorem cohF : Coherent d clFf clFf :=
  Coherent.of_rhs rfl rfl fun _ _ _ ha ha' _ _ _ => .inl ⟨rfl, fun i hi => by
    have e : varOccs clFf.rhs = [0] := by decide
    rw [e, List.mem_singleton] at hi
    subst hi
    exact pat0_same ha.2.1 ha'.2.1⟩

/-- **`clGg` is coherent with itself**: two matches at one argument give X, the one variable of its
right side, one value. -/
theorem cohG : Coherent d clGg clGg :=
  Coherent.of_rhs rfl rfl fun _ _ _ ha ha' _ _ _ => .inl ⟨rfl, fun i hi => by
    have e : varOccs clGg.rhs = [0] := by decide
    rw [e, List.mem_singleton] at hi
    subst hi
    exact pat0_same ha.2.1 ha'.2.1⟩

/-! #### h -/

/-- The truth value of h's `post` where #Cut0 has the value z and `f(X)`, `g(X)` the results rf, rg:
z is defined and is both. -/
def postVal (z rf rg : Option GroundTerm) : Bool :=
  z.isSome && ((z.isSome && sameResult z rf) && (z.isSome && sameResult z rg))

theorem post_holds (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    Holds d 2 σ clH.post (postVal (σ.lookup 1) (resF d n) (resG d n)) :=
  .and (.ceil .var)
    (.and (.mem .var (call_var hd.fC hooks.2.2.2.1 hd.fP h0 (valF hd n)))
      (.mem .var (call_var hd.gC hooks.2.2.2.2 hd.gP h0 (valG hd n))))

theorem post_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {t : Bool}
    (h : Holds d 2 σ clH.post t) : t = postVal (σ.lookup 1) (resF d n) (resG d n) := by
  cases h with
  | and hc hm =>
    cases hc with
    | ceil hz =>
      cases hm with
      | and hf hg =>
        cases hf with
        | mem hf1 hf2 =>
          cases hg with
          | mem hg1 hg2 =>
            obtain rfl := EvalTerm.var_inv hz
            obtain rfl := EvalTerm.var_inv hf1
            obtain rfl := EvalTerm.var_inv hg1
            obtain rfl := aloneF hd (call_var_inv hd.fC hooks.2.2.2.1 hd.fP hd.fO h0 hf2)
            obtain rfl := aloneG hd (call_var_inv hd.gC hooks.2.2.2.2 hd.gP hd.gO h0 hg2)
            rfl

/-- **Every instance at a match giving X the value n is decided and gives n or nothing**: its right
side is X, and its `post` has a truth value. -/
theorem inst_all (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) : InstIs d σ clH (some (int n)) := by
  cases hb : postVal (σ.lookup 1) (resF d n) (resG d n) with
  | true => exact .gives (h0 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds hd h0) hb)
  | false => exact .fails (post_holds hd h0) (.post (holds_cast (post_holds hd h0) hb))

/-- An instance whose `post` is false gives nothing. -/
theorem inst_none_of (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n))
    (hb : postVal (σ.lookup 1) (resF d n) (resG d n) = false) : InstIs d σ clH none :=
  .fails (post_holds hd h0) (.post (holds_cast (post_holds hd h0) hb))

/-- An instance whose `post` holds does not give nothing. -/
theorem inst_not_none (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n))
    (hp : postVal (σ.lookup 1) (resF d n) (resG d n) = true) : ¬ InstIs d σ clH none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hq => have e := post_inv hd h0 hq; rw [hp] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h0] at e; cases e

theorem agree_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

theorem ext_sorted {n : Int} {w : GroundTerm} (h0 : σ.lookup 0 = some (int n)) (hw : d.sortOf w = some Srt.int) :
    d.WellSorted clH.vars ((1, w) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (rmS_sortOf_int d n) (lkSelf _ _ _) hw

/-- **The results of h's clause at a match giving X the value n**: n, where an integer is both
results, or none, where every instance gives nothing. -/
theorem res_cases (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : Clause.Res d clH σ r) :
    (r = some (int n) ∧ ∃ w, d.sortOf w = some Srt.int ∧ postVal (some w) (resF d n) (resG d n) = true) ∨
    (r = none ∧ ∀ σ', AgreeOff clH.exsFree σ σ' → d.WellSorted clH.vars σ' → InstIs d σ' clH none) := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, ha, hw', ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · have h0' := (agree_x ha).trans h0
    obtain ⟨w, hw1, hws⟩ := hw' 1 Srt.int rfl
    have e := post_inv hd h0' hpost
    rw [hw1] at e
    have e' := EvalTerm.var_inv hrhs
    rw [h0'] at e'
    exact .inl ⟨e', w, hws, e.symm⟩
  · exact .inr ⟨rfl, hall⟩

/-- No match has both an instance whose `post` holds and every instance giving nothing. -/
theorem clash (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {w : GroundTerm}
    (hws : d.sortOf w = some Srt.int) (hp : postVal (some w) (resF d n) (resG d n) = true)
    (hall : ∀ σ', AgreeOff clH.exsFree σ σ' → d.WellSorted clH.vars σ' → InstIs d σ' clH none) : False :=
  inst_not_none hd ((lkNe _ _ (by decide)).trans h0) (by rw [lkSelf]; exact hp)
    (hall _ (agree_set1 σ w) (ext_sorted h0 hws))

/-- **h's clause has a result at every match giving X an integer.** -/
theorem res_some (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) : ∃ r, Clause.Res d clH σ r := by
  by_cases hP : ∃ w, d.sortOf w = some Srt.int ∧ postVal (some w) (resF d n) (resG d n) = true
  · obtain ⟨w, hws, hp⟩ := hP
    have h0' : ((1, w) :: σ : Subst).lookup 0 = some (int n) := (lkNe _ _ (by decide)).trans h0
    exact ⟨_, .inr ⟨by decide, .inl ⟨(1, w) :: σ, int n, agree_set1 σ w, ext_sorted h0 hws,
      ⟨h0' ▸ .var, (fun t ht => nomatch ht), holds_cast (post_holds hd h0') (by rw [lkSelf]; exact hp)⟩,
      fun σ'' ha _ => inst_all hd ((agree_x ha).trans h0), rfl⟩⟩⟩
  · exact ⟨none, .inr ⟨by decide, .inr ⟨rfl, ⟨_, agree_set1 σ (int 0), ext_sorted h0 (rmS_sortOf_int d 0)⟩,
      fun σ' ha hw => by
        obtain ⟨w, hw1, hws⟩ := hw 1 Srt.int rfl
        refine inst_none_of hd ((agree_x ha).trans h0) ?_
        rw [hw1]
        exact Bool.eq_false_iff.mpr fun hp => hP ⟨w, hws, hp⟩⟩⟩⟩

/-- The value a match of h's clause gives X is an integer. -/
theorem applies_x (hd : Reads d) {vs : List GroundTerm} (h : clH.AppliesAt d σ vs) :
    ∃ n, σ.lookup 0 = some (int n) := by
  obtain ⟨w, hw, hws⟩ := h.1 0 (by decide) Srt.int rfl
  obtain ⟨n, rfl⟩ := shape_int hd.shapes hws
  exact ⟨n, hw⟩

/-- **h's clause is match independent**: two matches at one argument list give X one value n, and
the clause's results there are n or none, never both; where it decides, it has a result. -/
theorem matchH (hd : Reads d) : MatchIndependent d clH := by
  refine ⟨fun vs σ σ' ha ha' _ _ _ _ _ => .inr fun r r' hr hr' => ?_, fun _ _ _ _ σ _ _ hdec => ?_⟩
  · obtain ⟨n, hb⟩ := applies_x hd ha
    have hb' : σ'.lookup 0 = some (int n) := (pat0_same ha'.2.1 ha.2.1).trans hb
    rcases res_cases hd hb hr with ⟨rfl, w, hws, hp⟩ | ⟨rfl, hall⟩ <;>
    rcases res_cases hd hb' hr' with ⟨rfl, w', hws', hp'⟩ | ⟨rfl, hall'⟩
    · rfl
    · exact (clash hd hb' hws hp hall').elim
    · exact (clash hd hb hws' hp' hall).elim
    · rfl
  · obtain ⟨n, hb⟩ := applies_x hd hdec.1
    exact res_some hd hb

/-- **`h(n)` has a result**: n by `Eval.clauseEx` where an integer is both `f(n)` and `g(n)`, and
none by `Eval.exNone` elsewhere. -/
theorem valueH (hd : Reads d) (n : Int) : ∃ r, Eval d hS [int n] r := by
  by_cases hP : ∃ w, d.sortOf w = some Srt.int ∧ postVal (some w) (resF d n) (resG d n) = true
  · obtain ⟨w, hws, hp⟩ := hP
    have h0 : ([(1, w), (0, int n)] : Subst).lookup 0 = some (int n) := rfl
    exact ⟨_, .clauseEx (fn := fnH) (cl := clH) (σ := [(1, w), (0, int n)]) hd.lookH (List.mem_singleton_self _)
      (sorted2 rfl (rmS_sortOf_int d n) rfl hws) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
      (fun cl' hcl' _ hlt => by
        simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
      (by decide) (h0 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds hd h0) hp)
      (fun σ' ha _ => inst_all hd ((agree_x ha).trans h0))⟩
  · have hs : d.WellSorted clH.vars [(1, int 0), (0, int n)] :=
      sorted2 rfl (rmS_sortOf_int d n) rfl (rmS_sortOf_int d 0)
    exact ⟨_, .exNone (fn := fnH) (cl := clH) (σ := [(1, int 0), (0, int n)]) hd.lookH (List.mem_singleton_self _)
      (by decide) (hs.at _) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
      (fun cl' hcl' _ hlt => by
        simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
      ⟨_, fun _ _ => rfl, hs⟩
      (fun σ' ha hw => by
        obtain ⟨w, hw1, hws⟩ := hw 1 Srt.int rfl
        refine inst_none_of hd ((agree_x ha).trans rfl) ?_
        rw [hw1]
        exact Bool.eq_false_iff.mpr fun hp => hP ⟨w, hws, hp⟩)⟩

/-- **`FnHyp`** of a semantics whose functions are `f`, `g` and `h` with these clauses, without
rules and open generators, where the values of Int are its literals. -/
theorem fnHyp_of (hd : Reads d) (hfns : d.fns = [fnF, fnG, fnH]) (hrules : d.rules = [])
    (hraw : ∀ k ∈ d.params, k.raw = false) : FnHyp d := by
  have hmem : ∀ {fn}, fn ∈ d.fns → fn = fnF ∨ fn = fnG ∨ fn = fnH := fun h => by rw [hfns] at h; simpa using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf ht => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecided_of_plain (fun r hr => by rw [hrules] at hr; cases hr) (fun fn hf cl hcl => ?_),
    openLaws_of_plain hraw⟩
  · rcases hmem hf with rfl | rfl | rfl
    · obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
      obtain ⟨n, rfl⟩ := shape_int hd.shapes hw
      exact ⟨_, valF hd n⟩
    · obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
      obtain ⟨n, rfl⟩ := shape_int hd.shapes hw
      exact ⟨_, valG hd n⟩
    · obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
      obtain ⟨n, rfl⟩ := shape_int hd.shapes hw
      exact valueH hd n
  · rcases hmem hf with rfl | rfl | rfl <;> cases ht
  · rcases hmem hf with rfl | rfl | rfl <;> exact agree_one rfl
  · rcases hmem hf with rfl | rfl | rfl
    · obtain rfl : cl = clFf := List.mem_singleton.mp hcl
      exact (matchIndependent_iff_noExs rfl).mpr cohF
    · obtain rfl : cl = clGg := List.mem_singleton.mp hcl
      exact (matchIndependent_iff_noExs rfl).mpr cohG
    · obtain rfl : cl = clH := List.mem_singleton.mp hcl
      exact matchH hd
  · rcases hmem hf with rfl | rfl | rfl
    · obtain rfl : cl = clFf := List.mem_singleton.mp hcl
      rfl
    · obtain rfl : cl = clGg := List.mem_singleton.mp hcl
      rfl
    · obtain rfl : cl = clH := List.mem_singleton.mp hcl
      rfl

end Clause

end CeEx

/-! ### The facts the deciders name -/

def callOrder : List Nat := [CeEx.fF, CeEx.gS, CeEx.hS]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause whose match independence no decider confirms: `h`'s. -/
theorem match_named : c.matchObligationsL = [(CeEx.hS, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-! ### `FnHyp` and consistency, for every H -/

theorem readsH (H : HookParams) : CeEx.Reads (cH H) where
  gt := (CeEx.isCtor_wh c H _).trans CeEx.ctors.1
  lt := (CeEx.isCtor_wh c H _).trans CeEx.ctors.2.1
  sub := (CeEx.isCtor_wh c H _).trans CeEx.ctors.2.2.1
  fC := (CeEx.isCtor_wh c H _).trans CeEx.ctors.2.2.2.1
  fP := (CeEx.isParam_wh c H _).trans CeEx.fnsPlain.1
  fO := (CeEx.isOvl_wh c H _).trans CeEx.fnsPlain.2.1
  gC := (CeEx.isCtor_wh c H _).trans CeEx.ctors.2.2.2.2
  gP := (CeEx.isParam_wh c H _).trans CeEx.fnsPlain.2.2.1
  gO := (CeEx.isOvl_wh c H _).trans CeEx.fnsPlain.2.2.2
  lookF := by rw [Semantics.lookupFn_withHooks]; exact CeEx.lookupF
  lookG := by rw [Semantics.lookupFn_withHooks]; exact CeEx.lookupG
  lookH := by rw [Semantics.lookupFn_withHooks]; exact CeEx.lookupH
  shapes := (CeEx.shapesOK_wh c H).trans CeEx.shapes

/-- **`FnHyp` holds, for every H.** -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  CeEx.fnHyp_of (readsH H) ((CeEx.fns_wh c H).trans CeEx.read) ((CeEx.rules_wh c H).trans CeEx.noRules)
    (fun k hk => noRaw k ((CeEx.params_wh c H) ▸ hk))

/-- **The clause `match_named` names is match independent, for every H**, whatever the rests of `f`
and `g` are. -/
theorem matchH (H : HookParams) : MatchIndependent (cH H) CeEx.clH :=
  (fnHypH H).2.2.2.1 CeEx.fnH
    (by rw [(CeEx.fns_wh c H).trans CeEx.read]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _)))
    CeEx.clH (List.mem_singleton_self _)

/-- **`f(n)` and `g(n)` have their one result, for every H.** -/
theorem f_result (H : HookParams) (n : Int) {r : Option GroundTerm} :
    Eval (cH H) CeEx.fF [int n] r ↔ r = CeEx.resF (cH H) n :=
  ⟨CeEx.aloneF (readsH H), fun h => h ▸ CeEx.valF (readsH H) n⟩
theorem g_result (H : HookParams) (n : Int) {r : Option GroundTerm} :
    Eval (cH H) CeEx.gS [int n] r ↔ r = CeEx.resG (cH H) n :=
  ⟨CeEx.aloneG (readsH H), fun h => h ▸ CeEx.valG (readsH H) n⟩

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


/-! ## Function equations (30 sentences) and priority equations (0 sentences)

Γ's item 2 (sentence 204) is not its sentence (`un<j>_differs`), and no reading here gives it from
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

/-- Γ's item 2 (sentence 204): no reading here ties it. -/
noncomputable def unItem2 : P := (TiePair.gammaPats c).getD 2 ⊥
theorem unItem2_at : (TiePair.gammaPats c)[2]? = some unItem2 := by decide +kernel
kernel_rfl fnText_at2 : fnText[2]? = some U.ax204
/-- **Γ's item 2 is not the text's sentence 204** (kernel): the sentence is uncovered. -/
theorem un2_differs : unItem2 ≠ (trS U.ax204).pat := by decide +kernel

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 2. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 2 unItem2

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

/-- **E for the function equations**: Γ entails each sentence of `fnText` but the untied ones (items 2), for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([2] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  intro M _ I hI
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn')) hI

/-- **The converse for `fnItems`**: each item but the untied ones (items 2) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
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

end KCore.TieE3MlEqRhsCeilAnd

#check @KCore.TieE3MlEqRhsCeilAnd.noRaw
#check @KCore.TieE3MlEqRhsCeilAnd.readsConfined_c
#check @KCore.TieE3MlEqRhsCeilAnd.userAxioms_eq
#check @KCore.TieE3MlEqRhsCeilAnd.coreOK
#check @KCore.TieE3MlEqRhsCeilAnd.account
#check @KCore.TieE3MlEqRhsCeilAnd.account_sizes
#check @KCore.TieE3MlEqRhsCeilAnd.account_classes
#check @KCore.TieE3MlEqRhsCeilAnd.account_absent
#check @KCore.TieE3MlEqRhsCeilAnd.absent_closed
#check @KCore.TieE3MlEqRhsCeilAnd.absent_proj_below_c
#check @KCore.TieE3MlEqRhsCeilAnd.absent_proj_below
#check @KCore.TieE3MlEqRhsCeilAnd.lists_in_account
#check @KCore.TieE3MlEqRhsCeilAnd.attrs_agree
#check @KCore.TieE3MlEqRhsCeilAnd.sig_origin_but_next
#check @KCore.TieE3MlEqRhsCeilAnd.decls_entailed
#check @KCore.TieE3MlEqRhsCeilAnd.consistent
#check @KCore.TieE3MlEqRhsCeilAnd.text_nextless
#check @KCore.TieE3MlEqRhsCeilAnd.nojunk_trivial_entailed
#check @KCore.TieE3MlEqRhsCeilAnd.nojunk_items_entailed
#check @KCore.TieE3MlEqRhsCeilAnd.nojunk_kitem_entailed
#check @KCore.TieE3MlEqRhsCeilAnd.cons_entailed
#check @KCore.TieE3MlEqRhsCeilAnd.idem_refuted
#check @KCore.TieE3MlEqRhsCeilAnd.lib166
#check @KCore.TieE3MlEqRhsCeilAnd.lib166_at_values
#check @KCore.TieE3MlEqRhsCeilAnd.owed_rules
#check @KCore.TieE3MlEqRhsCeilAnd.owed_clauses
#check @KCore.TieE3MlEqRhsCeilAnd.openDecidedH
#check @KCore.TieE3MlEqRhsCeilAnd.gammaCl_eq
#check @KCore.TieE3MlEqRhsCeilAnd.decls_entailed_c
#check @KCore.TieE3MlEqRhsCeilAnd.nojunk_trivial_entailed_c
#check @KCore.TieE3MlEqRhsCeilAnd.nojunk_items_entailed_c
#check @KCore.TieE3MlEqRhsCeilAnd.nojunk_kitem_entailed_c
#check @KCore.TieE3MlEqRhsCeilAnd.cons_entailed_c
#check @KCore.TieE3MlEqRhsCeilAnd.idem_refuted_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.noRaw
#print axioms KCore.TieE3MlEqRhsCeilAnd.readsConfined_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.userAxioms_eq
#print axioms KCore.TieE3MlEqRhsCeilAnd.coreOK
#print axioms KCore.TieE3MlEqRhsCeilAnd.account
#print axioms KCore.TieE3MlEqRhsCeilAnd.account_sizes
#print axioms KCore.TieE3MlEqRhsCeilAnd.account_classes
#print axioms KCore.TieE3MlEqRhsCeilAnd.account_absent
#print axioms KCore.TieE3MlEqRhsCeilAnd.absent_closed
#print axioms KCore.TieE3MlEqRhsCeilAnd.absent_proj_below_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.absent_proj_below
#print axioms KCore.TieE3MlEqRhsCeilAnd.lists_in_account
#print axioms KCore.TieE3MlEqRhsCeilAnd.attrs_agree
#print axioms KCore.TieE3MlEqRhsCeilAnd.sig_origin_but_next
#print axioms KCore.TieE3MlEqRhsCeilAnd.decls_entailed
#print axioms KCore.TieE3MlEqRhsCeilAnd.consistent
#print axioms KCore.TieE3MlEqRhsCeilAnd.text_nextless
#print axioms KCore.TieE3MlEqRhsCeilAnd.nojunk_trivial_entailed
#print axioms KCore.TieE3MlEqRhsCeilAnd.nojunk_items_entailed
#print axioms KCore.TieE3MlEqRhsCeilAnd.nojunk_kitem_entailed
#print axioms KCore.TieE3MlEqRhsCeilAnd.cons_entailed
#print axioms KCore.TieE3MlEqRhsCeilAnd.idem_refuted
#print axioms KCore.TieE3MlEqRhsCeilAnd.lib166
#print axioms KCore.TieE3MlEqRhsCeilAnd.lib166_at_values
#print axioms KCore.TieE3MlEqRhsCeilAnd.owed_rules
#print axioms KCore.TieE3MlEqRhsCeilAnd.owed_clauses
#print axioms KCore.TieE3MlEqRhsCeilAnd.openDecidedH
#print axioms KCore.TieE3MlEqRhsCeilAnd.gammaCl_eq
#print axioms KCore.TieE3MlEqRhsCeilAnd.decls_entailed_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.nojunk_trivial_entailed_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.nojunk_items_entailed_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.nojunk_kitem_entailed_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.cons_entailed_c
#print axioms KCore.TieE3MlEqRhsCeilAnd.idem_refuted_c
#check @KCore.TieE3MlEqRhsCeilAnd.fns_account
#check @KCore.TieE3MlEqRhsCeilAnd.un2_differs
#check @KCore.TieE3MlEqRhsCeilAnd.shape
#check @KCore.TieE3MlEqRhsCeilAnd.fns_entailed
#check @KCore.TieE3MlEqRhsCeilAnd.fns_from_text
#check @KCore.TieE3MlEqRhsCeilAnd.fn_prios
#check @KCore.TieE3MlEqRhsCeilAnd.gamma_from
#print axioms KCore.TieE3MlEqRhsCeilAnd.fns_account
#print axioms KCore.TieE3MlEqRhsCeilAnd.un2_differs
#print axioms KCore.TieE3MlEqRhsCeilAnd.shape
#print axioms KCore.TieE3MlEqRhsCeilAnd.fns_entailed
#print axioms KCore.TieE3MlEqRhsCeilAnd.fns_from_text
#print axioms KCore.TieE3MlEqRhsCeilAnd.fn_prios
#print axioms KCore.TieE3MlEqRhsCeilAnd.gamma_from
