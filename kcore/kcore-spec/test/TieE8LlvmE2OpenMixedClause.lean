/-
  The tie (C14) on `f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore`, the kompiled text of construct fixture e8-llvm-e2-open-mixed-clause
  (`test/constructs/fixtures/e8-llvm-e2-open-mixed-clause`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e8-llvm-e2-open-mixed-clause`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE8LlvmE2OpenMixedClause.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `coreOK`: `coreOK`; `wf` fails at the conjuncts clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate (`wfFailing`).
  - The account: the class lists partition the 148 sentences of the user module E2-OPEN-MIXED-CLAUSE, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the open
    generator `and` is a parameter declared without `hook` and without `function`, of which the
    text states no equation.
  - `sig_origin_but_next`: each of the 211 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`); its one open generator is `and`
    (`params_raw`), of B.
    The consistency section, written by hand, states that `Γc` with the step's closure has a model at
    `lawHooks c H` for every H (`consistent_lawHooks`), and states `consistent` under the hypotheses on
    H it names; `FnHyp` is owed. `lawHooks c H` satisfies the laws (`lawHooks_laws`) and is admitted by
    the library's sentences wherever H is (`libAdmitted_lawHooks`), so `lawHooks c HookParams.lib`
    satisfies the laws, the open generators' `functional` sentences and the library's sentences together
    (`lawHooks_lib`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (32) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (100) is not its sentence (`un<j>_differs`) and no reading
    here ties it: the sentence is `uncovered`, and `fns_entailed` and `fns_from_text` leave it out.
    `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Constructor sentences (29): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 8 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (48): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence is uncovered), Γ's rule items, the five parts Γ defines by predicates, or
    definedness (`gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (not stated here; no theorem); open generator functional: owed as `OpenTotal`
    (`open_functional_not_item`); no direction: `absent_closed`.

  `and`'s functional sentence (56) is no item of Γ and is owed at values as `OpenTotal`
  (`open_functional_not_item`); the account holds it in `open generator functional`, of the
  direction `hypothesis`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (19);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE8LlvmE2OpenMixedClause

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"
definition_of defn from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"
user_axioms U from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore" module "E2-OPEN-MIXED-CLAUSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `and`, the text's one open generator (`raw`), and B, its sort. -/
def and : Sym := 389
def b : Srt := 32

theorem names : c.symName and = "Lbland" ∧ c.sortName b = "B" := by decide +kernel

/-- **The definition's one open generator is `and`**, of B, `assoc` false and `idem` false. -/
theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =
    [(and, [33, 33], b, false, false)] := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-OPEN-MIXED-CLAUSE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 148 := by decide +kernel

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
  [("function equation", [100, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
      122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 76, 77, 84, 86]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30]),
   ("distinctness", [85]),
   ("no junk", [87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]),
   ("function functional", [59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 39, 43, 51, 52, 53, 54, 55, 58, 75, 78, 79, 80, 81, 82]),
   ("collection law", [40, 41, 42, 44, 45, 46, 47, 49, 50]),
   ("library", [99, 151]),
   ("set idempotence", [48]),
   ("set-variable lemma", []),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", [56]),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [37, 38, 57, 83, 101, 102, 103, 104, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
      147, 148, 149, 150])]

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
    [("function equation", 32), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 8), ("subsort", 16), ("injectivity", 4), ("distinctness", 1), ("no junk", 12), ("function functional", 16), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 0), ("function law", 0), ("open generator law", 0), ("open generator functional", 1), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 23)] := by
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
  [(136, "A"), (137, "B"), (138, "Bool"), (139, "GeneratedCounterCell"),
   (140, "GeneratedCounterCellOpt"), (141, "GeneratedTopCell"), (142, "GeneratedTopCellFragment"),
   (143, "Int"), (144, "K"), (145, "KCell"), (146, "KCellOpt"), (147, "KItem"), (148, "List"),
   (149, "Map"), (150, "Set")]

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
  [(10, "subsort"), (18, "subsort"), (56, "open generator functional"),
   (59, "function functional"), (60, "function functional"), (84, "constructor functional"),
   (85, "distinctness"), (86, "constructor functional"), (87, "no junk"), (88, "no junk"),
   (98, "no junk"), (100, "function equation"), (104, "no direction"), (105, "function equation"),
   (106, "function equation"), (107, "function equation"), (108, "function equation"),
   (136, "no direction"), (137, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(100, "function equation")]

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. The open generator `and` is a parameter (`raw`) that no
registry hook interprets, declared without `hook` and without `function`, and the text states
no equation of it (`AttrsAgree.eqnsOf`), which `AttrsAgree.hooks` admits. -/
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

theorem sig_sizes : (sigItems c).length = 211 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (17, 16, 91, 60, 4, 27) := by
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

/-! ## `lawHooks c H`: the open generator's laws and the library's sentences -/

/-- **`lawHooks c H` satisfies the laws and gives each open generator a value at every argument list**, for every H. -/
theorem lawHooks_laws (H : HookParams) :
    OpenLaws (c.withHooks (lawHooks c H)) ∧ OpenTotal (c.withHooks (lawHooks c H)) :=
  ⟨openLaws_lawHooks c coreOK H, openTotal_lawHooks c coreOK H⟩

/-- **`lawHooks c H` is admitted by the library's sentences wherever H is and gives `_RangeMap_`
no value**, for every H (`KCore.libAdmitted_lawHooks`). -/
theorem libAdmitted_lawHooks (H : HookParams) (ha : (c.withHooks H).libAdmitted)
    (hrm : ∀ vs, H.app rmConcat vs = none) : (c.withHooks (lawHooks c H)).libAdmitted :=
  KCore.libAdmitted_lawHooks c coreOK H ha hrm

/-- **`lawHooks c HookParams.lib` satisfies the laws, the open generators' `functional` sentences
and the library's sentences together.** -/
theorem lawHooks_lib :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted :=
  ⟨(lawHooks_laws HookParams.lib).1, (lawHooks_laws HookParams.lib).2,
    libAdmitted_lawHooks HookParams.lib (libAdmitted_lib_of_coreOK coreOK) lib_app_rmConcat_none⟩

/-! ## Consistency: exactly at the interpretations where `and` determines its first argument -/

/- The text's sentences about `and` are its `functional` sentence, B's no junk (every element of B
is an `and(X0, X1)`) and the equation `first(X0) = X` under `X0 ∈ and(X, _Gen0)`; A's two
generators `x` and `y` are apart (the text's no-confusion sentence). The text states no law of
`and`. In a model of these, `and(a, g) = and(a', g')` gives `first` of that element both `a` and
`a'`, so `a = a'`: every model of the text keeps `and(x, y)` and `and(y, x)` apart. The text has
models (B the pairs of A, `first` the first projection).

`Γ (cH H)` holds the graph of `and` that H gives at values. So `Γc (cH H)` with the step's closure
has a model exactly where that graph determines the first argument (`FirstDet H`, `consistent_iff`):
- where it does not, at one pair of argument lists with one value and first arguments apart,
  `first` at that value evaluates to both first arguments (`eval_first`), each of which the
  application denotes in a model of `Γc` (`eval_den4_coreCl`), and two values of A denote apart
  (`no_model_of_clash`, `not_consistent_of_clash`). `Hswap`, which gives `and(x, y)` the value
  `and(y, x)` and leaves the other applications free, is such an H (`not_consistent_swap`), so no
  statement of consistency holds for every H (`not_consistent_all`);
- where it does, the clause of `first` is coherent with itself (`first_coherent`), which is the one
  fact the deciders leave (`first_match_named`), so `FnHyp` holds (`first_fnHyp`) and the theory has
  a model (`consistent`).
`lawHooks c H` gives `and` its free applications (`lawHooks_and`), which determine their arguments
(`firstDet_lawHooks`): the theory has a model there for every H (`consistent_lawHooks`). -/

def firstS : Sym := 388
def xS : Sym := 386
def yS : Sym := 387
def aSrt : Srt := 33

theorem first_names : c.symName firstS = "Lblfirst" ∧ c.symName xS = "Lblx" ∧ c.symName yS = "Lbly" ∧
    c.sortName aSrt = "A" := by decide +kernel

/-! ### The clause of `first` and the parameter `and` -/

/-- `first(V) => X` with the predicate `V ∈ and(X, G)`; X and G of A, V of B. -/
def clFirst : Clause :=
  { vars := [aSrt, aSrt, b], pats := [.var 2], req := none, rhs := .var 0, ens := none,
    pre := .mem b (.var 2) (.app and [.var 0, .var 1]) }
def fFirst : Fn := { label := firstS, args := [b], result := aSrt, clauses := [clFirst] }

theorem first_text : c.fns = [fFirst] := by rfl
theorem first_lookupH (H : HookParams) : (cH H).lookupFn firstS = some fFirst := by rfl

/-- `and` as the definition's parameter: open, with no law. -/
def andK : ParamSig := { sig := ⟨and, [aSrt, aSrt], b⟩, raw := true }

theorem andK_mem : andK ∈ c.params := by decide +kernel
theorem and_syms : c.isCtor and = false ∧ isHook and = false ∧ c.isParam and = true := by decide +kernel

theorem andK_shape (H : HookParams) : LawShape (cH H) andK :=
  Semantics.lawShape_core (coreOKH H) andK andK_mem rfl

/-- **The value of `and` at H**: what H gives, the application itself where H gives nothing, kept
where it is a value of B. -/
theorem and_paramVal (H : HookParams) {vs : List GroundTerm} {v : GroundTerm} :
    (cH H).paramVal and vs = some v ↔ v = (H.app and vs).getD (.ctor and vs) ∧ (cH H).sortOf v = some b :=
  paramVal_raw_sorted (c := cH H) (f := and) (k := andK) (andK_shape H).1 rfl (andK_shape H).2.2.1

/-- **An application of `and` is a value at H** where its arguments are values of A and H leaves it
as it is; it is then of B. -/
theorem and_value (H : HookParams) {ts : List GroundTerm} {s : Srt} :
    (cH H).sortOf (.ctor and ts) = some s ↔
      (cH H).sortsOf ts = some [aSrt, aSrt] ∧ (cH H).keepsRaw and ts = true ∧ s = b :=
  Semantics.sortOf_open_iff (c := cH H) (f := and) (k := andK) (andK_shape H).2.1 (andK_shape H).2.2.2.1
    (andK_shape H).2.2.2.2.1

theorem first_srt1 {C : Semantics} {v : GroundTerm} {s : Srt} (h : C.sortOf v = some s) :
    C.sortsOf [v] = some [s] :=
  sortsOf_cons.mpr ⟨s, [], h, sortsOf_nil, rfl⟩

theorem first_srt2 {C : Semantics} {v w : GroundTerm} {s t : Srt} (h1 : C.sortOf v = some s)
    (h2 : C.sortOf w = some t) : C.sortsOf [v, w] = some [s, t] :=
  sortsOf_cons.mpr ⟨s, [t], h1, first_srt1 h2, rfl⟩

/-- **The hypothesis on H**: the values H gives `and` at values of A determine the first argument. -/
def FirstDet (H : HookParams) : Prop :=
  ∀ a g a' g' v : GroundTerm, (cH H).sortOf a = some aSrt → (cH H).sortOf g = some aSrt →
    (cH H).sortOf a' = some aSrt → (cH H).sortOf g' = some aSrt →
    (cH H).paramVal and [a, g] = some v → (cH H).paramVal and [a', g'] = some v → a = a'

/-! ### `first` at a value of `and` -/

/-- `X ↦ a, G ↦ g, V ↦ v`. -/
def σFirst (a g v : GroundTerm) : Subst := [(0, a), (1, g), (2, v)]

theorem first_sorted (H : HookParams) {a g v : GroundTerm} (ha : (cH H).sortOf a = some aSrt)
    (hg : (cH H).sortOf g = some aSrt) (hp : (cH H).paramVal and [a, g] = some v) :
    (cH H).WellSorted clFirst.vars (σFirst a g v) := by
  have hv := ((and_paramVal H).mp hp).2
  intro i s hs
  match i, hs with
  | 0, hs =>
    obtain rfl : aSrt = s := by simpa [clFirst] using hs
    exact ⟨a, rfl, ha⟩
  | 1, hs =>
    obtain rfl : aSrt = s := by simpa [clFirst] using hs
    exact ⟨g, rfl, hg⟩
  | 2, hs =>
    obtain rfl : b = s := by simpa [clFirst] using hs
    exact ⟨v, rfl, hv⟩
  | n + 3, hs => simp [clFirst] at hs

/-- The predicate `V ∈ and(X, G)` at `σFirst a g v`, where `and(a, g)` is `v`: true. -/
theorem first_pre (H : HookParams) {a g v : GroundTerm} (hp : (cH H).paramVal and [a, g] = some v) :
    Holds (cH H) clFirst.vars.length (σFirst a g v) clFirst.pre true := by
  have h := Holds.mem (c := cH H) (n := clFirst.vars.length) (σ := σFirst a g v) (s := b)
    (EvalTerm.var (i := 2))
    (EvalTerm.param (f := and) (ts := [.var 0, .var 1]) and_syms.1 and_syms.2.1 and_syms.2.2
      (.cons (.var (i := 0)) (.cons (.var (i := 1)) .nil)) rfl)
  have e : (((σFirst a g v).lookup 2).isSome && sameResult ((σFirst a g v).lookup 2)
      ((allSome [(σFirst a g v).lookup 0, (σFirst a g v).lookup 1]).bind ((cH H).paramVal and))) = true := by
    show ((some v).isSome && sameResult (some v) ((cH H).paramVal and [a, g])) = true
    rw [hp]
    simp [sameResult, GroundTerm.cmp_refl]
  rw [e] at h
  exact h

/-- **Where `and(a, g)` is `v` at H, `first(v)` evaluates to `a`**, by the clause at `σFirst a g v`. -/
theorem eval_first (H : HookParams) {a g v : GroundTerm} (ha : (cH H).sortOf a = some aSrt)
    (hg : (cH H).sortOf g = some aSrt) (hp : (cH H).paramVal and [a, g] = some v) :
    Eval (cH H) firstS [v] (some a) :=
  .clause (cl := clFirst) (σ := σFirst a g v) (first_lookupH H) (List.mem_singleton_self _)
    (first_sorted H ha hg hp) (.cons (.var rfl) .nil) (fun _ ht => by cases ht) (first_pre H hp)
    (fun cl' hcl' _ hlt => by
      have hcl : cl' = clFirst := by simpa [fFirst] using hcl'
      subst hcl
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun _ ht => by cases ht) .top

/-! ### No model where two applications with first arguments apart have one value -/

theorem first_owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem first_owed_clauses : c.owedClauses = ([] : List (Nat × Nat)) := by decide +kernel

/-- No clause's condition is owed, under every H. -/
theorem first_noWit (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) :=
  openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, first_owed_clauses]; intro p hp; cases hp)

theorem first_noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)
theorem first_noExsH (H : HookParams) : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr first_noExs

/-- **`Γc (cH H)` has no model where H gives `and(a, g)` and `and(a', g')` one value with `a` and
`a'` apart**: `first` of that value denotes the element of `a` and the element of `a'`. -/
theorem no_model_of_clash (H : HookParams) {a g a' g' v : GroundTerm}
    (ha : (cH H).sortOf a = some aSrt) (hg : (cH H).sortOf g = some aSrt)
    (ha' : (cH H).sortOf a' = some aSrt) (hg' : (cH H).sortOf g' = some aSrt)
    (hp : (cH H).paramVal and [a, g] = some v) (hp' : (cH H).paramVal and [a', g'] = some v) (hne : a ≠ a') :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc (cH H)) := by
  intro M _ I hIc
  obtain ⟨hok, hsr, hnn, hgw, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have F := HoldsShape.nodeFacts_of_core (coreOKH H) hIc
  have hws : (cH H).sortsOf [v] = some fFirst.args := first_srt1 ((and_paramVal H).mp hp).2
  have hden := fun (r : Option GroundTerm) (hev : Eval (cH H) firstS [v] r) (e : Valuation M) (m : M) =>
    eval_den4_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (first_noExsH H)) hsr
      (Semantics.coreOK_parts (coreOKH H)).2.1 hph (first_noWit H)
      (HoldsShape.preReadAll_of_core (coreOKH H) hIc) hev (first_lookupH H) hws e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨m, hm, -⟩ := F.val ha [] e
  have h1 := (hden _ (eval_first H ha hg hp) e m).mpr ((hm m).mpr rfl)
  have h2 := (hden _ (eval_first H ha' hg' hp') e m).mp h1
  exact hne (F.apart ha ha' e m ((hm m).mpr rfl) h2)

/-- **Not `Consistent` there.** -/
theorem not_consistent_of_clash (H : HookParams) {a g a' g' v : GroundTerm}
    (ha : (cH H).sortOf a = some aSrt) (hg : (cH H).sortOf g = some aSrt)
    (ha' : (cH H).sortOf a' = some aSrt) (hg' : (cH H).sortOf g' = some aSrt)
    (hp : (cH H).paramVal and [a, g] = some v) (hp' : (cH H).paramVal and [a', g'] = some v) (hne : a ≠ a') :
    ¬ Consistent (cH H) := fun ⟨M, hM, I, hI⟩ =>
  no_model_of_clash H ha hg ha' hg' hp hp' hne M hM I (fun φ hφ => hI φ (Or.inl hφ))

/-- **A model at H makes `and` determine its first argument.** -/
theorem firstDet_of_consistent (H : HookParams) (hc : Consistent (cH H)) : FirstDet H :=
  fun _ _ _ _ _ ha hg ha' hg' hp hp' =>
    Classical.byContradiction fun hne => not_consistent_of_clash H ha hg ha' hg' hp hp' hne hc

/-! ### An interpretation without a model -/

def xT : GroundTerm := .ctor xS []
def yT : GroundTerm := .ctor yS []

theorem xy_data : c.rawFree xT = true ∧ c.rawFree yT = true ∧ c.sortOf xT = some aSrt ∧
    c.sortOf yT = some aSrt := by decide +kernel

/-- `x` and `y` are values of A under every H. -/
theorem xy_sorts (H : HookParams) : (cH H).sortOf xT = some aSrt ∧ (cH H).sortOf yT = some aSrt :=
  ⟨(Semantics.sortOf_withHooks_rawFree c H xy_data.1).trans xy_data.2.2.1,
   (Semantics.sortOf_withHooks_rawFree c H xy_data.2.1).trans xy_data.2.2.2⟩

/-- `and(x, y) ↦ and(y, x)`, and nothing elsewhere: `and(y, x)` stays the application, so the two
have one value. -/
def Hswap : HookParams :=
  ⟨fun f vs => if f = and then
      (match vs with
        | [.ctor p [], .ctor q []] => if p = xS ∧ q = yS then some (.ctor and [yT, xT]) else none
        | _ => none)
    else none⟩

theorem swap_app : Hswap.app and [xT, yT] = some (.ctor and [yT, xT]) ∧ Hswap.app and [yT, xT] = none :=
  ⟨rfl, rfl⟩

/-- `and(y, x)` is a value of B at `Hswap`. -/
theorem swap_sort : (cH Hswap).sortOf (.ctor and [yT, xT]) = some b :=
  (and_value Hswap).mpr ⟨first_srt2 (xy_sorts Hswap).2 (xy_sorts Hswap).1,
    (by simp [Semantics.keepsRaw, Semantics.withHooks, swap_app.2]), rfl⟩

theorem swap_val : (cH Hswap).paramVal and [xT, yT] = some (.ctor and [yT, xT]) ∧
    (cH Hswap).paramVal and [yT, xT] = some (.ctor and [yT, xT]) :=
  ⟨(and_paramVal Hswap).mpr ⟨by rw [swap_app.1]; rfl, swap_sort⟩,
   (and_paramVal Hswap).mpr ⟨by rw [swap_app.2]; rfl, swap_sort⟩⟩

/-- **`Γc` with the step's closure has no model at `Hswap`.** -/
theorem not_consistent_swap : ¬ Consistent (cH Hswap) :=
  not_consistent_of_clash Hswap (xy_sorts Hswap).1 (xy_sorts Hswap).2 (xy_sorts Hswap).2 (xy_sorts Hswap).1
    swap_val.1 swap_val.2 (fun h => by simp [xT, yT, xS, yS] at h)

/-- **Consistency does not hold for every H.** -/
theorem not_consistent_all : ¬ ∀ H : HookParams, Consistent (cH H) := fun h => not_consistent_swap (h Hswap)

/-! ### A model where `and` determines its first argument -/

theorem holds_mem_inv {C : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {bb : Bool}
    (h : Holds C n σ (.mem s t u) bb) :
    ∃ r r', EvalTerm C σ t r ∧ EvalTerm C σ u r' ∧ bb = (r.isSome && sameResult r r') := by
  generalize hc : Cond.mem s t u = p at h
  cases h with
  | mem h h' => cases hc; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hc

/-- Where the clause of `first` applies under σ at `vs`: `vs` is one value, the value of `and` at
σ's X and G, which are values of A. -/
theorem first_applies (H : HookParams) {σ : Subst} {vs : List GroundTerm} (h : clFirst.AppliesAt (cH H) σ vs) :
    ∃ a g v, σ.lookup 0 = some a ∧ (cH H).sortOf a = some aSrt ∧ (cH H).sortOf g = some aSrt ∧
      (cH H).paramVal and [a, g] = some v ∧ vs = [v] := by
  obtain ⟨hws, hpat, -, hpre⟩ := h
  have hw : (cH H).WellSorted clFirst.vars σ := (wellSortedAt_univ (cl := clFirst) rfl).mp hws
  obtain ⟨a, ea, hsa⟩ := hw 0 aSrt (by simp [clFirst])
  obtain ⟨g, eg, hsg⟩ := hw 1 aSrt (by simp [clFirst])
  obtain ⟨w, vs', rfl, hpv, hnil⟩ := PatVals.cons_inv hpat
  cases hnil
  have ew := PatVal.var_inv hpv
  obtain ⟨r, r', hr, hr', hb⟩ := holds_mem_inv hpre
  have er := EvalTerm.var_inv hr
  obtain ⟨rs, hrs, err⟩ := EvalTerm.param_inv (c := cH H) and_syms.1 and_syms.2.1 and_syms.2.2 hr'
  obtain ⟨r0, rs0, rfl, h0, hrs0⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs0
  cases EvalTerms.nil_inv hrs1
  have e0 := EvalTerm.var_inv h0
  have e1 := EvalTerm.var_inv h1
  subst er; subst e0; subst e1; subst err
  rw [ew, ea, eg] at hb
  refine ⟨a, g, w, ea, hsa, hsg, ?_, rfl⟩
  have hb' : sameResult (some w) ((cH H).paramVal and [a, g]) = true := by simpa [allSome] using hb.symm
  cases hq : (cH H).paramVal and [a, g] with
  | none => rw [hq] at hb'; simp [sameResult] at hb'
  | some w' =>
    rw [hq] at hb'
    simp only [sameResult, beq_iff_eq] at hb'
    rw [cmp_eq_iff.mp hb']

/-- **Under `FirstDet H` the clause of `first` is coherent with itself**: two matches at one value
give X one value. -/
theorem first_coherent (H : HookParams) (hH : FirstDet H) : Coherent (cH H) clFirst clFirst := by
  intro vs σ σ' h1 h2 _ _ _ _ _
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have hi0 : i = 0 := by simpa [clFirst, varOccs] using hi
  subst hi0
  obtain ⟨a, g, v, e0, hsa, hsg, hpv, hvs⟩ := first_applies H h1
  obtain ⟨a', g', v', e0', hsa', hsg', hpv', hvs'⟩ := first_applies H h2
  subst hvs
  have hv : v' = v := by simpa using hvs'.symm
  subst hv
  rw [e0, e0', hH a g a' g' _ hsa hsg hsa' hsg' hpv hpv']

/-- `first`. -/
def firstOrder : List Sym := [firstS]

theorem first_term_named : c.preRankObligationsFP firstOrder = [] := by decide +kernel
theorem first_agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem first_match_named : c.matchObligationsL = [(firstS, 0)] := by decide +kernel
theorem first_fnOvl : c.fnOvlSyms = [] := by decide +kernel
theorem first_rightHeld (H : HookParams) : (cH H).RightHeld :=
  Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H

/-- The match independence the deciders leave, the clause of `first`'s, under `FirstDet H`. -/
theorem first_matchObl (H : HookParams) (hH : FirstDet H) : Det.MatchObligationsL (cH H) := by
  intro p hp fn hfn cl hcl
  rw [Det.Semantics.matchObligationsL_withHooks, first_match_named, List.mem_singleton] at hp
  subst hp
  rw [first_lookupH] at hfn
  cases hfn
  simp only [fFirst, List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact (matchIndependent_iff_noExs rfl).mpr (first_coherent H hH)

/-- `and` has no law: `OpenLaws` holds under every interpretation. -/
theorem first_openLaws (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'
  rw [params_raw, List.mem_singleton] at hm
  simp only [Prod.mk.injEq] at hm
  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩

/-- **`FnHyp` under `FirstDet H`**: no function's termination, totality or agreement is named, no
condition is owed, and the one match independence named is `first_coherent`. -/
theorem first_fnHyp (H : HookParams) (hH : FirstDet H) : FnHyp (cH H) :=
  fnHyp_of_decidedPre (coreOKH H) (first_rightHeld H) (show (cH H).fnOvlSyms = [] from first_fnOvl) firstOrder
    (fun g hg => by rw [Semantics.preRankObligationsFP_withHooks, first_term_named] at hg; cases hg)
    (fun fn hfn ht => by
      have hfn' : fn ∈ [fFirst] := first_text ▸ hfn
      rw [List.mem_singleton] at hfn'
      subst hfn'
      exact absurd ht (by decide))
    (fun f hf => by rw [Det.Semantics.agreeObligationsI_withHooks, first_agree_named] at hf; cases hf)
    (first_matchObl H hH)
    ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, first_owed_rules]; intro i hi; cases hi),
      first_noWit H⟩
    (first_openLaws H) (hnoEx := first_noExsH H)

/-- **`Γc` with the step's closure has a model at every H where `and` determines its first
argument.** -/
theorem consistent (H : HookParams) (hH : FirstDet H) : Consistent (cH H) :=
  consistent_of_fnHyp _ (coreOKH H) (first_fnHyp H hH)

/-- **`Γc` with the step's closure has a model at H exactly where `and`, as H gives it, determines
its first argument.** -/
theorem consistent_iff (H : HookParams) : Consistent (cH H) ↔ FirstDet H :=
  ⟨firstDet_of_consistent H, consistent H⟩

/-! ### At `lawHooks c H` -/

/-- `lawHooks c H` gives `and` its application. -/
theorem lawHooks_and (H : HookParams) (vs : List GroundTerm) :
    (lawHooks c H).app and vs = some (.ctor and vs) :=
  (lawHooks_app_self (c := c) (H := H) (k := andK) (Semantics.lawShape_core coreOK andK andK_mem rfl) vs).trans
    (congrArg some (lawApp_plain (k := andK) rfl rfl vs))

/-- **`lawHooks c H` makes `and` determine its arguments**, for every H. -/
theorem firstDet_lawHooks (H : HookParams) : FirstDet (lawHooks c H) := by
  intro a g a' g' v _ _ _ _ hp hp'
  have e1 := ((and_paramVal (lawHooks c H)).mp hp).1
  have e2 := ((and_paramVal (lawHooks c H)).mp hp').1
  rw [lawHooks_and, Option.getD_some] at e1 e2
  exact (List.cons.inj (GroundTerm.ctor.inj (e1.symm.trans e2)).2).1

/-- **`Γc` with the step's closure has a model at `lawHooks c H`, for every H.** -/
theorem consistent_lawHooks (H : HookParams) : Consistent (c.withHooks (lawHooks c H)) :=
  consistent (lawHooks c H) (firstDet_lawHooks H)

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
theorem nojunk_items : ∀ ad ∈ [U.ax87, U.ax88, U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax87, U.ax88, U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
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
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30,
   U.ax76, U.ax77, U.ax84, U.ax85, U.ax86]

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

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  simp only [Semantics.sortsOf, s1_sort H]
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


/-! ## The functional sentence of `and` (56): owed as `OpenTotal` -/

/-- **Γ holds no item for `and`'s functional sentence**: the constructors' items state the
functionality of the generators that are no open generator only. The sentence is owed, at values,
as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : !(consItemsK c).any (·.pat == (trS U.ax56).pat) &&
    !(fnItems c).any (·.pat == (trS U.ax56).pat) &&
    (classOf "open generator functional" == [56]) = true := by
  decide +kernel

/-! ## Function equations (32 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 100) is not its sentence (`un<j>_differs`), and no reading here gives it from
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

/-- Γ's item 0 (sentence 100): no reading here ties it. -/
noncomputable def unItem0 : P := (TiePair.gammaPats c).getD 0 ⊥
theorem unItem0_at : (TiePair.gammaPats c)[0]? = some unItem0 := by decide +kernel
kernel_rfl fnText_at0 : fnText[0]? = some U.ax100
/-- **Γ's item 0 is not the text's sentence 100** (kernel): the sentence is uncovered. -/
theorem un0_differs : unItem0 ≠ (trS U.ax100).pat := by decide +kernel

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
    ∀ ad ∈ [U.ax89, U.ax94, U.ax97], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax87, U.ax88, U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
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

end KCore.TieE8LlvmE2OpenMixedClause

#check @KCore.TieE8LlvmE2OpenMixedClause.params_raw
#check @KCore.TieE8LlvmE2OpenMixedClause.readsConfined_c
#check @KCore.TieE8LlvmE2OpenMixedClause.userAxioms_eq
#check @KCore.TieE8LlvmE2OpenMixedClause.coreOK
#check @KCore.TieE8LlvmE2OpenMixedClause.account
#check @KCore.TieE8LlvmE2OpenMixedClause.account_sizes
#check @KCore.TieE8LlvmE2OpenMixedClause.account_classes
#check @KCore.TieE8LlvmE2OpenMixedClause.account_absent
#check @KCore.TieE8LlvmE2OpenMixedClause.absent_closed
#check @KCore.TieE8LlvmE2OpenMixedClause.absent_proj_below_c
#check @KCore.TieE8LlvmE2OpenMixedClause.absent_proj_below
#check @KCore.TieE8LlvmE2OpenMixedClause.lists_in_account
#check @KCore.TieE8LlvmE2OpenMixedClause.attrs_agree
#check @KCore.TieE8LlvmE2OpenMixedClause.sig_origin_but_next
#check @KCore.TieE8LlvmE2OpenMixedClause.decls_entailed
#check @KCore.TieE8LlvmE2OpenMixedClause.consistent
#check @KCore.TieE8LlvmE2OpenMixedClause.text_nextless
#check @KCore.TieE8LlvmE2OpenMixedClause.nojunk_trivial_entailed
#check @KCore.TieE8LlvmE2OpenMixedClause.nojunk_items_entailed
#check @KCore.TieE8LlvmE2OpenMixedClause.nojunk_kitem_entailed
#check @KCore.TieE8LlvmE2OpenMixedClause.cons_entailed
#check @KCore.TieE8LlvmE2OpenMixedClause.idem_refuted
#check @KCore.TieE8LlvmE2OpenMixedClause.names
#check @KCore.TieE8LlvmE2OpenMixedClause.lawHooks_laws
#check @KCore.TieE8LlvmE2OpenMixedClause.libAdmitted_lawHooks
#check @KCore.TieE8LlvmE2OpenMixedClause.lawHooks_lib
#check @KCore.TieE8LlvmE2OpenMixedClause.consistent_lawHooks
#check @KCore.TieE8LlvmE2OpenMixedClause.open_functional_not_item
#check @KCore.TieE8LlvmE2OpenMixedClause.gammaCl_eq
#check @KCore.TieE8LlvmE2OpenMixedClause.decls_entailed_c
#check @KCore.TieE8LlvmE2OpenMixedClause.nojunk_trivial_entailed_c
#check @KCore.TieE8LlvmE2OpenMixedClause.nojunk_items_entailed_c
#check @KCore.TieE8LlvmE2OpenMixedClause.nojunk_kitem_entailed_c
#check @KCore.TieE8LlvmE2OpenMixedClause.cons_entailed_c
#check @KCore.TieE8LlvmE2OpenMixedClause.idem_refuted_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.params_raw
#print axioms KCore.TieE8LlvmE2OpenMixedClause.readsConfined_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.userAxioms_eq
#print axioms KCore.TieE8LlvmE2OpenMixedClause.coreOK
#print axioms KCore.TieE8LlvmE2OpenMixedClause.account
#print axioms KCore.TieE8LlvmE2OpenMixedClause.account_sizes
#print axioms KCore.TieE8LlvmE2OpenMixedClause.account_classes
#print axioms KCore.TieE8LlvmE2OpenMixedClause.account_absent
#print axioms KCore.TieE8LlvmE2OpenMixedClause.absent_closed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.absent_proj_below_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.absent_proj_below
#print axioms KCore.TieE8LlvmE2OpenMixedClause.lists_in_account
#print axioms KCore.TieE8LlvmE2OpenMixedClause.attrs_agree
#print axioms KCore.TieE8LlvmE2OpenMixedClause.sig_origin_but_next
#print axioms KCore.TieE8LlvmE2OpenMixedClause.decls_entailed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.consistent
#print axioms KCore.TieE8LlvmE2OpenMixedClause.text_nextless
#print axioms KCore.TieE8LlvmE2OpenMixedClause.nojunk_trivial_entailed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.nojunk_items_entailed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.nojunk_kitem_entailed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.cons_entailed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.idem_refuted
#print axioms KCore.TieE8LlvmE2OpenMixedClause.names
#print axioms KCore.TieE8LlvmE2OpenMixedClause.lawHooks_laws
#print axioms KCore.TieE8LlvmE2OpenMixedClause.libAdmitted_lawHooks
#print axioms KCore.TieE8LlvmE2OpenMixedClause.lawHooks_lib
#print axioms KCore.TieE8LlvmE2OpenMixedClause.consistent_lawHooks
#print axioms KCore.TieE8LlvmE2OpenMixedClause.open_functional_not_item
#print axioms KCore.TieE8LlvmE2OpenMixedClause.gammaCl_eq
#print axioms KCore.TieE8LlvmE2OpenMixedClause.decls_entailed_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.nojunk_trivial_entailed_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.nojunk_items_entailed_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.nojunk_kitem_entailed_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.cons_entailed_c
#print axioms KCore.TieE8LlvmE2OpenMixedClause.idem_refuted_c
#check @KCore.TieE8LlvmE2OpenMixedClause.fns_account
#check @KCore.TieE8LlvmE2OpenMixedClause.un0_differs
#check @KCore.TieE8LlvmE2OpenMixedClause.shape
#check @KCore.TieE8LlvmE2OpenMixedClause.fns_entailed
#check @KCore.TieE8LlvmE2OpenMixedClause.fns_from_text
#check @KCore.TieE8LlvmE2OpenMixedClause.fn_prios
#check @KCore.TieE8LlvmE2OpenMixedClause.gamma_from
#print axioms KCore.TieE8LlvmE2OpenMixedClause.fns_account
#print axioms KCore.TieE8LlvmE2OpenMixedClause.un0_differs
#print axioms KCore.TieE8LlvmE2OpenMixedClause.shape
#print axioms KCore.TieE8LlvmE2OpenMixedClause.fns_entailed
#print axioms KCore.TieE8LlvmE2OpenMixedClause.fns_from_text
#print axioms KCore.TieE8LlvmE2OpenMixedClause.fn_prios
#print axioms KCore.TieE8LlvmE2OpenMixedClause.gamma_from
