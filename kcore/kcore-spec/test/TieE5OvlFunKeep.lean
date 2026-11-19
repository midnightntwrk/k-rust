/-
  The tie (C14) on `f2-examples/e5-ovl-fun-keep.kompile.kore`, the kompiled text of construct fixture e5-ovl-fun-keep
  (`test/constructs/fixtures/e5-ovl-fun-keep`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e5-ovl-fun-keep`, its consistency, ovlfn section by hand; run from the package root:
  `lake env lean -j1 test/TieE5OvlFunKeep.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists and the three sentences of a function-overloaded symbol, listed
    apart (`ovlFnApart`), partition the 153 sentences of the user module E5-OVL-FUN-KEEP, the
    classes in `tieClassesOvl`' order (`account`, `account_sizes`, `account_classes`); the
    no-direction class holds exactly the sentences that apply a symbol Γ lacks (`account_absent`,
    `absent_closed`).
  - `absent_proj_below`: the 15 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 211 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the totality of the `[total]` function `capN` (`total_named`), which no decider confirms.
    The consistency section, written by hand, proves that Γ with the step's closure has a model for
    every H (`consistent`), through `FnHyp` for every H (`fnHypH`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (32): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (29): entailed by Γ (`cons_entailed`).
  - Overload axioms (102): entailed by Γ, whose overload equation states each at every
    element (`ovleq_entailed`).
  - Sentences of a function-overloaded symbol (57, the `functional` sentence of `LblcapGas`; 58, the
    same-constructor sentence of `LblcapGas`; 59, a different-constructors sentence of `LblcapGas`
    and `Lblinf`), weaker under overloadFunction, listed apart (`ovlFnApart`): Γ holds each at the
    arguments no overload covers only. Part 1, for every H: in a model of Γ the sentence, with the
    `functional` sentence it is joint with, entails Γ's item at uncovered arguments
    (`ovlfn_text_<i>`, `ovlfn_entails_item_<i>`), which is Γ's (`ovlfn_item_in_gamma_<i>`). Part 2,
    what it says at covered arguments, by hand: at values for every H (57, 58;
    `ovlfn_at_values_<i>`); refuted for every H (59; `ovlFnRefuted`, `ovlfn_refuted_<i>`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (49): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from `FnHyp`, which holds for every H
    (`fnHypH`), and the sort predicates' results (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  Gas's no junk (91) is entailed (`nojunk_gas_entailed`): its item lists Gas's generators in another
  order than `Semantics.gens`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (21);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunKeep

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-keep.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-keep.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-keep.kompile.kore" module "E5-OVL-FUN-KEEP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E5-OVL-FUN-KEEP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 153 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClassesOvl`: `tieClasses` with the class overload equation), the
indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [104, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
      126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [24, 26, 28, 30, 61, 81, 82, 89]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]),
   ("injectivity", [25, 27, 29, 31]),
   ("distinctness", []),
   ("no junk", [90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]),
   ("function functional", [60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]),
   ("hooked functional", [21, 22, 23, 32, 33, 34, 35, 36, 37, 40, 44, 52, 53, 54, 55, 56, 63, 80, 83, 84, 85, 86, 87]),
   ("collection law", [41, 42, 43, 45, 46, 47, 48, 50, 51]),
   ("library", [103, 155]),
   ("set idempotence", [49]),
   ("set-variable lemma", [156]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("overload equation", [102]),
   ("no direction", [38, 39, 62, 88, 105, 106, 107, 108, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
      151, 152, 153, 154])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences of a function-overloaded symbol (its `functional` sentence and its no-confusion
sentences), which Γ holds at the arguments no overload covers only: weaker under overloadFunction,
in no class. -/
def ovlFnApart : List Nat := [57, 58, 59]

/-- **The account**: the class lists and the sentences of a function-overloaded symbol partition the
user module's sentences. Their concatenation is a permutation of the sentences' indices, which are
distinct, so each sentence is in one class or among those of a function-overloaded symbol, and there
once. -/
theorem account : (classes.flatMap (·.2) ++ ovlFnApart).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 32), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 8), ("subsort", 17), ("injectivity", 4), ("distinctness", 0), ("no junk", 12), ("function functional", 17), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("overload equation", 1), ("no direction", 23)] := by
  decide +kernel

/-- The classes are the tie's for a text with a sentence of an overloading symbol (`tieClassesOvl`,
which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClassesOvl.map (·.1) := by decide +kernel

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
  [(140, "Bool"), (141, "Gas"), (142, "GeneratedCounterCell"), (143, "GeneratedCounterCellOpt"),
   (144, "GeneratedTopCell"), (145, "GeneratedTopCellFragment"), (146, "Int"), (147, "K"),
   (148, "KCell"), (149, "KCellOpt"), (150, "KItem"), (151, "List"), (152, "Map"), (153, "N"),
   (154, "Set")]

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
  [(14, "subsort"), (16, "subsort"), (19, "subsort"), (60, "function functional"),
   (61, "constructor functional"), (65, "function functional"), (78, "function functional"),
   (89, "constructor functional"), (91, "no junk"), (100, "no junk"), (101, "no junk"),
   (102, "overload equation"), (104, "function equation"), (108, "no direction"),
   (111, "function equation"), (112, "function equation"), (136, "function equation"),
   (137, "function equation"), (141, "no direction"), (153, "no direction"),
   (156, "set-variable lemma")]

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

/-! ## Consistency for every H: the totality of `capN` -/

/- `capN : N → Gas` is `[total]` with the one equation `capN(z) = inf`. No decider confirms its
totality (`total_named`). N holds `z` only (`val_N_ofr`: `z` is its one constructor, no sort is
below it, and it has neither literals nor collections), and the equation gives `capN(z)` the value
`inf` under every H (`eval_z_ofr`), so `capN` is total under every H (`total_capN_ofr`). The other
lists name nothing, no rule's or clause's condition is owed (`owed_rules`, `owed_clauses`), and the
definition has no open generator, so `FnObligations` holds for every H (`obl`), hence `FnHyp`
(`fnHypH`), and Γ with the step's closure has a model (`consistent`). -/

def gasS : Srt := 32
def nS : Srt := 33
def infS : Sym := 386
def zS : Sym := 387
def capN : Sym := 388
def capGas : Sym := 389

theorem syms_named : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName infS = "Lblinf" ∧
    c.symName zS = "Lblz" ∧ c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" := by decide +kernel

/-- `capN(z) = inf`. -/
def capCl : Clause := { vars := [], pats := [.app zS []], req := none, rhs := .app infS [], ens := none }
/-- `capN : N → Gas`, declared total. -/
def capNFn : Fn := ⟨capN, [nS], gasS, [capCl], true⟩
def capNSig : CtorSig := ⟨capN, [nS], gasS⟩
def capGasSig : CtorSig := ⟨capGas, [gasS], gasS⟩
def infSig : CtorSig := ⟨infS, [], gasS⟩
def zSig : CtorSig := ⟨zS, [], nS⟩
/-- `capGas` overloads `capN`. -/
def oCap : OvlSig := ⟨capGasSig, [capN]⟩

kernel_rfl fns_c : c.fns = [capNFn]
kernel_rfl ovls_c : c.ovls = [oCap]

/-- **The reading**: the one function is `capN`, the one overloading symbol `capGas`, over `capN`. -/
theorem reading : c.fns = [capNFn] ∧ c.ovls = [oCap] ∧ c.fnOvlSyms = [capGas] :=
  ⟨fns_c, ovls_c, by decide +kernel⟩

def zT : GroundTerm := .ctor zS []
def infT : GroundTerm := .ctor infS []
/-- `inj{N, Gas}(z)` -/
def injZ : GroundTerm := .inj nS gasS zT

kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn capN = some capNFn
kernel_rfl isCtor_H : ∀ H : HookParams, ((cH H).isCtor zS, (cH H).isCtor infS) = (true, true)

/-- A sort whose one generator is a constant holds that constant only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem onlyConst_ofr {c : Semantics} {s : Srt} {k0 : CtorSig} (ha : k0.args = [])
    (hk : ∀ k ∈ c.ctorSigs, k.result = s → k = k0)
    (ho : ∀ o ∈ c.ovls, o.sig.result ≠ s)
    (hp : ∀ k ∈ c.params, k.raw = false)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s)
    (hdv : ∀ lit, dvOK c.lib s lit = false)
    (hcoll : c.collOf s = none)
    {v : GroundTerm} (h : c.sortOf v = some s) : v = .ctor k0.name [] := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk', hs, hr⟩ | ⟨-, o, hlo, -, -, hr⟩ | ⟨-, -, k, hko, -⟩
    · obtain ⟨hm, hn⟩ := lookupSig_spec hk'
      have := hk k hm hr.symm
      subst this
      rw [ha] at hs
      rw [sortsOf_inv_nil hs, hn]
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec hlo
      exact absurd hr.symm (ho o (he ▸ List.getElem_mem hi))
    · obtain ⟨hm, hraw, -⟩ := Semantics.lookupOpen_spec _ hko
      rw [hp k hm] at hraw; cases hraw
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact absurd rfl (hsub _ (List.contains_iff_mem.mp hc.1.1))
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc; cases h; rw [hdv lit] at hc; cases hc
    · cases h
  | map s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_map_sort h
    rw [hcoll] at hc; cases hc
  | set s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_set_sort h
    rw [hcoll] at hc; cases hc
  | list s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_list_sort h
    rw [hcoll] at hc; cases hc

/-- A sort that is no carrier of literals has none. -/
theorem noLit_ofr {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

/-- **N holds `z` only.** -/
theorem val_N_ofr {v : GroundTerm} (h : c.sortOf v = some nS) : v = zT :=
  onlyConst_ofr (k0 := zSig) rfl (by decide +kernel) (by decide +kernel) noRaw (by decide +kernel)
    (noLit_ofr (by decide +kernel)) (by decide +kernel) h

/-- **`capN(z)` evaluates to `inf`**, by its one clause, under every H. -/
theorem eval_z_ofr (H : HookParams) : Eval (cH H) capN [zT] (some infT) :=
  .clause (cl := capCl) (σ := []) (lookupFn_H H) (List.mem_singleton_self _) (fun i s h => by simp [capCl] at h)
    (.cons (.ctor (congrArg Prod.fst (isCtor_H H)) .nil) .nil) (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      rw [show capNFn.clauses = [capCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl (.ctor (congrArg Prod.snd (isCtor_H H)) .nil) (fun t h => by cases h) .top

def callOrder : List Nat := [capN]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
/-- The `[total]` function whose totality no decider confirms: `capN`. -/
theorem total_named : c.totalObligationsRP callOrder [] = [capN] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

/-- **`capN` is `Total`, for every H**: its one clause decides at `z`, the one value of N. -/
theorem total_capN_ofr (H : HookParams) : Total (cH H) capN := fun fn' hfn' vs hvs => by
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans (lookupFn_H H))
  rw [show capNFn.args = [nS] from rfl, Semantics.sortsOf_withHooks _ _ noRaw] at hvs
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
  cases sortsOf_inv_nil hws
  cases val_N_ofr hw
  exact ⟨_, eval_z_ofr H⟩

/-- **The facts the deciders leave of `FnHyp` hold, for every H**: the one named is the totality of
`capN`. -/
theorem obl (H : HookParams) : FnObligations (cH H) callOrder [] :=
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP callOrder [] = [capN] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; rw [List.mem_singleton.mp hf]; exact total_capN_ofr H,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecidedH H,
   openLaws_of_plain (c := cH H) noRaw⟩

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Function functional (17): the `functional` sentences, at values in every model of Γc, from `FnHyp` -/

/- The class holds 17 `functional` sentences, `\exists{R}(Val:S, \equals{S, R}(Val:S, f(K0, …)))`:
16 of sort predicates `isX` (KCore builds them, `Semantics.sortPreds`) and 1 of functions of the
text declared total (60). A model of `Γc` reads the application of a function with a value at every
argument list of its sorts, at values' elements, as that value's element (`LibEv.fnFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and the clauses' conditions
decided where `needsWitness` holds). A sort predicate has those values from its own clauses
(`LibEv.sortPredFun_evC`); a function declared total has them from `FnHyp`
(`LibEv.fnFun_evC_withHooks`). `FnHyp`, which the tie states for every H (`fnHypH`), decides the
conditions (its `OpenDecided`). So each sentence holds in every model of `Γc`, and of `Γc` with the
step's closure, at every valuation sending its variables to values, for every H. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- **`fnFunText` is the account's function functional class**: the same indices, each once. -/
theorem fnFun_account : (classOf "function functional").isPerm (fnFunText.map (·.index)) = true := by
  decide +kernel

/-- The sentence is the `functional` sentence of a sort predicate of `c`, with its variables' sorts
the registry's, or of a function of `c` declared total, with its variables' sorts sorts of `c`, over
the one sort variable `R`. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    ((c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig) ||
      c.fns.any fun fn => fn.total && decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunRegS c fn.sig)

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the 17 reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\top` and no clause binds a variable by `\exists`. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true := by
  decide +kernel

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), from `FnHyp` (`fnHypH`). -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany | hany⟩ := hok
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
      (fnHypH H).2.2.2.2.1.2 hfn hfp.2 ad hfp.1 hsv
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.fnFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
      (fnHypH H) hfn hfp.1.1 hfp.2 ad hfp.1.2 hsv

/-- The same in every model of `Γc` with the step's closure, the theory `Consistent` asks a model of. -/
theorem fnFun_at_values_step (H : HookParams) : ∀ ad ∈ fnFunText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H)) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => fnFun_at_values H ad had M hM I (fun φ hφ => hI φ (Or.inl hφ))

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (32 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 32 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax104, U.ax123, U.ax131, U.ax130, U.ax129, U.ax128, U.ax135, U.ax134, U.ax139, U.ax138,
   U.ax133, U.ax132, U.ax110, U.ax109, U.ax122, U.ax121, U.ax118, U.ax117, U.ax120, U.ax119,
   U.ax125, U.ax124, U.ax127, U.ax126, U.ax114, U.ax113, U.ax116, U.ax115, U.ax112, U.ax111,
   U.ax137, U.ax136]

set_option maxHeartbeats 1000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel
decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl
  rw [fn_shape, List.getElem?_map] at h1
  cases hf : fnText[j]? with
  | none => rw [hf] at h1; cases h1
  | some ad =>
    rw [hf] at h1
    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
    have he : (trS ad).pat = it.pat := Option.some.inj h1
    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

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

theorem nj90 : (trS U.ax90).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj96 : (trS U.ax96).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj99 : (trS U.ax99).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax90, U.ax96, U.ax99], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj90]; exact orTopBot_valid hD rfl
  · rw [nj96]; exact orTopBot_valid hD rfl
  · rw [nj99]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax92, U.ax93, U.ax94, U.ax95, U.ax97, U.ax98, U.ax101],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax92, U.ax93, U.ax94, U.ax95, U.ax97, U.ax98, U.ax101],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax100).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (100)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax100).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- Gas, a sort with generators. -/
def gas : Srt := 32

theorem gas_name : c.sortName gas = "Gas" := by decide +kernel

/-- Gas's generators in the order the text's no-junk sentence (91) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def gasTextGens : List KoreAML.Gen :=
  match (c.gens gas).map (Gen.toK c) with
  | [g0, g1, g2] => [g1, g0, g2]
  | gs => gs

/-- Gas's no-junk sentence (91) is the item over Gas's generators in the text's order. -/
theorem nojunk_gas_order : (trS U.ax91).pat = (KoreAML.Cons.noJunkItem (c.sortName gas) gasTextGens).pat := by
  decide +kernel
theorem nojunk_gas_members : gasTextGens.isPerm ((c.gens gas).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for Gas's no junk (91)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_gas_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax91).pat := by
  intro M _ I hI
  rw [nojunk_gas_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens gas).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_gas_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := gas)
    (show gas ∈ consSorts c by decide +kernel) (show (c.gens gas).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30,
   U.ax31, U.ax61, U.ax81, U.ax82, U.ax89]

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

/-! ## The overload axioms -/

/-- The sentences of the class overload equation, in text order. -/
noncomputable def ovlEqText : List AxiomDecl :=
  [U.ax102]

theorem ovleq_account : (classOf "overload equation").isPerm (ovlEqText.map (·.index)) = true := by
  decide +kernel

/-- Each is an overload axiom of the semantics: of an overloading symbol over a symbol it overloads,
in the form `tieOvlEq_entailed` reads (`tieOvlEqB`; kernel). -/
theorem ovleq_checked : ovlEqText.all (fun ad => tieOvlEqB c ad.ax) = true := by decide +kernel

theorem ovleq_trS : ovlEqText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the overload axioms**: Γ entails each, for every H. Γ's overload equation states, at
every element of the overloaded symbol's argument sorts, that the overloading symbol applied to
their lifts is the lift of the overloaded symbol applied to them (`tieOvlEq_entailed`). -/
theorem ovleq_entailed (H : HookParams) : ∀ ad ∈ ovlEqText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp ovleq_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieOvlEq_entailed (c := cH H) (a := ad.ax)
    ((tieOvlEqB_withHooks c H ad.ax).trans (List.all_eq_true.mp ovleq_checked ad had)) ad.index ad.module hI

/-! ## Sentences of a function-overloaded symbol (57, 58, 59): weaker under
overloadFunction, listed apart

Γ holds each sentence at the arguments no overload of its generator covers only (Γ's items
`funUncItem`, `injUncItem`, `distUncItem`). This section states what holds for every H on every
text: the sentence entails that item in a model of Γ, the same-constructor and
different-constructors sentences with the `functional` sentence of their function-overloaded
generator. What a sentence says at covered arguments is the next section's, by hand. -/

/-- The sentences of `ovlFnApart`, in text order. -/
noncomputable def ovlFnText : List AxiomDecl :=
  [U.ax57, U.ax58, U.ax59]

theorem ovlfn_index : ovlFnText.map (·.index) = ovlFnApart := by decide +kernel

/-- The generator `LblcapGas`. -/
def ovlFnGen0 : Gen := .ctor ⟨389, [32], 32⟩

/-- The generator `Lblinf`. -/
def ovlFnGen1 : Gen := .ctor ⟨386, [], 32⟩

/-- The sorts of these generators are the semantics' sorts, named: -/
theorem ovlfn_sorts : 32 < nRegSorts + c.sortNames.length := by decide +kernel
theorem ovlfn_sort_names : c.sortName 32 = "Gas" := by decide +kernel

/-- Γ holds the G-arity item of each generator whose `functional` sentence the others are joint
with (`tieOvlFnArityB`). -/
theorem ovlfn_arity_0 : tieOvlFnArityB c 32 ovlFnGen0 = true := by decide +kernel

/-- Sentence 57 is the `functional` sentence of `LblcapGas` of Gas. -/
theorem ovlfn_text_57 : tieOvlFnFunAtB c 32 ovlFnGen0 U.ax57.ax = true := by decide +kernel
theorem ovlfn_trS_57 : (trS U.ax57).pat = (trAxiom [] [] U.ax57).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_57 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnFun_item_withHooks ovlfn_text_57 H

/-- **In a model of Γ, sentence 57 entails that item**, for every H. -/
theorem ovlfn_entails_item_57 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (h : I ⊧ᴵ (trS U.ax57).pat) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_57] at h
  exact tieOvlFnFun_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57) ovlfn_sorts
    ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) h _

/-- Sentence 58 is the same-constructor sentence of `LblcapGas` of Gas, joint with the `functional` sentence 57. -/
theorem ovlfn_text_58 : tieOvlFnInjAtB c 32 ovlFnGen0 U.ax58.ax = true := by decide +kernel
theorem ovlfn_trS_58 : (trS U.ax58).pat = (trAxiom [] [] U.ax58).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_58 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnInj_item_withHooks ovlfn_text_58 H

/-- **In a model of Γ, sentence 58 with sentence 57 entails that item**, for every H. -/
theorem ovlfn_entails_item_58 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax57).pat) (h : I ⊧ᴵ (trS U.ax58).pat) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_57] at hf
  rw [ovlfn_trS_58] at h
  exact tieOvlFnInj_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57)
    ((tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_58) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _

/-- Sentence 59 is a different-constructors sentence of `LblcapGas` and `Lblinf` of Gas, joint with the `functional` sentence 57. -/
theorem ovlfn_text_59 : tieOvlFnDistAtB c 32 ovlFnGen0 ovlFnGen1 U.ax59.ax = true := by decide +kernel
theorem ovlfn_trS_59 : (trS U.ax59).pat = (trAxiom [] [] U.ax59).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H (in one of the two orders). -/
theorem ovlfn_item_in_gamma_59 (H : HookParams) :
    (∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∨
    (∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) :=
  tieOvlFnDist_item_withHooks ovlfn_text_59 H

/-- **In a model of Γ, sentence 59 with sentence 57 entails that item**, in both orders, for every H. -/
theorem ovlfn_entails_item_59 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax57).pat) (h : I ⊧ᴵ (trS U.ax59).pat) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) := by
  rw [ovlfn_trS_57] at hf
  rw [ovlfn_trS_59] at h
  have hfa := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at hfa
  exact tieOvlFnDist_weaker_Γ hI (gf := ovlFnGen0) (.inl rfl) hfa.1.2
    ((tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_59) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _ _

/-! ## Sentences of a function-overloaded symbol: the covered part (by hand) -/

/- `capGas : Gas → Gas` overloads the function `capN : N → Gas`, N below Gas, and `capN(z)` is
`inf`. The one value list `capN` covers is `[inj{N, Gas}(z)]` (`cov_inv_ofr`: N holds `z` only),
where the application `capGas(inj z)` has the value `inf` (`res_injZ_ofr`); at any other value list
its value is the raw application (`res_inv_ofr`). So, for every H:
- `capN` has a value at every covered value list (`ovlFnTotal_ofr`), and the `functional` sentence
  of `capGas` (57) holds at values (`ovlfn_at_values_57`);
- two value lists at which `capGas` has one value are equal (`ovlFnInj_ofr`: one list is covered,
  and its value `inf` is no raw application of `capGas`), and the same-constructor sentence (58)
  holds at values (`ovlfn_at_values_58`);
- the value of `capGas(inj z)` is `inf`, so `OvlFnDist capGas inf` fails (`not_ovlFnDist_ofr`) and
  no model of Γ satisfies the different-constructors sentence of `capGas` and `inf` (59) as the
  text writes it (`ovlfn_refuted_59`): in a model of Γ the application `capGas(inj z)` holds the
  element of `inf`, and the sentence says no element is both.
The definition reads no confined sort (`readsConfined_c`), so `Γc` is `Γ`: 57 and 58 are in every
model of Γ at every valuation sending the sentence's variables to values' elements, and the
refutation of 59 is against Γ. Each statement has `FnHyp`, proved for every H (`fnHypH`). -/

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
kernel_rfl inf_H : ∀ H : HookParams, lookupSig (cH H).ctorSigs infSig.name = some infSig
-- `capN`, the one function `capGas` overloads, is declared total.
kernel_rfl total_H : ∀ H : HookParams,
  ((cH H).fns.all fun fn => !((cH H).ovlOver oCap).any (·.name == fn.label) || fn.total) = true
kernel_rfl over_H : ∀ H : HookParams, (cH H).ovlOver oCap = [capNSig]
-- `capGas`'s one overload is a function.
kernel_rfl byFn_H : ∀ H : HookParams, (cH H).ovlByFn capNSig = true
kernel_rfl sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [injZ] = some oCap.sig.args
kernel_rfl sorts_nil : ∀ H : HookParams, (cH H).sortsOf [] = some infSig.args
kernel_rfl cover_H : ∀ H : HookParams, (cH H).fnCover oCap.sig.name [injZ] = some capNSig

/-- The one sort directly below Gas is N. -/
theorem below_gas_ofr : ∀ p ∈ c.subsorts, p.2 = gasS → p.1 = nS := by decide +kernel

/-- **The one value list of `capGas`'s argument sort a function overload covers is `[inj z]`**,
covered by `capN`: a covered value is an injection into Gas, from N, of a value of N. -/
theorem cov_inv_ofr (H : HookParams) {us : List GroundTerm} {kg : CtorSig}
    (hus : (cH H).sortsOf us = some oCap.sig.args) (hc : (cH H).fnCover oCap.sig.name us = some kg) :
    us = [injZ] ∧ kg = capNSig := by
  obtain ⟨o', ho', hkg, -, hcv⟩ := OvlLaws.fnCover_some_parts hc
  rw [lookup_H H] at ho'; cases ho'
  rw [over_H H, List.mem_singleton] at hkg
  subst hkg
  rw [Semantics.sortsOf_withHooks _ _ noRaw] at hus
  obtain ⟨u, us', rfl, hu, hus'⟩ := sortsOf_inv_cons (show c.sortsOf us = some [gasS] from hus)
  cases sortsOf_inv_nil hus'
  refine ⟨?_, rfl⟩
  have hl : (cH H).lies nS gasS u = true := by
    simpa [Semantics.ovlCovers, capNSig, oCap, capGasSig] using hcv
  cases u with
  | inj C B w =>
    obtain ⟨hsub, -, hw, hB⟩ := OvlLaws.sortOf_inj_iff.mp hu
    cases hB
    obtain rfl : C = nS := below_gas_ofr _ hsub rfl
    rw [val_N_ofr hw]; rfl
  | ctor f ts => simp [Semantics.lies, nS, gasS] at hl
  | dv s l => simp [Semantics.lies, nS, gasS] at hl
  | map s es => simp [Semantics.lies, nS, gasS] at hl
  | set s es => simp [Semantics.lies, nS, gasS] at hl
  | list s es => simp [Semantics.lies, nS, gasS] at hl

/-- **`capGas(inj z)` has the value `inf`**, for every H: `capN` covers `inj z`, and `capN(z)` is
`inf`, of `capGas`'s result sort. -/
theorem res_injZ_ofr (H : HookParams) : OvlFnRes (cH H) oCap [injZ] (some infT) :=
  OvlFnRes.fn (cover_H H) (eval_z_ofr H)

/-- A function has one result at each argument list, for every H. -/
theorem fnDet_ofr (H : HookParams) : FnDet (cH H) := fnDet_of_agree (fnHypH H).2.2.1 (fnHypH H).2.2.2.1

/-- **The values of `capGas`'s application**, for every H: `inf` at `[inj z]`, and the raw
application at a value list no overload covers. -/
theorem res_inv_ofr (H : HookParams) {us : List GroundTerm} {v : GroundTerm}
    (hus : (cH H).sortsOf us = some oCap.sig.args) (h : OvlFnRes (cH H) oCap us (some v)) :
    (us = [injZ] ∧ v = infT) ∨ v = .ctor capGas us := by
  generalize hr : some v = r at h
  cases h with
  | norm hnf =>
    rw [ovlFnRes_norm_raw (lookup_H H) (fun kg hkg => by
      rw [over_H H, List.mem_singleton] at hkg; subst hkg; exact byFn_H H) hnf] at hr
    exact .inr (Option.some.inj hr)
  | @fn kg r' hcov hev =>
    obtain ⟨rfl, rfl⟩ := cov_inv_ofr H hus hcov
    obtain rfl := fnDet_ofr H _ _ _ _ hev (eval_z_ofr H)
    exact .inl ⟨rfl, Option.some.inj hr⟩

theorem fun_shape_ofr (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax57.ax = true := by
  have h := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_57
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem inj_shape_ofr (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax58.ax = true := by
  have h := (tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_58
  simp only [tieOvlFnInjAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem dist_shape_ofr (H : HookParams) :
    tieOvlFnDistShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) (Gen.toK (cH H) (.ctor infSig))
      U.ax59.ax = true := by
  have h := (tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_59
  simp only [tieOvlFnDistAtB, Bool.and_eq_true] at h
  exact h.1.2

/-- **`OvlFnTotal`**, for every H: `capN`, declared total, has a value at every covered value list. -/
theorem ovlFnTotal_ofr (H : HookParams) : OvlFnTotal (cH H) oCap :=
  ovlFnTotal_of_total (coreOKH H) (fnHypH H) (lookup_H H) (total_H H)

/-- **`OvlFnInj`**, for every H: the covered list's value, `inf`, is no raw application of
`capGas`, and two raw applications with one value have the same arguments. -/
theorem ovlFnInj_ofr (H : HookParams) : OvlFnInj (cH H) oCap := fun us vs v hus hvs h1 h2 => by
  rcases res_inv_ofr H hus h1 with ⟨rfl, rfl⟩ | rfl
  · rcases res_inv_ofr H hvs h2 with ⟨rfl, -⟩ | h
    · rfl
    · exact absurd h (by simp [infT, infS, capGas])
  · rcases res_inv_ofr H hvs h2 with ⟨-, h⟩ | h
    · exact absurd h (by simp [infT, infS, capGas])
    · injection h with _ h

/-- **`OvlFnDist capGas inf` fails**, for every H: `capGas(inj z)` is `inf`. -/
theorem not_ovlFnDist_ofr (H : HookParams) : ¬ OvlFnDist (cH H) oCap infSig :=
  fun h => h [injZ] [] (sorts_injZ H) (sorts_nil H) (res_injZ_ofr H)

/-- **The `functional` sentence of `capGas` (57) holds at values, for every H**, in every model of
`Γc`. -/
theorem ovlfn_at_values_57 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax57 (trS U.ax57).pat := by
  rw [ovlfn_trS_57]
  exact ovlFnTotal_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnTotal_ofr H) (fun_shape_ofr H)

/-- **The same-constructor sentence of `capGas` (58) holds at values, for every H**, in every model
of `Γc`. -/
theorem ovlfn_at_values_58 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax58 (trS U.ax58).pat := by
  rw [ovlfn_trS_58]
  exact ovlFnInj_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnInj_ofr H) (inj_shape_ofr H)

/-- The sentences of `ovlFnApart` refuted for every H. -/
def ovlFnRefuted : List Nat := [59]

/-- **No model of Γ satisfies the different-constructors sentence of `capGas` and `inf`**
(`\not(\and(LblcapGas(X0), Lblinf()))`, sentence 59), for every H: `capGas(inj z)` is `inf`. -/
theorem ovlfn_refuted_59 (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax59).pat) := by
  intro M inst I hI
  rw [ovlfn_trS_59]
  have hIc : I ⊧ᴵP Γc (cH H) := by
    rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI
  exact ovlFnDist_refuted (coreOKH H) (fnHypH H) (lookup_H H) (inf_H H) rfl (dist_shape_ofr H) (sorts_injZ H)
    (sorts_nil H) (res_injZ_ofr H) M inst I hIc

/-! ## The refuted sentences of a function-overloaded symbol -/

/-- The sentences the hand section refutes for every H are sentences of `ovlFnApart`, in its order. -/
theorem ovlfn_refuted_sub : ovlFnRefuted.isSublist ovlFnApart = true := by decide +kernel

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax49.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax49).pat = (trAxiom [] [] U.ax49).pat := by decide +kernel

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
theorem idem_vars : (U.ax49.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax49.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax49.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 49 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax49).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax49.ax.sortVars U.ax49.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax49.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax49.ax.pattern).eraseDups,
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


/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; the text has no rule, so Γ has no rule item; everything else is one of the five parts
defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl ⟨ad, had, he⟩))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))

end KCore.TieE5OvlFunKeep

#check @KCore.TieE5OvlFunKeep.noRaw
#check @KCore.TieE5OvlFunKeep.readsConfined_c
#check @KCore.TieE5OvlFunKeep.userAxioms_eq
#check @KCore.TieE5OvlFunKeep.coreOK
#check @KCore.TieE5OvlFunKeep.wf_defn
#check @KCore.TieE5OvlFunKeep.account
#check @KCore.TieE5OvlFunKeep.account_sizes
#check @KCore.TieE5OvlFunKeep.account_classes
#check @KCore.TieE5OvlFunKeep.account_absent
#check @KCore.TieE5OvlFunKeep.absent_closed
#check @KCore.TieE5OvlFunKeep.absent_proj_below_c
#check @KCore.TieE5OvlFunKeep.absent_proj_below
#check @KCore.TieE5OvlFunKeep.lists_in_account
#check @KCore.TieE5OvlFunKeep.attrs_agree
#check @KCore.TieE5OvlFunKeep.sig_origin_but_next
#check @KCore.TieE5OvlFunKeep.decls_entailed
#check @KCore.TieE5OvlFunKeep.consistent
#check @KCore.TieE5OvlFunKeep.total_named
#check @KCore.TieE5OvlFunKeep.fnHypH
#check @KCore.TieE5OvlFunKeep.fnFun_indices
#check @KCore.TieE5OvlFunKeep.fnFun_account
#check @KCore.TieE5OvlFunKeep.fnFun_checked
#check @KCore.TieE5OvlFunKeep.fnFun_trS
#check @KCore.TieE5OvlFunKeep.fnFun_at_values
#check @KCore.TieE5OvlFunKeep.fnFun_at_values_step
#check @KCore.TieE5OvlFunKeep.text_nextless
#check @KCore.TieE5OvlFunKeep.fn_shape
#check @KCore.TieE5OvlFunKeep.fns_account
#check @KCore.TieE5OvlFunKeep.fns_entailed
#check @KCore.TieE5OvlFunKeep.fns_from_text
#check @KCore.TieE5OvlFunKeep.fn_prios
#check @KCore.TieE5OvlFunKeep.nojunk_trivial_entailed
#check @KCore.TieE5OvlFunKeep.nojunk_items_entailed
#check @KCore.TieE5OvlFunKeep.nojunk_kitem_entailed
#check @KCore.TieE5OvlFunKeep.cons_entailed
#check @KCore.TieE5OvlFunKeep.ovleq_account
#check @KCore.TieE5OvlFunKeep.ovleq_entailed
#check @KCore.TieE5OvlFunKeep.ovlfn_index
#check @KCore.TieE5OvlFunKeep.ovlfn_text_57
#check @KCore.TieE5OvlFunKeep.ovlfn_item_in_gamma_57
#check @KCore.TieE5OvlFunKeep.ovlfn_entails_item_57
#check @KCore.TieE5OvlFunKeep.ovlfn_text_58
#check @KCore.TieE5OvlFunKeep.ovlfn_item_in_gamma_58
#check @KCore.TieE5OvlFunKeep.ovlfn_entails_item_58
#check @KCore.TieE5OvlFunKeep.ovlfn_text_59
#check @KCore.TieE5OvlFunKeep.ovlfn_item_in_gamma_59
#check @KCore.TieE5OvlFunKeep.ovlfn_entails_item_59
#check @KCore.TieE5OvlFunKeep.ovlFnRefuted
#check @KCore.TieE5OvlFunKeep.ovlfn_at_values_57
#check @KCore.TieE5OvlFunKeep.ovlfn_at_values_58
#check @KCore.TieE5OvlFunKeep.ovlfn_refuted_59
#check @KCore.TieE5OvlFunKeep.ovlfn_refuted_sub
#check @KCore.TieE5OvlFunKeep.idem_refuted
#check @KCore.TieE5OvlFunKeep.gamma_origin
#check @KCore.TieE5OvlFunKeep.gamma_from
#check @KCore.TieE5OvlFunKeep.nojunk_gas_order
#check @KCore.TieE5OvlFunKeep.nojunk_gas_members
#check @KCore.TieE5OvlFunKeep.nojunk_gas_entailed
#print axioms KCore.TieE5OvlFunKeep.noRaw
#print axioms KCore.TieE5OvlFunKeep.readsConfined_c
#print axioms KCore.TieE5OvlFunKeep.userAxioms_eq
#print axioms KCore.TieE5OvlFunKeep.coreOK
#print axioms KCore.TieE5OvlFunKeep.wf_defn
#print axioms KCore.TieE5OvlFunKeep.account
#print axioms KCore.TieE5OvlFunKeep.account_sizes
#print axioms KCore.TieE5OvlFunKeep.account_classes
#print axioms KCore.TieE5OvlFunKeep.account_absent
#print axioms KCore.TieE5OvlFunKeep.absent_closed
#print axioms KCore.TieE5OvlFunKeep.absent_proj_below_c
#print axioms KCore.TieE5OvlFunKeep.absent_proj_below
#print axioms KCore.TieE5OvlFunKeep.lists_in_account
#print axioms KCore.TieE5OvlFunKeep.attrs_agree
#print axioms KCore.TieE5OvlFunKeep.sig_origin_but_next
#print axioms KCore.TieE5OvlFunKeep.decls_entailed
#print axioms KCore.TieE5OvlFunKeep.consistent
#print axioms KCore.TieE5OvlFunKeep.total_named
#print axioms KCore.TieE5OvlFunKeep.fnHypH
#print axioms KCore.TieE5OvlFunKeep.fnFun_indices
#print axioms KCore.TieE5OvlFunKeep.fnFun_account
#print axioms KCore.TieE5OvlFunKeep.fnFun_checked
#print axioms KCore.TieE5OvlFunKeep.fnFun_trS
#print axioms KCore.TieE5OvlFunKeep.fnFun_at_values
#print axioms KCore.TieE5OvlFunKeep.fnFun_at_values_step
#print axioms KCore.TieE5OvlFunKeep.text_nextless
#print axioms KCore.TieE5OvlFunKeep.fn_shape
#print axioms KCore.TieE5OvlFunKeep.fns_account
#print axioms KCore.TieE5OvlFunKeep.fns_entailed
#print axioms KCore.TieE5OvlFunKeep.fns_from_text
#print axioms KCore.TieE5OvlFunKeep.fn_prios
#print axioms KCore.TieE5OvlFunKeep.nojunk_trivial_entailed
#print axioms KCore.TieE5OvlFunKeep.nojunk_items_entailed
#print axioms KCore.TieE5OvlFunKeep.nojunk_kitem_entailed
#print axioms KCore.TieE5OvlFunKeep.cons_entailed
#print axioms KCore.TieE5OvlFunKeep.ovleq_account
#print axioms KCore.TieE5OvlFunKeep.ovleq_entailed
#print axioms KCore.TieE5OvlFunKeep.ovlfn_index
#print axioms KCore.TieE5OvlFunKeep.ovlfn_text_57
#print axioms KCore.TieE5OvlFunKeep.ovlfn_item_in_gamma_57
#print axioms KCore.TieE5OvlFunKeep.ovlfn_entails_item_57
#print axioms KCore.TieE5OvlFunKeep.ovlfn_text_58
#print axioms KCore.TieE5OvlFunKeep.ovlfn_item_in_gamma_58
#print axioms KCore.TieE5OvlFunKeep.ovlfn_entails_item_58
#print axioms KCore.TieE5OvlFunKeep.ovlfn_text_59
#print axioms KCore.TieE5OvlFunKeep.ovlfn_item_in_gamma_59
#print axioms KCore.TieE5OvlFunKeep.ovlfn_entails_item_59
#print axioms KCore.TieE5OvlFunKeep.ovlFnRefuted
#print axioms KCore.TieE5OvlFunKeep.ovlfn_at_values_57
#print axioms KCore.TieE5OvlFunKeep.ovlfn_at_values_58
#print axioms KCore.TieE5OvlFunKeep.ovlfn_refuted_59
#print axioms KCore.TieE5OvlFunKeep.ovlfn_refuted_sub
#print axioms KCore.TieE5OvlFunKeep.idem_refuted
#print axioms KCore.TieE5OvlFunKeep.gamma_origin
#print axioms KCore.TieE5OvlFunKeep.gamma_from
#print axioms KCore.TieE5OvlFunKeep.nojunk_gas_order
#print axioms KCore.TieE5OvlFunKeep.nojunk_gas_members
#print axioms KCore.TieE5OvlFunKeep.nojunk_gas_entailed
