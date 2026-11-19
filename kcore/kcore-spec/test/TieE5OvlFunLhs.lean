/-
  The tie (C14) on `f2-examples/e5-ovl-fun-lhs.kompile.kore`, the kompiled text of construct fixture e5-ovl-fun-lhs
  (`test/constructs/fixtures/e5-ovl-fun-lhs`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e5-ovl-fun-lhs`, its consistency, ovlfn section by hand; run from the package root:
  `lake env lean -j1 test/TieE5OvlFunLhs.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end).

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists and the three sentences of a function-overloaded symbol, listed
    apart (`ovlFnApart`), partition the 283 sentences of the user module E5-OVL-FUN-LHS, the classes
    in `tieClassesOvl`' order (`account`, `account_sizes`, `account_classes`); the no-direction
    class holds exactly the sentences that apply a symbol Γ lacks (`account_absent`,
    `absent_closed`).
  - `absent_proj_below`: the 16 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 215 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator (`noRaw`).
    It owes the totality of the `[total]` function `capN` (`total_named`), which no decider confirms.
    The consistency section, written by hand, proves that `Γc` with the step's closure has a model for
    every H (`consistent`), through `FnHyp` for every H (`fnHypH`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (34): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (35): entailed by Γ (`cons_entailed`).
  - Overload axioms (139): entailed by Γ, whose overload equation states each at every
    element (`ovleq_entailed`).
  - Sentences of a function-overloaded symbol (81, the `functional` sentence of `LblcapGas`; 82, the
    same-constructor sentence of `LblcapGas`; 83, a different-constructors sentence of `LblcapGas`
    and `Lblinf`), weaker under overloadFunction, listed apart (`ovlFnApart`): Γ holds each at the
    arguments no overload covers only. Part 1, for every H: in a model of Γ the sentence, with the
    `functional` sentence it is joint with, entails Γ's item at uncovered arguments
    (`ovlfn_text_<i>`, `ovlfn_entails_item_<i>`), which is Γ's (`ovlfn_item_in_gamma_<i>`). Part 2,
    what it says at covered arguments, by hand: at values for every H (81, 82, 83;
    `ovlfn_at_values_<i>`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 8 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (64): Γ with it has no model (`idem_refuted`).
  - Library sample, 180 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - Function functional: at values in every model of `Γc`, from `FnHyp`, which holds for every H
    (`fnHypH`), and the sort predicates' results (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  Gas's no junk (127) is entailed (`nojunk_gas_entailed`): its item lists Gas's generators in
  another order than `Semantics.gens`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (32);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunLhs

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-lhs.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-lhs.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-lhs.kompile.kore" module "E5-OVL-FUN-LHS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E5-OVL-FUN-LHS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 283 := by decide +kernel

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
  [("function equation", [223, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245,
      246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261]),
   ("rewrite rule", [169]),
   ("priority equation", []),
   ("constructor functional", [25, 27, 29, 31, 85, 89, 113, 114, 118, 124]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]),
   ("injectivity", [26, 28, 30, 32, 86, 119]),
   ("distinctness", [87]),
   ("no junk", [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]),
   ("function functional", [84, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]),
   ("hooked functional", [22, 23, 24, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55,
      59, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 79, 80, 88, 91, 110, 111, 112, 115, 116, 117,
      120, 121, 122]),
   ("collection law", [56, 57, 58, 60, 61, 62, 63, 65, 66]),
   ("library", [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162,
      163, 164, 165, 166, 167, 168, 170, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182,
      183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200,
      201, 202, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
      220, 221, 222, 224, 264, 265, 266, 267, 284, 285]),
   ("set idempotence", [64]),
   ("set-variable lemma", [140, 141, 142, 143, 144, 286]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("overload equation", [139]),
   ("no direction", [39, 43, 45, 76, 78, 90, 109, 123, 125, 171, 203, 225, 226, 227, 228, 262, 263, 268, 269, 270,
      271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences of a function-overloaded symbol (its `functional` sentence and its no-confusion
sentences), which Γ holds at the arguments no overload covers only: weaker under overloadFunction,
in no class. -/
def ovlFnApart : List Nat := [81, 82, 83]

/-- **The account**: the class lists and the sentences of a function-overloaded symbol partition the
user module's sentences. Their concatenation is a permutation of the sentences' indices, which are
distinct, so each sentence is in one class or among those of a function-overloaded symbol, and there
once. -/
theorem account : (classes.flatMap (·.2) ++ ovlFnApart).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 34), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 10), ("subsort", 18), ("injectivity", 6), ("distinctness", 1), ("no junk", 13), ("function functional", 18), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("overload equation", 1), ("no direction", 33)] := by
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
  [(268, "Bool"), (269, "Gas"), (270, "GeneratedCounterCell"), (271, "GeneratedCounterCellOpt"),
   (272, "GeneratedTopCell"), (273, "GeneratedTopCellFragment"), (274, "Int"), (275, "K"),
   (276, "KCell"), (277, "KCellOpt"), (278, "KItem"), (279, "List"), (280, "Map"), (281, "N"),
   (282, "Pgm"), (283, "Set")]

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
  [(14, "subsort"), (16, "subsort"), (17, "subsort"), (20, "subsort"), (84, "function functional"),
   (85, "constructor functional"), (86, "injectivity"), (87, "distinctness"),
   (89, "constructor functional"), (93, "function functional"), (106, "function functional"),
   (107, "function functional"), (118, "constructor functional"), (119, "injectivity"),
   (124, "constructor functional"), (127, "no junk"), (136, "no junk"), (137, "no junk"),
   (138, "no junk"), (139, "overload equation"), (169, "rewrite rule"), (223, "function equation"),
   (228, "no direction"), (231, "function equation"), (232, "function equation"),
   (256, "function equation"), (257, "function equation"), (258, "function equation"),
   (259, "function equation"), (269, "no direction"), (281, "no direction"), (282, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(169, "rewrite rule")]

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

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFrom = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 13).all sigFrom = true := by decide +kernel
theorem sigE_47 : (((sigItems c).drop 47).take 13).all sigFrom = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFrom = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFrom = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFrom = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFrom = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFrom = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFrom = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFrom = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFrom = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFrom = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFrom = true := by decide +kernel
theorem sigE_190 : (((sigItems c).drop 190).take 13).all sigFrom = true := by decide +kernel
theorem sigE_203 : ((sigItems c).drop 203).all sigFrom = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 215 := by decide +kernel

/-- **Every item of Γ's signature has its origin**: the item of a declaration of the text, or the
sort constant of a registry sort or the arity of an interpreted hooked symbol that the text does not
declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAllE_whole (p := sigFrom) <|
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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (18, 17, 138, 98, 5, 35) := by
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

/-! ## Consistency for every H: the totality of `capN` -/

/- `capN : N → N` is `[total]` with the one equation `capN(z #as X) = X`, which gives `capN(z)` the value `z`. No decider confirms its totality
(`total_named`). N holds `z` only (`val_N_oft`: `z` is its one constructor, no sort is below it, and
it has neither literals nor collections), and the equation gives `capN(z)` the value `z` under
every H (`eval_z_oft`), so `capN` is total under every H (`total_capN_oft`). The other lists name
nothing, no rule's or clause's condition is owed (`owed_rules`, `owed_clauses`: the rule read
through the cut holds its open variable), and the definition has no open generator, so
`FnObligations` holds for every H (`obl`), hence `FnHyp` (`fnHypH`), and `Γc` with the step's
closure has a model (`consistent`). -/

def gasS : Srt := 32
def nS : Srt := 33
def infS : Sym := 388
def zS : Sym := 390
def capN : Sym := 391
def capGas : Sym := 392

theorem syms_named : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName infS = "Lblinf" ∧
    c.symName zS = "Lblz" ∧ c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" := by decide +kernel

/-- `capN(z #as X) = X`. -/
def capCl : Clause := { vars := [nS], pats := [.as (.app zS []) 0], req := none, rhs := .var 0, ens := none }
/-- `capN : N → N`, declared total. -/
def capNFn : Fn := ⟨capN, [nS], nS, [capCl], true⟩
def capNSig : CtorSig := ⟨capN, [nS], nS⟩
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
kernel_rfl isCtor_H : ∀ H : HookParams, (cH H).isCtor zS = true
kernel_rfl sort_z_H : ∀ H : HookParams, (cH H).sortOf zT = some nS

/-- A sort whose one generator is a constant holds that constant only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem onlyConst_oft {c : Semantics} {s : Srt} {k0 : CtorSig} (ha : k0.args = [])
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
theorem noLit_oft {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

/-- **N holds `z` only.** -/
theorem val_N_oft {v : GroundTerm} (h : c.sortOf v = some nS) : v = zT :=
  onlyConst_oft (k0 := zSig) rfl (by decide +kernel) (by decide +kernel) noRaw (by decide +kernel)
    (noLit_oft (by decide +kernel)) (by decide +kernel) h

/-- **`capN(z)` evaluates to `z`**, by its one clause, under every H. -/
theorem eval_z_oft (H : HookParams) : Eval (cH H) capN [zT] (some zT) :=
  .clause (fn := capNFn) (cl := capCl) (σ := [(0, zT)]) (lookupFn_H H) (List.mem_singleton_self _)
    (fun i s h => by
      cases i with
      | zero => cases h; exact ⟨zT, rfl, sort_z_H H⟩
      | succ i => simp [capCl] at h)
    (.cons (.as (.ctor (isCtor_H H) .nil) rfl) .nil) (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      rw [show capNFn.clauses = [capCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t h => by cases h) .top

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
theorem total_capN_oft (H : HookParams) : Total (cH H) capN := fun fn' hfn' vs hvs => by
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans (lookupFn_H H))
  rw [show capNFn.args = [nS] from rfl, Semantics.sortsOf_withHooks _ _ noRaw] at hvs
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
  cases sortsOf_inv_nil hws
  cases val_N_oft hw
  exact ⟨_, eval_z_oft H⟩

/-- **The facts the deciders leave of `FnHyp` hold, for every H**: the one named is the totality of
`capN`. -/
theorem obl (H : HookParams) : FnObligations (cH H) callOrder [] :=
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP callOrder [] = [capN] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; rw [List.mem_singleton.mp hf]; exact total_capN_oft H,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecidedH H,
   openLaws_of_plain (c := cH H) noRaw⟩

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl H)

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Function functional (18): the `functional` sentences, at values in every model of Γc, from `FnHyp` -/

/- The class holds 18 `functional` sentences, `\exists{R}(Val:S, \equals{S, R}(Val:S, f(K0, …)))`:
17 of sort predicates `isX` (KCore builds them, `Semantics.sortPreds`) and 1 of functions of the
text declared total (84). A model of `Γc` reads the application of a function with a value at every
argument list of its sorts, at values' elements, as that value's element (`LibEv.fnFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and the clauses' conditions
decided where `needsWitness` holds). A sort predicate has those values from its own clauses
(`LibEv.sortPredFun_evC`); a function declared total has them from `FnHyp`
(`LibEv.fnFun_evC_withHooks`). `FnHyp`, which the tie states for every H (`fnHypH`), decides the
conditions (its `OpenDecided`). So each sentence holds in every model of `Γc`, and of `Γc` with the
step's closure, at every valuation sending its variables to values, for every H. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [84, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]

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

/-- None of the 18 reads a declaration or an alias. -/
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

/-! ## Function equations (34 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 34 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax223, U.ax243, U.ax251, U.ax250, U.ax249, U.ax248, U.ax255, U.ax254, U.ax261, U.ax260,
   U.ax253, U.ax252, U.ax230, U.ax229, U.ax242, U.ax241, U.ax238, U.ax237, U.ax240, U.ax239,
   U.ax245, U.ax244, U.ax247, U.ax246, U.ax234, U.ax233, U.ax236, U.ax235, U.ax232, U.ax231,
   U.ax257, U.ax256, U.ax259, U.ax258]

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

theorem nj126 : (trS U.ax126).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj132 : (trS U.ax132).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj135 : (trS U.ax135).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax126, U.ax132, U.ax135], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj126]; exact orTopBot_valid hD rfl
  · rw [nj132]; exact orTopBot_valid hD rfl
  · rw [nj135]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax128, U.ax129, U.ax130, U.ax131, U.ax133, U.ax134, U.ax137, U.ax138],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax128, U.ax129, U.ax130, U.ax131, U.ax133, U.ax134, U.ax137, U.ax138],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax136).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (136)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax136).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- Gas, a sort with generators. -/
def gas : Srt := 32

theorem gas_name : c.sortName gas = "Gas" := by decide +kernel

/-- Gas's generators in the order the text's no-junk sentence (127) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def gasTextGens : List KoreAML.Gen :=
  match (c.gens gas).map (Gen.toK c) with
  | [g0, g1, g2] => [g1, g0, g2]
  | gs => gs

/-- Gas's no-junk sentence (127) is the item over Gas's generators in the text's order. -/
theorem nojunk_gas_order : (trS U.ax127).pat = (KoreAML.Cons.noJunkItem (c.sortName gas) gasTextGens).pat := by
  decide +kernel
theorem nojunk_gas_members : gasTextGens.isPerm ((c.gens gas).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for Gas's no junk (127)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_gas_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax127).pat := by
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
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax21, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax30,
   U.ax31, U.ax32, U.ax85, U.ax86, U.ax87, U.ax89, U.ax113, U.ax114, U.ax118, U.ax119, U.ax124]

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
  [U.ax139]

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

/-! ## Sentences of a function-overloaded symbol (81, 82, 83): weaker under
overloadFunction, listed apart

Γ holds each sentence at the arguments no overload of its generator covers only (Γ's items
`funUncItem`, `injUncItem`, `distUncItem`). This section states what holds for every H on every
text: the sentence entails that item in a model of Γ, the same-constructor and
different-constructors sentences with the `functional` sentence of their function-overloaded
generator. What a sentence says at covered arguments is the next section's, by hand. -/

/-- The sentences of `ovlFnApart`, in text order. -/
noncomputable def ovlFnText : List AxiomDecl :=
  [U.ax81, U.ax82, U.ax83]

theorem ovlfn_index : ovlFnText.map (·.index) = ovlFnApart := by decide +kernel

/-- The generator `LblcapGas`. -/
def ovlFnGen0 : Gen := .ctor ⟨392, [32], 32⟩

/-- The generator `Lblinf`. -/
def ovlFnGen1 : Gen := .ctor ⟨388, [], 32⟩

/-- The sorts of these generators are the semantics' sorts, named: -/
theorem ovlfn_sorts : 32 < nRegSorts + c.sortNames.length := by decide +kernel
theorem ovlfn_sort_names : c.sortName 32 = "Gas" := by decide +kernel

/-- Γ holds the G-arity item of each generator whose `functional` sentence the others are joint
with (`tieOvlFnArityB`). -/
theorem ovlfn_arity_0 : tieOvlFnArityB c 32 ovlFnGen0 = true := by decide +kernel

/-- Sentence 81 is the `functional` sentence of `LblcapGas` of Gas. -/
theorem ovlfn_text_81 : tieOvlFnFunAtB c 32 ovlFnGen0 U.ax81.ax = true := by decide +kernel
theorem ovlfn_trS_81 : (trS U.ax81).pat = (trAxiom [] [] U.ax81).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_81 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnFun_item_withHooks ovlfn_text_81 H

/-- **In a model of Γ, sentence 81 entails that item**, for every H. -/
theorem ovlfn_entails_item_81 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (h : I ⊧ᴵ (trS U.ax81).pat) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_81] at h
  exact tieOvlFnFun_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_81) ovlfn_sorts
    ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) h _

/-- Sentence 82 is the same-constructor sentence of `LblcapGas` of Gas, joint with the `functional` sentence 81. -/
theorem ovlfn_text_82 : tieOvlFnInjAtB c 32 ovlFnGen0 U.ax82.ax = true := by decide +kernel
theorem ovlfn_trS_82 : (trS U.ax82).pat = (trAxiom [] [] U.ax82).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H. -/
theorem ovlfn_item_in_gamma_82 (H : HookParams) :
    ∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  tieOvlFnInj_item_withHooks ovlfn_text_82 H

/-- **In a model of Γ, sentence 82 with sentence 81 entails that item**, for every H. -/
theorem ovlfn_entails_item_82 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax81).pat) (h : I ⊧ᴵ (trS U.ax82).pat) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat := by
  rw [ovlfn_trS_81] at hf
  rw [ovlfn_trS_82] at h
  exact tieOvlFnInj_weaker_Γ hI ((tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_81)
    ((tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_82) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _

/-- Sentence 83 is a different-constructors sentence of `LblcapGas` and `Lblinf` of Gas, joint with the `functional` sentence 81. -/
theorem ovlfn_text_83 : tieOvlFnDistAtB c 32 ovlFnGen0 ovlFnGen1 U.ax83.ax = true := by decide +kernel
theorem ovlfn_trS_83 : (trS U.ax83).pat = (trAxiom [] [] U.ax83).pat := by decide +kernel

/-- Γ holds its item at uncovered arguments, for every H (in one of the two orders). -/
theorem ovlfn_item_in_gamma_83 (H : HookParams) :
    (∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∨
    (∃ it ∈ consItemsK (cH H), it.pat = (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) :=
  tieOvlFnDist_item_withHooks ovlfn_text_83 H

/-- **In a model of Γ, sentence 83 with sentence 81 entails that item**, in both orders, for every H. -/
theorem ovlfn_entails_item_83 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax81).pat) (h : I ⊧ᴵ (trS U.ax83).pat) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) := by
  rw [ovlfn_trS_81] at hf
  rw [ovlfn_trS_83] at h
  have hfa := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_81
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at hfa
  exact tieOvlFnDist_weaker_Γ hI (gf := ovlFnGen0) (.inl rfl) hfa.1.2
    ((tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_83) ovlfn_sorts ((tieOvlFnArityB_withHooks c H _ _).trans ovlfn_arity_0) hf h _ _

/-! ## Sentences of a function-overloaded symbol: the covered part (by hand) -/

/- `capGas : Gas → Gas` overloads the function `capN : N → N`, N below Gas, and `capN(z)` is `z`.
The one value list `capN` covers is `[inj{N, Gas}(z)]` (`cov_inv_oft`: N holds `z` only), where the
application `capGas(inj z)` has the value `inj z` (`res_injZ_oft`). So, for every H:
- `capN` has a value at every covered value list (`ovlFnTotal_oft`), and the `functional` sentence
  of `capGas` (81) holds at values (`ovlfn_at_values_81`);
- two value lists at which `capGas` has one value are equal (`ovlFnInj_oft`: one covered list, a
  covered application's value is an injection and an uncovered one's the raw application), and the
  same-constructor sentence (82) holds at values (`ovlfn_at_values_82`);
- no value of an application of `capGas` is `inf` (`ovlFnDist_oft`), and the different-constructors
  sentence of `capGas` and `inf` (83) holds at values (`ovlfn_at_values_83`).
Each is in every model of `Γc`, at every valuation sending the sentence's variables to values'
elements (`EntailsAtValuesΓc`), with `FnHyp` proved for every H (`fnHypH`). -/

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
kernel_rfl inf_H : ∀ H : HookParams, lookupSig (cH H).ctorSigs infSig.name = some infSig
-- `capN`, the one function `capGas` overloads, is declared total.
kernel_rfl total_H : ∀ H : HookParams,
  ((cH H).fns.all fun fn => !((cH H).ovlOver oCap).any (·.name == fn.label) || fn.total) = true
-- `capGas`'s one overload is a function, of the result sort N.
kernel_rfl lifted_H : ∀ H : HookParams,
  (((cH H).ovlOver oCap).all fun kg => (cH H).ovlByFn kg && kg.result != oCap.sig.result) = true
kernel_rfl over_H : ∀ H : HookParams, (cH H).ovlOver oCap = [capNSig]
kernel_rfl sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [injZ] = some oCap.sig.args
kernel_rfl cover_H : ∀ H : HookParams, (cH H).fnCover oCap.sig.name [injZ] = some capNSig

/-- The one sort directly below Gas is N. -/
theorem below_gas_oft : ∀ p ∈ c.subsorts, p.2 = gasS → p.1 = nS := by decide +kernel

/-- **The one value list of `capGas`'s argument sort a function overload covers is `[inj z]`**,
covered by `capN`: a covered value is an injection into Gas, from N, of a value of N. -/
theorem cov_inv_oft (H : HookParams) {us : List GroundTerm} {kg : CtorSig}
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
    obtain rfl : C = nS := below_gas_oft _ hsub rfl
    rw [val_N_oft hw]; rfl
  | ctor f ts => simp [Semantics.lies, nS, gasS] at hl
  | dv s l => simp [Semantics.lies, nS, gasS] at hl
  | map s es => simp [Semantics.lies, nS, gasS] at hl
  | set s es => simp [Semantics.lies, nS, gasS] at hl
  | list s es => simp [Semantics.lies, nS, gasS] at hl

/-- **`capGas(inj z)` has the value `inj z`**, for every H: `capN` covers `inj z`, and `capN(z)` is
`z`, lifted to Gas. -/
theorem res_injZ_oft (H : HookParams) : OvlFnRes (cH H) oCap [injZ] (some injZ) :=
  OvlFnRes.fn (cover_H H) (eval_z_oft H)

theorem fun_shape_oft (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax81.ax = true := by
  have h := (tieOvlFnFunAtB_withHooks c H _ _ _).trans ovlfn_text_81
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem inj_shape_oft (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax82.ax = true := by
  have h := (tieOvlFnInjAtB_withHooks c H _ _ _).trans ovlfn_text_82
  simp only [tieOvlFnInjAtB, Bool.and_eq_true] at h
  exact h.1.2

theorem dist_shape_oft (H : HookParams) :
    tieOvlFnDistShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) (Gen.toK (cH H) (.ctor infSig))
      U.ax83.ax = true := by
  have h := (tieOvlFnDistAtB_withHooks c H _ _ _ _).trans ovlfn_text_83
  simp only [tieOvlFnDistAtB, Bool.and_eq_true] at h
  exact h.1.2

/-- **`OvlFnTotal`**, for every H: `capN`, declared total, has a value at every covered value list. -/
theorem ovlFnTotal_oft (H : HookParams) : OvlFnTotal (cH H) oCap :=
  ovlFnTotal_of_total (coreOKH H) (fnHypH H) (lookup_H H) (total_H H)

/-- **`OvlFnInj`**, for every H: one value list is covered. -/
theorem ovlFnInj_oft (H : HookParams) : OvlFnInj (cH H) oCap :=
  ovlFnInj_of_cov (lookup_H H) (lifted_H H) fun _ _ _ _ _ _ hus hvs h1 h2 _ _ _ =>
    (cov_inv_oft H hus h1).1.trans (cov_inv_oft H hvs h2).1.symm

/-- **`OvlFnDist capGas inf`**, for every H: `capGas`'s one overload is a function of the result
sort N, so a covered application's value is an injection. -/
theorem ovlFnDist_oft (H : HookParams) : OvlFnDist (cH H) oCap infSig :=
  ovlFnDist_of_lifted (lookup_H H) (lifted_H H) (by decide)

/-- **The `functional` sentence of `capGas` (81) holds at values, for every H**, in every model of
`Γc`. -/
theorem ovlfn_at_values_81 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax81 (trS U.ax81).pat := by
  rw [ovlfn_trS_81]
  exact ovlFnTotal_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnTotal_oft H) (fun_shape_oft H)

/-- **The same-constructor sentence of `capGas` (82) holds at values, for every H**, in every model
of `Γc`. -/
theorem ovlfn_at_values_82 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax82 (trS U.ax82).pat := by
  rw [ovlfn_trS_82]
  exact ovlFnInj_atValues (coreOKH H) (fnHypH H) (lookup_H H) (ovlFnInj_oft H) (inj_shape_oft H)

/-- **The different-constructors sentence of `capGas` and `inf` (83) holds at values, for every H**,
in every model of `Γc`. -/
theorem ovlfn_at_values_83 (H : HookParams) : EntailsAtValuesΓc (cH H) U.ax83 (trS U.ax83).pat := by
  rw [ovlfn_trS_83]
  exact ovlFnDist_atValues (coreOKH H) (fnHypH H) (lookup_H H) (inf_H H) rfl (ovlFnDist_oft H) (dist_shape_oft H)

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax64.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax64).pat = (trAxiom [] [] U.ax64).pat := by decide +kernel

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
theorem idem_vars : (U.ax64.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax64.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax64.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 64 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax64).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax64.ax.sortVars U.ax64.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax64.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax64.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 180, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax180).pat = (trAxiom [] [] U.ax180).pat := by decide +kernel
theorem s166_pattern : U.ax180.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax180.ax.sortVars.map sortVarKey ++ freeOf [] U.ax180.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax180.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 180 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax180.ax.sortVars U.ax180.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax180).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax180.ax.sortVars U.ax180.ax.pattern = t at he ⊢
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
/-- **Sentence 180 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax180 (trS U.ax180).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


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
theorem fns_entailed_c (H : HookParams) : ∀ ad ∈ fnText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (fns_entailed H ad had)
theorem nojunk_trivial_entailed_c (H : HookParams) :
    ∀ ad ∈ [U.ax126, U.ax132, U.ax135], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax128, U.ax129, U.ax130, U.ax131, U.ax133, U.ax134, U.ax137, U.ax138],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax136).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 64 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax64).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)
theorem ovleq_entailed_c (H : HookParams) : ∀ ad ∈ ovlEqText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (ovleq_entailed H ad had)
/-- **Over `Γc`, sentence 81 entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/
theorem ovlfn_entails_item_81_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) (h : I ⊧ᴵ (trS U.ax81).pat) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  ovlfn_entails_item_81 H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)) h
/-- **Over `Γc`, sentence 82 with sentence 81 entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/
theorem ovlfn_entails_item_82_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) (hf : I ⊧ᴵ (trS U.ax81).pat) (h : I ⊧ᴵ (trS U.ax82).pat) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) ((ovlArgsOf (cH H) ovlFnGen0).getD [])).pat :=
  ovlfn_entails_item_82 H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)) hf h
/-- **Over `Γc`, sentence 83 with sentence 81 entails Γ's item at uncovered arguments**, for every H: a model of `Γc` is one of Γ. -/
theorem ovlfn_entails_item_83_c (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γc (cH H)) (hf : I ⊧ᴵ (trS U.ax81).pat) (h : I ⊧ᴵ (trS U.ax83).pat) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen0) (Gen.toK (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1)).pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem ((cH H).sortName 32) (Gen.toK (cH H) ovlFnGen1) (Gen.toK (cH H) ovlFnGen0) (ovlArgsOf (cH H) ovlFnGen1) (ovlArgsOf (cH H) ovlFnGen0)).pat) :=
  ovlfn_entails_item_83 H (fun φ hφ => hI φ (Γ_sub_Γc _ hφ)) hf h

end KCore.TieE5OvlFunLhs

#check @KCore.TieE5OvlFunLhs.noRaw
#check @KCore.TieE5OvlFunLhs.readsConfined_c
#check @KCore.TieE5OvlFunLhs.userAxioms_eq
#check @KCore.TieE5OvlFunLhs.coreOK
#check @KCore.TieE5OvlFunLhs.wf_defn
#check @KCore.TieE5OvlFunLhs.account
#check @KCore.TieE5OvlFunLhs.account_sizes
#check @KCore.TieE5OvlFunLhs.account_classes
#check @KCore.TieE5OvlFunLhs.account_absent
#check @KCore.TieE5OvlFunLhs.absent_closed
#check @KCore.TieE5OvlFunLhs.absent_proj_below_c
#check @KCore.TieE5OvlFunLhs.absent_proj_below
#check @KCore.TieE5OvlFunLhs.lists_in_account
#check @KCore.TieE5OvlFunLhs.attrs_agree
#check @KCore.TieE5OvlFunLhs.sig_origin
#check @KCore.TieE5OvlFunLhs.decls_entailed
#check @KCore.TieE5OvlFunLhs.consistent
#check @KCore.TieE5OvlFunLhs.total_named
#check @KCore.TieE5OvlFunLhs.fnHypH
#check @KCore.TieE5OvlFunLhs.fnFun_indices
#check @KCore.TieE5OvlFunLhs.fnFun_account
#check @KCore.TieE5OvlFunLhs.fnFun_checked
#check @KCore.TieE5OvlFunLhs.fnFun_trS
#check @KCore.TieE5OvlFunLhs.fnFun_at_values
#check @KCore.TieE5OvlFunLhs.fnFun_at_values_step
#check @KCore.TieE5OvlFunLhs.fn_shape
#check @KCore.TieE5OvlFunLhs.fns_account
#check @KCore.TieE5OvlFunLhs.fns_entailed
#check @KCore.TieE5OvlFunLhs.fns_from_text
#check @KCore.TieE5OvlFunLhs.fn_prios
#check @KCore.TieE5OvlFunLhs.nojunk_trivial_entailed
#check @KCore.TieE5OvlFunLhs.nojunk_items_entailed
#check @KCore.TieE5OvlFunLhs.nojunk_kitem_entailed
#check @KCore.TieE5OvlFunLhs.cons_entailed
#check @KCore.TieE5OvlFunLhs.ovleq_account
#check @KCore.TieE5OvlFunLhs.ovleq_entailed
#check @KCore.TieE5OvlFunLhs.ovlfn_index
#check @KCore.TieE5OvlFunLhs.ovlfn_text_81
#check @KCore.TieE5OvlFunLhs.ovlfn_item_in_gamma_81
#check @KCore.TieE5OvlFunLhs.ovlfn_entails_item_81
#check @KCore.TieE5OvlFunLhs.ovlfn_text_82
#check @KCore.TieE5OvlFunLhs.ovlfn_item_in_gamma_82
#check @KCore.TieE5OvlFunLhs.ovlfn_entails_item_82
#check @KCore.TieE5OvlFunLhs.ovlfn_text_83
#check @KCore.TieE5OvlFunLhs.ovlfn_item_in_gamma_83
#check @KCore.TieE5OvlFunLhs.ovlfn_entails_item_83
#check @KCore.TieE5OvlFunLhs.ovlfn_at_values_81
#check @KCore.TieE5OvlFunLhs.ovlfn_at_values_82
#check @KCore.TieE5OvlFunLhs.ovlfn_at_values_83
#check @KCore.TieE5OvlFunLhs.idem_refuted
#check @KCore.TieE5OvlFunLhs.lib166
#check @KCore.TieE5OvlFunLhs.lib166_at_values
#check @KCore.TieE5OvlFunLhs.nojunk_gas_order
#check @KCore.TieE5OvlFunLhs.nojunk_gas_members
#check @KCore.TieE5OvlFunLhs.nojunk_gas_entailed
#check @KCore.TieE5OvlFunLhs.gammaCl_eq
#check @KCore.TieE5OvlFunLhs.decls_entailed_c
#check @KCore.TieE5OvlFunLhs.fns_entailed_c
#check @KCore.TieE5OvlFunLhs.nojunk_trivial_entailed_c
#check @KCore.TieE5OvlFunLhs.nojunk_items_entailed_c
#check @KCore.TieE5OvlFunLhs.nojunk_kitem_entailed_c
#check @KCore.TieE5OvlFunLhs.cons_entailed_c
#check @KCore.TieE5OvlFunLhs.idem_refuted_c
#check @KCore.TieE5OvlFunLhs.ovleq_entailed_c
#check @KCore.TieE5OvlFunLhs.ovlfn_entails_item_81_c
#check @KCore.TieE5OvlFunLhs.ovlfn_entails_item_82_c
#check @KCore.TieE5OvlFunLhs.ovlfn_entails_item_83_c
#print axioms KCore.TieE5OvlFunLhs.noRaw
#print axioms KCore.TieE5OvlFunLhs.readsConfined_c
#print axioms KCore.TieE5OvlFunLhs.userAxioms_eq
#print axioms KCore.TieE5OvlFunLhs.coreOK
#print axioms KCore.TieE5OvlFunLhs.wf_defn
#print axioms KCore.TieE5OvlFunLhs.account
#print axioms KCore.TieE5OvlFunLhs.account_sizes
#print axioms KCore.TieE5OvlFunLhs.account_classes
#print axioms KCore.TieE5OvlFunLhs.account_absent
#print axioms KCore.TieE5OvlFunLhs.absent_closed
#print axioms KCore.TieE5OvlFunLhs.absent_proj_below_c
#print axioms KCore.TieE5OvlFunLhs.absent_proj_below
#print axioms KCore.TieE5OvlFunLhs.lists_in_account
#print axioms KCore.TieE5OvlFunLhs.attrs_agree
#print axioms KCore.TieE5OvlFunLhs.sig_origin
#print axioms KCore.TieE5OvlFunLhs.decls_entailed
#print axioms KCore.TieE5OvlFunLhs.consistent
#print axioms KCore.TieE5OvlFunLhs.total_named
#print axioms KCore.TieE5OvlFunLhs.fnHypH
#print axioms KCore.TieE5OvlFunLhs.fnFun_indices
#print axioms KCore.TieE5OvlFunLhs.fnFun_account
#print axioms KCore.TieE5OvlFunLhs.fnFun_checked
#print axioms KCore.TieE5OvlFunLhs.fnFun_trS
#print axioms KCore.TieE5OvlFunLhs.fnFun_at_values
#print axioms KCore.TieE5OvlFunLhs.fnFun_at_values_step
#print axioms KCore.TieE5OvlFunLhs.fn_shape
#print axioms KCore.TieE5OvlFunLhs.fns_account
#print axioms KCore.TieE5OvlFunLhs.fns_entailed
#print axioms KCore.TieE5OvlFunLhs.fns_from_text
#print axioms KCore.TieE5OvlFunLhs.fn_prios
#print axioms KCore.TieE5OvlFunLhs.nojunk_trivial_entailed
#print axioms KCore.TieE5OvlFunLhs.nojunk_items_entailed
#print axioms KCore.TieE5OvlFunLhs.nojunk_kitem_entailed
#print axioms KCore.TieE5OvlFunLhs.cons_entailed
#print axioms KCore.TieE5OvlFunLhs.ovleq_account
#print axioms KCore.TieE5OvlFunLhs.ovleq_entailed
#print axioms KCore.TieE5OvlFunLhs.ovlfn_index
#print axioms KCore.TieE5OvlFunLhs.ovlfn_text_81
#print axioms KCore.TieE5OvlFunLhs.ovlfn_item_in_gamma_81
#print axioms KCore.TieE5OvlFunLhs.ovlfn_entails_item_81
#print axioms KCore.TieE5OvlFunLhs.ovlfn_text_82
#print axioms KCore.TieE5OvlFunLhs.ovlfn_item_in_gamma_82
#print axioms KCore.TieE5OvlFunLhs.ovlfn_entails_item_82
#print axioms KCore.TieE5OvlFunLhs.ovlfn_text_83
#print axioms KCore.TieE5OvlFunLhs.ovlfn_item_in_gamma_83
#print axioms KCore.TieE5OvlFunLhs.ovlfn_entails_item_83
#print axioms KCore.TieE5OvlFunLhs.ovlfn_at_values_81
#print axioms KCore.TieE5OvlFunLhs.ovlfn_at_values_82
#print axioms KCore.TieE5OvlFunLhs.ovlfn_at_values_83
#print axioms KCore.TieE5OvlFunLhs.idem_refuted
#print axioms KCore.TieE5OvlFunLhs.lib166
#print axioms KCore.TieE5OvlFunLhs.lib166_at_values
#print axioms KCore.TieE5OvlFunLhs.nojunk_gas_order
#print axioms KCore.TieE5OvlFunLhs.nojunk_gas_members
#print axioms KCore.TieE5OvlFunLhs.nojunk_gas_entailed
#print axioms KCore.TieE5OvlFunLhs.gammaCl_eq
#print axioms KCore.TieE5OvlFunLhs.decls_entailed_c
#print axioms KCore.TieE5OvlFunLhs.fns_entailed_c
#print axioms KCore.TieE5OvlFunLhs.nojunk_trivial_entailed_c
#print axioms KCore.TieE5OvlFunLhs.nojunk_items_entailed_c
#print axioms KCore.TieE5OvlFunLhs.nojunk_kitem_entailed_c
#print axioms KCore.TieE5OvlFunLhs.cons_entailed_c
#print axioms KCore.TieE5OvlFunLhs.idem_refuted_c
#print axioms KCore.TieE5OvlFunLhs.ovleq_entailed_c
#print axioms KCore.TieE5OvlFunLhs.ovlfn_entails_item_81_c
#print axioms KCore.TieE5OvlFunLhs.ovlfn_entails_item_82_c
#print axioms KCore.TieE5OvlFunLhs.ovlfn_entails_item_83_c
