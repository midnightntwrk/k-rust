/-
  The tie (C14) on `f2-examples/e2-cool-eq.kompile.kore`, the kompiled text of construct fixture e2-cool-eq
  (`test/constructs/fixtures/e2-cool-eq`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e2-cool-eq`, its consistency section by hand; run from the package root:
  `lake env lean -j1 test/TieE2CoolEq.lean`.

  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its
  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise
  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end), and every
  premise of `Γc` is a premise of Γ or `boolClosed`, the one item of `Γcl` here, which no sentence
  states (`gamma_origin_c`).

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 259 sentences of the user module E2-COOL-EQ, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 206 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads a confined sort (`readsConfined_c`) and has no open generator
    (`noRaw`). It owes the match independence of a clause (`match_named`) and the condition of a rule or clause (`owed_rules`, `owed_clauses`).
    The consistency section, written by hand, proves what it owes for every H (`openDecidedH`),
    so `Γc` with the step's closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (26): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (62): Γ with it has no model (`idem_refuted`).
  - Library sample, 161 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); user lemma: owed, by hand
    (`userlemma_account`, `UserLemmaEntailed`, `UserLemmaAtValues`); no direction: `absent_closed`.

  The user lemmas (205) are sentences of a user's file that the reader leaves out of Γ as lemmas
  (inert simplification) and that apply no parameter symbol without `impl`. Of the class `user
  lemma` (direction `entailed`): 205, each owed as `Γ (cH H) ⊧ (trS ad).pat` for every H
  (`UserLemmaEntailed`). Both are stated here and proved by hand: owed. A lemma that is false has no
  proof, and its text is not tied.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (11);
  the sentences of a class with a theorem that no theorem here holds of, and the user lemmas, are
  `uncovered` (1).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2CoolEq

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cool-eq.kompile.kore"
definition_of defn from "f2-examples/e2-cool-eq.kompile.kore"
user_axioms U from "f2-examples/e2-cool-eq.kompile.kore" module "E2-COOL-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-COOL-EQ")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 259 := by decide +kernel

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

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [204, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227,
      228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 101, 102]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30]),
   ("distinctness", []),
   ("no junk", [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]),
   ("function functional", [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      57, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 77, 78, 79, 81, 98, 99, 100, 103, 104, 105, 106,
      107, 108]),
   ("collection law", [54, 55, 56, 58, 59, 60, 61, 63, 64]),
   ("library", [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
      145, 146, 147, 148, 149, 150, 151, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
      164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181,
      182, 183, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200,
      201, 202, 203, 206, 242, 243, 244, 245, 260, 261]),
   ("set idempotence", [62]),
   ("set-variable lemma", [122, 123, 124, 125, 126, 262]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", [205]),
   ("user lemma at values", []),
   ("no direction", [37, 41, 43, 74, 76, 80, 97, 109, 110, 152, 184, 207, 208, 209, 210, 240, 241, 246, 247, 248,
      249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259])]

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
    [("function equation", 30), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 16), ("injectivity", 4), ("distinctness", 0), ("no junk", 11), ("function functional", 15), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 1), ("user lemma at values", 0), ("no direction", 31)] := by
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
  [(246, "Bool"), (247, "GeneratedCounterCell"), (248, "GeneratedCounterCellOpt"),
   (249, "GeneratedTopCell"), (250, "GeneratedTopCellFragment"), (251, "Int"), (252, "K"),
   (253, "KCell"), (254, "KCellOpt"), (255, "KItem"), (256, "KResult"), (257, "List"),
   (258, "Map"), (259, "Set")]

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
  [(9, "subsort"), (18, "subsort"), (93, "function functional"), (120, "no junk"),
   (121, "no junk"), (204, "function equation"), (205, "user lemma"), (210, "no direction"),
   (232, "function equation"), (233, "function equation"), (256, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of, and
the user lemmas, of which the tie has no generated theorem: the tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(205, "user lemma")]

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 129, 91, 5, 33) := by
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

/-! ## Consistency for every H: `f(X) => X requires true andBool isKResult(HOLE)`, witnessed at HOLE := `kseq(inj{Int,KItem}(0), dotk)` -/

def fS : Sym := 385
def krS : Sym := 382
def andS : Sym := 4
def krSort : Srt := 32

theorem symNames : c.symName fS = "Lblf" ∧ c.symName krS = "LblisKResult" ∧ c.symName andS = "Lbl'Unds'andBool'Unds'" ∧
    c.sortName krSort = "KResult" := by
  decide +kernel

/-- `f(X) => X requires true andBool isKResult(HOLE)`, X:Int, HOLE:K -/
def clCool : Clause :=
  { vars := [Srt.int, Srt.k], pats := [.var 0],
    req := some (.app andS [.dv Srt.bool (.bool true), .app krS [.var 1]]), rhs := .var 0, ens := none }
def fCool : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clCool] }
/-- `isKResult(kseq(inj{KResult,KItem}(V), dotk)) = true`, V:KResult -/
def kr1 : Clause :=
  { vars := [krSort], pats := [.app kseq [.inj krSort Srt.kitem (.var 0), .app dotk []]], req := none,
    rhs := .dv Srt.bool (.bool true), ens := none }
/-- otherwise `false` -/
def kr2 : Clause :=
  { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def fKR : Fn := ⟨krS, [Srt.k], Srt.bool, [kr1, kr2], true⟩

/-- The reader's function `f` is `fCool`; `isKResult` is the generated sort predicate `fKR`. -/
theorem fns_text : c.fns = [fCool] := by rfl
theorem lookupKR : c.lookupFn krS = some fKR := by rfl

theorem fnsH (H : HookParams) : (cH H).fns = [fCool] := fns_text
theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fCool := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem lookupKRH (H : HookParams) : (cH H).lookupFn krS = some fKR := by
  rw [Semantics.lookupFn_withHooks]; exact lookupKR
theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

/-- The clause of `f` needs a witness: its condition holds HOLE only, of K, which is not confined. -/
theorem needs : clCool.needsWitness c = true ∧ c.confined Srt.k = false ∧ clCool.condVars = [1] := by
  decide +kernel

/-- `kseq(inj{Int,KItem}(0), dotk)`: a K whose one item is an Int, so a KResult. -/
def hole : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (.dv Srt.int (.int 0)), .ctor dotk []]

theorem hole_sort : c.sortOf hole = some Srt.k := by decide +kernel

theorem syms (H : HookParams) : (cH H).isCtor kseq = true ∧ (cH H).isCtor dotk = true ∧
    (cH H).isCtor krS = false ∧ isHook krS = false ∧ (cH H).isParam krS = false ∧
    (cH H).isCtor andS = false ∧ isHook andS = true :=
  (by decide +kernel : c.isCtor kseq = true ∧ c.isCtor dotk = true ∧ c.isCtor krS = false ∧ isHook krS = false ∧
    c.isParam krS = false ∧ c.isCtor andS = false ∧ isHook andS = true)

/-- V := `inj{Int,KResult}(0)`, the match of `kr1` at `hole`. -/
def σV : Subst := [(0, .inj Srt.int krSort (.dv Srt.int (.int 0)))]

theorem σV_sorted (H : HookParams) : (cH H).WellSorted kr1.vars σV := fun i s hs => by
  cases i with
  | zero =>
    cases (show some krSort = some s from hs)
    exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
  | succ i => cases (show (none : Option Srt) = some s from hs)

theorem kr1_match (H : HookParams) : PatVals (cH H) σV kr1.pats [hole] :=
  .cons (.ctor (syms H).1
    (.cons (PatVal.inj (w := .inj Srt.int krSort (.dv Srt.int (.int 0))) (.var rfl))
      (.cons (.ctor (syms H).2.1 .nil) .nil))) .nil

/-- **`isKResult(hole)` is `true`**, by `kr1`: no clause of a smaller priority. -/
theorem kr_hole (H : HookParams) : Eval (cH H) krS [hole] (some (bool true)) :=
  .clause (lookupKRH H) (List.mem_cons_self ..) (σV_sorted H) (kr1_match H) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      rcases List.mem_cons.mp hcl' with rfl | hcl'
      · exact absurd hlt (by decide)
      · rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `isKResult(HOLE)` under a σ giving HOLE the value `hole`: `true`. -/
theorem call_kr (H : HookParams) {σ : Subst} (h1 : σ.lookup 1 = some hole) :
    EvalTerm (cH H) σ (.app krS [.var 1]) (some (bool true)) :=
  .call (vs := [hole]) (syms H).2.2.1 (syms H).2.2.2.1 (.cons .var .nil) (by rw [h1]; rfl) (kr_hole H)
    (syms H).2.2.2.2.1

/-- The `requires` under a σ giving HOLE the value `hole`: `true andBool true`, so `true`. -/
theorem req_true (H : HookParams) {σ : Subst} (h1 : σ.lookup 1 = some hole) :
    EvalTerm (cH H) σ (.app andS [.dv Srt.bool (.bool true), .app krS [.var 1]]) (some (bool true)) :=
  .hook (syms H).2.2.2.2.2.1 (syms H).2.2.2.2.2.2 (.cons .dv (.cons (call_kr H h1) .nil))
    (fun vs hvs => by cases hvs; exact Semantics.hookRes_of_value (by decide +kernel)) (fun h => by cases h)

theorem clCool_exs : clCool.exs = [] := by decide +kernel

/-- **The clause of `f` is match independent, for every H**: its right side is X, and two matches
at one argument list give X the argument. -/
theorem matchCool (H : HookParams) : MatchIndependent (cH H) clCool := by
  refine (matchIndependent_iff_noExs clCool_exs).mpr fun vs σ σ' ha ha' _ _ _ _ _ => .inl
    ⟨clCool_exs, clCool_exs, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have hi0 : i = 0 := by simpa [clCool, varOccs] using hi
  subst hi0
  have hp := ha.2.1
  have hp' := ha'.2.1
  cases hp with
  | cons h1 hn =>
    cases hn
    cases hp' with
    | cons h1' hn' =>
      cases hn'
      cases h1 with
      | var h => cases h1' with
        | var h' => rw [h, h']

def callOrder : List Nat := [fS]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause of `f` is the one clause whose match independence no decider shows. -/
theorem match_named : c.matchObligationsL = [(fS, 0)] := by decide +kernel

theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
/-- The clause of `f` is the one whose condition is owed: HOLE:K is bound by no argument, and K is
not confined. -/
theorem owed_clauses : c.owedClauses = [(0, 0)] := by decide +kernel

/-- The facts the deciders leave, for every H: the match independence of `f`'s clause. -/
theorem factsH (H : HookParams) : FnFacts (cH H) callOrder [] := by
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, fun p hp fn hfn cl hcl => ?_, openLaws_of_plain noRaw⟩
  · rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Semantics.totalObligationsRP_withHooks _ H _ _, total_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Det.Semantics.agreeObligationsI_withHooks, agree_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Det.Semantics.matchObligationsL_withHooks, match_named, List.mem_singleton] at hp
    subst hp
    rw [lookupFH H] at hfn
    cases hfn
    simp only [fCool, List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchCool H

/-- **`f` and `isKResult` have one result, for every H**, from the deciders' facts without the owed
condition (`TiePair.fnModel_noTotal`). -/
theorem fnDetH (H : HookParams) : FnDet (cH H) :=
  (TiePair.fnModel_noTotal (c := cH H)
    (hpreTop := by simp only [Semantics.clausesPreTop_withHooks]; decide +kernel)
    (hnoEx := (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))) (ord := callOrder) (coreOKH H)
    (fun g _ => (Semantics.rightHeld_withHooks (Semantics.rightHeld_of_valued (by decide +kernel)) H noRaw).heldOwed g)
    (factsH H).1 (factsH H).2.2.1 (factsH H).2.2.2.1).1

/-- **The clause of `f` is `Witnessed`, for every H**, at HOLE := `hole`: its `requires` is `true`
and nothing else. -/
theorem witnessedH (H : HookParams) : clCool.Witnessed (cH H) := by
  refine ⟨[(1, hole)], fun j hj s hs => ?_, fun t ht => ?_, .top⟩
  · rw [needs.2.2] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.k = some s from hs)
    exact ⟨hole, rfl, by rw [sortOfH]; exact hole_sort⟩
  · cases ht
    exact ⟨req_true H rfl, fun r hr => EvalTerm.functional_of_fnDet (fnDetH H) hr (req_true H rfl)⟩

/-- **The owed condition is decided, for every H** (`OpenDecided`): no rule needs a witness, and
the one clause that does is `Witnessed`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) := by
  refine ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
    openClauses_of_owed fun p hp fn hfn cl hcl => ?_⟩
  rw [Semantics.owedClauses_withHooks, owed_clauses, List.mem_singleton] at hp
  subst hp
  rw [fnsH] at hfn
  cases hfn
  cases hcl
  exact .inl (witnessedH H)

theorem obl (H : HookParams) : FnObligations (cH H) callOrder [] := (factsH H).obligations (openDecidedH H)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl H)

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (30 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 30 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax204, U.ax223, U.ax231, U.ax230, U.ax229, U.ax228, U.ax237, U.ax236, U.ax239, U.ax238,
   U.ax235, U.ax234, U.ax212, U.ax211, U.ax222, U.ax221, U.ax218, U.ax217, U.ax220, U.ax219,
   U.ax225, U.ax224, U.ax227, U.ax226, U.ax214, U.ax213, U.ax216, U.ax215, U.ax233, U.ax232]

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

theorem nj111 : (trS U.ax111).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj116 : (trS U.ax116).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj119 : (trS U.ax119).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax111, U.ax116, U.ax119], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj111]; exact orTopBot_valid hD rfl
  · rw [nj116]; exact orTopBot_valid hD rfl
  · rw [nj119]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax112, U.ax113, U.ax114, U.ax115, U.ax117, U.ax118, U.ax121],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax112, U.ax113, U.ax114, U.ax115, U.ax117, U.ax118, U.ax121],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax120).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (120)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax120).pat := by
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
   U.ax101, U.ax102]

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

theorem idem_pattern : U.ax62.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax62).pat = (trAxiom [] [] U.ax62).pat := by decide +kernel

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
theorem idem_vars : (U.ax62.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax62.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax62.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 62 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax62).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax62.ax.sortVars U.ax62.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax62.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax62.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 161, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax161).pat = (trAxiom [] [] U.ax161).pat := by decide +kernel
theorem s166_pattern : U.ax161.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax161.ax.sortVars.map sortVarKey ++ freeOf [] U.ax161.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax161.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 161 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax161.ax.sortVars U.ax161.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax161).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax161.ax.sortVars U.ax161.ax.pattern = t at he ⊢
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
      unfold symApp; rw [(sub_name H).1, (sub_name H).2]; rfl
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
/-- **Sentence 161 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax161 (trS U.ax161).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The user lemmas (205): owed, by hand -/

/-- The lemmas of a user's file that the reader leaves out of Γ and that apply no parameter symbol
without `impl`, of the class `user lemma`. -/
noncomputable def userLemmaText : List AxiomDecl := [U.ax205]

/-- Those of the class `user lemma at values`. -/
noncomputable def userLemmaValuesText : List AxiomDecl := []

/-- The two lists are the account's classes `user lemma`, of the direction `entailed`, and
`user lemma at values`, of the direction `atValues`. -/
theorem userlemma_account : userLemmaText.map (·.index) = classOf "user lemma" ∧
    userLemmaValuesText.map (·.index) = classOf "user lemma at values" := by
  decide +kernel

/-- **What the tie owes of the user lemmas of the class `user lemma`**: Γ entails each, for
every interpretation `H`. Stated, not proved here: the proof is owed. -/
def UserLemmaEntailed : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaText, Γ (cH H) ⊧ (trS ad).pat

/-- **What the tie owes of the user lemmas of the class `user lemma at values`**: each holds in
every model of Γ at the valuations sending its free element variables to values, for every
interpretation `H`. Stated, not proved here: the proof is owed. -/
def UserLemmaAtValues : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaValuesText, EntailsAtValues (cH H) ad (trS ad).pat

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

/-- **The origin of each premise of `Γc`**: one of Γ's (`gamma_origin`), or `boolClosed`, the item
of `Γcl`: every element of Bool is `true` or `false`, a family of the reading of a definition that
reads a confined sort, which no sentence of the text states. -/
theorem gamma_origin_c (H : HookParams) : ∀ φ, Γc (cH H) φ →
    ((∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨
      (∃ x : EVar, φ = @definedness KoreAML.Sym _ x)) ∨ φ = boolClosed (cH H) := by
  intro φ h
  rcases h with h | h
  · exact Or.inl (gamma_origin H φ h)
  · exact Or.inr ((gammaCl_eq H φ).mp h)

/-- Every premise of `Γc` is a consequence of `Pre` with `Γcl`. -/
theorem gamma_from_c (H : HookParams) : ∀ φ, Γc (cH H) φ → (Pre H ∪ Γcl (cH H)) ⊧ φ := by
  intro φ h M _ I hI
  rcases h with h | h
  · exact gamma_from H φ h (fun ψ hψ => hI ψ (Or.inl hψ))
  · exact hI _ (Or.inr h)

theorem decls_entailed_c (H : HookParams) : ∀ it ∈ declItems, Γc (cH H) ⊧ it.pat :=
  fun it hit => entails_c (decls_entailed H it hit)
theorem fns_entailed_c (H : HookParams) : ∀ ad ∈ fnText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (fns_entailed H ad had)
theorem nojunk_trivial_entailed_c (H : HookParams) :
    ∀ ad ∈ [U.ax111, U.ax116, U.ax119], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ [U.ax112, U.ax113, U.ax114, U.ax115, U.ax117, U.ax118, U.ax121],
    Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_items_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax120).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 62 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax62).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieE2CoolEq

#check @KCore.TieE2CoolEq.noRaw
#check @KCore.TieE2CoolEq.readsConfined_c
#check @KCore.TieE2CoolEq.userAxioms_eq
#check @KCore.TieE2CoolEq.coreOK
#check @KCore.TieE2CoolEq.wf_defn
#check @KCore.TieE2CoolEq.account
#check @KCore.TieE2CoolEq.account_sizes
#check @KCore.TieE2CoolEq.account_classes
#check @KCore.TieE2CoolEq.account_absent
#check @KCore.TieE2CoolEq.absent_closed
#check @KCore.TieE2CoolEq.absent_proj_below_c
#check @KCore.TieE2CoolEq.absent_proj_below
#check @KCore.TieE2CoolEq.lists_in_account
#check @KCore.TieE2CoolEq.attrs_agree
#check @KCore.TieE2CoolEq.sig_origin_but_next
#check @KCore.TieE2CoolEq.decls_entailed
#check @KCore.TieE2CoolEq.consistent
#check @KCore.TieE2CoolEq.text_nextless
#check @KCore.TieE2CoolEq.fn_shape
#check @KCore.TieE2CoolEq.fns_account
#check @KCore.TieE2CoolEq.fns_entailed
#check @KCore.TieE2CoolEq.fns_from_text
#check @KCore.TieE2CoolEq.fn_prios
#check @KCore.TieE2CoolEq.nojunk_trivial_entailed
#check @KCore.TieE2CoolEq.nojunk_items_entailed
#check @KCore.TieE2CoolEq.nojunk_kitem_entailed
#check @KCore.TieE2CoolEq.cons_entailed
#check @KCore.TieE2CoolEq.idem_refuted
#check @KCore.TieE2CoolEq.lib166
#check @KCore.TieE2CoolEq.lib166_at_values
#check @KCore.TieE2CoolEq.gamma_origin
#check @KCore.TieE2CoolEq.gamma_from
#check @KCore.TieE2CoolEq.userlemma_account
#check @KCore.TieE2CoolEq.UserLemmaEntailed
#check @KCore.TieE2CoolEq.UserLemmaAtValues
#check @KCore.TieE2CoolEq.owed_rules
#check @KCore.TieE2CoolEq.owed_clauses
#check @KCore.TieE2CoolEq.openDecidedH
#check @KCore.TieE2CoolEq.gammaCl_eq
#check @KCore.TieE2CoolEq.gamma_origin_c
#check @KCore.TieE2CoolEq.gamma_from_c
#check @KCore.TieE2CoolEq.decls_entailed_c
#check @KCore.TieE2CoolEq.fns_entailed_c
#check @KCore.TieE2CoolEq.nojunk_trivial_entailed_c
#check @KCore.TieE2CoolEq.nojunk_items_entailed_c
#check @KCore.TieE2CoolEq.nojunk_kitem_entailed_c
#check @KCore.TieE2CoolEq.cons_entailed_c
#check @KCore.TieE2CoolEq.idem_refuted_c
#print axioms KCore.TieE2CoolEq.noRaw
#print axioms KCore.TieE2CoolEq.readsConfined_c
#print axioms KCore.TieE2CoolEq.userAxioms_eq
#print axioms KCore.TieE2CoolEq.coreOK
#print axioms KCore.TieE2CoolEq.wf_defn
#print axioms KCore.TieE2CoolEq.account
#print axioms KCore.TieE2CoolEq.account_sizes
#print axioms KCore.TieE2CoolEq.account_classes
#print axioms KCore.TieE2CoolEq.account_absent
#print axioms KCore.TieE2CoolEq.absent_closed
#print axioms KCore.TieE2CoolEq.absent_proj_below_c
#print axioms KCore.TieE2CoolEq.absent_proj_below
#print axioms KCore.TieE2CoolEq.lists_in_account
#print axioms KCore.TieE2CoolEq.attrs_agree
#print axioms KCore.TieE2CoolEq.sig_origin_but_next
#print axioms KCore.TieE2CoolEq.decls_entailed
#print axioms KCore.TieE2CoolEq.consistent
#print axioms KCore.TieE2CoolEq.text_nextless
#print axioms KCore.TieE2CoolEq.fn_shape
#print axioms KCore.TieE2CoolEq.fns_account
#print axioms KCore.TieE2CoolEq.fns_entailed
#print axioms KCore.TieE2CoolEq.fns_from_text
#print axioms KCore.TieE2CoolEq.fn_prios
#print axioms KCore.TieE2CoolEq.nojunk_trivial_entailed
#print axioms KCore.TieE2CoolEq.nojunk_items_entailed
#print axioms KCore.TieE2CoolEq.nojunk_kitem_entailed
#print axioms KCore.TieE2CoolEq.cons_entailed
#print axioms KCore.TieE2CoolEq.idem_refuted
#print axioms KCore.TieE2CoolEq.lib166
#print axioms KCore.TieE2CoolEq.lib166_at_values
#print axioms KCore.TieE2CoolEq.gamma_origin
#print axioms KCore.TieE2CoolEq.gamma_from
#print axioms KCore.TieE2CoolEq.userlemma_account
#print axioms KCore.TieE2CoolEq.UserLemmaEntailed
#print axioms KCore.TieE2CoolEq.UserLemmaAtValues
#print axioms KCore.TieE2CoolEq.owed_rules
#print axioms KCore.TieE2CoolEq.owed_clauses
#print axioms KCore.TieE2CoolEq.openDecidedH
#print axioms KCore.TieE2CoolEq.gammaCl_eq
#print axioms KCore.TieE2CoolEq.gamma_origin_c
#print axioms KCore.TieE2CoolEq.gamma_from_c
#print axioms KCore.TieE2CoolEq.decls_entailed_c
#print axioms KCore.TieE2CoolEq.fns_entailed_c
#print axioms KCore.TieE2CoolEq.nojunk_trivial_entailed_c
#print axioms KCore.TieE2CoolEq.nojunk_items_entailed_c
#print axioms KCore.TieE2CoolEq.nojunk_kitem_entailed_c
#print axioms KCore.TieE2CoolEq.cons_entailed_c
#print axioms KCore.TieE2CoolEq.idem_refuted_c
