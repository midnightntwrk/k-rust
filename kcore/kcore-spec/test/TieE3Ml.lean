/-
  The tie (C14) on `f2-examples/e3-ml.kompile.kore`, the kompiled text of construct fixture e3-ml
  (`test/constructs/fixtures/e3-ml`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml`; run from the package root: `lake env lean -j1 test/TieE3Ml.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 260 sentences of the user module E3-ML, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 206 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (24): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 6 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (60): Γ with it has no model (`idem_refuted`).
  - Library sample, 163 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); parameter lemma: a hypothesis on H, at values, shown at one H
    (`paramlemma_account`, `paramlemma_heads`, `ParamLemmaWitnessAtValues`, `e3ml_witness`,
    `e3ml_open`); user lemma: entailed, by hand (`userlemma_account`, `userlemma_entailed`); no
    direction: `absent_closed`.

  The parameter lemmas (126, 127, 210, 211) apply a parameter symbol no registry hook interprets,
  whose value the interpretation gives: each is owed as a hypothesis on H, at the valuations sending
  its variables to values (`EntailsAtValues (cH H) ad (trS ad).pat`), since Γ states the parameter's
  graph at values only (`ΓDomains`). The account holds them in the class `parameter lemma`, of the
  direction `hypothesis`. A hypothesis no H satisfies would tie a text without a model, so the tie
  owes one H at which the functions' obligations hold and every parameter lemma holds at values
  (`ParamLemmaWitnessAtValues`). Proved here, by hand: at `H1`, the interpretation with `h(n) = n`,
  the obligations hold and each parameter lemma holds in every model of Γ at the valuations sending
  its variable to a value (`e3ml_witness`); at `HookParams.none` Γ with sentence 210 has no model
  (`e3ml_open`), so the class is no `entailed`. Every `simplification` equation of the user module
  whose left side's head is a parameter symbol without `impl` is one of them (`paramlemma_heads`).

  The user lemmas (123, 124, 125, 152) are sentences of a user's file that the reader leaves out of
  Γ as lemmas (inert simplification) and that apply no parameter symbol without `impl`. Of the class
  `user lemma` (direction `entailed`): 123, 124, 125, 152, each owed as `Γ (cH H) ⊧ (trS ad).pat`
  for every H (`UserLemmaEntailed`), proved here by hand (`userlemma_entailed`): `f` and `g` are the
  identity at every element of Int in every model of Γ (`fg_id_eml`, from the equations 206 and 208,
  Γ's items), which makes each side of each lemma the whole of its sort.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (12);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3Ml

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml.kompile.kore"
definition_of defn from "f2-examples/e3-ml.kompile.kore"
user_axioms U from "f2-examples/e3-ml.kompile.kore" module "E3-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 260 := by decide +kernel

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
  [("function equation", [206, 208, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
      231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241]),
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
   ("library", [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
      146, 147, 148, 149, 150, 151, 153, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165,
      166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183,
      184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
      203, 204, 205, 207, 244, 245, 246, 247, 261, 262]),
   ("set idempotence", [60]),
   ("set-variable lemma", [118, 119, 120, 121, 122, 263]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", [126, 127, 210, 211]),
   ("user lemma", [123, 124, 125, 152]),
   ("user lemma at values", []),
   ("no direction", [35, 39, 41, 72, 74, 78, 94, 106, 107, 154, 186, 209, 212, 213, 214, 242, 243, 248, 249, 250,
      251, 252, 253, 254, 255, 256, 257, 258, 259, 260])]

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
    [("function equation", 29), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 6), ("subsort", 14), ("injectivity", 4), ("distinctness", 0), ("no junk", 10), ("function functional", 14), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 4), ("user lemma", 4), ("user lemma at values", 0), ("no direction", 30)] := by
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

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(117, "no junk"), (123, "user lemma"), (124, "user lemma"), (125, "user lemma"),
   (126, "parameter lemma"), (127, "parameter lemma"), (152, "user lemma"),
   (206, "function equation"), (208, "function equation"), (210, "parameter lemma"),
   (211, "parameter lemma"), (214, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text (the user lemmas are proved by hand, `userlemma_entailed`). -/
def uncovered : List (Nat × String) := []

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

/-! ## Consistency for every H -/

def callOrder : List Nat := [
384,385]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (29 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax206, U.ax208, U.ax227, U.ax235, U.ax234, U.ax233, U.ax232, U.ax239, U.ax238, U.ax241,
   U.ax240, U.ax237, U.ax236, U.ax216, U.ax215, U.ax226, U.ax225, U.ax222, U.ax221, U.ax224,
   U.ax223, U.ax229, U.ax228, U.ax231, U.ax230, U.ax218, U.ax217, U.ax220, U.ax219]

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


/-! ## Library sample: sentence 163, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax163).pat = (trAxiom [] [] U.ax163).pat := by decide +kernel
theorem s166_pattern : U.ax163.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax163.ax.sortVars.map sortVarKey ++ freeOf [] U.ax163.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax163.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 163 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax163.ax.sortVars U.ax163.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax163).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax163.ax.sortVars U.ax163.ax.pattern = t at he ⊢
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
/-- **Sentence 163 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax163 (trS U.ax163).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The parameter lemmas (126, 127, 210, 211): owed as a hypothesis on H -/

/-- The text's lemmas that apply a parameter symbol no registry hook interprets (`isParamLemma`). -/
noncomputable def paramLemmaText : List AxiomDecl := [U.ax126, U.ax127, U.ax210, U.ax211]

/-- The parameter lemmas are the account's class `parameter lemma`, of the direction `hypothesis`
(Γ does not hold the sentence; at the member `cH H` it is owed at values). -/
theorem paramlemma_account : paramLemmaText.map (·.index) = classOf "parameter lemma" := by
  decide +kernel

/-- **What the tie owes of the parameter lemmas**: one interpretation `H` at which the functions'
obligations hold and every parameter lemma holds in every model of Γ at the valuations sending its
free element variables to values (`EntailsAtValues`), so that the text with its hypotheses has a
model. Γ states a parameter's graph at values only (`ΓDomains`), so the lemma is owed there. Proved
by hand: `e3ml_witness`. -/
def ParamLemmaWitnessAtValues : Prop :=
  ∃ H : HookParams, FnObligations (cH H) callOrder [] ∧
    ∀ ad ∈ paramLemmaText, EntailsAtValues (cH H) ad (trS ad).pat

/-- Every sentence of the user module that carries `simplification`, is an equation
(`AttrsAgree.eqnHead`) and has at the head of its left side a parameter symbol no registry hook
interprets (`impl = none`) is of the class `parameter lemma`: the sentences `attrsAgree` does not
count as equations of such a parameter are held by the account as hypotheses on `H`. -/
theorem paramlemma_heads : userAxioms.all (fun ad =>
    !(AttrsAgree.has ad.ax.attributes "simplification" &&
      (AttrsAgree.eqnHead ad.ax.pattern).any (fun n =>
        c.params.any fun k => k.impl.isNone && c.symName k.sig.name == n)) ||
    (classOf "parameter lemma").contains ad.index) = true := by
  rw [userAxioms_eq]; decide +kernel

/-! ## The user lemmas (123, 124, 125, 152): owed, by hand -/

/-- The lemmas of a user's file that the reader leaves out of Γ and that apply no parameter symbol
without `impl`, of the class `user lemma`. -/
noncomputable def userLemmaText : List AxiomDecl := [U.ax123, U.ax124, U.ax125, U.ax152]

/-- Those of the class `user lemma at values`. -/
noncomputable def userLemmaValuesText : List AxiomDecl := []

/-- The two lists are the account's classes `user lemma`, of the direction `entailed`, and
`user lemma at values`, of the direction `atValues`. -/
theorem userlemma_account : userLemmaText.map (·.index) = classOf "user lemma" ∧
    userLemmaValuesText.map (·.index) = classOf "user lemma at values" := by
  decide +kernel

/-- **What the tie owes of the user lemmas of the class `user lemma`**: Γ entails each, for
every interpretation `H`. Proved by hand: `userlemma_entailed`. -/
def UserLemmaEntailed : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaText, Γ (cH H) ⊧ (trS ad).pat

/-- **What the tie owes of the user lemmas of the class `user lemma at values`**: each holds in
every model of Γ at the valuations sending its free element variables to values, for every
interpretation `H`. None on this text. -/
def UserLemmaAtValues : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaValuesText, EntailsAtValues (cH H) ad (trS ad).pat

/-! ## The user lemmas and the parameter lemmas, by hand

The four user lemmas are about `f` and `g`, whose equations (206, 208) are Γ's items, so each holds
at every element of Int, value or not (`fg_id_eml`): they are entailed for every H. The four
parameter lemmas are about `h`, a parameter without `impl`, of which Γ states the graph at values
only (`ΓDomains`): at `H1`, the interpretation with `h(n) = n`, each holds at values; at
`HookParams.none` sentence 210 has no model (`e3ml_open`). -/


/-- What the symbol named `n` applied to the element `x` denotes. -/
def appEml {M : Type} (I : Interpretation KoreAML.Sym M) (n : String) (x m : M) : Prop :=
  ∃ a, I.evalSymb (.symbol n) a ∧ I.evalApp a x m

theorem tr_app1_eml {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} (t : VarTable) (n : String)
    (x : Kore.EVar) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (.app ⟨⟨n⟩⟩ [] [.var (.evar x)])).interpret I e m ↔
      appEml I n (e.evalEvar (t.ev (KoreAML.evarKey x))) m := by
  rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app, KoreAML.tr]
  simp only [KoreAML.interp_sym, KoreAML.interp_evar, appEml]
  constructor
  · rintro ⟨a, b, ha, rfl, h⟩; exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, _, ha, rfl, h⟩


/-- The text's variable `X:SortInt{}` of the name `n`. -/
def vInt (n : String) : Kore.Pattern := KoreAML.ev n (KoreAML.srt "Int")

/-- `rule n(X) => X`, as kompile writes it: `X0 ∈ VarX → n(X0) = VarX`. -/
def eqnPatEml (n : String) : Kore.Pattern :=
  .implies KoreAML.R (.and KoreAML.R [.top KoreAML.R, .and KoreAML.R [Kore.Pattern.in (KoreAML.srt "Int") KoreAML.R
      (vInt "X0") (vInt "VarX"), .top KoreAML.R]])
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨n⟩⟩ [] [vInt "X0"])
      (.and (KoreAML.srt "Int") [vInt "VarX", .top (KoreAML.srt "Int")]))

theorem f_eqn_pat : U.ax206.ax.pattern = eqnPatEml "Lblf" := by decide +kernel
theorem g_eqn_pat : U.ax208.ax.pattern = eqnPatEml "Lblg" := by decide +kernel
theorem f_eqn_sv : U.ax206.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem g_eqn_sv : U.ax208.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem f_eqn_trS : (trS U.ax206).pat = (trAxiom [] [] U.ax206).pat := by decide +kernel
theorem g_eqn_trS : (trS U.ax208).pat = (trAxiom [] [] U.ax208).pat := by decide +kernel

/-- The keys of the equation's variables. -/
def eqnKeys : VarTable := [.sortVar "R", .evar "X0" (KoreAML.srt "Int"), .evar "VarX" (KoreAML.srt "Int")]

theorem eqn_table (n : String) : tableOf [KoreAML.Rv] (eqnPatEml n) = eqnKeys := rfl
theorem eqn_free (n : String) : ([KoreAML.Rv].map sortVarKey ++ freeOf [] (eqnPatEml n)).eraseDups = eqnKeys := rfl

/-- **What `rule n(X) => X` says in a model**, at every element `x` of Int: on Int, `n(x)` is `x`. -/
theorem eqn_val_eml {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI)
    (hσI2 : IsSort I σI) {ad : AxiomDecl} {n : String} (hpat : ad.ax.pattern = eqnPatEml n)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) (hax : I ⊧ᴵ (trAxiom [] [] ad).pat) {x : M} (hx : Inh I σI x)
    {a : M} (ha : Inh I σI a) : appEml I n x a ↔ a = x := by
  let val : VarKey → M := fun
    | .sortVar _ => σI
    | _ => x
  let e' : Valuation M := valOf eqnKeys val
  have hR : e'.evalEvar (eqnKeys.ev (.sortVar "R")) = σI := valOf_ev (by decide)
  have hX0 : e'.evalEvar (eqnKeys.ev (.evar "X0" (KoreAML.srt "Int"))) = x := valOf_ev (by decide)
  have hVX : e'.evalEvar (eqnKeys.ev (.evar "VarX" (KoreAML.srt "Int"))) = x := valOf_ev (by decide)
  have hRv : ∀ b, (KoreAML.trSort eqnKeys KoreAML.R).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, hR]
  have hS : ∀ b, (KoreAML.trSort eqnKeys (KoreAML.srt "Int")).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hg : ∀ k ∈ (ad.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ad.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf (tableOf ad.ax.sortVars ad.ax.pattern) k).interpret I e' m := by
    rw [hpat, hsv, eqn_free, eqn_table]
    intro k hk m
    simp only [eqnKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · rw [KoreAML.interp_guard_sortVar hD, hR]; exact hσI2
    · rw [KoreAML.interp_guard_evar hD, hX0, KoreAML.interp_inhOf_of hS]; exact hx
    · rw [KoreAML.interp_guard_evar hD, hVX, KoreAML.interp_inhOf_of hS]; exact hx
  have hP := (KoreAML.trAxiom_at hD hax e' hg x).mpr (by
    rw [hpat, hsv, eqn_table]
    show (KoreAML.inhOf (KoreAML.trSort eqnKeys KoreAML.R)).interpret I e' x
    rw [KoreAML.interp_inhOf_of hRv]; exact hx)
  rw [hpat, hsv, eqn_table] at hP
  unfold eqnPatEml at hP
  rw [KoreAML.tr, KoreAML.interp_sImp] at hP
  have hXv : ∀ b, (KoreAML.tr ⟨eqnKeys, []⟩ (vInt "X0")).interpret I e' b ↔ b = x := fun b => by
    unfold vInt KoreAML.ev; rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (eqnKeys.ev (.evar "X0" (KoreAML.srt "Int"))) ↔ b = x
    rw [hX0]
  have hVv : ∀ b, (KoreAML.tr ⟨eqnKeys, []⟩ (vInt "VarX")).interpret I e' b ↔ b = x := fun b => by
    unfold vInt KoreAML.ev; rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (eqnKeys.ev (.evar "VarX" (KoreAML.srt "Int"))) ↔ b = x
    rw [hVX]
  have hTI : ∀ m, (KoreAML.tr ⟨eqnKeys, []⟩ (.top (KoreAML.srt "Int"))).interpret I e' m ↔ Inh I σI m := fun m => by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
  have hprem : (KoreAML.tr ⟨eqnKeys, []⟩ (.and KoreAML.R [.top KoreAML.R, .and KoreAML.R [Kore.Pattern.in
      (KoreAML.srt "Int") KoreAML.R (vInt "X0") (vInt "VarX"), .top KoreAML.R]])).interpret I e' x := by
    have hT : ∀ m, (KoreAML.tr ⟨eqnKeys, []⟩ (.top KoreAML.R)).interpret I e' m ↔ Inh I σI m := fun m => by
      rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_R]; simp [Pattern.isFreeEvar]; exact fun h => ev_ne_top h.symm),
        KoreAML.interp_inhOf_of hRv]
    simp only [KoreAML.tr, KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    refine ⟨(hT x).mpr hx, ?_, (hT x).mpr hx⟩
    rw [KoreAML.interp_sIn hD hc hS hRv hσI2 hσI2 (fun b hb => by rw [(hXv b).mp hb]; exact hx) x]
    exact ⟨⟨x, (hXv x).mpr rfl, (hVv x).mpr rfl⟩, hx⟩
  have hC := hP.2 hprem
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσI2 hσI2] at hC
  have h1 := hC.2 a ha
  have hL : ∀ b, (KoreAML.tr ⟨eqnKeys, []⟩ (.app ⟨⟨n⟩⟩ [] [vInt "X0"])).interpret I e' b ↔ appEml I n x b := fun b => by
    unfold vInt KoreAML.ev; rw [tr_app1_eml]; exact Iff.of_eq (congrArg (fun y => appEml I n y b) hX0)
  rw [hL] at h1
  have h2 : ∀ b, (KoreAML.tr ⟨eqnKeys, []⟩ (.and (KoreAML.srt "Int") [vInt "VarX", .top (KoreAML.srt "Int")])).interpret
      I e' b ↔ b = x ∧ Inh I σI b := fun b => by
    rw [KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd, hVv, hTI]
  rw [h1, h2]
  exact ⟨And.left, fun h => ⟨h, ha⟩⟩

/-- `f`, `g` and `h`: the symbols `Lblf`, `Lblg` (functions) and `Lblh` (a parameter). -/
theorem f_head (H : HookParams) : symHead (cH H) 384 = KoreAML.sym (.symbol "Lblf") := by
  unfold symHead
  rw [show (cH H).symName 384 = "Lblf" from (by decide +kernel : c.symName 384 = "Lblf")]
  rfl
theorem g_head (H : HookParams) : symHead (cH H) 385 = KoreAML.sym (.symbol "Lblg") := by
  unfold symHead
  rw [show (cH H).symName 385 = "Lblg" from (by decide +kernel : c.symName 385 = "Lblg")]
  rfl
theorem h_head (H : HookParams) : symHead (cH H) 386 = KoreAML.sym (.symbol "Lblh") := by
  unfold symHead
  rw [show (cH H).symName 386 = "Lblh" from (by decide +kernel : c.symName 386 = "Lblh")]
  rfl
theorem f_kernel (H : HookParams) : (⟨384, [Srt.int], Srt.int⟩ : CtorSig) ∈ kernelSyms (cH H) := by
  show _ ∈ kernelSyms c; decide +kernel
theorem g_kernel (H : HookParams) : (⟨385, [Srt.int], Srt.int⟩ : CtorSig) ∈ kernelSyms (cH H) := by
  show _ ∈ kernelSyms c; decide +kernel
theorem h_kernel (H : HookParams) : (⟨386, [Srt.int], Srt.int⟩ : CtorSig) ∈ kernelSyms (cH H) := by
  show _ ∈ kernelSyms c; decide +kernel

/-- **Arity**: a symbol of `Int → Int` applied to an element of Int gives elements of Int only. -/
theorem app_int_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI)
    {f : Sym} {n : String} (hk : (⟨f, [Srt.int], Srt.int⟩ : CtorSig) ∈ kernelSyms (cH H))
    (hhead : symHead (cH H) f = KoreAML.sym (.symbol n)) {x a : M} (hx : Inh I σI x) (h : appEml I n x a) :
    Inh I σI a := by
  have hS : ∀ b, (KoreAML.sym (.sort ("Sort" ++ "Int")) : KoreAML.P).interpret I KoreAML.val0 b ↔ b = σI := hσI1
  have := symArity_at hI hk KoreAML.val0 a (by
    simp only [List.map, int_name, hhead, KoreAML.appList, trSort_srt]
    obtain ⟨fa, hfa, happ⟩ := h
    exact KoreAML.interp_app.mpr ⟨fa, x, hfa, (KoreAML.interp_inhOf_of hS).mpr hx, happ⟩)
  rw [int_name] at this
  exact (KoreAML.interp_inhOf_of hS).mp this

/-- **`f` and `g` are the identity on Int, in every model of Γ, at every element** (not only at
values): `rule f(X) => X` and `rule g(X) => X` are Γ's items. -/
theorem fg_id_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hf : I ⊧ᴵ (trS U.ax206).pat) (hg : I ⊧ᴵ (trS U.ax208).pat)
    {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI) (hσI2 : IsSort I σI)
    {x : M} (hx : Inh I σI x) (a : M) :
    (appEml I "Lblf" x a ↔ a = x) ∧ (appEml I "Lblg" x a ↔ a = x) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  rw [f_eqn_trS] at hf
  rw [g_eqn_trS] at hg
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (eqn_val_eml hD hc hσI1 hσI2 f_eqn_pat f_eqn_sv hf hx (app_int_eml H hI hσI1 (f_kernel H) (f_head H) hx h)).mp h
  · subst h; exact (eqn_val_eml hD hc hσI1 hσI2 f_eqn_pat f_eqn_sv hf hx hx).mpr rfl
  · exact (eqn_val_eml hD hc hσI1 hσI2 g_eqn_pat g_eqn_sv hg hx (app_int_eml H hI hσI1 (g_kernel H) (g_head H) hx h)).mp h
  · subst h; exact (eqn_val_eml hD hc hσI1 hσI2 g_eqn_pat g_eqn_sv hg hx hx).mpr rfl

/-! ### The user lemmas' frame: `⊤_R → (L =_{Q0,R} Rt)` over `R`, `Q0` and `X:Int` -/

/-- The sort variable `Q0`. -/
def Q0s : Kore.KSort := .var ⟨⟨⟨"Q0"⟩⟩⟩

/-- The variable table of the sentences 123, 124, 125, 152. -/
def keysQ : VarTable := [.sortVar "R", .sortVar "Q0", .evar "VarX" (KoreAML.srt "Int")]

/-- **A sentence `⊤_R → (L = Rt)`** (at sorts `Q0`, `R`, its one element variable `X:Int`) is
entailed where `L` and `Rt` denote the same elements of `Q0`, in every model of Γ, at every
valuation sending `R` and `Q0` to sorts and `X` into Int. -/
theorem frameQ_eml (H : HookParams) (ad : AxiomDecl) (L Rt : Kore.Pattern)
    (htrS : (trS ad).pat = (trAxiom [] [] ad).pat)
    (hpat : ad.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals Q0s KoreAML.R L Rt))
    (htab : tableOf ad.ax.sortVars ad.ax.pattern = keysQ)
    (hfree : (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups =
      [.sortVar "R", .sortVar "Q0", .evar "VarX" (KoreAML.srt "Int")])
    (hmain : ∀ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}, I ⊧ᴵP Γ (cH H) →
      ∀ (e : Valuation M) (σI σQ : M), (∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI) → IsSort I σI →
      e.evalEvar (keysQ.ev (.sortVar "Q0")) = σQ → IsSort I σQ →
      Inh I σI (e.evalEvar (keysQ.ev (.evar "VarX" (KoreAML.srt "Int")))) →
      ∀ b, Inh I σQ b → ((KoreAML.tr ⟨keysQ, []⟩ L).interpret I e b ↔ (KoreAML.tr ⟨keysQ, []⟩ Rt).interpret I e b)) :
    Γ (cH H) ⊧ (trS ad).pat := by
  intro M _ I hI e m
  rw [htrS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  unfold trAxiom
  dsimp only
  rw [hfree, htab, hpat]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hQ := (interp_guard_sortVar hD).mp hg.2.1
  have hX := (interp_guard_evar hD).mp hg.2.2
  have hS : ∀ b, (KoreAML.trSort keysQ (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  rw [KoreAML.interp_inhOf_of hS] at hX
  have hRv : ∀ b, (KoreAML.trSort keysQ KoreAML.R).interpret I e b ↔ b = e.evalEvar (keysQ.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hQv : ∀ b, (KoreAML.trSort keysQ Q0s).interpret I e b ↔ b = e.evalEvar (keysQ.ev (.sortVar "Q0")) :=
    fun b => Iff.rfl
  rw [interp_equal hD]
  intro a
  simp only [sortOf]
  rw [KoreAML.tr, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hRv]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hQv hRv hQ hR]
    exact ⟨ha, hmain hI e σI _ hσI1 hσI2 rfl hQ hX⟩

/-- A model of Γ satisfies the equations of `f` and `g` (`fns_entailed`). -/
theorem fg_sat_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    (I ⊧ᴵ (trS U.ax206).pat) ∧ (I ⊧ᴵ (trS U.ax208).pat) :=
  ⟨fns_entailed H U.ax206 List.mem_cons_self hI,
    fns_entailed H U.ax208 (List.mem_cons_of_mem _ List.mem_cons_self) hI⟩

/-- `⌈p⌉{S,Q}` where `p` denotes exactly the element `x` of the sort `S`: the whole sort `Q`. -/
theorem ceil_one_eml {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) {e : Valuation M} {t : VarTable} {S Q : Kore.KSort} {p : Kore.Pattern}
    {σ σQ x : M} (hS : ∀ b, (KoreAML.trSort t S).interpret I e b ↔ b = σ)
    (hQv : ∀ b, (KoreAML.trSort t Q).interpret I e b ↔ b = σQ) (hσ : IsSort I σ) (hσQ : IsSort I σQ)
    (hx : Inh I σ x) (hp : ∀ y, (KoreAML.tr ⟨t, []⟩ p).interpret I e y ↔ y = x) (b : M) :
    (KoreAML.tr ⟨t, []⟩ (.ceil S Q p)).interpret I e b ↔ Inh I σQ b := by
  rw [KoreAML.tr, KoreAML.interp_sCeil hD hc hS hQv hσ hσQ (fun y hy => by rw [(hp y).mp hy]; exact hx)]
  exact ⟨And.right, fun h => ⟨⟨x, (hp x).mpr rfl⟩, h⟩⟩

/-- `⊤` at a sort variable denoting the sort `σQ`: the sort. -/
theorem top_var_eml {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {e : Valuation M}
    {t : VarTable} {α : Kore.SortVar} {σQ : M} (hQv : ∀ b, (KoreAML.trSort t (.var α)).interpret I e b ↔ b = σQ)
    (b : M) : (KoreAML.tr ⟨t, []⟩ (.top (.var α))).interpret I e b ↔ Inh I σQ b := by
  rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [KoreAML.trSort]; simp [Pattern.isFreeEvar]; exact fun h => ev_ne_top h.symm),
    KoreAML.interp_inhOf_of hQv]

/-- In a model of Γ, at a valuation sending `X` into Int: `f(X)` and `g(X)` denote `X`'s element. -/
theorem fgX_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI)
    (hσI2 : IsSort I σI) {e : Valuation M} {t : VarTable} {k : String}
    (hx : Inh I σI (e.evalEvar (t.ev (.evar k (KoreAML.srt "Int"))))) (y : M) :
    ((KoreAML.tr ⟨t, []⟩ (.app ⟨⟨"Lblf"⟩⟩ [] [vInt k])).interpret I e y ↔ y = e.evalEvar (t.ev (.evar k (KoreAML.srt "Int")))) ∧
    ((KoreAML.tr ⟨t, []⟩ (.app ⟨⟨"Lblg"⟩⟩ [] [vInt k])).interpret I e y ↔ y = e.evalEvar (t.ev (.evar k (KoreAML.srt "Int")))) := by
  obtain ⟨hf, hg⟩ := fg_sat_eml H hI
  have h := fg_id_eml H hI hf hg hσI1 hσI2 hx y
  unfold vInt KoreAML.ev
  rw [tr_app1_eml, tr_app1_eml]
  exact h

/-- The patterns of the four user lemmas. -/
def fX : Kore.Pattern := .app ⟨⟨"Lblf"⟩⟩ [] [vInt "VarX"]
def gX : Kore.Pattern := .app ⟨⟨"Lblg"⟩⟩ [] [vInt "VarX"]
def ceilQ (p : Kore.Pattern) : Kore.Pattern := .ceil (KoreAML.srt "Int") Q0s p

theorem s123_pattern : U.ax123.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0s KoreAML.R (ceilQ fX) (.and Q0s [.top Q0s, .top Q0s])) := by decide +kernel
theorem s124_pattern : U.ax124.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0s KoreAML.R (ceilQ gX) (.and Q0s [.implies Q0s (ceilQ fX) (.top Q0s), .top Q0s])) := by decide +kernel
theorem s125_pattern : U.ax125.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0s KoreAML.R (ceilQ gX) (.and Q0s [.not Q0s (.bottom Q0s), .top Q0s])) := by decide +kernel
theorem s152_pattern : U.ax152.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0s KoreAML.R (.equals (KoreAML.srt "Int") Q0s fX gX) (.and Q0s [.top Q0s, .top Q0s])) := by decide +kernel
theorem userLemma_trS : ∀ ad ∈ [U.ax123, U.ax124, U.ax125, U.ax152], (trS ad).pat = (trAxiom [] [] ad).pat ∧
    tableOf ad.ax.sortVars ad.ax.pattern = keysQ ∧
    (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups =
      [.sortVar "R", .sortVar "Q0", .evar "VarX" (KoreAML.srt "Int")] := by decide +kernel

/-- The common facts at a valuation of the frame. -/
theorem frameQ_facts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (σI σQ : M) (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI)
    (hσI2 : IsSort I σI) (hQe : e.evalEvar (keysQ.ev (.sortVar "Q0")) = σQ) (hQ : IsSort I σQ)
    (hx : Inh I σI (e.evalEvar (keysQ.ev (.evar "VarX" (KoreAML.srt "Int"))))) :
    (∀ b, (KoreAML.inhOf (KoreAML.trSort keysQ Q0s)).interpret I e b ↔ Inh I σQ b) ∧
    (∀ b, (KoreAML.sTop (KoreAML.trSort keysQ Q0s)).interpret I e b ↔ Inh I σQ b) ∧
    (∀ b, (KoreAML.tr ⟨keysQ, []⟩ (.top Q0s)).interpret I e b ↔ Inh I σQ b) ∧
    (∀ b, (KoreAML.tr ⟨keysQ, []⟩ (ceilQ fX)).interpret I e b ↔ Inh I σQ b) ∧
    (∀ b, (KoreAML.tr ⟨keysQ, []⟩ (ceilQ gX)).interpret I e b ↔ Inh I σQ b) ∧
    (∀ b, Inh I σQ b → ((KoreAML.tr ⟨keysQ, []⟩ (.equals (KoreAML.srt "Int") Q0s fX gX)).interpret I e b)) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hQv : ∀ b, (KoreAML.trSort keysQ Q0s).interpret I e b ↔ b = σQ := fun b => by
    rw [← hQe]; exact Iff.rfl
  have hS : ∀ b, (KoreAML.trSort keysQ (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hfg := fgX_eml H hI hσI1 hσI2 (t := keysQ) (k := "VarX") hx
  have hT := top_var_eml hD hQv
  refine ⟨fun b => KoreAML.interp_inhOf_of hQv, fun b => by rw [← hT b, KoreAML.tr]; exact Iff.rfl, hT,
    ceil_one_eml hD hc hS hQv hσI2 hQ hx (fun y => (hfg y).1),
    ceil_one_eml hD hc hS hQv hσI2 hQ hx (fun y => (hfg y).2), fun b hb => ?_⟩
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hQv hσI2 hQ]
  exact ⟨hb, fun y _ => by unfold fX gX; rw [(hfg y).1, (hfg y).2]⟩

/-- **Sentence 123** (`#Ceil(f(X)) => #Top`): entailed by Γ, for every H. -/
theorem s123_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax123).pat := by
  obtain ⟨h1, h2, h3⟩ := userLemma_trS U.ax123 (by simp)
  refine frameQ_eml H U.ax123 _ _ h1 s123_pattern h2 h3 fun hI e σI σQ hσI1 hσI2 hQe hQ hx b hb => ?_
  obtain ⟨-, -, hT, hF, -, -⟩ := frameQ_facts H hI e σI σQ hσI1 hσI2 hQe hQ hx
  rw [hF, KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd, hT]
  exact ⟨fun h => ⟨h, h⟩, And.left⟩

/-- **Sentence 125** (`#Ceil(g(X)) => #Not(#Bottom)`): entailed by Γ, for every H. -/
theorem s125_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax125).pat := by
  obtain ⟨h1, h2, h3⟩ := userLemma_trS U.ax125 (by simp)
  refine frameQ_eml H U.ax125 _ _ h1 s125_pattern h2 h3 fun hI e σI σQ hσI1 hσI2 hQe hQ hx b hb => ?_
  obtain ⟨hIQ, hST, hT, -, hG, -⟩ := frameQ_facts H hI e σI σQ hσI1 hσI2 hQe hQ hx
  rw [hG, KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd, hT, KoreAML.tr, KoreAML.interp_sNot,
    KoreAML.tr]
  unfold sBot
  dsimp only
  rw [KoreAML.interp_sNot, hIQ, hST]
  exact ⟨fun h => ⟨⟨fun h' => h'.1 h, h⟩, h⟩, And.right⟩

/-- **Sentence 124** (`#Ceil(g(X)) => #Ceil(f(X)) #Implies #Top`): entailed by Γ, for every H. -/
theorem s124_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax124).pat := by
  obtain ⟨h1, h2, h3⟩ := userLemma_trS U.ax124 (by simp)
  refine frameQ_eml H U.ax124 _ _ h1 s124_pattern h2 h3 fun hI e σI σQ hσI1 hσI2 hQe hQ hx b hb => ?_
  obtain ⟨hIQ, -, hT, hF, hG, -⟩ := frameQ_facts H hI e σI σQ hσI1 hσI2 hQe hQ hx
  rw [hG, KoreAML.tr]; simp only [KoreAML.trAndList]
  rw [KoreAML.interp_sAnd, hT, KoreAML.tr, KoreAML.interp_sImp, hF, hT]
  dsimp only
  rw [hIQ]
  exact ⟨fun h => ⟨⟨h, fun h' => h'⟩, h⟩, fun h => h.2⟩

/-- **Sentence 152** (`{f(X) #Equals g(X)} => #Top`): entailed by Γ, for every H. -/
theorem s152_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax152).pat := by
  obtain ⟨h1, h2, h3⟩ := userLemma_trS U.ax152 (by simp)
  refine frameQ_eml H U.ax152 _ _ h1 s152_pattern h2 h3 fun hI e σI σQ hσI1 hσI2 hQe hQ hx b hb => ?_
  obtain ⟨-, -, hT, -, -, hE⟩ := frameQ_facts H hI e σI σQ hσI1 hσI2 hQe hQ hx
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]
  rw [KoreAML.interp_sAnd, hT]
  exact ⟨fun _ => ⟨hb, hb⟩, fun _ => hE b hb⟩

/-! ### The parameter lemmas: at values, at the interpretation giving `h(n) = n` -/

/-- At a valuation sending the sentence's variable `X:Int` to a value: it is an integer's element. -/
theorem atX_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {e : Valuation M} {ad : AxiomDecl} (hat : AtValues (cH H) I e ad.ax)
    (hmem : VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] ad.ax.pattern).eraseDups) :
    ∃ n : Int, e.evalEvar ((tableOf ad.ax.sortVars ad.ax.pattern).ev (.evar "VarX" (KoreAML.srt "Int"))) =
      elemOf (cH H) I (KCore.int n) := by
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarX" (KoreAML.srt "Int") hmem
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact ⟨n, ((elemOf_spec hI hv e).1 _).mp hden⟩

/-- An integer's element is an element of Int. -/
theorem int_elem_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI) (n : Int) :
    Inh I σI (elemOf (cH H) I (KCore.int n)) := by
  have h := (elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0).2
  rw [int_name] at h
  exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσI1).mp h

/-- The interpretation giving `h(n) = n` at every integer (and nothing elsewhere). -/
def H1 : HookParams := ⟨fun f vs => if f = 386 then vs.head? else none⟩

/-- `h`'s declaration: a parameter of `Int → Int` no hook implements. -/
def kh : ParamSig := ⟨⟨386, [Srt.int], Srt.int⟩, none, false, false, false⟩

theorem params_c : c.params = [kh] := by decide +kernel
theorem lookup_h (H : HookParams) : (cH H).lookupParam 386 = some kh :=
  (by decide +kernel : c.lookupParam 386 = some kh)

theorem paramVal_H1 (n : Int) : (cH H1).paramVal 386 [KCore.int n] = some (KCore.int n) := by
  unfold Semantics.paramVal
  rw [lookup_h]
  simp only [kh, H1, Semantics.withHooks]
  rfl

theorem paramVal_none (n : Int) : (cH HookParams.none).paramVal 386 [KCore.int n] = none := by
  unfold Semantics.paramVal
  rw [lookup_h]
  simp only [kh, HookParams.none, Semantics.withHooks]
  rfl

/-- **`h` at an integer, in a model**: `h(n)`'s element is what `paramVal` gives (`ΓDomains`). -/
theorem h_graph_eml (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (n : Int) (a : M) :
    appEml I "Lblh" (elemOf (cH H) I (KCore.int n)) a ↔ Res (cH H) I KoreAML.val0 ((cH H).paramVal 386 [KCore.int n]) a := by
  have hD := defOK hI
  have hk : kh ∈ (cH H).params := by rw [show (cH H).params = c.params from rfl, params_c]; exact List.mem_singleton_self _
  have hgraph := sat_dom hI (Or.inr (Or.inl ⟨kh, [KCore.int n], hk, rfl, rfl⟩))
  have h2 := (KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a
  obtain ⟨hes, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0
  have hL : (KoreAML.den (symApp (cH H) kh.sig.name (GroundTerm.koreList (cH H) [KCore.int n]))).interpret I KoreAML.val0 a ↔
      appEml I "Lblh" (elemOf (cH H) I (KCore.int n)) a := by
    unfold KoreAML.den
    rw [tr_symApp, show kh.sig.name = 386 from rfl, h_head]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app]
    simp only [KoreAML.interp_sym, appEml]
    constructor
    · rintro ⟨fa, b, hfa, hb, happ⟩
      exact ⟨fa, hfa, by rw [← (hes b).mp hb]; exact happ⟩
    · rintro ⟨fa, hfa, happ⟩
      exact ⟨fa, _, hfa, (hes _).mpr rfl, happ⟩
  rw [← hL, h2, show kh.sig.name = 386 from rfl]
  cases (cH H).paramVal 386 [KCore.int n] with
  | some v => exact Iff.rfl
  | none => simp [Res, Pattern.interpret]

theorem h_H1_eml {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H1)) (n : Int)
    (a : M) : appEml I "Lblh" (elemOf (cH H1) I (KCore.int n)) a ↔ a = elemOf (cH H1) I (KCore.int n) := by
  rw [h_graph_eml H1 hI n a, paramVal_H1]
  exact (elemOf_spec hI (show (cH H1).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0).1 a

theorem h_none_eml {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH HookParams.none)) (n : Int) (a : M) : ¬ appEml I "Lblh" (elemOf (cH HookParams.none) I (KCore.int n)) a := by
  rw [h_graph_eml HookParams.none hI n a, paramVal_none]
  exact id

/-- **A sentence `⊤_R → (L =_{S,R} Rt)` at one valuation**: it holds where its guards give a sort
`σS` for `S` on whose elements `L` and `Rt` agree. -/
theorem frame_at_eml {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (ad : AxiomDecl) (T : VarTable) (ks : List VarKey) (S : Kore.KSort)
    (L Rt : Kore.Pattern)
    (hpat : ad.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals S KoreAML.R L Rt))
    (htab : tableOf ad.ax.sortVars ad.ax.pattern = T)
    (hfree : (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups = .sortVar "R" :: ks)
    (e : Valuation M) (m : M)
    (hmain : (∀ k ∈ ks, (guardOf T k).interpret I e m) → ∃ σS : M,
      (∀ b, (KoreAML.trSort T S).interpret I e b ↔ b = σS) ∧ IsSort I σS ∧
      ∀ b, Inh I σS b → ((KoreAML.tr ⟨T, []⟩ L).interpret I e b ↔ (KoreAML.tr ⟨T, []⟩ Rt).interpret I e b)) :
    (trAxiom [] [] ad).pat.interpret I e m := by
  unfold trAxiom
  dsimp only
  rw [hfree, htab, hpat]
  rw [interpret_impl]
  intro hg
  have hall := conjList_mem hg
  have hR := (interp_guard_sortVar hD).mp (hall _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩))
  obtain ⟨σS, hSv, hσS, hm⟩ := hmain fun k hk => hall _ (List.mem_map.mpr ⟨k, List.mem_cons_of_mem _ hk, rfl⟩)
  have hRv : ∀ b, (KoreAML.trSort T KoreAML.R).interpret I e b ↔ b = e.evalEvar (T.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [interp_equal hD]
  intro a
  simp only [sortOf]
  rw [KoreAML.tr, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hRv]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hSv hRv hσS hR]
    exact ⟨ha, hm⟩

def hX : Kore.Pattern := .app ⟨⟨"Lblh"⟩⟩ [] [vInt "VarX"]

theorem s210_pattern : U.ax210.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals (KoreAML.srt "Int") KoreAML.R hX
    (.and (KoreAML.srt "Int") [.and (KoreAML.srt "Int") [fX, gX], .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s211_pattern : U.ax211.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals (KoreAML.srt "Int") KoreAML.R hX
    (.and (KoreAML.srt "Int") [.or (KoreAML.srt "Int") [fX, gX], .top (KoreAML.srt "Int")])) := by decide +kernel

/-- The variable table of the sentences 210 and 211. -/
def keysV : VarTable := [.sortVar "R", .evar "VarX" (KoreAML.srt "Int")]

theorem hEq_text : ∀ ad ∈ [U.ax210, U.ax211], (trS ad).pat = (trAxiom [] [] ad).pat ∧
    tableOf ad.ax.sortVars ad.ax.pattern = keysV ∧
    (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups = .sortVar "R" :: [.evar "VarX" (KoreAML.srt "Int")] ∧
    VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] ad.ax.pattern).eraseDups := by decide +kernel

/-- At a valuation sending `X` to an integer's element, in a model of Γ at `H1`: `h(X)`, `f(X)`,
`g(X)` each denote that element (on Int), and so do `f(X) ∧ g(X)` and `f(X) ∨ g(X)`. -/
theorem hfgV_eml {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H1))
    {e : Valuation M} (n : Int) (hxe : e.evalEvar (keysV.ev (.evar "VarX" (KoreAML.srt "Int"))) = elemOf (cH H1) I (KCore.int n))
    {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI) (hσI2 : IsSort I σI) (b : M) :
    ((KoreAML.tr ⟨keysV, []⟩ hX).interpret I e b ↔ b = elemOf (cH H1) I (KCore.int n)) ∧
    ((KoreAML.tr ⟨keysV, []⟩ fX).interpret I e b ↔ b = elemOf (cH H1) I (KCore.int n)) ∧
    ((KoreAML.tr ⟨keysV, []⟩ gX).interpret I e b ↔ b = elemOf (cH H1) I (KCore.int n)) := by
  have hx := int_elem_eml H1 hI hσI1 n
  rw [← hxe] at hx
  have hfg := fgX_eml H1 hI hσI1 hσI2 (t := keysV) (k := "VarX") hx b
  rw [hxe] at hfg
  refine ⟨?_, hfg.1, hfg.2⟩
  unfold hX vInt KoreAML.ev
  rw [tr_app1_eml]
  show appEml I "Lblh" (e.evalEvar (keysV.ev (.evar "VarX" (KoreAML.srt "Int")))) b ↔ _
  rw [hxe]
  exact h_H1_eml hI n b

/-- **Sentence 210** (`h(X) => f(X) #And g(X)`) **holds at values at `H1`**. -/
theorem s210_at_values : EntailsAtValues (cH H1) U.ax210 (trS U.ax210).pat := by
  intro M _ I hI e hat m
  obtain ⟨h1, h2, h3, h4⟩ := hEq_text U.ax210 (by simp)
  rw [h1]
  haveI : OvlOK (cH H1) := ovlOK_of_core (coreOKH H1)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H1))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H1)
  rw [int_name] at hσI1
  obtain ⟨n, hn⟩ := atX_eml H1 hI hat h4
  rw [h2] at hn
  refine frame_at_eml hD hc U.ax210 keysV _ _ _ _ s210_pattern h2 h3 e m fun _ => ⟨σI, fun b => by
    rw [trSort_srt]; exact hσI1 b, hσI2, fun b hb => ?_⟩
  obtain ⟨hh, hf, hg⟩ := hfgV_eml hI n hn hσI1 hσI2 b
  have hS : ∀ b, (KoreAML.trSort keysV (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  rw [hh, KoreAML.tr]; simp only [KoreAML.trAndList]
  have hA : (KoreAML.tr ⟨keysV, []⟩ (.and (KoreAML.srt "Int") [fX, gX])).interpret I e b ↔
      (KoreAML.tr ⟨keysV, []⟩ fX).interpret I e b ∧ (KoreAML.tr ⟨keysV, []⟩ gX).interpret I e b := by
    rw [KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd]
  rw [KoreAML.interp_sAnd, hA, hf, hg, KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
  exact ⟨fun h => ⟨⟨h, h⟩, hb⟩, fun h => h.1.1⟩

/-- **Sentence 211** (`h(X) => f(X) #Or g(X)`) **holds at values at `H1`**. -/
theorem s211_at_values : EntailsAtValues (cH H1) U.ax211 (trS U.ax211).pat := by
  intro M _ I hI e hat m
  obtain ⟨h1, h2, h3, h4⟩ := hEq_text U.ax211 (by simp)
  rw [h1]
  haveI : OvlOK (cH H1) := ovlOK_of_core (coreOKH H1)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H1))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H1)
  rw [int_name] at hσI1
  obtain ⟨n, hn⟩ := atX_eml H1 hI hat h4
  rw [h2] at hn
  refine frame_at_eml hD hc U.ax211 keysV _ _ _ _ s211_pattern h2 h3 e m fun _ => ⟨σI, fun b => by
    rw [trSort_srt]; exact hσI1 b, hσI2, fun b hb => ?_⟩
  obtain ⟨hh, hf, hg⟩ := hfgV_eml hI n hn hσI1 hσI2 b
  have hS : ∀ b, (KoreAML.trSort keysV (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  rw [hh, KoreAML.tr]; simp only [KoreAML.trAndList]
  have hO : (KoreAML.tr ⟨keysV, []⟩ (.or (KoreAML.srt "Int") [fX, gX])).interpret I e b ↔
      (KoreAML.inhOf (KoreAML.trSort keysV (KoreAML.srt "Int"))).interpret I e b ∧
        ((KoreAML.tr ⟨keysV, []⟩ fX).interpret I e b ∨ (KoreAML.tr ⟨keysV, []⟩ gX).interpret I e b) := by
    rw [KoreAML.tr]; simp only [KoreAML.trOrList]; rw [KoreAML.interp_sOr]
  rw [KoreAML.interp_sAnd, hO, hf, hg, KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
  exact ⟨fun h => ⟨⟨hb, Or.inl h⟩, hb⟩, fun h => h.1.2.elim id id⟩

/-- **At `HookParams.none` Γ with sentence 210 has no model**: there `h(0)` denotes nothing
(`ΓDomains`, `paramVal` undefined), while 210 at `X = 0` makes it `f(0) ∧ g(0)`, the element of 0.
So the class `parameter lemma` is not `entailed`: the sentence holds only for some `H`. -/
theorem e3ml_open : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH HookParams.none) → ¬ (I ⊧ᴵ (trS U.ax210).pat) := by
  intro M _ I hI hax
  obtain ⟨h1, h2, h3, -⟩ := hEq_text U.ax210 (by simp)
  rw [h1] at hax
  haveI : OvlOK (cH HookParams.none) := ovlOK_of_core (coreOKH HookParams.none)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH HookParams.none))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered HookParams.none)
  rw [int_name] at hσI1
  have hx := int_elem_eml HookParams.none hI hσI1 0
  let x := elemOf (cH HookParams.none) I (KCore.int 0)
  let val : VarKey → M := fun
    | .sortVar _ => σI
    | _ => x
  let e' : Valuation M := valOf keysV val
  have hR : e'.evalEvar (keysV.ev (.sortVar "R")) = σI := valOf_ev (by decide)
  have hXe : e'.evalEvar (keysV.ev (.evar "VarX" (KoreAML.srt "Int"))) = x := valOf_ev (by decide)
  have hRv : ∀ b, (KoreAML.trSort keysV KoreAML.R).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, hR]
  have hS : ∀ b, (KoreAML.trSort keysV (KoreAML.srt "Int")).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hg : ∀ k ∈ (U.ax210.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax210.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf (tableOf U.ax210.ax.sortVars U.ax210.ax.pattern) k).interpret I e' m := by
    rw [h3, h2]
    intro k hk m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · rw [KoreAML.interp_guard_sortVar hD, hR]; exact hσI2
    · rw [KoreAML.interp_guard_evar hD, hXe, KoreAML.interp_inhOf_of hS]; exact hx
  have hP := (KoreAML.trAxiom_at hD hax e' hg x).mpr (by
    rw [h2, s210_pattern]
    show (KoreAML.inhOf (KoreAML.trSort keysV KoreAML.R)).interpret I e' x
    rw [KoreAML.interp_inhOf_of hRv]; exact hx)
  rw [h2, s210_pattern, KoreAML.tr, KoreAML.interp_sImp] at hP
  have hC := hP.2 (by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_R]; simp [Pattern.isFreeEvar]; exact fun h => ev_ne_top h.symm),
      KoreAML.interp_inhOf_of hRv]
    exact hx)
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσI2 hσI2] at hC
  have hfg := fgX_eml HookParams.none hI hσI1 hσI2 (t := keysV) (k := "VarX") (e := e') (by rw [hXe]; exact hx) x
  rw [hXe] at hfg
  have hrhs : (KoreAML.tr ⟨keysV, []⟩ (.and (KoreAML.srt "Int") [.and (KoreAML.srt "Int") [fX, gX],
      .top (KoreAML.srt "Int")])).interpret I e' x := by
    rw [KoreAML.tr]; simp only [KoreAML.trAndList]
    have hA : (KoreAML.tr ⟨keysV, []⟩ (.and (KoreAML.srt "Int") [fX, gX])).interpret I e' x ↔
        (KoreAML.tr ⟨keysV, []⟩ fX).interpret I e' x ∧ (KoreAML.tr ⟨keysV, []⟩ gX).interpret I e' x := by
      rw [KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd]
    refine KoreAML.interp_sAnd.mpr ⟨hA.mpr ⟨hfg.1.mpr rfl, hfg.2.mpr rfl⟩, ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
    exact hx
  have hh := (hC.2 x hx).mpr hrhs
  unfold hX vInt KoreAML.ev at hh
  rw [tr_app1_eml] at hh
  change appEml I "Lblh" (e'.evalEvar (keysV.ev (.evar "VarX" (KoreAML.srt "Int")))) x at hh
  rw [hXe] at hh
  exact h_none_eml hI 0 x hh

/-! ### Sentence 126: `#Ceil(h(X)) => #Exists Y. {f(X) #Equals Y}` -/

/-- `kseq(inj{Int,KItem}(f(X)), dotk)` and the variable `Y:K`. -/
def kseqFX : Kore.Pattern :=
  .app ⟨⟨"kseq"⟩⟩ [] [.app ⟨⟨"inj"⟩⟩ [KoreAML.srt "Int", KoreAML.srt "KItem"] [fX], .app ⟨⟨"dotk"⟩⟩ [] []]
def yK : Kore.EVar := KoreAML.evar "VarY" (KoreAML.srt "K")

theorem s126_pattern : U.ax126.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals Q0s KoreAML.R (ceilQ hX)
    (.and Q0s [.exist Q0s yK (.equals (KoreAML.srt "K") Q0s kseqFX (.var (.evar yK))), .top Q0s])) := by decide +kernel

/-- The variable table of sentence 126. -/
def keys126 : VarTable :=
  [.sortVar "R", .sortVar "Q0", .evar "VarX" (KoreAML.srt "Int"), .evar "VarY" (KoreAML.srt "K")]

theorem s126_text : (trS U.ax126).pat = (trAxiom [] [] U.ax126).pat ∧
    tableOf U.ax126.ax.sortVars U.ax126.ax.pattern = keys126 ∧
    (U.ax126.ax.sortVars.map sortVarKey ++ freeOf [] U.ax126.ax.pattern).eraseDups =
      .sortVar "R" :: [.sortVar "Q0", .evar "VarX" (KoreAML.srt "Int")] ∧
    VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] U.ax126.ax.pattern).eraseDups := by decide +kernel

theorem k_numbered_eml (H : HookParams) : Srt.k < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.k < nRegSorts + c.sortNames.length)
theorem k_name_eml (H : HookParams) : (cH H).sortName Srt.k = "K" := (by decide +kernel : c.sortName Srt.k = "K")

/-- The value `kseq(inj{Int,KItem}(n), dotk)` of the sort K. -/
def vK (n : Int) : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (KCore.int n), .ctor dotk []]

theorem vK_sort (H : HookParams) (n : Int) : (cH H).sortOf (vK n) = some Srt.k :=
  LibEv.KReq.sortOf_kseqV (coreOKH H) rfl

theorem vK_den (H : HookParams) (n : Int) : den (cH H) (vK n) =
    (KoreAML.sym (.symbol "kseq") ⬝ (KoreAML.sym (.symbol "inj") ⬝ KoreAML.sym (.sort ("Sort" ++ "Int")) ⬝
      KoreAML.sym (.sort ("Sort" ++ "KItem")) ⬝ den (cH H) (KCore.int n))) ⬝ KoreAML.sym (.symbol "dotk") := rfl

theorem kseqFX_tr (t : VarTable) : KoreAML.tr ⟨t, []⟩ kseqFX =
    (KoreAML.sym (.symbol "kseq") ⬝ (KoreAML.sym (.symbol "inj") ⬝ KoreAML.sym (.sort ("Sort" ++ "Int")) ⬝
      KoreAML.sym (.sort ("Sort" ++ "KItem")) ⬝ KoreAML.tr ⟨t, []⟩ fX)) ⬝ KoreAML.sym (.symbol "dotk") := rfl

/-- **Sentence 126 holds at values at `H1`**: at `X = n` both sides are the sort `Q0`, `h(n)`
denoting `n` and `kseq(inj(f(n)), dotk)` the one element of the value `kseq(inj(n), dotk)`. -/
theorem s126_at_values : EntailsAtValues (cH H1) U.ax126 (trS U.ax126).pat := by
  intro M _ I hI e hat m
  obtain ⟨h1, h2, h3, h4⟩ := s126_text
  rw [h1]
  haveI : OvlOK (cH H1) := ovlOK_of_core (coreOKH H1)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H1))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H1)
  rw [int_name] at hσI1
  obtain ⟨σK, hσK1, hσK2⟩ := sortSing hI (k_numbered_eml H1)
  rw [k_name_eml] at hσK1
  obtain ⟨n, hn⟩ := atX_eml H1 hI hat h4
  rw [h2] at hn
  have hx := int_elem_eml H1 hI hσI1 n
  refine frame_at_eml hD hc U.ax126 keys126 _ _ _ _ s126_pattern h2 h3 e m fun hgs => ?_
  have hQ : IsSort I (e.evalEvar (keys126.ev (.sortVar "Q0"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (hgs _ List.mem_cons_self)
  have hQv : ∀ b, (KoreAML.trSort keys126 Q0s).interpret I e b ↔ b = e.evalEvar (keys126.ev (.sortVar "Q0")) :=
    fun b => Iff.rfl
  refine ⟨_, hQv, hQ, fun b hb => ?_⟩
  have hS : ∀ b, (KoreAML.trSort keys126 (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  -- the left side: `⌈h(X)⌉`, `h(n)` denoting `n`
  have hh : ∀ y, (KoreAML.tr ⟨keys126, []⟩ hX).interpret I e y ↔ y = elemOf (cH H1) I (KCore.int n) := fun y => by
    unfold hX vInt KoreAML.ev
    rw [tr_app1_eml]
    show appEml I "Lblh" (e.evalEvar (keys126.ev (.evar "VarX" (KoreAML.srt "Int")))) y ↔ _
    rw [hn]
    exact h_H1_eml hI n y
  rw [show ceilQ hX = .ceil (KoreAML.srt "Int") Q0s hX from rfl, ceil_one_eml hD hc hS hQv hσI2 hQ hx hh b]
  -- the right side
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]
  have hT : (KoreAML.tr ⟨keys126, []⟩ (.top Q0s)).interpret I e b ↔ Inh I (e.evalEvar (keys126.ev (.sortVar "Q0"))) b :=
    top_var_eml hD hQv b
  rw [KoreAML.interp_sAnd, hT]
  refine ⟨fun _ => ⟨?_, hb⟩, fun h => h.2⟩
  -- `∃ Y:K. kseq(inj(f(X)), dotk) = Y`, with `Y` the value's element
  have hYne : keys126.ev (KoreAML.evarKey yK) ≠ keys126.ev (.sortVar "Q0") := by decide
  have hYneX : keys126.ev (KoreAML.evarKey yK) ≠ keys126.ev (.evar "VarX" (KoreAML.srt "Int")) := by decide
  obtain ⟨hesK, hvKin⟩ := elemOf_spec hI (vK_sort H1 n) KoreAML.val0
  obtain ⟨hesI, -⟩ := elemOf_spec hI (show (cH H1).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0
  rw [k_name_eml] at hvKin
  let w := elemOf (cH H1) I (vK n)
  let e1 : Valuation M := ⟨Function.update e.evalEvar (keys126.ev (KoreAML.evarKey yK)) w, e.evalSvar⟩
  have hX1 : e1.evalEvar (keys126.ev (.evar "VarX" (KoreAML.srt "Int"))) = elemOf (cH H1) I (KCore.int n) :=
    (Function.update_noteq hYneX.symm w e.evalEvar).trans hn
  have hQe1 : e1.evalEvar (keys126.ev (.sortVar "Q0")) = e.evalEvar (keys126.ev (.sortVar "Q0")) :=
    Function.update_noteq hYne.symm w e.evalEvar
  have hw : e1.evalEvar (keys126.ev (KoreAML.evarKey yK)) = w := Function.update_same (keys126.ev (KoreAML.evarKey yK)) w e.evalEvar
  have hQ1 : ∀ b, (KoreAML.trSort keys126 Q0s).interpret I e1 b ↔ b = e.evalEvar (keys126.ev (.sortVar "Q0")) :=
    fun b => by
      rw [← hQe1]; exact Iff.rfl
  have hSK : ∀ b, (KoreAML.trSort keys126 (KoreAML.srt "K")).interpret I e1 b ↔ b = σK := fun b => by
    rw [trSort_srt]; exact hσK1 b
  rw [KoreAML.tr, KoreAML.interp_sExists]
  refine ⟨w, ?_, ?_⟩
  · rw [KoreAML.interp_member hD]
    change (KoreAML.inhOf (KoreAML.trSort keys126 (KoreAML.srt "K"))).interpret I e1 (e1.evalEvar (keys126.ev (KoreAML.evarKey yK)))
    rw [hw, trSort_srt]
    exact (((Closed.sym _).app (Closed.sym _)).interp _ _ _).mp hvKin
  · change (KoreAML.tr ⟨keys126, []⟩ (.equals (KoreAML.srt "K") Q0s kseqFX (.var (.evar yK)))).interpret I e1 b
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hSK hQ1 hσK2 hQ]
    refine ⟨hb, fun y _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_evar]
    change _ ↔ y = e1.evalEvar (keys126.ev (KoreAML.evarKey yK))
    rw [hw, kseqFX_tr, ← hesK y, vK_den]
    refine KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun m => (Closed.sym _).interp _ _ m)
      (KoreAML.interp_app_congr (fun m => (((Closed.sym _).app (Closed.sym _)).app (Closed.sym _)).interp _ _ m)
        (fun z => ?_))) (fun m => (Closed.sym _).interp _ _ m) y
    unfold fX
    rw [(fgX_eml H1 hI hσI1 hσI2 (t := keys126) (k := "VarX") (e := e1) (by rw [hX1]; exact hx) z).1, hX1, hesI z]

/-! ### Sentence 127: `#Ceil(h(X)) => #Floor(#Forall Y. {f(Y) #Equals g(Y)})` -/

def Q14s : Kore.KSort := .var ⟨⟨⟨"Q14"⟩⟩⟩
def yI : Kore.EVar := KoreAML.evar "VarY" (KoreAML.srt "Int")
def fY : Kore.Pattern := .app ⟨⟨"Lblf"⟩⟩ [] [vInt "VarY"]
def gY : Kore.Pattern := .app ⟨⟨"Lblg"⟩⟩ [] [vInt "VarY"]

theorem s127_pattern : U.ax127.ax.pattern = .implies KoreAML.R (.top KoreAML.R) (.equals Q0s KoreAML.R (ceilQ hX)
    (.and Q0s [.floor Q14s Q0s (.forall Q14s yI (.equals (KoreAML.srt "Int") Q14s fY gY)), .top Q0s])) := by
  decide +kernel

/-- The variable table of sentence 127. -/
def keys127 : VarTable :=
  [.sortVar "R", .sortVar "Q14", .sortVar "Q0", .evar "VarX" (KoreAML.srt "Int"), .evar "VarY" (KoreAML.srt "Int")]

theorem s127_text : (trS U.ax127).pat = (trAxiom [] [] U.ax127).pat ∧
    tableOf U.ax127.ax.sortVars U.ax127.ax.pattern = keys127 ∧
    (U.ax127.ax.sortVars.map sortVarKey ++ freeOf [] U.ax127.ax.pattern).eraseDups =
      .sortVar "R" :: [.sortVar "Q14", .sortVar "Q0", .evar "VarX" (KoreAML.srt "Int")] ∧
    VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] U.ax127.ax.pattern).eraseDups := by decide +kernel

/-- **Sentence 127 holds at values at `H1`**: at `X = n` the left side is the sort `Q0` (`h(n)`
denotes `n`) and so is the right side, since `f(Y) = g(Y)` at every element `Y` of Int. -/
theorem s127_at_values : EntailsAtValues (cH H1) U.ax127 (trS U.ax127).pat := by
  intro M _ I hI e hat m
  obtain ⟨h1, h2, h3, h4⟩ := s127_text
  rw [h1]
  haveI : OvlOK (cH H1) := ovlOK_of_core (coreOKH H1)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H1))
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H1)
  rw [int_name] at hσI1
  obtain ⟨n, hn⟩ := atX_eml H1 hI hat h4
  rw [h2] at hn
  have hx := int_elem_eml H1 hI hσI1 n
  refine frame_at_eml hD hc U.ax127 keys127 _ _ _ _ s127_pattern h2 h3 e m fun hgs => ?_
  have h14 : IsSort I (e.evalEvar (keys127.ev (.sortVar "Q14"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (hgs _ List.mem_cons_self)
  have hQ : IsSort I (e.evalEvar (keys127.ev (.sortVar "Q0"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (hgs _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hQv : ∀ b, (KoreAML.trSort keys127 Q0s).interpret I e b ↔ b = e.evalEvar (keys127.ev (.sortVar "Q0")) :=
    fun b => Iff.rfl
  have h14v : ∀ b, (KoreAML.trSort keys127 Q14s).interpret I e b ↔ b = e.evalEvar (keys127.ev (.sortVar "Q14")) :=
    fun b => Iff.rfl
  refine ⟨_, hQv, hQ, fun b hb => ?_⟩
  have hS : ∀ (e' : Valuation M) b, (KoreAML.trSort keys127 (KoreAML.srt "Int")).interpret I e' b ↔ b = σI :=
    fun _ b => by rw [trSort_srt]; exact hσI1 b
  have hh : ∀ y, (KoreAML.tr ⟨keys127, []⟩ hX).interpret I e y ↔ y = elemOf (cH H1) I (KCore.int n) := fun y => by
    unfold hX vInt KoreAML.ev
    rw [tr_app1_eml]
    show appEml I "Lblh" (e.evalEvar (keys127.ev (.evar "VarX" (KoreAML.srt "Int")))) y ↔ _
    rw [hn]
    exact h_H1_eml hI n y
  rw [show ceilQ hX = .ceil (KoreAML.srt "Int") Q0s hX from rfl, ceil_one_eml hD hc (hS e) hQv hσI2 hQ hx hh b]
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]
  have hT : (KoreAML.tr ⟨keys127, []⟩ (.top Q0s)).interpret I e b ↔ Inh I (e.evalEvar (keys127.ev (.sortVar "Q0"))) b :=
    top_var_eml hD hQv b
  rw [KoreAML.interp_sAnd, hT]
  refine ⟨fun _ => ⟨?_, hb⟩, fun h => h.2⟩
  -- `∀ Y. f(Y) = g(Y)` is the sort `Q14`
  have hYne : keys127.ev (KoreAML.evarKey yI) ≠ keys127.ev (.sortVar "Q14") := by decide
  have hall : ∀ m', (KoreAML.tr ⟨keys127, []⟩ (.forall Q14s yI (.equals (KoreAML.srt "Int") Q14s fY gY))).interpret I e m' ↔
      Inh I (e.evalEvar (keys127.ev (.sortVar "Q14"))) m' := by
    intro m'
    rw [KoreAML.tr]
    unfold sForall
    rw [KoreAML.interp_sNot, KoreAML.interp_sExists, KoreAML.interp_inhOf_of h14v]
    refine ⟨And.right, fun hm => ⟨?_, hm⟩⟩
    rintro ⟨a, ha, hne⟩
    let e1 : Valuation M := ⟨Function.update e.evalEvar (keys127.ev (KoreAML.evarKey yI)) a, e.evalSvar⟩
    have hYa : e1.evalEvar (keys127.ev (.evar "VarY" (KoreAML.srt "Int"))) = a :=
      Function.update_same (keys127.ev (KoreAML.evarKey yI)) a e.evalEvar
    have h14e1 : e1.evalEvar (keys127.ev (.sortVar "Q14")) = e.evalEvar (keys127.ev (.sortVar "Q14")) :=
      Function.update_noteq hYne.symm a e.evalEvar
    have h14v1 : ∀ b, (KoreAML.trSort keys127 Q14s).interpret I e1 b ↔ b = e.evalEvar (keys127.ev (.sortVar "Q14")) :=
      fun b => by rw [← h14e1]; exact Iff.rfl
    rw [KoreAML.interp_member hD] at ha
    change (KoreAML.inhOf (KoreAML.trSort keys127 (KoreAML.srt "Int"))).interpret I e1
      (e1.evalEvar (keys127.ev (.evar "VarY" (KoreAML.srt "Int")))) at ha
    rw [hYa, KoreAML.interp_inhOf_of (hS e1)] at ha
    change (KoreAML.sNot (KoreAML.trSort keys127 Q14s)
      (KoreAML.tr ⟨keys127, []⟩ (.equals (KoreAML.srt "Int") Q14s fY gY))).interpret I e1 m' at hne
    rw [KoreAML.interp_sNot, KoreAML.interp_inhOf_of h14v1, KoreAML.tr,
      KoreAML.interp_sEquals hD hc (hS e1) h14v1 hσI2 h14] at hne
    refine hne.1 ⟨hne.2, fun z _ => ?_⟩
    have hfg := fgX_eml H1 hI hσI1 hσI2 (t := keys127) (k := "VarY") (e := e1) (by rw [hYa]; exact ha) z
    unfold fY gY
    rw [hfg.1, hfg.2]
  rw [KoreAML.tr]
  unfold sFloor
  rw [KoreAML.interp_sNot, KoreAML.interp_inhOf_of hQv]
  refine ⟨?_, hb⟩
  rw [KoreAML.interp_sCeil hD hc h14v hQv h14 hQ (fun a ha => (KoreAML.interp_inhOf_of h14v).mp (KoreAML.interp_sNot.mp ha).2)]
  rintro ⟨⟨a, ha⟩, -⟩
  rw [KoreAML.interp_sNot, hall] at ha
  exact ha.1 ((KoreAML.interp_inhOf_of h14v).mp ha.2)

/-- **The user lemmas are entailed, for every H** (`UserLemmaEntailed`). -/
theorem userlemma_entailed : UserLemmaEntailed := by
  intro H ad had
  simp only [userLemmaText, List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl
  · exact s123_entailed H
  · exact s124_entailed H
  · exact s125_entailed H
  · exact s152_entailed H

/-- **The witness**: at `H1` (`h(n) = n`) the obligations hold (`obl_nil`) and the four parameter
lemmas hold at values. -/
theorem e3ml_witness : ParamLemmaWitnessAtValues := by
  refine ⟨H1, obl_nil H1, fun ad had => ?_⟩
  simp only [paramLemmaText, List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl
  · exact s126_at_values
  · exact s127_at_values
  · exact s210_at_values
  · exact s211_at_values

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

end KCore.TieE3Ml

#check @KCore.TieE3Ml.noRaw
#check @KCore.TieE3Ml.readsConfined_c
#check @KCore.TieE3Ml.userAxioms_eq
#check @KCore.TieE3Ml.coreOK
#check @KCore.TieE3Ml.wf_defn
#check @KCore.TieE3Ml.account
#check @KCore.TieE3Ml.account_sizes
#check @KCore.TieE3Ml.account_classes
#check @KCore.TieE3Ml.account_absent
#check @KCore.TieE3Ml.absent_closed
#check @KCore.TieE3Ml.lists_in_account
#check @KCore.TieE3Ml.attrs_agree
#check @KCore.TieE3Ml.sig_origin_but_next
#check @KCore.TieE3Ml.decls_entailed
#check @KCore.TieE3Ml.consistent
#check @KCore.TieE3Ml.text_nextless
#check @KCore.TieE3Ml.fn_shape
#check @KCore.TieE3Ml.fns_account
#check @KCore.TieE3Ml.fns_entailed
#check @KCore.TieE3Ml.fns_from_text
#check @KCore.TieE3Ml.fn_prios
#check @KCore.TieE3Ml.nojunk_trivial_entailed
#check @KCore.TieE3Ml.nojunk_items_entailed
#check @KCore.TieE3Ml.nojunk_kitem_entailed
#check @KCore.TieE3Ml.cons_entailed
#check @KCore.TieE3Ml.idem_refuted
#check @KCore.TieE3Ml.lib166
#check @KCore.TieE3Ml.lib166_at_values
#check @KCore.TieE3Ml.gamma_origin
#check @KCore.TieE3Ml.gamma_from
#check @KCore.TieE3Ml.paramlemma_account
#check @KCore.TieE3Ml.paramlemma_heads
#check @KCore.TieE3Ml.ParamLemmaWitnessAtValues
#check @KCore.TieE3Ml.userlemma_account
#check @KCore.TieE3Ml.UserLemmaEntailed
#check @KCore.TieE3Ml.UserLemmaAtValues
#print axioms KCore.TieE3Ml.noRaw
#print axioms KCore.TieE3Ml.readsConfined_c
#print axioms KCore.TieE3Ml.userAxioms_eq
#print axioms KCore.TieE3Ml.coreOK
#print axioms KCore.TieE3Ml.wf_defn
#print axioms KCore.TieE3Ml.account
#print axioms KCore.TieE3Ml.account_sizes
#print axioms KCore.TieE3Ml.account_classes
#print axioms KCore.TieE3Ml.account_absent
#print axioms KCore.TieE3Ml.absent_closed
#print axioms KCore.TieE3Ml.lists_in_account
#print axioms KCore.TieE3Ml.attrs_agree
#print axioms KCore.TieE3Ml.sig_origin_but_next
#print axioms KCore.TieE3Ml.decls_entailed
#print axioms KCore.TieE3Ml.consistent
#print axioms KCore.TieE3Ml.text_nextless
#print axioms KCore.TieE3Ml.fn_shape
#print axioms KCore.TieE3Ml.fns_account
#print axioms KCore.TieE3Ml.fns_entailed
#print axioms KCore.TieE3Ml.fns_from_text
#print axioms KCore.TieE3Ml.fn_prios
#print axioms KCore.TieE3Ml.nojunk_trivial_entailed
#print axioms KCore.TieE3Ml.nojunk_items_entailed
#print axioms KCore.TieE3Ml.nojunk_kitem_entailed
#print axioms KCore.TieE3Ml.cons_entailed
#print axioms KCore.TieE3Ml.idem_refuted
#print axioms KCore.TieE3Ml.lib166
#print axioms KCore.TieE3Ml.lib166_at_values
#print axioms KCore.TieE3Ml.gamma_origin
#print axioms KCore.TieE3Ml.gamma_from
#print axioms KCore.TieE3Ml.paramlemma_account
#print axioms KCore.TieE3Ml.paramlemma_heads
#print axioms KCore.TieE3Ml.ParamLemmaWitnessAtValues
#print axioms KCore.TieE3Ml.userlemma_account
#print axioms KCore.TieE3Ml.UserLemmaEntailed
#print axioms KCore.TieE3Ml.UserLemmaAtValues
#check @KCore.TieE3Ml.fg_id_eml
#check @KCore.TieE3Ml.s123_entailed
#check @KCore.TieE3Ml.s124_entailed
#check @KCore.TieE3Ml.s125_entailed
#check @KCore.TieE3Ml.s152_entailed
#check @KCore.TieE3Ml.userlemma_entailed
#check @KCore.TieE3Ml.s126_at_values
#check @KCore.TieE3Ml.s127_at_values
#check @KCore.TieE3Ml.s210_at_values
#check @KCore.TieE3Ml.s211_at_values
#check @KCore.TieE3Ml.e3ml_witness
#check @KCore.TieE3Ml.e3ml_open
#print axioms KCore.TieE3Ml.fg_id_eml
#print axioms KCore.TieE3Ml.s123_entailed
#print axioms KCore.TieE3Ml.s124_entailed
#print axioms KCore.TieE3Ml.s125_entailed
#print axioms KCore.TieE3Ml.s152_entailed
#print axioms KCore.TieE3Ml.userlemma_entailed
#print axioms KCore.TieE3Ml.s126_at_values
#print axioms KCore.TieE3Ml.s127_at_values
#print axioms KCore.TieE3Ml.s210_at_values
#print axioms KCore.TieE3Ml.s211_at_values
#print axioms KCore.TieE3Ml.e3ml_witness
#print axioms KCore.TieE3Ml.e3ml_open
