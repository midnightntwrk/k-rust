/-
  The tie (C14) on `f2-examples/e7-guardors.kompile.kore`, the kompiled text of construct fixture e7-guardors
  (`test/constructs/fixtures/e7-guardors`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e7-guardors`; run from the package root: `lake env lean -j1 test/TieE7Guardors.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 146 sentences of the user module E7-GUARDORS, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 208 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (32): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (47): Γ with it has no model (`idem_refuted`).
  - Rewrite rule (99, `c(a() #Or b())` on the left side): Γ holds two rule items, one per disjunct,
    each a consequence of the sentence with the domains (`rule_from_text`, W1, every H; written by
    hand: each item is the sentence with one disjunct in the place of the disjunction and `⌈r⌉`
    more, `rule_text0`, `rule_text1`, `left0`, `left1`).
  - The converse over Γ's content: each premise is a function sentence's translation, a rule item
    (a consequence of sentence 99 with the domains), one of the five parts Γ defines by predicates,
    or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (17);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE7Guardors

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e7-guardors.kompile.kore"
definition_of defn from "f2-examples/e7-guardors.kompile.kore"
user_axioms U from "f2-examples/e7-guardors.kompile.kore" module "E7-GUARDORS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E7-GUARDORS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 146 := by decide +kernel

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
  [("function equation", [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
      123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]),
   ("rewrite rule", [99]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 55, 58, 60, 80, 81]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 61]),
   ("distinctness", [56, 57, 59]),
   ("no junk", [88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]),
   ("function functional", [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 38, 42, 50, 51, 52, 53, 54, 63, 79, 82, 83, 84, 85, 86]),
   ("collection law", [39, 40, 41, 43, 44, 45, 46, 48, 49]),
   ("library", [100, 148]),
   ("set idempotence", [47]),
   ("set-variable lemma", [149]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 37, 62, 87, 101, 102, 103, 104, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
      145, 146, 147])]

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
    [("function equation", 29), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 9), ("subsort", 15), ("injectivity", 5), ("distinctness", 3), ("no junk", 11), ("function functional", 15), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 22)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has** (the injection `inj`
aside, which Γ's constructor items apply), and each sentence of that class applies one Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index !=
      (symbolsOf ad.ax.pattern).all (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has. -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (symbolsOf ad.ax.pattern).all
        (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(14, "subsort"), (55, "constructor functional"), (56, "distinctness"), (57, "distinctness"),
   (58, "constructor functional"), (59, "distinctness"), (60, "constructor functional"),
   (61, "injectivity"), (65, "function functional"), (89, "no junk"), (98, "no junk"),
   (99, "rewrite rule"), (104, "no direction"), (107, "function equation"),
   (108, "function equation"), (135, "no direction"), (149, "set-variable lemma")]

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

theorem sig_sizes : (sigItems c).length = 208 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 88, 58, 4, 26) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 25).all inSigItems = true := by decide +kernel
theorem declsE_25 : (((declItems).drop 25).take 25).all inSigItems = true := by decide +kernel
theorem declsE_50 : ((declItems).drop 50).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    declsE_50

/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of
a symbol Γ has, for every H. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-! ## Consistency for every H -/

def callOrder : List Nat := []

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
  [U.ax119, U.ax127, U.ax126, U.ax125, U.ax124, U.ax131, U.ax130, U.ax133, U.ax132, U.ax129,
   U.ax128, U.ax106, U.ax105, U.ax118, U.ax117, U.ax114, U.ax113, U.ax116, U.ax115, U.ax121,
   U.ax120, U.ax123, U.ax122, U.ax110, U.ax109, U.ax112, U.ax111, U.ax108, U.ax107]

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

theorem nj88 : (trS U.ax88).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj94 : (trS U.ax94).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj97 : (trS U.ax97).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax88, U.ax94, U.ax97], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj88]; exact orTopBot_valid hD rfl
  · rw [nj94]; exact orTopBot_valid hD rfl
  · rw [nj97]; exact orTopBot_valid hD rfl

/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax89, U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax89, U.ax90, U.ax91, U.ax92, U.ax93, U.ax95, U.ax96],
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
   U.ax16, U.ax17, U.ax18, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27, U.ax28, U.ax29, U.ax55,
   U.ax56, U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax80, U.ax81]

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

theorem idem_pattern : U.ax47.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax47).pat = (trAxiom [] [] U.ax47).pat := by decide +kernel

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
theorem idem_vars : (U.ax47.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax47.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax47.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 47 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax47).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax47.ax.sortVars U.ax47.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax47.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax47.ax.pattern).eraseDups,
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

/-! ## The rewrite rule (sentence 99): W1

The text's one rule, `c(a() #Or b())` on the left side, is two of Γ's rule items, one per disjunct.
Each is the sentence with `a()` (`b()`) in the place of `\or{SortExp{}}(a(), b())` and the conjunct
`⌈r⌉` more on its left side: the sentence is the item of `\rewrites{C}(Ltext, r)` at the table of
Γ's axiom (`rule_text0`, `rule_text1`, kernel), and every element of Γ's left side is one of
`Ltext` (`left0`, `left1`: an application context is monotone, and a disjunct is in the
disjunction where its elements are in Exp, which `ΓDomains` states of the values `a()` and `b()`).
So the sentence with the domains entails each item (`rule_from_text`, every H). -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of rule 0. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut0 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

/-- Γ's axiom of rule 1. -/
noncomputable def p1 : Kore.Pattern := prioRuleK c r1

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q1 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p1).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

-- The sort and the right side are rule 0's.
kernel_rfl q1_eq : TieRuleLhs.rwParts p1 = some (q0.1, q1.2.1, q0.2.2)

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut1 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q1.2.1)).getD (.hole, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by kernel_rfl

/-- The two left sides have one context around the argument of `c`. -/
noncomputable def K : KoreCutCtx := cut0.1

kernel_rfl l0_eq : q0.2.1 = .and q0.1 (K.fill cut0.2 :: .top q0.1 :: (TieRuleLhs.andTail q0.2.1).drop 1)
kernel_rfl l1_eq : q1.2.1 = .and q0.1 (K.fill cut1.2 :: .top q0.1 :: (TieRuleLhs.andTail q1.2.1).drop 1)

/-- The left side as the text writes it: the argument of `c` is `\or{SortExp{}}(a(), b())`, and
no conjunct follows `\top`. -/
noncomputable def Ltext : Kore.Pattern :=
  .and q0.1 [K.fill (.or (KoreAML.srt "Exp") [cut0.2, cut1.2]), .top q0.1]

/-- The free variables of the text's form. -/
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups

/-- **The text's sentence 99 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**,
for each of Γ's two axioms (kernel): Γ's axiom is the sentence with one disjunct in the place of
the disjunction and the conjunct `⌈r⌉` more. -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax99).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias0 : K.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem rule_text1 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p1) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax99).pat := by
  decide +kernel
theorem fT_free1 : fT.all (fun k => (freeOf [] p1).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias1 : K.noAlias ⟨tableOf [] p1, []⟩ = true := by decide +kernel

def aV : GroundTerm := .ctor 385 []
def bV : GroundTerm := .ctor 386 []

theorem names : c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

kernel_rfl a_kore : cut0.2 = aV.kore c
kernel_rfl b_kore : cut1.2 = bV.kore c
theorem a_koreH (H : HookParams) : cut0.2 = aV.kore (cH H) := a_kore
theorem b_koreH (H : HookParams) : cut1.2 = bV.kore (cH H) := b_kore
theorem a_sort (H : HookParams) : (cH H).sortOf aV = some 32 := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem b_sort (H : HookParams) : (cH H).sortOf bV = some 32 := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- A value of Exp denotes an element of Exp, in a model of the domains. -/
theorem exp_inh (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) {v : GroundTerm} (hv : (cH H).sortOf v = some 32) {t : VarTable} {e : Valuation M}
    (a : M) (h : (tr ⟨t, []⟩ (v.kore (cH H))).interpret I e a) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e a := by
  have h1 := TieRuleLhs.ground_inh hD hDom hv (t := t) (e := e) a h
  rw [show (cH H).sortName 32 = "Exp" from names.2.2.2] at h1
  rw [trSort_srt]; exact h1

/-- Every element of Γ's left side of rule 0 is an element of the text's left side. -/
theorem left0 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e a := by
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias0 (TieRuleLhs.sub_or_left fun a' h' => exp_inh H hD hDom (a_sort H) a' (a_koreH H ▸ h')) a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- Every element of Γ's left side of rule 1 is an element of the text's left side. -/
theorem left1 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] p1, []⟩ q1.2.1).interpret I e a) : (tr ⟨tableOf [] p1, []⟩ Ltext).interpret I e a := by
  rw [l1_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias1 (TieRuleLhs.sub_or_right fun a' h' => exp_inh H hD hDom (b_sort H) a' (b_koreH H ▸ h')) a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's two rule items is a
consequence of the text's sentence 99 with the domains (a value of Exp is an element of Exp:
`\or{SortExp{}}` holds the elements of its disjuncts that are in Exp), for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax99).pat] ∪ ΓDomains (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ (trS U.ax99).pat := hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rcases List.mem_cons.mp hit with rfl | hit
  · exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0 hT fun e _ _ a ha => left0 H hD hDom e a ha
  · rw [List.mem_singleton.mp hit]
    exact TieRuleLhs.rule_w1 hD q1_eq rule_text1 fT_free1 hT fun e _ _ a ha => left1 H hD hDom e a ha

/-! ## The converse over Γ's content -/

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, Γ's rule items (each a consequence of
sentence 99 with the domains, `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; a rule item is a consequence of sentence 99 with the domains; everything else is one of
the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨
      (ΓRules (cH H) φ ∧ ((TiePair.Texts [(trS U.ax99).pat] ∪ ΓDomains (cH H)) ⊧ φ)) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))


end KCore.TieE7Guardors

#check @KCore.TieE7Guardors.noRaw
#check @KCore.TieE7Guardors.readsConfined_c
#check @KCore.TieE7Guardors.userAxioms_eq
#check @KCore.TieE7Guardors.coreOK
#check @KCore.TieE7Guardors.wf_defn
#check @KCore.TieE7Guardors.account
#check @KCore.TieE7Guardors.account_sizes
#check @KCore.TieE7Guardors.account_classes
#check @KCore.TieE7Guardors.account_absent
#check @KCore.TieE7Guardors.absent_closed
#check @KCore.TieE7Guardors.lists_in_account
#check @KCore.TieE7Guardors.attrs_agree
#check @KCore.TieE7Guardors.sig_origin
#check @KCore.TieE7Guardors.decls_entailed
#check @KCore.TieE7Guardors.consistent
#check @KCore.TieE7Guardors.fn_shape
#check @KCore.TieE7Guardors.fns_account
#check @KCore.TieE7Guardors.fns_entailed
#check @KCore.TieE7Guardors.fns_from_text
#check @KCore.TieE7Guardors.fn_prios
#check @KCore.TieE7Guardors.nojunk_trivial_entailed
#check @KCore.TieE7Guardors.nojunk_items_entailed
#check @KCore.TieE7Guardors.nojunk_kitem_entailed
#check @KCore.TieE7Guardors.cons_entailed
#check @KCore.TieE7Guardors.idem_refuted
#print axioms KCore.TieE7Guardors.noRaw
#print axioms KCore.TieE7Guardors.readsConfined_c
#print axioms KCore.TieE7Guardors.userAxioms_eq
#print axioms KCore.TieE7Guardors.coreOK
#print axioms KCore.TieE7Guardors.wf_defn
#print axioms KCore.TieE7Guardors.account
#print axioms KCore.TieE7Guardors.account_sizes
#print axioms KCore.TieE7Guardors.account_classes
#print axioms KCore.TieE7Guardors.account_absent
#print axioms KCore.TieE7Guardors.absent_closed
#print axioms KCore.TieE7Guardors.lists_in_account
#print axioms KCore.TieE7Guardors.attrs_agree
#print axioms KCore.TieE7Guardors.sig_origin
#print axioms KCore.TieE7Guardors.decls_entailed
#print axioms KCore.TieE7Guardors.consistent
#print axioms KCore.TieE7Guardors.fn_shape
#print axioms KCore.TieE7Guardors.fns_account
#print axioms KCore.TieE7Guardors.fns_entailed
#print axioms KCore.TieE7Guardors.fns_from_text
#print axioms KCore.TieE7Guardors.fn_prios
#print axioms KCore.TieE7Guardors.nojunk_trivial_entailed
#print axioms KCore.TieE7Guardors.nojunk_items_entailed
#print axioms KCore.TieE7Guardors.nojunk_kitem_entailed
#print axioms KCore.TieE7Guardors.cons_entailed
#print axioms KCore.TieE7Guardors.idem_refuted
#check @KCore.TieE7Guardors.ruleItems_eq
#check @KCore.TieE7Guardors.rule_text0
#check @KCore.TieE7Guardors.rule_text1
#check @KCore.TieE7Guardors.left0
#check @KCore.TieE7Guardors.left1
#check @KCore.TieE7Guardors.rule_from_text
#check @KCore.TieE7Guardors.gamma_origin
#check @KCore.TieE7Guardors.gamma_from
#print axioms KCore.TieE7Guardors.ruleItems_eq
#print axioms KCore.TieE7Guardors.rule_text0
#print axioms KCore.TieE7Guardors.rule_text1
#print axioms KCore.TieE7Guardors.left0
#print axioms KCore.TieE7Guardors.left1
#print axioms KCore.TieE7Guardors.rule_from_text
#print axioms KCore.TieE7Guardors.gamma_origin
#print axioms KCore.TieE7Guardors.gamma_from
