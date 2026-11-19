/-
  The tie (C14) on `f2-examples/mllhsandv.kompile.kore`, the kompiled text of construct fixture e3-ml-rule-lhs-and
  (`test/constructs/fixtures/e3-ml-rule-lhs-and`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-ml-rule-lhs-and` (its text written there is `f2-examples/mllhsandv.kompile.kore` byte for byte, which this
  test reads; its namespace and file named TieLhsAndVar), with the section `Run` by hand; run from the package root: `lake env lean -j1 test/TieLhsAndVar.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 151 sentences of the user module E3-ML-RULE-LHS-AND, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 209 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (37): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (47): Γ with it has no model (`idem_refuted`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (22);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (1).

  The rule (c(X #And d(_, b())) => X, read as c(d(G, b()) #as X) => X; sentence 104) is `uncovered`: Γ's item of it is the reading's rule, whose
  left side holds the predicate as a conjunct of `pre`, and no theorem here ties it to the sentence
  as written. The section `Run`, by hand, states the steps through the reading (C7 form (a), the
  step's closure), for every interpretation H, from `StepBy` and `Holds`:
  - `Run.step`: `<k> c(d(u, b)) </k>` steps to `<k> d(u, b) </k>` for every value u of Exp, for every H
    (X := d(u, b)); `Run.stuck_a`: `<k> c(a) </k>` has no successor, for every H (a is no d(u, b)).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieLhsAndVar

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mllhsandv.kompile.kore"
definition_of defn from "f2-examples/mllhsandv.kompile.kore"
user_axioms U from "f2-examples/mllhsandv.kompile.kore" module "E3-ML-RULE-LHS-AND"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-RULE-LHS-AND")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 151 := by decide +kernel

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
  [("function equation", [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
      128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]),
   ("rewrite rule", [104]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 55, 59, 62, 65, 85, 86]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 63, 66]),
   ("distinctness", [56, 57, 58, 60, 61, 64]),
   ("no junk", [93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]),
   ("function functional", [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 38, 42, 50, 51, 52, 53, 54, 68, 84, 87, 88, 89, 90, 91]),
   ("collection law", [39, 40, 41, 43, 44, 45, 46, 48, 49]),
   ("library", [105, 153]),
   ("set idempotence", [47]),
   ("set-variable lemma", [154]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [36, 37, 67, 92, 106, 107, 108, 109, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
      150, 151, 152])]

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
    [("function equation", 29), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 10), ("subsort", 15), ("injectivity", 6), ("distinctness", 6), ("no junk", 11), ("function functional", 15), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 22)] := by
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
  [(139, "Bool"), (140, "Exp"), (141, "GeneratedCounterCell"), (142, "GeneratedCounterCellOpt"),
   (143, "GeneratedTopCell"), (144, "GeneratedTopCellFragment"), (145, "Int"), (146, "K"),
   (147, "KCell"), (148, "KCellOpt"), (149, "KItem"), (150, "List"), (151, "Map"), (152, "Set")]

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
  [(14, "subsort"), (55, "constructor functional"), (56, "distinctness"), (57, "distinctness"),
   (58, "distinctness"), (59, "constructor functional"), (60, "distinctness"),
   (61, "distinctness"), (62, "constructor functional"), (63, "injectivity"), (64, "distinctness"),
   (65, "constructor functional"), (66, "injectivity"), (70, "function functional"),
   (94, "no junk"), (103, "no junk"), (104, "rewrite rule"), (109, "no direction"),
   (112, "function equation"), (113, "function equation"), (140, "no direction"),
   (154, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  [(104, "rewrite rule")]

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

theorem sig_sizes : (sigItems c).length = 209 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 89, 59, 4, 26) := by
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
  [U.ax124, U.ax132, U.ax131, U.ax130, U.ax129, U.ax136, U.ax135, U.ax138, U.ax137, U.ax134,
   U.ax133, U.ax111, U.ax110, U.ax123, U.ax122, U.ax119, U.ax118, U.ax121, U.ax120, U.ax126,
   U.ax125, U.ax128, U.ax127, U.ax115, U.ax114, U.ax117, U.ax116, U.ax113, U.ax112]

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

theorem nj93 : (trS U.ax93).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj99 : (trS U.ax99).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj102 : (trS U.ax102).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax93, U.ax99, U.ax102], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj93]; exact orTopBot_valid hD rfl
  · rw [nj99]; exact orTopBot_valid hD rfl
  · rw [nj102]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax100, U.ax101],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax103).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (103)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax103).pat := by
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
   U.ax56, U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax62, U.ax63, U.ax64, U.ax65, U.ax66, U.ax85,
   U.ax86]

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


/-! ## The steps through the reading, for every H (by hand) -/

namespace Run

def exp : Srt := 32
def kCell : KCore.Sym := 383
def symA : KCore.Sym := 385
def symB : KCore.Sym := 386
def symC : KCore.Sym := 387
def symD : KCore.Sym := 388

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧ c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" := by
  decide +kernel

theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

theorem prios : c.rules.length = 1 ∧ ∀ r ∈ c.rules, r.prio = 50 := by decide +kernel

/-- The rule the reader reads: `c(d(G, b()) #as X) => X`. -/
noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem r0_mem (H : HookParams) : r0 ∈ (cH H).rules := List.getElem_mem _
theorem rule_eq (H : HookParams) {r : Rule} (hr : r ∈ (cH H).rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have : i = 0 := by have := prios.1; simp only [cH, Semantics.withHooks] at hi ⊢; omega
  subst this
  rfl

/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(p), Vk)), Vc)`. -/
def cfgP (p : Term) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem p, .var 2]], .var 3]

/-- `\and(X, d(G, b()))` read as `d(G, b()) #as X`: G the variable 0, X the variable 1. -/
theorem r0_vars : r0.vars = [exp, exp, Srt.k, 19] := by decide +kernel
theorem r0_lhs : r0.lhs = cfgP (.app symC [.as (.app symD [.var 0, .app symB []]) 1]) := rfl
theorem r0_rhs : r0.rhs = cfgP (.var 1) := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [] ∧ r0.pre = .top ∧ r0.post = .top :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symB = true ∧ c.isCtor symC = true ∧ c.isCtor symD = true := by
  decide +kernel

theorem symsH (H : HookParams) : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧
    (cH H).isCtor kseq = true ∧ (cH H).isCtor symB = true ∧ (cH H).isCtor symC = true ∧
    (cH H).isCtor symD = true := syms_ok

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false ∧
    patternHooks.contains symD = false ∧ patternHooks.contains symB = false := by
  decide +kernel

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symC).isSome = true ∧
    (lookupSig c.ctorSigs symD).isSome = true := by
  decide +kernel

theorem exp_bottom : ∀ p ∈ c.subsorts, p.2 ≠ exp := by
  intro p hp
  have h : c.subsorts.all (fun p => p.2 != exp) = true := by decide +kernel
  simpa using List.all_eq_true.mp h p hp

theorem sortOf_ctor_congrL {f : KCore.Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congrL {t t0 : GroundTerm} {ts : List GroundTerm}
    (h : c.sortOf t = c.sortOf t0) : c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congrL {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

/-- A value of Exp, a sort no sort lies below, is no injection. -/
theorem isInj_of_expL {v : GroundTerm} (hv : c.sortOf v = some exp) : v.isInj = false := by
  cases v with
  | inj a b w =>
    simp only [Semantics.sortOf] at hv
    split at hv
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      cases hv
      exact absurd rfl (exp_bottom _ hc.1.1)
    · cases hv
  | _ => rfl

theorem patVal_ctor2L {c : Semantics} {σ : Subst} {f : KCore.Sym} {p q : Term} {v w : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p, q]) (.ctor f [v, w])) : PatVal c σ p v ∧ PatVal c σ q w := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, hs1⟩ := PatVals.cons_inv hs
  cases he1
  obtain ⟨_, _, he2, h2, _⟩ := PatVals.cons_inv hs1
  cases he2
  exact ⟨h1, h2⟩

theorem patVal_ctor1L {c : Semantics} {σ : Subst} {f : KCore.Sym} {p : Term} {v : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p]) (.ctor f [v])) : PatVal c σ p v := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, _⟩ := PatVals.cons_inv hs
  cases he1
  exact h1

def A : GroundTerm := .ctor symA []
def B : GroundTerm := .ctor symB []
def ctr : GroundTerm := .ctor counterLabel [int 0]
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(st), dotk)), <generatedCounter>(0))`. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj exp Srt.kitem st, .ctor dotk []]], ctr]
/-- `d(u, b)`. -/
def D (u : GroundTerm) : GroundTerm := .ctor symD [u, B]

theorem sortOf_A : c.sortOf A = some exp := by decide +kernel
theorem sortOf_B : c.sortOf B = some exp := by decide +kernel

theorem sortOf_D {u : GroundTerm} (hu : c.sortOf u = some exp) : c.sortOf (D u) = some exp := by
  have h0 : c.sortOf (D B) = some exp := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congrL lookups_ok.2.2.2.2 (sortsOf_head_congrL (by rw [hu, sortOf_B]))

theorem sortOf_cfg {g : GroundTerm} (hg : c.sortOf g = some exp) : c.sortOf (cfg g) = some topCellSort := by
  have h0 : c.sortOf (cfg A) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congrL lookups_ok.1 (sortsOf_head_congrL (sortOf_ctor_congrL lookups_ok.2.1
    (sortsOf_head_congrL (sortOf_ctor_congrL lookups_ok.2.2.1 (sortsOf_head_congrL
      (sortOf_inj_congrL (by rw [hg, sortOf_A]) (by rw [isInj_of_expL hg]; rfl)))))))

theorem sortOf_cfgC {z : GroundTerm} (hz : c.sortOf z = some exp) :
    c.sortOf (cfg (.ctor symC [z])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symC [A])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congrL lookups_ok.1 (sortsOf_head_congrL (sortOf_ctor_congrL lookups_ok.2.1
    (sortsOf_head_congrL (sortOf_ctor_congrL lookups_ok.2.2.1 (sortsOf_head_congrL (sortOf_inj_congrL
      (sortOf_ctor_congrL lookups_ok.2.2.2.1 (sortsOf_head_congrL (by rw [hz, sortOf_A]))) rfl))))))

/-- `<k> c(z) </k>` under H. -/
def C (H : HookParams) (z : GroundTerm) (hz : c.sortOf z = some exp) : Config (cH H) :=
  ⟨cfg (.ctor symC [z]), by rw [sortOfH]; exact sortOf_cfgC hz⟩
/-- `<k> g </k>` under H. -/
def G (H : HookParams) (g : GroundTerm) (hg : c.sortOf g = some exp) : Config (cH H) :=
  ⟨cfg g, by rw [sortOfH]; exact sortOf_cfg hg⟩

def σ (u : GroundTerm) : Subst := [(0, u), (1, D u), (2, .ctor dotk []), (3, ctr)]

/-- **`c(d(u, b))` steps to `d(u, b)`**, for every value u of Exp and every H: X := d(u, b). -/
theorem step (H : HookParams) {u : GroundTerm} (hu : c.sortOf u = some exp) :
    Step (cH H) (C H (D u) (sortOf_D hu)) (G H (D u) (sortOf_D hu)) := step_iff_by.mpr ⟨r0, σ u, {
  mem := r0_mem H
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact hu⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact sortOf_D hu⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
    | 3, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
  hmatch := by
    rw [r0_lhs]
    have hi : injNormal exp Srt.kitem (.ctor symC [D u]) = .inj exp Srt.kitem (.ctor symC [D u]) := rfl
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons (hi ▸ .inj (.ctor (symsH H).2.2.2.2.1 (.cons (.as (.ctor (symsH H).2.2.2.2.2
        (.cons (.var rfl) (.cons (.ctor (symsH H).2.2.2.1 .nil) .nil))) rfl) .nil)))
        (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    have hig : injNormal exp Srt.kitem (D u) = .inj exp Srt.kitem (D u) := rfl
    have he : EvalTerm (cH H) (σ u) (.inj exp Srt.kitem (.var 1))
        (((σ u).lookup 1).map (injNormal exp Srt.kitem)) := .inj .var
    have hv : ((σ u).lookup 1).map (injNormal exp Srt.kitem) = some (.inj exp Srt.kitem (D u)) := by
      show (some (D u)).map _ = _
      rw [Option.map_some, hig]
    rw [hv] at he
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.2]; exact .top
  hprio := fun r' hr' hlt => by
    rw [prios.2 r' hr', prios.2 r0 (r0_mem H)] at hlt; exact absurd hlt (Nat.lt_irrefl _) }⟩

/-- A match of the left side at `<k> c(z) </k>`: z is `d(u, b)` for the value u of G. -/
theorem match_inv (H : HookParams) {τ : Subst} {z : GroundTerm}
    (hm : PatVal (cH H) τ r0.lhs (cfg (.ctor symC [z]))) : ∃ u, z = D u := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2L hooks_ok.1 (symsH H).1 hm).1
  have h2 := patVal_ctor1L hooks_ok.2.1 (symsH H).2.1 h1
  have h3 := (patVal_ctor2L hooks_ok.2.2.1 (symsH H).2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2.1 hw (symsH H).2.2.2.2.1
  have he' : GroundTerm.inj exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  have h5 := (PatVal.as_inv h4).1
  obtain ⟨-, ws, rfl, hs'⟩ := PatVal.app_inv hooks_ok.2.2.2.2.1 h5 (symsH H).2.2.2.2.2
  obtain ⟨u, _, rfl, -, hs1⟩ := PatVals.cons_inv hs'
  obtain ⟨v, _, rfl, hv, hs2⟩ := PatVals.cons_inv hs1
  cases PatVals.nil_inv hs2
  obtain ⟨-, vs', rfl, hs3⟩ := PatVal.app_inv hooks_ok.2.2.2.2.2 hv (symsH H).2.2.2.1
  cases PatVals.nil_inv hs3
  exact ⟨u, rfl⟩

/-- **`c(a)` has no successor, for every H**: a is no `d(u, b)`. -/
theorem stuck_a (H : HookParams) (y : Config (cH H)) : ¬ Step (cH H) (C H A sortOf_A) y := by
  intro h
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  have hr := rule_eq H hs.mem
  subst hr
  obtain ⟨u, hu⟩ := match_inv H hs.hmatch
  cases hu

end Run

end KCore.TieLhsAndVar

#check @KCore.TieLhsAndVar.noRaw
#check @KCore.TieLhsAndVar.readsConfined_c
#check @KCore.TieLhsAndVar.userAxioms_eq
#check @KCore.TieLhsAndVar.coreOK
#check @KCore.TieLhsAndVar.wf_defn
#check @KCore.TieLhsAndVar.account
#check @KCore.TieLhsAndVar.account_sizes
#check @KCore.TieLhsAndVar.account_classes
#check @KCore.TieLhsAndVar.account_absent
#check @KCore.TieLhsAndVar.absent_closed
#check @KCore.TieLhsAndVar.absent_proj_below_c
#check @KCore.TieLhsAndVar.absent_proj_below
#check @KCore.TieLhsAndVar.lists_in_account
#check @KCore.TieLhsAndVar.attrs_agree
#check @KCore.TieLhsAndVar.sig_origin
#check @KCore.TieLhsAndVar.decls_entailed
#check @KCore.TieLhsAndVar.consistent
#check @KCore.TieLhsAndVar.fn_shape
#check @KCore.TieLhsAndVar.fns_account
#check @KCore.TieLhsAndVar.fns_entailed
#check @KCore.TieLhsAndVar.fns_from_text
#check @KCore.TieLhsAndVar.fn_prios
#check @KCore.TieLhsAndVar.nojunk_trivial_entailed
#check @KCore.TieLhsAndVar.nojunk_items_entailed
#check @KCore.TieLhsAndVar.nojunk_kitem_entailed
#check @KCore.TieLhsAndVar.cons_entailed
#check @KCore.TieLhsAndVar.idem_refuted
#print axioms KCore.TieLhsAndVar.noRaw
#print axioms KCore.TieLhsAndVar.readsConfined_c
#print axioms KCore.TieLhsAndVar.userAxioms_eq
#print axioms KCore.TieLhsAndVar.coreOK
#print axioms KCore.TieLhsAndVar.wf_defn
#print axioms KCore.TieLhsAndVar.account
#print axioms KCore.TieLhsAndVar.account_sizes
#print axioms KCore.TieLhsAndVar.account_classes
#print axioms KCore.TieLhsAndVar.account_absent
#print axioms KCore.TieLhsAndVar.absent_closed
#print axioms KCore.TieLhsAndVar.absent_proj_below_c
#print axioms KCore.TieLhsAndVar.absent_proj_below
#print axioms KCore.TieLhsAndVar.lists_in_account
#print axioms KCore.TieLhsAndVar.attrs_agree
#print axioms KCore.TieLhsAndVar.sig_origin
#print axioms KCore.TieLhsAndVar.decls_entailed
#print axioms KCore.TieLhsAndVar.consistent
#print axioms KCore.TieLhsAndVar.fn_shape
#print axioms KCore.TieLhsAndVar.fns_account
#print axioms KCore.TieLhsAndVar.fns_entailed
#print axioms KCore.TieLhsAndVar.fns_from_text
#print axioms KCore.TieLhsAndVar.fn_prios
#print axioms KCore.TieLhsAndVar.nojunk_trivial_entailed
#print axioms KCore.TieLhsAndVar.nojunk_items_entailed
#print axioms KCore.TieLhsAndVar.nojunk_kitem_entailed
#print axioms KCore.TieLhsAndVar.cons_entailed
#print axioms KCore.TieLhsAndVar.idem_refuted
#check @KCore.TieLhsAndVar.Run.step
#check @KCore.TieLhsAndVar.Run.stuck_a
#print axioms KCore.TieLhsAndVar.Run.step
#print axioms KCore.TieLhsAndVar.Run.stuck_a
