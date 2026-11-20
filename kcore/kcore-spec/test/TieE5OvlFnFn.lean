/-
  The tie (C14) on `f2-examples/e5-ovl-fn-fn.kompile.kore`, the kompiled text of construct fixture e5-ovl-fn-fn
  (`test/constructs/fixtures/e5-ovl-fn-fn`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e5-ovl-fn-fn`; run from the package root: `lake env lean -j1 test/TieE5OvlFnFn.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 262 sentences of the user module E5-OVL-FN-FN, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 14 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_parts`, `attrs_prios_false`, `attrs_prios_but`: the attributes the translation does not
    read agree with `defn` but for the priorities (`attrsAgree` is false by `prios` alone): the
    clause read from a `symbol-overload` axiom has the priority 0, which the reading gives and no
    attribute states; with it and the overload axioms left out (`AttrsAgree.priosBut`) the
    priorities agree, and each clause left out is tied to its sentence (LblnegExp 0: sentence 124,
    `prios_out_at0`, `prios_out_entailed0`). At Γ's item 0 the item binds the argument by a
    membership where the axiom applies the function to the argument pattern, an injection: the axiom
    is the item's text form up to the names of the variables (`ovlm<j>_same`, `TieOvlMem.textItem`),
    and Γ entails it, its models having the constructors' facts and Cons-Fun of the injection
    (`TieOvlMem.ovlMem_entailed`).
  - `sig_origin_but_next`: each of the 208 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes
    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's
    condition (`owed_rules`, `owed_clauses`), so Γ with the step's closure has a model for every
    H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (32) and priority equations (0), in the order `fnText` lists them
    (`fns_account`): each of Γ's items but 0 is the translation of one sentence (`shape`), so Γ
    entails it (`fns_entailed`). Item 0 (124) is the clause read from a `symbol-overload` axiom,
    pinned to its axiom (`fnPins`): Γ's item binds the argument by a membership, the axiom applies
    the function to the argument pattern, an injection, and is the item's text form
    (`TieOvlMem.textItem`, `ovlm<j>_same`; not the item, `ovlm<j>_differs`). Γ entails the axiom
    (`prios_out_entailed<j>`, in `fns_entailed`), and the axiom gives the item in a model with the
    constructors' facts and Cons-Fun of the injection (`ovlm<j>_from_text`), which `fns_from_text`
    leaves out. `fns_from_text` (the converse), `fn_prios_but` (the priorities the sentences state
    are the clauses' but at the overload clauses).
  - Constructor sentences (27): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (62): Γ with it has no model (`idem_refuted`).
  - Library sample, 164 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a consequence of the function sentences, Γ's own
    item 0 (whose sentence gives it with the constructors' facts and Cons-Fun of the injection:
    `ovlm<j>_from_text`), Γ's rule items, the five parts Γ defines by predicates, or definedness
    (`gamma_from`).
  - Function functional: at values in every model of `Γc`, from `FnHyp`, which holds for every H
    (`fnHypH`), and the sort predicates' results (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (14);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFnFn

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fn-fn.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fn-fn.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fn-fn.kompile.kore" module "E5-OVL-FN-FN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E5-OVL-FN-FN")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 262 := by decide +kernel

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
  [("function equation", [124, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228,
      229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 245, 246]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [23, 25, 27, 29, 79, 103, 104]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]),
   ("injectivity", [24, 26, 28, 30]),
   ("distinctness", []),
   ("no junk", [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]),
   ("function functional", [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 102]),
   ("hooked functional", [20, 21, 22, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      57, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 77, 78, 80, 82, 99, 100, 101, 105, 106, 107, 108,
      109, 110]),
   ("collection law", [54, 55, 56, 58, 59, 60, 61, 63, 64]),
   ("library", [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
      148, 149, 150, 151, 152, 153, 154, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166,
      167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
      185, 186, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
      204, 205, 206, 207, 243, 244, 247, 248, 263, 264]),
   ("set idempotence", [62]),
   ("set-variable lemma", [125, 126, 127, 128, 129, 265]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [37, 41, 43, 74, 76, 81, 98, 111, 112, 155, 187, 208, 209, 210, 211, 241, 242, 249, 250, 251,
      252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262])]

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
    [("function equation", 32), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 7), ("subsort", 16), ("injectivity", 4), ("distinctness", 0), ("no junk", 11), ("function functional", 16), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 31)] := by
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
  [(249, "Bool"), (250, "Exp"), (251, "GeneratedCounterCell"), (252, "GeneratedCounterCellOpt"),
   (253, "GeneratedTopCell"), (254, "GeneratedTopCellFragment"), (255, "Int"), (256, "K"),
   (257, "KCell"), (258, "KCellOpt"), (259, "KItem"), (260, "List"), (261, "Map"), (262, "Set")]

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
  [(14, "subsort"), (18, "subsort"), (79, "constructor functional"), (84, "function functional"),
   (102, "function functional"), (114, "no junk"), (123, "no junk"), (124, "function equation"),
   (211, "no direction"), (214, "function equation"), (215, "function equation"),
   (245, "function equation"), (246, "function equation"), (250, "no direction")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn` but for the priorities**: constructors, functions,
hooks and collection symbols agree (`attrs_parts`), and `prios` is false (`attrs_prios_false`). -/
theorem attrs_parts : AttrsAgree.ctors kore defn.sem = true ∧ AttrsAgree.fns kore defn.sem = true ∧
    AttrsAgree.hooks kore defn.sem = true ∧ AttrsAgree.colls kore defn.sem = true := by decide +kernel
theorem attrs_prios_false : AttrsAgree.prios kore defn = false ∧ attrsAgree kore defn = false := by
  decide +kernel

/-- The clause read from a `symbol-overload` axiom, by (function, position): its priority 0 is what
the reading gives such a clause, below every other clause of the function, and no attribute states
it; the text's equations of the function count the axiom at the default 50. The overload axiom of
the user module, by index. -/
def priosOutCl : List (String × Nat) := [("LblnegExp", 0)]
def priosOutAx : List Nat := [124]

/-- **With the overload clauses left out of the clause side and the overload axioms left out of the
text side, the priorities agree** (`AttrsAgree.priosBut`). Each clause left out is tied to its
sentence: `prios_out_at0`, `prios_out_entailed0`. -/
theorem attrs_prios_but : AttrsAgree.priosBut priosOutAx priosOutCl kore defn = true := by decide +kernel

kernel_rfl ovlm_consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- Γ's axiom of item 0. -/
noncomputable def ovlmAx0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
/-- **The clause 0 of `LblnegExp`, which `attrs_prios_but` leaves out, is Γ's item 0** (kernel). -/
theorem prios_out_at0 : ((c.allFns.takeWhile (c.symName ·.label != "LblnegExp")).map (·.clauses.length)).sum + 0 = 0 ∧
    (TiePair.fnAxioms c)[0]? = some ovlmAx0 := by decide +kernel
noncomputable def ovlmItem0 : P := (trAxiom [] [] ⟨0, "kernel", ovlmAx0⟩).pat
theorem ovlmItem0_at : (TiePair.gammaPats c)[0]? = some ovlmItem0 := TiePair.gammaPats_at prios_out_at0.2
/-- The text's form of item 0 (`TieOvlMem.textItem`): Γ's item binds the argument by the membership
`x ∈ inj{SortInt, SortExp}(VarV0)`, the text's form applies `LblnegExp` to that pattern. -/
noncomputable def ovlmText0 : P := (TieOvlMem.textItem ovlmAx0).getD .bottom
kernel_rfl ovlm0_text_eq : TieOvlMem.textItem ovlmAx0 = some ovlmText0
theorem ovlm0_ok : TieOvlMem.okB c ovlmAx0 = true := by decide +kernel
/-- The argument is the injection of `VarV0` into SortExp, and Cons-Fun of that injection is
an item of Γ (kernel). -/
theorem ovlm0_inj : TieOvlMem.injB ovlmAx0 "Exp" "Int"
    ⟨⟨⟨"VarV0"⟩⟩, .ctor ⟨⟨"SortInt"⟩⟩ []⟩ = true := by decide +kernel
theorem ovlm0_injFun : (consItemsK c).any (·.pat == (Cons.funItem "Exp" (.inj "Int")).pat) = true := by
  decide +kernel
/-- **Sentence 124 is the text's form of item 0** up to the names of the variables (kernel). -/
theorem ovlm0_same : TieAlpha.acEqB ovlmText0 (trS U.ax124).pat = true := by decide +kernel

/-- **E for sentence 124**: a model of Γ has the constructors' facts and Cons-Fun of the injection,
where the argument is one element of SortExp (`TieOvlMem.argOne_inj`), and there Γ's item 0 gives
the item's text form (`TieOvlMem.ovlMem_entailed`), so Γ entails the sentence, for every H. -/
theorem prios_out_entailed0 (H : HookParams) : Γ (cH H) ⊧ (trS U.ax124).pat := by
  intro M _ I hI
  have hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "Int")).pat := by
    obtain ⟨it, hit, he⟩ := List.any_eq_true.mp ovlm0_injFun
    rw [← of_decide_eq_true he]
    exact sat_cons hI (Or.inl ⟨it, by rw [ovlm_consItemsK_withHooks]; exact hit, rfl⟩)
  obtain ⟨it, hit, he⟩ : ∃ it ∈ fnItems c, it.pat = ovlmItem0 := by
    have hg := ovlmItem0_at
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[0]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  have hg : I ⊧ᴵ ovlmItem0 := by
    rw [← he]
    exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))
  exact (TieAlpha.acEqB_sat ovlm0_same).mp (TieOvlMem.ovlMem_entailed
    (HoldsShape.nodeFacts_of_core (coreOKH H)
      (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI))
    ovlm0_text_eq ((TieOvlMem.okB_withHooks c H _).trans ovlm0_ok)
    (TieOvlMem.argOne_inj (defOK hI) hf ovlm0_inj) hg)


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

theorem sig_sizes : (sigItems c).length = 208 := by decide +kernel

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
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 131, 93, 5, 33) := by
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
387,386]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  (FnFacts.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)
    (show c.params.all (fun k => !k.raw) = true by decide +kernel)).obligations (openDecidedH H)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Function functional (16): the `functional` sentences, at values in every model of Γc, from `FnHyp` -/

/- The class holds 16 `functional` sentences, `\exists{R}(Val:S, \equals{S, R}(Val:S, f(K0, …)))`:
15 of sort predicates `isX` (KCore builds them, `Semantics.sortPreds`) and 1 of functions of the
text declared total (102). A model of `Γc` reads the application of a function with a value at every
argument list of its sorts, at values' elements, as that value's element (`LibEv.fnFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and the clauses' conditions
decided where `needsWitness` holds). A sort predicate has those values from its own clauses
(`LibEv.sortPredFun_evC`); a function declared total has them from `FnHyp`
(`LibEv.fnFun_evC_withHooks`). `FnHyp`, which the tie states for every H (`fnHypH`), decides the
conditions (its `OpenDecided`). So each sentence holds in every model of `Γc`, and of `Γc` with the
step's closure, at every valuation sending its variables to values, for every H. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 102]

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

/-- None of the 16 reads a declaration or an alias. -/
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

theorem nj113 : (trS U.ax113).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj119 : (trS U.ax119).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj122 : (trS U.ax122).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax113, U.ax119, U.ax122], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj113]; exact orTopBot_valid hD rfl
  · rw [nj119]; exact orTopBot_valid hD rfl
  · rw [nj122]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax120, U.ax121],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax120, U.ax121],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax123).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (123)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax123).pat := by
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
   U.ax79, U.ax103, U.ax104]

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


/-! ## Library sample: sentence 164, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax164).pat = (trAxiom [] [] U.ax164).pat := by decide +kernel
theorem s166_pattern : U.ax164.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax164.ax.sortVars.map sortVarKey ++ freeOf [] U.ax164.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax164.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 164 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax164.ax.sortVars U.ax164.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax164).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax164.ax.sortVars U.ax164.ax.pattern = t at he ⊢
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
/-- **Sentence 164 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax164 (trS U.ax164).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## Function equations (32 sentences) and priority equations (0 sentences)

Γ's item 0 (sentence 124) is the clause read from a `symbol-overload` axiom, pinned to its axiom
(`fnPins`). Γ's item states the equation with a variable x at the argument, bound by the membership
of x in the argument pattern `inj{A, N}(v)`, and the axiom applies the function to that pattern
itself: the axiom is the item's text form (`TieOvlMem.textItem`, up to the names of its variables:
`ovlm<j>_same`, in layer 1), and it is not the item (`ovlm<j>_differs`). The two hold in the same
models with the constructors' facts in which the argument is one element of N, which Cons-Fun of the
injection gives (`TieOvlMem.ovlMem_iff`, `TieOvlMem.argOne_inj`). A model of Γ has both, so Γ
entails the axiom (`prios_out_entailed<j>`, layer 1), and the axiom gives the item in a model with
both (`ovlm<j>_from_text`), which `fns_from_text` leaves out (its premise set is the sentence
alone). The priority 0 the reading gives such a clause is stated by no attribute, so the priorities
agree at every position but those (`fn_prios_but`).

Every other item is the translation of its function sentence (`shape`). -/

/-- The pins of the alignment, `(item, sentence index)`: each clause read from a `symbol-overload`
axiom, at that axiom. -/
def fnPins : List (Nat × Nat) := [(0, 124)]

/-- The text sentences of Γ's equations, in `fnItems`'s order: a pinned position holds its
sentence, every other one the first sentence of its head symbol and priority that no earlier
position took (`TiePair.fnTextMany`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnTextO : List (Option AxiomDecl) := TiePair.fnTextMany c U.all fnPins

/-- **Each pin names a clause position and an equation of that clause's function, no position
twice, the positions of one sentence consecutive** (kernel). -/
theorem fnPins_ok : TiePair.pinsOK c U.all fnPins = true := by decide +kernel

/-- **Every position holds a sentence, one per item of `fnItems`** (kernel). -/
theorem fnText_all : TiePair.manyAllSomeB fnTextO = true ∧ TiePair.manyLengthB c fnTextO = true := by
  decide +kernel

noncomputable def fnText : List AxiomDecl := fnTextO.filterMap id

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once, a pinned sentence at each position of its run. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm
      (fnText.map (·.index)).eraseDups = true := by
  decide +kernel

kernel_rfl fnText_at0 : fnText[0]? = some U.ax124
/-- **Γ's item 0 is not the text's sentence 124** (kernel). -/
theorem ovlm0_differs : ovlmItem0 ≠ (trS U.ax124).pat := by decide +kernel

/-- **Sentence 124 gives Γ's item 0** in a model with the constructors' facts and Cons-Fun of the
injection, for every H (`TieOvlMem.ovlMem_from_text`). -/
theorem ovlm0_from_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "Int")).pat)
    (h : I ⊧ᴵ (trS U.ax124).pat) : I ⊧ᴵ ovlmItem0 :=
  TieOvlMem.ovlMem_from_text N ovlm0_text_eq ((TieOvlMem.okB_withHooks c H _).trans ovlm0_ok)
    (TieOvlMem.argOne_inj N.defOK hf ovlm0_inj) ((TieAlpha.acEqB_sat ovlm0_same).mpr h)

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item at position 0. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 ovlmItem0

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

/-- **E for the function equations**: Γ entails each sentence of `fnText`, for every H; item 0 by `prios_out_entailed0`. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ ([] : List Nat) → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  by_cases h0 : j = 0
  · subst h0
    rw [fnText_at0] at hj
    rw [← Option.some.inj hj]
    exact prios_out_entailed0 H
  have hn' : j ∉ pairSetAt := by
    simp only [pairSetAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    omega
  exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))

/-- **The converse for `fnItems`**: each item but the overload clauses given with the constructors' facts and Cons-Fun of the injection (items 0) is a consequence of a text sentence, the j-th of `fnText`; the others by their translation. -/
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

/-- The positions of the clauses read from a `symbol-overload` axiom. -/
def priosOutJ : List Nat := [0]

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order, but at the clauses read from a `symbol-overload`
axiom (`priosOutJ`): the axiom states no priority, read as 50, and the reading gives the clause 0. -/
theorem fn_prios_but : fnText.length = (c.allFns.flatMap (fun f => f.clauses.map (·.prio))).length ∧
    ((fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes)).zip
      (c.allFns.flatMap (fun f => f.clauses.map (·.prio)))).zipIdx.all
      (fun x => x.1.1 == x.1.2 || priosOutJ.contains x.2) = true := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (the items set to
Γ's through their sentences, the overload clauses as Γ's own), Γ's rule items and the five parts Γ defines by predicates
(`TiePair.Pre`), for every H. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → TiePair.Pre (cH H) textPats ⊧ φ :=
  TiePair.gamma_from (shapeH H)


end KCore.TieE5OvlFnFn

#check @KCore.TieE5OvlFnFn.noRaw
#check @KCore.TieE5OvlFnFn.readsConfined_c
#check @KCore.TieE5OvlFnFn.userAxioms_eq
#check @KCore.TieE5OvlFnFn.coreOK
#check @KCore.TieE5OvlFnFn.wf_defn
#check @KCore.TieE5OvlFnFn.account
#check @KCore.TieE5OvlFnFn.account_sizes
#check @KCore.TieE5OvlFnFn.account_classes
#check @KCore.TieE5OvlFnFn.account_absent
#check @KCore.TieE5OvlFnFn.absent_closed
#check @KCore.TieE5OvlFnFn.absent_proj_below_c
#check @KCore.TieE5OvlFnFn.absent_proj_below
#check @KCore.TieE5OvlFnFn.lists_in_account
#check @KCore.TieE5OvlFnFn.attrs_parts
#check @KCore.TieE5OvlFnFn.attrs_prios_false
#check @KCore.TieE5OvlFnFn.attrs_prios_but
#check @KCore.TieE5OvlFnFn.prios_out_at0
#check @KCore.TieE5OvlFnFn.ovlm0_ok
#check @KCore.TieE5OvlFnFn.ovlm0_inj
#check @KCore.TieE5OvlFnFn.ovlm0_injFun
#check @KCore.TieE5OvlFnFn.ovlm0_same
#check @KCore.TieE5OvlFnFn.prios_out_entailed0
#check @KCore.TieE5OvlFnFn.sig_origin_but_next
#check @KCore.TieE5OvlFnFn.decls_entailed
#check @KCore.TieE5OvlFnFn.consistent
#check @KCore.TieE5OvlFnFn.fnFun_indices
#check @KCore.TieE5OvlFnFn.fnFun_account
#check @KCore.TieE5OvlFnFn.fnFun_checked
#check @KCore.TieE5OvlFnFn.fnFun_trS
#check @KCore.TieE5OvlFnFn.fnFun_at_values
#check @KCore.TieE5OvlFnFn.fnFun_at_values_step
#check @KCore.TieE5OvlFnFn.text_nextless
#check @KCore.TieE5OvlFnFn.nojunk_trivial_entailed
#check @KCore.TieE5OvlFnFn.nojunk_items_entailed
#check @KCore.TieE5OvlFnFn.nojunk_kitem_entailed
#check @KCore.TieE5OvlFnFn.cons_entailed
#check @KCore.TieE5OvlFnFn.idem_refuted
#check @KCore.TieE5OvlFnFn.lib166
#check @KCore.TieE5OvlFnFn.lib166_at_values
#check @KCore.TieE5OvlFnFn.owed_rules
#check @KCore.TieE5OvlFnFn.owed_clauses
#check @KCore.TieE5OvlFnFn.openDecidedH
#print axioms KCore.TieE5OvlFnFn.noRaw
#print axioms KCore.TieE5OvlFnFn.readsConfined_c
#print axioms KCore.TieE5OvlFnFn.userAxioms_eq
#print axioms KCore.TieE5OvlFnFn.coreOK
#print axioms KCore.TieE5OvlFnFn.wf_defn
#print axioms KCore.TieE5OvlFnFn.account
#print axioms KCore.TieE5OvlFnFn.account_sizes
#print axioms KCore.TieE5OvlFnFn.account_classes
#print axioms KCore.TieE5OvlFnFn.account_absent
#print axioms KCore.TieE5OvlFnFn.absent_closed
#print axioms KCore.TieE5OvlFnFn.absent_proj_below_c
#print axioms KCore.TieE5OvlFnFn.absent_proj_below
#print axioms KCore.TieE5OvlFnFn.lists_in_account
#print axioms KCore.TieE5OvlFnFn.attrs_parts
#print axioms KCore.TieE5OvlFnFn.attrs_prios_false
#print axioms KCore.TieE5OvlFnFn.attrs_prios_but
#print axioms KCore.TieE5OvlFnFn.prios_out_at0
#print axioms KCore.TieE5OvlFnFn.ovlm0_ok
#print axioms KCore.TieE5OvlFnFn.ovlm0_inj
#print axioms KCore.TieE5OvlFnFn.ovlm0_injFun
#print axioms KCore.TieE5OvlFnFn.ovlm0_same
#print axioms KCore.TieE5OvlFnFn.prios_out_entailed0
#print axioms KCore.TieE5OvlFnFn.sig_origin_but_next
#print axioms KCore.TieE5OvlFnFn.decls_entailed
#print axioms KCore.TieE5OvlFnFn.consistent
#print axioms KCore.TieE5OvlFnFn.fnFun_indices
#print axioms KCore.TieE5OvlFnFn.fnFun_account
#print axioms KCore.TieE5OvlFnFn.fnFun_checked
#print axioms KCore.TieE5OvlFnFn.fnFun_trS
#print axioms KCore.TieE5OvlFnFn.fnFun_at_values
#print axioms KCore.TieE5OvlFnFn.fnFun_at_values_step
#print axioms KCore.TieE5OvlFnFn.text_nextless
#print axioms KCore.TieE5OvlFnFn.nojunk_trivial_entailed
#print axioms KCore.TieE5OvlFnFn.nojunk_items_entailed
#print axioms KCore.TieE5OvlFnFn.nojunk_kitem_entailed
#print axioms KCore.TieE5OvlFnFn.cons_entailed
#print axioms KCore.TieE5OvlFnFn.idem_refuted
#print axioms KCore.TieE5OvlFnFn.lib166
#print axioms KCore.TieE5OvlFnFn.lib166_at_values
#print axioms KCore.TieE5OvlFnFn.owed_rules
#print axioms KCore.TieE5OvlFnFn.owed_clauses
#print axioms KCore.TieE5OvlFnFn.openDecidedH
#check @KCore.TieE5OvlFnFn.fnPins_ok
#check @KCore.TieE5OvlFnFn.fnText_all
#check @KCore.TieE5OvlFnFn.fns_account
#check @KCore.TieE5OvlFnFn.ovlm0_differs
#check @KCore.TieE5OvlFnFn.ovlm0_from_text
#check @KCore.TieE5OvlFnFn.shape
#check @KCore.TieE5OvlFnFn.fns_entailed
#check @KCore.TieE5OvlFnFn.fns_from_text
#check @KCore.TieE5OvlFnFn.fn_prios_but
#check @KCore.TieE5OvlFnFn.gamma_from
#print axioms KCore.TieE5OvlFnFn.fnPins_ok
#print axioms KCore.TieE5OvlFnFn.fnText_all
#print axioms KCore.TieE5OvlFnFn.fns_account
#print axioms KCore.TieE5OvlFnFn.ovlm0_differs
#print axioms KCore.TieE5OvlFnFn.ovlm0_from_text
#print axioms KCore.TieE5OvlFnFn.shape
#print axioms KCore.TieE5OvlFnFn.fns_entailed
#print axioms KCore.TieE5OvlFnFn.fns_from_text
#print axioms KCore.TieE5OvlFnFn.fn_prios_but
#print axioms KCore.TieE5OvlFnFn.gamma_from
