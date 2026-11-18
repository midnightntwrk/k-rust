/-
  The tie (C14) on `f2-examples/unbound.kompile.kore` (fixture e2-unbound: `syntax Exp ::= a() | b(Int)`,
  the one rule `<k> a() => b(X) ... </k> [unboundVariables(X)]`), sentence by sentence, against the
  translation of the text as written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), stated on
  the literal `defn` for every interpretation H: layer 1, the function equations, the no-junk and
  constructor sentences, set idempotence and the account. Run from the package root:
  `lake env lean -j1 test/TieUnbound.lean`.

  The text shares 248 of its 261 user-module sentences with `f2-examples/ens.kompile.kore`, text for
  text up to Location, Source and UNIQUE_ID attributes; the sections below state over this text's
  indices what test/TieEns.lean states over ens's. The other 13: the subsort of Exp (14), the `functional` sentences of `a`
  and `b` (77, 80), their distinctness (78), `b`'s injectivity (81), isExp's `functional` sentence
  (86), Exp's and KItem's no junk (115, 124), the rule (154), `initKCell` (212), isExp's two
  equations (215, 216) and the projection to Exp (249).

  The rule leaves X open, so the definition reads a confined sort and its theory is `Γc = Γ ∪ Γcl`
  (`readsConfined_c`). Each statement below is over Γ; `Γc` holds every premise of Γ, so each holds
  over `Γc` as well (`Γ_sub_Γc`, the `_c` forms at the end).

  Layer 1.
  - `wf_defn`: `wf defn = true` (kernel).
  - `not_reordered`: `Reordered defn.emit kore` is false: the emitted user module has 430 sentences,
    the text's 402. So `Tied kore` does not hold, whatever `Parse.parse kore` is.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (29: the sort predicates' `isX` equations 213 to 241, 14 of them `[owise]`):
    `fn_shape` shows that each of the 29 items of `fnItems` is the translation of one text sentence,
    in the order `fnText` lists them (a kernel decision). isExp's `[owise]` sentence (215) names its
    bound variable `_Gen1`, ens's `_Gen0`; the translation reads variables by their keys in the
    sentence's table, and the two give equal patterns. `fns_entailed` (E) and `fns_from_text` (the
    converse) follow.
  - No junk of Bool, Int, KConfigVar (114, 120, 123): logical truths (`nojunk_trivial_entailed`).
  - No junk of Exp and the cells (115 to 119, 121, 122): each translation is one of Γ's constructor
    items (`nojunk_items`). KItem's (124) is Γ's item with its disjuncts in the text's order
    (`nojunk_kitem_order`), entailed by Γ for every H (`nojunk_kitem_entailed`).
  - Constructor sentences (29: `functional` of the 8 constructors, among them `a` and `b`, the 15
    `subsort` sentences, 5 no-confusion sentences of one constructor, 1 of two): entailed by Γ, for
    every H (`cons_entailed`).
  - Set idempotence (61): Γ with it has no model, for every H (`idem_refuted`).
  - The rule (154) is the subject of the tie of the rule with its open variable; here it is listed
    in its class only.
  - Sentences applying a head Γ does not have: no direction (`absent_syms`, `ite_absent`, `account_absent`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieUnbound

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/unbound.kompile.kore"
definition_of defn from "f2-examples/unbound.kompile.kore"
user_axioms U from "f2-examples/unbound.kompile.kore" module "E2-UNBOUND"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-UNBOUND")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 261 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-- `Reordered` keeps the length of each module. -/
theorem reordered_lengths {e k : Kore.Definition} (h : Reordered e k) :
    (e.modules.zip k.modules).all (fun mm => mm.1.sentences.length == mm.2.sentences.length) = true :=
  List.all_eq_true.mpr fun mm hm => beq_iff_eq.mpr (h.2.2 mm hm).2.2.length_eq

theorem lengths_differ :
    (defn.emit.modules.zip kore.modules).all (fun mm => mm.1.sentences.length == mm.2.sentences.length) = false := by
  decide +kernel

theorem user_lengths : (defn.emit.modules.getLast?.map (·.sentences.length), kore.modules.getLast?.map (·.sentences.length)) =
    (some 430, some 402) := by decide +kernel

/-- **`defn` does not print back to the text up to order**, so `Tied kore` fails at its last
conjunct. -/
theorem not_reordered : ¬ Reordered defn.emit kore := fun h => by
  have := reordered_lengths h
  rw [lengths_differ] at this
  exact Bool.false_ne_true this

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))
theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)

/-! ## Function equations (29 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order: the sort predicates' (`isX`'s
plain equation, then its `[owise]` one). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax227, U.ax235, U.ax234, U.ax233, U.ax232, U.ax239, U.ax238, U.ax241, U.ax240, U.ax237,
   U.ax236, U.ax214, U.ax213, U.ax226, U.ax225, U.ax222, U.ax221, U.ax224, U.ax223, U.ax229, U.ax228,
   U.ax231, U.ax230, U.ax218, U.ax217, U.ax220, U.ax219, U.ax216, U.ax215]

/-- Γ's equations are the text's sentences' translations, pattern for pattern. -/
def FnShape : Prop := (fnItems c).map (·.pat) = fnText.map (trS · |>.pat)

theorem fnShape_of_eq (h : ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat)) :
    FnShape := by
  unfold FnShape; rw [fnItems_eq, List.map_map]; exact h

/-- Each of Γ's equations is the translation of its text sentence (kernel). -/
theorem fn_shape : FnShape :=
  fnShape_of_eq (by decide +kernel)

/-- **E for the 29 equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: each item is a text sentence's translation, the j-th's
`fnText[j]`. -/
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

/-! ## No junk of the sorts without constructors (114, 120, 123) -/

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

theorem nj114 : (trS U.ax114).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj120 : (trS U.ax120).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj123 : (trS U.ax123).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for 114, 120, 123**: entailed by Γ (by any theory with definedness), for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax114, U.ax120, U.ax123], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj114]; exact orTopBot_valid hD rfl
  · rw [nj120]; exact orTopBot_valid hD rfl
  · rw [nj123]; exact orTopBot_valid hD rfl

/-- **No junk of the sorts with generators** (115 to 119, 121, 122: Exp and the cells): the
translation of each text sentence is the pattern of one of `Γ`'s constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax115, U.ax116, U.ax117, U.ax118, U.ax119, U.ax121, U.ax122],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

/-- KItem's (124) is the item over KItem's generators in the text's order (`gensInOrder`, the
injections by their source sort's name), the same generators as `Semantics.gens` lists (by sort
number), in another order: `Γ`'s item is the text's disjunction with its disjuncts permuted. -/
theorem nojunk_kitem_order : (trS U.ax124).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel
theorem nojunk_kitem_not_gens_order :
    (c.gens Srt.kitem).map (Gen.toK c) ≠ (gensInOrder c defn.pres Srt.kitem).map (Gen.toK c) := by decide +kernel

/-- **E for 124**: Γ entails KItem's no-junk sentence, for every H. Γ's item is the sentence over
the same generators in another order, and a no-junk item entails the one over any list that holds
its generators (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax124).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax61.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax61).pat = (trAxiom [] [] U.ax61).pat := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The rule leaves a variable open: the definition reads a confined sort, so its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

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
theorem idem_vars : (U.ax61.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax61.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax61.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 61 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax61).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax61.ax.sortVars U.ax61.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax61.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax61.ax.pattern).eraseDups,
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

/-! ## Symbols the text's sentences apply that Γ has no symbol for

The cell initializers and the counter's getter (83, 209 to 212), the projections (248 to 261),
seven hooked symbols' `functional` sentences (36, 40, 42, 73, 75, 112, 113) and two library
sentences (156, 188) apply a symbol that is not among
Γ's symbols (`kernelSyms`): Γ states nothing of it, so no direction holds for these sentences.
The same holds of 100 (`ite{Sort}`'s `functional` sentence, at the sort variable `Sort`) and 242,
243 (`ite{K}`'s two equations): a symbol with sort parameters is one symbol at each instance, and
Γ applies its `ite`, the registry's `kIte` at KItem, at no sort argument (`ite_absent`).
`<<Int` and `>>Int` are symbols of Γ (interpreted hooks), so the sentences over them alone are
not of this kind (`shift_syms`, `account_absent`); nor are the equations of the two bit ranges
(207, 263), also interpreted hooks. -/

theorem absent_syms : ["LblinitKCell", "LblgetGeneratedCounterCell", "Lblproject'Coln'Int",
    "Lbl'UndsAnd-'Int'Unds'"].all (fun n => (kernelSyms c).all (fun k => c.symName k.name != n)) = true := by
  decide +kernel

theorem ite_absent : [U.ax100, U.ax242, U.ax243].all (fun ad =>
      (appHeadsOf ad.ax.pattern).any (fun h => h.1 == "Lblite" && !gammaHasHead c h)) = true ∧
    gammaHasHead c ("Lblite", []) = true := by
  decide +kernel

theorem shift_syms : ["Lbl'Unds-LT--LT-'Int'Unds'", "Lbl'Unds-GT--GT-'Int'Unds'"].all
    (fun n => (kernelSyms c).any (fun k => c.symName k.name == n)) = true := by
  decide +kernel

/-! ## The account: every sentence of the user module is in exactly one class

The classes are those of the tie's directions. The lists are checked for one thing here, that they
partition the 261 sentences; what holds of a class is its own theorem, stated over its list. -/

/-- Per class, the indices (`AxiomDecl.index`) of its sentences.
- function equation: the 29 of `fnText`, equal to Γ's items;
- rewrite rule: 154, the rule with the open variable X;
- priority equation: an equation with `priority(n)` that is not `owise` (none here);
- constructor functional, subsort, injectivity, distinctness, no junk: the constructor sentences;
- function functional: the `functional` sentence of a function of the definition (the 15 sort
  predicates), which Γ does not hold;
- hooked functional: the `functional` sentence of a symbol Γ states by its graph (`freshInt`'s
  among them, 82: the registry interprets it);
- collection law: associativity and the two units of `_List_`, `_Map_`, `_Set_`;
- library: an equation or a lemma of the builtin library over symbols Γ has;
- set idempotence: 61, refuted;
- set-variable lemma: 125 to 129 and 264, listed in their class;
- no direction: a sentence that applies a head Γ does not have (`appHeadsOf`, `gammaHasHead`). -/
def classes : List (String × List Nat) :=
  [("function equation", [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232,
      233, 234, 235, 236, 237, 238, 239, 240, 241]),
   ("rewrite rule", [154]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 77, 80, 104, 105]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 81]),
   ("distinctness", [78]),
   ("no junk", [114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]),
   ("function functional", [85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 56, 64,
      65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 79, 82, 84, 101, 102, 103, 106, 107, 108, 109, 110, 111]),
   ("collection law", [53, 54, 55, 57, 58, 59, 60, 62, 63]),
   ("library", [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
      150, 151, 152, 153, 155, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171,
      172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 189, 190, 191, 192,
      193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 244, 245, 246,
      247, 262, 263]),
   ("set idempotence", [61]),
   ("set-variable lemma", [125, 126, 127, 128, 129, 264]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter lemma", []),
   ("no direction", [36, 40, 42, 73, 75, 83, 100, 112, 113, 156, 188, 209, 210, 211, 212, 242, 243, 248, 249, 250,
      251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261])]

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
    [("function equation", 29), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 8),
     ("subsort", 15), ("injectivity", 5), ("distinctness", 1), ("no junk", 11), ("function functional", 15),
     ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1),
     ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter lemma", 0), ("no direction", 31)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The class lists agree with the lists the class theorems are stated over: the function
equations are `fnText`'s, the rule is 154, the no-junk sentences are the three trivial ones and
the eight over generators, the refuted one is 61, and the set-variable lemmas are six. -/
theorem account_lists : (classOf "function equation").isPerm (fnText.map (·.index)) = true ∧
    classOf "rewrite rule" = [U.ax154.index] ∧
    classOf "no junk" = [U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax119, U.ax120, U.ax121, U.ax122, U.ax123,
      U.ax124].map (·.index) ∧
    classOf "set idempotence" = [U.ax61.index] ∧
    classOf "set-variable lemma" = [U.ax125, U.ax126, U.ax127, U.ax128, U.ax129, U.ax264].map (·.index) := by
  decide +kernel

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

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The sentences of the four classes, in text order. -/
noncomputable def consText : List AxiomDecl := U.all.filter fun ad =>
  (classOf "constructor functional" ++ classOf "subsort" ++ classOf "injectivity" ++ classOf "distinctness").contains
    ad.index

theorem consText_length : consText.length = 29 := by decide +kernel

/-- Each of the 29 is a constructor sentence Γ's constructor items entail (`tieConsB`): for a
constructor sort and generators of it, the sentence has the form of the generator's `functional`
or `subsort` sentence, or of a no-confusion sentence, and `consItemsK c` holds the items it follows
from (Cons-Fun; Cons-Fun and Cons-Inj; two Cons-Fun and Cons-Dist). -/
theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel

/-- None of the 29 reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each of the 29, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

/-! ## The tie's statement definitions on this text

`surplusItem` at two sort constants, `attrsAgree` at the whole text, with the pairing of the
function sentences' priorities. -/

/-- The text declares no sort `Float`, so Γ's sort constant of Float is surplus; it declares `Int`,
whose sort constant is not. -/
theorem surplus_float : surplusItem kore (KoreAML.sortConstantItem (sortDeclOf c Srt.float)) = true ∧
    surplusItem kore (KoreAML.sortConstantItem (sortDeclOf c Srt.int)) = false := by decide +kernel

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation (`fn_shape`), item by item in `fnItems`'s order: `attrsAgree`
compares a function's priorities up to order, this pairs them. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The registry family: a String literal's value item

The text declares no sort `String` and `defn` names none; Γ holds, for each String literal, that
it denotes one element of String. That premise is a member of the registry family at the detached
name `SortString`. -/

def Dstring : KoreAML.Sym → Prop := fun σ => σ = .sort "SortString"

theorem string_undeclared : kore.sortDecls.all (·.name != "SortString") = true := by decide +kernel

/-- No symbol with a signature in `defn`'s own lists (constructors, functions, parameter symbols,
overloading symbols) has String among its sorts. -/
theorem string_unnamed : (c.ctorSigs ++ c.allFns.map Fn.sig ++ c.params.map (·.sig) ++ c.ovlSigs).all
    (fun k => !(k.result :: k.args).contains Srt.string) = true := by decide +kernel

/-- The value item of the String literal `"abc"`. -/
noncomputable def strItem (H : HookParams) : KoreAML.P :=
  KoreAML.sExists ⟨1⟩ (sortP ((cH H).sortName Srt.string)) (den (cH H) (.dv Srt.string (.tok "abc")) ≡ .evar ⟨1⟩)

theorem str_sort (H : HookParams) : (cH H).sortOf (.dv Srt.string (.tok "abc")) = some Srt.string := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- The item is a premise of Γ, for every H. -/
theorem strItem_mem (H : HookParams) : Γ (cH H) (strItem H) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, Srt.string, str_sort H, rfl⟩)))))))

/-- **The item is a `RegistryItem` at the name `SortString`**, for every H. -/
theorem strItem_registry (H : HookParams) : RegistryItem (cH H) Dstring (strItem H) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, Srt.string, ⟨by decide, (by decide +kernel : c.sortName Srt.string = "String") ▸ rfl⟩,
    str_sort H, rfl⟩))))

/-- The item names the detached symbol, so it is not a premise of the theory without the family. -/
theorem strItem_not_own (H : HookParams) : ¬ Γown (cH H) Dstring (strItem H) := fun h =>
  h.2 (.sort "SortString") (by
    have : strItem H = KoreAML.sExists ⟨1⟩ (sortP "String") (den c (.dv Srt.string (.tok "abc")) ≡ .evar ⟨1⟩) := rfl
    rw [this]; decide +kernel) rfl

/-! ## Over `Γc`, the theory the statements are about -/

/-- `Γc` holds every premise of Γ. -/
theorem Γ_sub_Γc (c : Semantics) {φ : P} (h : Γ c φ) : Γc c φ := Or.inl h

/-- What Γ entails, `Γc` entails. -/
theorem entails_c {c : Semantics} {ψ : P} (h : Γ c ⊧ ψ) : Γc c ⊧ ψ :=
  fun hI => h fun φ hφ => hI φ (Γ_sub_Γc c hφ)

theorem fns_entailed_c (H : HookParams) : ∀ ad ∈ fnText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (fns_entailed H ad had)
theorem nojunk_trivial_entailed_c (H : HookParams) :
    ∀ ad ∈ [U.ax114, U.ax120, U.ax123], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax124).pat :=
  entails_c (nojunk_kitem_entailed H)
theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
/-- **Sentence 61 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax61).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieUnbound

open KCore.TieUnbound in
#print axioms wf_defn
open KCore.TieUnbound in
#print axioms not_reordered
#print axioms KCore.TieUnbound.fn_shape
#print axioms KCore.TieUnbound.fns_entailed
#print axioms KCore.TieUnbound.fns_from_text
#print axioms KCore.TieUnbound.nojunk_trivial_entailed
#print axioms KCore.TieUnbound.nojunk_items
#print axioms KCore.TieUnbound.nojunk_kitem_order
#print axioms KCore.TieUnbound.nojunk_kitem_entailed
#print axioms KCore.TieUnbound.idem_refuted
#print axioms KCore.TieUnbound.readsConfined_c
#print axioms KCore.TieUnbound.absent_syms
#print axioms KCore.TieUnbound.ite_absent
#print axioms KCore.TieUnbound.attrs_agree
#print axioms KCore.TieUnbound.fn_prios
#print axioms KCore.TieUnbound.absent_closed
#print axioms KCore.TieUnbound.strItem_registry
#print axioms KCore.TieUnbound.account
#print axioms KCore.TieUnbound.account_absent
#print axioms KCore.TieUnbound.account_lists
#print axioms KCore.TieUnbound.cons_entailed
#print axioms KCore.TieUnbound.fns_entailed_c
#print axioms KCore.TieUnbound.nojunk_trivial_entailed_c
#print axioms KCore.TieUnbound.nojunk_kitem_entailed_c
#print axioms KCore.TieUnbound.cons_entailed_c
#print axioms KCore.TieUnbound.idem_refuted_c
