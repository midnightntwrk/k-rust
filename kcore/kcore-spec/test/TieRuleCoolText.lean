/-
  The tie (C14) on `f2-examples/rulecool.kompile.kore` (fixture e2-rule: `syntax KResult ::= Int`,
  `syntax Exp ::= Int | a(Int) | b(Int) | c(Int)` and nine rules, the `[cool]` and `[heat]` ones
  among them), sentence by sentence, against the translation of the text as written
  (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), stated on the literal `defn` for every
  interpretation H: layer 1, the function equations, the no-junk and constructor sentences, set
  idempotence. The rules (164 to 172) and the steps are test/TieRuleCool.lean's; the
  classes entailed at values and the set-variable lemmas test/TieRuleCoolAtValues.lean's.
  Run from the package root: `lake env lean -j1 test/TieRuleCoolText.lean`.

  The text shares 256 of its 282 user-module sentences with `f2-examples/unbound.kompile.kore`, text
  for text up to Location, Source and UNIQUE_ID attributes; the sections below are
  test/TieUnbound.lean's over this text's indices. The other 26: the subsorts of KResult in KItem
  and of Int in KResult and in Exp (9, 19, 20), the `functional` sentences of `a` and `c` (80, 88),
  their injectivity (81, 89), the three no-confusion sentences of two constructors (82, 83, 87),
  isKResult's `functional` sentence (105), the no junk of Exp, KItem and KResult (124, 133, 134), the
  nine rules (164 to 172), isKResult's two equations (254, 255) and the projection to KResult (279).

  HOLE is left open, so the definition reads a confined sort and its theory is `Γc = Γ ∪ Γcl`
  (`readsConfined_c`). Each statement below is over Γ; `Γc` holds every premise of Γ, so each holds
  over `Γc` as well (`Γ_sub_Γc`, the `_c` forms at the end).

  Layer 1.
  - `wf_defn`: `wf defn = true` (kernel; test/TieRuleCoolWf.lean).
  - `not_reordered` (test/TieRuleCoolWf.lean): `Reordered defn.emit kore` is false: the emitted user module and the text's
    differ in length. So `Tied kore` does not hold, whatever `Parse.parse kore` is.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (31: the sort predicates' `isX` equations): `shape` shows that each of Γ's
    items is the translation of one text sentence (`TiePair.sameB`, a kernel decision), and Γ
    entails each (`fns_entailed`).
  - No junk of Bool, Int, KConfigVar (123, 129, 132): logical truths (`nojunk_trivial_entailed`).
  - No junk of Exp, KResult and the cells (124, 125 to 128, 130, 131, 134): each translation is one
    of Γ's constructor items (`nojunk_items`). KItem's (133) is Γ's item with its disjuncts in the
    text's order (`nojunk_kitem_order`), entailed by Γ for every H (`nojunk_kitem_entailed`).
  - Constructor sentences (`functional` of the constructors, the `subsort` sentences, the
    no-confusion sentences of one and of two constructors): entailed by Γ, for every H
    (`cons_entailed`, test/TieRuleCoolCons.lean).
  - Set idempotence (64): Γ with it has no model, for every H (`idem_refuted`).
  - Sentences applying a symbol Γ does not have: no direction. The account of the 282 sentences
    and the no-direction class are test/TieRuleCoolAccount.lean's (`account`, `account_absent`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCoolText

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"
user_axioms U from "f2-examples/rulecool.kompile.kore" module "E2-RULE"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-RULE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 282 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))
theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)

/-! ## Function equations (31 sentences: the sort predicates', isKResult's 254, 255 among them) -/

noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-! ## No junk of the sorts without constructors (123, 129, 132) -/

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

theorem nj123 : (trS U.ax123).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj129 : (trS U.ax129).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj132 : (trS U.ax132).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for 123, 129, 132**: entailed by Γ (by any theory with definedness), for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax123, U.ax129, U.ax132], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj123]; exact orTopBot_valid hD rfl
  · rw [nj129]; exact orTopBot_valid hD rfl
  · rw [nj132]; exact orTopBot_valid hD rfl

/-- **No junk of the sorts with generators** (124 to 128, 130, 131, 134: Exp, the cells and KResult): the
translation of each text sentence is the pattern of one of `Γ`'s constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax124, U.ax125, U.ax126, U.ax127, U.ax128, U.ax130, U.ax131, U.ax134],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

/-- KItem's (133) is the item over KItem's generators in the text's order (`gensInOrder`, the
injections by their source sort's name), the same generators as `Semantics.gens` lists (by sort
number), in another order: `Γ`'s item is the text's disjunction with its disjuncts permuted. -/
theorem nojunk_kitem_order : (trS U.ax133).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel
theorem nojunk_kitem_not_gens_order :
    (c.gens Srt.kitem).map (Gen.toK c) ≠ (gensInOrder c defn.pres Srt.kitem).map (Gen.toK c) := by decide +kernel

/-- **E for 133**: Γ entails KItem's no-junk sentence, for every H. Γ's item is the sentence over
the same generators in another order, and a no-junk item entails the one over any list that holds
its generators (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax133).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-! ## Set idempotence (64): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax64.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax64).pat = (trAxiom [] [] U.ax64).pat := by decide +kernel

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
    ∀ ad ∈ [U.ax123, U.ax129, U.ax132], Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (nojunk_trivial_entailed H ad had)
theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax133).pat :=
  entails_c (nojunk_kitem_entailed H)
/-- **Sentence 64 is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax64).pat) :=
  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)

end KCore.TieRuleCoolText

#print axioms KCore.TieRuleCoolText.shape
#print axioms KCore.TieRuleCoolText.fns_entailed
#print axioms KCore.TieRuleCoolText.nojunk_trivial_entailed
#print axioms KCore.TieRuleCoolText.nojunk_items
#print axioms KCore.TieRuleCoolText.nojunk_kitem_order
#print axioms KCore.TieRuleCoolText.nojunk_kitem_entailed
#print axioms KCore.TieRuleCoolText.idem_refuted
#print axioms KCore.TieRuleCoolText.readsConfined_c
#print axioms KCore.TieRuleCoolText.strItem_registry
#print axioms KCore.TieRuleCoolText.fns_entailed_c
#print axioms KCore.TieRuleCoolText.nojunk_trivial_entailed_c
#print axioms KCore.TieRuleCoolText.nojunk_kitem_entailed_c
#print axioms KCore.TieRuleCoolText.idem_refuted_c
