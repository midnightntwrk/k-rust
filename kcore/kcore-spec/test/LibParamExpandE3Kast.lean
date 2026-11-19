/-
  The sentences of ID-COMMON's `freshId` and `String2Id`, two library symbols Γ lacks, hold
  together at values in one model of Γ whose steps are Step's, on the text of the fixture e3-kast
  (`f2-examples/e3-kast.kompile.kore`: INT and ID imported), for every interpretation H:
  owed-sentence rule item 7, library parameters. Run from the package root:
  `lake env lean -j1 test/LibParamExpandE3Kast.lean`.

  Both are library parameters no rule and no function of the reading applies, so Γ lacks them
  (`lacked_names`; `test/LibEvDeclsE3Kast.lean`): `freshId` (registry symbol 322) and `String2Id`
  (321). The model is the value model with the two names patched (`TieLibParam.model_lacked`),
  their values at values chosen by shape:
  - `String2Id(s)` is the Id token with the characters of the String `s`: the text states nothing
    of it but that it is a function into Id with a value everywhere (its `functional` axiom, 48),
    so any such choice meets its sentences;
  - `freshId(i)` is what `String2Id("_" +String Int2String(i))` has: its defining equation (268,
    domains.md 2299), whose other heads are interpreted hooked symbols.

  `expansion`: Γ has no head under either name, and for every H there is one interpretation
  satisfying `Γc ∪ Γstep` of `c.withHooks H`, whose steps at configurations are `Step`'s, in which
  `freshId`'s equation 268 and the `functional` axioms 110 (`freshId`) and 48 (`String2Id`), each
  as the text's translation writes it, hold at every valuation that sends its free element
  variables to values.

  Not stated here: the expansion condition (E) of owed-sentence rule item 7, that every model of Γ
  extends, possibly gaining elements, to a model of Γ and of these sentences that is elementary for
  Γ's language at the model's elements.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibParamExpandE3Kast

open KCore ML Faithful KoreAML LibEv TieLibParam

kore_term kore from "f2-examples/e3-kast.kompile.kore"
definition_of defn from "f2-examples/e3-kast.kompile.kore"
user_axioms U from "f2-examples/e3-kast.kompile.kore" module "E3-KAST"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The text's translation of a sentence, with its declarations. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem sortOfH (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H (by decide +kernel)
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-! ## `FnHyp` under every H, as the tie has it -/

theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) [] [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-! ## The symbols -/

def freshIdName : String := "LblfreshId'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'Int"
def string2IdName : String := "LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String"

def freshIdSig : CtorSig := ⟨322, [Srt.int], Srt.ident⟩
def string2IdSig : CtorSig := ⟨321, [Srt.string], Srt.ident⟩

/-- The two library symbols: the heads the sentences apply that are no interpreted hooked symbol. -/
def lacked : List CtorSig := [freshIdSig, string2IdSig]

/-- **The two are the registry's library parameters under the names the text declares, Γ lacks
each, and each resolves to no symbol**: each is a parameter of a module of the library with the
signature above, no hook interprets it, the text declares it once, and its name is neither `inj`
nor the name of a head of Γ. -/
theorem lacked_names :
    lacked.all (fun k => (library.any fun m => m.params.any (· == k)) && !isHook k.name &&
      (kore.symbolDecls.filter (·.name == c.symName k.name)).length == 1 &&
      sigNamed c lacked (c.symName k.name) == some k && lackedNameB c (c.symName k.name) &&
      GenEqs.unresolvedB c (c.symName k.name) && (iteSort? (c.symName k.name)).isNone) = true := by
  decide +kernel

theorem names_text : c.symName 322 = freshIdName ∧ c.symName 321 = string2IdName ∧
    lackedNameB c freshIdName = true ∧ lackedNameB c string2IdName = true := by
  decide +kernel

/-! ## The values -/

/-- The Id token with a token's characters. -/
def idOf : GroundTerm → Option GroundTerm
  | .dv _ (.tok t) => some (.dv Srt.ident (.tok t))
  | _ => none

/-- `String2Id` at a String is the Id token with its characters; `freshId(i)` is `String2Id` at
`"_" +String Int2String(i)`. -/
noncomputable def G (H : HookParams) : Sym → List GroundTerm → Option GroundTerm := fun f ws =>
  if f = 321 then
    match ws with
    | [s] => idOf s
    | _ => none
  else if f = 322 then
    match ws with
    | [i] => ((cH H).hv int2String [i]).bind fun s =>
        ((cH H).hv stringConcat [.dv Srt.string (.tok "_"), s]).bind idOf
    | _ => none
  else none

theorem isHook_facts : isHook 322 = false ∧ isHook 321 = false ∧ isHook int2String = true ∧
    isHook stringConcat = true := by
  decide +kernel

/-! ## The equation -/

/-- 268 (domains.md 2299): `freshId(I) => String2Id("_" +String Int2String(I))`. -/
def e268 : FnEqn :=
  ⟨[("VarI", Srt.int)], 322, [(Srt.int, .var 0, none)], Srt.ident, none,
    .app 321 [.app stringConcat [.dv Srt.string (.tok "_"), .app int2String [.var 0]]]⟩

theorem e268_text : U.ax268.ax.pattern = e268.patR ∧ U.ax268.ax.sortVars = [KoreAML.Rv] ∧ e268.regular = true ∧
    e268.typedLk c.sortOf lacked = true ∧ (trS U.ax268).pat = (trAxiom [] [] U.ax268).pat := by
  decide +kernel

theorem fun_text : U.ax110.ax.pattern = funPatR freshIdSig ∧ U.ax110.ax.sortVars = [KoreAML.Rv] ∧
    funReg freshIdSig = true ∧ (trS U.ax110).pat = (trAxiom [] [] U.ax110).pat ∧
    U.ax48.ax.pattern = funPatR string2IdSig ∧ U.ax48.ax.sortVars = [KoreAML.Rv] ∧
    funReg string2IdSig = true ∧ (trS U.ax48).pat = (trAxiom [] [] U.ax48).pat ∧
    sigLk lacked freshIdSig.name = some freshIdSig ∧ sigLk lacked string2IdSig.name = some string2IdSig := by
  decide +kernel

theorem holds268 (H : HookParams) : e268.HoldsLk (cH H) (G H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, -⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, -⟩ := hσ 1 _ rfl
  obtain ⟨hm0, -, -⟩ := hm
  simp only [e268, valLk, List.length_cons, List.length_nil, Nat.zero_add, h0, h1,
    Option.some.injEq] at hm0
  subst hm0
  cases ha : (cH H).hv int2String [v0] with
  | none => simp [e268, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, isHook_facts, G, ha]
  | some s =>
    cases hb : (cH H).hv stringConcat [.dv Srt.string (.tok "_"), s] with
    | none => simp [e268, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, isHook_facts, G, ha, hb]
    | some r => simp [e268, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, isHook_facts, G, ha, hb]

/-! ## The values' sorts -/

theorem ident_tokens : c.lib.carrier Srt.ident = Srt.ident ∧ c.lib.tokenSorts.contains Srt.ident = true := by
  decide +kernel

theorem idOf_sorted (H : HookParams) {s v : GroundTerm} (h : idOf s = some v) :
    (cH H).sortOf v = some Srt.ident := by
  rw [sortOfH]
  unfold idOf at h
  split at h
  · cases h
    have hm : Srt.ident ∈ c.lib.tokenSorts := by simpa using ident_tokens.2
    exact sortOf_dv.mpr ⟨by simp [dvOK, ident_tokens.1, hm], rfl⟩
  · cases h

/-- **`G`'s values at values of a lacked symbol's argument sorts are of its result sort.** -/
theorem G_sorted (H : HookParams) : ∀ k ∈ lacked, ∀ ws, (cH H).sortsOf ws = some k.args → ∀ v,
    G H k.name ws = some v → (cH H).sortOf v = some k.result := by
  intro k hk ws hws v hv
  simp only [lacked, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · obtain ⟨i, rfl⟩ : ∃ i, ws = [i] := by
      match ws, hws with
      | [i], _ => exact ⟨i, rfl⟩
    rw [show G H freshIdSig.name [i] = (((cH H).hv int2String [i]).bind fun s =>
      ((cH H).hv stringConcat [.dv Srt.string (.tok "_"), s]).bind idOf) from rfl] at hv
    obtain ⟨s, -, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨r, -, hv⟩ := Option.bind_eq_some_iff.mp hv
    exact idOf_sorted H hv
  · obtain ⟨s, rfl⟩ : ∃ s, ws = [s] := by
      match ws, hws with
      | [s], _ => exact ⟨s, rfl⟩
    exact idOf_sorted H (show idOf s = some v from hv)

/-! ## The `functional` sentences: `G` has a value at every argument list of the sorts -/

theorem sortsOf1 {d : Semantics} {a : GroundTerm} {s : Srt} : d.sortsOf [a] = some [s] ↔ d.sortOf a = some s := by
  rw [sortsOf_cons]
  constructor
  · rintro ⟨s', ss', h1, h2, he⟩
    rw [sortsOf_nil] at h2
    cases h2
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact h1
  · intro h1
    exact ⟨s, [], h1, sortsOf_nil, rfl⟩

theorem string2Id_total (H : HookParams) : ∀ ws, (cH H).sortsOf ws = some string2IdSig.args →
    ∃ v, G H string2IdSig.name ws = some v := by
  intro ws hws
  obtain ⟨s, rfl⟩ : ∃ s, ws = [s] := by
    have hl := Faithful.sortsOf_length hws
    match ws, hl with
    | [s], _ => exact ⟨s, rfl⟩
    | [], h => simp [string2IdSig] at h
    | _ :: _ :: _, h => simp [string2IdSig] at h
  obtain ⟨t, rfl⟩ := shape_string (shapesOKH H) (sortsOf1.mp hws)
  exact ⟨.dv Srt.ident (.tok t), rfl⟩

theorem freshId_total (H : HookParams) : ∀ ws, (cH H).sortsOf ws = some freshIdSig.args →
    ∃ v, G H freshIdSig.name ws = some v := by
  intro ws hws
  obtain ⟨i, rfl⟩ : ∃ i, ws = [i] := by
    have hl := Faithful.sortsOf_length hws
    match ws, hl with
    | [i], _ => exact ⟨i, rfl⟩
    | [], h => simp [freshIdSig] at h
    | _ :: _ :: _, h => simp [freshIdSig] at h
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) (sortsOf1.mp hws)
  have h1 : hook int2String [int x] = some (some (strV (intRepr x).toList)) := rfl
  obtain ⟨r, h2⟩ : ∃ r, hook stringConcat [.dv Srt.string (.tok "_"), strV (intRepr x).toList] =
      some (some (strV r)) := ⟨_, rfl⟩
  refine ⟨.dv Srt.ident (.tok (String.ofList r)), ?_⟩
  rw [show G H freshIdSig.name [int x] = (((cH H).hv int2String [int x]).bind fun s =>
    ((cH H).hv stringConcat [.dv Srt.string (.tok "_"), s]).bind idOf) from rfl]
  rw [hv_of_value h1]
  simp only [Option.bind_some]
  rw [hv_of_value h2]
  rfl

/-! ## The model -/

theorem lacked_ok (H : HookParams) : ∀ k ∈ lacked, sigNamed (cH H) lacked ((cH H).symName k.name) = some k ∧
    lackedNameB (cH H) ((cH H).symName k.name) = true ∧ GenEqs.unresolvedB (cH H) ((cH H).symName k.name) = true ∧
    iteSort? ((cH H).symName k.name) = none := by
  intro k hk
  have h := List.all_eq_true.mp lacked_names k hk
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **Γ has no head named `freshId` or `String2Id`, and for every H one model of `Γc ∪ Γstep` of
`c.withHooks H`, whose steps at configurations are `Step`'s, holds the library's sentences of the
two at values**: 268 (`freshId`'s equation, domains.md 2299) and the `functional` sentences 110
(`freshId`) and 48 (`String2Id`), each as the text's translation writes it, at every valuation
that sends its free element variables to values. -/
theorem expansion (H : HookParams) :
    lackedNameB c freshIdName = true ∧ lackedNameB c string2IdName = true ∧
    ∃ I : Interpretation KoreAML.Sym Faithful.Model.Elem,
      (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧
      (∀ x y : Config (cH H), Step (cH H) x y ↔ ¬ (I ⊧ᴵ (den (cH H) x.val ⇒ ∼ KoreAML.sNext (den (cH H) y.val)))) ∧
      (∀ e, AtValues (cH H) I e U.ax268.ax → ∀ m, (trS U.ax268).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax110.ax → ∀ m, (trS U.ax110).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax48.ax → ∀ m, (trS U.ax48).pat.interpret I e m) := by
  refine ⟨names_text.2.2.1, names_text.2.2.2, ?_⟩
  obtain ⟨I, hsat, hstep, hL⟩ := model_lacked (cH H) (coreOKH H) (fnHypH H) lacked (G H) (lacked_ok H) (G_sorted H)
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ => hsat φ (Or.inl (Or.inl hφ))
  obtain ⟨p110, sv110, r110, tr110, p48, sv48, r48, tr48, k110, k48⟩ := fun_text
  refine ⟨I, hsat, hstep, ?_, ?_, ?_⟩
  · obtain ⟨hp, hsv, hr, ht, htr⟩ := e268_text
    rw [htr]
    exact FnEqn.entailedLk_reg (coreOKH H) hΓ hL e268 hr (by rw [sortOfH]; exact ht) (holds268 H) U.ax268 hp hsv
  · rw [tr110]
    exact functionalLk (coreOKH H) hΓ hL isHook_facts.1 k110 (freshId_total H) r110 U.ax110 p110 sv110
  · rw [tr48]
    exact functionalLk (coreOKH H) hΓ hL isHook_facts.2.1 k48 (string2Id_total H) r48 U.ax48 p48 sv48

end KCore.LibParamExpandE3Kast

#check @KCore.LibParamExpandE3Kast.expansion
/-- info: 'KCore.LibParamExpandE3Kast.expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibParamExpandE3Kast.expansion
