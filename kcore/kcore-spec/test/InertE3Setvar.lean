/-
  The C2 evidence of the inert simplification over a set variable on the fixture e3-setvar:
  `rule f(X) => X` beside `rule f(@S) => @S [simplification]`, `f(Int)` a function.
  The text is `f2-examples/e3-setvar.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/e3-setvar/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/InertE3Setvar.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `lem_class`: the reader leaves the simplification (axiom 200) inert, class `simplification`;
    `lem_text`: its pattern is
    `\implies{R}(\top{R}(), \equals{SortInt{}, R}(f(@VarS), \and{SortInt{}}(@VarS, \top{SortInt{}}())))`.
  - `eq_text`, `eq_entailed`: f's equation (axiom 201), `X0 ∈ VarX → f(X0) = VarX` over element
    variables of sort Int, is entailed by Γ for every H: Γ's item of f's clause is its translation
    (`shape`, `TiePair.entailed`).
  - `eqn_at`: so in a model of Γ, at every inhabitant x of Int, `f` applied to x holds, among the
    inhabitants of Int, exactly x.
  - `lem_entailed`: **Γ entails the simplification, for every H, at every valuation**. Its guard
    puts `@VarS` inside the inhabitants of Int; application is pointwise, so `f(@VarS)` holds, among
    the inhabitants of Int, the union of `f` at each element of `@VarS`, which is `@VarS`; and so does
    `\and{SortInt{}}(@VarS, \top{SortInt{}}())`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertE3Setvar

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-setvar.kompile.kore"
definition_of defn from "f2-examples/e3-setvar.kompile.kore"
user_axioms U from "f2-examples/e3-setvar.kompile.kore" module "E3-SETVAR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The two sentences -/

def sInt : Kore.KSort := .ctor ⟨⟨"SortInt"⟩⟩ []
def fId : Kore.SymbolIdent := ⟨⟨"Lblf"⟩⟩
def x0 : Kore.EVar := ⟨⟨⟨"X0"⟩⟩, sInt⟩
def vX : Kore.EVar := ⟨⟨⟨"VarX"⟩⟩, sInt⟩
def vS : Kore.SVar := ⟨⟨⟨"VarS"⟩⟩, sInt⟩

/-- f's equation as kompile writes it. -/
def eqPat : Kore.Pattern :=
  .implies R (.and R [.top R, .and R [.in sInt R (.var (.evar x0)) (.var (.evar vX)), .top R]])
    (.equals sInt R (.app fId [] [.var (.evar x0)]) (.and sInt [.var (.evar vX), .top sInt]))

/-- The simplification. -/
def lemPat : Kore.Pattern :=
  .implies R (.top R) (.equals sInt R (.app fId [] [.var (.svar vS)]) (.and sInt [.var (.svar vS), .top sInt]))

noncomputable abbrev lemAx : AxiomDecl := U.ax200
noncomputable abbrev eqAx : AxiomDecl := U.ax201

/-- The reader's class of the simplification. -/
theorem lem_class : Parse.classifyShape (.axiom lemAx.ax) = .inert .simplification := by decide +kernel

theorem lem_text : lemAx.ax.pattern = lemPat ∧ lemAx.ax.sortVars = [Rv] ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat := by
  decide +kernel

theorem eq_text : eqAx.ax.pattern = eqPat ∧ eqAx.ax.sortVars = [Rv] ∧
    (trS eqAx).pat = (trAxiom [] [] eqAx).pat := by
  decide +kernel

/-- The free variables of each sentence after its sort variable, and the table's elements of f's
equation: `R` is neither `X0` nor `VarX`. -/
theorem tables : ([Rv].map sortVarKey ++ freeOf [] eqPat).eraseDups = [.sortVar "R", evarKey x0, evarKey vX] ∧
    (tableOf [Rv] eqPat).ev (.sortVar "R") ≠ (tableOf [Rv] eqPat).ev (evarKey x0) ∧
    (tableOf [Rv] eqPat).ev (.sortVar "R") ≠ (tableOf [Rv] eqPat).ev (evarKey vX) ∧
    ([Rv].map sortVarKey ++ freeOf [] lemPat).eraseDups = [.sortVar "R", svarKey vS] := by
  decide +kernel

theorem sortName_int (H : HookParams) : "Sort" ++ (cH H).sortName Srt.int = "SortInt" := by
  show "Sort" ++ c.sortName Srt.int = "SortInt"; decide +kernel

/-! ## f's equation is entailed -/

noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

theorem eq_mem : (trS eqAx).pat ∈ textPats := by decide +kernel

/-- **Γ entails f's equation**, for every H. -/
theorem eq_entailed (H : HookParams) : Γ (cH H) ⊧ (trS eqAx).pat :=
  TiePair.entailed (shapeH H) _ eq_mem

/-! ## In a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem trSort_sInt (t : VarTable) : trSort t sInt = sym (.sort "SortInt") := rfl

theorem trSort_R' (t : VarTable) : trSort t R = .evar (t.ev (.sortVar "R")) := rfl

theorem R_topFresh (t : VarTable) : (trSort t R).isFreeEvar topVar = false := by
  rw [trSort_R']; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm

theorem sInt_topFresh (t : VarTable) : (trSort t sInt).isFreeEvar topVar = false := by
  rw [trSort_sInt]; rfl

/-- **f at an inhabitant of Int**: in a model of Γ, where `Int` is the sort `σI`, `f` applied to
an inhabitant x of it holds, among its inhabitants, exactly x. -/
theorem eqn_at (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) {σI : M} (hsI : IsSort I σI)
    (hσI : ∀ (e : Valuation M) a, (sym (.sort "SortInt") : P).interpret I e a ↔ a = σI)
    {x : M} (hx : Inh I σI x) {b : M} (hb : Inh I σI b) :
    (∃ a, I.evalSymb (.symbol "Lblf") a ∧ I.evalApp a x b) ↔ b = x := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨hp, hsv, htr⟩ := eq_text
  obtain ⟨hfree, hne1, hne2, -⟩ := tables
  have hF : I ⊧ᴵ (trAxiom [] [] eqAx).pat := htr ▸ eq_entailed H hI
  generalize eqAx = ad at hp hsv hF
  obtain ⟨i, mo, ⟨sv, pat, att⟩⟩ := ad
  dsimp only at hp hsv
  subst hp hsv
  let e' : Valuation M := ⟨fun v => if v = (tableOf [Rv] eqPat).ev (.sortVar "R") then σI else x, fun _ _ => False⟩
  have heR : e'.evalEvar ((tableOf [Rv] eqPat).ev (.sortVar "R")) = σI :=
    show (if (tableOf [Rv] eqPat).ev (.sortVar "R") = (tableOf [Rv] eqPat).ev (.sortVar "R") then σI else x) = σI
    from if_pos rfl
  have heX0 : e'.evalEvar ((tableOf [Rv] eqPat).ev (evarKey x0)) = x :=
    show (if (tableOf [Rv] eqPat).ev (evarKey x0) = (tableOf [Rv] eqPat).ev (.sortVar "R") then σI else x) = x
    from if_neg (fun h => hne1 h.symm)
  have heVX : e'.evalEvar ((tableOf [Rv] eqPat).ev (evarKey vX)) = x :=
    show (if (tableOf [Rv] eqPat).ev (evarKey vX) = (tableOf [Rv] eqPat).ev (.sortVar "R") then σI else x) = x
    from if_neg (fun h => hne2 h.symm)
  have hRv : ∀ a, (trSort (tableOf [Rv] eqPat) R).interpret I e' a ↔ a = σI := fun a => by
    rw [trSort_R', KoreAML.interp_evar, heR]
  have hIv : ∀ a, (trSort (tableOf [Rv] eqPat) sInt).interpret I e' a ↔ a = σI := fun a => by
    rw [trSort_sInt]; exact hσI e' a
  have hg : ∀ k ∈ ([Rv].map sortVarKey ++ freeOf [] eqPat).eraseDups, ∀ m,
      (guardOf (tableOf [Rv] eqPat) k).interpret I e' m := by
    rw [hfree]
    intro k hk m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · rw [KoreAML.interp_guard_sortVar hD, heR]; exact hsI
    · show (guardOf _ (.evar x0.var.ident.name x0.sort)).interpret I e' m
      rw [KoreAML.interp_guard_evar hD]
      show (inhOf (trSort _ sInt)).interpret I e' (e'.evalEvar ((tableOf [Rv] eqPat).ev (evarKey x0)))
      rw [heX0, KoreAML.interp_inhOf_of hIv]; exact hx
    · show (guardOf _ (.evar vX.var.ident.name vX.sort)).interpret I e' m
      rw [KoreAML.interp_guard_evar hD]
      show (inhOf (trSort _ sInt)).interpret I e' (e'.evalEvar ((tableOf [Rv] eqPat).ev (evarKey vX)))
      rw [heVX, KoreAML.interp_inhOf_of hIv]; exact hx
  have h2 := trAxiom_at hD hF e' hg x
  dsimp only at h2
  simp only [KoreAML.sortOf] at h2
  have hL := h2.mpr ((KoreAML.interp_inhOf_of hRv).mpr hx)
  have hX0 : ∀ a, (Pattern.evar ((tableOf [Rv] eqPat).ev (evarKey x0)) : P).interpret I e' a ↔ a = x :=
    fun a => by rw [KoreAML.interp_evar]; exact iff_of_eq (congrArg (a = ·) heX0)
  have hVX : ∀ a, (Pattern.evar ((tableOf [Rv] eqPat).ev (evarKey vX)) : P).interpret I e' a ↔ a = x :=
    fun a => by rw [KoreAML.interp_evar]; exact iff_of_eq (congrArg (a = ·) heVX)
  generalize tableOf [Rv] eqPat = T at hL hRv hIv hX0 hVX
  simp only [eqPat, fId, KoreAML.tr, KoreAML.trAndList, KoreAML.trArgs, KoreAML.trSortApp, List.contains_nil,
    Bool.false_eq_true, ↓reduceIte] at hL
  rw [KoreAML.interp_sImp] at hL
  have hprem := hL.2 (by
    rw [KoreAML.interp_sAnd, KoreAML.interp_sTop hD (R_topFresh _), KoreAML.interp_inhOf_of hRv,
      KoreAML.interp_sAnd, KoreAML.interp_sIn hD hc hIv hRv hsI hsI
        (fun a ha => by rw [(hX0 a).mp ha]; exact hx)]
    exact ⟨hx, ⟨⟨x, (hX0 x).mpr rfl, (hVX x).mpr rfl⟩, hx⟩,
      by rw [KoreAML.interp_sTop hD (R_topFresh _), KoreAML.interp_inhOf_of hRv]; exact hx⟩)
  rw [KoreAML.interp_sEquals hD hc hIv hRv hsI hsI] at hprem
  have hb' := hprem.2 b hb
  rw [KoreAML.interp_app, KoreAML.interp_sAnd, KoreAML.interp_sTop hD (sInt_topFresh _),
    KoreAML.interp_inhOf_of hIv, hVX] at hb'
  constructor
  · rintro ⟨a, ha, hab⟩
    exact (hb'.mp ⟨a, x, ha, (hX0 x).mpr rfl, hab⟩).1
  · intro hbx
    obtain ⟨a, y, ha, hy, hab⟩ := hb'.mpr ⟨hbx, hb⟩
    rw [(hX0 y).mp hy] at hab
    exact ⟨a, ha, hab⟩

/-- **The simplification holds** in every model of Γ, for every H, at every valuation. -/
theorem lem_holds (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) : I ⊧ᴵ (trAxiom [] [] lemAx).pat := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σI, hsI, hσ⟩ := srt_den hI (s := Srt.int)
    (Nat.lt_of_lt_of_le (by decide +kernel : Srt.int < nRegSorts) (Nat.le_add_right _ _))
  have hσI : ∀ (e : Valuation M) a, (sym (.sort "SortInt") : P).interpret I e a ↔ a = σI := fun e a => by
    have := hσ [] e a
    rwa [trSort_srtOf_twoT, sortName_int] at this
  obtain ⟨hp, hsv, -⟩ := lem_text
  obtain ⟨-, -, -, hfree⟩ := tables
  generalize lemAx = ad at hp hsv
  obtain ⟨i, mo, ⟨sv, pat, att⟩⟩ := ad
  dsimp only at hp hsv
  subst hp hsv
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  rw [interpret_impl]
  intro hgd
  generalize htb : tableOf [Rv] lemPat = t at hgd
  have hR : IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R", by
      rw [hfree]; exact List.mem_cons_self .., rfl⟩))
  have hSg := conjList_mem hgd _ (List.mem_map.mpr ⟨svarKey vS, by
      rw [hfree]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩)
  have hS : ∀ y, e.evalSvar (t.sv (svarKey vS)) y → Inh I σI y := by
    intro y hy
    have := (KoreAML.interp_included hD).mp hSg y hy
    change (inhOf (trSort t sInt)).interpret I e y at this
    rwa [KoreAML.interp_inhOf_of (fun a => by rw [trSort_sInt]; exact hσI e a)] at this
  have hRv : ∀ b, (trSort t R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R', KoreAML.interp_evar]
  have hIv : ∀ a, (trSort t sInt).interpret I e a ↔ a = σI := fun a => by
    rw [trSort_sInt]; exact hσI e a
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [lemPat, KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hIv hRv hsI hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [tr_app0]
    simp only [KoreAML.tr, KoreAML.trArgs, KoreAML.trAndList]
    rw [KoreAML.interp_app, KoreAML.interp_sAnd, KoreAML.interp_sTop hD (sInt_topFresh _),
      KoreAML.interp_inhOf_of hIv]
    show (∃ f' y, _ ∧ e.evalSvar (t.sv (svarKey vS)) y ∧ _) ↔ e.evalSvar (t.sv (svarKey vS)) b ∧ _
    constructor
    · rintro ⟨f', y, hf, hy, hfy⟩
      have hby := (eqn_at H hI hsI hσI (hS y hy) hb).mp ⟨f', hf, hfy⟩
      subst hby
      exact ⟨hy, hb⟩
    · rintro ⟨hbS, -⟩
      obtain ⟨f', hf, hfb⟩ := (eqn_at H hI hsI hσI (hS b hbS) hb).mpr rfl
      exact ⟨f', b, hf, hbS, hfb⟩

end

/-- **Γ entails the simplification, for every H** (class user lemma: at every valuation). -/
theorem lem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS lemAx).pat := by
  rw [lem_text.2.2]
  intro M _ I hI
  exact lem_holds H hI

end KCore.InertE3Setvar

#check @KCore.InertE3Setvar.lem_entailed
#print axioms KCore.InertE3Setvar.lem_class
#print axioms KCore.InertE3Setvar.lem_text
#print axioms KCore.InertE3Setvar.eq_entailed
#print axioms KCore.InertE3Setvar.eqn_at
#print axioms KCore.InertE3Setvar.lem_entailed
