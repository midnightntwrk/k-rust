/-
  Row KORE in K: `countAllOccurrences`' second equation (domains.md 1898, sentence 521 of kore.k's
  text as kompile wrote it, `examples/ref-kk/RefKk/definition.kore`, user module `KORE`) at the
  empty needle, in models of Γ, and with the text's `functional` sentence of `countAllOccurrences`
  (sentence 202, `\exists{R}(Val:SortInt{}, \equals{SortInt{}, R}(Val, countAllOccurrences(K0, K1)))`),
  on the generated package's semantics `RefKk.defn.sem` with its `coreOK` (`RefKk.coreOK_defn`).
  Run from the package root with the package built (test/kk-tie-atvalues.sh does both).

  At `Source = ""`, `ToCount = ""` the `requires` `findString("", "", 0) >=Int 0` is `true`, the
  patterns match, the left side is the count c at `("", "")` and the right side `1 +Int c`
  (`substrString("", 0 +Int 0, 0)` is `""`). Hence:
  - `s521_at_of`: for every H under which the count has an Int value at `("", "")`, in every model
    of Γ (cH H) the sentence fails at that valuation.
  - `s521_at`, `s521_refuted`: so for every H meeting `Semantics.silentTotal`, and Γ (cH H) with the
    sentence has no model; `s521_refuted_lib` at `HookParams.lib`.
  - `count202_value`: for every H, in a model of Γ (cH H) where sentence 202 holds, the count has an
    Int value at `("", "")`.
  - `s521_202_refuted`: for every H, Γ (cH H) with sentences 202 and 521 has no model.
  - `s521_none`: where H gives the count no value at `("", "")`, both sides have no value there.
  - `s202_none_refuted`: at `HookParams.none`, which gives the count no value at `("", "")`, Γ with
    sentence 202 has no model.

  So sentence 521 is refuted jointly with sentence 202, a sentence of the same library text.
-/
import RefKk.CoreOK

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKkCountEmpty

open KCore ML Faithful KoreAML LibEv

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := RefKk.defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := RefKk.coreOK_defn
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- **domains.md 1898**: `countAllOccurrences(Source, ToCount) => 1 +Int
countAllOccurrences(substrString(Source, findString(Source, ToCount, 0) +Int lengthString(ToCount),
lengthString(Source)), ToCount) requires findString(Source, ToCount, 0) >=Int 0`. -/
def fnCountRecCe : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToCount", Srt.string)], stringCountAll,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none)], Srt.int,
    some (.app intGe [stFind 0 1, intT 0]),
    .app intAdd [intT 1, .app stringCountAll
      [.app stringSubstr [.var 0, .app intAdd [stFind 0 1, .app stringLength [.var 1]], .app stringLength [.var 0]],
       .var 1]]⟩

/-- The valuation at the empty needle: `Source`, `ToCount`, `X0`, `X1` all `""`. -/
def σCe : Subst := [(0, foS ""), (1, foS ""), (2, foS ""), (3, foS "")]

kernel_rfl patternCe : ∀ H : HookParams, U.ax521.ax.pattern = fnCountRecCe.patternP (cH H)
kernel_rfl typedCe : ∀ H : HookParams, fnCountRecCe.typedPT (cH H) = fnCountRecCe.typedPT c
kernel_rfl vkeyCe_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i
kernel_rfl keysCe_wh : ∀ (H : HookParams) (vars : Vars), keysRPT (cH H) vars = keysRPT c vars

theorem textCe : U.ax521.ax.sortVars = [KoreAML.Rv] ∧ fnCountRecCe.typedPT c = true ∧
    (trS U.ax521).pat = (trAxiom [] [] U.ax521).pat ∧
    (∀ k ∈ KoreAML.freeOf [] U.ax521.ax.pattern, ∃ i, i < fnCountRecCe.av.length ∧ k = vkey c fnCountRecCe.av i) ∧
    ((keysRPT c fnCountRecCe.av).map (KoreAML.tableOf U.ax521.ax.sortVars U.ax521.ax.pattern).idxOf).Nodup := by
  decide +kernel

/-- An interpreted hooked symbol's value in `valP` is `Semantics.hv`'s. -/
theorem appValP_hookedCe {d : Semantics} {f : Sym} (h : (lookupSig hookSigs f).isSome = true)
    (ws : List GroundTerm) : appValP d f ws = d.hv f ws := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  unfold appValP
  rw [hk]

/-- At `σCe` the `requires` is `true`, the patterns match, the left side is the count at
`("", "")` and the right side one more than it. -/
theorem partsCe (d : Semantics) :
    valP d σCe (.app intGe [stFind 0 1, intT 0]) = some (bool true) ∧
    FnEqn.MatchesP d σCe 2 fnCountRecCe.pats ∧
    valP d σCe fnCountRecCe.lhs = d.hv stringCountAll [foS "", foS ""] ∧
    valP d σCe fnCountRecCe.rhs =
      (d.hv stringCountAll [foS "", foS ""]).bind fun k => d.hv intAdd [int 1, k] := by
  have aFind := appValP_hookedCe (d := d) (f := stringFind) (by decide +kernel)
  have aGe := appValP_hookedCe (d := d) (f := intGe) (by decide +kernel)
  have aAdd := appValP_hookedCe (d := d) (f := intAdd) (by decide +kernel)
  have aLen := appValP_hookedCe (d := d) (f := stringLength) (by decide +kernel)
  have aSub := appValP_hookedCe (d := d) (f := stringSubstr) (by decide +kernel)
  have aCnt := appValP_hookedCe (d := d) (f := stringCountAll) (by decide +kernel)
  have hfind : d.hv stringFind [foS "", foS "", int 0] = some (int 0) := by
    rw [st_hv_find0]
    simp [st_occ_nil, KStr.positions, List.range_succ_eq_map, KStr.firstOr]
  have hlen0 : d.hv stringLength [foS ""] = some (int 0) := st_hv_length ""
  have hsub : d.hv stringSubstr [foS "", int 0, int 0] = some (foS "") := by
    rw [st_hv_substr "" 0 0 (by simp) (by simp)]
    simp only [String.toList_empty, List.drop_nil, List.take_nil]
    exact congrArg some (st_foS_strV "")
  have l0 : σCe.lookup 0 = some (foS "") := rfl
  have l1 : σCe.lookup 1 = some (foS "") := rfl
  have l2 : σCe.lookup 2 = some (foS "") := rfl
  have l3 : σCe.lookup 3 = some (foS "") := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [stFind, valP, valPList, allSome, l0, l1, intT, dv_int, aFind, aGe, hfind, fhv_intGe]
  · simp [FnEqn.MatchesP, fnCountRecCe, valP, l0, l1, l2, l3]
  · simp [fnCountRecCe, FnEqn.lhs, FnEqn.xTerms, valP, valPList, allSome, l2, l3, aCnt]
  · simp [fnCountRecCe, stFind, valP, valPList, allSome, l0, l1, intT, dv_int, aFind, aAdd, aLen, aSub,
      aCnt, hfind, hlen0, hv_intAdd, hsub]
    cases d.hv stringCountAll [foS "", foS ""] <;> rfl

/-- Under an interpretation meeting `silentTotal`, where Int values are literals, the count at
`("", "")` is an Int value. -/
theorem totalCe {d : Semantics} (hs : d.shapesOK = true) (ht : d.silentTotal) :
    ∃ n, d.hv stringCountAll [foS "", foS ""] = some (int n) := by
  have hk : lookupSig hookSigs stringCountAll = some ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩ := by
    decide +kernel
  have hmem := (lookupSig_spec hk).1
  have hvs : d.sortsOf [foS "", foS ""] = some [Srt.string, Srt.string] := by
    simp [Semantics.sortsOf, foS, Semantics.sortOf, dvOK]
  have hh : hook stringCountAll [foS "", foS ""] = some none := rfl
  have hsil : silent stringCountAll [foS "", foS ""] = true := rfl
  have hf := ht _ hmem (by decide) _ hvs hh hsil
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hf
  have hws : d.sortOf w = some Srt.int := by
    unfold Semantics.fallback at hw
    rw [hk] at hw
    simp only [Option.filter_eq_some_iff, beq_iff_eq] at hw
    exact hw.2
  obtain ⟨n, rfl⟩ := shape_int hs hws
  refine ⟨n, ?_⟩
  unfold Semantics.hv
  rw [Semantics.hookRes_of_silent hh hsil, hw]
  rfl

/-- **Under every H giving the count an Int value at `("", "")`, in every model of Γ (cH H),
sentence 521 fails at the valuation sending its variables to `""`.** -/
theorem s521_at_of (H : HookParams) (hv : ∃ n, (cH H).hv stringCountAll [foS "", foS ""] = some (int n))
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax521.ax ∧ SetVarsAtValues (cH H) I e U.ax521.ax ∧
      ¬ (trS U.ax521).pat.interpret I e default := by
  rw [textCe.2.2.1]
  obtain ⟨hq, hm, hl, hr⟩ := partsCe (cH H)
  obtain ⟨n, hn⟩ := hv
  refine FnEqn.refutedPT_at (coreOKH H) fnCountRecCe ((typedCe H).trans textCe.2.1) σCe ?_
    (fun q hq' => by cases hq'; exact hq) hm ?_ U.ax521 (patternCe H) textCe.1
    (fun k hk => by simp only [vkeyCe_wh]; exact textCe.2.2.2.1 k hk) (by rw [keysCe_wh]; exact textCe.2.2.2.2) hI
  · intro i p hp
    have hs : (cH H).sortOf (foS "") = some Srt.string := by simp [foS, Semantics.sortOf, dvOK]
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, hs⟩
    | 1, hp => cases hp; exact ⟨_, rfl, hs⟩
    | 2, hp => cases hp; exact ⟨_, rfl, hs⟩
    | 3, hp => cases hp; exact ⟨_, rfl, hs⟩
  · rw [hl, hr, hn, Option.bind_some, hv_intAdd]
    intro he
    have : n = 1 + n := by simpa [int] using he
    omega

/-- **Under every H meeting `silentTotal`, in every model of Γ (cH H), sentence 521 fails at the
valuation sending its variables to `""`.** -/
theorem s521_at (H : HookParams) (ht : (cH H).silentTotal) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax521.ax ∧ SetVarsAtValues (cH H) I e U.ax521.ax ∧
      ¬ (trS U.ax521).pat.interpret I e default :=
  s521_at_of H (totalCe (shapesOKH H) ht) hI

/-- **Γ (cH H) with sentence 521 has no model, for every H meeting `silentTotal`.** -/
theorem s521_refuted (H : HookParams) (ht : (cH H).silentTotal) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax521).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := s521_at H ht hI
  exact hn (hax e default)

theorem s521_refuted_lib : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH HookParams.lib) → ¬ (I ⊧ᴵ (trS U.ax521).pat) :=
  s521_refuted HookParams.lib (silentTotal_of_libAdmitted (libAdmitted_lib_of_coreOK coreOK))

/-- Where the interpretation gives the count no value at `("", "")`, both sides have none there. -/
theorem s521_none (H : HookParams) (h : (cH H).hv stringCountAll [foS "", foS ""] = none) :
    valP (cH H) σCe fnCountRecCe.lhs = valP (cH H) σCe fnCountRecCe.rhs := by
  obtain ⟨-, -, hl, hr⟩ := partsCe (cH H)
  rw [hl, hr, h]; rfl

/-! ## Sentence 202 -/

/-- `countAllOccurrences`' signature in the registry. -/
def kCe : CtorSig := ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩

kernel_rfl pattern202 : U.ax202.ax.pattern = LibEv.funPatR kCe

/-- Sentence 202 as `LibEv.functional_ev` reads such a sentence: one sort variable `R`, the
registry's names, `trS` the translation over no declarations, free variables `K0` and `K1`, and
places in its table apart for `R`, `K0`, `K1` and the bound `Val`. -/
theorem text202 : U.ax202.ax.sortVars = [KoreAML.Rv] ∧ LibEv.funReg kCe = true ∧
    (trS U.ax202).pat = (trAxiom [] [] U.ax202).pat ∧
    (U.ax202.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax202.ax.pattern).eraseDups =
      [.sortVar "R", .evar "K0" (regSrtK Srt.string), .evar "K1" (regSrtK Srt.string)] ∧
    (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "K0" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.sortVar "R") ∧
    (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "K1" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.sortVar "R") ∧
    (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "K0" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "Val" (regSrtK Srt.int)) ∧
    (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "K1" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "Val" (regSrtK Srt.int)) ∧
    (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.sortVar "R") ≠
      (KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern).ev (.evar "Val" (regSrtK Srt.int)) := by
  decide +kernel

/-- `K0` and `K1` both at `""`. -/
def σ202 : Subst := [(0, foS ""), (1, foS "")]

/-- **In a model of Γ (cH H) where sentence 202 holds, the count has an Int value at `("", "")`,
for every H.** -/
theorem count202_value (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (h202 : I ⊧ᴵ (trS U.ax202).pat) :
    ∃ n, (cH H).hv stringCountAll [foS "", foS ""] = some (int n) := by
  have h := coreOKH H
  haveI : OvlOK (cH H) := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨hsv, hreg, htr, hfree, hK0R, hK1R, hK0V, hK1V, hRV⟩ := text202
  have hk : kCe ∈ hookSigs :=
    (lookupSig_spec (show lookupSig hookSigs stringCountAll = some kCe by decide +kernel)).1
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + (cH H).sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨τI, hτIsort, hτI⟩ := srt_den hI (hnum (show Srt.int < nRegSorts by decide))
  obtain ⟨τS, -, hτS⟩ := srt_den hI (hnum (show Srt.string < nRegSorts by decide))
  have hsS : srtOf (cH H) Srt.string = regSrtK Srt.string := srtOf_reg _ (by decide)
  have hsI : srtOf (cH H) Srt.int = regSrtK Srt.int := srtOf_reg _ (by decide)
  have hsE : (cH H).sortOf (foS "") = some Srt.string := by simp [foS, Semantics.sortOf, dvOK]
  have hsZ : (cH H).sortOf (int 0) = some Srt.int := by simp [int, Semantics.sortOf, dvOK]
  -- the translated sentence at a valuation meeting its guards
  have h202' : I ⊧ᴵ (KoreAML.trAxiom [] [] U.ax202).pat := htr ▸ h202
  have hA := KoreAML.trAxiom_at hD h202'
  rw [hfree] at hA
  generalize KoreAML.tableOf U.ax202.ax.sortVars U.ax202.ax.pattern = t at hA hK0R hK1R hK0V hK1V hRV
  rw [pattern202, ← LibEv.funPat_reg (cH H) hreg] at hA
  unfold LibEv.funPat at hA
  simp only [KoreAML.sortOf] at hA
  -- the valuation: `R` at Int's sort, every other variable at the element of `""`
  let e0 : Valuation M :=
    ⟨fun x => if x = t.ev (.sortVar "R") then τI else elemOf (cH H) I (foS ""), fun _ _ => False⟩
  have he0R : e0.evalEvar (t.ev (.sortVar "R")) = τI := by simp [e0]
  have he0K0 : e0.evalEvar (t.ev (.evar "K0" (regSrtK Srt.string))) = elemOf (cH H) I (foS "") := by simp [e0, hK0R]
  have he0K1 : e0.evalEvar (t.ev (.evar "K1" (regSrtK Srt.string))) = elemOf (cH H) I (foS "") := by simp [e0, hK1R]
  have hinhE : KoreAML.Inh I τS (elemOf (cH H) I (foS "")) := by
    obtain ⟨-, hw2⟩ := elemOf_spec hI hsE e0
    refine (KoreAML.interp_inhOf_of (fun a => ?_)).mp hw2
    have := hτS t e0 a
    rwa [trSort_srtOf_twoT] at this
  have hinhZ : KoreAML.Inh I τI (elemOf (cH H) I (int 0)) := by
    obtain ⟨-, hw2⟩ := elemOf_spec hI hsZ e0
    refine (KoreAML.interp_inhOf_of (fun a => ?_)).mp hw2
    have := hτI t e0 a
    rwa [trSort_srtOf_twoT] at this
  have hg : ∀ k ∈ [KoreAML.VarKey.sortVar "R", .evar "K0" (regSrtK Srt.string), .evar "K1" (regSrtK Srt.string)],
      ∀ m, (KoreAML.guardOf t k).interpret I e0 m := by
    intro k hk' m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl | rfl
    · rw [KoreAML.interp_guard_sortVar hD, he0R]; exact hτIsort
    · rw [KoreAML.interp_guard_evar hD, he0K0, ← hsS, KoreAML.interp_inhOf_of (hτS t e0)]; exact hinhE
    · rw [KoreAML.interp_guard_evar hD, he0K1, ← hsS, KoreAML.interp_inhOf_of (hτS t e0)]; exact hinhE
  have hRv0 : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e0 b ↔ b = τI :=
    fun b => by rw [trSort_R, KoreAML.interp_evar, he0R]
  have hex := (hA e0 hg (elemOf (cH H) I (int 0))).mpr ((KoreAML.interp_inhOf_of hRv0).mpr hinhZ)
  rw [KoreAML.tr, KoreAML.interp_sExists] at hex
  obtain ⟨x, hxm, hx⟩ := hex
  -- under the binder
  let ex : Valuation M := ⟨Function.update e0.evalEvar (t.ev (LibEv.valKey (srtOf (cH H) kCe.result))) x, e0.evalSvar⟩
  have hVk : t.ev (LibEv.valKey (srtOf (cH H) kCe.result)) = t.ev (.evar "Val" (regSrtK Srt.int)) := by
    show t.ev (.evar "Val" (srtOf (cH H) Srt.int)) = _
    rw [hsI]
  have hexR : ex.evalEvar (t.ev (.sortVar "R")) = τI := by
    show Function.update e0.evalEvar _ x _ = _
    rw [hVk, Function.update_noteq hRV, he0R]
  have hexK0 : ex.evalEvar (t.ev (.evar "K0" (regSrtK Srt.string))) = elemOf (cH H) I (foS "") := by
    show Function.update e0.evalEvar _ x _ = _
    rw [hVk, Function.update_noteq hK0V, he0K0]
  have hexK1 : ex.evalEvar (t.ev (.evar "K1" (regSrtK Srt.string))) = elemOf (cH H) I (foS "") := by
    show Function.update e0.evalEvar _ x _ = _
    rw [hVk, Function.update_noteq hK1V, he0K1]
  have hexV : ex.evalEvar (t.ev (LibEv.valKey (srtOf (cH H) kCe.result))) = x := Function.update_same _ _ _
  -- the application at `K0`, `K1` denotes the value of the count at `("", "")`
  have hσ : ∀ i p, (LibEv.funVars kCe)[i]? = some p →
      ∃ v, σ202.lookup i = some v ∧ (cH H).sortOf v = some p.2 := by
    intro i p hp
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, hsE⟩
    | 1, hp => cases hp; exact ⟨_, rfl, hsE⟩
    | _ + 2, hp => simp [LibEv.funVars, LibEv.funVarsFrom, kCe] at hp
  have hag : ∀ i v, i < (LibEv.funVars kCe).length → σ202.lookup i = some v →
      ∀ m, m = ex.evalEvar (t.ev (vkey (cH H) (LibEv.funVars kCe) i)) ↔ (den (cH H) v).interpret I ex m := by
    intro i v hi hv m
    match i, hi, hv with
    | 0, _, hv =>
      cases hv
      have hk0 : vkey (cH H) (LibEv.funVars kCe) 0 = .evar "K0" (regSrtK Srt.string) := by
        show KoreAML.VarKey.evar "K0" (srtOf (cH H) Srt.string) = _
        rw [hsS]
      rw [hk0, hexK0]
      exact ((elemOf_spec hI hsE ex).1 m).symm
    | 1, _, hv =>
      cases hv
      have hk1 : vkey (cH H) (LibEv.funVars kCe) 1 = .evar "K1" (regSrtK Srt.string) := by
        show KoreAML.VarKey.evar "K1" (srtOf (cH H) Srt.string) = _
        rw [hsS]
      rw [hk1, hexK1]
      exact ((elemOf_spec hI hsE ex).1 m).symm
    | n + 2, hi, _ => exact absurd hi (by rw [LibEv.funVars_length kCe]; show ¬ (n + 2 < 2); omega)
  have hlen := LibEv.funVars_length kCe
  have hsrts : LibEv.srts? (cH H) (LibEv.funVars kCe) (LibEv.argVars 0 kCe.args.length) = some kCe.args := by
    rw [LibEv.srts_argVars (cH H) (LibEv.funVars kCe) kCe.args.length 0 (by omega), List.drop_zero]
    exact congrArg some (LibEv.funVarsFrom_sorts 0 kCe.args)
  have hsrt : LibEv.srt? (cH H) (LibEv.funVars kCe) (LibEv.funTerm kCe) = some kCe.result := by
    unfold LibEv.funTerm
    rw [LibEv.srt?, hookSigs_lookup kCe hk]
    simp only [Option.bind_some, hsrts, beq_self_eq_true, ite_true]
  have hDV := LibEv.den_val (tbl := t) (e := ex) h hI hσ hag (LibEv.funTerm kCe) hsrt
  have hval : LibEv.val (cH H) σ202 (LibEv.funTerm kCe) = (cH H).hv stringCountAll [foS "", foS ""] := rfl
  -- sentence 202 at `x`: `Val`, which is `x`, is the application
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I ex b ↔ b = τI :=
    fun b => by rw [trSort_R, KoreAML.interp_evar, hexR]
  have hx' : (KoreAML.sEquals (KoreAML.trSort t (srtOf (cH H) Srt.int)) (KoreAML.trSort t KoreAML.R)
      (KoreAML.tr ⟨t, []⟩ (.var (.evar (KoreAML.evar "Val" (srtOf (cH H) kCe.result)))))
      (KoreAML.tr ⟨t, []⟩ (LibEv.kore (cH H) (LibEv.funVars kCe) (LibEv.funTerm kCe)))).interpret I
      ex (elemOf (cH H) I (int 0)) := by
    rw [KoreAML.tr] at hx
    exact hx
  rw [KoreAML.interp_sEquals hD hc (hτI t ex) hRv hτIsort hτIsort] at hx'
  have hxI : KoreAML.Inh I τI x := by
    rw [KoreAML.interp_member hD] at hxm
    have hxm' : (KoreAML.inhOf (KoreAML.trSort t (srtOf (cH H) Srt.int))).interpret I ex (ex.evalEvar
        (t.ev (LibEv.valKey (srtOf (cH H) kCe.result)))) := hxm
    rw [hexV, KoreAML.interp_inhOf_of (hτI t ex)] at hxm'
    exact hxm'
  have happ := (hx'.2 x hxI).mp (by
    rw [KoreAML.tr]
    show x = ex.evalEvar (t.ev (LibEv.valKey (srtOf (cH H) kCe.result)))
    rw [hexV])
  rw [hDV.1 x, hval] at happ
  cases hw : (cH H).hv stringCountAll [foS "", foS ""] with
  | none => rw [hw] at happ; exact happ.elim
  | some w =>
    have hws : (cH H).sortOf w = some Srt.int := hDV.2 w (hval.trans hw)
    obtain ⟨n, rfl⟩ := shape_int (shapesOKH H) hws
    exact ⟨n, rfl⟩

/-- **For every H, Γ (cH H) with sentences 202 and 521 has no model**: sentence 202 gives the count
a value at `("", "")`, where sentence 521 fails. -/
theorem s521_202_refuted (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → I ⊧ᴵ (trS U.ax202).pat → ¬ (I ⊧ᴵ (trS U.ax521).pat) := by
  intro M _ I hI h202 hax
  obtain ⟨e, -, -, hn⟩ := s521_at_of H (count202_value H hI h202) hI
  exact hn (hax e default)

/-- **At `HookParams.none`, Γ with sentence 202 has no model**: the interpretation gives the count
no value at `("", "")`, a silent point, and sentence 202 asks one there (`count202_value`). -/
theorem s202_none_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH HookParams.none) → ¬ (I ⊧ᴵ (trS U.ax202).pat) := by
  intro M _ I hI h202
  obtain ⟨n, hn⟩ := count202_value HookParams.none hI h202
  have h0 : (cH HookParams.none).hv stringCountAll [foS "", foS ""] = none := by decide +kernel
  rw [h0] at hn
  cases hn

/-- The sentence of the library class refuted here. -/
theorem s521_indices : [U.ax521].map (·.index) = [521] := by decide +kernel

end KCore.TieKkCountEmpty

/-- info: 'KCore.TieKkCountEmpty.s521_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkCountEmpty.s521_refuted
/-- info: 'KCore.TieKkCountEmpty.s521_refuted_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkCountEmpty.s521_refuted_lib
/-- info: 'KCore.TieKkCountEmpty.s521_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkCountEmpty.s521_none
/-- info: 'KCore.TieKkCountEmpty.count202_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkCountEmpty.count202_value
/-- info: 'KCore.TieKkCountEmpty.s521_202_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkCountEmpty.s521_202_refuted
#check @KCore.TieKkCountEmpty.s521_indices
/-- info: 'KCore.TieKkCountEmpty.s202_none_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkCountEmpty.s202_none_refuted
