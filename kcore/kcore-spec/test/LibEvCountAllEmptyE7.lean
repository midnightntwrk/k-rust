/-
  `countAllOccurrences`' second equation (domains.md 1898, sentence 243 of
  `f2-examples/e7-constfold.kompile.kore`) with the text's `functional` sentence of
  `countAllOccurrences` (sentence 98, `\exists{R}(Val:SortInt{}, \equals{SortInt{}, R}(Val,
  countAllOccurrences(K0, K1)))`), on a text whose Γ has a model for every H.
  Run from the package root: `lake env lean -j1 test/LibEvCountAllEmptyE7.lean`.

  At `Source = ""`, `ToCount = ""` the `requires` `findString("", "", 0) >=Int 0` is `true`, the
  patterns match, the left side is the count c at `("", "")` and the right side `1 +Int c`
  (`substrString("", 0 +Int 0, 0)` is `""`). Hence:
  - `s243_at_of`: for every H under which the count has an Int value at `("", "")`, in every model
    of Γ (cH H) sentence 243 fails at that valuation.
  - `count98_value`: for every H, in a model of Γ (cH H) where sentence 98 holds, the count has an
    Int value at `("", "")` (Γ's graph there is H's value of Int sort, and ⊥ where H gives none).
  - `s98_refuted_of_none`: for every H that gives the count no value at `("", "")`, Γ (cH H) with
    sentence 98 has no model.
  - `s243_98_refuted`: for every H, Γ (cH H) with sentences 98 and 243 has no model.
  - `consistent`: Γ with the step's closure has a model, for every H (the text owes no fact).
  - `s243_98_refuted_consistent`: for every H, Γ (cH H) has a model and no model of it satisfies
    sentences 98 and 243, so the refutation is of the two sentences against Γ, not a consequence
    of Γ having no model.
  The premises beside the two sentences are Γ's: the graphs of `STRING.find`, `STRING.length`,
  `STRING.substr`, `INT.add`, `INT.ge` at values, value distinctness, and Γ's value of the count at
  its silent point. No sentence of the text states a value of `findString`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvCountAllEmptyE7

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/e7-constfold.kompile.kore"
definition_of defn from "f2-examples/e7-constfold.kompile.kore"
user_axioms U from "f2-examples/e7-constfold.kompile.kore" module "E7-CONSTFOLD"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
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

kernel_rfl patternCe : ∀ H : HookParams, U.ax243.ax.pattern = fnCountRecCe.patternP (cH H)
kernel_rfl typedCe : ∀ H : HookParams, fnCountRecCe.typedPT (cH H) = fnCountRecCe.typedPT c
kernel_rfl vkeyCe_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i
kernel_rfl keysCe_wh : ∀ (H : HookParams) (vars : Vars), keysRPT (cH H) vars = keysRPT c vars

theorem textCe : U.ax243.ax.sortVars = [KoreAML.Rv] ∧ fnCountRecCe.typedPT c = true ∧
    (trS U.ax243).pat = (trAxiom [] [] U.ax243).pat ∧
    (∀ k ∈ KoreAML.freeOf [] U.ax243.ax.pattern, ∃ i, i < fnCountRecCe.av.length ∧ k = vkey c fnCountRecCe.av i) ∧
    ((keysRPT c fnCountRecCe.av).map (KoreAML.tableOf U.ax243.ax.sortVars U.ax243.ax.pattern).idxOf).Nodup := by
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

/-- **Under every H giving the count an Int value at `("", "")`, in every model of Γ (cH H),
sentence 243 fails at the valuation sending its variables to `""`.** -/
theorem s243_at_of (H : HookParams) (hv : ∃ n, (cH H).hv stringCountAll [foS "", foS ""] = some (int n))
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax243.ax ∧ SetVarsAtValues (cH H) I e U.ax243.ax ∧
      ¬ (trS U.ax243).pat.interpret I e default := by
  rw [textCe.2.2.1]
  obtain ⟨hq, hm, hl, hr⟩ := partsCe (cH H)
  obtain ⟨n, hn⟩ := hv
  refine FnEqn.refutedPT_at (coreOKH H) fnCountRecCe ((typedCe H).trans textCe.2.1) σCe ?_
    (fun q hq' => by cases hq'; exact hq) hm ?_ U.ax243 (patternCe H) textCe.1
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

/-! ## Sentence 98 -/

/-- `countAllOccurrences`' signature in the registry. -/
def kCe : CtorSig := ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩

kernel_rfl pattern98 : U.ax98.ax.pattern = LibEv.funPatR kCe

/-- Sentence 98 as `LibEv.functional_ev` reads such a sentence: one sort variable `R`, the
registry's names, `trS` the translation over no declarations, free variables `K0` and `K1`, and
places in its table apart for `R`, `K0`, `K1` and the bound `Val`. -/
theorem text98 : U.ax98.ax.sortVars = [KoreAML.Rv] ∧ LibEv.funReg kCe = true ∧
    (trS U.ax98).pat = (trAxiom [] [] U.ax98).pat ∧
    (U.ax98.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax98.ax.pattern).eraseDups =
      [.sortVar "R", .evar "K0" (regSrtK Srt.string), .evar "K1" (regSrtK Srt.string)] ∧
    (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "K0" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.sortVar "R") ∧
    (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "K1" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.sortVar "R") ∧
    (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "K0" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "Val" (regSrtK Srt.int)) ∧
    (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "K1" (regSrtK Srt.string)) ≠
      (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "Val" (regSrtK Srt.int)) ∧
    (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.sortVar "R") ≠
      (KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern).ev (.evar "Val" (regSrtK Srt.int)) := by
  decide +kernel

/-- `K0` and `K1` both at `""`. -/
def σ98 : Subst := [(0, foS ""), (1, foS "")]

/-- **In a model of Γ (cH H) where sentence 98 holds, the count has an Int value at `("", "")`,
for every H.** -/
theorem count98_value (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (h98 : I ⊧ᴵ (trS U.ax98).pat) :
    ∃ n, (cH H).hv stringCountAll [foS "", foS ""] = some (int n) := by
  have h := coreOKH H
  haveI : OvlOK (cH H) := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨hsv, hreg, htr, hfree, hK0R, hK1R, hK0V, hK1V, hRV⟩ := text98
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
  have h98' : I ⊧ᴵ (KoreAML.trAxiom [] [] U.ax98).pat := htr ▸ h98
  have hA := KoreAML.trAxiom_at hD h98'
  rw [hfree] at hA
  generalize KoreAML.tableOf U.ax98.ax.sortVars U.ax98.ax.pattern = t at hA hK0R hK1R hK0V hK1V hRV
  rw [pattern98, ← LibEv.funPat_reg (cH H) hreg] at hA
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
      ∃ v, σ98.lookup i = some v ∧ (cH H).sortOf v = some p.2 := by
    intro i p hp
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, hsE⟩
    | 1, hp => cases hp; exact ⟨_, rfl, hsE⟩
    | _ + 2, hp => simp [LibEv.funVars, LibEv.funVarsFrom, kCe] at hp
  have hag : ∀ i v, i < (LibEv.funVars kCe).length → σ98.lookup i = some v →
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
  have hval : LibEv.val (cH H) σ98 (LibEv.funTerm kCe) = (cH H).hv stringCountAll [foS "", foS ""] := rfl
  -- sentence 98 at `x`: `Val`, which is `x`, is the application
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

/-- **For every H, Γ (cH H) with sentences 98 and 243 has no model**: sentence 98 gives the count
a value at `("", "")`, where sentence 243 fails. -/
theorem s243_98_refuted (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → I ⊧ᴵ (trS U.ax98).pat → ¬ (I ⊧ᴵ (trS U.ax243).pat) := by
  intro M _ I hI h98 hax
  obtain ⟨e, -, -, hn⟩ := s243_at_of H (count98_value H hI h98) hI
  exact hn (hax e default)


/-- **For every H giving the count no value at `("", "")`, Γ (cH H) with sentence 98 has no
model.** -/
theorem s98_refuted_of_none (H : HookParams) (h : (cH H).hv stringCountAll [foS "", foS ""] = none) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax98).pat) := by
  intro M _ I hI h98
  obtain ⟨n, hn⟩ := count98_value H hI h98
  rw [h] at hn
  cases hn

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

/-- **For every H, Γ (cH H) has a model, and none of its models satisfies sentences 98 and 243.** -/
theorem s243_98_refuted_consistent (H : HookParams) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H)) ∧
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → I ⊧ᴵ (trS U.ax98).pat → ¬ (I ⊧ᴵ (trS U.ax243).pat) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  exact ⟨⟨M, hM, I, fun φ hφ => hI φ (Or.inl (Or.inl hφ))⟩, s243_98_refuted H⟩

end KCore.LibEvCountAllEmptyE7

/-- info: 'KCore.LibEvCountAllEmptyE7.s243_at_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCountAllEmptyE7.s243_at_of
/-- info: 'KCore.LibEvCountAllEmptyE7.count98_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCountAllEmptyE7.count98_value
/-- info: 'KCore.LibEvCountAllEmptyE7.s98_refuted_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCountAllEmptyE7.s98_refuted_of_none
/-- info: 'KCore.LibEvCountAllEmptyE7.s243_98_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCountAllEmptyE7.s243_98_refuted
/-- info: 'KCore.LibEvCountAllEmptyE7.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCountAllEmptyE7.consistent
/-- info: 'KCore.LibEvCountAllEmptyE7.s243_98_refuted_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCountAllEmptyE7.s243_98_refuted_consistent
