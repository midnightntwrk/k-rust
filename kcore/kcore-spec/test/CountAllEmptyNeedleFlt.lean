/-
  `countAllOccurrences`' second equation (domains.md 1898, sentence 294 of
  `f2-examples/silentflt.kompile.kore`) at the empty needle, in models of Γ.
  Run from the package root: `lake env lean -j1 test/CountAllEmptyNeedleFlt.lean`.

  At `Source = ""`, `ToCount = ""` the `requires` `findString("", "", 0) >=Int 0` is `true`, the
  patterns match, the left side is the count c at `("", "")` and the right side `1 +Int c`
  (`substrString("", 0 +Int 0, 0)` is `""`). Hence:
  - `s294_at`, `s294_refuted`: for every H under which Γ (cH H) meets `Semantics.silentTotal`
    (the count has an Int value at every pair of Strings, as the text's `functional` sentence of
    `countAllOccurrences`, 113, states), in every model of Γ (cH H) the sentence fails at that
    valuation, so Γ (cH H) with the sentence has no model; `s294_refuted_lib` at `HookParams.lib`.
  - `s294_none`: under an interpretation that gives the count no value at `("", "")`, both sides
    have no value there (`valP`), so the sentence is not refuted this way; such an interpretation
    does not meet `silentTotal`, and the `functional` sentence 113 asks a value there.
  That no interpretation admits both sentence 113 and sentence 294 is argued from these two facts,
  not stated here: the first form covers an H giving the count a value at `("", "")` only where H
  meets `silentTotal`, and the second does not state that 113 fails in models of Γ.

  This file states facts about one sentence; it is no tie file of the text (e6map reads
  `TieEns*`, `TieKimp*`, `TieKk*` and `LibEv*` files only), and the row of the sentence takes its
  status from those.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.CountAllEmptyNeedleFlt

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

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

kernel_rfl patternCe : ∀ H : HookParams, U.ax294.ax.pattern = fnCountRecCe.patternP (cH H)
kernel_rfl typedCe : ∀ H : HookParams, fnCountRecCe.typedPT (cH H) = fnCountRecCe.typedPT c
kernel_rfl vkeyCe_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i
kernel_rfl keysCe_wh : ∀ (H : HookParams) (vars : Vars), keysRPT (cH H) vars = keysRPT c vars

theorem textCe : U.ax294.ax.sortVars = [KoreAML.Rv] ∧ fnCountRecCe.typedPT c = true ∧
    (trS U.ax294).pat = (trAxiom [] [] U.ax294).pat ∧
    (∀ k ∈ KoreAML.freeOf [] U.ax294.ax.pattern, ∃ i, i < fnCountRecCe.av.length ∧ k = vkey c fnCountRecCe.av i) ∧
    ((keysRPT c fnCountRecCe.av).map (KoreAML.tableOf U.ax294.ax.sortVars U.ax294.ax.pattern).idxOf).Nodup := by
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

/-- **Under every H meeting `silentTotal`, in every model of Γ (cH H), sentence 294 fails at the
valuation sending its variables to `""`.** -/
theorem s294_at (H : HookParams) (ht : (cH H).silentTotal) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax294.ax ∧ SetVarsAtValues (cH H) I e U.ax294.ax ∧
      ¬ (trS U.ax294).pat.interpret I e default := by
  rw [textCe.2.2.1]
  obtain ⟨hq, hm, hl, hr⟩ := partsCe (cH H)
  obtain ⟨n, hn⟩ := totalCe (shapesOKH H) ht
  refine FnEqn.refutedPT_at (coreOKH H) fnCountRecCe ((typedCe H).trans textCe.2.1) σCe ?_
    (fun q hq' => by cases hq'; exact hq) hm ?_ U.ax294 (patternCe H) textCe.1
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

/-- **Γ (cH H) with sentence 294 has no model, for every H meeting `silentTotal`.** -/
theorem s294_refuted (H : HookParams) (ht : (cH H).silentTotal) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax294).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := s294_at H ht hI
  exact hn (hax e default)

theorem s294_refuted_lib : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH HookParams.lib) → ¬ (I ⊧ᴵ (trS U.ax294).pat) :=
  s294_refuted HookParams.lib (silentTotal_of_libAdmitted (libAdmitted_lib_of_coreOK coreOK))

/-- Where the interpretation gives the count no value at `("", "")`, both sides have none there. -/
theorem s294_none (H : HookParams) (h : (cH H).hv stringCountAll [foS "", foS ""] = none) :
    valP (cH H) σCe fnCountRecCe.lhs = valP (cH H) σCe fnCountRecCe.rhs := by
  obtain ⟨-, -, hl, hr⟩ := partsCe (cH H)
  rw [hl, hr, h]; rfl

end KCore.CountAllEmptyNeedleFlt

/-- info: 'KCore.CountAllEmptyNeedleFlt.s294_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CountAllEmptyNeedleFlt.s294_refuted
/-- info: 'KCore.CountAllEmptyNeedleFlt.s294_refuted_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CountAllEmptyNeedleFlt.s294_refuted_lib
/-- info: 'KCore.CountAllEmptyNeedleFlt.s294_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CountAllEmptyNeedleFlt.s294_none
