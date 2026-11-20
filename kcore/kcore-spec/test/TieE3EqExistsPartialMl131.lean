/-
  The companion of sentence 131 of fixture `e3-eq-exists-partial-ml` (test/constructs/fixtures), on
  the fixture's kompiled text `f2-examples/e3-eq-exists-partial-ml.kompile.kore`:
  `rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`, f not `total`. Indices are
  `AxiomDecl.index`. Run from the package root: `lake env lean -j1 test/TieE3EqExistsPartialMl131.lean`.

  The reading (`existentialClause`). `defn.sem` has one function, f, with one clause: B an
  existential variable, the right side B, the predicate `B = notBool(X)` its `post`. Γ's item for
  it is item 0 of `fnItems`: the equation whose right side is `∃B:Bool. (B ∧ ⊤_Bool ∧ B = notBool(X))`,
  the clause's `ensures` part (none: `⊤_Bool`) written between the term and the predicate under the
  binder (`Faithful.clauseRhs`). The sentence has no such conjunct, so the item is not the sentence's
  translation (`TieE3EqExistsPartialMl.un0_differs`).

  The shapes (kernel).
  - `text_shape`: the translated sentence 131 is `eqnPat` with the right side
    `(∃B:Bool. B ∧ (B = notBool(X))) ∧ ⊤`.
  - `gamma_shape`: Γ's item 0 is `eqnPat` over the same guards, premise, sort and left side, with
    the right side `(∃B:Bool. B ∧ (⊤_Bool ∧ (B = notBool(X)))) ∧ ⊤`. The variables' indices are the
    same in the two: no variable is renamed.
  - `top_free`: the variable `⊤_Bool` binds is not free in Bool's pattern.

  The two hold in the same interpretations (`item0_iff`), with no premise: under `∃B:Bool` the
  conjunct B makes the element the one B holds, which the binder's guard puts in Bool, so `⊤_Bool`
  holds there (`ExEnsTop.sTop_of_member`, read without definedness: `ExEnsTop.member_raw`); an
  equation reads its right side by its elements (`TieExHoistB.eqnPat_congr`). The three lemmas of
  `ExEnsTop` are over any patterns and any interpretation; nothing in them is of this text.

  - W1, `ex_from_text`, for every H: every interpretation that satisfies sentence 131 as written
    satisfies Γ's item 0. The one premise is the sentence: no item of Γ, no fact of the
    interpretation, no definedness, no functional sentence. `ex_from_text_sig` is the same over the
    premise set `TiePair.Texts [sentence 131] ∪ ΓSig (cH H)`, of which it reads the sentence alone.
  - E, `ex_entailed`, for every H: `Γ (cH H)` entails sentence 131, from its item 0 alone;
    `ex_entailed_c`: so does `Γc (cH H)`, the definition's theory (it reads a confined sort,
    `TieE3EqExistsPartialMl.readsConfined_c`). `boolClosed` is not read.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ExEnsTop

open ML KoreAML KoreAML.TieFR

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A membership `x ∈ φ`, read with no fact of the interpretation. -/
theorem member_raw {x : EVar} {φ : P} {e : Valuation M} {m : M} :
    (x ∈∈ φ : P).interpret I e m ↔
      ∃ d, I.evalSymb HasDefined.defined d ∧ φ.interpret I e (e.evalEvar x) ∧ I.evalApp d (e.evalEvar x) m := by
  unfold member
  rw [interp_app]
  constructor
  · rintro ⟨d, b, hd, hb, happ⟩
    rw [interpret_conj, interp_evar] at hb
    obtain ⟨rfl, hφ⟩ := hb
    exact ⟨d, hd, hφ, happ⟩
  · rintro ⟨d, hd, hφ, happ⟩
    exact ⟨d, _, hd, interpret_conj.mpr ⟨interp_evar.mpr rfl, hφ⟩, happ⟩

/-- Where the element is the one x holds and x is of the sort s, `⊤_s` holds. -/
theorem sTop_of_member {x : EVar} {s : P} (hs : s.isFreeEvar topVar = false) {e : Valuation M} {m : M}
    (hx : (Pattern.evar x : P).interpret I e m) (h : (x ∈∈ inhOf s : P).interpret I e m) :
    (sTop s).interpret I e m := by
  rw [interp_evar] at hx
  unfold sTop
  rw [interp_sExists]
  refine ⟨m, ?_, by rw [interp_evar]; show m = Function.update e.evalEvar topVar m topVar; rw [Function.update_same]⟩
  obtain ⟨d, hd, hφ, happ⟩ := member_raw.mp h
  rw [← hx] at hφ happ
  refine member_raw.mpr ⟨d, hd, ?_, ?_⟩
  · show (inhOf s).interpret I _ (Function.update e.evalEvar topVar m topVar)
    rw [Function.update_same]
    refine (only_free_var_relevant _ _ _ _ (fun y hy => ?_) (fun _ _ => rfl) m).mpr hφ
    have hyx : y ≠ topVar := by
      rintro rfl
      have : (inhOf s).isFreeEvar topVar = false := by
        unfold inhOf sym; simp [Pattern.isFreeEvar, hs]
      rw [this] at hy; cases hy
    exact Function.update_noteq hyx _ _
  · show I.evalApp d (Function.update e.evalEvar topVar m topVar) m
    rw [Function.update_same]; exact happ

/-- **`⊤_s` beside the bound variable is no conjunct**: under `∃x:s`, the body `x ∧ (⊤_s ∧ ψ)`
holds the elements `x ∧ ψ` holds, in every interpretation. -/
theorem exists_ensTop {x : EVar} {s ψ : P} (hs : s.isFreeEvar topVar = false) (e : Valuation M) (m : M) :
    (sExists x s (sAnd (.evar x) (sAnd (sTop s) ψ))).interpret I e m ↔
      (sExists x s (sAnd (.evar x) ψ)).interpret I e m := by
  rw [interp_sExists, interp_sExists]
  refine exists_congr fun a => and_congr_right fun hin => ?_
  rw [interp_sAnd, interp_sAnd, interp_sAnd]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, sTop_of_member hs h.1 hin, h.2⟩⟩

/-- **The equation with `⊤_s` beside the bound variable holds in the models of the equation
without it**, whatever the `ensures` part: no premise. -/
theorem eqnPat_ensTop {ws : List P} {r x : EVar} {prem S F s ψ ens : P} (hs : s.isFreeEvar topVar = false) :
    (I ⊧ᴵ eqnPat ws r prem S F (sAnd (sExists x s (sAnd (.evar x) (sAnd (sTop s) ψ))) ens)) ↔
      (I ⊧ᴵ eqnPat ws r prem S F (sAnd (sExists x s (sAnd (.evar x) ψ)) ens)) :=
  TieExHoistB.eqnPat_congr fun e m => by rw [interp_sAnd, interp_sAnd, exists_ensTop hs e m]
end

end KCore.ExEnsTop

namespace KCore.TieE3EqExistsPartialMl131

open ML KoreAML KoreAML.TieFR

kore_term kore from "f2-examples/e3-eq-exists-partial-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-partial-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-partial-ml.kompile.kore" module "E3-EQ-EXISTS-PARTIAL-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-- The sentence's index in the text. -/
theorem sentence_index : U.ax131.index = 131 := rfl

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
/-- The predicate under the binder, `B = notBool(X)`. -/
def eqK : Kore.Pattern := .equals bS bS Bp (ap "LblnotBool'Unds'" [Xp])
def premK : Kore.Pattern := .and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]]
def FK : Kore.Pattern := ap "Lblf" [ev "X0" bS]

/-- The table of sentence 131, its guards, and the patterns of its parts. -/
noncomputable def tbl : VarTable := tableOf U.ax131.ax.sortVars U.ax131.ax.pattern
noncomputable abbrev ctx : Ctx := ⟨tbl, kore.aliasNames⟩
noncomputable def ws : List P := guardsOf U.ax131.ax
noncomputable def rG : EVar := tbl.ev (sortVarKey Rv)
noncomputable def prem : P := tr ctx premK
noncomputable def BoolP : P := trSort tbl bS
noncomputable def Ff : P := tr ctx FK
noncomputable def xB : EVar := tbl.ev (evarKey (evar "VarB" bS))
noncomputable def eqP : P := tr ctx eqK
noncomputable def ensT : P := tr ctx (.top bS)

theorem tbl_eq : tbl = [.sortVar "R", .evar "X0" bS, .evar "VarX" bS, .evar "VarB" bS] := by decide +kernel

/-- **Sentence 131, translated as the text writes it, is the equation
`X0 ∈ X → f(X0) = (∃B:Bool. B ∧ (B = notBool(X))) ∧ ⊤`** (kernel). -/
theorem text_shape : (trS U.ax131).pat =
    eqnPat ws rG prem BoolP Ff (sAnd (sExists xB BoolP (sAnd (.evar xB) eqP)) ensT) := by decide +kernel

/-- Γ's item 0: the existential clause's equation. -/
noncomputable def item0 : P :=
  eqnPat ws rG prem BoolP Ff (sAnd (sExists xB BoolP (sAnd (.evar xB) (sAnd (sTop BoolP) eqP))) ensT)

/-- **Γ's item 0 is the equation with `⊤_Bool` between the term and the predicate under the
binder** (kernel), over the sentence's guards, premise, sort, left side and variables. -/
theorem gamma_shape : (TiePair.gammaPats c)[0]? = some item0 := by decide +kernel

/-- The variable `⊤_Bool` binds is not free in Bool's pattern. -/
theorem top_free : BoolP.isFreeEvar topVar = false := by decide +kernel

/-- Γ's item 0, for every H. -/
theorem item0_at (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it → it.pat = item0 := by
  intro it hit
  rw [TiePair.fnItems_withHooks] at hit
  have h : (TiePair.gammaPats c)[0]? = some it.pat := by
    unfold TiePair.gammaPats; rw [List.getElem?_map, hit]; rfl
  rw [gamma_shape] at h
  exact (Option.some.inj h).symm

/-- Γ has an item 0, for every H. -/
theorem item0_mem (H : HookParams) : ∃ it ∈ Faithful.fnItems (cH H), it.pat = item0 := by
  have h := gamma_shape
  unfold TiePair.gammaPats at h
  rw [List.getElem?_map] at h
  obtain ⟨it, hit, hp⟩ := Option.map_eq_some_iff.mp h
  exact ⟨it, by rw [TiePair.fnItems_withHooks]; exact List.mem_of_getElem? hit, hp⟩

/-- **Sentence 131 and Γ's item 0 hold in the same interpretations.** No premise. -/
theorem item0_iff {M : Type} {I : Interpretation KoreAML.Sym M} : (I ⊧ᴵ item0) ↔ (I ⊧ᴵ (trS U.ax131).pat) := by
  rw [text_shape]
  exact ExEnsTop.eqnPat_ensTop top_free

/-- **W1. The sentence as written gives Γ's item 0**, for every H: in every interpretation that
satisfies sentence 131. The sentence is the one premise. -/
theorem ex_from_text (H : HookParams) {M : Type} {I : Interpretation KoreAML.Sym M}
    (hT : I ⊧ᴵ (trS U.ax131).pat) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it → I ⊧ᴵ it.pat := by
  intro it hit
  rw [item0_at H it hit]
  exact item0_iff.mpr hT

/-- W1 over the premise set of the sentence and the signature: Γ's item 0 is a consequence of
`TiePair.Texts [sentence 131] ∪ ΓSig (cH H)`, for every H. Of it the proof reads the sentence. -/
theorem ex_from_text_sig (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax131).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  exact ex_from_text H (hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))) it hit

/-- **E. Γ entails sentence 131**, for every H, from its item 0. -/
theorem ex_entailed (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax131).pat := by
  intro M _ I hI
  obtain ⟨it, hit, hp⟩ := item0_mem H
  refine item0_iff.mp ?_
  rw [← hp]
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, hit, rfl⟩))

/-- **E over the definition's theory**: `Γc (cH H)` entails sentence 131, for every H. -/
theorem ex_entailed_c (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax131).pat := by
  intro M _ I hIc
  exact ex_entailed H fun φ hφ => hIc φ (Or.inl hφ)

end KCore.TieE3EqExistsPartialMl131

#check @KCore.ExEnsTop.member_raw
#check @KCore.ExEnsTop.sTop_of_member
#check @KCore.ExEnsTop.exists_ensTop
#check @KCore.ExEnsTop.eqnPat_ensTop
#check @KCore.TieE3EqExistsPartialMl131.text_shape
#check @KCore.TieE3EqExistsPartialMl131.gamma_shape
#check @KCore.TieE3EqExistsPartialMl131.item0_iff
#check @KCore.TieE3EqExistsPartialMl131.ex_from_text
#check @KCore.TieE3EqExistsPartialMl131.ex_from_text_sig
#check @KCore.TieE3EqExistsPartialMl131.ex_entailed
#check @KCore.TieE3EqExistsPartialMl131.ex_entailed_c
#print axioms KCore.TieE3EqExistsPartialMl131.ex_from_text
#print axioms KCore.TieE3EqExistsPartialMl131.ex_from_text_sig
#print axioms KCore.TieE3EqExistsPartialMl131.ex_entailed_c
