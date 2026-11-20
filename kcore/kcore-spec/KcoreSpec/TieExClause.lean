/-
  KCore, outside the cone: the right side of an equation read as a clause with existential
  variables (`Parse.ceRead`, `Faithful.clauseRhs`) against the right side the text writes. Γ's item
  of such a clause is `prem → F = (∃x̄. rhs ∧ ⊤_S ∧ post) ∧ ⊤`: the clause's `ensures` part between
  the term and the predicates under the binders, a conjunction or disjunction of terms read as a
  fresh variable with its memberships. Each lemma here says that one such right side holds the
  elements of the text's, at every valuation; an equation reads its right side by its elements on
  its sort (`eqnPat_congr_on`), so the two sentences hold in the same interpretations.

  With no fact of the interpretation (`ExEnsTop`):
  - `exists_ensTop`, `eqnPat_ensTop`: under `∃x:s`, `x ∧ (⊤_s ∧ ψ)` is `x ∧ ψ`.

  In an interpretation where definedness is definedness and the item of `⌈_⌉` holds, the sorts
  named denoting sorts (`SortAt`), at an element of the equation's sort:
  - `ensTop_body`, `ensTop_ex_body`: `t ∧ (⊤_S ∧ ψ)` is `t ∧ ψ`, any term t, under a binder of any sort.
  - `memTerm_body`: `∃x. x ∧ (⊤ ∧ x ∈ t)` is `∃x. x ∧ t`.
  - `andRight_body`: `∃x. x ∧ (⊤ ∧ (ψ ∧ x ∈ u))` is `u ∧ ∃x. (x ∧ ψ)`, x not free in u.
  - `underApp_body`: `∃x. h(x) ∧ (⊤ ∧ ψ)` is `h(∃x. (x ∧ ψ))`, ψ a predicate on the sort (`PredOn`),
    x not free in h.
  - `mems2_body`, `twoBinders_body`: `∃y. ∃z. z ∧ (⊤ ∧ (ψ ∧ (z ∈ t ∧ z ∈ u)))` is
    `∃y. ∃z. ((z ∧ t) ∧ u) ∧ ψ`.
  - `cutAnd_body`: `∃z. z ∧ (⊤ ∧ (z ∈ t ∧ z ∈ u))` is `t ∧ u`, z free in neither.
  - `cutCeil_body`: `∃z. X ∧ (⊤ ∧ (⌈z⌉ ∧ (z ∈ t ∧ z ∈ u)))` is `X ∧ ⌈t ∧ u⌉`, where the elements of
    `t ∧ u` lie in the sort (a premise: the arity of the heads of t or u gives it).
  - `cutOr_body`: `∃z. z ∧ (⊤ ∧ (z ∈ t ∨ z ∈ u))` is `t ∨ u`.
  - `inOr_body`: `∃y. ∃z. z ∧ (⊤ ∧ (z ∈ X ∨ (z ∈ y ∧ ψ)))` is `X ∨ ∃y. (y ∧ ψ)`.
  - `inOrEx_body`: `∃z. z ∧ (⊤ ∧ (z ∈ X ∨ ∃y'. (z ∈ y' ∧ ψ')))` is `X ∨ ∃y. (y ∧ ψ)`, ψ' being ψ with
    its binder renamed (`renamed_body` gives the premise from a decision on the patterns).
  - `sortAt_sig`: a numbered sort's pattern denotes a sort, in an interpretation with the
    signature's facts. `tie_of_iff`: where Γ's item j and a sentence hold in the same
    interpretations with those facts, the item is a consequence of the sentence with definedness
    and `ΓSig`, and Γ entails the sentence.
  - `eqnPat_congr_on`, `eqnPat_of_body`: the sentences with two right sides that hold the same
    elements of the sort, at the valuations satisfying the guards, hold in the same interpretations.
  - `exVac_body`: `∃x. φ` is φ where φ does not hold x; `exVar_body`, `exVarTop_body`: `∃x. x` and
    `∃x. x ∧ ⊤` hold every element of the sort.
  - `topCut_body`: `∃z. z ∧ (⊤ ∧ (z ∈ X ∧ ψ'))` is `X ∧ ψ`, ψ' and ψ holding an element together
    (`sNot_congr_body` carries that under a `\not`); `ceilEx_body`: `∃y. ⌈y⌉ ∧ (y ∈ t ∧ y ∈ u)` is
    `⌈t ∧ u⌉`, where the elements of `t ∧ u` lie in the sort.
  - `exEqVar_body`: `∃c. (c ∧ c = y)` holds the element y holds, y at an element of the sort and c
    another variable; `nestedApp_body`: `∃z. h(z) ∧ ⊤` is `∃y. h(∃c. (c ∧ c = y))`.
  - `CutOf`, `cutOf_body`, `cutOf_mem`, `cutOf_or`: `∃z. z ∧ (⊤ ∧ ψ')` is T where ψ' is T's cut at z: a
    membership of z in a pattern that does not hold it, or a disjunction of cuts.
  - The parts of an equation sentence read off its KORE pattern (`premK`, `lhsK`, `rhsK`, `ensK`,
    `exBK`, `exVK`, `argK`, `ceilK`, `eqLK`, `eqRK`, `notK`, `headK`), and `sortAtN`: a numbered sort's
    pattern, by its name, denotes a sort.
-/
import KcoreSpec.TieExHoistB
import KcoreSpec.TieRename
import KcoreSpec.TiePairs
import KcoreSpec.TieFRSig

set_option autoImplicit false

namespace KCore

open ML KoreAML KoreAML.TieFR

namespace ExEnsTop

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

end ExEnsTop

namespace TieExClause

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation e with x at a. -/
abbrev upd (e : Valuation M) (x : EVar) (a : M) : Valuation M :=
  ⟨Function.update e.evalEvar x a, e.evalSvar⟩

theorem upd_same (e : Valuation M) (x : EVar) (b : M) : (upd e x b).evalEvar x = b := by
  show Function.update e.evalEvar x b x = b
  rw [Function.update_same]

theorem upd_ne (e : Valuation M) {x y : EVar} (h : y ≠ x) (b : M) : (upd e x b).evalEvar y = e.evalEvar y := by
  show Function.update e.evalEvar x b y = e.evalEvar y
  rw [Function.update_noteq h]

/-- A pattern in which x is not free holds the same elements whatever x holds. -/
theorem upd_irrel {x : EVar} {φ : P} (h : φ.isFreeEvar x = false) (e : Valuation M) (b m : M) :
    φ.interpret I (upd e x b) m ↔ φ.interpret I e m :=
  only_free_var_relevant _ _ _ _ (fun y hy => by
    have hyx : y ≠ x := by rintro rfl; rw [h] at hy; cases hy
    exact Function.update_noteq hyx _ _) (fun _ _ => rfl) m

/-- ψ is a predicate on the sort σ at e: the whole sort or nothing. -/
def PredOn (I : Interpretation KoreAML.Sym M) (σ : M) (ψ : P) (e : Valuation M) : Prop :=
  ∃ Q : Prop, ∀ m, ψ.interpret I e m ↔ Inh I σ m ∧ Q

section
variable (hD : DefOK I)
include hD

/-- A sorted `\exists` over a sort that denotes τ: some element of τ has the body at it. -/
theorem exS_iff {x : EVar} {s φ : P} {τ : M} (hs : SortAt I s τ) {e : Valuation M} {m : M} :
    (sExists x s φ).interpret I e m ↔ ∃ b, Inh I τ b ∧ φ.interpret I (upd e x b) m := by
  rw [interp_sExists_elem hD]
  exact exists_congr fun b => and_congr_left' (interp_inhOf_of (hs.den _))

/-- `⊤_S` is the sort. -/
theorem sTop_iff {S : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M} :
    (sTop S).interpret I e a ↔ Inh I σ a := by
  rw [interp_sTop hD hS.closed, interp_inhOf_of (hS.den e)]

/-- **`t ∧ (⊤_S ∧ ψ)` is `t ∧ ψ` at an element of S.** -/
theorem ensTop_body {S t ψ : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sAnd t (sAnd (sTop S) ψ)).interpret I e a ↔ (sAnd t ψ).interpret I e a := by
  rw [interp_sAnd, interp_sAnd, interp_sAnd, sTop_iff hD hS]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ha, h.2⟩⟩

/-- **Under a binder of any sort, `∃x:s. t ∧ (⊤_S ∧ ψ)` is `∃x:s. t ∧ ψ` at an element of S.** -/
theorem ensTop_ex_body {x : EVar} {s S t ψ : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M}
    (ha : Inh I σ a) :
    (sExists x s (sAnd t (sAnd (sTop S) ψ))).interpret I e a ↔ (sExists x s (sAnd t ψ)).interpret I e a := by
  rw [interp_sExists, interp_sExists]
  exact exists_congr fun b => and_congr_right fun _ => ensTop_body hD hS ha

section
variable [Inhabited M] (hc : I ⊧ᴵ ceilDefItem.pat)
include hc

/-- A membership of a variable that holds an element of s, in a pattern: the sort S' where the
element is in the pattern. -/
theorem sIn_var {x : EVar} {s S' t : P} {τ σ' : M} (hs : SortAt I s τ) (hS' : SortAt I S' σ')
    {e : Valuation M} (hx : Inh I τ (e.evalEvar x)) (m : M) :
    (sIn s S' (.evar x) t).interpret I e m ↔ t.interpret I e (e.evalEvar x) ∧ Inh I σ' m := by
  rw [interp_sIn hD hc (hs.den e) (hS'.den e) hs.isSort hS'.isSort
    (fun a ha => by rw [interp_evar] at ha; rw [ha]; exact hx) m]
  simp only [interp_evar]
  exact and_congr_left' ⟨fun ⟨_, h1, h2⟩ => h1 ▸ h2, fun h => ⟨_, rfl, h⟩⟩

/-- `\equals` at the sort S is a predicate on it. -/
theorem sEquals_predOn {s S φ ψ : P} {τ σ : M} (hs : SortAt I s τ) (hS : SortAt I S σ) (e : Valuation M) :
    PredOn I σ (sEquals s S φ ψ) e :=
  ⟨∀ a, Inh I τ a → (φ.interpret I e a ↔ ψ.interpret I e a), fun m =>
    interp_sEquals hD hc (hs.den e) (hS.den e) hs.isSort hS.isSort m⟩

/-- **`∃x. x ∧ (⊤ ∧ x ∈ t)` is `∃x. x ∧ t`** at an element of S. -/
theorem memTerm_body {x : EVar} {S t : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M}
    (ha : Inh I σ a) :
    (sExists x S (sAnd (.evar x) (sAnd (sTop S) (sIn S S (.evar x) t)))).interpret I e a ↔
      (sExists x S (sAnd (.evar x) t)).interpret I e a := by
  rw [exS_iff hD hS, exS_iff hD hS]
  refine exists_congr fun b => and_congr_right fun hb => ?_
  have hx : Inh I σ ((upd e x b).evalEvar x) := by rw [upd_same]; exact hb
  rw [interp_sAnd, interp_sAnd, interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar]
  constructor
  · rintro ⟨h1, -, h3, -⟩; exact ⟨h1, h1 ▸ h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, ha, h1 ▸ h2, ha⟩

/-- **`∃x. x ∧ (⊤ ∧ (ψ ∧ x ∈ u))` is `u ∧ ∃x. (x ∧ ψ)`** at an element of S, x not free in u. -/
theorem andRight_body {x : EVar} {S u ψ : P} {σ : M} (hS : SortAt I S σ) (hu : u.isFreeEvar x = false)
    {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sExists x S (sAnd (.evar x) (sAnd (sTop S) (sAnd ψ (sIn S S (.evar x) u))))).interpret I e a ↔
      (sAnd u (sExists x S (sAnd (.evar x) ψ))).interpret I e a := by
  rw [interp_sAnd, exS_iff hD hS, exS_iff hD hS]
  constructor
  · rintro ⟨b, hb, h⟩
    have hx : Inh I σ ((upd e x b).evalEvar x) := by rw [upd_same]; exact hb
    rw [interp_sAnd, interp_sAnd, interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar] at h
    obtain ⟨h1, -, h3, h4, -⟩ := h
    exact ⟨(upd_irrel hu e b a).mp (h1 ▸ h4), b, hb, interp_sAnd.mpr ⟨interp_evar.mpr h1, h3⟩⟩
  · rintro ⟨h0, b, hb, h⟩
    have hx : Inh I σ ((upd e x b).evalEvar x) := by rw [upd_same]; exact hb
    rw [interp_sAnd, interp_evar] at h
    refine ⟨b, hb, ?_⟩
    rw [interp_sAnd, interp_sAnd, interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar]
    exact ⟨h.1, ha, h.2, h.1 ▸ (upd_irrel hu e b a).mpr h0, ha⟩

omit hc [Inhabited M] in
/-- **`∃x. h(x) ∧ (⊤ ∧ ψ)` is `h(∃x. (x ∧ ψ))`** at an element of S, for a predicate ψ on S and a
head h in which x is not free. -/
theorem underApp_body {x : EVar} {S hd ψ : P} {σ : M} (hS : SortAt I S σ) (hh : hd.isFreeEvar x = false)
    {e : Valuation M} (hψ : ∀ b, Inh I σ b → PredOn I σ ψ (upd e x b)) {a : M} (ha : Inh I σ a) :
    (sExists x S (sAnd (hd ⬝ .evar x) (sAnd (sTop S) ψ))).interpret I e a ↔
      (hd ⬝ sExists x S (sAnd (.evar x) ψ)).interpret I e a := by
  rw [exS_iff hD hS, interp_app]
  constructor
  · rintro ⟨b, hb, h⟩
    rw [interp_sAnd, interp_sAnd, sTop_iff hD hS, interp_app] at h
    obtain ⟨⟨f, c, hf, hc', happ⟩, -, h3⟩ := h
    rw [interp_evar] at hc'
    obtain ⟨Q, hQ⟩ := hψ b hb
    have hcb : c = b := by rw [hc']; exact Function.update_same ..
    refine ⟨f, c, (upd_irrel hh e b f).mp hf, (exS_iff hD hS).mpr ⟨b, hb, ?_⟩, happ⟩
    rw [interp_sAnd, interp_evar]
    exact ⟨hc', (hQ c).mpr ⟨hcb ▸ hb, ((hQ a).mp h3).2⟩⟩
  · rintro ⟨f, c, hf, hex, happ⟩
    obtain ⟨b, hb, h⟩ := (exS_iff hD hS).mp hex
    rw [interp_sAnd, interp_evar] at h
    obtain ⟨Q, hQ⟩ := hψ b hb
    refine ⟨b, hb, ?_⟩
    rw [interp_sAnd, interp_sAnd, sTop_iff hD hS, interp_app]
    exact ⟨⟨f, c, (upd_irrel hh e b f).mpr hf, interp_evar.mpr h.1, happ⟩, ha, (hQ a).mpr ⟨ha, ((hQ c).mp h.2).2⟩⟩

/-- `z ∧ (⊤ ∧ (ψ ∧ (z ∈ t ∧ z ∈ u)))` is `((z ∧ t) ∧ u) ∧ ψ` at an element of S, z holding an
element of S. -/
theorem mems2_body {z : EVar} {S t u ψ : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M}
    (hz : Inh I σ (e.evalEvar z)) {a : M} (ha : Inh I σ a) :
    (sAnd (.evar z) (sAnd (sTop S) (sAnd ψ (sAnd (sIn S S (.evar z) t) (sIn S S (.evar z) u))))).interpret I e a ↔
      (sAnd (sAnd (sAnd (.evar z) t) u) ψ).interpret I e a := by
  simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hz, interp_evar]
  constructor
  · rintro ⟨h1, -, h3, ⟨h4, -⟩, h5, -⟩; exact ⟨⟨⟨h1, h1 ▸ h4⟩, h1 ▸ h5⟩, h3⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, ha, h4, ⟨h1 ▸ h2, ha⟩, h1 ▸ h3, ha⟩

/-- **`∃y:s. ∃z:S. z ∧ (⊤ ∧ (ψ ∧ (z ∈ t ∧ z ∈ u)))` is `∃y:s. ∃z:S. ((z ∧ t) ∧ u) ∧ ψ`** at an
element of S. -/
theorem twoBinders_body {y z : EVar} {s S t u ψ : P} {τ σ : M} (hs : SortAt I s τ) (hS : SortAt I S σ)
    {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sExists y s (sExists z S (sAnd (.evar z) (sAnd (sTop S)
        (sAnd ψ (sAnd (sIn S S (.evar z) t) (sIn S S (.evar z) u))))))).interpret I e a ↔
      (sExists y s (sExists z S (sAnd (sAnd (sAnd (.evar z) t) u) ψ))).interpret I e a := by
  rw [exS_iff hD hs, exS_iff hD hs]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  rw [exS_iff hD hS, exS_iff hD hS]
  refine exists_congr fun w => and_congr_right fun hw => ?_
  refine mems2_body hD hc hS ?_ ha
  rw [upd_same]; exact hw

/-- **`∃z. z ∧ (⊤ ∧ (z ∈ t ∧ z ∈ u))` is `t ∧ u`** at an element of S, z free in neither. -/
theorem cutAnd_body {z : EVar} {S t u : P} {σ : M} (hS : SortAt I S σ) (ht : t.isFreeEvar z = false)
    (hu : u.isFreeEvar z = false) {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sExists z S (sAnd (.evar z) (sAnd (sTop S) (sAnd (sIn S S (.evar z) t) (sIn S S (.evar z) u))))).interpret I e a ↔
      (sAnd t u).interpret I e a := by
  rw [exS_iff hD hS, interp_sAnd]
  constructor
  · rintro ⟨b, hb, h⟩
    have hx : Inh I σ ((upd e z b).evalEvar z) := by rw [upd_same]; exact hb
    simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar, Function.update_same] at h
    obtain ⟨h1, -, ⟨h3, -⟩, h4, -⟩ := h
    exact ⟨(upd_irrel ht e b a).mp (h1 ▸ h3), (upd_irrel hu e b a).mp (h1 ▸ h4)⟩
  · rintro ⟨h1, h2⟩
    have hx : Inh I σ ((upd e z a).evalEvar z) := by rw [upd_same]; exact ha
    have hza : (upd e z a).evalEvar z = a := upd_same ..
    refine ⟨a, ha, ?_⟩
    simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar, Function.update_same]
    exact ⟨trivial, ha, ⟨(upd_irrel ht e a a).mpr h1, ha⟩, (upd_irrel hu e a a).mpr h2, ha⟩

/-- **`∃z. X ∧ (⊤ ∧ (⌈z⌉ ∧ (z ∈ t ∧ z ∈ u)))` is `X ∧ ⌈t ∧ u⌉`** at an element of S, z free in
none of X, t, u, where the elements of `t ∧ u` lie in S. -/
theorem cutCeil_body {z : EVar} {S X t u : P} {σ : M} (hS : SortAt I S σ) (hX : X.isFreeEvar z = false)
    (ht : t.isFreeEvar z = false) (hu : u.isFreeEvar z = false) {e : Valuation M}
    (hin : ∀ b, t.interpret I e b → u.interpret I e b → Inh I σ b) {a : M} (ha : Inh I σ a) :
    (sExists z S (sAnd X (sAnd (sTop S) (sAnd (sCeil S S (.evar z))
        (sAnd (sIn S S (.evar z) t) (sIn S S (.evar z) u)))))).interpret I e a ↔
      (sAnd X (sCeil S S (sAnd t u))).interpret I e a := by
  rw [exS_iff hD hS, interp_sAnd,
    interp_sCeil hD hc (hS.den e) (hS.den e) hS.isSort hS.isSort
      (fun b hb => hin b (interp_sAnd.mp hb).1 (interp_sAnd.mp hb).2) a]
  constructor
  · rintro ⟨b, hb, h⟩
    have hx : Inh I σ ((upd e z b).evalEvar z) := by rw [upd_same]; exact hb
    have hzb : (upd e z b).evalEvar z = b := upd_same ..
    simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, Function.update_same] at h
    obtain ⟨h1, -, -, ⟨h3, -⟩, h4, -⟩ := h
    exact ⟨(upd_irrel hX e b a).mp h1,
      ⟨b, interp_sAnd.mpr ⟨(upd_irrel ht e b b).mp h3, (upd_irrel hu e b b).mp h4⟩⟩, ha⟩
  · rintro ⟨h1, ⟨b, hb⟩, -⟩
    rw [interp_sAnd] at hb
    have hbσ : Inh I σ b := hin b hb.1 hb.2
    have hx : Inh I σ ((upd e z b).evalEvar z) := by rw [upd_same]; exact hbσ
    have hzb : (upd e z b).evalEvar z = b := upd_same ..
    refine ⟨b, hbσ, ?_⟩
    simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, Function.update_same]
    refine ⟨(upd_irrel hX e b a).mpr h1, ha, ?_, ⟨(upd_irrel ht e b b).mpr hb.1, ha⟩,
      (upd_irrel hu e b b).mpr hb.2, ha⟩
    rw [interp_sCeil hD hc (hS.den _) (hS.den _) hS.isSort hS.isSort
      (fun c hc' => by rw [interp_evar] at hc'; rw [hc']; exact hx) a]
    exact ⟨⟨_, interp_evar.mpr rfl⟩, ha⟩

/-- **`∃z. z ∧ (⊤ ∧ (z ∈ t ∨ z ∈ u))` is `t ∨ u`** at an element of S, z free in neither. -/
theorem cutOr_body {z : EVar} {S t u : P} {σ : M} (hS : SortAt I S σ) (ht : t.isFreeEvar z = false)
    (hu : u.isFreeEvar z = false) {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sExists z S (sAnd (.evar z) (sAnd (sTop S) (sOr S (sIn S S (.evar z) t) (sIn S S (.evar z) u))))).interpret I e a ↔
      (sOr S t u).interpret I e a := by
  rw [exS_iff hD hS, interp_sOr, interp_inhOf_of (hS.den e)]
  constructor
  · rintro ⟨b, hb, h⟩
    have hx : Inh I σ ((upd e z b).evalEvar z) := by rw [upd_same]; exact hb
    have hzb : (upd e z b).evalEvar z = b := upd_same ..
    simp only [interp_sAnd, interp_sOr, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar,
      Function.update_same] at h
    obtain ⟨h1, -, -, h3⟩ := h
    refine ⟨ha, ?_⟩
    rcases h3 with ⟨h3, -⟩ | ⟨h3, -⟩
    · exact Or.inl ((upd_irrel ht e b a).mp (h1 ▸ h3))
    · exact Or.inr ((upd_irrel hu e b a).mp (h1 ▸ h3))
  · rintro ⟨-, h⟩
    have hx : Inh I σ ((upd e z a).evalEvar z) := by rw [upd_same]; exact ha
    have hza : (upd e z a).evalEvar z = a := upd_same ..
    refine ⟨a, ha, ?_⟩
    simp only [interp_sAnd, interp_sOr, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar,
      interp_inhOf_of (hS.den _), Function.update_same]
    refine ⟨trivial, ha, ha, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨(upd_irrel ht e a a).mpr h, ha⟩
    · exact Or.inr ⟨(upd_irrel hu e a a).mpr h, ha⟩

/-- **`∃y. ∃z. z ∧ (⊤ ∧ (z ∈ X ∨ (z ∈ y ∧ ψ)))` is `X ∨ ∃y. (y ∧ ψ)`** at an element of S: y and z
not free in X, z not free in ψ, z another variable than y. -/
theorem inOr_body {y z : EVar} {S X ψ : P} {σ : M} (hS : SortAt I S σ) (hXy : X.isFreeEvar y = false)
    (hXz : X.isFreeEvar z = false) (hψz : ψ.isFreeEvar z = false) (hzy : z ≠ y) {e : Valuation M} {a : M}
    (ha : Inh I σ a) :
    (sExists y S (sExists z S (sAnd (.evar z) (sAnd (sTop S)
        (sOr S (sIn S S (.evar z) X) (sAnd (sIn S S (.evar z) (.evar y)) ψ)))))).interpret I e a ↔
      (sOr S X (sExists y S (sAnd (.evar y) ψ))).interpret I e a := by
  rw [exS_iff hD hS, interp_sOr, interp_inhOf_of (hS.den e), exS_iff hD hS]
  have body : ∀ v w, Inh I σ w →
      ((sAnd (.evar z) (sAnd (sTop S) (sOr S (sIn S S (.evar z) X)
          (sAnd (sIn S S (.evar z) (.evar y)) ψ)))).interpret I (upd (upd e y v) z w) a ↔
        a = w ∧ (X.interpret I e w ∨ (w = v ∧ ψ.interpret I (upd e y v) a))) := by
    intro v w hw
    have hx : Inh I σ ((upd (upd e y v) z w).evalEvar z) := by rw [upd_same]; exact hw
    have hzw : (upd (upd e y v) z w).evalEvar z = w := upd_same ..
    simp only [interp_sAnd, interp_sOr, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar,
      interp_inhOf_of (hS.den _), Function.update_same, Function.update_noteq (Ne.symm hzy)]
    rw [upd_irrel hψz (upd e y v) w a, upd_irrel hXz (upd e y v) w w, upd_irrel hXy e v w]
    constructor
    · rintro ⟨h1, -, -, h⟩
      refine ⟨h1, ?_⟩
      rcases h with ⟨h, -⟩ | ⟨⟨h, -⟩, h'⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, h'⟩
    · rintro ⟨h1, h⟩
      refine ⟨h1, ha, ha, ?_⟩
      rcases h with h | ⟨h, h'⟩
      · exact Or.inl ⟨h, ha⟩
      · exact Or.inr ⟨⟨h, ha⟩, h'⟩
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨w, hw, h⟩ := (exS_iff hD hS).mp h
    obtain ⟨h1, h⟩ := (body v w hw).mp h
    refine ⟨ha, ?_⟩
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl (h1 ▸ h)
    · refine Or.inr ⟨v, hv, ?_⟩
      rw [interp_sAnd, interp_evar]
      exact ⟨by rw [upd_same, h1, h], h'⟩
  · rintro ⟨-, h⟩
    rcases h with h | ⟨v, hv, h⟩
    · exact ⟨a, ha, (exS_iff hD hS).mpr ⟨a, ha, (body a a ha).mpr ⟨rfl, Or.inl h⟩⟩⟩
    · rw [interp_sAnd, interp_evar] at h
      have hav : a = v := by rw [h.1]; exact upd_same ..
      exact ⟨v, hv, (exS_iff hD hS).mpr ⟨a, ha, (body v a ha).mpr ⟨rfl, Or.inr ⟨hav, h.2⟩⟩⟩⟩

/-- **`∃z. z ∧ (⊤ ∧ (z ∈ X ∨ ∃y'. (z ∈ y' ∧ ψ')))` is `X ∨ ∃y. (y ∧ ψ)`** at an element of S: z
not free in X, z another variable than y', and ψ' with y' at an element holding what ψ holds with
y at it (`hren`: ψ with its binder renamed). -/
theorem inOrEx_body {y y' z : EVar} {S X ψ ψ' : P} {σ : M} (hS : SortAt I S σ)
    (hXz : X.isFreeEvar z = false) (hzy : z ≠ y') {e : Valuation M}
    (hren : ∀ v w m, ψ'.interpret I (upd (upd e z w) y' v) m ↔ ψ.interpret I (upd e y v) m) {a : M}
    (ha : Inh I σ a) :
    (sExists z S (sAnd (.evar z) (sAnd (sTop S)
        (sOr S (sIn S S (.evar z) X) (sExists y' S (sAnd (sIn S S (.evar z) (.evar y')) ψ')))))).interpret I e a ↔
      (sOr S X (sExists y S (sAnd (.evar y) ψ))).interpret I e a := by
  rw [exS_iff hD hS, interp_sOr, interp_inhOf_of (hS.den e), exS_iff hD hS]
  have body : ∀ w, Inh I σ w →
      ((sAnd (.evar z) (sAnd (sTop S) (sOr S (sIn S S (.evar z) X)
          (sExists y' S (sAnd (sIn S S (.evar z) (.evar y')) ψ'))))).interpret I (upd e z w) a ↔
        a = w ∧ (X.interpret I e w ∨ ∃ v, Inh I σ v ∧ w = v ∧ ψ.interpret I (upd e y v) a)) := by
    intro w hw
    have hx : Inh I σ ((upd e z w).evalEvar z) := by rw [upd_same]; exact hw
    have hzw : (upd e z w).evalEvar z = w := upd_same ..
    have inner : ∀ v, Inh I σ v →
        ((sAnd (sIn S S (.evar z) (.evar y')) ψ').interpret I (upd (upd e z w) y' v) a ↔
          w = v ∧ ψ.interpret I (upd e y v) a) := by
      intro v _
      have hx' : Inh I σ ((upd (upd e z w) y' v).evalEvar z) := by rw [upd_ne _ hzy, upd_same]; exact hw
      have hz' : (upd (upd e z w) y' v).evalEvar z = w := by rw [upd_ne _ hzy, upd_same]
      have hy' : (upd (upd e z w) y' v).evalEvar y' = v := upd_same ..
      rw [interp_sAnd, sIn_var hD hc hS hS hx', interp_evar, hz', hy', hren]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ha⟩, h.2⟩⟩
    rw [interp_sAnd, interp_sAnd, interp_sOr, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar,
      interp_inhOf_of (hS.den _), exS_iff hD hS, hzw, upd_irrel hXz e w w]
    constructor
    · rintro ⟨h1, -, -, h⟩
      refine ⟨h1, ?_⟩
      rcases h with ⟨h, -⟩ | ⟨v, hv, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, (inner v hv).mp h⟩
    · rintro ⟨h1, h⟩
      refine ⟨h1, ha, ha, ?_⟩
      rcases h with h | ⟨v, hv, h⟩
      · exact Or.inl ⟨h, ha⟩
      · exact Or.inr ⟨v, hv, (inner v hv).mpr h⟩
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨h1, h⟩ := (body w hw).mp h
    refine ⟨ha, ?_⟩
    rcases h with h | ⟨v, hv, h, h'⟩
    · exact Or.inl (h1 ▸ h)
    · refine Or.inr ⟨v, hv, ?_⟩
      rw [interp_sAnd, interp_evar]
      exact ⟨by rw [upd_same, h1, h], h'⟩
  · rintro ⟨-, h⟩
    refine ⟨a, ha, (body a ha).mpr ⟨rfl, ?_⟩⟩
    rcases h with h | ⟨v, hv, h⟩
    · exact Or.inl h
    · rw [interp_sAnd, interp_evar] at h
      have hav : a = v := by rw [h.1]; exact upd_same ..
      exact Or.inr ⟨v, hv, hav, h.2⟩

/-- **Two right sides that hold the same elements of the sort, at the valuations satisfying the
guards, give sentences that hold in the same interpretations.** -/
theorem eqnPat_congr_on {ws : List P} {r : EVar} {prem S F B B' : P} {σ : M} (hS : SortAt I S σ)
    (hr : sortGuard r ∈ ws) (hG : GuardsPred I ws)
    (h : ∀ (e : Valuation M) (m : M), At I ws r e m → ∀ a, Inh I σ a →
      (B.interpret I e a ↔ B'.interpret I e a)) :
    (I ⊧ᴵ eqnPat ws r prem S F B) ↔ (I ⊧ᴵ eqnPat ws r prem S F B') :=
  ⟨fun H => eqnPat_of hD hc hS.den hS.isSort hr hG fun e m hat hp a ha =>
      (eqnPat_at hD hc hS.den hS.isSort hr H hat hp a ha).trans (h e m hat a ha),
    fun H => eqnPat_of hD hc hS.den hS.isSort hr hG fun e m hat hp a ha =>
      (eqnPat_at hD hc hS.den hS.isSort hr H hat hp a ha).trans (h e m hat a ha).symm⟩

/-- The same with the `ensures` part beside each right side. -/
theorem eqnPat_of_body {ws : List P} {r : EVar} {prem S F B B' ens : P} {σ : M} (hS : SortAt I S σ)
    (hr : sortGuard r ∈ ws) (hG : GuardsPred I ws)
    (h : ∀ (e : Valuation M) (m : M), At I ws r e m → ∀ a, Inh I σ a →
      (B.interpret I e a ↔ B'.interpret I e a)) :
    (I ⊧ᴵ eqnPat ws r prem S F (sAnd B ens)) ↔ (I ⊧ᴵ eqnPat ws r prem S F (sAnd B' ens)) :=
  eqnPat_congr_on hD hc hS hr hG fun e m hat a ha => by rw [interp_sAnd, interp_sAnd, h e m hat a ha]

end

/-- A guard `x ∈ ⟦s⟧` of the sentence puts what x holds in the sort, where the guards hold. -/
theorem var_in {ws : List P} {r x : EVar} {s : P} {τ : M} (hs : SortAt I s τ)
    (hx : (x ∈∈ inhOf s) ∈ ws) {e : Valuation M} {m : M} (hat : At I ws r e m) : Inh I τ (e.evalEvar x) := by
  have := hat.1 _ hx
  rwa [interp_member hD, interp_inhOf_of (hs.den e)] at this

end

/-- **ψ with its binder y renamed to y' holds, with y' at an element, what ψ holds with y at it**:
`ψ.substEvar y y'` where the substitution captures nothing, y' is not free in ψ, and z is y, y' or
not free in ψ. -/
theorem renamed_body {y y' z : EVar} {ψ : P} (hs : Faithful.renOK y y' ψ = true) (hy' : ψ.isFreeEvar y' = false)
    (hz : ψ.isFreeEvar z = false ∨ z = y ∨ z = y') (e : Valuation M) (v w m : M) :
    (ψ.substEvar y (.evar y')).interpret I (upd (upd e z w) y' v) m ↔ ψ.interpret I (upd e y v) m := by
  rw [subf_xy_eq_eval_xey m _ (Faithful.renOK_sound hs)]
  refine only_free_var_relevant _ _ _ _ (fun k hk => ?_) (fun _ _ => rfl) m
  show Function.update (Function.update (Function.update e.evalEvar z w) y' v) y
      (Function.update (Function.update e.evalEvar z w) y' v y') k = Function.update e.evalEvar y v k
  rw [Function.update_same]
  by_cases hky : k = y
  · subst hky; rw [Function.update_same, Function.update_same]
  · rw [Function.update_noteq hky, Function.update_noteq hky]
    have hky' : k ≠ y' := by rintro rfl; rw [hy'] at hk; cases hk
    rw [Function.update_noteq hky']
    have hkz : k ≠ z := by
      rcases hz with hz | hz | hz
      · rintro rfl; rw [hz] at hk; cases hk
      · rw [hz]; exact hky
      · rw [hz]; exact hky'
    exact Function.update_noteq hkz _ _

/-- **A numbered sort's pattern denotes a sort**, in an interpretation with the signature's facts. -/
theorem sortAt_sig {c : Semantics} (F : TieFRSig.SigFacts c I) {s : Srt}
    (hs : s < nRegSorts + c.sortNames.length) (tbl : VarTable) :
    ∃ τ, SortAt I (trSort tbl (srtOf c s)) τ := by
  obtain ⟨τ, hτ, hd⟩ := F.sort hs
  exact ⟨τ, fun e a => hd tbl e a, hτ, by unfold srtOf; rw [Faithful.trSort_srt]; rfl⟩

/-- **The two directions between a sentence and Γ's item j**, from their holding in the same
interpretations among those with the signature's facts: the item is a consequence of the sentence
with definedness and `ΓSig c` (no other part of Γ), and `Γ c` entails the sentence. -/
theorem tie_of_iff {c : Semantics} (hcore : c.coreOK = true) {j : Nat} {text item : P}
    (hitem : (TiePair.gammaPats c)[j]? = some item)
    (hiff : ∀ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}, TieFRSig.SigFacts c I →
      TieFRSig.TermsInSortNI c I → ((I ⊧ᴵ item) ↔ (I ⊧ᴵ text))) :
    (∀ it, (Faithful.fnItems c)[j]? = some it → (TiePair.Texts [text] ∪ Faithful.ΓSig c) ⊧ it.pat) ∧
      (Faithful.Γ c ⊧ text) := by
  constructor
  · intro it hit M _ I hI
    have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
    obtain ⟨F, hTS⟩ := TieFRSig.sig_of_core hcore hD fun φ hφ => hI φ (Or.inr hφ)
    have h : (TiePair.gammaPats c)[j]? = some it.pat := by
      unfold TiePair.gammaPats; rw [List.getElem?_map, hit]; rfl
    rw [hitem] at h
    rw [← Option.some.inj h]
    exact (hiff F hTS).mpr (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
  · intro M _ I hI
    have hD : DefOK I := Faithful.defOK hI
    obtain ⟨F, hTS⟩ := TieFRSig.sig_of_core hcore hD
      fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hφ))))))
    unfold TiePair.gammaPats at hitem
    rw [List.getElem?_map] at hitem
    obtain ⟨it, hit, hp⟩ := Option.map_eq_some_iff.mp hitem
    refine (hiff F hTS).mp ?_
    rw [← hp]
    exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, List.mem_of_getElem? hit, rfl⟩))

/-! ## A binder its body does not hold, a variable alone, the top cut, `\ceil` under a binder, the cut
of alternatives -/

section More

/-- `ψ'`, read with z at an element b of S, is the sort where b is an element of T, and nothing
elsewhere: the condition of a clause whose right side is the variable z, against the pattern T it
cuts. -/
def CutOf (I : Interpretation KoreAML.Sym M) (σ : M) (e : Valuation M) (z : EVar) (ψ' T : P) : Prop :=
  ∀ b, Inh I σ b → ∀ m, Inh I σ m → (ψ'.interpret I (upd e z b) m ↔ T.interpret I e b)

/-- A disjunction of cuts is the cut of the disjunction. -/
theorem cutOf_or {z : EVar} {S ψ₁ ψ₂ T₁ T₂ : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M}
    (h₁ : CutOf I σ e z ψ₁ T₁) (h₂ : CutOf I σ e z ψ₂ T₂) : CutOf I σ e z (sOr S ψ₁ ψ₂) (sOr S T₁ T₂) := by
  intro b hb m hm
  rw [interp_sOr, interp_sOr, interp_inhOf_of (hS.den _), interp_inhOf_of (hS.den _), h₁ b hb m hm, h₂ b hb m hm]
  exact ⟨fun h => ⟨hb, h.2⟩, fun h => ⟨hm, h.2⟩⟩

/-- `¬ψ'` and `¬ψ` hold an element together where ψ' and ψ do. -/
theorem sNot_congr_body {S ψ' ψ : P} {e : Valuation M} {a : M}
    (h : ψ'.interpret I e a ↔ ψ.interpret I e a) :
    (sNot S ψ').interpret I e a ↔ (sNot S ψ).interpret I e a := by
  rw [interp_sNot, interp_sNot, h]

section
variable (hD : DefOK I)
include hD

/-- **A binder whose variable the body does not hold: `∃x:S. φ` is φ** at an element of S (which
is the element of S the binder asks for). -/
theorem exVac_body {x : EVar} {S φ : P} {σ : M} (hS : SortAt I S σ) (hφ : φ.isFreeEvar x = false)
    {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sExists x S φ).interpret I e a ↔ φ.interpret I e a := by
  rw [exS_iff hD hS]
  exact ⟨fun ⟨b, _, h⟩ => (upd_irrel hφ e b a).mp h, fun h => ⟨a, ha, (upd_irrel hφ e a a).mpr h⟩⟩

/-- **`∃x:S. x` holds every element of S.** -/
theorem exVar_body {x : EVar} {S : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M}
    (ha : Inh I σ a) : (sExists x S (.evar x)).interpret I e a := by
  rw [exS_iff hD hS]
  refine ⟨a, ha, ?_⟩
  simp only [interp_evar, Function.update_same]

/-- **`∃x:S. x ∧ ⊤` holds every element of S.** -/
theorem exVarTop_body {x : EVar} {S : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M}
    (ha : Inh I σ a) : (sExists x S (sAnd (.evar x) (sTop S))).interpret I e a := by
  rw [exS_iff hD hS]
  refine ⟨a, ha, ?_⟩
  simp only [interp_sAnd, sTop_iff hD hS, interp_evar, Function.update_same]
  exact ⟨trivial, ha⟩

/-- **`∃z. z ∧ (⊤ ∧ ψ')` is T** at an element of S, where ψ' is T's cut at z. -/
theorem cutOf_body {z : EVar} {S ψ' T : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M}
    (h : CutOf I σ e z ψ' T) {a : M} (ha : Inh I σ a) :
    (sExists z S (sAnd (.evar z) (sAnd (sTop S) ψ'))).interpret I e a ↔ T.interpret I e a := by
  rw [exS_iff hD hS]
  constructor
  · rintro ⟨b, hb, h'⟩
    simp only [interp_sAnd, sTop_iff hD hS, interp_evar, Function.update_same] at h'
    obtain ⟨h1, -, h3⟩ := h'
    subst h1
    exact (h _ hb _ ha).mp h3
  · intro hT
    refine ⟨a, ha, ?_⟩
    simp only [interp_sAnd, sTop_iff hD hS, interp_evar, Function.update_same]
    exact ⟨trivial, ha, (h a ha a ha).mpr hT⟩

section
variable [Inhabited M] (hc : I ⊧ᴵ ceilDefItem.pat)
include hc

/-- A membership of z in a pattern that does not hold z is the pattern's cut at z. -/
theorem cutOf_mem {z : EVar} {S t : P} {σ : M} (hS : SortAt I S σ) (ht : t.isFreeEvar z = false)
    {e : Valuation M} : CutOf I σ e z (sIn S S (.evar z) t) t := by
  intro b hb m hm
  have hx : Inh I σ ((upd e z b).evalEvar z) := by rw [upd_same]; exact hb
  rw [sIn_var hD hc hS hS hx, upd_same]
  exact ⟨fun h => (upd_irrel ht e b b).mp h.1, fun h => ⟨(upd_irrel ht e b b).mpr h, hm⟩⟩

/-- **`∃z. z ∧ (⊤ ∧ (z ∈ X ∧ ψ'))` is `X ∧ ψ`** at an element a of S: z free in neither X nor ψ',
and ψ' and ψ hold a together (the same pattern, or one whose cut the reader keeps under a binder). -/
theorem topCut_body {z : EVar} {S X ψ' ψ : P} {σ : M} (hS : SortAt I S σ) (hX : X.isFreeEvar z = false)
    (hψ : ψ'.isFreeEvar z = false) {e : Valuation M} {a : M} (ha : Inh I σ a)
    (h : ψ'.interpret I e a ↔ ψ.interpret I e a) :
    (sExists z S (sAnd (.evar z) (sAnd (sTop S) (sAnd (sIn S S (.evar z) X) ψ')))).interpret I e a ↔
      (sAnd X ψ).interpret I e a := by
  rw [exS_iff hD hS, interp_sAnd]
  constructor
  · rintro ⟨b, hb, h'⟩
    have hx : Inh I σ ((upd e z b).evalEvar z) := by rw [upd_same]; exact hb
    simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar, Function.update_same] at h'
    obtain ⟨h1, -, ⟨h3, -⟩, h4⟩ := h'
    exact ⟨(upd_irrel hX e b a).mp (h1 ▸ h3), h.mp ((upd_irrel hψ e b a).mp h4)⟩
  · rintro ⟨h1, h2⟩
    have hx : Inh I σ ((upd e z a).evalEvar z) := by rw [upd_same]; exact ha
    refine ⟨a, ha, ?_⟩
    simp only [interp_sAnd, sTop_iff hD hS, sIn_var hD hc hS hS hx, interp_evar, Function.update_same]
    exact ⟨trivial, ha, ⟨(upd_irrel hX e a a).mpr h1, ha⟩, (upd_irrel hψ e a a).mpr (h.mpr h2)⟩

/-- **`∃y. ⌈y⌉ ∧ (y ∈ t ∧ y ∈ u)` is `⌈t ∧ u⌉`** at an element of S, y free in neither, where the
elements of `t ∧ u` lie in S. -/
theorem ceilEx_body {y : EVar} {S t u : P} {σ : M} (hS : SortAt I S σ) (ht : t.isFreeEvar y = false)
    (hu : u.isFreeEvar y = false) {e : Valuation M}
    (hin : ∀ b, t.interpret I e b → u.interpret I e b → Inh I σ b) {a : M} (ha : Inh I σ a) :
    (sExists y S (sAnd (sCeil S S (.evar y)) (sAnd (sIn S S (.evar y) t) (sIn S S (.evar y) u)))).interpret I e a ↔
      (sCeil S S (sAnd t u)).interpret I e a := by
  rw [exS_iff hD hS,
    interp_sCeil hD hc (hS.den e) (hS.den e) hS.isSort hS.isSort
      (fun b hb => hin b (interp_sAnd.mp hb).1 (interp_sAnd.mp hb).2) a]
  constructor
  · rintro ⟨b, hb, h⟩
    have hx : Inh I σ ((upd e y b).evalEvar y) := by rw [upd_same]; exact hb
    simp only [interp_sAnd, sIn_var hD hc hS hS hx, Function.update_same] at h
    obtain ⟨-, ⟨h3, -⟩, h4, -⟩ := h
    exact ⟨⟨b, interp_sAnd.mpr ⟨(upd_irrel ht e b b).mp h3, (upd_irrel hu e b b).mp h4⟩⟩, ha⟩
  · rintro ⟨⟨b, hb⟩, -⟩
    rw [interp_sAnd] at hb
    have hbσ : Inh I σ b := hin b hb.1 hb.2
    have hx : Inh I σ ((upd e y b).evalEvar y) := by rw [upd_same]; exact hbσ
    refine ⟨b, hbσ, ?_⟩
    simp only [interp_sAnd, sIn_var hD hc hS hS hx, Function.update_same]
    refine ⟨?_, ⟨(upd_irrel ht e b b).mpr hb.1, ha⟩, (upd_irrel hu e b b).mpr hb.2, ha⟩
    rw [interp_sCeil hD hc (hS.den _) (hS.den _) hS.isSort hS.isSort
      (fun c hc' => by rw [interp_evar] at hc'; rw [hc']; exact hx) a]
    exact ⟨⟨_, interp_evar.mpr rfl⟩, ha⟩

/-- **`∃c:S. (c ∧ c = y)` holds the element y holds, and nothing else**, y holding an element of S
and c another variable: an element is in it where it is the binder's element b and b is y's. -/
theorem exEqVar_body {y c : EVar} {S : P} {σ : M} (hS : SortAt I S σ) (hcy : c ≠ y) {e : Valuation M}
    (hy : Inh I σ (e.evalEvar y)) (m : M) :
    (sExists c S (sAnd (.evar c) (sEquals S S (.evar c) (.evar y)))).interpret I e m ↔ m = e.evalEvar y := by
  rw [exS_iff hD hS]
  constructor
  · rintro ⟨b, hb, h⟩
    rw [interp_sAnd, interp_evar,
      interp_sEquals hD hc (hS.den _) (hS.den _) hS.isSort hS.isSort m] at h
    obtain ⟨h1, -, h3⟩ := h
    have hmb : m = b := by rw [h1]; exact upd_same e c b
    have := (h3 b hb).mp (interp_evar.mpr (upd_same e c b).symm)
    rw [interp_evar, upd_ne e hcy.symm b] at this
    exact hmb.trans this
  · intro hm
    refine ⟨m, hm ▸ hy, ?_⟩
    rw [interp_sAnd, interp_evar,
      interp_sEquals hD hc (hS.den _) (hS.den _) hS.isSort hS.isSort m]
    refine ⟨(upd_same e c m).symm, hm ▸ hy, fun a _ => ?_⟩
    rw [interp_evar, interp_evar, upd_same, upd_ne e hcy.symm m, hm]

/-- **`∃z. h(z) ∧ ⊤` is `∃y. h(∃c. (c ∧ c = y))`** at an element of S: the binder c equated with the
variable y of the binder around it holds y's element, so both sides hold what h gives at an element
of S. The variables are free in h, and c is not y. -/
theorem nestedApp_body {y c z : EVar} {S hd : P} {σ : M} (hS : SortAt I S σ) (hcy : c ≠ y)
    (hhy : hd.isFreeEvar y = false) (hhz : hd.isFreeEvar z = false) {e : Valuation M} {a : M}
    (ha : Inh I σ a) :
    (sExists z S (sAnd (hd ⬝ .evar z) (sTop S))).interpret I e a ↔
      (sExists y S (hd ⬝ sExists c S (sAnd (.evar c) (sEquals S S (.evar c) (.evar y))))).interpret I e a := by
  rw [exS_iff hD hS, exS_iff hD hS]
  refine exists_congr fun b => and_congr_right fun hb => ?_
  have hyb : Inh I σ ((upd e y b).evalEvar y) := by rw [upd_same]; exact hb
  rw [interp_sAnd, sTop_iff hD hS, interp_app, interp_app]
  constructor
  · rintro ⟨⟨f, w, hf, hw, happ⟩, -⟩
    rw [interp_evar, upd_same] at hw
    refine ⟨f, w, (upd_irrel hhy e b f).mpr ((upd_irrel hhz e b f).mp hf), ?_, happ⟩
    rw [exEqVar_body hD hc hS hcy hyb, upd_same]
    exact hw
  · rintro ⟨f, w, hf, hw, happ⟩
    rw [exEqVar_body hD hc hS hcy hyb, upd_same] at hw
    refine ⟨⟨f, w, (upd_irrel hhz e b f).mpr ((upd_irrel hhy e b f).mp hf), ?_, happ⟩, ha⟩
    rw [interp_evar, upd_same]
    exact hw

end
end


end More

/-! ## The parts of an equation sentence, read off the KORE pattern, for the ties that state these
shapes of a text -/

/-- The premise of an equation sentence `\implies(prem, \equals(l, \and(r, ens)))`. -/
def premK : Kore.Pattern → Kore.Pattern
  | .implies _ p _ => p
  | p => p
/-- Its left side. -/
def lhsK : Kore.Pattern → Kore.Pattern
  | .implies _ _ (.equals _ _ l _) => l
  | p => p
/-- Its right side. -/
def rhsK : Kore.Pattern → Kore.Pattern
  | .implies _ _ (.equals _ _ _ (.and _ [r, _])) => r
  | p => p
/-- Its `ensures` part. -/
def ensK : Kore.Pattern → Kore.Pattern
  | .implies _ _ (.equals _ _ _ (.and _ [_, e])) => e
  | p => p
/-- The body of an `\exists`. -/
def exBK : Kore.Pattern → Kore.Pattern
  | .exist _ _ b => b
  | p => p
/-- The variable an `\exists` binds, in the table. -/
def exVK (tbl : VarTable) : Kore.Pattern → EVar
  | .exist _ x _ => tbl.ev (evarKey x)
  | _ => ⟨0⟩
/-- The operand i of a conjunction, a disjunction or an application. -/
def argK (i : Nat) : Kore.Pattern → Kore.Pattern
  | .and _ ps => ps.getD i (.string "")
  | .or _ ps => ps.getD i (.string "")
  | .app _ _ ps => ps.getD i (.string "")
  | p => p
/-- The operand of a `\ceil`. -/
def ceilK : Kore.Pattern → Kore.Pattern
  | .ceil _ _ p => p
  | p => p
/-- The left operand of an `\equals`. -/
def eqLK : Kore.Pattern → Kore.Pattern
  | .equals _ _ l _ => l
  | p => p
/-- The right operand of an `\equals`. -/
def eqRK : Kore.Pattern → Kore.Pattern
  | .equals _ _ _ r => r
  | p => p
/-- The operand of a `\not`. -/
def notK : Kore.Pattern → Kore.Pattern
  | .not _ p => p
  | p => p
/-- The name of an application's symbol. -/
def headK : Kore.Pattern → String
  | .app h _ _ => h.ident.name
  | _ => ""

/-- A numbered sort's pattern, by its name, denotes a sort. -/
theorem sortAtN {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M} (F : TieFRSig.SigFacts c I)
    {s : Srt} {n : String} (hn : c.sortName s = n) (hs : s < nRegSorts + c.sortNames.length) (tbl : VarTable) :
    ∃ τ, SortAt I (trSort tbl (srt n)) τ := by
  obtain ⟨τ, h⟩ := sortAt_sig F hs tbl
  have he : srtOf c s = srt n := by unfold srtOf; rw [hn]
  exact ⟨τ, he ▸ h⟩

end TieExClause

end KCore
