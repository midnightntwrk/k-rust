/-
  KCore. Moving a sorted `\exists` out of an application context, an `\and` and an `\or`, and an
  element variable beside a pattern in an `\and`, on KoreAML patterns and on the translation `tr`
  of KORE patterns. Each holds in every interpretation where definedness is definedness (`DefOK`)
  and at every valuation.

  - `app_exists`: `C[∃x:s. φ]` is `∃x:s. C[φ]` for a context C of applications no side pattern of
    which reads x. Nothing is asked of the sort s: where it has no element both sides are empty.
  - `and_exists`: `(∃x:s. φ) ∧ ψ` is `∃x:s. (φ ∧ ψ)` where ψ does not read x; no premise on s.
  - `or_exists`: `(∃x:s. φ) ∨ ψ` is `∃x:s. (φ ∨ ψ)` where ψ and the sort of the `\or` do not read
    x and **s has an element**; `or_exists_only_if`: without an element of s the right side is
    empty, so the premise is needed wherever ψ has an element of the `\or`'s sort.
  - `var_and_mem`: `x ∧ φ` is `x ∧ (x ∈ φ)` for an element variable x in the two sorts of the
    `\in`.
  - `tr_app_exists`, `tr_and_exists`, `tr_or_exists`, `tr_var_and_mem`, `tr_mem_and`: the same at
    the translation of the KORE patterns, both sides translated in one context `ctx` (one table of
    variables). `KoreAML.denB t` is `tr ⟨tableOf [] t, []⟩ t`, whose table is the pattern's own:
    the two sides of a law are numbered by two tables, so the laws are stated at a table given.
-/
import KcoreSpec.CutIdentity

set_option autoImplicit false

namespace KoreAML

open ML

variable {M : Type} {I : Interpretation Sym M}

/-- The valuation e with x at a. -/
abbrev updE (e : Valuation M) (x : EVar) (a : M) : Valuation M :=
  ⟨Function.update e.evalEvar x a, e.evalSvar⟩

/-- A sorted `\exists` at an element: some element a of the sort (read with x at a) has the body
at it. -/
theorem interp_sExists_elem (hD : DefOK I) {e : Valuation M} {x : EVar} {s φ : P} {m : M} :
    (sExists x s φ).interpret I e m ↔
      ∃ a, (inhOf s).interpret I (updE e x a) a ∧ φ.interpret I (updE e x a) m := by
  rw [interp_sExists]
  refine exists_congr fun a => and_congr_left' ?_
  rw [interp_member hD]
  show (inhOf s).interpret I (updE e x a) (Function.update e.evalEvar x a x) ↔ _
  rw [Function.update_same]

/-- **`C[∃x:s. φ] = ∃x:s. C[φ]`** for a context of applications whose side patterns do not read
x. No premise on the sort s. -/
theorem app_exists (hD : DefOK I) (x : EVar) (s φ : P) : ∀ (C : CutCtx), C.Fresh I x →
    ∀ (e : Valuation M) (m : M),
    (C.fill (sExists x s φ)).interpret I e m ↔ (sExists x s (C.fill φ)).interpret I e m
  | .hole, _, _, _ => Iff.rfl
  | .fn C ψ, hC, e, m => by
    rw [interp_sExists_elem hD]
    show (C.fill (sExists x s φ) ⬝ ψ).interpret I e m ↔ ∃ a, _ ∧ (C.fill φ ⬝ ψ).interpret I _ m
    rw [interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨a, ha, hpa⟩ := (interp_sExists_elem hD).mp ((app_exists hD x s φ C hC.1 e p).mp hp)
      exact ⟨a, ha, interp_app.mpr ⟨p, b, hpa, (hC.2 e a b).mpr hb, hpb⟩⟩
    · rintro ⟨a, ha, hm⟩
      obtain ⟨p, b, hpa, hb, hpb⟩ := interp_app.mp hm
      exact ⟨p, b, (app_exists hD x s φ C hC.1 e p).mpr ((interp_sExists_elem hD).mpr ⟨a, ha, hpa⟩),
        (hC.2 e a b).mp hb, hpb⟩
  | .arg ψ C, hC, e, m => by
    rw [interp_sExists_elem hD]
    show (ψ ⬝ C.fill (sExists x s φ)).interpret I e m ↔ ∃ a, _ ∧ (ψ ⬝ C.fill φ).interpret I _ m
    rw [interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨a, ha, hba⟩ := (interp_sExists_elem hD).mp ((app_exists hD x s φ C hC.2 e b).mp hb)
      exact ⟨a, ha, interp_app.mpr ⟨p, b, (hC.1 e a p).mpr hp, hba, hpb⟩⟩
    · rintro ⟨a, ha, hm⟩
      obtain ⟨p, b, hp, hba, hpb⟩ := interp_app.mp hm
      exact ⟨p, b, (hC.1 e a p).mp hp,
        (app_exists hD x s φ C hC.2 e b).mpr ((interp_sExists_elem hD).mpr ⟨a, ha, hba⟩), hpb⟩

/-- **`(∃x:s. φ) ∧ ψ = ∃x:s. (φ ∧ ψ)`** where ψ does not read x. No premise on the sort s. -/
theorem and_exists (hD : DefOK I) (x : EVar) (s φ ψ : P) (hψ : NoReadCut I x ψ)
    (e : Valuation M) (m : M) :
    (sAnd (sExists x s φ) ψ).interpret I e m ↔ (sExists x s (sAnd φ ψ)).interpret I e m := by
  rw [interp_sAnd, interp_sExists_elem hD, interp_sExists_elem hD]
  constructor
  · rintro ⟨⟨a, ha, hφ⟩, h⟩
    exact ⟨a, ha, interp_sAnd.mpr ⟨hφ, (hψ e a m).mpr h⟩⟩
  · rintro ⟨a, ha, h⟩
    obtain ⟨hφ, h⟩ := interp_sAnd.mp h
    exact ⟨⟨a, ha, hφ⟩, (hψ e a m).mp h⟩

/-- **`(∃x:s. φ) ∨ ψ = ∃x:s. (φ ∨ ψ)`** where ψ and the sort S of the `\or` do not read x and the
sort s has an element (`hs`). -/
theorem or_exists (hD : DefOK I) (x : EVar) (S s φ ψ : P) (hψ : NoReadCut I x ψ)
    (hS : NoReadCut I x S) (e : Valuation M) (hs : ∃ a, (inhOf s).interpret I (updE e x a) a) (m : M) :
    (sOr S (sExists x s φ) ψ).interpret I e m ↔ (sExists x s (sOr S φ ψ)).interpret I e m := by
  have hSi : ∀ a, (inhOf S).interpret I (updE e x a) m ↔ (inhOf S).interpret I e m := fun a => by
    rw [interp_inhOf, interp_inhOf]
    exact exists_congr fun σ => and_congr_left' (hS e a σ)
  rw [interp_sOr, interp_sExists_elem hD, interp_sExists_elem hD]
  constructor
  · rintro ⟨hi, ⟨a, ha, hφ⟩ | h⟩
    · exact ⟨a, ha, interp_sOr.mpr ⟨(hSi a).mpr hi, .inl hφ⟩⟩
    · obtain ⟨a, ha⟩ := hs
      exact ⟨a, ha, interp_sOr.mpr ⟨(hSi a).mpr hi, .inr ((hψ e a m).mpr h)⟩⟩
  · rintro ⟨a, ha, h⟩
    obtain ⟨hi, hφ | h⟩ := interp_sOr.mp h
    · exact ⟨(hSi a).mp hi, .inl ⟨a, ha, hφ⟩⟩
    · exact ⟨(hSi a).mp hi, .inr ((hψ e a m).mp h)⟩

/-- **The premise of `or_exists` is needed**: where the sort s has no element, `∃x:s. (φ ∨ ψ)` is
empty, and `(∃x:s. φ) ∨ ψ` holds every element of ψ in the sort S. -/
theorem or_exists_only_if (hD : DefOK I) (x : EVar) (S s φ ψ : P) (e : Valuation M)
    (hs : ¬ ∃ a, (inhOf s).interpret I (updE e x a) a) (m : M) :
    ¬ (sExists x s (sOr S φ ψ)).interpret I e m ∧
      ((sOr S (sExists x s φ) ψ).interpret I e m ↔
        (inhOf S).interpret I e m ∧ ψ.interpret I e m) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := (interp_sExists_elem hD).mp h
    exact hs ⟨a, ha⟩
  · rw [interp_sOr, interp_sExists_elem hD]
    constructor
    · rintro ⟨hi, ⟨a, ha, -⟩ | h⟩
      · exact absurd ⟨a, ha⟩ hs
      · exact ⟨hi, h⟩
    · rintro ⟨hi, h⟩; exact ⟨hi, .inr h⟩

/-- **`x ∧ φ = x ∧ (x ∈ φ)`** for an element variable x that is an element of the sort S of the
`\in`'s operands and of its result sort S'. -/
theorem var_and_mem [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S S' : P} {σ σ' : M}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (x : EVar) (hx : Inh I σ (e.evalEvar x)) (hx' : Inh I σ' (e.evalEvar x)) (φ : P) (m : M) :
    (sAnd (.evar x) φ).interpret I e m ↔
      (sAnd (.evar x) (sIn S S' (.evar x) φ)).interpret I e m := by
  rw [interp_sAnd, interp_sAnd, mem_iff_cut hD hc hS hS' hσ hσ' x hx]
  constructor
  · rintro ⟨hm, h⟩
    have hm' : m = e.evalEvar x := hm
    exact ⟨hm, by rw [← hm']; exact h, by rw [hm']; exact hx'⟩
  · rintro ⟨hm, h, -⟩
    have hm' : m = e.evalEvar x := hm
    exact ⟨hm, by rw [hm']; exact h⟩

/-! ## At the translation of KORE patterns -/

/-- **`tr` of `K[\exists{r}(x, φ)]` is `tr` of `\exists{r'}(x, K[φ])`** for a KORE context K of
applications, no head an alias, whose side patterns do not read x, at every result sorts r and r'
of the two binders (the translation of `\exists` does not read its result sort). -/
theorem tr_app_exists (hD : DefOK I) (ctx : Ctx) (r r' : Kore.KSort) (x : Kore.EVar) (φ : Kore.Pattern)
    (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (hx : K.SidesNoRead I ctx (ctx.vars.ev (evarKey x))) (e : Valuation M) (m : M) :
    (tr ctx (K.fill (.exist r x φ))).interpret I e m ↔
      (tr ctx (.exist r' x (K.fill φ))).interpret I e m := by
  rw [tr_cutCtx ctx _ K hK]
  simp only [tr]
  rw [tr_cutCtx ctx φ K hK]
  exact app_exists hD _ _ _ _ (KoreCutCtx.toCut_fresh K hx) e m

/-- `tr` of `\and{r}(\exists{r}(x, φ), ψ)` is `tr` of `\exists{r}(x, \and{r}(φ, ψ))` where ψ does
not read x. -/
theorem tr_and_exists (hD : DefOK I) (ctx : Ctx) (r : Kore.KSort) (x : Kore.EVar) (φ ψ : Kore.Pattern)
    (hψ : NoReadCut I (ctx.vars.ev (evarKey x)) (tr ctx ψ)) (e : Valuation M) (m : M) :
    (tr ctx (.and r [.exist r x φ, ψ])).interpret I e m ↔
      (tr ctx (.exist r x (.and r [φ, ψ]))).interpret I e m := by
  simp only [tr, trAndList]
  exact and_exists hD _ _ _ _ hψ e m

/-- `tr` of `\or{r}(\exists{r}(x, φ), ψ)` is `tr` of `\exists{r}(x, \or{r}(φ, ψ))` where ψ and
the sort r do not read x and x's sort has an element. -/
theorem tr_or_exists (hD : DefOK I) (ctx : Ctx) (r : Kore.KSort) (x : Kore.EVar) (φ ψ : Kore.Pattern)
    (hψ : NoReadCut I (ctx.vars.ev (evarKey x)) (tr ctx ψ))
    (hr : NoReadCut I (ctx.vars.ev (evarKey x)) (trSort ctx.vars r)) (e : Valuation M)
    (hs : ∃ a, (inhOf (trSort ctx.vars x.sort)).interpret I (updE e (ctx.vars.ev (evarKey x)) a) a)
    (m : M) :
    (tr ctx (.or r [.exist r x φ, ψ])).interpret I e m ↔
      (tr ctx (.exist r x (.or r [φ, ψ]))).interpret I e m := by
  simp only [tr, trOrList]
  exact or_exists hD _ _ _ _ _ hψ hr e hs m

/-- `tr` of `\and{s}(x, φ)` is `tr` of `\and{s}(x, \in{s,s'}(x, φ))` for a variable x that is an
element of the sorts s and s'. -/
theorem tr_var_and_mem [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (ctx : Ctx)
    (s s' : Kore.KSort) (x : Kore.EVar) (φ : Kore.Pattern) {e : Valuation M} {σ σ' : M}
    (hS : ∀ a, (trSort ctx.vars s).interpret I e a ↔ a = σ)
    (hS' : ∀ a, (trSort ctx.vars s').interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hx : Inh I σ (e.evalEvar (ctx.vars.ev (evarKey x))))
    (hx' : Inh I σ' (e.evalEvar (ctx.vars.ev (evarKey x)))) (m : M) :
    (tr ctx (.and s [.var (.evar x), φ])).interpret I e m ↔
      (tr ctx (.and s [.var (.evar x), .in s s' (.var (.evar x)) φ])).interpret I e m := by
  simp only [tr, trAndList]
  exact var_and_mem hD hc hS hS' hσ hσ' _ hx hx' _ m

/-- `tr` of `\in{s,s'}(z, \and{s}(φ, ψ))` is `tr` of `\and{s'}(\in{s,s'}(z, φ), \in{s,s'}(z, ψ))`
for a variable z that is an element of the sort s. -/
theorem tr_mem_and [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (ctx : Ctx)
    (s s' : Kore.KSort) (z : Kore.EVar) (φ ψ : Kore.Pattern) {e : Valuation M} {σ σ' : M}
    (hS : ∀ a, (trSort ctx.vars s).interpret I e a ↔ a = σ)
    (hS' : ∀ a, (trSort ctx.vars s').interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hz : Inh I σ (e.evalEvar (ctx.vars.ev (evarKey z)))) (m : M) :
    (tr ctx (.in s s' (.var (.evar z)) (.and s [φ, ψ]))).interpret I e m ↔
      (tr ctx (.and s' [.in s s' (.var (.evar z)) φ, .in s s' (.var (.evar z)) ψ])).interpret I e m := by
  simp only [tr, trAndList]
  exact mem_and hD hc hS hS' hσ hσ' _ hz _ _ m

end KoreAML
