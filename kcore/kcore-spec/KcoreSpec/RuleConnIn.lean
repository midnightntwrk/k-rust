/-
  KCore. A connective at a position under applications, read with the position cut and the
  membership of the cut variable in the connective written as a predicate.

  - `MemOf … q φ`: the predicate q is the membership of the element of x, an element of the sort
    S, in φ: at an element a of S for x, q holds (everywhere in the sort C) exactly where a is one
    of φ's elements. `MemOf.in'`: `\in{S,C}(x, t)` is the membership in t. `MemOf.or`, `MemOf.and`,
    `MemOf.not`: the connective at C of memberships is the membership in the connective at S of
    the operands. `MemOf.top`, `MemOf.bot`: `\top{C}` is the membership in `\top{S}` and
    `\bottom{C}` the membership in `\bottom{S}`, where neither sort pattern holds the variable
    that `\top` binds (`interp_sTop`).
  - `rule_cut_mem`: `\exists{C}(Z:S, \and{C}(K[Z], E, q))` is `\and{C}(K[φ], E)`, where q is the
    membership of Z in φ, definedness is definedness, S denotes a sort, every element of φ is in S
    and every element of `K[φ]` in C, no head on the path is an alias, and the side patterns, φ, E
    and S do not read Z.
  - `or_inh`, `not_inh`: every element of `\or{S}(t, u)` and of `\not{S}(t)` is in S.
  - `rule_and_pred`: `K[\and{S}(t, P)]` is `\and{C}(K[t], P')`, where P is a predicate at S and P'
    one at C of one truth value p (each the whole sort or nothing), every element of t is in S and
    every element of `K[t]` in C, and no head on the path is an alias. `cutCtx_fill_and_pred`: the
    same over AML's application contexts, P being p at every element of t.
  - `rule_and_as`: `K[\and{S}(X, p)]` is `K[\and{S}(p, X)]`, the reading's `p #as X`
    (`cutCtx_fill_congr`: a context's filling depends only on the elements of what fills it).
  The left pattern is a rule's right side under its binder with `post` the membership
  (`ruleRight`), and, read from right to left, a rule's left side with `pre` the membership: for
  the left side the variable is one of the rule's, and `L[φ] ∧ E → •R` is, for Z not in R,
  `∀Z:S. (L[Z] ∧ E ∧ q → •R)`.
-/
import KcoreSpec.CutIdentity

set_option autoImplicit false

namespace KoreAML

open ML

variable {M : Type} {I : Interpretation Sym M}

/-- q is the membership of x's element, an element of the sort σ, in φ, at the sort σ'. -/
def MemOf (I : Interpretation Sym M) (ctx : Ctx) (e : Valuation M) (x : EVar) (σ σ' : M)
    (q φ : Kore.Pattern) : Prop :=
  ∀ a, Inh I σ a → ∀ m,
    (tr ctx q).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ↔
      ((tr ctx φ).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a ∧ Inh I σ' m)

section Mem
variable [Inhabited M]
  {ctx : Ctx} {e : Valuation M} {S C : Kore.KSort} {σ σ' : M} {z : Kore.EVar}
  (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
  (hCz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars C))
  (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
  (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
include hSz hCz hS hC

theorem MemOf.in' (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hσ : IsSort I σ) (hσ' : IsSort I σ') (t : Kore.Pattern) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.in S C (.var (.evar z)) t) t := by
  intro a ha m
  have hSu : ∀ b, (trSort ctx.vars S).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ :=
    fun b => (hSz e a b).trans (hS b)
  have hCu : ∀ b, (trSort ctx.vars C).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ' :=
    fun b => (hCz e a b).trans (hC b)
  have hup : (⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ : Valuation M).evalEvar
      (ctx.vars.ev (evarKey z)) = a := by simp
  have h := mem_iff_cut hD hc hSu hCu hσ hσ' (ctx.vars.ev (evarKey z)) (by rw [hup]; exact ha) (tr ctx t) m
  rw [hup] at h
  simpa only [tr] using h

omit [Inhabited M] in
theorem MemOf.or {q₁ q₂ φ₁ φ₂ : Kore.Pattern}
    (h₁ : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q₁ φ₁)
    (h₂ : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q₂ φ₂) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.or C [q₁, q₂]) (.or S [φ₁, φ₂]) := by
  intro a ha m
  have hSu : ∀ b, (trSort ctx.vars S).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ :=
    fun b => (hSz e a b).trans (hS b)
  have hCu : ∀ b, (trSort ctx.vars C).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ' :=
    fun b => (hCz e a b).trans (hC b)
  simp only [tr, trOrList]
  rw [interp_sOr, interp_sOr, interp_inhOf_of hSu, interp_inhOf_of hCu, h₁ a ha m, h₂ a ha m]
  constructor
  · rintro ⟨hm, h | h⟩
    · exact ⟨⟨ha, .inl h.1⟩, hm⟩
    · exact ⟨⟨ha, .inr h.1⟩, hm⟩
  · rintro ⟨⟨-, h | h⟩, hm⟩
    · exact ⟨hm, .inl ⟨h, hm⟩⟩
    · exact ⟨hm, .inr ⟨h, hm⟩⟩

omit [Inhabited M] hSz hCz hS hC in
theorem MemOf.and {q₁ q₂ φ₁ φ₂ : Kore.Pattern}
    (h₁ : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q₁ φ₁)
    (h₂ : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q₂ φ₂) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.and C [q₁, q₂]) (.and S [φ₁, φ₂]) := by
  intro a ha m
  simp only [tr, trAndList]
  rw [interp_sAnd, interp_sAnd, h₁ a ha m, h₂ a ha m]
  exact ⟨fun ⟨⟨h1, hm⟩, ⟨h2, _⟩⟩ => ⟨⟨h1, h2⟩, hm⟩, fun ⟨⟨h1, h2⟩, hm⟩ => ⟨⟨h1, hm⟩, ⟨h2, hm⟩⟩⟩

omit [Inhabited M] in
theorem MemOf.not {q φ : Kore.Pattern} (h : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q φ) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.not C q) (.not S φ) := by
  intro a ha m
  have hSu : ∀ b, (trSort ctx.vars S).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ :=
    fun b => (hSz e a b).trans (hS b)
  have hCu : ∀ b, (trSort ctx.vars C).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ' :=
    fun b => (hCz e a b).trans (hC b)
  simp only [tr]
  rw [interp_sNot, interp_sNot, interp_inhOf_of hSu, interp_inhOf_of hCu, h a ha m]
  exact ⟨fun ⟨hn, hm⟩ => ⟨⟨fun hφ => hn ⟨hφ, hm⟩, ha⟩, hm⟩, fun ⟨⟨hn, _⟩, hm⟩ => ⟨fun hφ => hn hφ.1, hm⟩⟩

omit [Inhabited M] in
theorem MemOf.top (hD : DefOK I) (hSt : (trSort ctx.vars S).isFreeEvar topVar = false)
    (hCt : (trSort ctx.vars C).isFreeEvar topVar = false) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.top C) (.top S) := by
  intro a ha m
  have hSu : ∀ b, (trSort ctx.vars S).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ :=
    fun b => (hSz e a b).trans (hS b)
  have hCu : ∀ b, (trSort ctx.vars C).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ' :=
    fun b => (hCz e a b).trans (hC b)
  simp only [tr]
  rw [interp_sTop hD hCt, interp_sTop hD hSt, interp_inhOf_of hSu, interp_inhOf_of hCu]
  exact ⟨fun hm => ⟨ha, hm⟩, fun h => h.2⟩

omit [Inhabited M] hSz hCz hS hC in
theorem MemOf.bot (hD : DefOK I) (hSt : (trSort ctx.vars S).isFreeEvar topVar = false)
    (hCt : (trSort ctx.vars C).isFreeEvar topVar = false) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.bottom C) (.bottom S) := by
  intro a _ m
  simp only [tr, sBot]
  rw [interp_sNot, interp_sNot, interp_sTop hD hCt, interp_sTop hD hSt]
  exact ⟨fun h => (h.1 h.2).elim, fun h => (h.1.1 h.1.2).elim⟩

end Mem

/-- Every element of `\or{S}(t, u)` is in S. -/
theorem or_inh {ctx : Ctx} {e : Valuation M} {S : Kore.KSort} {σ : M}
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ) (t u : Kore.Pattern) (a : M)
    (h : (tr ctx (.or S [t, u])).interpret I e a) : Inh I σ a := by
  simp only [tr, trOrList] at h
  exact (interp_inhOf_of hS).mp (interp_sOr.mp h).1

/-- Every element of `\not{S}(t)` is in S. -/
theorem not_inh {ctx : Ctx} {e : Valuation M} {S : Kore.KSort} {σ : M}
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ) (t : Kore.Pattern) (a : M)
    (h : (tr ctx (.not S t)).interpret I e a) : Inh I σ a := by
  simp only [tr] at h
  exact (interp_inhOf_of hS).mp (interp_sNot.mp h).2

/-- **The cut with the membership as a predicate**: `\exists{C}(Z:S, \and{C}(K[Z], E, q))` is
`\and{C}(K[φ], E)`, q the membership of Z in φ. -/
theorem rule_cut_mem (hD : DefOK I)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (z : Kore.EVar) (hz : z.sort = S) (φ q E : Kore.Pattern)
    (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ctx (ctx.vars.ev (evarKey z)))
    (hφ : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx φ))
    (hE : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx E))
    (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hq : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q φ)
    (hin : ∀ a, (tr ctx φ).interpret I e a → Inh I σ a)
    (hout : ∀ m, (tr ctx (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      (tr ctx (.and C [K.fill φ, E])).interpret I e m := by
  have hl : tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E, q])) =
      sExists (ctx.vars.ev (evarKey z)) (trSort ctx.vars S)
        (sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey z)))) (sAnd (tr ctx E) (tr ctx q))) := by
    simp only [tr, trAndList, hz]
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hr : tr ctx (.and C [K.fill φ, E]) = sAnd ((K.toCut ctx).fill (tr ctx φ)) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK]
  rw [tr_cutCtx ctx _ K hK] at hout
  rw [hl, hr, interp_sExists, interp_sAnd,
    cut_sem (ctx.vars.ev (evarKey z)) _ (K.toCut ctx) (KoreCutCtx.toCut_fresh K hsides) e m]
  generalize ctx.vars.ev (evarKey z) = x at *
  have hSu : ∀ a b, (trSort ctx.vars S).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ :=
    fun a b => (hSz e a b).trans (hS b)
  have hup : ∀ a, (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a :=
    fun a => by simp
  constructor
  · rintro ⟨a, hxa, hbody⟩
    simp only [interp_sAnd] at hbody
    obtain ⟨hCx, hE', hmem⟩ := hbody
    rw [interp_member hD, interp_inhOf_of (hSu a), hup a] at hxa
    exact ⟨⟨a, (hφ e a a).mp ((hq a hxa m).mp hmem).1, hCx⟩, (hE e a m).mp hE'⟩
  · rintro ⟨⟨a, hφa, hCx⟩, hEm⟩
    have hIa : Inh I σ a := hin a hφa
    have hm' : Inh I σ' m :=
      hout m ((cut_sem x _ (K.toCut ctx) (KoreCutCtx.toCut_fresh K hsides) e m).mpr ⟨a, hφa, hCx⟩)
    refine ⟨a, ?_, ?_⟩
    · rw [interp_member hD, interp_inhOf_of (hSu a), hup a]; exact hIa
    · simp only [interp_sAnd]
      exact ⟨hCx, (hE e a m).mpr hEm, (hq a hIa m).mpr ⟨(hφ e a a).mpr hφa, hm'⟩⟩

/-- A context's filling depends only on the elements of what fills it. -/
theorem cutCtx_fill_congr {φ ψ : P} {e : Valuation M} (h : ∀ a, φ.interpret I e a ↔ ψ.interpret I e a) :
    ∀ (C : CutCtx) (m : M), (C.fill φ).interpret I e m ↔ (C.fill ψ).interpret I e m
  | .hole, m => h m
  | .fn C χ, m => by
    show (C.fill φ ⬝ χ).interpret I e m ↔ (C.fill ψ ⬝ χ).interpret I e m
    simp only [interp_app, cutCtx_fill_congr h C]
  | .arg χ C, m => by
    show (χ ⬝ C.fill φ).interpret I e m ↔ (χ ⬝ C.fill ψ).interpret I e m
    simp only [interp_app, cutCtx_fill_congr h C]

/-- **A predicate conjoined in a context of applications floats out**: where ψ is p at every element
of φ, `C[φ ∧ ψ]` is `C[φ]` where p holds and nothing where it does not. -/
theorem cutCtx_fill_and_pred {φ ψ : P} {e : Valuation M} {p : Prop}
    (hψ : ∀ a, φ.interpret I e a → (ψ.interpret I e a ↔ p)) :
    ∀ (C : CutCtx) (m : M), (C.fill (sAnd φ ψ)).interpret I e m ↔ (C.fill φ).interpret I e m ∧ p
  | .hole, m => by
    show (sAnd φ ψ).interpret I e m ↔ φ.interpret I e m ∧ p
    rw [interp_sAnd]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hψ m h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hψ m h1).mpr h2⟩⟩
  | .fn C χ, m => by
    show (C.fill (sAnd φ ψ) ⬝ χ).interpret I e m ↔ (C.fill φ ⬝ χ).interpret I e m ∧ p
    simp only [interp_app, cutCtx_fill_and_pred hψ C]
    exact ⟨fun ⟨a, b, ⟨ha, hp⟩, hb, hab⟩ => ⟨⟨a, b, ha, hb, hab⟩, hp⟩,
      fun ⟨⟨a, b, ha, hb, hab⟩, hp⟩ => ⟨a, b, ⟨ha, hp⟩, hb, hab⟩⟩
  | .arg χ C, m => by
    show (χ ⬝ C.fill (sAnd φ ψ)).interpret I e m ↔ (χ ⬝ C.fill φ).interpret I e m ∧ p
    simp only [interp_app, cutCtx_fill_and_pred hψ C]
    exact ⟨fun ⟨a, b, ha, ⟨hb, hp⟩, hab⟩ => ⟨⟨a, b, ha, hb, hab⟩, hp⟩,
      fun ⟨⟨a, b, ha, hb, hab⟩, hp⟩ => ⟨a, b, ha, ⟨hb, hp⟩, hab⟩⟩

/-- **A predicate conjoined at a position under applications**: `K[\and{S}(t, P)]` is
`\and{C}(K[t], P')`, where P is p at every element of the sort σ and P' is p at every element of the
sort σ' (a predicate is the whole sort or nothing), every element of t is in σ, every element of
`K[t]` is in σ', and no head on the path is an alias. -/
theorem rule_and_pred (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (t P P' : Kore.Pattern) (e : Valuation M) {σ σ' : M} (p : Prop)
    (hP : ∀ a, Inh I σ a → ((tr ctx P).interpret I e a ↔ p))
    (hP' : ∀ m, Inh I σ' m → ((tr ctx P').interpret I e m ↔ p))
    (hin : ∀ a, (tr ctx t).interpret I e a → Inh I σ a)
    (hout : ∀ m, (tr ctx (K.fill t)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (K.fill (.and S [t, P]))).interpret I e m ↔
      (tr ctx (.and C [K.fill t, P'])).interpret I e m := by
  have hr : tr ctx (.and C [K.fill t, P']) = sAnd (tr ctx (K.fill t)) (tr ctx P') := by
    simp only [tr, trAndList]
  rw [hr, interp_sAnd]
  have hl : tr ctx (.and S [t, P]) = sAnd (tr ctx t) (tr ctx P) := by simp only [tr, trAndList]
  rw [tr_cutCtx ctx _ K hK, hl,
    cutCtx_fill_and_pred (fun a ha => hP a (hin a ha)) (K.toCut ctx) m, ← tr_cutCtx ctx _ K hK]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hP' m (hout m h1)).mpr h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hP' m (hout m h1)).mp h2⟩⟩

/-- **A variable conjoined at a position under applications**: `K[\and{S}(X, p)]` is
`K[\and{S}(p, X)]`, the pattern the reading's `p #as X` translates to, where no head on the path is an
alias. -/
theorem rule_and_as (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S : Kore.KSort) (x : Kore.EVar) (p : Kore.Pattern) (e : Valuation M) (m : M) :
    (tr ctx (K.fill (.and S [.var (.evar x), p]))).interpret I e m ↔
      (tr ctx (K.fill (.and S [p, .var (.evar x)]))).interpret I e m := by
  rw [tr_cutCtx ctx _ K hK, tr_cutCtx ctx _ K hK]
  refine cutCtx_fill_congr (fun a => ?_) (K.toCut ctx) m
  simp only [tr, trAndList, interp_sAnd]
  exact And.comm

end KoreAML
