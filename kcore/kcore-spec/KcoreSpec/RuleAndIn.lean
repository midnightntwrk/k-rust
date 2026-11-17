/-
  KCore. A rule's right side holding `t ∧ u` of two terms at a position under applications, read
  with the position cut.

  - `rule_and_in` (the fresh form): `∃Z:S. (K[Z] ∧ E ∧ (Z ∈ t ∧ Z ∈ u))` is `K[t ∧ u] ∧ E`, where
    definedness is definedness, the two sort patterns denote sorts, every element of `t ∧ u` is in
    S and every element of `K[t ∧ u]` in C, no head on the path to the position is an alias, and
    the side patterns, t, u, E and the two sorts do not read Z.
  - `rule_and_var` (the variable form): where a conjunct is a variable V with an element of S,
    `K[V] ∧ E ∧ V ∈ u` is `K[V ∧ u] ∧ E`, where every element of `K[V]` is in C. No variable is
    added, and nothing is asked of what the side patterns read.
  Both are stated at one context `ctx` for the two patterns.
-/
import KcoreSpec.CutIdentity

set_option autoImplicit false

namespace KoreAML

open ML

variable {M : Type} {I : Interpretation Sym M}

/-- A context of applications at `x ∧ ψ`, x an element variable: the context at x, where the
element of x is one of ψ. Nothing is asked of what the side patterns read. -/
theorem CutCtx.fill_evar_and (x : EVar) (ψ : P) (e : Valuation M) : ∀ (C : CutCtx) (m : M),
    (C.fill (sAnd (.evar x) ψ)).interpret I e m ↔
      ψ.interpret I e (e.evalEvar x) ∧ (C.fill (.evar x)).interpret I e m
  | .hole, m => by
    show (sAnd (.evar x) ψ).interpret I e m ↔ _ ∧ (Pattern.evar x : P).interpret I e m
    rw [interp_sAnd, interp_evar]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1 ▸ h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h2 ▸ h1⟩
  | .fn C χ, m => by
    show (C.fill _ ⬝ χ).interpret I e m ↔ _ ∧ (C.fill _ ⬝ χ).interpret I e m
    rw [interp_app, interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨h1, h2⟩ := (CutCtx.fill_evar_and x ψ e C p).mp hp
      exact ⟨h1, p, b, h2, hb, hpb⟩
    · rintro ⟨h1, p, b, h2, hb, hpb⟩
      exact ⟨p, b, (CutCtx.fill_evar_and x ψ e C p).mpr ⟨h1, h2⟩, hb, hpb⟩
  | .arg χ C, m => by
    show (χ ⬝ C.fill _).interpret I e m ↔ _ ∧ (χ ⬝ C.fill _).interpret I e m
    rw [interp_app, interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨h1, h2⟩ := (CutCtx.fill_evar_and x ψ e C b).mp hb
      exact ⟨h1, p, b, hp, h2, hpb⟩
    · rintro ⟨h1, p, b, hp, h2, hpb⟩
      exact ⟨p, b, hp, (CutCtx.fill_evar_and x ψ e C b).mpr ⟨h1, h2⟩, hpb⟩

/-- **The fresh form**: `\exists{C}(Z:S, \and{C}(K[Z], E, \and{C}(\in{S,C}(Z, t), \in{S,C}(Z, u))))`
is `\and{C}(K[\and{S}(t, u)], E)`. -/
theorem rule_and_in [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (z : Kore.EVar) (hz : z.sort = S) (t u E : Kore.Pattern)
    (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ctx (ctx.vars.ev (evarKey z)))
    (ht : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx t))
    (hu : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx u))
    (hE : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx E))
    (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
    (hCz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars C))
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hin : ∀ a, (tr ctx (.and S [t, u])).interpret I e a → Inh I σ a)
    (hout : ∀ m, (tr ctx (K.fill (.and S [t, u]))).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E,
        .and C [.in S C (.var (.evar z)) t, .in S C (.var (.evar z)) u]]))).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [t, u]), E])).interpret I e m := by
  have hand : tr ctx (.and S [t, u]) = sAnd (tr ctx t) (tr ctx u) := by simp only [tr, trAndList]
  have hl : tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E,
        .and C [.in S C (.var (.evar z)) t, .in S C (.var (.evar z)) u]])) =
      sExists (ctx.vars.ev (evarKey z)) (trSort ctx.vars S)
        (sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey z)))) (sAnd (tr ctx E)
          (sAnd (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey z))) (tr ctx t))
            (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey z))) (tr ctx u))))) := by
    simp only [tr, trAndList, hz]
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hr : tr ctx (.and C [K.fill (.and S [t, u]), E]) =
      sAnd ((K.toCut ctx).fill (sAnd (tr ctx t) (tr ctx u))) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK, hand]
  have hfill : tr ctx (K.fill (.and S [t, u])) = (K.toCut ctx).fill (sAnd (tr ctx t) (tr ctx u)) := by
    rw [tr_cutCtx ctx _ K hK, hand]
  rw [hand] at hin
  rw [hfill] at hout
  rw [hl, hr, interp_sExists, interp_sAnd,
    cut_sem (ctx.vars.ev (evarKey z)) _ (K.toCut ctx) (KoreCutCtx.toCut_fresh K hsides) e m]
  generalize ctx.vars.ev (evarKey z) = x at *
  have hSu : ∀ a b, (trSort ctx.vars S).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ :=
    fun a b => (hSz e a b).trans (hS b)
  have hCu : ∀ a b, (trSort ctx.vars C).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ' :=
    fun a b => (hCz e a b).trans (hC b)
  have hup : ∀ a, Function.update e.evalEvar x a x = a := fun a => by simp
  constructor
  · rintro ⟨a, hxa, hbody⟩
    simp only [interp_sAnd] at hbody
    obtain ⟨hCx, hE', hint, hinu⟩ := hbody
    rw [interp_member hD, interp_inhOf_of (hSu a)] at hxa
    have h1 := (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx t) m).mp hint
    have h2 := (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx u) m).mp hinu
    have h1' : (tr ctx t).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a := by
      have := h1.1; rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a] at this
      exact this
    have h2' : (tr ctx u).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a := by
      have := h2.1; rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a] at this
      exact this
    exact ⟨⟨a, interp_sAnd.mpr ⟨(ht e a a).mp h1', (hu e a a).mp h2'⟩, hCx⟩, (hE e a m).mp hE'⟩
  · rintro ⟨⟨a, hta, hCx⟩, hEm⟩
    have hφ := interp_sAnd.mp hta
    have hIa : Inh I σ a := hin a hta
    have hm' : Inh I σ' m :=
      hout m ((cut_sem x _ (K.toCut ctx) (KoreCutCtx.toCut_fresh K hsides) e m).mpr ⟨a, hta, hCx⟩)
    have hxa : Inh I σ ((⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x) := by
      rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a]
      exact hIa
    refine ⟨a, ?_, ?_⟩
    · rw [interp_member hD, interp_inhOf_of (hSu a)]; exact hxa
    · simp only [interp_sAnd]
      refine ⟨hCx, (hE e a m).mpr hEm,
        (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx t) m).mpr ⟨?_, hm'⟩,
        (mem_iff_cut hD hc (hSu a) (hCu a) hσ hσ' x hxa (tr ctx u) m).mpr ⟨?_, hm'⟩⟩
      · rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a]
        exact (ht e a a).mpr hφ.1
      · rw [show (⟨Function.update e.evalEvar x a, e.evalSvar⟩ : Valuation M).evalEvar x = a from hup a]
        exact (hu e a a).mpr hφ.2

/-- **The variable form**: `\and{C}(K[V], E, \in{S,C}(V, u))` is `\and{C}(K[\and{S}(V, u)], E)`. -/
theorem rule_and_var [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (v : Kore.EVar) (u E : Kore.Pattern) (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hv : Inh I σ (e.evalEvar (ctx.vars.ev (evarKey v))))
    (hout : ∀ m, (tr ctx (K.fill (.var (.evar v)))).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u])).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E])).interpret I e m := by
  have hand : tr ctx (.and S [.var (.evar v), u]) =
      sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u) := by simp only [tr, trAndList]
  have hfillv : tr ctx (K.fill (.var (.evar v))) =
      (K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v))) := by
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hl : tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u]) =
      sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v)))) (sAnd (tr ctx E)
        (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) := by
    simp only [tr, trAndList]
    rw [hfillv]
  have hr : tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E]) =
      sAnd ((K.toCut ctx).fill (sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK, hand]
  rw [hfillv] at hout
  rw [hl, hr, interp_sAnd, interp_sAnd, interp_sAnd, CutCtx.fill_evar_and,
    mem_iff_cut hD hc hS hC hσ hσ' _ hv]
  constructor
  · rintro ⟨hCx, hEm, hu, -⟩; exact ⟨⟨hu, hCx⟩, hEm⟩
  · rintro ⟨⟨hu, hCx⟩, hEm⟩; exact ⟨hCx, hEm, hu, hout m hCx⟩

end KoreAML
