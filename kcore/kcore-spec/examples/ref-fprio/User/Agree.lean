/-
  `ag`'s agreement on the package `RefFprio`, read from kompile's own KORE of `f2-examples/fprio.k`
  (`f2-examples/fprio.kompile.kore`): its two clauses of priority 50, `ag(0 #as X) => X` and
  `ag(N) => N *Int N`, give one result where both apply, at `ag(0)`. It is the package's one named
  obligation (`agree_obligations`); with it the obligations hold, and the definition is sound and
  complete (`sound_defn`, `complete_defn`).
-/
import RefFprio
import RefFprio.Sound
import KcoreSpec.Cert
import KcoreSpec.EvalComplete

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefFprio.Agree

open KCore KCore.Exec KCore.Cert RefFprio

/-! ## `ag`'s two clauses of priority 50 agree -/

/-- `ag`'s clauses: `ag(0 #as X) => X` and `ag(N) => N *Int N`. -/
theorem ag_clauses {fn : Fn} (hfn : c.lookupFn Sym.«ag» = some fn) :
    fn.clauses = [{ vars := [KCore.Srt.int], pats := [.as (.dv KCore.Srt.int (.int 0)) 0], req := none,
                    rhs := .var 0, ens := none, prio := 50 },
                  { vars := [KCore.Srt.int], pats := [.var 0], req := none,
                    rhs := .app KCore.intMul [.var 0, .var 0], ens := none, prio := 50 }] := by
  have hsig := fn_ag_sig
  have h0 := fn_ag_0
  have h1 := fn_ag_1
  rw [hfn] at hsig h0 h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Option.bind_some] at hsig h0 h1
  have hl := hsig.2.2
  generalize fn.clauses = l at hl h0 h1 ⊢
  match l, hl with
  | [a, b], _ =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    rw [h0, h1]

/-- Where `ag-z` applies, its argument is 0 and its right-hand side's result is 0. -/
theorem agZ_val {σ : Subst} {vs : List GroundTerm} {r : Option GroundTerm}
    (hm : PatVals c σ [.as (.dv KCore.Srt.int (.int 0)) 0] vs) (he : EvalTerm c σ (.var 0) r) :
    vs = [int 0] ∧ r = some (int 0) := by
  cases hm with
  | cons hp hs =>
    cases hs
    cases hp with
    | as hp hi =>
      cases hp
      cases he
      exact ⟨rfl, hi⟩

/-- Where `ag-sq` applies at `[int 0]`, its right-hand side's result is 0. -/
theorem agSq_val {σ : Subst} {r : Option GroundTerm}
    (hm : PatVals c σ [.var 0] [int 0]) (he : EvalTerm c σ (.app KCore.intMul [.var 0, .var 0]) r) :
    r = some (int 0) := by
  cases hm with
  | cons hp hs =>
    cases hp with
    | var hi =>
      cases he with
      | ctor h _ => exact absurd h (by decide +kernel)
      | hook _ _ hts hh _ =>
        cases hts with
        | cons h1 hs1 =>
          cases hs1 with
          | cons h2 hs2 =>
            cases hs2
            cases h1
            cases h2
            have := hh [int 0, int 0] (by simp only [allSome, hi]; rfl)
            rw [Semantics.hookRes_of_notKey (by decide +kernel)] at this
            simp only [hook] at this
            exact (Option.some.inj this).symm.trans rfl
      | param _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
      | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
      | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
      | ovl _ ho _ => exact absurd ho (by decide +kernel)

/-- **`ag`'s agreement**, the package's one named agreement (`agree_obligations`): its two clauses,
of one priority, give one result where both apply, at `ag(0)`, in both orders. -/
theorem ag_agree : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn := by
  intro f hf fn hfn
  rw [agree_obligations] at hf
  rw [List.mem_singleton.mp hf] at hfn
  intro cl cl' hp _
  rw [ag_clauses hfn] at hp
  simp [pairs] at hp
  obtain ⟨rfl, rfl⟩ := hp
  refine ⟨Coherent.of_rhs rfl rfl fun vs σ σ' ha ha' _ _ _ => .inr fun r r' he he' => ?_,
          Coherent.of_rhs rfl rfl fun vs σ σ' ha ha' _ _ _ => .inr fun r r' he he' => ?_⟩
  · obtain ⟨rfl, rfl⟩ := agZ_val ha.2.1 he
    exact (agSq_val ha'.2.1 he').symm
  · obtain ⟨rfl, rfl⟩ := agZ_val ha'.2.1 he'
    exact agSq_val ha.2.1 he

/-- The clauses of one priority are coherent. -/
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_fixed ok srReady matchReady clausesFixed ag_agree

/-- No rule or clause has an open variable or a condition with a binder. -/
theorem readsConfined_defn : c.readsConfined = false := by decide +kernel

/-- **The package's named obligations hold**, and it is sound. -/
theorem obligations_hold : Obligations defn :=
  ⟨fun f hf => by rw [named_terminates] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [named_totals] at hf; exact absurd hf List.not_mem_nil,
   ag_agree,
   fun p hp => by rw [match_obligations] at hp; exact absurd hp List.not_mem_nil,
   fun o ho => by rw [lazy_obligations] at ho; exact absurd ho List.not_mem_nil,
   openDecided_of_readsConfined readsConfined_defn, openLaws_of_plain (by decide +kernel)⟩

theorem sound_defn : Sound defn := RefFprio.sound obligations_hold

theorem complete_defn (ref : OutFn) : Complete defn ref := RefFprio.complete ref obligations_hold

end RefFprio.Agree
