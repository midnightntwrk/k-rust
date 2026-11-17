/-
  KCore, checked layer: `Det.detOK` makes `Step` deterministic (`Det.deterministic_of`).
  The conditions are Determinism.lean's; each part's soundness is a section below.
-/
import KcoreSpec.Determinism
import KcoreSpec.MatchIndependent
import KcoreSpec.Kind

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec GroundTerm

variable {c : Semantics}

/-! ## Evaluation of a term has one result -/

/-- A term has one result under each substitution, where clauses of one priority are coherent
(`EvalTerm.functional`; `coherentAll_of`, FnExclusive.lean, gives the premise in a core that `ok`
and `matchReady` accept, with the named obligations). -/
theorem evalTerm_det (hmi : CoherentAll c) {σ : Subst} {t : Term} {r r' : Option GroundTerm}
    (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  EvalTerm.functional hmi h h'

theorem below_mem {a a₀ : Srt} (h : (a₀, a) ∈ c.subsorts) : a₀ ∈ below (tables c) a := by
  simp only [below, mem_below_tables]; exact h

/-- The source sorts `srcs` gives contain the source of the injection of t's value. -/
theorem srcs_eval {σ : Subst} {vars : List Srt} (hσ : c.WellSorted vars σ) :
    ∀ (t : Term) (a : Srt) (w : GroundTerm) (S : List Srt) (srt : Bool),
    EvalTerm c σ t (some w) → srcs c (tables c) vars a t = some (S, srt) → ∀ b,
      ∃ s u, injNormal a b w = .inj s b u ∧ s ∈ S ∧ u.isInj = false ∧
        (srt = true → c.sortOf u = some s)
  | .var j, a, w, S, srt, h, hs, b => by
    have hw := EvalTerm.var_inv h
    simp only [srcs] at hs
    split at hs
    · rename_i hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨v, hv, hvs⟩ := hσ j a (by simpa using hj)
      rw [← hw] at hv; cases hv
      cases w with
      | inj a₀ b₀ u =>
        obtain ⟨hsub, hu, hus, rfl⟩ := sortOf_inj.mp hvs
        exact ⟨a₀, u, rfl, List.mem_cons_of_mem _ (below_mem hsub), hu, fun _ => hus⟩
      | _ => exact ⟨a, _, rfl, List.mem_cons_self .., rfl, fun _ => hvs⟩
    · cases hs
  | .inj a₁ b₁ t, a, w, S, srt, h, hs, b => by
    simp only [srcs] at hs
    split at hs
    · rename_i hb
      have hb : b₁ = a := by simpa using hb
      subst hb
      obtain ⟨r', hr', hw⟩ := EvalTerm.inj_inv h
      cases r' with
      | none => cases hw
      | some w₁ =>
        simp only [Option.map_some, Option.some.injEq] at hw
        subst hw
        obtain ⟨s, u, he, hsS, hu, hsu⟩ := srcs_eval hσ t a₁ w₁ S srt hr' hs b₁
        refine ⟨s, u, ?_, hsS, hu, hsu⟩
        rw [he]; rfl
    · cases hs
  | .as t i, a, w, S, srt, h, hs, b => by cases h
  | .dv s l, a, w, S, srt, h, hs, b => by
    have hw : w = .dv s l := by cases h; rfl
    subst hw
    simp only [srcs, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨a, _, rfl, List.mem_singleton_self _, rfl, fun h => ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hd⟩ := h
    exact sortOf_dv.mpr ⟨hd, rfl⟩
  | .app f ts, a, w, S, srt, h, hs, b => by
    simp only [srcs] at hs
    split at hs
    · rename_i hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hni : w.isInj = false := by
        generalize ht : Term.app f ts = t' at h
        generalize hr : some w = r at h
        cases h with
        | @ctor _ _ _ rs _ _ =>
          cases ht
          cases hw' : allSome rs <;> rw [hw'] at hr <;> cases hr; rfl
        | @hook _ _ _ rs _ hk _ _ hh hund =>
          cases ht
          have hph : patternHooks.contains f = true := by simpa [hk] using hf
          cases hrs : allSome rs with
          | none => rw [hund hrs] at hr; cases hr
          | some vs =>
            have hv := hh vs hrs
            rw [Semantics.hookRes_of_notKey (silentKey_of_patternHook hph)] at hv
            obtain ⟨es, he⟩ := patternHook_map hph (hr ▸ hv)
            rw [he]; rfl
        | param hk hhk _ _ _ =>
          cases ht
          have hph : patternHooks.contains f = true := by simpa [hk] using hf
          rw [patternHooks_isHook hph] at hhk; cases hhk
        | call hk hhk _ _ _ _ =>
          cases ht
          have hph : patternHooks.contains f = true := by simpa [hk] using hf
          rw [patternHooks_isHook hph] at hhk; cases hhk
        | callUndef hk hhk _ _ _ =>
          cases ht
          have hph : patternHooks.contains f = true := by simpa [hk] using hf
          rw [patternHooks_isHook hph] at hhk; cases hhk
        | ovl hk ho _ =>
          cases ht
          have hph : patternHooks.contains f = true := by simpa [hk] using hf
          rw [c.isOvl_of_patternHook hph] at ho; cases ho
        | ovlFn hk ho =>
          cases ht
          have hph : patternHooks.contains f = true := by simpa [hk] using hf
          rw [c.isOvl_of_patternHook hph] at ho; cases ho
        | _ => cases ht
      exact ⟨a, w, injNormal_of_not_inj hni, List.mem_singleton_self _, hni, fun h => by cases h⟩
    · cases hs

theorem allSome_map_some : ∀ (ws : List GroundTerm), allSome (ws.map some) = some ws
  | [] => rfl
  | w :: ws => by simp [allSome, allSome_map_some ws]

mutual
  /-- A pattern's value is its term's value, `as` removed. -/
  theorem PatVal.eval_strip (hmc : MatchCtx c) {σ : Subst} : ∀ {p : Term} {w : GroundTerm},
      PatVal c σ p w → EvalTerm c σ (strip p) (some w)
    | _, _, .var h => by rw [strip, ← h]; exact .var
    | _, _, .dv => by rw [strip]; exact .dv
    | _, _, .ctor hc hs => by
      rw [strip]
      have := EvalTerm.ctor (σ := σ) hc (PatVals.eval_strip hmc hs)
      rwa [allSome_map_some, Option.map_some] at this
    | _, _, .hook (f := f) (vs := vs) hp hs hv => by
      rw [strip]
      refine EvalTerm.hook (hmc.patHooks f (List.contains_iff_mem.mp hp)) (patternHooks_isHook hp)
        (PatVals.eval_strip hmc hs) (fun vs' h => ?_) (fun h => ?_)
      · rw [allSome_map_some] at h; cases h; exact Semantics.hookRes_of_value hv
      · rw [allSome_map_some] at h; cases h
    | _, _, .coll (f := f) (vs := ws) hc hp hs hv => by
      rw [strip]
      unfold Semantics.collVal at hv
      by_cases hh : isHook f = true
      · rw [if_pos hh] at hv
        refine EvalTerm.hook hc hh (PatVals.eval_strip hmc hs) (fun vs' h => ?_) (fun h => ?_)
        · rw [allSome_map_some] at h; cases h
          exact Semantics.hookRes_of_value (Option.join_eq_some_iff.mp hv)
        · rw [allSome_map_some] at h; cases h
      · rw [if_neg hh] at hv
        have hhk : isHook f = false := by simpa using hh
        have hpar : c.isParam f = true := by
          unfold Semantics.isCollPat at hp; rw [hhk] at hp
          unfold Semantics.isParam
          cases hk : c.lookupParam f with
          | none => rw [hk] at hp; simp at hp
          | some _ => rfl
        exact EvalTerm.param hc hhk hpar (PatVals.eval_strip hmc hs) (by rw [allSome_map_some]; exact hv.symm)
    | _, _, .inj (a := a) (b := b) h => by
      rw [strip]
      simpa using EvalTerm.inj (a := a) (b := b) (PatVal.eval_strip hmc h)
    | _, _, .as h _ => by rw [strip]; exact PatVal.eval_strip hmc h
    | _, _, .ovl hc ho hs hv => by
      rw [strip]
      have := EvalTerm.ovl (σ := σ) hc ho (PatVals.eval_strip hmc hs)
        (fun vs _ => OvlLaws.fnCover_none_of_nil hmc.noOvl _ vs)
      rwa [allSome_map_some, Option.map_some, hv] at this
  theorem PatVals.eval_strip (hmc : MatchCtx c) {σ : Subst} : ∀ {ps : List Term} {ws : List GroundTerm},
      PatVals c σ ps ws → EvalTerms c σ (stripList ps) (ws.map some)
    | _, _, .nil => by rw [stripList]; exact .nil
    | _, _, .cons h hs => by
      rw [stripList]
      exact .cons (PatVal.eval_strip hmc h) (PatVals.eval_strip hmc hs)
end

theorem srcs_strip {vars : List Srt} : ∀ (p : Term) (a : Srt), srcs c (tables c) vars a (strip p) = srcs c (tables c) vars a p
  | .var _, _ => by rw [strip]
  | .dv _ _, _ => by rw [strip]
  | .app _ _, _ => by rw [strip]; rfl
  | .inj a₁ b₁ t, a => by rw [strip]; simp only [srcs, srcs_strip t a₁]
  | .as t _, a => by rw [strip]; simp only [srcs, srcs_strip t a]

theorem srcs_pat (hmc : MatchCtx c) {σ : Subst} {vars : List Srt} (hσ : c.WellSorted vars σ)
    {p : Term} {a : Srt} {w : GroundTerm} {S : List Srt} {srt : Bool}
    (h : PatVal c σ p w) (hs : srcs c (tables c) vars a p = some (S, srt)) (b : Srt) :
    ∃ s u, injNormal a b w = .inj s b u ∧ s ∈ S :=
  have ⟨s, u, h1, h2, _⟩ := srcs_eval hσ (strip p) a w S srt (PatVal.eval_strip hmc h)
    (by rw [srcs_strip]; exact hs) b
  ⟨s, u, h1, h2⟩

/-! ## `peelQ` -/

theorem peelQ_spec {σ : Subst} : ∀ {q q₀ : Term} {js : List Nat} {v : GroundTerm},
    peelQ q = (q₀, js) → PatVal c σ q v → PatVal c σ q₀ v ∧ ∀ j ∈ js, σ.lookup j = some v
  | .as t j, q₀, js, v, he, h => by
    obtain ⟨ht, hj⟩ := PatVal.as_inv h
    simp only [peelQ] at he
    obtain ⟨h1, h2⟩ := peelQ_spec (q := t) rfl ht
    generalize hp : peelQ t = pr at he h1 h2
    obtain ⟨u, js'⟩ := pr
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨h1, fun j' hj' => ?_⟩
    rcases List.mem_cons.mp hj' with rfl | hj'
    · exact hj
    · exact h2 j' hj'
  | .var _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨h, by simp⟩
  | .dv _ _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨h, by simp⟩
  | .app _ _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨h, by simp⟩
  | .inj _ _ _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨h, by simp⟩

theorem peelQ_sort {x : TermCtx} {vars : List Srt} : ∀ {q q₀ : Term} {js : List Nat} {s : Srt},
    peelQ q = (q₀, js) → sortOfTerm x vars q = some s → sortOfTerm x vars q₀ = some s
  | .as t j, q₀, js, s, he, h => by
    have ht := (sortOfTerm_as h).2
    simp only [peelQ] at he
    have := peelQ_sort (q := t) rfl ht
    generalize hp : peelQ t = pr at he this
    obtain ⟨u, js'⟩ := pr
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact this
  | .var _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact h
  | .dv _ _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact h
  | .app _ _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact h
  | .inj _ _ _, _, _, _, he, h => by simp only [peelQ, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact h

/-! ## `meet` -/

/-- Each pair denotes one value, its first pattern under σ, its second under σ'. -/
def Rel (c : Semantics) (σ σ' : Subst) (C : List (Term × Term)) : Prop :=
  ∀ pq ∈ C, ∃ w, PatVal c σ pq.1 w ∧ PatVal c σ' pq.2 w

theorem Rel.nil {σ σ' : Subst} : Rel c σ σ' [] := fun _ h => by cases h

theorem Rel.append {σ σ' : Subst} {C D : List (Term × Term)} (h1 : Rel c σ σ' C) (h2 : Rel c σ σ' D) :
    Rel c σ σ' (C ++ D) := fun pq h => (List.mem_append.mp h).elim (h1 pq) (h2 pq)

theorem Rel.cons {σ σ' : Subst} {p q : Term} {C : List (Term × Term)} {w : GroundTerm}
    (hp : PatVal c σ p w) (hq : PatVal c σ' q w) (h : Rel c σ σ' C) : Rel c σ σ' ((p, q) :: C) :=
  fun pq hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨w, hp, hq⟩
    · exact h pq hm

theorem meetQ_sound {σ σ' : Subst} {p q : Term} {v : GroundTerm} {k : Term → Option (List (Term × Term))}
    (hp : PatVal c σ p v) (hq : PatVal c σ' q v)
    (hk : ∀ q₀ js, peelQ q = (q₀, js) → PatVal c σ' q₀ v → ∃ C, k q₀ = some C ∧ Rel c σ σ' C) :
    ∃ C, meetQ p q k = some C ∧ Rel c σ σ' C := by
  unfold meetQ
  generalize hpq : peelQ q = pr
  obtain ⟨q₀, js⟩ := pr
  obtain ⟨hq₀, hjs⟩ := peelQ_spec hpq hq
  have hpre : Rel c σ σ' (js.map fun j => (p, Term.var j)) := fun pq hm => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
    exact ⟨v, hp, .var (hjs j hj)⟩
  cases q₀ with
  | var j => exact ⟨_, rfl, hpre.append (Rel.cons hp hq₀ Rel.nil)⟩
  | _ =>
    obtain ⟨C, hC, hR⟩ := hk _ js hpq hq₀
    exact ⟨_, by simp only [hC, Option.map_some], hpre.append hR⟩

theorem not_app_inj (hno : c.ovls = []) {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (h : PatVal c σ (.app f ps) v) (hi : v.isInj = true) : False := by
  rcases PatVal.app_shape hno h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases hi

mutual
  theorem meet_sound (hmc : MatchCtx c) {σ σ' : Subst} {vs vs' : List Srt}
      (hσ : c.WellSorted vs σ) (hσ' : c.WellSorted vs' σ') :
      ∀ (p q : Term) {v : GroundTerm} {s s' : Srt}, PatVal c σ p v → PatVal c σ' q v →
        sortOfTerm c.patCtx vs p = some s → sortOfTerm c.patCtx vs' q = some s' →
        ∃ C, meet c (tables c) vs vs' p q = some C ∧ Rel c σ σ' C
    | .as p i, q, v, s, s', hp, hq, hs, hs' => by
      obtain ⟨hp', hi⟩ := PatVal.as_inv hp
      obtain ⟨C, hC, hR⟩ := meet_sound hmc hσ hσ' p q hp' hq (sortOfTerm_as hs).2 hs'
      exact ⟨_, by rw [meet, hC]; rfl, Rel.cons (.var hi) hq hR⟩
    | .var i, q, v, s, s', hp, hq, _, _ => ⟨_, by rw [meet], Rel.cons hp hq Rel.nil⟩
    | .dv s₀ l, q, v, s, s', hp, hq, _, hs' => by
      have hv := PatVal.dv_shape hp
      subst hv
      rw [meet]
      refine meetQ_sound hp hq fun q₀ js hpq hq₀ => ?_
      cases q₀ with
      | dv s₁ l₁ =>
        have := PatVal.dv_shape hq₀
        cases this
        exact ⟨[], by simp, Rel.nil⟩
      | app g qs => exact (by rcases PatVal.app_shape hmc.noOvl hq₀ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h)
      | inj a' b' q' => exact absurd (PatVal.inj_shape hq₀) (by simp [GroundTerm.isInj])
      | var _ => exact ⟨[], rfl, Rel.nil⟩
      | as _ _ => exact ⟨[], rfl, Rel.nil⟩
    | .app f ps, q, v, s, s', hp, hq, hs, hs' => by
      rw [meet]
      refine meetQ_sound hp hq fun q₀ js hpq hq₀ => ?_
      have hs₀ := peelQ_sort hpq hs'
      cases q₀ with
      | app g qs =>
        dsimp only
        split
        · rename_i hfg
          have hfg := beq_iff_eq.mp hfg
          subst hfg
          split
          · rename_i hf
            obtain ⟨vs₀, rfl, hps⟩ := PatVal.ctor_shape hmc hf hp
            obtain ⟨vs₁, he, hqs⟩ := PatVal.ctor_shape hmc hf hq₀
            cases he
            obtain ⟨k, -, hk, -⟩ := sortOfTerm_app.mp hs
            obtain ⟨k', -, hk', -⟩ := sortOfTerm_app.mp hs₀
            exact meetList_sound hmc hσ hσ' ps qs hps hqs hk hk'
          · exact ⟨_, rfl, Rel.cons hp hq₀ Rel.nil⟩
        · rename_i hfg
          split
          · rename_i hfg'
            obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hfg'
            obtain ⟨_, rfl, _⟩ := PatVal.ctor_shape hmc h1 hp
            obtain ⟨_, he, _⟩ := PatVal.ctor_shape hmc h2 hq₀
            cases he
            exact absurd (beq_self_eq_true f) hfg
          · exact ⟨_, rfl, Rel.cons hp hq₀ Rel.nil⟩
      | dv s₁ l₁ =>
        have := PatVal.dv_shape hq₀
        subst this
        exact (by rcases PatVal.app_shape hmc.noOvl hp with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h)
      | inj a' b' q' => exact (not_app_inj hmc.noOvl hp (PatVal.inj_shape hq₀)).elim
      | var _ => exact ⟨[], rfl, Rel.nil⟩
      | as _ _ => exact ⟨[], rfl, Rel.nil⟩
    | .inj a b p, q, v, s, s', hp, hq, hs, hs' => by
      obtain ⟨w, hpw, hv⟩ := PatVal.inj_inv hp
      obtain ⟨-, hps, -⟩ := sortOfTerm_inj.mp hs
      rw [meet]
      refine meetQ_sound hp hq fun q₀ js hpq hq₀ => ?_
      have hs₀ := peelQ_sort hpq hs'
      cases q₀ with
      | inj a' b' q' =>
        dsimp only
        obtain ⟨w', hqw, hv'⟩ := PatVal.inj_inv hq₀
        obtain ⟨-, hqs, -⟩ := sortOfTerm_inj.mp hs₀
        have hvv : injNormal a b w = injNormal a' b' w' := hv.symm.trans hv'
        split
        · rename_i hb
          obtain ⟨s₁, u₁, h₁⟩ := injNormal_shape a b w
          obtain ⟨s₂, u₂, h₂⟩ := injNormal_shape a' b' w'
          rw [h₁, h₂] at hvv
          cases hvv
          simp at hb
        · rename_i hb
          have hb : b = b' := by simpa using hb
          subst hb
          split
          · rename_i ha
            have ha := beq_iff_eq.mp ha
            subst ha
            have hw := injNormal_inj hmc (patVal_sorted hmc hσ hpw hps) (patVal_sorted hmc hσ' hqw hqs) hvv
            subst hw
            exact meet_sound hmc hσ hσ' p q' hpw hqw hps hqs
          · rcases hS : srcs c (tables c) vs a p with _ | ⟨S, x⟩ <;> rcases hS' : srcs c (tables c) vs' a' q' with _ | ⟨S', y⟩
            · exact ⟨_, rfl, Rel.cons hp hq₀ Rel.nil⟩
            · exact ⟨_, rfl, Rel.cons hp hq₀ Rel.nil⟩
            · exact ⟨_, rfl, Rel.cons hp hq₀ Rel.nil⟩
            · dsimp only
              split
              · exact ⟨_, rfl, Rel.cons hp hq₀ Rel.nil⟩
              · rename_i hdis
                obtain ⟨t₁, u₁, e₁, m₁⟩ := srcs_pat hmc hσ hpw hS b
                obtain ⟨t₂, u₂, e₂, m₂⟩ := srcs_pat hmc hσ' hqw hS' b
                rw [hvv, e₂] at e₁
                simp only [GroundTerm.inj.injEq] at e₁
                obtain ⟨rfl, -, -⟩ := e₁
                exact absurd (List.any_eq_true.mpr ⟨_, m₁, List.contains_iff_mem.mpr m₂⟩) hdis
      | dv s₁ l₁ =>
        have := PatVal.dv_shape hq₀
        rw [this] at hv
        exact absurd (hv ▸ injNormal_isInj a b w) (by simp [GroundTerm.isInj])
      | app g qs => exact (not_app_inj hmc.noOvl hq₀ (hv ▸ injNormal_isInj a b w)).elim
      | var _ => exact ⟨[], rfl, Rel.nil⟩
      | as _ _ => exact ⟨[], rfl, Rel.nil⟩
  theorem meetList_sound (hmc : MatchCtx c) {σ σ' : Subst} {vs vs' : List Srt}
      (hσ : c.WellSorted vs σ) (hσ' : c.WellSorted vs' σ') :
      ∀ (ps qs : List Term) {ws : List GroundTerm} {ss ss' : List Srt},
        PatVals c σ ps ws → PatVals c σ' qs ws →
        sortsOfTerms c.patCtx vs ps = some ss → sortsOfTerms c.patCtx vs' qs = some ss' →
        ∃ C, meetList c (tables c) vs vs' ps qs = some C ∧ Rel c σ σ' C
    | [], [], _, _, _, _, _, _, _ => ⟨[], by rw [meetList], Rel.nil⟩
    | p :: ps, q :: qs, _, _, _, .cons hp hps, .cons hq hqs, hs, hs' => by
      obtain ⟨s₁, ss₁, h1, h2, _⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨s₂, ss₂, h3, h4, _⟩ := sortsOfTerms_cons.mp hs'
      obtain ⟨C, hC, hR⟩ := meet_sound hmc hσ hσ' p q hp hq h1 h3
      obtain ⟨D, hD, hR'⟩ := meetList_sound hmc hσ hσ' ps qs hps hqs h2 h4
      exact ⟨C ++ D, by rw [meetList, hC, hD], hR.append hR'⟩
    | [], _ :: _, _, _, _, h, h', _, _ => by cases h; cases h'
    | _ :: _, [], _, _, _, h, h', _, _ => by cases h; cases h'
end

/-! ## Syntactic equality -/

mutual
  theorem Term.beq_sound : ∀ {t u : Term}, Term.beq t u = true → t = u
    | .var i, .var j, h => by simp only [Term.beq, beq_iff_eq] at h; rw [h]
    | .app f ts, .app g us, h => by
      simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, Term.beqList_sound h.2]
    | .inj a b t, .inj a' b' t', h => by
      simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, h.1.2, Term.beq_sound h.2]
    | .as t i, .as t' j, h => by
      simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, Term.beq_sound h.2]
    | .dv s l, .dv s' l', h => by
      simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, h.2]
    | .var _, .app .., h | .var _, .inj .., h | .var _, .as .., h | .var _, .dv .., h
    | .app .., .var _, h | .app .., .inj .., h | .app .., .as .., h | .app .., .dv .., h
    | .inj .., .var _, h | .inj .., .app .., h | .inj .., .as .., h | .inj .., .dv .., h
    | .as .., .var _, h | .as .., .app .., h | .as .., .inj .., h | .as .., .dv .., h
    | .dv .., .var _, h | .dv .., .app .., h | .dv .., .inj .., h | .dv .., .as .., h => by
      simp [Term.beq] at h
  theorem Term.beqList_sound : ∀ {ts us : List Term}, Term.beqList ts us = true → ts = us
    | [], [], _ => rfl
    | t :: ts, u :: us, h => by
      simp only [Term.beqList, Bool.and_eq_true] at h
      rw [Term.beq_sound h.1, Term.beqList_sound h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [Term.beqList] at h
end

/-! ## Translating r's terms to r''s variables -/

theorem envOf_sound (hmc : MatchCtx c) {σ σ' : Subst} {C : List (Term × Term)} (hR : Rel c σ σ' C)
    {i : Nat} {q : Term} (h : envOf C i = some q) :
    ∃ w, σ.lookup i = some w ∧ EvalTerm c σ' q (some w) := by
  unfold envOf at h
  obtain ⟨pq, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  obtain ⟨w, h1, h2⟩ := hR pq hm
  obtain ⟨p, q'⟩ := pq
  cases p with
  | var j =>
    simp only [beq_iff_eq] at hp
    subst hp
    exact ⟨w, PatVal.var_inv h1, PatVal.eval_strip hmc h2⟩
  | _ => simp at hp

mutual
  theorem tr_sound {σ σ' : Subst} {env : Nat → Option Term}
      (henv : ∀ i q, env i = some q → ∃ w, σ.lookup i = some w ∧ EvalTerm c σ' q (some w)) :
      ∀ {t t' : Term} {r : Option GroundTerm}, EvalTerm c σ t r → tr env t = some t' → EvalTerm c σ' t' r
    | .var i, t', r, h, ht => by
      rw [EvalTerm.var_inv h]
      simp only [tr] at ht
      obtain ⟨w, hw, he⟩ := henv i t' ht
      rw [hw]; exact he
    | .dv s l, t', r, h, ht => by
      simp only [tr, Option.some.injEq] at ht
      subst ht
      cases h; exact .dv
    | .app f ts, t', r, h, ht => by
      simp only [tr, Option.map_eq_some_iff] at ht
      obtain ⟨ts', hts', rfl⟩ := ht
      cases h with
      | ctor hk hts => exact .ctor hk (trList_sound henv hts hts')
      | hook hk hhk hts hh hund => exact .hook hk hhk (trList_sound henv hts hts') hh hund
      | param hk hhk hp hts hr => exact .param hk hhk hp (trList_sound henv hts hts') hr
      | call hk hhk hts hvs hf hp => exact .call hk hhk (trList_sound henv hts hts') hvs hf hp
      | callUndef hk hhk hts hvs hp => exact .callUndef hk hhk (trList_sound henv hts hts') hvs hp
      | ovl hk ho hts hnf => exact .ovl hk ho (trList_sound henv hts hts') hnf
      | ovlFn hk ho hts hvs hlo hcov hf => exact .ovlFn hk ho (trList_sound henv hts hts') hvs hlo hcov hf
    | .inj a b t, t', r, h, ht => by
      simp only [tr, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      cases h with
      | inj h' => exact .inj (tr_sound henv h' hu)
    | .as _ _, _, _, _, ht => by simp [tr] at ht
  theorem trList_sound {σ σ' : Subst} {env : Nat → Option Term}
      (henv : ∀ i q, env i = some q → ∃ w, σ.lookup i = some w ∧ EvalTerm c σ' q (some w)) :
      ∀ {ts ts' : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
        trList env ts = some ts' → EvalTerms c σ' ts' rs
    | [], ts', rs, h, ht => by
      simp only [trList, Option.some.injEq] at ht
      subst ht; cases h; exact .nil
    | t :: ts, ts', rs, h, ht => by
      simp only [trList] at ht
      cases h with
      | cons h1 h2 =>
        split at ht
        · rename_i u us hu hus
          simp only [Option.some.injEq] at ht
          subst ht
          exact .cons (tr_sound henv h1 hu) (trList_sound henv h2 hus)
        · cases ht
end

/-! ## Literals -/

theorem asBool_some {w : GroundTerm} {x : Bool} (h : asBool w = some x) : w = bool x := by
  cases w with
  | dv s lit =>
    cases lit with
    | bool b =>
      simp only [asBool] at h
      by_cases hs : s = Srt.bool
      · subst hs; simp at h; subst h; rfl
      · simp [hs] at h
    | _ => simp [asBool] at h
  | _ => simp [asBool] at h

theorem bool_inj {x y : Bool} (h : bool x = bool y) : x = y := by
  cases x <;> cases y <;> simp_all [bool, boolRepr]

theorem hook_and (vs : List GroundTerm) : hook boolAnd vs = some (bool2 vs (· && ·)) := rfl
theorem hook_not (w : GroundTerm) : hook boolNot [w] = some ((asBool w).map fun x => bool !x) := rfl
theorem isHook_and : isHook boolAnd = true := rfl
theorem isHook_not : isHook boolNot = true := rfl

theorem evalTerms_two {σ : Subst} {t₁ t₂ : Term} {rs : List (Option GroundTerm)}
    (h : EvalTerms c σ [t₁, t₂] rs) : ∃ r₁ r₂, rs = [r₁, r₂] ∧ EvalTerm c σ t₁ r₁ ∧ EvalTerm c σ t₂ r₂ := by
  cases h with
  | cons h1 hs => cases hs with
    | cons h2 hs' => cases hs'; exact ⟨_, _, rfl, h1, h2⟩

theorem evalTerms_one {σ : Subst} {t : Term} {rs : List (Option GroundTerm)}
    (h : EvalTerms c σ [t] rs) : ∃ r, rs = [r] ∧ EvalTerm c σ t r := by
  cases h with
  | cons h1 hs => cases hs; exact ⟨_, rfl, h1⟩

theorem and_inv {σ : Subst} {t₁ t₂ : Term} (h : EvalTerm c σ (.app boolAnd [t₁, t₂]) (some (bool true))) :
    EvalTerm c σ t₁ (some (bool true)) ∧ EvalTerm c σ t₂ (some (bool true)) := by
  generalize ht : Term.app boolAnd [t₁, t₂] = t at h
  generalize hr : some (bool true) = r at h
  cases h with
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w₁ =>
      cases r₂ with
      | none => rw [hund (by simp [allSome])] at hr; cases hr
      | some w₂ =>
        have hv := hh [w₁, w₂] (by simp [allSome])
        rw [Semantics.hookRes_of_notKey silentKey_boolAnd, hook_and, Option.some.injEq] at hv
        subst hv
        have hr' := hr.symm
        unfold bool2 at hr'
        cases hx : asBool w₁ with
        | none => simp [hx] at hr'
        | some x =>
        cases hy : asBool w₂ with
        | none => simp [hx, hy] at hr'
        | some y =>
        simp only [hx, hy, Option.bind_some, Option.map_some, Option.some.injEq] at hr'
        have := bool_inj hr'
        simp only [Bool.and_eq_true] at this
        obtain ⟨rfl, rfl⟩ := this
        rw [asBool_some hx] at h1; rw [asBool_some hy] at h2
        rw [← hr]
        exact ⟨h1, h2⟩
  | param _ hhk _ _ _ => cases ht; rw [isHook_and] at hhk; cases hhk
  | call _ hhk _ _ _ _ => cases ht; rw [isHook_and] at hhk; cases hhk
  | callUndef _ _ _ _ _ => cases ht; cases hr
  | ovl _ ho _ => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_and] at this; cases this
  | ovlFn _ ho => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_and] at this; cases this
  | _ => cases ht

theorem not_inv {σ : Subst} {t : Term} (h : EvalTerm c σ (.app boolNot [t]) (some (bool true))) :
    EvalTerm c σ t (some (bool false)) := by
  generalize ht : Term.app boolNot [t] = t' at h
  generalize hr : some (bool true) = r at h
  cases h with
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, rfl, h1⟩ := evalTerms_one hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w =>
      have hv := hh [w] (by simp [allSome])
      rw [Semantics.hookRes_of_notKey silentKey_boolNot, hook_not, Option.some.injEq] at hv
      subst hv
      obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp hr.symm
      have := bool_inj he
      simp only [Bool.not_eq_true'] at this
      subst this
      rw [asBool_some hx] at h1
      exact h1
  | param _ hhk _ _ _ => cases ht; rw [isHook_not] at hhk; cases hhk
  | call _ hhk _ _ _ _ => cases ht; rw [isHook_not] at hhk; cases hhk
  | callUndef _ _ _ _ _ => cases ht; cases hr
  | ovl _ ho _ => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_not] at this; cases this
  | ovlFn _ ho => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_not] at this; cases this
  | _ => cases ht

theorem lits_sound {σ : Subst} : ∀ {t : Term}, EvalTerm c σ t (some (bool true)) →
    ∀ {A : Term} {b : Bool}, (A, b) ∈ lits t → EvalTerm c σ A (some (bool b))
  | .app f [t₁, t₂], h, A, b, hm => by
    simp only [lits] at hm
    split at hm
    · rename_i hf
      have hf := beq_iff_eq.mp hf
      subst hf
      obtain ⟨h1, h2⟩ := and_inv h
      rcases List.mem_append.mp hm with hm | hm
      · exact lits_sound h1 hm
      · exact lits_sound h2 hm
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact h
  | .app f [t], h, A, b, hm => by
    simp only [lits] at hm
    split at hm
    · rename_i hf
      have hf := beq_iff_eq.mp hf
      subst hf
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact not_inv h
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact h
  | .dv s l, h, A, b, hm => by
    simp only [lits] at hm
    split at hm
    · simp at hm
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact h
  | .app f [], h, A, b, hm | .app f (_ :: _ :: _ :: _), h, A, b, hm | .var _, h, A, b, hm
  | .inj _ _ _, h, A, b, hm | .as _ _, h, A, b, hm => by
    simp only [lits, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact h

/-! ## Sort predicates -/

theorem isCtor_fixed {f : Sym} (h : (lookupSig fixedCtors f).isSome = true) : c.isCtor f = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  unfold Semantics.isCtor Semantics.ctorSigs
  rw [lookupSig_append_of_some (lookupSig_append_of_some hk)]
  rfl

theorem isCtor_kseq : c.isCtor kseq = true := isCtor_fixed rfl
theorem isCtor_dotk : c.isCtor dotk = true := isCtor_fixed rfl

theorem sortPredOf_spec {fn : Fn} {S : Srt} (h : sortPredOf fn = some S) :
    ∃ cl o, fn.clauses = [cl, o] ∧ cl.vars = [S] ∧ cl.pats = [kseqPat S] ∧
      cl.req = none ∧ cl.rhs = .dv Srt.bool (.bool true) ∧ cl.prio < o.prio ∧
      o.rhs = .dv Srt.bool (.bool false) ∧ cl.ens = none ∧ cl.aside = false ∧
      cl.pre = .top ∧ o.pre = .top ∧ cl.exs = [] := by
  unfold sortPredOf at h
  split at h
  · rename_i cl o hcl
    split at h
    · rename_i S' hv
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hc
        exact ⟨cl, o, hcl, hv, Term.beqList_sound h1, h2, Term.beq_sound h3, h4, Term.beq_sound h8, h9,
          by simpa using h10, Cond.eq_top_of_isTop h11, Cond.eq_top_of_isTop h12, List.isEmpty_iff.mp h13⟩
      · cases h
    · cases h
  · cases h

/-- The second clause of a sort predicate `isS` is `isS(K) => false`: one variable of sort `K`,
no `requires`. -/
theorem sortPredOf_owise {fn : Fn} {S : Srt} {cl o : Clause} (h : sortPredOf fn = some S)
    (hcl : fn.clauses = [cl, o]) : o.vars = [Srt.k] ∧ o.pats = [.var 0] ∧ o.req = none := by
  unfold sortPredOf at h
  rw [hcl] at h
  simp only at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
      exact ⟨h5, Term.beqList_sound h6, h7⟩
    · cases h
  · cases h

/-- The clause pattern of `isS` matches `kseq(inj{s,KItem}(u), dotk)` only if s ≤ S. -/
theorem kseq_match {σ : Subst} {S s : Srt} {u : GroundTerm} (hσ : c.WellSorted [S] σ)
    (h : PatVals c σ [kseqPat S] [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]]) : leS (tables c) s S = true := by
  obtain ⟨_, _, he₀, h1, -⟩ := PatVals.cons_inv' h
  cases he₀
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv rfl h1
    (by
      have h := KCore.lookupSig_ctorSigs_of_fixed (c := c) (L := []) (show lookupSig fixedCtors kseq = some _ from rfl)
      rw [List.append_nil] at h
      simp [Semantics.isCtor, h])
  cases he
  obtain ⟨_, _, he₁, h2, -⟩ := PatVals.cons_inv' hs
  cases he₁
  obtain ⟨w₀, hw₀, he⟩ := PatVal.inj_inv h2
  obtain ⟨v, hv, hvs⟩ := hσ 0 S rfl
  rw [PatVal.var_inv hw₀] at hv
  cases hv
  cases w₀ with
  | inj a₀ b₀ u₀ =>
    obtain ⟨hsub, -, -, rfl⟩ := sortOf_inj.mp hvs
    simp only [injNormal, GroundTerm.inj.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    simp [leS, hsub]
  | _ =>
    simp only [injNormal, GroundTerm.inj.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    simp [leS]

/-- What the generated sort predicate `isS` gives at `kseq(inj{s,KItem}(u), dotk)`: not `true`
where s is not below S, and `true` where it is (u of sort s, not an injection). -/
theorem sortPred_eval {f : Sym} {fn : Fn} {S s : Srt} {u : GroundTerm} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hS : sortPredOf fn = some S)
    (h : Eval c f [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]] r) :
    (leS (tables c) s S = false → r ≠ some (bool true)) ∧
    (leS (tables c) s S = true → u.isInj = false → c.sortOf u = some s → r = some (bool true)) := by
  obtain ⟨cl, o, hcl, hv, hp, hrq, hrh, hpr, hor, hce, hna, hclT, hoT, hclX⟩ := sortPredOf_spec hS
  -- where s is below S, the first clause applies: it does not fail
  have hnf : leS (tables c) s S = true → u.isInj = false → c.sortOf u = some s →
      ¬ Fails c [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]] cl := fun hle hu hsu hF => by
    cases hF with
    | intro hF =>
    let w₀ : GroundTerm := if s = S then u else .inj s S u
    have hw₀ : c.sortOf w₀ = some S := by
      by_cases hsS : s = S
      · simp only [w₀, hsS, ite_true]; rw [← hsS]; exact hsu
      · simp only [w₀, hsS, ite_false]
        have hsub : (s, S) ∈ c.subsorts := by
          simp only [leS, le_tables_eq, Bool.or_eq_true, beq_iff_eq, hsS, false_or, List.contains_iff_mem] at hle
          exact hle
        exact sortOf_inj.mpr ⟨hsub, hu, hsu, rfl⟩
    have hinj : injNormal S Srt.kitem w₀ = .inj s Srt.kitem u := by
      by_cases hsS : s = S
      · simp only [w₀, hsS, ite_true]; exact injNormal_of_not_inj hu
      · simp only [w₀, hsS, ite_false]; rfl
    have hσ₀ : c.WellSorted cl.vars [(0, w₀)] := by
      rw [hv]
      intro i s' hi
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨w₀, rfl, hw₀⟩
      | succ i => simp at hi
    have hm : PatVals c [(0, w₀)] cl.pats [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]] := by
      rw [hp]
      refine .cons (.ctor isCtor_kseq (.cons ?_ (.cons (.ctor isCtor_dotk .nil) .nil))) .nil
      rw [← hinj]
      exact .inj (.var rfl)
    have hRF := hF _ (hσ₀.at _) hm
    cases hRF with
    | intro ht _ _ => rw [hrq] at ht; cases ht
    | pre hf => rw [hclT] at hf; exact absurd hf.top_eq (by simp)
  cases h with
  | clause hfn' hmem hσ hmatch _ _ hprio _ hrhs _ _ =>
    rw [hfn] at hfn'
    cases hfn'
    rw [hcl] at hmem hprio
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [hrh] at hrhs
      cases hrhs
      rw [hv] at hσ
      rw [hp] at hmatch
      have hle := kseq_match hσ hmatch
      exact ⟨(fun h => by rw [hle] at h; cases h), fun _ _ _ => rfl⟩
    · rw [hor] at hrhs
      cases hrhs
      refine ⟨fun _ h => (by cases h), fun hle hu hsu => ?_⟩
      exact absurd (hprio _ (List.mem_cons_self ..) hna hpr) (hnf hle hu hsu)
  | rest hfn' hnone =>
    rw [hfn] at hfn'
    cases hfn'
    -- at an argument of its sort the `[owise]` clause applies, so the rest is never taken there
    have hrest : c.fnRest fn [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]] = none := by
      cases hr : c.fnRest fn [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]] with
      | none => rfl
      | some w =>
        exfalso
        have hsorts := (Semantics.fnRest_spec hr).2.1
        obtain ⟨hov, hop, hoq⟩ := sortPredOf_owise hS hcl
        have hK : c.sortOf (.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]) = some Srt.k := by
          cases hx : c.sortOf (.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]) with
          | none => simp [Semantics.sortsOf, hx] at hsorts
          | some x =>
            have hkq := KCore.lookupSig_ctorSigs_of_fixed (c := c) (L := [])
              (show lookupSig fixedCtors kseq = some _ from rfl)
            rw [List.append_nil] at hkq
            rcases c.sortOf_ctor_iff.mp hx with ⟨k, hk, -, rfl⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
            · rw [hkq] at hk; cases hk; rfl
            · rw [hkq] at hk; cases hk
            · rw [hkq] at hk; cases hk
        have hF := hnone o (by rw [hcl]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
        cases hF with
        | intro hF =>
        have hσo : c.WellSorted o.vars [(0, .ctor kseq [.inj s Srt.kitem u, .ctor dotk []])] := by
          rw [hov]
          intro i s' hi
          cases i with
          | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨_, rfl, hK⟩
          | succ i => simp at hi
        have hmo : PatVals c [(0, .ctor kseq [.inj s Srt.kitem u, .ctor dotk []])] o.pats
            [.ctor kseq [.inj s Srt.kitem u, .ctor dotk []]] := by
          rw [hop]; exact .cons (.var rfl) .nil
        cases hF _ (hσo.at _) hmo with
        | intro ht _ _ => rw [hoq] at ht; cases ht
        | pre hf => rw [hoT] at hf; exact absurd hf.top_eq (by simp)
    rw [hrest]
    refine ⟨fun _ h => (by cases h), fun hle hu hsu => ?_⟩
    exact absurd (hnone cl (by rw [hcl]; exact List.mem_cons_self ..)) (hnf hle hu hsu)
  | ensFails hfn' hmem _ _ _ _ hprio _ ht _ _ =>
    rw [hfn] at hfn'
    cases hfn'
    rw [hcl] at hmem hprio
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    refine ⟨fun _ h => (by cases h), fun hle hu hsu => ?_⟩
    rcases hmem with rfl | rfl
    · rw [hce] at ht; cases ht
    · exact absurd (hprio _ (List.mem_cons_self ..) hna hpr) (hnf hle hu hsu)
  | clauseEx hfn' hmem _ _ _ _ hprio hne hrhs _ _ _ =>
    -- the first clause has no existential variable; the `[owise]` clause's value is `false`
    rw [hfn] at hfn'
    cases hfn'
    rw [hcl] at hmem hprio
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact absurd hclX hne
    · rw [hor] at hrhs
      cases hrhs
      refine ⟨fun _ h => (by cases h), fun hle hu hsu => ?_⟩
      exact absurd (hprio _ (List.mem_cons_self ..) hna hpr) (hnf hle hu hsu)
  | exNone hfn' hmem hne _ _ _ _ hprio _ _ =>
    rw [hfn] at hfn'
    cases hfn'
    rw [hcl] at hmem hprio
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    refine ⟨fun _ h => (by cases h), fun hle hu hsu => ?_⟩
    rcases hmem with rfl | rfl
    · exact absurd hclX hne
    · exact absurd (hprio _ (List.mem_cons_self ..) hna hpr) (hnf hle hu hsu)

theorem refutes_sound {σ : Subst} {vs : List Srt} (hσ : c.WellSorted vs σ) {A : Term} {b : Bool}
    (hr : refutes c (tables c) vs (A, b) = true) (he : EvalTerm c σ A (some (bool b))) : False := by
  unfold refutes at hr
  split at hr
  · rename_i f a t b' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split at hr
    · cases hr
    · rename_i hnh
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hnh
      split at hr
      · rename_i fn hfn
        split at hr
        · rename_i S ss srt hS hsrc
          generalize hA : Term.app f _ = A' at he
          generalize hres : some (bool b) = r at he
          cases he with
          | ctor hk _ => cases hA; rw [show c.isCtor f = false from hnh.1.2] at hk; cases hk
          | hook _ hhk _ _ _ => cases hA; rw [hnh.1.1] at hhk; cases hhk
          | param _ _ hp _ _ => cases hA; rw [hnh.2] at hp; cases hp
          | callUndef _ _ _ _ _ => cases hA; cases hres
          | @call _ _ _ rs vs₁ _ _ _ hts hvs hev _ =>
            cases hA
            obtain ⟨r₁, rfl, h₁⟩ := evalTerms_one hts
            cases r₁ with
            | none => simp [allSome] at hvs
            | some v₁ =>
            simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
            subst hvs
            obtain ⟨rs₂, hts₂, hv₁⟩ := EvalTerm.ctor_inv isCtor_kseq h₁
            obtain ⟨rX, rD, rfl, hX, hD⟩ := evalTerms_two hts₂
            obtain ⟨rs₃, hts₃, hrD⟩ := EvalTerm.ctor_inv isCtor_dotk hD
            cases hts₃
            obtain ⟨r', hr', hrX⟩ := EvalTerm.inj_inv hX
            cases r' with
            | none =>
              simp only [Option.map_none] at hrX
              subst hrX
              simp [allSome] at hv₁
            | some wt =>
            simp only [Option.map_some] at hrX
            subst hrX hrD
            simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hv₁
            subst hv₁
            obtain ⟨s, u, hsu, hs, hu, hsrt⟩ := srcs_eval hσ t a wt ss srt hr' hsrc Srt.kitem
            rw [hsu] at hev
            have hP := sortPred_eval hfn hS hev
            cases b with
            | true =>
              simp only [ite_true, List.all_eq_true, Bool.not_eq_true'] at hr
              exact hP.1 (hr s hs) hres.symm
            | false =>
              simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, List.all_eq_true] at hr
              have := hP.2 (hr.2 s hs) hu (hsrt hr.1)
              rw [← hres] at this
              exact absurd (bool_inj (Option.some.inj this)) (by simp)
          | ovl _ ho _ => cases hA; rw [c.isOvl_of_lookupFn hfn] at ho; cases ho
          | ovlFn _ ho => cases hA; rw [c.isOvl_of_lookupFn hfn] at ho; cases ho
          | _ => cases hA
        · cases hr
      · cases hr
  · cases hr

/-! ## Two rules apart -/

section
variable (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
  (hmo : CoherentAll c)

mutual
/-- A pure term's value does not depend on the interpretation of the parameters. -/
theorem evalT_pure (c : Semantics) (H : HookParams) : ∀ (n : Nat) (σ : Subst) (A : Term),
    pureT c A = true → evalT (c.withHooks H) n σ A = evalT c n σ A
  | 0, _, _, _ => rfl
  | n + 1, σ, .var i, _ => rfl
  | n + 1, σ, .dv s l, _ => rfl
  | n + 1, σ, .as _ _, h => by simp [pureT] at h
  | n + 1, σ, .inj a b t, h => by
    simp only [pureT] at h
    simp only [evalT, evalT_pure c H n σ t h]
  | n + 1, σ, .app f ts, h => by
    simp only [pureT, Bool.and_eq_true] at h
    obtain ⟨hf, hts⟩ := h
    have hc : (c.withHooks H).isCtor f = c.isCtor f := rfl
    simp only [evalT, evalTs_pure c H n σ ts hts, hc]
    rcases Bool.or_eq_true_iff.mp hf with hf | hf
    · simp [hf]
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      simp [hf.1, Semantics.hookRes_of_notKey hf.2]
theorem evalTs_pure (c : Semantics) (H : HookParams) : ∀ (n : Nat) (σ : Subst) (ts : List Term),
    pureL c ts = true → evalTs (c.withHooks H) n σ ts = evalTs c n σ ts
  | 0, _, _, _ => rfl
  | n + 1, σ, [], _ => rfl
  | n + 1, σ, t :: ts, h => by
    simp only [pureL, Bool.and_eq_true] at h
    simp only [evalTs, evalT_pure c H n σ t h.1, evalTs_pure c H n σ ts h.2]
end

include hok hsr hmr hmo in
theorem groundRefutes_sound {vs : List Srt} {σ : Subst} (hσ : c.WellSorted vs σ) {A : Term} {b : Bool}
    (hr : groundRefutes c (tables c) vs (A, b) = true) (he : EvalTerm c σ A (some (bool b))) : False := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  have hmi := hmo
  simp only [groundRefutes, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hr
  obtain ⟨⟨⟨hpure, hv⟩, hs⟩, hev⟩ := hr
  rw [evalT_pure c _ litFuel [] A hpure] at hev
  have hc : evalT c litFuel σ A = evalT c litFuel [] A :=
    evalT_congr litFuel (fun i hi => by rw [hv] at hi; cases hi)
  split at hev
  · rename_i w hw
    rw [← hc] at hw
    have := evalTerm_det hmi (evalT_sound hsc hcc hmc litFuel hw headsOK_fns hσ hs) he
    rw [Option.some.injEq] at this
    subst this
    rw [same_iff.mpr rfl] at hev; cases hev
  · rename_i hw
    rw [← hc] at hw
    have := evalTerm_det hmi (evalT_sound hsc hcc hmc litFuel hw headsOK_fns hσ hs) he
    cases this
  · cases hev

include hok hsr hmr hmo in
theorem clashes_sound {vs : List Srt} {σ : Subst} (hσ : c.WellSorted vs σ) {L : List (Term × Bool)}
    (hL : ∀ A b, (A, b) ∈ L → EvalTerm c σ A (some (bool b))) (h : clashes c (tables c) vs L = true) : False := by
  simp only [clashes, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (⟨⟨A, b⟩, hm, hr⟩ | ⟨⟨A, b⟩, hm, hr⟩) | ⟨⟨A, b⟩, hm, ⟨A', b'⟩, hm', hc⟩
  · exact refutes_sound hσ hr (hL A b hm)
  · exact groundRefutes_sound hok hsr hmr hmo hσ hr (hL A b hm)
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨hb, he⟩, -⟩ := hc
    have he := Term.beq_sound he
    subst he
    have := evalTerm_det (hmo) (hL A b hm) (hL A b' hm')
    exact hb (bool_inj (Option.some.inj this))

include hok hsr hmr hmo in
/-- Two rules that `apart` separates never both apply to one configuration. -/
theorem apart_sound {r r' : Rule} (hr : r ∈ c.rules) (hr' : r' ∈ c.rules) (hap : apart c (tables c) r r' = true)
    {x : GroundTerm} {σ σ' : Subst}
    (hσ : c.WellSorted r.vars σ) (hm : PatVal c σ r.lhs x)
    (hq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hσ' : c.WellSorted r'.vars σ') (hm' : PatVal c σ' r'.lhs x)
    (hq' : ∀ t, r'.req = some t → EvalTerm c σ' t (some (bool true))) : False := by
  have hmc := matchCtx_of hmr
  obtain ⟨hlt, -, -, -, -⟩ := ruleOK_of hok hr
  obtain ⟨hlt', -, -, -, -⟩ := ruleOK_of hok hr'
  obtain ⟨C, hC, hR⟩ := meet_sound hmc hσ hσ' r.lhs r'.lhs hm hm' hlt hlt'
  unfold apart at hap
  rw [hC] at hap
  refine clashes_sound hok hsr hmr hmo hσ' (fun A b hAb => ?_) hap
  rcases List.mem_append.mp hAb with hAb | hAb
  · unfold litsL at hAb
    split at hAb
    · rename_i t ht
      obtain ⟨⟨A₀, b₀⟩, hm₀, he₀⟩ := List.mem_filterMap.mp hAb
      obtain ⟨A₁, htr, he₁⟩ := Option.map_eq_some_iff.mp he₀
      simp only [Prod.mk.injEq] at he₁
      obtain ⟨rfl, rfl⟩ := he₁
      exact tr_sound (fun i q h => envOf_sound hmc hR h) (lits_sound (hq t ht) hm₀) htr
    · simp at hAb
  · unfold litsR at hAb
    split at hAb
    · rename_i t ht
      exact lits_sound (hq' t ht) hAb
    · simp at hAb

end

/-! ## Head keys: a value's key at a path is among those its pattern allows -/

/-- The argument of an injection (a value that is not an injection is its own). -/
def injChild : GroundTerm → GroundTerm
  | .inj _ _ u => u
  | .ctor f vs => .ctor f vs
  | .dv s l => .dv s l
  | .map s es => .map s es
  | .set s es => .set s es
  | .list s es => .list s es

theorem injNormal_child (a b : Srt) (w : GroundTerm) : ∃ s, injNormal a b w = .inj s b (injChild w) := by
  cases w <;> exact ⟨_, rfl⟩

theorem injChild_injNormal (a b : Srt) (w : GroundTerm) : injChild (injNormal a b w) = injChild w := by
  cases w <;> rfl

theorem injNormal_retarget {a b b' s : Srt} {w u : GroundTerm} (h : injNormal a b w = .inj s b u) :
    injNormal a b' w = .inj s b' u := by
  cases w <;> (injection h with h1 h2 h3; subst h1; subst h3; rfl)

theorem vkey_inj_cons (a b : Srt) (w : GroundTerm) (P : List Nat) :
    vkey (injNormal a b w) (0 :: P) = vkey (injChild w) P := by
  obtain ⟨s, h⟩ := injNormal_child a b w
  rw [h, vkey]

mutual
  /-- Evaluating a pattern as a term gives only its value. -/
  theorem PatVal.strip_det (hmc : MatchCtx c) {σ : Subst} : ∀ {p : Term} {w : GroundTerm} {r : Option GroundTerm},
      PatVal c σ p w → EvalTerm c σ (strip p) r → r = some w
    | _, _, _, .var h, he => by rw [strip] at he; rw [EvalTerm.var_inv he, h]
    | _, _, _, .dv, he => by rw [strip] at he; cases he; rfl
    | _, _, _, .ctor hc hs, he => by
      rw [strip] at he
      obtain ⟨rs, hts, rfl⟩ := EvalTerm.ctor_inv hc he
      rw [PatVals.strip_det hmc hs hts, allSome_map_some]; rfl
    | _, _, _, .hook (f := f) hp hs hv, he => by
      rw [strip] at he
      have hc := hmc.patHooks f (List.contains_iff_mem.mp hp)
      have hh := patternHooks_isHook hp
      generalize ht : Term.app f (stripList _) = t at he
      cases he with
      | ctor h _ => cases ht; rw [hc] at h; cases h
      | hook _ _ hts hh' _ =>
        cases ht
        rw [PatVals.strip_det hmc hs hts] at hh'
        have := hh' _ (allSome_map_some _)
        rw [Semantics.hookRes_of_value hv] at this
        exact (Option.some.inj this).symm
      | param _ h _ _ _ => cases ht; rw [hh] at h; cases h
      | call _ h _ _ _ _ => cases ht; rw [hh] at h; cases h
      | callUndef _ h _ _ _ => cases ht; rw [hh] at h; cases h
      | ovl _ ho _ => cases ht; rw [c.isOvl_of_patternHook hp] at ho; cases ho
      | ovlFn _ ho => cases ht; rw [c.isOvl_of_patternHook hp] at ho; cases ho
      | _ => cases ht
    | _, _, _, .coll (f := f) hc hp hs hv, he => by
      rw [strip] at he
      unfold Semantics.collVal at hv
      generalize ht : Term.app f (stripList _) = t at he
      cases he with
      | ctor h _ => cases ht; rw [hc] at h; cases h
      | hook _ hhk hts hh' _ =>
        cases ht
        rw [if_pos hhk] at hv
        rw [PatVals.strip_det hmc hs hts] at hh'
        have := hh' _ (allSome_map_some _)
        rw [Semantics.hookRes_of_value (Option.join_eq_some_iff.mp hv)] at this
        exact (Option.some.inj this).symm
      | param _ hhk _ hts hr =>
        cases ht
        rw [if_neg (by simp [hhk])] at hv
        rw [PatVals.strip_det hmc hs hts, allSome_map_some] at hr
        rw [hr]; exact hv
      | call _ hhk _ _ _ hp' =>
        cases ht
        unfold Semantics.isCollPat at hp; rw [hhk] at hp
        unfold Semantics.isParam at hp'
        cases hk : c.lookupParam f with
        | none => rw [hk] at hp; simp at hp
        | some _ => rw [hk] at hp'; cases hp'
      | callUndef _ _ hts hvs _ =>
        cases ht
        rw [PatVals.strip_det hmc hs hts, allSome_map_some] at hvs; cases hvs
      | ovl _ ho _ => cases ht; rw [c.isOvl_of_collPat hp] at ho; cases ho
      | ovlFn _ ho => cases ht; rw [c.isOvl_of_collPat hp] at ho; cases ho
      | _ => cases ht
    | _, _, _, .inj h, he => by
      rw [strip] at he
      obtain ⟨r', h', rfl⟩ := EvalTerm.inj_inv he
      rw [PatVal.strip_det hmc h h']; rfl
    | _, _, _, .as h _, he => by rw [strip] at he; exact PatVal.strip_det hmc h he
    | _, _, _, .ovl _ ho hs hv, he => by
      rw [strip] at he
      obtain ⟨rs, hts, rfl⟩ := EvalTerm.ovl_inv ho (OvlLaws.fnCover_none_of_nil hmc.noOvl _) he
      rw [PatVals.strip_det hmc hs hts, allSome_map_some, Option.map_some, hv]
  theorem PatVals.strip_det (hmc : MatchCtx c) {σ : Subst} : ∀ {ps : List Term} {ws : List GroundTerm}
      {rs : List (Option GroundTerm)}, PatVals c σ ps ws → EvalTerms c σ (stripList ps) rs → rs = ws.map some
    | _, _, _, .nil, he => by rw [stripList] at he; cases he; rfl
    | _, _, _, .cons h hs, he => by
      rw [stripList] at he
      obtain ⟨r, rs', rfl, h1, h2⟩ := EvalTerms.cons_inv he
      rw [PatVal.strip_det hmc h h1, PatVals.strip_det hmc hs h2]; rfl
end

/-- A sort predicate's literal `isS(kseq(u, dotk)) = b` evaluates its argument. -/
theorem sortLit_eval {σ : Subst} {f : Sym} {u : Term} {b : Bool} (hnh : isHook f = false)
    (hnc : c.isCtor f = false) (hnp : c.isParam f = false) (hno : c.isOvl f = false)
    (he : EvalTerm c σ (.app f [.app kseq [u, .app dotk []]]) (some (bool b))) :
    ∃ v, EvalTerm c σ u (some v) ∧ Eval c f [.ctor kseq [v, .ctor dotk []]] (some (bool b)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTerm.call_inv hnc hnh hnp hno he
  obtain ⟨r₁, rfl, h₁⟩ := evalTerms_one hts
  rcases hcase with ⟨vs₁, hvs, hev⟩ | ⟨_, hr⟩
  · cases r₁ with
    | none => simp [allSome] at hvs
    | some v₁ =>
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      obtain ⟨rs₂, hts₂, hv₁⟩ := EvalTerm.ctor_inv isCtor_kseq h₁
      obtain ⟨rX, rD, rfl, hX, hD⟩ := evalTerms_two hts₂
      obtain ⟨rs₃, hts₃, hrD⟩ := EvalTerm.ctor_inv isCtor_dotk hD
      cases hts₃
      cases rX with
      | none => simp [allSome] at hv₁
      | some w =>
        subst hrD
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨w, hX, hev⟩
  · cases hr

/-- A literal's bound holds of the injection's source sort. -/
theorem litBound_sound (hmc : MatchCtx c) {σ : Subst} {a b : Srt} {p : Term} {js : List Nat}
    {w u : GroundTerm} {s : Srt} (hp : PatVal c σ p w) (hsu : injNormal a b w = .inj s b u)
    (hjs : ∀ j ∈ js, σ.lookup j = some (injNormal a b w)) {l : Term × Bool} {T : Srt}
    (hl : EvalTerm c σ l.1 (some (bool l.2))) (hb : litBound c a b p js l = some T) : leS (tables c) s T = true := by
  obtain ⟨A, bb⟩ := l
  unfold litBound at hb
  split at hb
  · rename_i f u' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split at hb
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨hit, hnh⟩, hnc⟩, hnp⟩ := hc
      obtain ⟨fn, hfn, hS⟩ := Option.bind_eq_some_iff.mp hb
      obtain ⟨v', hu, hev⟩ := sortLit_eval hnh hnc hnp (c.isOvl_of_lookupFn hfn) hl
      have hv' : v' = .inj s Srt.kitem u := by
        cases u' with
        | inj a' b' t =>
          simp only [litHit, Bool.and_eq_true, beq_iff_eq] at hit
          obtain ⟨⟨rfl, rfl⟩, ht⟩ := hit
          have ht := Term.beq_sound ht
          subst ht
          obtain ⟨r', h', hr'⟩ := EvalTerm.inj_inv hu
          rw [PatVal.strip_det hmc hp h'] at hr'
          simp only [Option.map_some, Option.some.injEq] at hr'
          rw [hr']; exact injNormal_retarget hsu
        | var j =>
          simp only [litHit, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hit
          obtain ⟨rfl, hj⟩ := hit
          have := (EvalTerm.var_inv hu).trans (hjs j hj)
          rw [hsu] at this
          exact Option.some.inj this
        | _ => simp [litHit] at hit
      subst hv'
      cases hle : leS (tables c) s T with
      | true => rfl
      | false =>
        exact absurd rfl ((sortPred_eval hfn hS hev).1 hle)
    · cases hb
  · cases hb

section Keys
variable (hmc : MatchCtx c) {σ : Subst} {vs : List Srt} {L : List (Term × Bool)}
  (hσ : c.WellSorted vs σ) (hL : ∀ l ∈ L, EvalTerm c σ l.1 (some (bool l.2)))
include hmc hσ hL

theorem srcKey_sound (js : List Nat) {a b : Srt} {p : Term} {w : GroundTerm} {K : List Key}
    (hp : PatVal c σ p w) (hjs : ∀ j ∈ js, σ.lookup j = some (injNormal a b w))
    (h : (srcs c (tables c) vs a p).map (fun (S, _) => (refineSrcs c (tables c) a b p js L S).map Key.src) = some K) :
    ∃ k, vkey (injNormal a b w) [] = some k ∧ k ∈ K := by
  obtain ⟨⟨S, srt⟩, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨s, u, hsu, hsS⟩ := srcs_pat hmc hσ hp hs b
  refine ⟨.src s, by rw [hsu, vkey], List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hsS, ?_⟩, rfl⟩⟩
  rw [List.all_eq_true]
  intro l hl
  split
  · rename_i T hT; exact litBound_sound hmc hp hsu hjs (hL l hl) hT
  · rfl

omit hmc hσ hL in
theorem ctorKey {f : Sym} {ps : List Term} {v : GroundTerm} (hv : PatVal c σ (.app f ps) v)
    (hc : (c.isCtor f && !patternHooks.contains f) = true) :
    ∃ vs', v = .ctor f vs' ∧ PatVals c σ ps vs' := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨-, vs', rfl, hs⟩ := PatVal.app_inv hc.2 hv hc.1
  exact ⟨vs', rfl, hs⟩

mutual
  theorem pkeys_sound : ∀ (p : Term) (P : List Nat) {v : GroundTerm} {K : List Key},
      PatVal c σ p v → pkeys c (tables c) vs L p P = some K → ∃ k, vkey v P = some k ∧ k ∈ K
    | .as p j, [], _, _, hv, h => by
      obtain ⟨hp, hj⟩ := PatVal.as_inv hv
      rw [pkeys] at h
      exact pkeysAs_sound p [j] hp (by simpa using hj) h
    | .as p _, i :: P, _, _, hv, h => by
      rw [pkeys] at h
      exact pkeys_sound p (i :: P) (PatVal.as_inv hv).1 h
    | .app f ps, [], _, _, hv, h => by
      rw [pkeys] at h
      split at h
      · rename_i hc
        obtain ⟨vs', rfl, -⟩ := ctorKey hv hc
        cases h; exact ⟨_, by rw [vkey], List.mem_singleton_self _⟩
      · cases h
    | .app f ps, i :: P, _, _, hv, h => by
      rw [pkeys] at h
      split at h
      · rename_i hc
        obtain ⟨vs', rfl, hs⟩ := ctorKey hv hc
        rw [vkey]; exact pkeysL_sound ps i P hs h
      · cases h
    | .dv s l, [], _, _, hv, h => by
      rw [pkeys] at h; cases h; rw [PatVal.dv_shape hv]; exact ⟨_, by rw [vkey], List.mem_singleton_self _⟩
    | .dv _ _, _ :: _, _, _, _, h => by simp [pkeys] at h
    | .inj a b p, [], _, _, hv, h => by
      obtain ⟨w, hp, rfl⟩ := PatVal.inj_inv hv
      rw [pkeys] at h
      exact srcKey_sound hmc hσ hL [] hp (by simp) h
    | .inj a b p, 0 :: P, _, _, hv, h => by
      obtain ⟨w, hp, rfl⟩ := PatVal.inj_inv hv
      rw [pkeys] at h
      rw [vkey_inj_cons]; exact pkeysI_sound p P hp h
    | .inj _ _ _, (_ + 1) :: _, _, _, _, h => by simp [pkeys] at h
    | .var _, _, _, _, _, h => by simp [pkeys] at h
  theorem pkeysAs_sound : ∀ (p : Term) (js : List Nat) {v : GroundTerm} {K : List Key},
      PatVal c σ p v → (∀ j ∈ js, σ.lookup j = some v) → pkeysAs c (tables c) vs L js p = some K →
      ∃ k, vkey v [] = some k ∧ k ∈ K
    | .as p j, js, _, _, hv, hjs, h => by
      obtain ⟨hp, hj⟩ := PatVal.as_inv hv
      rw [pkeysAs] at h
      exact pkeysAs_sound p (j :: js) hp (fun j' hj' => by
        rcases List.mem_cons.mp hj' with rfl | hj'
        · exact hj
        · exact hjs j' hj') h
    | .app f ps, _, _, _, hv, _, h => by
      rw [pkeysAs] at h
      split at h
      · rename_i hc
        obtain ⟨vs', rfl, -⟩ := ctorKey hv hc
        cases h; exact ⟨_, by rw [vkey], List.mem_singleton_self _⟩
      · cases h
    | .dv s l, _, _, _, hv, _, h => by
      rw [pkeysAs] at h; cases h; rw [PatVal.dv_shape hv]; exact ⟨_, by rw [vkey], List.mem_singleton_self _⟩
    | .inj a b p, js, _, _, hv, hjs, h => by
      obtain ⟨w, hp, rfl⟩ := PatVal.inj_inv hv
      rw [pkeysAs] at h
      exact srcKey_sound hmc hσ hL js hp hjs h
    | .var _, _, _, _, _, _, h => by simp [pkeysAs] at h
  theorem pkeysI_sound : ∀ (p : Term) (P : List Nat) {w : GroundTerm} {K : List Key},
      PatVal c σ p w → pkeysI c (tables c) vs L p P = some K → ∃ k, vkey (injChild w) P = some k ∧ k ∈ K
    | .as q _, P, _, _, hv, h => by
      rw [pkeysI] at h; exact pkeysI_sound q P (PatVal.as_inv hv).1 h
    | .inj _ _ q, P, _, _, hv, h => by
      obtain ⟨w', hq, rfl⟩ := PatVal.inj_inv hv
      rw [pkeysI] at h; rw [injChild_injNormal]; exact pkeysI_sound q P hq h
    | .app f ps, [], _, _, hv, h => by
      rw [pkeysI] at h
      split at h
      · rename_i hc
        obtain ⟨vs', rfl, -⟩ := ctorKey hv hc
        cases h; exact ⟨_, by rw [injChild, vkey], List.mem_singleton_self _⟩
      · cases h
    | .app f ps, i :: P, _, _, hv, h => by
      rw [pkeysI] at h
      split at h
      · rename_i hc
        obtain ⟨vs', rfl, hs⟩ := ctorKey hv hc
        rw [injChild, vkey]; exact pkeysL_sound ps i P hs h
      · cases h
    | .dv s l, [], _, _, hv, h => by
      rw [pkeysI] at h; cases h; rw [PatVal.dv_shape hv]; exact ⟨_, by rw [injChild, vkey], List.mem_singleton_self _⟩
    | .dv _ _, _ :: _, _, _, _, h => by simp [pkeysI] at h
    | .var _, _, _, _, _, h => by simp [pkeysI] at h
  theorem pkeysL_sound : ∀ (ps : List Term) (i : Nat) (P : List Nat) {ws : List GroundTerm} {K : List Key},
      PatVals c σ ps ws → pkeysL c (tables c) vs L ps i P = some K → ∃ k, vkeyL ws i P = some k ∧ k ∈ K
    | [], _, _, _, _, _, h => by simp [pkeysL] at h
    | p :: _, 0, P, _, _, hs, h => by
      obtain ⟨v, ws', rfl, hp, -⟩ := PatVals.cons_inv hs
      rw [pkeysL] at h; rw [vkeyL]; exact pkeys_sound p P hp h
    | _ :: ps, i + 1, P, _, _, hs, h => by
      obtain ⟨v, ws', rfl, -, hs'⟩ := PatVals.cons_inv hs
      rw [pkeysL] at h; rw [vkeyL]; exact pkeysL_sound ps i P hs' h
end

end Keys

/-! ## Determinism -/

/-- Rule r applies to x: a well-sorted match whose `requires` is true. -/
def Applies (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x ∧ ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))

theorem litsR_sound {r : Rule} {σ : Subst} (hq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) :
    ∀ l ∈ litsR r, EvalTerm c σ l.1 (some (bool l.2)) := by
  intro ⟨A, b⟩ hl
  unfold litsR at hl
  split at hl
  · rename_i t ht; exact lits_sound (hq t ht) hl
  · simp at hl

/-- A rule that applies at x has, at each path, a key that x has there. -/
theorem ruleKeys_sound (hmc : MatchCtx c) {r : Rule} {x : GroundTerm} (ha : Applies c r x) :
    ∀ P K, pkeys c (tables c) r.vars (litsR r) r.lhs P = some K → ∃ k, vkey x P = some k ∧ k ∈ K := by
  obtain ⟨σ, hσ, hm, hq⟩ := ha
  intro P K h
  exact pkeys_sound hmc hσ (litsR_sound hq) r.lhs P hm h

theorem compat_map {x : GroundTerm} {f g : List Nat → Option (List Key)}
    (hf : ∀ P K, f P = some K → ∃ k, vkey x P = some k ∧ k ∈ K)
    (hg : ∀ P K, g P = some K → ∃ k, vkey x P = some k ∧ k ∈ K) :
    ∀ paths : List (List Nat), compat (paths.map f) (paths.map g) = true
  | [] => rfl
  | P :: ps => by
    have ih := compat_map hf hg ps
    simp only [List.map_cons]
    cases hfP : f P with
    | none => cases hgP : g P <;> simp [compat, ih]
    | some K =>
      cases hgP : g P with
      | none => simp [compat, ih]
      | some K' =>
        obtain ⟨k, hk, hkK⟩ := hf P K hfP
        obtain ⟨k', hk', hkK'⟩ := hg P K' hgP
        rw [hk] at hk'; cases hk'
        simp only [compat, ih, Bool.and_true, List.any_eq_true, List.contains_iff_mem]
        exact ⟨k, hkK, hkK'⟩

/-- What `idxOK` says of rule i. -/
theorem idxOK_spec {ix : DetIndex} (h : idxOK c (tables c) ix = true) {i : Nat} (hi : i < c.rules.length) :
    ∃ ks, ix.keys[i]? = some ks ∧ ks = ruleKeys c (tables c) ix.paths c.rules[i] ∧
      ∀ p < ix.paths.length, (∀ K, ks[p]? = some (some K) → ∀ k ∈ K, i ∈ ix.bucket p k) ∧
        (ks[p]? = some none → i ∈ ix.wildAt p) := by
  simp only [idxOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  have h := hall i hi
  have hik : i < ix.keys.length := hlen ▸ hi
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hik] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hks, hp⟩ := h
  refine ⟨_, List.getElem?_eq_getElem hik, hks, fun p hpl => ⟨fun K hK k hk => ?_, fun hK => ?_⟩⟩
  · have := hp p hpl
    rw [hK] at this
    simp only [List.all_eq_true, List.contains_iff_mem] at this
    exact this k hk
  · have := hp p hpl
    rw [hK] at this
    simpa [List.contains_iff_mem] using this

theorem mem_cands {ix : DetIndex} {n i j : Nat} {ks : List (Option (List Key))} (hj : j < n)
    (H : ∀ p K, ks[p]? = some (some K) → (∃ k ∈ K, j ∈ ix.bucket p k) ∨ j ∈ ix.wildAt p) :
    j ∈ ix.cands n i ks := by
  unfold DetIndex.cands
  split
  · rename_i p _
    split
    · rename_i K hK
      rcases H p K hK with ⟨k, hk, hb⟩ | hw
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, hk, hb⟩)
      · exact List.mem_append_right _ hw
    · exact List.mem_range.mpr hj
  · exact List.mem_range.mpr hj

theorem row_of {ix : DetIndex} {ovl : List (Nat × Nat)} (hd : detOKExcept c (tables c) ix ovl = true) {i : Nat}
    (hi : i < c.rules.length) : detRow c (tables c) ix ovl i = true := by
  simp only [detOKExcept, detRows, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at hd
  exact hd.2 i ⟨Nat.zero_le _, by simpa using hi⟩

/-- Every rule's match fixes its right-hand side (each row checks its rule). -/
theorem uniq_of {ix : DetIndex} {ovl : List (Nat × Nat)} (hd : detOKExcept c (tables c) ix ovl = true) :
    ∀ r ∈ c.rules, uniqOK c r = true := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hrow := row_of hd hi
  have hidx : idxOK c (tables c) ix = true := by simp only [detOKExcept, Bool.and_eq_true] at hd; exact hd.1
  obtain ⟨ks, hks, -⟩ := idxOK_spec hidx hi
  unfold detRow at hrow
  rw [List.getElem?_eq_getElem hi, hks] at hrow
  simp only [Bool.and_eq_true] at hrow
  exact hrow.1

/-- Two rules that both apply at x: the second is among the first's candidates, and their keys are
compatible (the index is the rules', `idxOK`). -/
theorem cand_of_applies (hmc : MatchCtx c) {ix : DetIndex} (hidx : idxOK c (tables c) ix = true)
    {x : GroundTerm} {i j : Nat} (hi : i < c.rules.length) (hj : j < c.rules.length)
    (hai : Applies c c.rules[i] x) (haj : Applies c c.rules[j] x) :
    ∃ ks ks', ix.keys[i]? = some ks ∧ ix.keys[j]? = some ks' ∧ j ∈ ix.cands c.rules.length i ks ∧
      compat ks ks' = true := by
  obtain ⟨ks, hks, hkr, -⟩ := idxOK_spec hidx hi
  obtain ⟨ks', hks', hkr', hidxj⟩ := idxOK_spec hidx hj
  refine ⟨ks, ks', hks, hks', mem_cands hj fun p K hK => ?_, ?_⟩
  · rw [hkr, ruleKeys, List.getElem?_map] at hK
    cases hpp : ix.paths[p]? with
    | none => rw [hpp] at hK; cases hK
    | some P =>
      rw [hpp] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      obtain ⟨k, hk, hkK⟩ := ruleKeys_sound hmc hai P K hK
      have hpl : p < ix.paths.length := (List.getElem?_eq_some_iff.mp hpp).1
      have hkj : ks'[p]? = some (pkeys c (tables c) c.rules[j].vars (litsR c.rules[j]) c.rules[j].lhs P) := by
        rw [hkr', ruleKeys, List.getElem?_map, hpp]; rfl
      cases hK' : pkeys c (tables c) c.rules[j].vars (litsR c.rules[j]) c.rules[j].lhs P with
      | none => exact .inr ((hidxj p hpl).2 (by rw [hkj, hK']))
      | some K' =>
        obtain ⟨k', hk', hkK'⟩ := ruleKeys_sound hmc haj P K' hK'
        rw [hk] at hk'; cases hk'
        exact .inl ⟨k, hkK, (hidxj p hpl).1 K' (by rw [hkj, hK']) k hkK'⟩
  · rw [hkr, hkr', ruleKeys, ruleKeys]
    exact compat_map (ruleKeys_sound hmc hai) (ruleKeys_sound hmc haj) _

/-- Two rules i < j that both apply at x: the pair passes `pairOK` (row i, its candidates). -/
theorem pair_of_rows (hmc : MatchCtx c) {ix : DetIndex} {ovl : List (Nat × Nat)}
    (hd : detOKExcept c (tables c) ix ovl = true) {x : GroundTerm} {i j : Nat} (hij : i < j) (hj : j < c.rules.length)
    (hai : Applies c (c.rules[i]'(Nat.lt_trans hij hj)) x) (haj : Applies c c.rules[j] x) :
    pairOK c (tables c) ovl i j (c.rules[i]'(Nat.lt_trans hij hj)) c.rules[j] = true := by
  have hi : i < c.rules.length := Nat.lt_trans hij hj
  have hidx : idxOK c (tables c) ix = true := by simp only [detOKExcept, Bool.and_eq_true] at hd; exact hd.1
  obtain ⟨ks, ks', hks, hks', hmem, hc⟩ := cand_of_applies hmc hidx hi hj hai haj
  have hrow := row_of hd hi
  unfold detRow at hrow
  rw [List.getElem?_eq_getElem hi, hks] at hrow
  simp only [Bool.and_eq_true, List.all_eq_true] at hrow
  have := hrow.2 j hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with hle | h
  · omega
  · rw [List.getElem?_eq_getElem hj, hks'] at h
    simpa [hc] using h

theorem pairOK_symm (ovl : List (Nat × Nat)) (i j : Nat) (r r' : Rule) :
    pairOK c (tables c) ovl i j r r' = pairOK c (tables c) ovl j i r' r := by
  simp only [pairOK]
  rw [bne_comm]
  generalize (r'.prio != r.prio) = a0
  generalize apart c (tables c) r r' = a1
  generalize apart c (tables c) r' r = a2
  generalize sameRule r r' = a3
  generalize sameRule r' r = a4
  generalize ovl.contains (i, j) = a5
  generalize ovl.contains (j, i) = a6
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> rfl

/-! ## Determinism as a kind

An index is a pair of rules (i, j), i ≤ j: the diagonal (i, i), and each candidate j after i whose
keys are compatible (`detPairs`, the rows of `detIdx`). The obligation at (i, j) is that two steps
from one configuration where `Inv` holds, by rules i and j, reach one configuration (`JoinsOn`).
Every pair of steps from a configuration is of one of these pairs (`joins_glue`, by the index:
`cand_of_applies`), so the obligations give determinism where `Inv` holds (`kind`).

The decider (`detCond`): at (i, i), the rule's match fixes its right-hand side (`uniqOK`); at
(i, j), i < j, the rules have different priorities, are apart, or are alike with a match that
fixes the right-hand side (`pairCond`). An index it does not confirm is an obligation: an overlap
(i, j), or a rule (i, i) whose match is not shown to fix its right-hand side. -/

/-- Rule r rewrites x to y: `Step`'s premises for that rule, its premise predicate `pre` and its
right-side predicate `post` holding among them, in `Step.rule`'s order. -/
def StepBy (c : Semantics) (r : Rule) (x y : GroundTerm) : Prop :=
  ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
    Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y) ∧
    (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true ∧
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x

theorem stepBy_of_step {x y : Config c} (h : Step c x y) : ∃ r ∈ c.rules, StepBy c r x.val y.val := by
  cases h with
  | rule r mem σ hσ hm hreq hpr he hens hpo hp => exact ⟨r, mem, σ, hσ, hm, hreq, hpr, he, hens, hpo, hp⟩

/-- A step by a rule of the definition is a step; `pre` and `post` are read from `StepBy`. -/
theorem step_of_stepBy_pp {r : Rule} (mem : r ∈ c.rules) {x y : Config c} (h : StepBy c r x.val y.val) :
    Step c x y := by
  obtain ⟨σ, hσ, hm, hreq, hpr, he, hens, hpo, hp⟩ := h
  exact .rule r mem σ hσ hm hreq hpr he hens hpo hp

/-- `step_of_stepBy_pp` at a rule whose predicates are `\top` (the hypotheses on them are no longer
read). -/
theorem step_of_stepBy {r : Rule} (mem : r ∈ c.rules) (hpre : r.pre = .top) (hpost : r.post = .top)
    {x y : Config c} (h : StepBy c r x.val y.val) : Step c x y :=
  step_of_stepBy_pp mem h

/-- **`Step` is a step by one of the definition's rules.** -/
theorem step_iff_stepBy {x y : Config c} : Step c x y ↔ ∃ r ∈ c.rules, StepBy c r x.val y.val :=
  ⟨stepBy_of_step, fun ⟨_, mem, h⟩ => step_of_stepBy_pp mem h⟩

theorem StepBy.applies {r : Rule} {x y : GroundTerm} (h : StepBy c r x y) : Applies c r x :=
  let ⟨σ, hσ, hm, hq, _⟩ := h; ⟨σ, hσ, hm, hq⟩

/-- **The obligation at a pair of rules**: from a configuration where `Inv` holds, a step by rule i
and a step by rule j reach one configuration. -/
def JoinsOn (c : Semantics) (Inv : Config c → Prop) (i j : Nat) : Prop :=
  ∀ r r', c.rules[i]? = some r → c.rules[j]? = some r' → ∀ x y y' : Config c, Inv x →
    StepBy c r x.val y.val → StepBy c r' x.val y'.val → y = y'

theorem JoinsOn.swap {Inv : Config c → Prop} {i j : Nat} (h : JoinsOn c Inv i j) : JoinsOn c Inv j i :=
  fun r r' hr hr' x y y' hx hb hb' => (h r' r hr' hr x y' y hx hb' hb).symm

theorem JoinsOn.mono {Inv Inv' : Config c → Prop} {i j : Nat} (hI : ∀ x, Inv' x → Inv x)
    (h : JoinsOn c Inv i j) : JoinsOn c Inv' i j :=
  fun r r' hr hr' x y y' hx => h r r' hr hr' x y y' (hI x hx)

/-- Rule i's row: (i, i), then (i, j) for each candidate j after i whose keys are compatible. -/
def detPairs (ix : DetIndex) (n i : Nat) : List (Nat × Nat) :=
  (i, i) :: match ix.keys[i]? with
    | some ks => ((ix.cands n i ks).filter fun j => decide (i < j) && match ix.keys[j]? with
        | some ks' => compat ks ks'
        | none => true).map (i, ·)
    | none => []

/-- The indices of determinism for n rules: the rows 0, …, n - 1. -/
def detIdx (ix : DetIndex) (n : Nat) : List (Nat × Nat) := Kind.rows (detPairs ix n) 0 n

/-- Two different rules, of one priority or not, step alike where both apply: different
priorities, apart in one order or the other, or alike with a match that fixes the right-hand side. -/
def pairCond (c : Semantics) (T : Tables) (r r' : Rule) : Bool :=
  r.prio != r'.prio || apart c T r r' || apart c T r' r || ((sameRule r r' || sameRule r' r) && uniqOK c r)

/-- **Determinism's decider**: at (i, i), rule i's match fixes its right-hand side; at (i, j) with
i ≠ j, `pairCond`. -/
def detCond (c : Semantics) (T : Tables) (p : Nat × Nat) : Bool :=
  match c.rules[p.1]?, c.rules[p.2]? with
  | some r, some r' => if p.1 == p.2 then uniqOK c r else pairCond c T r r'
  | _, _ => true

theorem diag_mem_detIdx {ix : DetIndex} {n i : Nat} (hi : i < n) : (i, i) ∈ detIdx ix n :=
  List.mem_flatMap.mpr ⟨i, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, List.mem_cons_self ..⟩

/-- Two rules i < j that both apply at x: (i, j) is an index. -/
theorem mem_detIdx (hmc : MatchCtx c) {ix : DetIndex} (hidx : idxOK c (tables c) ix = true)
    {x : GroundTerm} {i j : Nat} (hij : i < j) (hj : j < c.rules.length)
    (hai : Applies c (c.rules[i]'(Nat.lt_trans hij hj)) x) (haj : Applies c c.rules[j] x) :
    (i, j) ∈ detIdx ix c.rules.length := by
  have hi : i < c.rules.length := Nat.lt_trans hij hj
  obtain ⟨ks, ks', hks, hks', hmem, hc⟩ := cand_of_applies hmc hidx hi hj hai haj
  refine List.mem_flatMap.mpr ⟨i, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, ?_⟩
  unfold detPairs
  rw [hks]
  refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨hmem, ?_⟩, rfl⟩)
  simp [hij, hks', hc]

/-- **The glue**: the obligations at every index give determinism where `Inv` holds. -/
theorem joins_glue (hmc : MatchCtx c) {T : Tables} (hT : T = tables c) {ix : DetIndex}
    (hidx : idxOK c T ix = true) {Inv : Config c → Prop}
    (h : ∀ p ∈ detIdx ix c.rules.length, JoinsOn c Inv p.1 p.2) :
    ∀ x y y' : Config c, Inv x → Step c x y → Step c x y' → y = y' := by
  subst hT
  intro x y y' hx hs hs'
  obtain ⟨r, hr, hb⟩ := stepBy_of_step hs
  obtain ⟨r', hr', hb'⟩ := stepBy_of_step hs'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact h (i, j) (mem_detIdx hmc hidx hij hj hb.applies hb'.applies) _ _
      (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) x y y' hx hb hb'
  · exact h (i, i) (diag_mem_detIdx hi) _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hi)
      x y y' hx hb hb'
  · exact (h (j, i) (mem_detIdx hmc hidx hij hi hb'.applies hb.applies) _ _
      (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hi) x y' y hx hb' hb).symm

/-- **The determinism kind**: indexed by the pairs of rules of `detIdx` (the diagonal included), the
obligation at a pair that its two rules' steps from a configuration where `Inv` holds join, the goal
determinism where `Inv` holds. -/
@[reducible] def kind (c : Semantics) (T : Tables) (ix : DetIndex) (Inv : Config c → Prop)
    (hmr : c.matchReady = true) (hT : T = tables c) (hidx : idxOK c T ix = true) : Kind where
  Idx := Nat × Nat
  idxs := detIdx ix c.rules.length
  Ob p := JoinsOn c Inv p.1 p.2
  Goal := ∀ x y y' : Config c, Inv x → Step c x y → Step c x y' → y = y'
  glue := joins_glue (matchCtx_of hmr) hT hidx

/-- A predicate has at most one truth value where a term has at most one result. -/
theorem holds_det (hd : ∀ (σ : Subst) (t : Term) (r r' : Option GroundTerm), EvalTerm c σ t r → EvalTerm c σ t r' → r = r')
    {n : Nat} {σ : Subst} {p : Cond} {b b' : Bool} (h : Holds c n σ p b) (h' : Holds c n σ p b') : b = b' := by
  induction p generalizing n σ b b' with
  | top => cases h; cases h'; rfl
  | bot => cases h; cases h'; rfl
  | not p ih => cases h with | not h => cases h' with | not g => rw [ih h g]
  | and p q ih1 ih2 => cases h with | and h1 h2 => cases h' with | and g1 g2 => rw [ih1 h1 g1, ih2 h2 g2]
  | or p q ih1 ih2 => cases h with | or h1 h2 => cases h' with | or g1 g2 => rw [ih1 h1 g1, ih2 h2 g2]
  | implies p q ih1 ih2 =>
    cases h with | implies h1 h2 => cases h' with | implies g1 g2 => rw [ih1 h1 g1, ih2 h2 g2]
  | ceil s t => cases h with | ceil he => cases h' with | ceil ge => rw [hd _ _ _ _ he ge]
  | equals s t u =>
    cases h with | equals he1 he2 => cases h' with | equals g1 g2 => rw [hd _ _ _ _ he1 g1, hd _ _ _ _ he2 g2]
  | mem s t u =>
    cases h with | mem he1 he2 => cases h' with | mem g1 g2 => rw [hd _ _ _ _ he1 g1, hd _ _ _ _ he2 g2]
  | exMatch ys s pt t body ih =>
    cases h with
    | exNone he =>
      cases h' with
      | exNone _ => rfl
      | exSome g' ge _ _ => cases hd _ _ _ _ he ge
    | exSome g he hb hr =>
      cases h' with
      | exNone ge => cases hd _ _ _ _ he ge
      | exSome g' ge hb' hr' =>
        cases hd _ _ _ _ he ge
        have hg : ∀ σ', Extends c _ _ _ σ' → PatVal c σ' _ _ → g σ' = g' σ' :=
          fun σ' hx hp => ih (hb σ' hx hp) (hb' σ' hx hp)
        apply Bool.eq_iff_iff.mpr
        rw [hr, hr']
        constructor
        · rintro ⟨σ', hx, hp, hgt⟩; exact ⟨σ', hx, hp, by rw [← hg σ' hx hp]; exact hgt⟩
        · rintro ⟨σ', hx, hp, hgt⟩; exact ⟨σ', hx, hp, by rw [hg σ' hx hp]; exact hgt⟩
  | ex s body ih =>
    cases h with
    | ex g hb hr =>
      cases h' with
      | ex g' hb' hr' =>
        have hg : ∀ σ', Extends c _ _ _ σ' → g σ' = g' σ' := fun σ' hx => ih (hb σ' hx) (hb' σ' hx)
        apply Bool.eq_iff_iff.mpr
        rw [hr, hr']
        constructor
        · rintro ⟨σ', hx, hgt⟩; exact ⟨σ', hx, by rw [← hg σ' hx]; exact hgt⟩
        · rintro ⟨σ', hx, hgt⟩; exact ⟨σ', hx, by rw [hg σ' hx]; exact hgt⟩
  | all s body ih =>
    cases h with
    | all g hb hr =>
      cases h' with
      | all g' hb' hr' =>
        have hg : ∀ σ', Extends c _ _ _ σ' → g σ' = g' σ' := fun σ' hx => ih (hb σ' hx) (hb' σ' hx)
        apply Bool.eq_iff_iff.mpr
        rw [hr, hr']
        constructor
        · intro ha σ' hx; rw [← hg σ' hx]; exact ha σ' hx
        · intro ha σ' hx; rw [hg σ' hx]; exact ha σ' hx

/-- A rule that applies at x under τ, its premise predicate holding there, is not blocked at x. -/
theorem not_notApplies (hmi : CoherentAll c) {r : Rule} {x : GroundTerm} {τ : Subst}
    (hτ : c.WellSorted r.vars τ) (hm : PatVal c τ r.lhs x)
    (hq : ∀ t, r.req = some t → EvalTerm c τ t (some (bool true)))
    (hpre : Holds c r.vars.length τ r.pre true) (hna : NotApplies c r x) : False := by
  cases hna _ (hτ.at _) hm with
  | intro ht he hv => exact hv (evalTerm_det hmi he (hq _ ht))
  | pre h => exact absurd (holds_det (fun _ _ _ _ a b => evalTerm_det hmi a b) hpre h) (by decide)

/-- Two rules with one left-hand side, one right-hand side and the same variables, the first's match
fixing its right-hand side (`uniqOK`), rewrite x to one value. -/
theorem eval_eq_of_uniq (hok : c.ok = true) (hmc : MatchCtx c) (hmi : CoherentAll c)
    {r r₁ : Rule} (hr : r ∈ c.rules) (hu : uniqOK c r = true) (hv : r.vars = r₁.vars)
    (hl : r.lhs = r₁.lhs) (hrh : r.rhs = r₁.rhs) {x : GroundTerm} {τ τ' : Subst} {z z' : GroundTerm}
    (hτ : c.WellSorted r.vars τ) (hm : PatVal c τ r.lhs x) (he : EvalTerm c τ r.rhs (some z))
    (hτ' : c.WellSorted r₁.vars τ') (hm' : PatVal c τ' r₁.lhs x) (he' : EvalTerm c τ' r₁.rhs (some z')) :
    z = z' := by
  rw [← hv] at hτ'
  rw [← hl] at hm'
  rw [← hrh] at he'
  unfold uniqOK at hu
  split at hu
  · rename_i D hD
    obtain ⟨hlt, -, -, -, -⟩ := ruleOK_of hok hr
    have hag := uniq_sound hmc hτ hτ' _ hD hm hm' (sortOfTerm_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) _ _ hlt) (fun _ h => by cases h)
    have he₂ := Exec.EvalTerm.congr he fun k hk => hag k (by
      simp only [List.all_eq_true, List.contains_iff_mem] at hu; exact hu k hk)
    exact Option.some.inj (evalTerm_det hmi he₂ he')
  · cases hu

/-- **The decider is sound**: where `detCond` holds at a pair, its two rules' steps join. -/
theorem detCond_sound (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hmo : CoherentAll c) {T : Tables} (hT : T = tables c) {Inv : Config c → Prop} (p : Nat × Nat)
    (h : detCond c T p = true) : JoinsOn c Inv p.1 p.2 := by
  subst hT
  have hmc := matchCtx_of hmr
  have hmi := hmo
  intro r r' hr hr' x y y' _ hb hb'
  have hmem := List.mem_of_getElem? hr
  have hmem' := List.mem_of_getElem? hr'
  obtain ⟨σ, hσ, hm, hq, hpr, he, -, -, hp⟩ := hb
  obtain ⟨σ', hσ', hm', hq', hpr', he', -, -, hp'⟩ := hb'
  unfold detCond at h
  rw [hr, hr'] at h
  simp only at h
  split at h
  · rename_i hij
    rw [beq_iff_eq.mp hij, hr'] at hr
    cases Option.some.inj hr
    exact Subtype.ext (eval_eq_of_uniq hok hmc hmi hmem h rfl rfl rfl hσ hm he hσ' hm' he')
  · simp only [pairCond, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with (((hne | hap) | hap) | ⟨hsame, hu⟩)
    · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact (not_notApplies hmi hσ hm hq hpr (hp' _ hmem hlt)).elim
      · exact (not_notApplies hmi hσ' hm' hq' hpr' (hp _ hmem' hlt)).elim
    · exact (apart_sound hok hsr hmr hmo hmem hmem' hap hσ hm hq hσ' hm' hq').elim
    · exact (apart_sound hok hsr hmr hmo hmem' hmem hap hσ' hm' hq' hσ hm hq).elim
    · simp only [sameRule, Bool.and_eq_true, beq_iff_eq] at hsame
      rcases hsame with ⟨⟨hv, hl⟩, hrh⟩ | ⟨⟨hv, hl⟩, hrh⟩
      · exact Subtype.ext (eval_eq_of_uniq hok hmc hmi hmem hu hv (Term.beq_sound hl) (Term.beq_sound hrh)
          hσ hm he hσ' hm' he')
      · exact Subtype.ext (eval_eq_of_uniq hok hmc hmi hmem hu hv.symm (Term.beq_sound hl).symm
          (Term.beq_sound hrh).symm hσ hm he hσ' hm' he')

/-- **Determinism's decider** for `kind`. -/
def decider (hok : c.ok = true) (hsr : c.srReady = true) (hmo : CoherentAll c) {T : Tables}
    {ix : DetIndex} {Inv : Config c → Prop} {hmr : c.matchReady = true} {hT : T = tables c}
    {hidx : idxOK c T ix = true} : (kind c T ix Inv hmr hT hidx).Decider where
  cond := detCond c T
  sound p h := detCond_sound hok hsr hmr hmo hT p h

/-- `detOKExcept` is the kind's decision with the listed overlaps, in either order, as the
obligations: a row's uniqueness confirms its diagonal, and its candidates' `pairOK` confirms each of
its pairs or lists it. -/
theorem decides_of_detOKExcept {ix : DetIndex} {ovl : List (Nat × Nat)}
    (hd : detOKExcept c (tables c) ix ovl = true) :
    Kind.decides (detCond c (tables c)) (ovl ++ ovl.map Prod.swap) (detIdx ix c.rules.length) = true := by
  have hidx : idxOK c (tables c) ix = true := by simp only [detOKExcept, Bool.and_eq_true] at hd; exact hd.1
  refine List.all_eq_true.mpr fun p hp => ?_
  simp only [Bool.or_eq_true, List.contains_iff_mem]
  obtain ⟨i, hi, hp⟩ := List.mem_flatMap.mp hp
  have hi : i < c.rules.length := by have := List.mem_range'_1.mp hi; omega
  have hrow := row_of hd hi
  obtain ⟨ks, hks, -⟩ := idxOK_spec hidx hi
  unfold detRow at hrow
  rw [List.getElem?_eq_getElem hi, hks] at hrow
  simp only [Bool.and_eq_true, List.all_eq_true] at hrow
  obtain ⟨hu, hrow⟩ := hrow
  unfold detPairs at hp
  rw [hks] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · left
    simp [detCond, List.getElem?_eq_getElem hi, hu]
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hjc, hf⟩ := List.mem_filter.mp hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hij, hcomp⟩ := hf
    have := hrow j hjc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with hle | h
    · omega
    · split at h
      · rename_i r' ks' hrj hkj
        rw [hkj] at hcomp
        simp only at hcomp
        rw [hcomp] at h
        simp only [Bool.not_true, Bool.false_or] at h
        have hne : (i == j) = false := by simp; omega
        simp only [pairOK, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
        rcases h with ((((((hne' | hap) | hap) | hs) | hs) | ho) | ho)
        · left; simp [detCond, List.getElem?_eq_getElem hi, hrj, hne, pairCond, hne']
        · left; simp [detCond, List.getElem?_eq_getElem hi, hrj, hne, pairCond, hap]
        · left; simp [detCond, List.getElem?_eq_getElem hi, hrj, hne, pairCond, hap]
        · left; simp [detCond, List.getElem?_eq_getElem hi, hrj, hne, pairCond, hs, hu]
        · left; simp [detCond, List.getElem?_eq_getElem hi, hrj, hne, pairCond, hs, hu]
        · right; exact List.mem_append_left _ (List.contains_iff_mem.mp ho)
        · right; exact List.mem_append_right _ (List.mem_map.mpr ⟨(j, i), List.contains_iff_mem.mp ho, rfl⟩)
      · cases h

/-- **Determinism up to listed overlaps from the kind**: where the obligations at the pairs `ovl`
give determinism relative to every `Inv`, two steps from one configuration reach one
configuration, or the two rules of a listed pair both apply there (`Inv`: no listed pair's rules
both apply, under which every listed obligation holds). -/
theorem deterministic_except_of_on {ovl : List (Nat × Nat)}
    (hon : ∀ Inv : Config c → Prop, (∀ p ∈ ovl, JoinsOn c Inv p.1 p.2) →
      ∀ x y y' : Config c, Inv x → Step c x y → Step c x y' → y = y')
    {x y y' : Config c} (h : Step c x y) (h' : Step c x y') :
    y = y' ∨ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧ ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Applies c c.rules[i] x.val ∧ Applies c c.rules[j] x.val := by
  by_cases hx : ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧ ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Applies c c.rules[i] x.val ∧ Applies c c.rules[j] x.val
  · exact .inr hx
  · refine .inl (hon (fun z => ¬ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧
      ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
        Applies c c.rules[i] z.val ∧ Applies c c.rules[j] z.val) (fun p hp r r' hr hr' z _ _ hz hb hb' => ?_)
      x y y' hx h h')
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hr
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hr'
    exact (hz ⟨p.1, p.2, .inl hp, hi, hj, hb.applies, hb'.applies⟩).elim

/-- **Where `detOKExcept c (tables c) ix ovl` holds, `Step` is deterministic up to the listed overlaps**: two
steps from one configuration reach one configuration, or the two rules of a listed pair both apply
there. By the determinism kind, with the listed pairs as its obligations. -/
theorem deterministic_except (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hmo : CoherentAll c) {T : Tables} (hT : T = tables c)
    {ix : DetIndex} {ovl : List (Nat × Nat)} (hd : detOKExcept c T ix ovl = true) {x y y' : Config c}
    (h : Step c x y) (h' : Step c x y') :
    y = y' ∨ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧ ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Applies c c.rules[i] x.val ∧ Applies c c.rules[j] x.val := by
  subst hT
  have hidx : idxOK c (tables c) ix = true := by simp only [detOKExcept, Bool.and_eq_true] at hd; exact hd.1
  refine deterministic_except_of_on (fun Inv ho => ?_) h h'
  refine Kind.of_decided (kind c (tables c) ix Inv hmr rfl hidx) (decider hok hsr hmo) (ovl ++ ovl.map Prod.swap)
    (decides_of_detOKExcept hd) fun p hp => ?_
  rcases List.mem_append.mp hp with hp | hp
  · exact ho p hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (ho q hq).swap

/-- **`Step` is deterministic where `detOK` holds** (with the core's `ok`, `srReady` and
`matchReady`, and the named match obligations): two steps from one configuration reach one
configuration. -/
theorem deterministic_of (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hmo : CoherentAll c) {T : Tables} (hT : T = tables c)
    {ix : DetIndex} (hd : detOK c T ix = true) {x y y' : Config c} (h : Step c x y) (h' : Step c x y') : y = y' :=
  (deterministic_except hok hsr hmr hmo hT hd h h').resolve_right fun ⟨_, _, hm, _⟩ => by rcases hm with hm | hm <;> cases hm

/-! ## Blocks: the condition split over rows, for one kernel decision per block -/

/-- Two adjacent blocks of rows make one. -/
theorem detRows_add {T : Tables} {ix : DetIndex} {ovl : List (Nat × Nat)} {lo a b : Nat}
    (h1 : detRows c T ix ovl lo a = true) (h2 : detRows c T ix ovl (lo + a) b = true) :
    detRows c T ix ovl lo (a + b) = true := by
  simp only [detRows, List.all_eq_true, List.mem_range'_1] at *
  intro m hm
  by_cases hma : m < lo + a
  · exact h1 m ⟨hm.1, hma⟩
  · exact h2 m ⟨by omega, by omega⟩

/-- `detRows_add` with the boundaries as equations (closed by `rfl` on numerals), so that elaborating
a join never unfolds the decision. -/
theorem detRows_join {T : Tables} {ix : DetIndex} {ovl : List (Nat × Nat)} {a m b n : Nat}
    (h1 : detRows c T ix ovl 0 a = true) (h2 : detRows c T ix ovl m b = true) (hm : a = m)
    (hn : a + b = n) : detRows c T ix ovl 0 n = true := by
  subst hm hn; exact detRows_add (by simpa using h1) (by simpa using h2)

theorem detRows_all {T : Tables} {ix : DetIndex} {ovl : List (Nat × Nat)} {n : Nat}
    (hn : c.rules.length = n) (h : detRows c T ix ovl 0 n = true) :
    detRows c T ix ovl 0 c.rules.length = true := hn ▸ h

theorem detOKExcept_of {T : Tables} {ix : DetIndex} {ovl : List (Nat × Nat)} (hidx : idxOK c T ix = true)
    (hrows : detRows c T ix ovl 0 c.rules.length = true) : detOKExcept c T ix ovl = true := by
  simp [detOKExcept, hidx, hrows]

/-! ## Witnesses -/

section
variable (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)

include hok hsr hmr in
theorem applies_of {r : Rule} (hr : r ∈ c.rules) {x : Config c} {n : Nat}
    (h : appliesN c n r x.val = true) : Applies c r x.val := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  obtain ⟨⟨σ, b⟩, hσm, hb⟩ := List.any_eq_true.mp h
  simp only [beq_iff_eq] at hb
  subst hb
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσm
  obtain ⟨hm, hws⟩ := List.mem_filter.mp hσm
  have hσ := wellSorted_iff.mp hws
  obtain ⟨_, hpv⟩ := matchP_sound _ (canonV_of_sortOf x.property) hm
  obtain ⟨_, _, _, hreq, _⟩ := ruleOK_of hok hr
  refine ⟨σ, hσ, hpv, fun t ht => ?_⟩
  rw [ht] at hreq
  unfold reqVal at hb
  rw [ht] at hb
  cases he' : evalT c n σ t with
  | none => simp [he'] at hb
  | some v =>
    simp only [he', Option.map_some, Option.some.injEq] at hb
    rw [isTrue_iff.mp hb.symm] at he'
    exact evalT_sound hsc hcc hmc n he' headsOK_fns hσ (reqOK_some hreq)

include hok hsr hmr in
/-- A successor the executable step lists is a step. -/
theorem step_of_mem {x : Config c} {n : Nat} {y : GroundTerm} (hy : y ∈ successorsN c n x.val) :
    ∃ hs : c.sortOf y = some topCellSort, Step c x ⟨y, hs⟩ := by
  obtain ⟨r, hr, σ, hσ, hpv, hreq, heval, hens, hs, hprio⟩ := successorsN_sound hok hsr hmr hy
  exact ⟨hs, Step.rule_top (y := ⟨y, hs⟩) r hr σ (Semantics.ok_rule hok hr).2.1 (Semantics.ok_rule hok hr).2.2.1
    hσ hpv hreq heval hens hprio⟩

include hok hsr hmr in
/-- A listed overlap witnessed at x (`witnessOK`): both rules apply at x, and x steps to two
different configurations. -/
theorem witnessed_of {n i j : Nat} {x : Config c} (h : witnessOK c n i j x.val = true) :
    ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Applies c c.rules[i] x.val ∧ Applies c c.rules[j] x.val ∧
      ∃ y y' : Config c, Step c x y ∧ Step c x y' ∧ y ≠ y' := by
  unfold witnessOK at h
  split at h
  · rename_i r r' hri hrj
    obtain ⟨hi, hri'⟩ := List.getElem?_eq_some_iff.mp hri
    obtain ⟨hj, hrj'⟩ := List.getElem?_eq_some_iff.mp hrj
    simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨ha, ha'⟩, y, hy, y', hy', hne⟩ := h
    obtain ⟨hs, hst⟩ := step_of_mem hok hsr hmr hy
    obtain ⟨hs', hst'⟩ := step_of_mem hok hsr hmr hy'
    refine ⟨hi, hj, ?_, ?_, ⟨y, hs⟩, ⟨y', hs'⟩, hst, hst', fun he => ?_⟩
    · rw [hri']; exact applies_of hok hsr hmr (hri' ▸ List.getElem_mem hi) ha
    · rw [hrj']; exact applies_of hok hsr hmr (hrj' ▸ List.getElem_mem hj) ha'
    · have := congrArg Subtype.val he
      simp only at this
      subst this
      rw [same_iff.mpr rfl] at hne
      cases hne
  · cases h

end

end KCore.Det
