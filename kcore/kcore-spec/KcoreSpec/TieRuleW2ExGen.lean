/-
  KCore, outside the cone: W2 for a rule whose right side is under one binder,
  `\exists{C}(Z:zs, \and{C}(r, \top{C}()))`, with `r` built of the rule's variables, the binder and
  generators (`TieRuleCutG.builtGB`).

  Γ's axiom of such a rule adds the one conjunct `⌈∃Z. (r ∧ ⊤)⌉` to the text's left side. Where the
  binder's sort has an element w, `r` read with Z at w denotes one element of the rule's sort (each
  generator's Cons-Fun item gives one element from elements of its argument sorts), so the conjunct
  holds of every element of `\top{C}()` and the text's sentence holds where Γ's axiom does.

  - `rightExBuiltGB gs fT s zs g`: the shape, decided on the axiom `g`.
  - `ruleGuard_of_exBuiltG`: the conjunct holds, in a model of Γ where the binder's sort has an
    element and the guards of `g`'s free variables hold.
  - `rule_w2_exBuiltG`: W2 at a valuation. `rule_w2_exBuiltG_Γ`: Γ entails the text's sentence of
    a rule of Γ, where every model of Γ has an element of the binder's sort.
  - Not covered: more binders than one, an `ensures`, a `requires`, a `pre`, a rule of a smaller
    priority, and a right side `builtGB` does not read.
-/
import KcoreSpec.TieRuleW2GuardedGen

set_option autoImplicit false

namespace KCore

namespace TieRuleW2G

open ML Faithful KoreAML
open TieRulePair (kAx leftOf extraOf ruleTextB RuleGuard rulesTieB)

/-- The key of an element variable of a sort without arguments. -/
def exKeyConstB : VarKey → Bool
  | .evar _ (.ctor _ []) => true
  | _ => false

/-- The one conjunct `g` adds is `⌈∃Z. (r ∧ ⊤)⌉` in the sort named `s`, the binder Z of the sort
named `zs`; `\top` of the sort named `s` is one of the first two conjuncts; each key of `fT` is
free in `g`, an element variable of a sort without arguments, and not the binder's variable in
`g`'s table; `r` is built of the binder, the variables of `fT` and the generators of `gs`. -/
def rightExBuiltGB (gs : List (String × KoreAML.Gen)) (fT : List VarKey) (s zs : String)
    (g : Kore.Pattern) : Bool :=
  match extraOf g with
  | [.ceil S S' (.exist S'' z (.and S3 [r, tp]))] =>
    decide (S = srt s ∧ S' = srt s ∧ S'' = srt s ∧ S3 = srt s ∧ tp = .top (srt s) ∧ z.sort = srt zs) &&
      (leftOf g).any (fun p => decide (p = .top (srt s))) &&
      fT.all (fun k => (freeOf [] g).eraseDups.contains k && exKeyConstB k &&
        decide ((tableOf [] g).ev k ≠ (tableOf [] g).ev (evarKey z))) &&
      TieRuleCutG.builtGB gs (evarKey z :: fT) r s
  | _ => false

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **The guard of a rule with a binder.** In a model of Γ that has the Cons-Fun items of `gs`,
for `g` with `rightExBuiltGB`, where the binder's sort has an element and the guards of `g`'s free
variables hold: the conjunct `g` adds holds of every element its first two hold. -/
theorem ruleGuard_of_exBuiltG [Inhabited M] {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s zs : String}
    {g : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCutG.funsInGB c gs = true)
    (hb : rightExBuiltGB gs fT s zs g = true) (hw : ∃ w, InS I zs w)
    (e : Valuation M) (m : M) (hgd : GuardsAt g I e m) : RuleGuard g I e := by
  unfold rightExBuiltGB at hb
  split at hb
  next S S' S'' z S3 r tp hex =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hb
    obtain ⟨⟨⟨⟨hS, hS', hS'', hS3, htp, hz⟩, p0, hp0, hp0e⟩, hsub⟩, hbuilt⟩ := hb
    subst hS hS' hS'' hS3 htp hs
    have htopmem : Kore.Pattern.top (srt (c.sortName N)) ∈ leftOf g := hp0e ▸ hp0
    intro x hx a hl
    rw [hex] at hx
    rw [List.mem_singleton.mp hx]
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI hN
    have hS : ∀ (e' : Valuation M) b,
        (trSort (tableOf [] g) (srt (c.sortName N))).interpret I e' b ↔ b = σ := fun e' b => by
      rw [trSort_srt, interp_sym]; exact hσ1 b
    have htop : ∀ (e' : Valuation M) b,
        (tr ⟨tableOf [] g, []⟩ (.top (srt (c.sortName N)))).interpret I e' b ↔ Inh I σ b := fun e' b => by
      have h1 : tr ⟨tableOf [] g, []⟩ (.top (srt (c.sortName N))) =
          sTop (trSort (tableOf [] g) (srt (c.sortName N))) := by rw [tr]
      rw [h1, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of (hS e')]
    have hT : ∀ φ, tr ⟨tableOf [] g, []⟩ (.ceil (srt (c.sortName N)) (srt (c.sortName N)) φ) =
        sCeil (trSort (tableOf [] g) (srt (c.sortName N))) (trSort (tableOf [] g) (srt (c.sortName N)))
          (tr ⟨tableOf [] g, []⟩ φ) := fun φ => by rw [tr]
    have hE : ∀ φ, tr ⟨tableOf [] g, []⟩ (.exist (srt (c.sortName N)) z φ) =
        sExists ((tableOf [] g).ev (evarKey z)) (trSort (tableOf [] g) z.sort)
          (tr ⟨tableOf [] g, []⟩ φ) := fun φ => by rw [tr]
    have hin' : ∀ b, (sExists ((tableOf [] g).ev (evarKey z)) (trSort (tableOf [] g) z.sort)
        (tr ⟨tableOf [] g, []⟩ (.and (srt (c.sortName N)) [r, .top (srt (c.sortName N))]))).interpret I e b →
        Inh I σ b := fun b hb' => by
      obtain ⟨w, -, hbody⟩ := (interp_sExists_elem hD).mp hb'
      exact (htop _ b).mp ((interp_and (List.cons_ne_nil _ _)).mp hbody _
        (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hT, hE, interp_sCeil hD hc (hS e) (hS e) hσ2 hσ2 hin' a]
    refine ⟨?_, (htop e a).mp (hl _ htopmem)⟩
    obtain ⟨w, hw⟩ := hw
    have hgs : ∀ g' ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g'.1 g'.2).pat := fun g' hg' => by
      obtain ⟨it, hit, hpat⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin g' hg')
      rw [← of_decide_eq_true hpat]
      exact sat_cons hI (Or.inl ⟨it, hit, rfl⟩)
    have hzg : (inhOf (trSort (tableOf [] g) z.sort)).interpret I
        (updE e ((tableOf [] g).ev (evarKey z)) w) w := by
      rw [hz, trSort_srt]; exact (inS_iff _).mpr hw
    have hg' : ∀ k ∈ evarKey z :: fT,
        (guardOf (tableOf [] g) k).interpret I (updE e ((tableOf [] g).ev (evarKey z)) w) m := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [TieRuleLhs.guard_evarKey hD]
        have h1 : (updE e ((tableOf [] g).ev (evarKey z)) w).evalEvar ((tableOf [] g).ev (evarKey z)) = w := by
          simp
        rw [h1]; exact hzg
      · have hk' := hsub k hk
        obtain ⟨⟨hfree, hconst⟩, hne⟩ := hk'
        have h0 := hgd k (List.contains_iff_mem.mp hfree)
        match k, hconst, hne, h0 with
        | .evar n (.ctor C []), _, hne, h0 =>
          rw [interp_guard_evar hD, trSort_const] at h0 ⊢
          have h1 : (updE e ((tableOf [] g).ev (evarKey z)) w).evalEvar
              ((tableOf [] g).ev (.evar n (.ctor C []))) = e.evalEvar ((tableOf [] g).ev (.evar n (.ctor C []))) :=
            Function.update_noteq hne _ _
          rw [h1]
          exact (((Closed.sym _).app (Closed.sym _)).interp _ _ _).mp h0
    obtain ⟨y, hy, hyu⟩ := TieRuleCutG.builtGB_one hD hgs hg' r _ hbuilt
    refine ⟨y, (interp_sExists_elem hD).mpr ⟨w, hzg, (interp_and (List.cons_ne_nil _ _)).mpr fun p hp => ?_⟩⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (hyu y).mpr rfl
    · rw [List.mem_singleton.mp hp]
      exact (htop _ y).mpr ((interp_inhOf_of (hS e)).mp (by rw [trSort_srt]; exact (inS_iff e).mpr hy))
  next => exact absurd hb (by simp)

/-- **W2 for a rule whose right side is under a binder and built of generators**: in a model of Γ
where the binder's sort has an element, the text's sentence `t` of Γ's axiom `g` holds. -/
theorem rule_w2_exBuiltG [Inhabited M] {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s zs : String}
    {g : Kore.Pattern} {t : P} (h : ruleTextB t g = true)
    (hg : I ⊧ᴵ (trAxiom [] [] (kAx g)).pat) (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCutG.funsInGB c gs = true)
    (hb : rightExBuiltGB gs fT s zs g = true) (hw : ∃ w, InS I zs w) : I ⊧ᴵ t :=
  fun e m => rule_w2_guarded (defOK hI) h hg e m fun hgd => ruleGuard_of_exBuiltG hI hN hs hin hb hw e m hgd
end

/-- **Γ entails the text's sentence of a rule under a binder**: for a rule `r` of `c` whose axiom
is the pattern `t` with the conjunct `⌈∃Z. (r ∧ ⊤)⌉` more on the left side (`ruleTextB`,
`rightExBuiltGB`), where every model of Γ has an element of the binder's sort. -/
theorem rule_w2_exBuiltG_Γ {c : Semantics} [OvlOK c] {r : Rule} (hr : r ∈ c.rules) {t : P}
    (h : ruleTextB t (prioRuleK c r) = true)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s zs : String}
    (hN : N < nRegSorts + c.sortNames.length) (hs : c.sortName N = s)
    (hin : TieRuleCutG.funsInGB c gs = true) (hb : rightExBuiltGB gs fT s zs (prioRuleK c r) = true)
    (hw : ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c → ∃ w, InS I zs w) :
    Γ c ⊧ t :=
  fun {_} _ {_} hI => rule_w2_exBuiltG hI h
    (hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map_of_mem hr, rfl⟩)))) hN hs hin hb (hw _ _ hI)

end TieRuleW2G

end KCore
