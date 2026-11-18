/-
  KCore, outside the cone: the tie of a text's rewrite rules, and the successors of a configuration
  listed by a decision, for any semantics. A tie file of one text instantiates these with kernel
  decisions on the literal definition; nothing here reads `Parse.parse` or `Definition.emit`.

  - `ruleTextB t g`: `g` (Γ's axiom of a rule, `prioRuleK`) is a rewrite whose left side is a
    conjunction of at least two patterns, `t` is the translation of `g` with its left side cut to
    the first two (`textOf g`: the left side and the `requires`, the form of a kompiled rule), and
    the two have one variable table and one list of free variables. Then `t` gives `g`
    (`rule_weaker`, W1: Γ's item is a consequence of the sentence), and `g` gives `t` at a
    valuation where each conjunct `g` adds holds of every element the first two hold (`rule_w2`,
    `RuleGuard`: for `prioRuleK` the negation of the rules of a smaller priority and the
    definedness of the right side with its `ensures`).
  - `listedCheck c n x ys`: each rule either is blocked at `x` by a rule of a smaller priority
    whose `requires` is `true` at a match, or gives at each of its matches, within fuel n, no
    successor or one of `ys`. Then every `Step` successor of `x` is one of `ys`, for every
    interpretation of the parameters (`listed_sound`); with `ys = []`, `x` has none.
  - `step_withHooks`: a step a rule's check accepts on the data is a step for every interpretation.
-/
import KcoreSpec.TiePairs
import KcoreSpec.TieRule

set_option autoImplicit false

namespace KCore

namespace TieRulePair

open ML Faithful KoreAML

/-! ## Γ's axiom of a rule and the text's sentence -/

/-- The axiom of a pattern, without sort variables or attributes. -/
def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- A rewrite whose left side is a conjunction, with the conjunction cut to its first two
conjuncts. -/
def textOf : Kore.Pattern → Kore.Pattern
  | .rewrites C (.and C1 L) r => .rewrites C (.and C1 (L.take 2)) r
  | p => p

/-- The first two conjuncts of a rewrite's left side. -/
def leftOf : Kore.Pattern → List Kore.Pattern
  | .rewrites _ (.and _ L) _ => L.take 2
  | _ => []

/-- The conjuncts of a rewrite's left side after the first two. -/
def extraOf : Kore.Pattern → List Kore.Pattern
  | .rewrites _ (.and _ L) _ => L.drop 2
  | _ => []

/-- `t` is the translation of `g`'s text form `textOf g`, the two have one list of free variables,
and the guards of the free variables, the sorts, the first two conjuncts of the left side and the
right side translate alike under the two variable tables (the table of `g` may hold more keys: the
binders of the conjuncts `g` adds). -/
def ruleTextB (t : P) : Kore.Pattern → Bool
  | .rewrites C (.and C1 L) r =>
    let g : Kore.Pattern := .rewrites C (.and C1 L) r
    let x : Kore.Pattern := .rewrites C (.and C1 (L.take 2)) r
    let Tg := tableOf [] g
    let Tt := tableOf [] x
    let F := (freeOf [] g).eraseDups
    decide (2 ≤ L.length) &&
    decide (F = (freeOf [] x).eraseDups) &&
    decide (F.map (guardOf Tg) = F.map (guardOf Tt)) &&
    decide (trSort Tg C = trSort Tt C) && decide (trSort Tg C1 = trSort Tt C1) &&
    decide ((L.take 2).map (KoreAML.tr ⟨Tg, []⟩) = (L.take 2).map (KoreAML.tr ⟨Tt, []⟩)) &&
    decide (KoreAML.tr ⟨Tg, []⟩ r = KoreAML.tr ⟨Tt, []⟩ r) &&
    decide (t = (trAxiom [] [] (kAx x)).pat)
  | _ => false

theorem ruleTextB_parts {t : P} {g : Kore.Pattern} (h : ruleTextB t g = true) :
    ∃ C C1 L r, g = .rewrites C (.and C1 L) r ∧ 2 ≤ L.length ∧
      (freeOf [] g).eraseDups = (freeOf [] (.rewrites C (.and C1 (L.take 2)) r)).eraseDups ∧
      (freeOf [] g).eraseDups.map (guardOf (tableOf [] g)) =
        (freeOf [] g).eraseDups.map (guardOf (tableOf [] (.rewrites C (.and C1 (L.take 2)) r))) ∧
      trSort (tableOf [] g) C = trSort (tableOf [] (.rewrites C (.and C1 (L.take 2)) r)) C ∧
      trSort (tableOf [] g) C1 = trSort (tableOf [] (.rewrites C (.and C1 (L.take 2)) r)) C1 ∧
      (L.take 2).map (KoreAML.tr ⟨tableOf [] g, []⟩) =
        (L.take 2).map (KoreAML.tr ⟨tableOf [] (.rewrites C (.and C1 (L.take 2)) r), []⟩) ∧
      KoreAML.tr ⟨tableOf [] g, []⟩ r = KoreAML.tr ⟨tableOf [] (.rewrites C (.and C1 (L.take 2)) r), []⟩ r ∧
      t = (trAxiom [] [] (kAx (.rewrites C (.and C1 (L.take 2)) r))).pat := by
  match g, h with
  | .rewrites C (.and C1 L) r, h =>
    simp only [ruleTextB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨C, C1, L, r, rfl, h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
      h.1.2, h.2⟩

theorem tr_rewrites_and {ctx : KoreAML.Ctx} {C C1 : Kore.KSort} {L : List Kore.Pattern} {r : Kore.Pattern} :
    KoreAML.tr ctx (.rewrites C (.and C1 L) r) =
      KoreAML.sRewrites (KoreAML.trSort ctx.vars C) (KoreAML.trAndList ctx (KoreAML.trSort ctx.vars C1) L)
        (KoreAML.tr ctx r) := by
  rw [KoreAML.tr, KoreAML.tr]

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The translation of a rewrite whose left side is a conjunction, read. -/
theorem interp_rewrites_and {ctx : KoreAML.Ctx} {C C1 : Kore.KSort} {L : List Kore.Pattern} {r : Kore.Pattern}
    {e : Valuation M} (hl : L ≠ []) {m : M} :
    (KoreAML.tr ctx (.rewrites C (.and C1 L) r)).interpret I e m ↔
      (inhOf (KoreAML.trSort ctx.vars C)).interpret I e m ∧
      ((∀ p ∈ L, (KoreAML.tr ctx p).interpret I e m) → (KoreAML.sNext (KoreAML.tr ctx r)).interpret I e m) := by
  rw [tr_rewrites_and]
  unfold KoreAML.sRewrites
  rw [KoreAML.interp_sImp, interp_trAndList hl]

/-- The conjuncts Γ's axiom `g` adds hold of every element its first two hold, at `e` (under `g`'s
variable table). -/
def RuleGuard (g : Kore.Pattern) (I : Interpretation KoreAML.Sym M) (e : Valuation M) : Prop :=
  ∀ x ∈ extraOf g, ∀ a,
    (∀ p ∈ leftOf g, (KoreAML.tr ⟨tableOf [] g, []⟩ p).interpret I e a) →
      (KoreAML.tr ⟨tableOf [] g, []⟩ x).interpret I e a

/-- The two translations of a rule axiom and of its text form, at one valuation: the same sort and
guards; the text's gives Γ's (W1) and, under the guard, Γ's gives the text's (W2). -/
theorem rule_parts_at {g : Kore.Pattern} {t : P} (h : ruleTextB t g = true) (e : Valuation M) :
    ∃ (W S G X : P), (trAxiom [] [] (kAx g)).pat = (W ⇒ (G ≡ S)) ∧ t = (W ⇒ (X ≡ S)) ∧
      (∀ a, G.interpret I e a → S.interpret I e a) ∧ (∀ a, X.interpret I e a → S.interpret I e a) ∧
      (∀ a, X.interpret I e a → G.interpret I e a) ∧
      (RuleGuard g I e → ∀ a, G.interpret I e a → X.interpret I e a) := by
  obtain ⟨C, C1, L, r, rfl, hlen, hfree, hguard, hC, hC1, hleft, hright, rfl⟩ := ruleTextB_parts h
  have hl : L.take 2 ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_take]; omega)
  have hL : L ≠ [] := fun h0 => by subst h0; simp at hlen
  generalize hTg : tableOf [] (.rewrites C (.and C1 L) r) = Tg at hguard hC hC1 hleft hright
  generalize hTt : tableOf [] (.rewrites C (.and C1 (L.take 2)) r) = Tt at hguard hC hC1 hleft hright
  have hleft' : ∀ p ∈ L.take 2, KoreAML.tr ⟨Tt, []⟩ p = KoreAML.tr ⟨Tg, []⟩ p := fun p hp =>
    (List.map_inj_left.mp hleft p hp).symm
  refine ⟨conjList (((freeOf [] (.rewrites C (.and C1 L) r)).eraseDups).map (guardOf Tg)),
    inhOf (trSort Tg C), KoreAML.tr ⟨Tg, []⟩ (.rewrites C (.and C1 L) r),
    KoreAML.tr ⟨Tt, []⟩ (.rewrites C (.and C1 (L.take 2)) r), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show conjList (((freeOf [] (.rewrites C (.and C1 L) r)).eraseDups).map (guardOf (tableOf [] (.rewrites C (.and C1 L) r)))) ⇒
      (KoreAML.tr ⟨tableOf [] (.rewrites C (.and C1 L) r), []⟩ (.rewrites C (.and C1 L) r) ≡
        inhOf (trSort (tableOf [] (.rewrites C (.and C1 L) r)) C)) = _
    rw [hTg]
  · show conjList (((freeOf [] (.rewrites C (.and C1 (L.take 2)) r)).eraseDups).map
        (guardOf (tableOf [] (.rewrites C (.and C1 (L.take 2)) r)))) ⇒
      (KoreAML.tr ⟨tableOf [] (.rewrites C (.and C1 (L.take 2)) r), []⟩ (.rewrites C (.and C1 (L.take 2)) r) ≡
        inhOf (trSort (tableOf [] (.rewrites C (.and C1 (L.take 2)) r)) C)) = _
    rw [hTt, ← hfree, ← hguard, ← hC]
  · intro a ha
    exact ((interp_rewrites_and hL).mp ha).1
  · intro a ha
    have := ((interp_rewrites_and hl).mp ha).1
    simpa only [← hC] using this
  · intro a ha
    obtain ⟨hs, hi⟩ := (interp_rewrites_and hl).mp ha
    refine (interp_rewrites_and hL).mpr ⟨by simpa only [hC] using hs, fun hall => ?_⟩
    have := hi fun p hp => by rw [hleft' p hp]; exact hall p (List.mem_of_mem_take hp)
    simpa only [hright, hC1] using this
  · intro hg a ha
    obtain ⟨hs, hi⟩ := (interp_rewrites_and hL).mp ha
    refine (interp_rewrites_and hl).mpr ⟨by simpa only [← hC] using hs, fun hall => ?_⟩
    have hall' : ∀ p ∈ L.take 2, (KoreAML.tr ⟨Tg, []⟩ p).interpret I e a :=
      fun p hp => by rw [← hleft' p hp]; exact hall p hp
    have := hi fun p hp => by
      rw [← List.take_append_drop 2 L] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hall' p hp
      · have := hg p (by simpa only [extraOf] using hp) a (by simpa only [leftOf, hTg] using hall')
        simpa only [hTg] using this
    simpa only [hright] using this

/-- **W1 for a rule**: the text's sentence `t` gives Γ's axiom `g`. -/
theorem rule_weaker (hD : KoreAML.DefOK I) {g : Kore.Pattern} {t : P} (h : ruleTextB t g = true)
    (ht : I ⊧ᴵ t) : I ⊧ᴵ (trAxiom [] [] (kAx g)).pat := by
  intro e m
  obtain ⟨W, S, G, X, hg, htx, hGS, hXS, hXG, -⟩ := rule_parts_at (I := I) h e
  have h1 := ht e m
  rw [htx, interpret_impl] at h1
  rw [hg, interpret_impl]
  intro hw
  have h2 := (KoreAML.interp_equal hD).mp (h1 hw)
  exact (KoreAML.interp_equal hD).mpr fun a => ⟨hGS a, fun hs => hXG a ((h2 a).mpr hs)⟩

/-- **W2 for a rule, with the guard**: in a model of Γ's axiom `g`, the text's sentence `t` holds at
each valuation at which the conjuncts `g` adds hold of every element its first two hold. -/
theorem rule_w2 (hD : KoreAML.DefOK I) {g : Kore.Pattern} {t : P} (h : ruleTextB t g = true)
    (hg : I ⊧ᴵ (trAxiom [] [] (kAx g)).pat) (e : Valuation M) (hx : RuleGuard g I e) (m : M) :
    t.interpret I e m := by
  obtain ⟨W, S, G, X, hgp, htx, hGS, hXS, -, hGX⟩ := rule_parts_at (I := I) h e
  have h1 := hg e m
  rw [hgp, interpret_impl] at h1
  rw [htx, interpret_impl]
  intro hw
  have h2 := (KoreAML.interp_equal hD).mp (h1 hw)
  exact (KoreAML.interp_equal hD).mpr fun a => ⟨hXS a, fun hs => hGX hx a ((h2 a).mpr hs)⟩
end

/-! ## Γ's rule items against the text's rule sentences, position for position -/

/-- Γ's axiom of each rule against the pattern of `R` at its position (`ruleTextB`). -/
def rulesTieB (c : Semantics) (R : List P) : Bool :=
  c.rules.length == R.length && (c.rules.zip R).all fun p => ruleTextB p.2 (prioRuleK c p.1)

kernel_rfl rulesTieB_withHooks : ∀ (c : Semantics) (H : HookParams) (R : List P),
  rulesTieB (c.withHooks H) R = rulesTieB c R

section
variable {c : Semantics} {R : List P}

theorem rulesTie_at (h : rulesTieB c R = true) {j : Nat} {r : Rule} (hr : c.rules[j]? = some r) :
    ∃ t, R[j]? = some t ∧ ruleTextB t (prioRuleK c r) = true := by
  rw [rulesTieB, Bool.and_eq_true, beq_iff_eq] at h
  have hj : j < R.length := h.1 ▸ (List.getElem?_eq_some_iff.mp hr).1
  refine ⟨R[j], List.getElem?_eq_getElem hj, ?_⟩
  have hz : (c.rules.zip R)[j]? = some (r, R[j]) :=
    List.getElem?_zip_eq_some.mpr ⟨hr, List.getElem?_eq_getElem hj⟩
  exact List.all_eq_true.mp h.2 _ (List.mem_of_getElem? hz)

/-- **W1 for every rule**: each of Γ's rule items is a consequence of the pattern of `R` at its
index. -/
theorem rules_from_text (h : rulesTieB c R = true) :
    ∀ (j : Nat) (it : Item), (ruleItems c)[j]? = some it → ∃ t, R[j]? = some t ∧ (TiePair.Texts [t] ⊧ it.pat) := by
  intro j it hj
  unfold ruleItems at hj
  rw [List.getElem?_map] at hj
  cases hr : c.rules[j]? with
  | none => rw [hr] at hj; cases hj
  | some r =>
    rw [hr] at hj; cases hj
    obtain ⟨t, ht, hb⟩ := rulesTie_at h hr
    exact ⟨t, ht, fun {M} _ {I} hI =>
      rule_weaker (TiePair.defOK_texts hI) hb (hI _ (Or.inl (List.mem_singleton_self _)))⟩

/-- **W2 for every rule, with the guard**: in a model of Γ, the pattern of `R` at a rule's index
holds at each valuation at which the conjuncts Γ's axiom of the rule adds hold where the text's
left side and `requires` hold (`RuleGuard`: the negation of the rules of a smaller priority and the
definedness of the right side with its `ensures`). -/
theorem rules_w2 (h : rulesTieB c R = true) {j : Nat} {r : Rule} {t : P} (hr : c.rules[j]? = some r)
    (ht : R[j]? = some t) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    (e : Valuation M) (hx : RuleGuard (prioRuleK c r) I e) (m : M) : t.interpret I e m := by
  obtain ⟨t', ht', hb⟩ := rulesTie_at h hr
  rw [ht] at ht'; cases ht'
  exact rule_w2 (defOK hI) hb
    (hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map_of_mem (List.mem_of_getElem? hr), rfl⟩)))) e hx m

/-- The premises of a derivation from sentences: the patterns of `T` (function sentences) and of
`R` (rule sentences) as written, and the families (the parts of Γ no sentence states). -/
def PreS (c : Semantics) (T R : List P) : Premises KoreAML.Sym := TiePair.Texts (T ++ R) ∪ TiePair.Families c

/-- Every premise of Γ is a consequence of `PreS c T R`: the function items by `T`'s shape, the
rule items by W1. -/
theorem gamma_fromS {T : List P} (hT : TiePair.shapeB (TiePair.gammaPats c) T = true) (h : rulesTieB c R = true) :
    ∀ φ, Γ c φ → PreS c T R ⊧ φ := by
  intro φ hφ M _ I hI
  refine TiePair.gamma_from hT φ hφ (I := I) fun ψ hψ => ?_
  rcases hψ with (hψ | hψ) | hψ
  · rcases hψ with hψ | hψ
    · exact hI _ (Or.inl (Or.inl (List.mem_append_left _ hψ)))
    · exact hI _ (Or.inl (Or.inr hψ))
  · rcases hψ with ⟨it, hit, rfl⟩ | hx
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hit
      obtain ⟨t, ht, hent⟩ := rules_from_text h j it hj
      refine hent (I := I) fun χ hχ => ?_
      rcases hχ with hχ | hχ
      · rw [List.mem_singleton.mp hχ]
        exact hI _ (Or.inl (Or.inl (List.mem_append_right _ (List.mem_of_getElem? ht))))
      · exact hI _ (Or.inl (Or.inr hχ))
    · exact hI _ (Or.inl (Or.inr hx))
  · exact hI _ (Or.inr hψ)

/-- The cut to the sentences: what Γ entails, `PreS c T R` entails. -/
theorem cutS {T : List P} (hT : TiePair.shapeB (TiePair.gammaPats c) T = true) (h : rulesTieB c R = true)
    {ψ : P} (hψ : Γ c ⊧ ψ) : PreS c T R ⊧ ψ :=
  fun hI => hψ fun φ hφ => gamma_fromS hT h φ hφ hI
end

/-! ## The successors of a configuration, listed -/

section
open Exec Cert

/-- At each match of `r` at `x`, within fuel n: the `requires` is `false`, or it is `true` and the
right side has no value, or its value is no configuration, or the `ensures` is `false`, or the
`ensures` is `true` and the value is one of `ys`. -/
def ruleListed (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) (ys : List GroundTerm) : Bool :=
  ((matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars)).all fun σ =>
    match reqValC c n r σ with
    | some false => true
    | some true => match evalTC c n σ r.rhs with
      | some none => true
      | some (some y) => !(c.sortOf y == some topCellSort) || ensValC c n r σ == some false ||
          (ensValC c n r σ == some true && ys.any (same · y))
      | none => false
    | none => false

/-- A rule of a smaller priority than `r` has a match at `x` whose `requires` is `true` within
fuel n. -/
def blockedAt (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : Bool :=
  c.rules.any fun r₀ => decide (r₀.prio < r.prio) &&
    ((matchP c (patFuel [r₀.lhs]) [] r₀.lhs x).filter (wellSorted c r₀.vars)).any
      (fun σ => reqValC c n r₀ σ == some true)

/-- Each rule is blocked at `x` or lists its successors among `ys`. -/
def listedCheck (c : Semantics) (n : Nat) (x : GroundTerm) (ys : List GroundTerm) : Bool :=
  c.rules.all fun r => blockedAt c n r x || ruleListed c n r x ys

variable {c : Semantics}

/-- What `ruleListed` gives at a match, read with the executable evaluation. -/
theorem ruleListed_at {n : Nat} {r : Rule} {σ : Subst} {ys : List GroundTerm}
    (h : (match reqValC c n r σ with
      | some false => true
      | some true => match evalTC c n σ r.rhs with
        | some none => true
        | some (some y) => !(c.sortOf y == some topCellSort) || ensValC c n r σ == some false ||
            (ensValC c n r σ == some true && ys.any (same · y))
        | none => false
      | none => false) = true) :
    reqVal c n r σ = some false ∨ (reqVal c n r σ = some true ∧
      (evalT c n σ r.rhs = some none ∨
        ∃ y, evalT c n σ r.rhs = some (some y) ∧
          (c.sortOf y ≠ some topCellSort ∨ ensVal c n r σ = some false ∨ y ∈ ys))) := by
  cases hq : reqValC c n r σ with
  | none => rw [hq] at h; cases h
  | some b =>
    cases b with
    | false => exact Or.inl (reqValC_sound hq)
    | true =>
      rw [hq] at h
      refine Or.inr ⟨reqValC_sound hq, ?_⟩
      cases he : evalTC c n σ r.rhs with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h
        cases o with
        | none => exact Or.inl (evalTC_sound n he)
        | some y =>
          refine Or.inr ⟨y, evalTC_sound n he, ?_⟩
          by_cases hs : c.sortOf y = some topCellSort
          · simp only [hs, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
              Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
            rcases h with h | ⟨-, z, hz, hzy⟩
            · exact Or.inr (Or.inl (ensValC_sound h))
            · exact Or.inr (Or.inr (same_iff.mp hzy ▸ hz))
          · exact Or.inl hs

variable (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)

include hok hsr hmr in
/-- **The listed successors at every fuel**: where `listedCheck` holds at fuel n, every successor
the executable step lists at x, at any fuel, is one of `ys`. -/
theorem successorsN_sub_of_listed (hco : CoherentAll c) {n : Nat} {x : GroundTerm} {ys : List GroundTerm}
    (h : listedCheck c n x ys = true) (m : Nat) : ∀ y ∈ successorsN c m x, y ∈ ys := by
  intro y hy
  obtain ⟨r, hr, hlow, σ, hσb, he, hs, hens⟩ := successorsN_mem_ens hy
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  have hagree : ∀ {r : Rule} {σ : Subst} {t : Term} {v w : Option GroundTerm} {s : Srt},
      c.WellSorted r.vars σ → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some s →
      evalT c n σ t = some v → evalT c m σ t = some w → v = w := fun hσw ht hv hw =>
    EvalTerm.functional hco (evalT_sound hsc hcc hmc n hv (headsOK_fns _) hσw ht)
      (evalT_sound hsc hcc hmc m hw (headsOK_fns _) hσw ht)
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp h r hr) with hb | hl
  · -- a rule of a smaller priority applies at fuel n: at fuel m its `requires` is not `false`
    obtain ⟨r₀, hr₀, hb⟩ := List.any_eq_true.mp hb
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hp, happ⟩ := hb
    obtain ⟨σ₀, hσ₀, hb₀⟩ := List.any_eq_true.mp happ
    have hq := reqValC_sound (beq_iff_eq.mp hb₀)
    have hl := hlow r₀ hr₀ hp (σ₀, reqVal c m r₀ σ₀) (ruleMatches_mem.mpr ⟨hσ₀, rfl⟩)
    simp only at hl
    have hσw : c.WellSorted r₀.vars σ₀ := wellSorted_iff.mp (List.mem_filter.mp hσ₀).2
    obtain ⟨-, -, -, hrqOK, -⟩ := ruleOK_of hok hr₀
    unfold reqVal at hq hl
    cases hrq : r₀.req with
    | none => rw [hrq] at hl; cases hl
    | some t =>
      rw [hrq] at hq hl hrqOK
      simp only at hq hl
      cases hn : evalT c n σ₀ t with
      | none => rw [hn] at hq; cases hq
      | some v =>
        cases hm : evalT c m σ₀ t with
        | none => rw [hm] at hl; cases hl
        | some w =>
          rw [hn] at hq; rw [hm] at hl
          cases hagree hσw (reqOK_some hrqOK) hn hm
          simp only [Option.map_some, Option.some.injEq] at hq hl
          rw [hq] at hl; cases hl
  · obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσb
    have h2 := ruleListed_at (List.all_eq_true.mp hl σ hσm)
    have hσw : c.WellSorted r.vars σ := wellSorted_iff.mp (List.mem_filter.mp hσm).2
    obtain ⟨-, -, -, hrqOK, hrtOK⟩ := ruleOK_of hok hr
    have hreq : reqVal c n r σ = some true ∨ reqVal c n r σ = none := by
      unfold reqVal at hb ⊢
      cases hrq : r.req with
      | none => left; rfl
      | some t =>
        rw [hrq] at hb
        cases hm : evalT c m σ t with
        | none => simp [hm] at hb
        | some w =>
          cases hn : evalT c n σ t with
          | none => right; simp only [hn, Option.map_none]
          | some v =>
            left
            rw [hrq] at hrqOK
            cases hagree hσw (reqOK_some hrqOK) hn hm
            simp only [hm, Option.map_some, Option.some.injEq] at hb
            simp [hn, hb]
    rcases h2 with h2 | ⟨h2, h3⟩
    · rcases hreq with hreq | hreq <;> rw [hreq] at h2 <;> cases h2
    · rcases h3 with h3 | ⟨y', h3, hs'⟩
      · cases hagree hσw hrtOK h3 he
      · cases hagree hσw hrtOK h3 he
        rcases hs' with hs' | hs' | hs'
        · exact absurd hs hs'
        · exact (ensVal_not_false_true hok hsr hmr hco hr hσw hs' hens).elim
        · exact hs'
end

section
open Exec Cert
variable (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false)
include hr

theorem ruleListed_withHooks (n : Nat) (r : Rule) (x : GroundTerm) (ys : List GroundTerm) :
    ruleListed (c.withHooks H) n r x ys = ruleListed c n r x ys := by
  unfold ruleListed
  rw [matchP_withHooksC, wellSorted_withHooks_hr c H hr]
  simp only [reqValC_withHooks_hr c H hr, evalTC_withHooks c H hr, sortOf_withHooks_hrC c H hr,
    ensValC_withHooks_hr c H hr]

theorem blockedAt_withHooks (n : Nat) (r : Rule) (x : GroundTerm) :
    blockedAt (c.withHooks H) n r x = blockedAt c n r x := by
  unfold blockedAt
  simp only [matchP_withHooksC, wellSorted_withHooks_hr c H hr, reqValC_withHooks_hr c H hr]
  rfl

theorem listedCheck_withHooks (n : Nat) (x : GroundTerm) (ys : List GroundTerm) :
    listedCheck (c.withHooks H) n x ys = listedCheck c n x ys := by
  unfold listedCheck
  simp only [ruleListed_withHooks c H hr, blockedAt_withHooks c H hr]
  rfl
end

section
open Exec Cert
variable {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)

/-- A configuration of the data is one under every interpretation, where no parameter is an open
generator. -/
def cfgH (hr : ∀ k ∈ c.params, k.raw = false) (x : Config c) (H : HookParams) : Config (c.withHooks H) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks _ _ hr]; exact x.property⟩

include hok hsr hmr in
/-- **The successors, for every interpretation of the parameters**: where `listedCheck` holds on
the data, every `Step (c.withHooks H)` successor of `x` is one of `ys`, for every H whose clauses
of one priority are coherent, where no clause is `aside` and no parameter is raw. -/
theorem listed_sound (H : HookParams) (hco : CoherentAll (c.withHooks H)) {n : Nat}
    {x : Config c} {ys : List GroundTerm} (h : listedCheck c n x.val ys = true)
    (hna : c.asideFree = true) (hr : ∀ k ∈ c.params, k.raw = false) :
    ∀ y, Step (c.withHooks H) (cfgH hr x H) y → y.val ∈ ys := by
  intro y hstep
  obtain ⟨m, hm⟩ := (Exec.step_iff_all hok hsr hmr H hco (cfgH hr x H) y hna).mp hstep
  obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp hm
  rw [← same_iff.mp hzy]
  exact successorsN_sub_of_listed ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr) hco
    ((listedCheck_withHooks c H hr n x.val ys).trans h) m z hz

include hok hsr hmr in
/-- A step some rule's check accepts on the data, which reads no interpretation, is a step under
every interpretation. -/
theorem step_withHooks (hr : ∀ k ∈ c.params, k.raw = false) {x y : Config c} {n : Nat}
    (hc : c.rules.any (fun r => checkStep c n r x.val y.val) = true) (H : HookParams) :
    Step (c.withHooks H) (cfgH hr x H) (cfgH hr y H) := by
  obtain ⟨r, hmem, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨_, hstep⟩ := step_of_listed ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    (x := cfgH hr x H)
    (listed_of_checkStep (c := c.withHooks H) (r := r) hmem ((checkStep_withHooks c H hr n r _ _).trans hc))
  exact hstep
end

end TieRulePair

end KCore
