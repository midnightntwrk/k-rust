/-
  What kore.k's `succs` gives at the encoding of an object definition `d` and of a configuration
  `x` of `d₀ d`, read from User.RuleWalk's `rule_walk`, at the statements' own call
  (`SuccsAt sig E x r`, KKStatements.lean), with `hr`, `hE` the only hypotheses.

  - `succs_char`: either `stuck`, and no rule applies at `x`; or `next(L)` at a priority `p` at
    which a rule applies and below which none does, where each member of `L` is no `bot` and is a
    result of a rule of priority `p` under a match (`FiredBy_krw`, KK-1's `FiresK`), and each match
    of each rule of priority `p` fails its `requires` or has a result that is in `L` unless it is
    `bot` (the completeness conjunct K-2 reads).
  - `succs_value`: the result is a `Step` value (never none: no kore.k function is undefined on an
    encoding).
  - `succs_unique`: one result, with no hypothesis (`KK.coherent`).

  KK-1's `succs_char` states `L`'s membership as an iff. With `FiredBy_krw` for `FiresK` the
  converse needs that a term has one result (`hco`): a `requires` with two results, `true` and
  another, has a `FiredBy_krw` at `true` where kore.k computed the other one and listed nothing.
  So `succs_char` holds the forward half and the completeness conjunct, and the iff is
  `succs_mem_iff_kch`, under `hco : CoherentAll (d₀ d)`.
-/
import User.RuleWalk

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

section
variable {d : Semantics} {E : D}

/-- `drop(X, Ts)`'s members: those of `Ts` other than `X`. -/
theorem mem_dropF_kch {x y : T} : ∀ {us : List T}, y ∈ dropF x us ↔ y ∈ us ∧ y ≠ x
  | [] => by simp [dropF]
  | u :: us => by
    rw [dropF]
    by_cases h : u = x
    · rw [if_pos h, mem_dropF_kch]
      constructor
      · exact fun ⟨hm, hne⟩ => ⟨List.mem_cons_of_mem _ hm, hne⟩
      · rintro ⟨hm, hne⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd h hne
        · exact ⟨hm, hne⟩
    · rw [if_neg h, List.mem_cons, mem_dropF_kch]
      constructor
      · rintro (rfl | ⟨hm, hne⟩)
        · exact ⟨List.mem_cons_self .., h⟩
        · exact ⟨List.mem_cons_of_mem _ hm, hne⟩
      · rintro ⟨hm, hne⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact .inl rfl
        · exact .inr ⟨hm, hne⟩

/-- **`succs` characterized.** At a configuration `x` of `d₀ d`, kore.k's `succs` gives `stuck`
and no rule applies; or it gives `next(L)` at a priority `p` at which a rule applies and below
which none does, each member of `L` is a result other than `bot` of a rule of priority `p` under
a match, and each match of each rule of priority `p` fails its `requires` or has a result, in `L`
where it is not `bot`. -/
theorem succs_char (hr : CExec.execReady d = true) (hE : encDef d = some E) (x : Config (d₀ d))
    {r : Option GroundTerm} (h : SuccsAt sig E x.val r) :
    (r = some (embSt .stuck) ∧ ∀ ru ∈ d.rules, NotApplies (d₀ d) ru x.val) ∨
    ∃ (p : Nat) (L : List T), r = some (embSt (.next L)) ∧
      (∃ ru ∈ d.rules, ru.prio = p ∧ RuleApplies (d₀ d) ru x.val) ∧
      (∀ ru ∈ d.rules, ru.prio < p → NotApplies (d₀ d) ru x.val) ∧
      (∀ y', y' ∈ L → y' ≠ .bot ∧ ∃ ru ∈ d.rules, ru.prio = p ∧ ∃ σ, FiredBy_krw d ru σ x.val y') ∧
      (∀ ru ∈ d.rules, ru.prio = p → ∀ σ, (d₀ d).WellSorted ru.vars σ →
        PatVal (d₀ d) σ ru.lhs x.val →
        RuleReqFails (d₀ d) σ ru ∨ ∃ u, FiredBy_krw d ru σ x.val u ∧ (u ≠ .bot → u ∈ L)) := by
  rcases rule_walk hr hE x.property h with h | ⟨P, us, hres, hne, hb, hf⟩
  · exact .inl h
  obtain ⟨ru₀, hm₀, hp₀, happ⟩ := firedAt_applies_krw hE hf hne
  subst hp₀
  refine .inr ⟨ru₀.prio, dropF .bot us, hres, ⟨ru₀, hm₀, rfl, happ⟩,
    fun ru hm hlt => hb ru hm fun P e => by cases e; exact Int.ofNat_lt.mpr hlt,
    fun y' hy => ?_, fun ru hm hp σ hσ hx => ?_⟩
  · obtain ⟨hy, hne'⟩ := mem_dropF_kch.mp hy
    obtain ⟨ru, hm, hp, hfb⟩ := hf.1 y' hy
    exact ⟨hne', ru, hm, Int.ofNat_inj.mp hp, hfb⟩
  · rcases hf.2 ru hm (by rw [hp]) σ hσ hx with h | ⟨u, hu, hfb⟩
    · exact .inl h
    · exact .inr ⟨u, hfb, fun hb' => mem_dropF_kch.mpr ⟨hu, hb'⟩⟩

/-- **`succs` has a value**, a `Step`, at every configuration. -/
theorem succs_value (hr : CExec.execReady d = true) (hE : encDef d = some E) (x : Config (d₀ d))
    {r : Option GroundTerm} (h : SuccsAt sig E x.val r) : ∃ st, r = some (embSt st) := by
  rcases rule_walk hr hE x.property h with ⟨h, -⟩ | ⟨P, us, hres, -⟩
  · exact ⟨_, h⟩
  · exact ⟨_, hres⟩

/-- **`succs` has one result**, at any `E` and `x`. -/
theorem succs_unique {x : GroundTerm} {r r' : Option GroundTerm} (h : SuccsAt sig E x r)
    (h' : SuccsAt sig E x r') : r = r' :=
  ((evalF_iff h).mp h').symm

/-- Under `hco`, two results of one rule under one substitution are one. -/
theorem firedBy_functional_kch (hco : CoherentAll (d₀ d)) {ru : Rule} {σ : Subst}
    {x : GroundTerm} {u u' : T} (h : FiredBy_krw d ru σ x u) (h' : FiredBy_krw d ru σ x u') :
    u = u' := by
  obtain ⟨-, -, -, o, ho, hu⟩ := h
  obtain ⟨-, -, -, o', ho', hu'⟩ := h'
  have e := EvalTerm.functional hco ho ho'
  subst e
  rcases hu with ⟨hn, rfl⟩ | ⟨e, w, he, hw, rfl⟩ <;> rcases hu' with ⟨hn', rfl⟩ | ⟨e', w', he', hw', rfl⟩
  · rfl
  · rw [hn] at he'; cases he'
  · rw [he] at hn'; cases hn'
  · rw [he] at he'
    cases he'
    rw [EvalTerm.functional hco hw hw']

/-- **`next(L)`'s members under `hco`**: exactly the results other than `bot` of the rules of the
priority under a match. -/
theorem succs_mem_iff_kch (hr : CExec.execReady d = true) (hco : CoherentAll (d₀ d))
    (hE : encDef d = some E) (x : Config (d₀ d)) {L : List T}
    (h : SuccsAt sig E x.val (some (embSt (.next L)))) :
    ∃ p : Nat, (∃ ru ∈ d.rules, ru.prio = p ∧ RuleApplies (d₀ d) ru x.val) ∧
      (∀ ru ∈ d.rules, ru.prio < p → NotApplies (d₀ d) ru x.val) ∧
      ∀ y', y' ∈ L ↔ y' ≠ .bot ∧ ∃ ru ∈ d.rules, ru.prio = p ∧ ∃ σ, FiredBy_krw d ru σ x.val y' := by
  rcases succs_char hr hE x h with ⟨hs, -⟩ | ⟨p, L', hL, happ, hbelow, hmem, hcomp⟩
  · exact absurd (embSt_injective (Option.some.inj hs)) (by simp)
  have e : L' = L := by
    have := embSt_injective (Option.some.inj hL)
    cases this; rfl
  subst e
  refine ⟨p, happ, hbelow, fun y' => ⟨hmem y', ?_⟩⟩
  rintro ⟨hne, ru, hm, hp, σ, hfb⟩
  rcases hcomp ru hm hp σ hfb.1 hfb.2.1 with hf | ⟨u, hu, hin⟩
  · exfalso
    cases hf with
    | intro ht he hv =>
      exact hv (EvalTerm.functional hco he (hfb.2.2.1 _ ht))
    | pre hp' =>
      rw [(ruleShape_krw (encodable_of_encDef_ksc hE) hm).2.1] at hp'
      cases Holds.top_eq hp'
  · have e := firedBy_functional_kch hco hu hfb
    subst e
    exact hin hne

end

/-! ## Instances -/

/-- `mem_dropF_kch` at `drop(bot, iv(1) ; bot)`. -/
example : T.iv 1 ∈ dropF .bot [.iv 1, .bot] ∧ T.bot ∉ dropF .bot [.iv 1, .bot] :=
  ⟨mem_dropF_kch.mpr ⟨by simp, by simp⟩, fun h => (mem_dropF_kch.mp h).2 rfl⟩

/-- `succs_char` is stated at the statements' own call. -/
example (d : Semantics) (E : D) (x : Config (d₀ d)) (r : Option GroundTerm) :
    SuccsAt sig E x.val r = Eval (K₀ sig) sig.succs [sig.embD E, sig.emb (sig.enc x.val)] r := rfl

/-! ## Checks -/

#check @succs_char
#check @succs_value
#check @succs_unique
#check @succs_mem_iff_kch

open Lean in
#eval show CoreM Unit from do
  for n in [``mem_dropF_kch, ``succs_char, ``succs_value, ``succs_unique, ``firedBy_functional_kch,
      ``succs_mem_iff_kch] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
