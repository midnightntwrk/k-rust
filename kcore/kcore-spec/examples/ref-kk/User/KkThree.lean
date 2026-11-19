/-
  **The three statements at `KK.sig`**: kore.k's `succs`, read from its kompiled text, is sound,
  stuck exactly where no rule applies (the half without `hco`), and complete, for every object
  definition `d` that `execReady` accepts and `encDef` encodes (`succs_sound : SuccsSound sig`,
  `succs_stuck : SuccsStuck sig`, `succs_complete : SuccsComplete sig`, together `kk_step`; the propositions of
  KKStatements.lean, not restated).

  - Soundness and stuckness are `succs_char` (User.SuccsChar) with `firedBy_step_krw`: a member
    of `next(L)` is a result other than `bot` of a rule of the walk's priority, below which no rule
    applies, so it is a `Step`.
  - Completeness is K-2: a `Step` by the rule `ru` under `σ` has `ru`'s `requires` true, its right
    side the successor and its ensures true under `σ`. Under `hco` a term has one result
    (`EvalTerm.functional`), so `σ` fails no `requires` (`ruleReqFails_false_kkt`): `succs` is not
    `stuck`, `ru` is at the walk's priority `p` (below `p` no rule applies, and the rule that
    applies at `p` is not below `ru` by `hprio`), and the result kore.k has at `σ` is the
    successor's encoding, which is no `bot`, so it is in `L`.
  - `succs_stuck_iff` (with `hco`): `stuck` exactly where no rule applies; `succs_applies_no_result`
    (with `hco`): `next(.Ts)` where a rule applies and there is no step (every result `bot`).
-/
import User.SuccsChar

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

section
variable {d : Semantics} {E : D}

/-- Under `hco`, a substitution under which a rule's `requires` is true and whose predicate is
`\top` fails no condition of the rule. -/
theorem ruleReqFails_false_kkt (hco : CoherentAll (d₀ d)) {ru : Rule} {σ : Subst}
    (hpre : ru.pre = .top) (hreq : ∀ t, ru.req = some t → EvalTerm (d₀ d) σ t (some (bool true)))
    (h : RuleReqFails (d₀ d) σ ru) : False := by
  cases h with
  | intro ht he hv => exact hv (EvalTerm.functional hco he (hreq _ ht))
  | pre hp => rw [hpre] at hp; cases Holds.top_eq hp

/-- Under `hco`, a rule that applies is not one that does not. -/
theorem applies_notApplies_kkt (hco : CoherentAll (d₀ d)) (hE : encDef d = some E) {ru : Rule}
    (hm : ru ∈ d.rules) {x : GroundTerm} (ha : RuleApplies (d₀ d) ru x)
    (hn : NotApplies (d₀ d) ru x) : False := by
  obtain ⟨σ, hσ, hx, hreq, -⟩ := ha
  exact ruleReqFails_false_kkt hco (ruleShape_krw (encodable_of_encDef_ksc hE) hm).2.1 hreq
    (hn σ hσ hx)

theorem embSt_next_ne_stuck_kkt {L : List T} : some (embSt (.next L)) ≠ some (embSt .stuck) :=
  fun h => by cases embSt_injective (Option.some.inj h)

end

/-! ## The three statements -/

/-- **Soundness**: each successor `succs` lists is the encoding of a `Step`. -/
theorem succs_sound : SuccsSound sig := by
  intro d E hr hE x L h y' hy
  rcases succs_char hr hE x h with ⟨hs, -⟩ | ⟨p, L', hL, -, hbelow, hmem, -⟩
  · exact absurd hs embSt_next_ne_stuck_kkt
  have e : St.next L = St.next L' :=
    embSt_injective (Option.some.inj (show some (embSt (.next L)) = some (embSt (.next L')) from hL))
  cases e
  obtain ⟨hne, ru, hm, hp, σ, hfb⟩ := hmem y' hy
  exact firedBy_step_krw hr hE hm hfb hne fun r' hr' hlt =>
    hbelow r' hr' (by have := hlt _ rfl; rw [hp] at this; exact Int.ofNat_lt.mp this)

/-- **Stuckness**: where `succs` gives `stuck`, no rule applies. -/
theorem succs_stuck : SuccsStuck sig := by
  intro d E hr hE x h
  rcases succs_char hr hE x h with ⟨-, hna⟩ | ⟨p, L, hL, -⟩
  · exact hna
  · exact absurd hL.symm embSt_next_ne_stuck_kkt

/-- **Completeness** (K-2): where `succs` has a value at all, it is `next(L)` and `L` holds the
encoding of every `Step`. -/
theorem succs_complete : SuccsComplete sig := by
  intro d E hr hco hE x y s hdef hst
  have hc := encodable_of_encDef_ksc hE
  obtain ⟨ru, σ, hb⟩ := step_iff_by.mp hst
  have hpre := (ruleShape_krw hc hb.mem).2.1
  have hfail : RuleReqFails (d₀ d) σ ru → False := ruleReqFails_false_kkt hco hpre hb.hreq
  have happ : RuleApplies (d₀ d) ru x.val := ⟨σ, hb.hσ.at _, hb.hmatch, hb.hreq, hb.hpre⟩
  rcases succs_char hr hE x hdef with ⟨-, hna⟩ | ⟨p, L, hL, ⟨ru₀, hm₀, hp₀, happ₀⟩, hbelow, -, hcomp⟩
  · exact (applies_notApplies_kkt hco hE hb.mem happ (hna ru hb.mem)).elim
  have hp : ru.prio = p := by
    rcases Nat.lt_trichotomy ru.prio p with hlt | heq | hgt
    · exact (applies_notApplies_kkt hco hE hb.mem happ (hbelow ru hb.mem hlt)).elim
    · exact heq
    · exact (applies_notApplies_kkt hco hE hm₀ happ₀ (hb.hprio ru₀ hm₀ (hp₀ ▸ hgt))).elim
  rcases hcomp ru hb.mem hp σ hb.hσ hb.hmatch with h | ⟨u, ⟨-, -, -, o, ho, hu⟩, hin⟩
  · exact (hfail h).elim
  have eo := EvalTerm.functional hco ho hb.heval
  subst eo
  have hu' : u = enc y.val := by
    rcases hu with ⟨-, rfl⟩ | ⟨e, w, he, hw, rfl⟩
    · rfl
    · rw [EvalTerm.functional hco hw (hb.hens e he)]
      unfold ensureF
      rw [if_pos (show encR (some (bool true)) = T.bv true from rfl)]
      rfl
  subst hu'
  have hlv : litsV y.val = true := litsV_kst hr hc y.property (by decide)
  have hnb : enc y.val ≠ .bot := fun e => by
    have := enc_ne_bot hlv
    rw [e] at this
    exact this
  exact ⟨L, Option.some.inj hL, hin hnb⟩

/-- **The three statements at `KK.sig`** (DONE-0's `KK.kk_step`). -/
theorem kk_step : SuccsSound sig ∧ SuccsStuck sig ∧ SuccsComplete sig :=
  ⟨succs_sound, succs_stuck, succs_complete⟩

/-! ## With `hco`: stuck exactly where no rule applies, and the empty list -/

section
variable {d : Semantics} {E : D}

/-- **`stuck` exactly where no rule applies**, under `hco`, where `succs` has a value. -/
theorem succs_stuck_iff (hr : CExec.execReady d = true) (hco : CoherentAll (d₀ d))
    (hE : encDef d = some E) (x : Config (d₀ d)) {s : GroundTerm}
    (hdef : SuccsAt sig E x.val (some s)) :
    s = embSt .stuck ↔ ∀ ru ∈ d.rules, NotApplies (d₀ d) ru x.val := by
  constructor
  · rintro rfl
    exact succs_stuck hr hE x hdef
  · intro hna
    rcases succs_char hr hE x hdef with ⟨hs, -⟩ | ⟨p, L, -, ⟨ru₀, hm₀, -, happ₀⟩, -⟩
    · exact Option.some.inj hs
    · exact (applies_notApplies_kkt hco hE hm₀ happ₀ (hna ru₀ hm₀)).elim

/-- **`next(.Ts)`**, under `hco`: a rule applies and there is no step (every result of the
walk's priority is `bot`: a right side or an ensures without a value). -/
theorem succs_applies_no_result (hr : CExec.execReady d = true) (hco : CoherentAll (d₀ d))
    (hE : encDef d = some E) (x : Config (d₀ d))
    (h : SuccsAt sig E x.val (some (embSt (.next [])))) :
    (∃ ru ∈ d.rules, RuleApplies (d₀ d) ru x.val) ∧ ∀ y, ¬ Step (d₀ d) x y := by
  refine ⟨?_, fun y hst => ?_⟩
  · rcases succs_char hr hE x h with ⟨hs, -⟩ | ⟨p, L, -, ⟨ru₀, hm₀, -, happ₀⟩, -⟩
    · exact absurd hs embSt_next_ne_stuck_kkt
    · exact ⟨ru₀, hm₀, happ₀⟩
  · obtain ⟨L, hL, hin⟩ := succs_complete hr hco hE h hst
    have e : St.next [] = St.next L := embSt_injective (show embSt (.next []) = embSt (.next L) from hL)
    cases e
    exact (nomatch hin)

end

/-! ## Checks -/

#check @succs_sound
#check @succs_stuck
#check @succs_complete
#check @kk_step
#check @succs_stuck_iff
#check @succs_applies_no_result

open Lean in
#eval show CoreM Unit from do
  for n in [``ruleReqFails_false_kkt, ``applies_notApplies_kkt, ``embSt_next_ne_stuck_kkt,
      ``succs_sound, ``succs_stuck, ``succs_complete, ``kk_step, ``succs_stuck_iff,
      ``succs_applies_no_result] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
