/-
  KCore. The value model at a transition T satisfies the axiom of a rule with existential
  variables.

  A rule's axiom is `\rewrites(L, ∃ē. (rhs ∧ ens))`, ē its existential variables (`ruleRight`), and
  L holds `⌈∃ē. (rhs ∧ ens)⌉`. The axiom's guards give every variable but the existential ones a
  value of its sort; inside `∃ē` every element of a sort is a value, so a configuration x is in L
  under such a valuation σ exactly where the left side matches x, the `requires` holds, no rule of
  a smaller priority applies, and some σ' that differs from σ at ē only evaluates the right side to
  a value with a true `ensures` (`rule_premise_T`). The axiom then asks that x has a T successor in
  `∃ē. (rhs ∧ ens)`: one some σ' of that kind gives.

  - `StepMAt c r σ x y`: `StepM`'s premises for the rule r under σ, r not asked to be one of the
    definition's; `StepMBy` adds that it is one, and `StepM` is `StepMBy` of some rule and σ
    (`stepM_iff_by`).
  - `ruleRight_read_T`: the elements of `∃ē. (rhs ∧ ens)` in the value model at T, under a
    valuation reading the other variables as σ: the right side's values under the σ' that differ
    from σ at ē only and give ē values of their sorts.
  - `applies_iff_T`: the competitors' `applies` read at T, for rules with `ruleSorted` and
    `rulePlainEx` (an existential variable occurs in no `applies`).
  - `sat_rule_T`: the axiom of a rule with `ruleSorted` and `rulePlainEx`, not asked to be one of
    the definition's, holds at T when every instance of `StepMAt` of a rule without existential
    variables is in T (`hall`) and, for a rule with existential variables, some instance that
    differs from it at ē only is (`hsome`).
  - `satRulesGoal_T`: the same for every rule of the definition, from the rules' facts taken per
    rule.
-/
import KcoreSpec.ModelFnsCl
import KcoreSpec.Confined
import KcoreSpec.OpenConsistent
import KcoreSpec.ExPlain
import KcoreSpec.CondKoreVars

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

/-- `StepM`'s premises for the rule r under σ: σ well sorted, the left side matching x, the
`requires`, `pre`, `ensures` and `post` true, the right side evaluating to y, and no rule of the
definition of a smaller priority applying at x. The rule is not asked to be one of the definition's. -/
def StepMAt (c : Semantics) (r : Rule) (σ : Subst) (x y : GroundTerm) : Prop :=
  c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true ∧
    EvalTerm c σ r.rhs (some y) ∧
    (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true ∧
    ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x

/-- `StepM`'s premises for a rule of the definition. -/
def StepMBy (c : Semantics) (r : Rule) (σ : Subst) (x y : GroundTerm) : Prop :=
  r ∈ c.rules ∧ StepMAt c r σ x y

/-- `StepM` is `StepMBy` of some rule and substitution. -/
theorem stepM_iff_by (c : Semantics) {x y : GroundTerm} : StepM c x y ↔ ∃ r σ, StepMBy c r σ x y :=
  ⟨fun ⟨r, hr, σ, h⟩ => ⟨r, σ, hr, h⟩, fun ⟨r, σ, hr, h⟩ => ⟨r, hr, σ, h⟩⟩

variable {c : Semantics}

/-! ## The value model at T -/

/-- **A value denotes its own element** in the value model at any transition `T`. -/
theorem den_val_T (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) (v : GroundTerm) {s : Srt}
    (hv : c.sortOf v = some s) (e : Valuation Elem) (m : Elem) :
    (den c v).interpret (stdI_T c T) e m ↔ m = .val v :=
  AtT.den_val (T := T) h v hv e m

/-- `•φ` in the value model at `T`: the configurations with a `T` successor in `φ`. -/
theorem sNext_iff_T (T : GroundTerm → GroundTerm → Prop) (φ : KoreAML.P) (e : Valuation Elem) (x : GroundTerm) :
    (KoreAML.sNext φ).interpret (stdI_T c T) e (.val x) ↔
      ∃ y, φ.interpret (stdI_T c T) e (.val y) ∧ StepE_T c T (.val x) (.val y) :=
  AtT.sNext_iff φ e x

/-- **The value model at any transition `T` satisfies the parts of `Γ` and `Γcl` that do not read
the step**: the signature, the constructors (with the open generators' law sentences, where the
interpretation satisfies the laws: `OpenLaws`), the domains, the collections, the
interpretation's values at silent points, and Bool's closure where Bool holds only its literals;
with them the functions' equations, where the model satisfies them (`hFns`). -/
theorem model_parts_T (h : HypModelCore c) (hc : c.coreOK = true) (hl : OpenLaws c)
    (T : GroundTerm → GroundTerm → Prop) (hFns : stdI_T c T ⊧ᴵP ΓFns c) :
    (stdI_T c T ⊧ᴵP ΓSig c) ∧ (stdI_T c T ⊧ᴵP ΓCons c) ∧ (stdI_T c T ⊧ᴵP ΓDomains c) ∧
    (stdI_T c T ⊧ᴵP ΓColls c) ∧ (stdI_T c T ⊧ᴵP ΓFns c) ∧ (stdI_T c T ⊧ᴵP ΓFallback c) ∧
    (c.litSort Srt.bool = true → (stdI_T c T ⊧ᴵ boolClosed c)) :=
  ⟨AtT.satSigGoal h, AtT.satConsGoal h hl, AtT.satDomainsGoal h, AtT.satCollsGoal h, hFns,
   AtT.satFallbackGoal h, AtT.boolClosed_model h hc⟩

/-- A rule's right side with a `\top` `post` is `∃ē. (rhs ∧ ens)`. -/
theorem ruleRight_eqEx {r : Rule} (hpost : r.post = .top) (hlt : ∀ i ∈ r.exs, i < r.vars.length) :
    ruleRight c r = KoreAML.existsAll (srtOf c topCellSort) (ruleExBinders c r) (ruleRightBody c r) := by
  unfold ruleRight ruleExBinders ruleRightBody KoreAML.existsAll
  dsimp only
  rw [filterMap_getElem?_of_lt _ _ (by rw [canonVars_length]; exact hlt)]
  simp only [hpost, Cond.conj, Cond.isTop, if_true, List.append_nil, List.foldr_map]

/-- The keys of the binders of a rule's right side. -/
theorem ruleExBinders_keys {r : Rule} :
    ((ruleExBinders c r).map KoreAML.evarKey) = r.exs.map (canonKey c r.vars) := by
  unfold ruleExBinders canonKey
  rw [List.map_map]
  rfl

/-- A variable of a rule other than its existential ones is not bound by the right side's
binders. -/
theorem notBound_ruleEx {r : Rule} (hlt : ∀ i ∈ r.exs, i < r.vars.length) {i : Nat} (hi : i < r.vars.length)
    (hx : i ∉ r.exs) (bound : List KoreAML.VarKey) (hb : bound.contains (canonKey c r.vars i) = false) :
    (((ruleExBinders c r).map KoreAML.evarKey).reverse ++ bound).contains (canonKey c r.vars i) = false := by
  rw [ruleExBinders_keys]
  simp only [List.contains_append, hb, Bool.or_false]
  apply Bool.eq_false_iff.mpr
  intro hc
  rw [List.contains_iff_mem, List.mem_reverse, List.mem_map] at hc
  obtain ⟨j, hj, he⟩ := hc
  rw [canonKey_inj (hlt j hj) hi he] at hj
  exact hx hj

/-- A variable of a rule other than its existential ones, of its right side or `ensures`, is free in
its right side; every variable of the rule is a variable of it. -/
theorem ruleRight_keysEx {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) :
    (∀ i < r.vars.length, i ∉ r.exs → (i ∈ varOccs r.rhs ∨ ∃ t, r.ens = some t ∧ i ∈ varOccs t) →
      canonKey c r.vars i ∈ KoreAML.freeOf [] (ruleRight c r)) ∧
    (∀ i < r.vars.length, i ∈ r.exs ∨ i ∈ varOccs r.rhs ∨ (∃ t, r.ens = some t ∧ i ∈ varOccs t) →
      canonKey c r.vars i ∈ KoreAML.varsOf (ruleRight c r)) := by
  obtain ⟨-, -, -, -, -, -, hexs⟩ := ruleSorted_partsEx hs hp
  obtain ⟨-, hpost⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  rw [ruleRight_eqEx hpost hlt]
  let vs := canonVars c r.vars
  let C := srtOf c topCellSort
  refine ⟨fun i hi hx hocc => ?_, fun i hi hocc => ?_⟩
  · rw [freeOf_existsAll_eqEx]
    have hb := notBound_ruleEx (c := c) hlt hi hx [] rfl
    rw [List.append_nil] at hb
    unfold ruleRightBody
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList]
    simp only [List.append_nil]
    rcases hocc with hR | ⟨t, ht, hit⟩
    · exact List.mem_append_left _ (kore_freeOfBEx c vs r.rhs hR hb)
    · refine List.mem_append_right _ ?_
      rw [ht]; simp only [Option.map_some, reqPat]
      rw [KoreAML.freeOf]
      exact List.mem_append_left _ (kore_freeOfBEx c vs t hit hb)
  · rcases hocc with hE | hR | ⟨t, ht, hit⟩
    · refine varsOf_existsAll_binder _ ?_
      exact List.mem_map_of_mem hE
    · refine varsOf_existsAll_bodyEx ?_ _
      exact varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c vs r.rhs hR)
    · refine varsOf_existsAll_bodyEx ?_ _
      refine varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      rw [ht]; simp only [Option.map_some, reqPat]
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c vs t hit))

/-- **A rule's right side read at T.** Under a valuation that reads each variable of the rule but
the existential ones as its value under σ, of its sort, an element is in `∃ē. (rhs ∧ ens)` exactly
where it is the value of the right side under a well-sorted σ' that agrees with σ off ē, with a
true `ensures`. -/
theorem ruleRight_read_T (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainEx r = true) {T : GroundTerm → GroundTerm → Prop} {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e : Valuation Elem} {σ : Subst}
    (hσ : ∀ i < r.vars.length, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0))
    (hvar : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret (stdI_T c T) e m ↔
      ∃ σ' y, (∀ i < r.vars.length, i ∉ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
        EvalTerm c σ' r.rhs (some y) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
        m = .val y := by
  have hn := h.namesK
  obtain ⟨-, -, -, hensS, hrhss, hnd, hexs⟩ := ruleSorted_partsEx hs hp
  obtain ⟨-, hpost⟩ := Semantics.rulePlainEx_top hp
  have hnum := rule_vars_numEx h hs hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  let n := r.vars.length
  have hnd' : ((ruleExBinders c r).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    unfold ruleExBinders
    rw [List.map_map]
    exact nodup_map_of_injOn _ (fun i hi j hj he =>
      canonKey_inj (hlt i hi) (hlt j hj) (ev_inj (hkeys i (hlt i hi)) (hkeys j (hlt j hj)) he)) hnd
  have hsrt : ∀ b ∈ ruleExBinders c r, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hlt i hi)]; exact ⟨_, rfl⟩
  have hrhsOK : TermOK c (· < n) r.rhs := termOK_of_sorted h fns_headsOK hrhss
  have hensOK : ∀ t, r.ens = some t → TermOK c (· < n) t := fun t ht => termOK_of_sorted h fns_headsOK (hensS t ht)
  -- each variable but the existential ones reads as a value of its sort
  have hval : ∀ i < n, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) ∧
      e.evalEvar (tbl.ev (canonKey c r.vars i)) = .val v := by
    intro i hi hx
    obtain ⟨v, hv, hsv⟩ := hσ i hi hx
    obtain ⟨v', hv', he⟩ := (hvar i hi hx (e.evalEvar (tbl.ev (canonKey c r.vars i)))).mp
      ((AtT.var_read (T := T) i _).mpr rfl)
    rw [hv] at hv'
    cases hv'
    exact ⟨v, hv, hsv, he⟩
  rw [ruleRight_eqEx hpost hlt]
  constructor
  · intro hm
    obtain ⟨e', hoff, hguard, hbody⟩ := existsAll_elim AtT.defOK_std _ e m hnd' hsrt hm
    have hoffK : ∀ i < n, i ∉ r.exs →
        e'.evalEvar (tbl.ev (canonKey c r.vars i)) = e.evalEvar (tbl.ev (canonKey c r.vars i)) := by
      intro i hi hx
      refine hoff _ (fun b hb he => ?_)
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hij : i = j := canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)
      rw [hij] at hx
      exact hx hj
    have hin : ∀ i < n, InSort c (r.vars.getD i 0) (e'.evalEvar (tbl.ev (canonKey c r.vars i))) := by
      intro i hi
      by_cases hx : i ∈ r.exs
      · exact (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mp
          (hguard _ (List.mem_map_of_mem hx) _
            (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl))
      · obtain ⟨v, -, hsv, he⟩ := hval i hi hx
        rw [hoffK i hi hx, he]
        exact hsv
    obtain ⟨hσ', hvar'⟩ := AtT.substE_ok (T := T) hin
    unfold ruleRightBody at hbody
    rw [tr_and2, KoreAML.interp_sAnd] at hbody
    obtain ⟨y, hy, rfl⟩ := (AtT.tr_term h hvar' hrhsOK m).mp hbody.1
    have hys := rhs_sorted_open h hs hσ' hy
    have hens := (reqRead_T h hvar' r.ens hensOK hys).mp hbody.2
    refine ⟨substE c tbl r.vars e', y, fun i hi hx => ?_, hσ', hy, hens, rfl⟩
    obtain ⟨v, hv, -, he⟩ := hval i hi hx
    rw [substE_lookup hi, hoffK i hi hx, he, hv]
    rfl
  · rintro ⟨σ', y, hag, hσ', hy, hens, rfl⟩
    have hk' : ∀ i < n, i ∈ r.exs → canonKey c r.vars i ∈ tbl := fun i hi _ => hkeys i hi
    let f : Nat → Elem := fun j => .val ((σ'.lookup j).getD default)
    let e' := setV c tbl r.vars r.exs f e
    have hvar' : ∀ i, i < n → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ'.lookup i = some v ∧ m = .val v := by
      intro i hi m
      rw [AtT.var_read]
      show m = (setV c tbl r.vars r.exs f e).evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
      by_cases hx : i ∈ r.exs
      · rw [setV_on hk' hi hx]
        obtain ⟨w, hw, -⟩ := hσ' i (r.vars.getD i 0)
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
        simp [f, hw]
      · obtain ⟨v, hv, -, he⟩ := hval i hi hx
        rw [setV_off hk' hi hx, hag i hi hx, he, hv]
        simp
    have hys := rhs_sorted_open h hs hσ' hy
    refine AtT.existsAll_intro _ e e' _ hnd' hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_
    · show (if h : _ then _ else _) = _
      rw [dif_neg]
      rintro ⟨i, -, hix, rfl⟩
      exact hz _ (List.mem_map_of_mem hix) rfl
    · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb
      have hi := hlt i hix
      have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
        rw [canonVars_getD c hi]; rfl
      change ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt k at hk
      rw [hs'] at hk
      rw [← srt_inj hk]
      show InS (stdI_T c T) _ ((setV c tbl r.vars r.exs f e).evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [setV_on hk' hi hix]
      obtain ⟨w, hw, hws⟩ := hσ' i (r.vars.getD i 0)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
      show InS (stdI_T c T) _ (Elem.val ((σ'.lookup i).getD default))
      rw [hw, Option.getD_some]
      exact (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mpr hws
    · unfold ruleRightBody
      rw [tr_and2, KoreAML.interp_sAnd]
      exact ⟨(AtT.tr_term h hvar' hrhsOK _).mpr ⟨y, hy, rfl⟩, (reqRead_T h hvar' r.ens hensOK hys).mpr hens⟩

/-! ## A rule's axiom -/

/-- The axiom of a rule with a `\top` premise predicate: `\rewrites(lhs ∧ ⌈req = true⌉ ∧ ¬ ⋁
competitors ∧ ⌈right⌉, right)`, without the negation where the rule has no competitor. -/
theorem prioRuleK_preTop {r : Rule} (hpre : r.pre = .top) :
    prioRuleK c r =
      (let C := srtOf c topCellSort
       let vs := canonVars c r.vars
       let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
       if comps.isEmpty then
         .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
           .ceil C C (ruleRight c r)]) (ruleRight c r)
       else .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
           .not C (anyOfC C comps), .ceil C C (ruleRight c r)]) (ruleRight c r)) := by
  simp only [prioRuleK, hpre, Cond.conj, Cond.isTop, if_true, List.append_nil, List.cons_append,
    List.nil_append]

/-- **The left part of a rule's axiom, read at T.** For a rule with `ruleSorted` and `rulePlainEx`
(not asked to be one of the definition's), among rules with those facts, the axiom is
`\rewrites(L, ∃ē. (rhs ∧ ens))`; each variable but ē is free in L, and each is a variable of L.
Under a valuation that reads the variables but ē as their values under σ, a configuration x is in
L exactly where the left side matches x under σ, the `requires` holds, no rule of a smaller priority
applies, and some σ' that agrees with σ off ē is well sorted, evaluates the right side to a value
and makes the `ensures` true. -/
theorem rule_premise_T (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ i < r.vars.length, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] L) ∧
      ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst)
        (x : GroundTerm), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) → c.sortOf x = some topCellSort →
        (∀ i < r.vars.length, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0)) →
        (∀ i < r.vars.length, i ∉ r.exs → ∀ m,
          (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
            ∃ v, σ.lookup i = some v ∧ m = .val v) →
        ((KoreAML.tr ⟨tbl, []⟩ L).interpret (stdI_T c T) e (.val x) ↔
          PatVal c σ r.lhs x ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
          (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) ∧
          ∃ σ' y, (∀ i < r.vars.length, i ∉ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
            EvalTerm c σ' r.rhs (some y) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true)))) := by
  obtain ⟨hlhs, hocc, hreqs, -, -, -, hexs⟩ := ruleSorted_partsEx hs hp
  obtain ⟨hpre₀, -⟩ := Semantics.rulePlainEx_top hp
  obtain ⟨hRf, hRv⟩ := ruleRight_keysEx hs hp
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let n := r.vars.length
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let P : Nat → Prop := fun i => i < n ∧ i ∉ r.exs
  have hltL : ∀ i ∈ varOccs r.lhs, P i := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hreqP : ∀ t, r.req = some t → ∀ i ∈ varOccs t, P i := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2
      (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hpat : PatOK c P r.lhs := (patOK_of_sorted h hlhs).monoOpen hltL
  have hreqT : ∀ t, r.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h fns_headsOK (hreqs t ht)).monoOpen (hreqP t ht)
  -- the keys of the parts
  have hreqK : ∀ {k : KoreAML.VarKey} {p : Kore.Pattern}, k ∈ KoreAML.freeOf [] p → k ∈ KoreAML.varsOf p →
      k ∈ KoreAML.freeOf [] (reqPat C (some p)) ∧ k ∈ KoreAML.varsOf (reqPat C (some p)) := fun hf hv => by
    simp only [reqPat]
    rw [KoreAML.freeOf, KoreAML.varsOf]
    exact ⟨List.mem_append_left _ hf, List.mem_append_left _ (List.mem_append_right _ hv)⟩
  have hceilK : ∀ {k : KoreAML.VarKey}, (k ∈ KoreAML.freeOf [] (ruleRight c r) →
      k ∈ KoreAML.freeOf [] (.ceil C C (ruleRight c r))) ∧
      (k ∈ KoreAML.varsOf (ruleRight c r) → k ∈ KoreAML.varsOf (.ceil C C (ruleRight c r))) :=
    ⟨fun hk => by rw [KoreAML.freeOf]; exact hk,
     fun hk => by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk⟩
  have hkeys : ∀ {ps : List Kore.Pattern},
      Term.kore c vs r.lhs ∈ ps → reqPat C (r.req.map (Term.kore c vs)) ∈ ps → .ceil C C (ruleRight c r) ∈ ps →
      (∀ i < n, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps)) ∧
      (∀ i < n, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) := by
    intro ps h1 h2 h3
    have hpart : ∀ i < n, (i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) ∧
        canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps) := by
      intro i hi
      by_cases hx : i ∈ r.exs
      · exact ⟨fun h' => absurd hx h', varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inl hx)))⟩
      rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
      · exact ⟨fun _ => freeOf_and_memOpen h1 (kore_freeOf c vs r.lhs hL),
          varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)⟩
      · rw [ht] at h2
        obtain ⟨hf, hv⟩ := hreqK (kore_freeOf c vs t hit) (varsOf_kore c vs t hit)
        exact ⟨fun _ => freeOf_and_memOpen h2 hf, varsOf_and_mem h2 hv⟩
      · exact ⟨fun _ => freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inl hR))),
          varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inl hR))))⟩
      · exact ⟨fun _ => freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr ⟨t, ht, hit⟩))),
          varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr ⟨t, ht, hit⟩))))⟩
    exact ⟨fun i hi => (hpart i hi).2, fun i hi hx => (hpart i hi).1 hx⟩
  -- the parts of the left side, each read
  have hreadL : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst)
      (x : GroundTerm), (∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret (stdI_T c T) e (.val x) ↔ PatVal c σ r.lhs x) := by
    intro T tbl e σ x hvar
    rw [AtT.tr_pat h hvar hpat]
    constructor
    · rintro ⟨v, hv, he⟩; cases he; exact hv
    · intro hv; exact ⟨x, hv, rfl⟩
  have hreadCeil : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst)
      (x : GroundTerm), (∀ i < n, canonKey c r.vars i ∈ tbl) → c.sortOf x = some topCellSort →
      (∀ i < n, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0)) →
      (∀ i < n, i ∉ r.exs → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (.ceil C C (ruleRight c r))).interpret (stdI_T c T) e (.val x) ↔
        ∃ σ' y, (∀ i < n, i ∉ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
          EvalTerm c σ' r.rhs (some y) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true)))) := by
    intro T tbl e σ x htk hx hσ hvar
    have hrd := ruleRight_read_T h hs hp htk hσ hvar
    rw [KoreAML.tr, KoreAML.interp_sCeil AtT.defOK_std AtT.sat_ceilDef (srtOf_top_den_T h e)
      (srtOf_top_den_T h e) top_isSort_T top_isSort_T (fun a ha => by
        obtain ⟨σ', y, -, hσ', hy, -, rfl⟩ := (hrd a).mp ha
        exact (AtT.inh_srt _ _).mpr (rhs_sorted_open h hs hσ' hy))]
    constructor
    · rintro ⟨⟨a, ha⟩, -⟩
      obtain ⟨σ', y, hag, hσ', hy, hens, -⟩ := (hrd a).mp ha
      exact ⟨σ', y, hag, hσ', hy, hens⟩
    · rintro ⟨σ', y, hag, hσ', hy, hens⟩
      exact ⟨⟨.val y, (hrd _).mpr ⟨σ', y, hag, hσ', hy, hens, rfl⟩⟩, (AtT.inh_srt topCellSort (.val x)).mpr hx⟩
  have hreadN : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem)
      (x : GroundTerm), (∀ k ∈ KoreAML.varsOf (.not C (anyOfC C comps)), k ∈ tbl) → c.sortOf x = some topCellSort →
      ((KoreAML.tr ⟨tbl, []⟩ (.not C (anyOfC C comps))).interpret (stdI_T c T) e (.val x) ↔
        ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) := by
    intro T tbl e x hk hx
    have happ : ∀ r' ∈ c.rules, r'.prio < r.prio →
        ((KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret (stdI_T c T) e (.val x) ↔
          RuleApplies c r' x) := by
      intro r' hr' hp'
      obtain ⟨hs', hpo'⟩ := hrules r' hr'
      have hφ : applies c r' (canonRulePres r') ∈ comps :=
        List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hp'⟩, rfl⟩
      refine applies_iff_T h hs' hpo' (fun i hi hil => hk _ ?_) e hx
      rw [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC hφ
        (varsOf_appliesOpen (Semantics.rulePlainEx_top hpo').1 hi hil))
    rw [KoreAML.tr, KoreAML.interp_sNot]
    constructor
    · rintro ⟨hnc, -⟩ r' hr' hp' hna
      have hφ : applies c r' (canonRulePres r') ∈ comps :=
        List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hp'⟩, rfl⟩
      refine hnc ?_
      have key : ∀ (cs : List Kore.Pattern), applies c r' (canonRulePres r') ∈ cs →
          (KoreAML.tr ⟨tbl, []⟩ (anyOfC C cs)).interpret (stdI_T c T) e (.val x) := by
        intro cs hcs
        induction cs with
        | nil => exact absurd hcs List.not_mem_nil
        | cons φ cs ih =>
          rw [anyOfC, KoreAML.tr]
          simp only [KoreAML.trOrList]
          rw [KoreAML.interp_sOr]
          refine ⟨KoreAML.interp_inhOf_of (srtOf_top_den_T h e) |>.mpr
            ((AtT.inh_srt topCellSort (.val x)).mpr hx), ?_⟩
          rcases List.mem_cons.mp hcs with rfl | hcs
          · exact Or.inl ((happ r' hr' hp').mpr hna)
          · exact Or.inr (ih hcs)
      exact key comps hφ
    · intro hprio
      refine ⟨anyOfC_empty AtT.defOK_std (top_free _) _ (fun φ hφ hφm => ?_),
        KoreAML.interp_inhOf_of (srtOf_top_den_T h e) |>.mpr ((AtT.inh_srt topCellSort (.val x)).mpr hx)⟩
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hr'm, hp'⟩ := List.mem_filter.mp hr'
      exact hprio r' hr'm (by simpa using hp') ((happ r' hr'm (by simpa using hp')).mp hφm)
  have hvarP : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst),
      (∀ i < n, i ∉ r.exs → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v :=
    fun _ _ _ _ hvar i hi => hvar i hi.1 hi.2
  by_cases hce : comps.isEmpty
  · obtain ⟨hKv, hKf⟩ := hkeys (ps := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .ceil C C (ruleRight c r)]) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .ceil C C (ruleRight c r)],
      by rw [prioRuleK_preTop hpre₀]; dsimp only; rw [if_pos hce], hKv, hKf, ?_⟩
    intro T tbl e σ x hkL hx hσ hvar
    have hnone : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x := fun r' hr' hp' => by
      have hne := List.isEmpty_iff.mp hce
      rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hne
      exact absurd (by simpa using hp') (hne r' hr')
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd, hreadL T tbl e σ x (hvarP T tbl e σ hvar),
      reqRead_T h (hvarP T tbl e σ hvar) r.req hreqT hx,
      hreadCeil T tbl e σ x (fun i hi => hkL _ (hKv i hi)) hx hσ hvar]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun r' hr' hp' => hnone r' hr' hp', h3⟩
    · rintro ⟨h1, h2, -, h3⟩; exact ⟨h1, h2, h3⟩
  · obtain ⟨hKv, hKf⟩ := hkeys (ps := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .not C (anyOfC C comps), .ceil C C (ruleRight c r)]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .not C (anyOfC C comps),
      .ceil C C (ruleRight c r)], by rw [prioRuleK_preTop hpre₀]; dsimp only; rw [if_neg hce], hKv, hKf, ?_⟩
    intro T tbl e σ x hkL hx hσ hvar
    have hkN : ∀ k ∈ KoreAML.varsOf (.not C (anyOfC C comps)), k ∈ tbl := fun k hk =>
      hkL k (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hk)
    rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd,
      hreadL T tbl e σ x (hvarP T tbl e σ hvar), reqRead_T h (hvarP T tbl e σ hvar) r.req hreqT hx,
      hreadN T tbl e x hkN hx, hreadCeil T tbl e σ x (fun i hi => hkL _ (hKv i hi)) hx hσ hvar]

/-- **A rule's axiom holds in the value model at T**, for a rule with `ruleSorted` and
`rulePlainEx`, not asked to be one of the definition's, among rules with those facts: where every
`StepMAt` instance of the rule is in T if it has no existential variable (`hall`), and where it has
some, some instance that differs from it at ē only is (`hsome`). The guards give every variable but
ē a value; where the left part holds, `⌈∃ē. (rhs ∧ ens)⌉` gives ē values, hence a `StepMAt`
instance, and T a successor in the right side. -/
theorem sat_rule_T (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) (T : GroundTerm → GroundTerm → Prop)
    (hall : ∀ σ x y, StepMAt c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ σ x y, StepMAt c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepMAt c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat := by
  have hn := h.namesK
  have hnum := rule_vars_numEx h hs hp
  obtain ⟨L, hP, hLv, hLf, hLread⟩ := rule_premise_T h hrules hs hp
  let C := srtOf c topCellSort
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hsortP : KoreAML.sortOf [] (prioRuleK c r) = some C := by rw [hP]; rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  let tbl : KoreAML.VarTable := KoreAML.tableOf [] (prioRuleK c r)
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    rw [hP, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have htk : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hLv i hi)
  -- the guards give each variable but the existential ones a value of its sort
  have hin : ∀ i < r.vars.length, i ∉ r.exs →
      InSort c (r.vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c r.vars i))) := by
    intro i hi hx
    have hk : canonKey c r.vars i ∈ ((([] : List Kore.SortVar).map KoreAML.sortVarKey) ++
        KoreAML.freeOf [] (prioRuleK c r)).eraseDups := by
      refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
      rw [hP, KoreAML.freeOf]
      exact List.mem_append_left _ (hLf i hi hx)
    have hg := AtT.conjList_elim hgs _ (List.mem_map.mpr ⟨_, hk, rfl⟩)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar AtT.defOK_std, trSort_srt, ← hkk] at hg
    exact (AtT.inhOf_sort hn (hnum i hi) e _).mp hg
  let σ₀ := substE c tbl r.vars e
  have hσ₀ : ∀ i < r.vars.length, i ∉ r.exs →
      ∃ v, σ₀.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) := fun i hi hx => by
    obtain ⟨v, he, hsv⟩ := inSort_val (hin i hi hx)
    exact ⟨v, by rw [substE_lookup hi, he]; rfl, hsv⟩
  have hvar₀ : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ₀.lookup i = some v ∧ m = .val v := fun i hi hx m => by
    obtain ⟨v, he, -⟩ := inSort_val (hin i hi hx)
    rw [AtT.var_read, substE_lookup hi]
    show m = e.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [he]
    simp [toVal]
  have hPtr : ∀ tb, KoreAML.tr ⟨tb, []⟩ (prioRuleK c r) =
      KoreAML.sRewrites (KoreAML.trSort tb C) (KoreAML.tr ⟨tb, []⟩ L) (KoreAML.tr ⟨tb, []⟩ (ruleRight c r)) :=
    fun tb => by rw [hP, KoreAML.tr]
  rw [KoreAML.interp_equal AtT.defOK_std]
  intro a
  rw [hPtr]
  unfold KoreAML.sRewrites
  rw [KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hL => ?_⟩
    rw [KoreAML.interp_inhOf_of (srtOf_top_den_T h e), AtT.inh_srt] at ha
    obtain ⟨x, rfl, hx⟩ := inSort_val ha
    obtain ⟨-, -, -, σ', y, hag, hσ', hy, hens⟩ := (hLread T tbl e σ₀ x hvarsL hx hσ₀ hvar₀).mp hL
    -- the left part read again under σ', which agrees with σ₀ off the existential variables
    have hσ'n : ∀ i < r.vars.length, i ∉ r.exs →
        ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) := fun i hi hx' => by
      rw [hag i hi hx']; exact hσ₀ i hi hx'
    have hvar' : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
        (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
          ∃ v, σ'.lookup i = some v ∧ m = .val v := fun i hi hx' m => by
      rw [hag i hi hx']; exact hvar₀ i hi hx' m
    obtain ⟨hmatch, hreq, hprio, -⟩ := (hLread T tbl e σ' x hvarsL hx hσ'n hvar').mp hL
    have hst : StepMAt c r σ' x y := ⟨hσ', hmatch, hreq, (Semantics.rulePlainEx_top hp).1 ▸ .top, hy, hens,
      (Semantics.rulePlainEx_top hp).2 ▸ .top, hprio⟩
    obtain ⟨y', σ'', hag', hst', hT⟩ : ∃ y' σ'', (∀ i, ¬ i ∈ r.exs → σ''.lookup i = σ'.lookup i) ∧
        StepMAt c r σ'' x y' ∧ T x y' := by
      by_cases hex : r.exs = []
      · exact ⟨y, σ', fun _ _ => rfl, hst, hall σ' x y hst hex⟩
      · exact hsome σ' x y hst hex
    obtain ⟨hσ'', -, -, -, hy', hens', -, -⟩ := hst'
    rw [AtT.sNext_iff]
    refine ⟨y', ?_, hx, rhs_sorted_open h hs hσ'' hy', hT⟩
    exact (ruleRight_read_T h hs hp htk hσ₀ hvar₀ _).mpr
      ⟨σ'', y', fun i hi hx' => (hag' i hx').trans (hag i hi hx'), hσ'', hy', hens', rfl⟩

/-- **The rules' axioms hold in the value model at T**, for a definition whose rules have
`ruleSorted` and `rulePlainEx`, taken per rule: where every `StepMBy` instance of a rule without
existential variables is in T (`hall`), and for a rule with existential variables, some instance
that differs from a given one at ē only (`hsome`). -/
theorem satRulesGoal_T (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hall : ∀ r σ x y, StepMBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepMBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepMBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP ΓRules c := by
  refine AtT.sat_itemsPremises c fun it hit => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hit
  refine sat_rule_T h hrules (hrules r hr).1 (hrules r hr).2 T
    (fun σ x y hb hex => hall r σ x y ⟨hr, hb⟩ hex) (fun σ x y hb hex => ?_)
  obtain ⟨y', σ', hag, ⟨-, hb'⟩, hT⟩ := hsome r σ x y ⟨hr, hb⟩ hex
  exact ⟨y', σ', hag, hb', hT⟩

end Model

end Faithful

end KCore
