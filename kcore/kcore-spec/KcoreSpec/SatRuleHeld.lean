/-
  KCore. The value model's rule axioms, for rules with `rulePlainHeldH`.

  `ruleRight_read_held`, `rule_premise_held`, `sat_rule_held` and `satRulesGoal_held` are
  `ruleRight_read_pp`, `rule_premise_pp`, `sat_rule_pp` and `satRulesGoal_pp` with the per-rule
  fact `rulePlainHeldH c H` in place of `rulePlainPP`. The proofs read `ruleSorted` only: the
  conjunct is carried, so H is any set of symbols.
-/
import KcoreSpec.SatRulePP
import KcoreSpec.StepValuesHeld

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

variable {H : Sym → Bool}

/-- **A rule's right side read at T.** Under a valuation that reads each variable of the rule but
the existential ones as its value under σ, of its sort, an element is in `∃ē. (rhs ∧ ens ∧ post)`
exactly where it is the value of the right side under a well-sorted σ' that agrees with σ off ē,
with a true `ensures` and `post` true in the value model (`TrueV`). The keys of the rule's
variables and of `post`'s pattern are in the table. -/
theorem ruleRight_read_held (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainHeldH H r = true) {T : GroundTerm → GroundTerm → Prop} {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation Elem} {σ : Subst}
    (hσ : ∀ i < r.vars.length, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0))
    (hvar : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret (stdI_T c T) e m ↔
      ∃ σ' y, (∀ i < r.vars.length, i ∉ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
        EvalTerm c σ' r.rhs (some y) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
        TrueV c r.vars.length σ' r.post ∧ m = .val y := by
  -- `rulePlainHeldH` is not read here: the statement keeps it as ruled for the rule-case lemmas
  have _hp := hp
  have hn := h.namesK
  obtain ⟨-, -, -, hensS, hrhss, hnd, hexs, -, hokQ, -, hbdQ⟩ := ruleSorted_partsPP hs
  have hnum := rule_vars_numCN h hs
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
  have hPk : ∀ i, i < n → i < r.vars.length ∧ canonKey c r.vars i ∈ tbl := fun i hi => ⟨hi, hkeys i hi⟩
  -- `post` in the value model, under a valuation reading every variable as σ'
  have hpost : ∀ {e' : Valuation Elem} {σ' : Subst} {y : GroundTerm}, c.WellSorted r.vars σ' →
      c.sortOf y = some topCellSort →
      (∀ i, i < n → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ'.lookup i = some v ∧ m = .val v) →
      ((∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post,
        (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e' (.val y)) ↔ TrueV c n σ' r.post) := by
    intro e' σ' y hσ' hys hvar'
    have hσs : ∀ i, i < n → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) := fun i hi =>
      hσ' i (r.vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    exact preConj_iffPP h hokQ hbdQ (P := (· < n)) (fun _ _ hlt => hlt) (readsT_of_hvar hPk hσs hvar') hkQ hys
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
  rw [ruleRight_eqPP hlt]
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
    unfold ruleRightBodyPP at hbody
    obtain ⟨hb1, hb2, hb3⟩ := (interp_bodyPP _ _ _ _ _ _).mp hbody
    obtain ⟨y, hy, rfl⟩ := (AtT.tr_term h hvar' hrhsOK m).mp hb1
    have hys := rhs_sorted_open h hs hσ' hy
    have hens := (reqRead_T h hvar' r.ens hensOK hys).mp hb2
    refine ⟨substE c tbl r.vars e', y, fun i hi hx => ?_, hσ', hy, hens, (hpost hσ' hys hvar').mp hb3, rfl⟩
    obtain ⟨v, hv, -, he⟩ := hval i hi hx
    rw [substE_lookup hi, hoffK i hi hx, he, hv]
    rfl
  · rintro ⟨σ', y, hag, hσ', hy, hens, hpo, rfl⟩
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
    · unfold ruleRightBodyPP
      exact (interp_bodyPP _ _ _ _ _ _).mpr ⟨(AtT.tr_term h hvar' hrhsOK _).mpr ⟨y, hy, rfl⟩,
        (reqRead_T h hvar' r.ens hensOK hys).mpr hens, (hpost hσ' hys hvar').mpr hpo⟩

/-- **The left part of a rule's axiom, read at T**, for a well-sorted rule with `rulePlainHeldH` (not
asked to be one of the definition's), among rules with those facts. The axiom is `\rewrites(L,
∃ē. (rhs ∧ ens ∧ post))`; each variable of the rule is a variable of L and each but ē free in it.
Under a valuation that reads the variables but ē as their values under σ, with the keys of L in the
table, a configuration x is in L exactly where the left side matches x under σ, the `requires`
holds, `pre` is true in the value model, no rule of a smaller priority applies in the value model
(`RuleAppliesV`), and some σ' that agrees with σ off ē is well sorted, evaluates the right side to a
value and makes the `ensures` and `post` true. -/
theorem rule_premise_held (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainHeldH H r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true) :
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
          TrueV c r.vars.length σ r.pre ∧
          (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleAppliesV c r' x) ∧
          ∃ σ' y, (∀ i < r.vars.length, i ∉ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
            EvalTerm c σ' r.rhs (some y) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
            TrueV c r.vars.length σ' r.post) := by
  -- `rulePlainHeldH` is not read here: the statement keeps it as ruled for the rule-case lemmas
  have _hp := hp
  obtain ⟨hlhs, hocc, hreqs, -, -, -, hexs, hokP, -, hbdP, -⟩ := ruleSorted_partsPP hs
  obtain ⟨hRf, hRv⟩ := ruleRight_keysPP (c := c) hs
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let n := r.vars.length
  let P : Nat → Prop := fun i => i < n ∧ i ∉ r.exs
  have hltL : ∀ i ∈ varOccs r.lhs, P i := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hreqP : ∀ t, r.req = some t → ∀ i ∈ varOccs t, P i := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2
      (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hpreP : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length → P i := fun i hi hlt =>
    ⟨hlt, fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi)⟩
  have hpat : PatOK c P r.lhs := (patOK_of_sorted h (h.lhs_nf hr hlhs)).monoOpen hltL
  have hreqT : ∀ t, r.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h fns_headsOK (hreqs t ht)).monoOpen (hreqP t ht)
  -- the keys of the parts
  have hreqK : ∀ {k : KoreAML.VarKey} {p : Kore.Pattern}, k ∈ KoreAML.freeOf [] p → k ∈ KoreAML.varsOf p →
      k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (some p)) ∧
        k ∈ KoreAML.varsOf (reqPat (srtOf c topCellSort) (some p)) := fun hf hv => by
    simp only [reqPat]
    rw [KoreAML.freeOf, KoreAML.varsOf]
    exact ⟨List.mem_append_left _ hf, List.mem_append_left _ (List.mem_append_right _ hv)⟩
  have hceilK : ∀ {k : KoreAML.VarKey}, (k ∈ KoreAML.freeOf [] (ruleRight c r) →
      k ∈ KoreAML.freeOf [] (.ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r))) ∧
      (k ∈ KoreAML.varsOf (ruleRight c r) →
        k ∈ KoreAML.varsOf (.ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r))) :=
    ⟨fun hk => by rw [KoreAML.freeOf]; exact hk,
     fun hk => by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk⟩
  have hkeys : ∀ {ps : List Kore.Pattern},
      Term.kore c (canonVars c r.vars) r.lhs ∈ ps →
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))) ∈ ps →
      (∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre, φ ∈ ps) →
      .ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r) ∈ ps →
      (∀ i < n, canonKey c r.vars i ∈ KoreAML.varsOf (.and (srtOf c topCellSort) ps)) ∧
      (∀ i < n, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and (srtOf c topCellSort) ps)) := by
    intro ps h1 h2 hpre h3
    have hpart : ∀ i < n, (i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and (srtOf c topCellSort) ps)) ∧
        canonKey c r.vars i ∈ KoreAML.varsOf (.and (srtOf c topCellSort) ps) := by
      intro i hi
      by_cases hx : i ∈ r.exs
      · exact ⟨fun h' => absurd hx h', varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inl hx)))⟩
      rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hP | hR | ⟨t, ht, hit⟩ | hPo
      · exact ⟨fun _ => freeOf_and_memOpen h1 (kore_freeOf c _ r.lhs hL),
          varsOf_and_mem h1 (varsOf_kore c _ r.lhs hL)⟩
      · rw [ht] at h2
        obtain ⟨hf, hv⟩ := hreqK (kore_freeOf c _ t hit) (varsOf_kore c _ t hit)
        exact ⟨fun _ => freeOf_and_memOpen h2 hf, varsOf_and_mem h2 hv⟩
      · have hT : r.pre.isTop = false := by
          cases hq : r.pre
          case top => rw [hq] at hP; simp [varOccsCond] at hP
          all_goals rfl
        have hmem := hpre (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre) (by simp [Cond.conj, hT])
        obtain ⟨k1, k2⟩ := condKore_keys (bound := []) (srtOf c topCellSort) r.pre hi hP rfl
        exact ⟨fun _ => freeOf_and_memOpen hmem k1, varsOf_and_mem hmem k2⟩
      · exact ⟨fun _ => freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inl hR))),
          varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inl hR))))⟩
      · exact ⟨fun _ => freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr (Or.inl ⟨t, ht, hit⟩)))),
          varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr (Or.inl ⟨t, ht, hit⟩)))))⟩
      · exact ⟨fun _ => freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr (Or.inr hPo)))),
          varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr (Or.inr hPo)))))⟩
    exact ⟨fun i hi => (hpart i hi).2, fun i hi hx => (hpart i hi).1 hx⟩
  -- the parts of the left side, each read
  have hreadL : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst)
      (x : GroundTerm), (∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret
        (stdI_T c T) e m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret (stdI_T c T) e (.val x) ↔
        PatVal c σ r.lhs x) := by
    intro T tbl e σ x hvar
    rw [AtT.tr_pat h hvar hpat]
    constructor
    · rintro ⟨v, hv, he⟩; cases he; exact hv
    · intro hv; exact ⟨x, hv, rfl⟩
  have hreadCeil : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst)
      (x : GroundTerm), (∀ i < n, canonKey c r.vars i ∈ tbl) → (∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈ tbl) →
      c.sortOf x = some topCellSort →
      (∀ i < n, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0)) →
      (∀ i < n, i ∉ r.exs → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret
        (stdI_T c T) e m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (.ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r))).interpret
          (stdI_T c T) e (.val x) ↔
        ∃ σ' y, (∀ i < n, i ∉ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
          EvalTerm c σ' r.rhs (some y) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
          TrueV c r.vars.length σ' r.post) := by
    intro T tbl e σ x htk hkR hx hσ hvar
    have hrd := ruleRight_read_held h hs hp htk (fun k hk => hkR k (varsOf_post_ruleRight hs hk)) hσ hvar
    rw [KoreAML.tr, KoreAML.interp_sCeil AtT.defOK_std AtT.sat_ceilDef (srtOf_top_den_T h e)
      (srtOf_top_den_T h e) top_isSort_T top_isSort_T (fun a ha => by
        obtain ⟨σ', y, -, hσ', hy, -, -, rfl⟩ := (hrd a).mp ha
        exact (AtT.inh_srt _ _).mpr (rhs_sorted_open h hs hσ' hy))]
    constructor
    · rintro ⟨⟨a, ha⟩, -⟩
      obtain ⟨σ', y, hag, hσ', hy, hens, hpo, -⟩ := (hrd a).mp ha
      exact ⟨σ', y, hag, hσ', hy, hens, hpo⟩
    · rintro ⟨σ', y, hag, hσ', hy, hens, hpo⟩
      exact ⟨⟨.val y, (hrd _).mpr ⟨σ', y, hag, hσ', hy, hens, hpo, rfl⟩⟩,
        (AtT.inh_srt topCellSort (.val x)).mpr hx⟩
  have hreadN : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem)
      (x : GroundTerm), (∀ k ∈ KoreAML.varsOf (.not (srtOf c topCellSort) (anyOfC (srtOf c topCellSort) comps)),
        k ∈ tbl) → c.sortOf x = some topCellSort →
      ((KoreAML.tr ⟨tbl, []⟩ (.not (srtOf c topCellSort) (anyOfC (srtOf c topCellSort) comps))).interpret
          (stdI_T c T) e (.val x) ↔
        ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleAppliesV c r' x) := by
    intro T tbl e x hk hx
    have happ : ∀ r' ∈ c.rules, r'.prio < r.prio →
        ((KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret (stdI_T c T) e (.val x) ↔
          RuleAppliesV c r' x) := by
      intro r' hr' hp'
      obtain ⟨hs', -⟩ := hrules r' hr'
      have hφ : applies c r' (canonRulePres r') ∈ comps :=
        List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hp'⟩, rfl⟩
      have hsub : ∀ k ∈ KoreAML.varsOf (applies c r' (canonRulePres r')), k ∈ tbl := fun k hk' => hk _ (by
        rw [KoreAML.varsOf]; exact List.mem_append_right _ (mem_varsOf_anyOfC hφ hk'))
      obtain ⟨hA1, hA2⟩ := varsOf_applies_pp (c := c) r'
      exact applies_iff_T_pp h hs' (fun i hi hil => hsub _ (hA1 i hi hil)) (fun k hk' => hsub _ (hA2 k hk')) e hx
    rw [KoreAML.tr, KoreAML.interp_sNot]
    constructor
    · rintro ⟨hnc, -⟩ r' hr' hp' hna
      have hφ : applies c r' (canonRulePres r') ∈ comps :=
        List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hp'⟩, rfl⟩
      refine hnc ?_
      have key : ∀ (cs : List Kore.Pattern), applies c r' (canonRulePres r') ∈ cs →
          (KoreAML.tr ⟨tbl, []⟩ (anyOfC (srtOf c topCellSort) cs)).interpret (stdI_T c T) e (.val x) := by
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
  -- `pre`, read by its truth in the value model
  have hreadP : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst)
      (x : GroundTerm), (∀ i < n, canonKey c r.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl) →
      c.sortOf x = some topCellSort →
      (∀ i < n, i ∉ r.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0)) →
      (∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret
        (stdI_T c T) e m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
        (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e (.val x)) ↔ TrueV c r.vars.length σ r.pre) := by
    intro T tbl e σ x htk hkP hx hσ hvar
    exact preConj_iffPP h hokP hbdP hpreP
      (readsT_of_hvar (fun i hi => ⟨hi.1, htk i hi.1⟩) (fun i hi => hσ i hi.1 hi.2) hvar) hkP hx
  have hvarP : ∀ (T : GroundTerm → GroundTerm → Prop) (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst),
      (∀ i < n, i ∉ r.exs → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret
        (stdI_T c T) e m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v :=
    fun _ _ _ _ hvar i hi => hvar i hi.1 hi.2
  by_cases hce : comps.isEmpty
  · obtain ⟨hKv, hKf⟩ := hkeys (ps := Term.kore c (canonVars c r.vars) r.lhs ::
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))) ::
      (Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre ++
        [.ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r)]))
      (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (fun φ hφ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hφ))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))))
    refine ⟨.and (srtOf c topCellSort) (Term.kore c (canonVars c r.vars) r.lhs ::
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))) ::
      (Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre ++
        [.ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r)])),
      by unfold prioRuleK; dsimp only; rw [if_pos hce]; simp only [List.cons_append, List.nil_append],
      hKv, hKf, ?_⟩
    intro T tbl e σ x hkL hx hσ hvar
    have hnone : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleAppliesV c r' x := fun r' hr' hp' => by
      have hne := List.isEmpty_iff.mp hce
      rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hne
      exact absurd (by simpa using hp') (hne r' hr')
    have htk : ∀ i < n, canonKey c r.vars i ∈ tbl := fun i hi => hkL _ (hKv i hi)
    have hkR : ∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈ tbl := fun k hk =>
      hkL k (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))) (hceilK.2 hk))
    have hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl :=
      fun k hk => hkL k (varsOf_condConj (fun φ hφ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hφ))) hk)
    rw [interp_andAll]
    simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil, false_implies, implies_true,
      and_true]
    rw [hreadL T tbl e σ x (hvarP T tbl e σ hvar), reqRead_T h (hvarP T tbl e σ hvar) r.req hreqT hx,
      hreadP T tbl e σ x htk hkP hx hσ (hvarP T tbl e σ hvar), hreadCeil T tbl e σ x htk hkR hx hσ hvar]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, hnone, h4⟩
    · rintro ⟨h1, h2, h3, -, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨hKv, hKf⟩ := hkeys (ps := Term.kore c (canonVars c r.vars) r.lhs ::
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))) ::
      (Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre ++
        [.not (srtOf c topCellSort) (anyOfC (srtOf c topCellSort) comps),
          .ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r)]))
      (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (fun φ hφ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hφ))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
    refine ⟨.and (srtOf c topCellSort) (Term.kore c (canonVars c r.vars) r.lhs ::
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))) ::
      (Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre ++
        [.not (srtOf c topCellSort) (anyOfC (srtOf c topCellSort) comps),
          .ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r)])),
      by unfold prioRuleK; dsimp only; rw [if_neg hce]; simp only [List.cons_append, List.nil_append]; rfl,
      hKv, hKf, ?_⟩
    intro T tbl e σ x hkL hx hσ hvar
    have htk : ∀ i < n, canonKey c r.vars i ∈ tbl := fun i hi => hkL _ (hKv i hi)
    have hkR : ∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈ tbl := fun k hk =>
      hkL k (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))) (hceilK.2 hk))
    have hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl :=
      fun k hk => hkL k (varsOf_condConj (fun φ hφ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hφ))) hk)
    have hkN : ∀ k ∈ KoreAML.varsOf (.not (srtOf c topCellSort) (anyOfC (srtOf c topCellSort) comps)), k ∈ tbl :=
      fun k hk => hkL k (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..)))) hk)
    rw [interp_andAll]
    simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil, false_implies, implies_true,
      and_true]
    rw [hreadL T tbl e σ x (hvarP T tbl e σ hvar), reqRead_T h (hvarP T tbl e σ hvar) r.req hreqT hx,
      hreadP T tbl e σ x htk hkP hx hσ (hvarP T tbl e σ hvar), hreadN T tbl e x hkN hx,
      hreadCeil T tbl e σ x htk hkR hx hσ hvar]

/-- **A rule's axiom holds in the value model at T**, for a well-sorted rule with `rulePlainHeldH`,
not asked to be one of the definition's, among rules with those facts: where every `StepVAt`
instance of the rule is in T if it has no existential variable (`hall`), and where it has some, some
instance that differs from it at ē only is (`hsome`). No truth value of `pre`, `post` or a
competitor's `pre` is asked for. -/
theorem sat_rule_held (h : HypModelCore c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainHeldH H r' = true)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true) (T : GroundTerm → GroundTerm → Prop)
    (hall : ∀ σ x y, StepVAt c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ σ x y, StepVAt c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVAt c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat := by
  have hn := h.namesK
  have hnum := rule_vars_numCN h hs
  obtain ⟨L, hP, hLv, hLf, hLread⟩ := rule_premise_held h hrules hs hp
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
  have hvarsR : ∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    rw [hP, KoreAML.varsOf]
    exact List.mem_append_right _ hk
  have htk : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hLv i hi)
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => hvarsR k (varsOf_post_ruleRight hs hk)
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
    obtain ⟨-, -, -, -, σ', y, hag, hσ', hy, hens, hpo⟩ := (hLread T tbl e σ₀ x hvarsL hx hσ₀ hvar₀).mp hL
    -- the left part read again under σ', which agrees with σ₀ off the existential variables
    have hσ'n : ∀ i < r.vars.length, i ∉ r.exs →
        ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) := fun i hi hx' => by
      rw [hag i hi hx']; exact hσ₀ i hi hx'
    have hvar' : ∀ i < r.vars.length, i ∉ r.exs → ∀ m,
        (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret (stdI_T c T) e m ↔
          ∃ v, σ'.lookup i = some v ∧ m = .val v := fun i hi hx' m => by
      rw [hag i hi hx']; exact hvar₀ i hi hx' m
    obtain ⟨hmatch, hreq, hpre, hprio, -⟩ := (hLread T tbl e σ' x hvarsL hx hσ'n hvar').mp hL
    have hst : StepVAt c r σ' x y := ⟨hσ', hmatch, hreq, hpre, hy, hens, hpo, hprio⟩
    obtain ⟨y', σ'', hag', hst', hT⟩ : ∃ y' σ'', (∀ i, ¬ i ∈ r.exs → σ''.lookup i = σ'.lookup i) ∧
        StepVAt c r σ'' x y' ∧ T x y' := by
      by_cases hex : r.exs = []
      · exact ⟨y, σ', fun _ _ => rfl, hst, hall σ' x y hst hex⟩
      · exact hsome σ' x y hst hex
    obtain ⟨hσ'', -, -, -, hy', hens', hpo', -⟩ := hst'
    rw [AtT.sNext_iff]
    refine ⟨y', ?_, hx, rhs_sorted_open h hs hσ'' hy', hT⟩
    exact (ruleRight_read_held h hs hp htk hkQ hσ₀ hvar₀ _).mpr
      ⟨σ'', y', fun i hi hx' => (hag' i hx').trans (hag i hi hx'), hσ'', hy', hens', hpo', rfl⟩

/-- **The rules' axioms hold in the value model at T**, for a definition whose rules are well
sorted with `rulePlainHeldH`, taken per rule: where every `StepVBy` instance of a rule without
existential variables is in T (`hall`), and for a rule with existential variables, some instance
that differs from a given one at ē only (`hsome`). No decidedness hypothesis. -/
theorem satRulesGoal_held (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP ΓRules c := by
  refine AtT.sat_itemsPremises c fun it hit => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hit
  refine sat_rule_held h hrules (hrules r hr).1 (hrules r hr).2 T
    (fun σ x y hb hex => hall r σ x y ⟨hr, hb⟩ hex) (fun σ x y hb hex => ?_)
  obtain ⟨y', σ', hag, ⟨-, hb'⟩, hT⟩ := hsome r σ x y ⟨hr, hb⟩ hex
  exact ⟨y', σ', hag, hb', hT⟩

end Model

end Faithful

end KCore
