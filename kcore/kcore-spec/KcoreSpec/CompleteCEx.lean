/-
  KCore. CompletePP.lean's `step_successor_pp` and `successor_split_pp` for a semantics `coreOKEx`
  accepts (`*CEx`): each is its `coreOK` counterpart's statement with `coreOKEx` for `coreOK`,
  proved as it is, through FamExCEx.lean's siblings.
-/
import KcoreSpec.FamExCEx

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
variable {H : Sym → Bool}

/-- **The successor a rule's axiom gives, in two cases, for a rule with predicates.** For a rule r
with `ruleSorted` (not asked to be one of the definition's) in a definition whose rules have it, in
a model of `Γc`, at a valuation of r's variables other than the existential ones in their sorts
where x's element is in r's left side, in `⌈req = true⌉`, in `pre` and in no competitor's
`applies`, and b is in r's right side `∃ē. (rhs ∧ ens ∧ post)`, where the step at x is decided
(`StepDecided`): there is an unblocked match σ of r at x, and
- where r's left side binds every variable, b is the element of a configuration y with every premise
  of `StepBy c r σ x y` but the rule's membership, `Holds … pre true` and `Holds … post true`
  included: each predicate has a truth value at σ (`StepDecided`), and in a model of `Γc` it holds
  at an element exactly where that value is `true` (`conj_iff_holdsPPCEx`);
- otherwise b is in `famOpen c r σ`.
No rule of a smaller priority applies at values (`applies_of_values_ppCEx`), so none applies where its
`requires` has a result and its `pre` a truth value at each match (`notApplies_of_not_applies_ppCEx`). -/
theorem successor_split_ppCEx (h : c.coreOKEx = true) (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hdr : (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val) →
      (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
        (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
      (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x.val →
        (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
          (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
          ∃ b, Holds c r.vars.length σ r.post b))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    (hkeysC : ∀ r' ∈ c.rules, r'.prio < r.prio →
      (∀ i < r'.vars.length, i ∈ r'.leftVars → canonKey c r'.vars i ∈ tbl) ∧
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r'.vars) (srtOf c topCellSort) r'.pre), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio →
      ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e (elemOf c I x.val))
    {b : M} (hy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e b) :
    (r.opens = [] ∧ ∃ (y : Config c) (σ : Subst), (r ∈ c.rules → StepBy c r σ x y) ∧ b = elemOf c I y.val) ∨
    (r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ ∀ e', (famOpen c r σ).interpret I e' b) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  have hneg := (neg_of_coreClEx hI (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_coreEx h hI))
  obtain ⟨hlhs, -, hreqs, hensS, hrhss, hexnd, hexs, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hnxP : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi)⟩
  -- inside `∃ē`: a valuation that agrees with e off ē and gives ē elements of their sorts
  rw [Model.ruleRight_eqPP hlt] at hy
  obtain ⟨eR, hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hy
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c vs r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I eR b :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      eR.evalEvar (tbl.ev (canonKey c r.vars i)) = e.evalEvar (tbl.ev (canonKey c r.vars i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
  have hinR : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (eR.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (by rw [canonVars_getD c hi]; rfl)
    · show InS I _ (eR.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoffE i hi hx]; exact hin i hi hx
  have hlR : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I eR (elemOf c I x.val) :=
    (tr_kore_congr r.lhs (fun i hi => (hoffE i (hnxL i hi).1 (hnxL i hi).2).symm) _).mp hl
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c vs)))).interpret I eR (elemOf c I x.val) :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl eR)
  have hpreR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I eR (elemOf c I x.val) :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hnxP i hi).1)
      (fun i hi => (hoffE i (hnxP i hi).1 (hnxP i hi).2).symm) hprem
  let σ := substOf c I tbl vs r.vars eR
  -- the left side binds the variables it holds at values
  obtain ⟨hmatch, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hinR
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hlR
  -- no rule of a smaller priority applies at values: it would apply in the model
  have hnoapp : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val :=
    fun r' hr' hlt' ⟨σ', hσ', hpv', hreq', hpre'⟩ => hcomp r' hr' hlt'
      (applies_of_values_ppCEx h hI hcw (hrules r' hr') (readsConfined_of_pre hr') hσ' hpv' hreq' hpre'
        (hkeysC r' hr' hlt').1 (hkeysC r' hr' hlt').2 e)
  -- so none applies, at values, where its `requires` has a result and its `pre` a truth value
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    intro r' hr' hlt'
    have hun : ∀ r'' ∈ c.rules, r''.prio < r'.prio → ¬ RuleApplies c r'' x.val :=
      fun r'' hr'' hlt'' => hnoapp r'' hr'' (Nat.lt_trans hlt'' hlt')
    exact notApplies_of_not_applies_ppCEx h hI hcw (hrules r' hr') (readsConfined_of_pre hr') (hd r' hr' hun).1
      (hkeysC r' hr' hlt').1 (hkeysC r' hr' hlt').2 e (hcomp r' hr' hlt')
  by_cases hop : r.opens = []
  · -- every variable is held by the left side: the step of `StepDecided`
    left
    refine ⟨hop, ?_⟩
    have hbinds := Rule.lhs_of_opens_nilSplit hop
    obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwitL i (hbinds i hi))
    have hdr' := hdr hnoapp
    obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
    have hSC : ∀ a, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I eR a ↔ a = σC := fun a => by
      unfold srtOf; rw [trSort_srt]; exact hσC1 a
    -- a condition the element satisfies evaluates to `true`, where it has a result
    have htrue : ∀ (q : Option Term) (m : M), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
        (∀ t, q = some t → ∃ v, EvalTerm c σ t v) →
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I eR m →
        ∀ t, q = some t → EvalTerm c σ t (some (bool true)) := by
      intro q m hqs hqv hqm t ht
      obtain ⟨v, hv⟩ := hqv t ht
      by_cases hvt : v = some (bool true)
      · rw [hvt] at hv; exact hv
      · exfalso
        rw [ht] at hqm
        exact reqFalse_empty hIΓ hSC hσC2 hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hqs t ht) hu)
          (evalTerm_den4ClQ hIΓ hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok)
            hneg (HoldsShape.preReadAll_of_coreEx h hI) (clauseExRead_all_of_coreEx h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag (hqs t ht)) _ hqm
    have hreqT := htrue r.req _ hreqs (hdr'.1 σ (hσ.at _) hmatch).1 hreqR
    -- `pre` has a truth value at σ, and x's element is in `pre`: it is `true`
    have hpreT : Holds c r.vars.length σ r.pre true := by
      obtain ⟨bp, hbp⟩ := (hdr'.1 σ (hσ.at _) hmatch).2
      have hbt := (conj_iff_holdsPPCEx h hI hcw hokP hbdP hrcP
        (reads_of_agrees hσ hag fun i hi => ⟨(hnxP i hi).1, hkeys i (hnxP i hi).1⟩)
        hkP (inh_top_PP hIΓ x tbl eR) hbp).mp hpreR
      rw [hbt] at hbp; exact hbp
    have hrest := hdr'.2 σ hσ hmatch hreqT hpreT
    have hensT := htrue r.ens _ hensS hrest.2.1 hensR
    obtain ⟨v, hv⟩ := hrest.1
    have hbR := (evalTerm_den4ClQ hIΓ hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok)
      hneg (HoldsShape.preReadAll_of_coreEx h hI) (clauseExRead_all_of_coreEx h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp hyR
    cases v with
    | none => exact hbR.elim
    | some yv =>
      have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhss rfl
      have hbe : b = elemOf c I yv := ((elemOf_spec hIΓ hyv eR).1 b).mp (((den_closed c yv).interp eR eR b).mp hbR)
      -- `post` has a truth value at σ, and b is in `post`: it is `true`
      have hpostT : Holds c r.vars.length σ r.post true := by
        obtain ⟨bq, hbq⟩ := hrest.2.2
        have hbt := (conj_iff_holdsPPCEx h hI hcw hokQ hbdQ hrcQ
          (reads_of_agrees hσ hag fun i hi =>
            ⟨varOccsCond_lt_twoT r.post hokQ i hi, hkeys i (varOccsCond_lt_twoT r.post hokQ i hi)⟩)
          hkQ (by rw [hbe]; exact inh_top_PP hIΓ ⟨yv, hyv⟩ tbl eR) hbq).mp hpostR
        rw [hbt] at hbq; exact hbq
      exact ⟨⟨yv, hyv⟩, σ, fun hmem => ⟨hmem, hσ, hmatch, hreqT, hpreT, hv, hensT, hpostT, hprio⟩, hbe⟩
  -- an open variable: the valuation, moved to `famOpen`'s variables, satisfies its body at b
  right
  refine ⟨hop, σ, ⟨fun i hi s hsi => ?_, hmatch, hprio⟩, fun e' => ?_⟩
  · have hlti : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
    obtain ⟨h1, -⟩ := pick_spec (hwitL i hi)
    refine ⟨_, substOf_lookup hlti, ?_⟩
    rw [h1, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
  rw [famOpen_eqPP hlt]
  unfold KoreAML.denB
  obtain ⟨hkf, hkfP, hkfQ⟩ := famOpen_keysPP (c := c) (r := r) (σ := σ)
  generalize KoreAML.tableOf [] (famOpenPatPP c r σ) = tf at hkf hkfP hkfQ ⊢
  unfold famOpenPatPP
  let outer := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have houter : ∀ i, i ∈ outer ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by simp [outer]
  have hol : ∀ i ∈ outer, i < r.vars.length := fun i hi => ((houter i).mp hi).1
  have hsortB : ∀ i < r.vars.length,
      ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    rw [canonVars_getD c hi]; rfl
  let e₁ := copyVEx c tbl tf r.vars outer eR e'
  let e₂ := copyVSplit c tbl tf r.vars eR e₁
  have hat₁ : ∀ i < r.vars.length, i ∉ r.exs →
      e₁.evalEvar (tf.ev (keyAt vs i)) = eR.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hx => copyVEx_at hkf hi ((houter i).mpr ⟨hi, hx⟩)
  have hat₂ : ∀ i < r.vars.length, e₂.evalEvar (tf.ev (keyAt vs i)) = eR.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi => copyVSplit_at hkf hi
  have hinC : (KoreAML.inhOf (KoreAML.trSort tf (srtOf c topCellSort))).interpret I e₁ b :=
    reqPat_inhSplit hIΓ hensR tf e₁
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  refine existsAll_intro_at hD _ e' e₁ b (binders_nodupEx hkf hol (List.nodup_range.filter _)) (binders_sortEx hol)
    (fun z hz => copyVEx_off fun i hi his he => hz _ (List.mem_map_of_mem his) he) rfl
    (fun b' hb' n hn => ?_) ?_
  · obtain ⟨i, hio, rfl⟩ := List.mem_map.mp hb'
    have hi := hol i hio
    rw [hsortB i hi] at hn
    rw [← srt_inj hn]
    show InS I _ (e₁.evalEvar (tf.ev (canonKey c r.vars i)))
    rw [copyVEx_at hkf hi hio]
    exact hinR i hi
  rw [interp_and (hne _ _)]
  intro p hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  · -- the left side's variables, fixed to their values under σ
    unfold fixK at hp'
    obtain ⟨i, hiL, hpi⟩ := List.mem_filterMap.mp hp'
    split at hpi
    · rename_i v s g hv hsi hg'
      cases hpi
      have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
      obtain ⟨hgs, hge⟩ := pick_spec (hwitL i hiL)
      rw [substOf_lookup hi] at hg'
      cases hg'
      have hgs' : c.sortOf (pick c I (r.vars.getD i 0) (eR.evalEvar (tbl.ev (keyAt vs i)))) = some s := by
        rw [hgs, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
      refine (fixEq_iff hIΓ (sortOf_numbered_ofCEx hs0 (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h) hgs') hgs'
        b).mpr ⟨hinC, ?_⟩
      have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
        unfold canonKey
        rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
      rw [hvk]
      exact (hat₁ i hi (hnxL i hiL).2).trans hge.symm
    · cases hpi
  · -- the `requires`, from x's element
    rw [List.mem_singleton.mp hp']
    exact reqPat_transferSplit hIΓ (fun t ht i hi => (hat₁ i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqR hinC
  · -- `pre`, from x's element: its free variables are not existential
    exact cond_pred_transfer_topCEx h hIΓ hokP tf e₁ _ b (fun k hk => hkfP k hk)
      (fun i hi => ⟨hkf i (hnxP i hi).1, by
        show InS I _ (e₁.evalEvar (tf.ev (keyAt vs i)))
        rw [hat₁ i (hnxP i hi).1 (hnxP i hi).2]; exact hinR i (hnxP i hi).1⟩)
      (inh_top_PP hIΓ x tf e₁) hinC (conj_twoTPP hD hokP (fun k hk => ⟨hkP k hk, hkfP k hk⟩)
      (fun i hi => ⟨hkeys i (hnxP i hi).1, hkf i (hnxP i hi).1, (hat₁ i (hnxP i hi).1 (hnxP i hi).2).symm⟩)
      hpreR) p hp'
  · -- inside `∃ē`, the existential variables at their elements under the binders
    rw [List.mem_singleton.mp hp']
    refine existsAll_intro_at hD _ e₁ e₂ b (binders_nodupEx hkf hlt hexnd) (binders_sortEx hlt) (fun z hz => ?_) rfl
      (fun b' hb' n hn => ?_) ?_
    · by_cases hk : ∃ i < r.vars.length, z = tf.ev (canonKey c r.vars i)
      · obtain ⟨i, hi, rfl⟩ := hk
        have hx : i ∉ r.exs := fun hx => hz _ (List.mem_map_of_mem hx) rfl
        exact (hat₂ i hi).trans (hat₁ i hi hx).symm
      · exact copyVSplit_off fun i hi he => hk ⟨i, hi, he⟩
    · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb'
      have hi := hlt i hix
      rw [hsortB i hi] at hn
      rw [← srt_inj hn]
      show InS I _ (e₂.evalEvar (tf.ev (keyAt vs i)))
      rw [hat₂ i hi]
      exact hinR i hi
    · unfold Model.ruleRightBodyPP
      rw [interp_and (by simp)]
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact (tr_kore_congr r.rhs (fun i hi => (hat₂ i (varOccs_lt r.rhs hrhss i hi)).symm) b).mp hyR
        · exact reqPat_transferSplit hIΓ (fun t ht i hi => (hat₂ i (varOccs_lt t (hensS t ht) i hi)).symm) hensR
            (reqPat_inhSplit hIΓ hensR tf e₂)
      · exact conj_twoTPP hD hokQ (fun k hk => ⟨hkQ k hk, hkfQ k hk⟩)
          (fun i hi => ⟨hkeys i (varOccsCond_lt_twoT r.post hokQ i hi), hkf i (varOccsCond_lt_twoT r.post hokQ i hi),
            (hat₂ i (varOccsCond_lt_twoT r.post hokQ i hi)).symm⟩) hpostR q hq

/-- **A successor is a step's or an open family's**, for rules with predicates:
`step_successor_axiomPP` then `successor_split_ppCEx`, a binder in a predicate of a rule of the
definition giving `readsConfined`. -/
theorem step_successor_ppCEx (h : c.coreOKEx = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧
      ((∃ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] ∧ StepBy c r σ x y ∧ b = elemOf c I y.val) ∨
       (∃ r ∈ c.rules, r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ (famOpen c r σ).interpret I e b)) := by
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkP, hkQ, hkeysC, hin, hl, hreq, hprem, hcomp, hy⟩ :=
    step_successor_axiomPP hrules x hI e ψ hs
  refine ⟨b, hb, ?_⟩
  rcases successor_split_ppCEx h hrules x hd (fun φ hφ => hI φ (Or.inl hφ)) hcw (hrules r hr)
      (readsConfined_of_pre hr) (readsConfined_of_post hr) (hd r hr) hkeys hkP hkQ hkeysC hin hl
      hreq hprem hcomp hy with
    ⟨hop, y', σ, hst, hbe⟩ | ⟨hop, σ, hu, hfam⟩
  · exact Or.inl ⟨y', r, σ, hop, hst hr, hbe⟩
  · exact Or.inr ⟨r, hr, hop, σ, hu, hfam e⟩

end

end Faithful

end KCore
