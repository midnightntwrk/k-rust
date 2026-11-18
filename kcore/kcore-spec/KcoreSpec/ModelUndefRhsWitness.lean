/-
  KCore. A semantics whose one rule applies at every configuration with an undefined right-hand
  side: a regression test for the premise `⌈rhs⌉` of a rule's axiom (`prioRuleK`).

  Its configuration is `<k> K </k>` with the generated counter, and its one rule is
  `<k> X </k> <generatedCounter> N </generatedCounter> => <k> X </k> <generatedCounter> N /Int 0 </generatedCounter>`.
  The rule's left-hand side matches every configuration, it has no `requires` and no competitor,
  and its right-hand side is undefined (`/Int` by zero), so `Step` gives no step. The rule's axiom
  reads that premise and says nothing there. It satisfies `Hyp` and `HypSound`; the decidable
  facts are kernel decisions.
-/
import KcoreSpec.FaithfulSound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace UndefRhsWitness

open ML

/-- The `k` cell: its sorts `KCell`, `KCellOpt` and symbols `<k>`, `noKCell`, numbered as the
definition's first own sorts and symbols after the predicates of its two own sorts. -/
def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- `<k> X </k> <generatedCounter> N </generatedCounter> => <k> X </k> <generatedCounter> N /Int 0 </generatedCounter>`. -/
def rule : Rule :=
  { vars := [Srt.k, Srt.int]
    lhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]
    req := none
    rhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.app intTDiv [.var 1, .dv Srt.int (.int 0)]]]
    ens := none
    prio := 50 }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [rule] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun fn hfn => ?_, fun fn hfn s hs => ?_⟩
  · exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp names_plain k hk)
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact Option.isNone_iff_eq_none.mp this.1
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

theorem genWf_ok : genWf c = true := by decide +kernel
theorem patHooks_ok : patHooksApart c = true := by decide +kernel
theorem collSorts_ok : collSortsOK c = true := by decide +kernel
theorem colls_ok : collsOK c = true := by decide +kernel
theorem patHeads_ok : patHeadsOK c = true := by decide +kernel

theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, genWf_ok, patHooks_ok, collSorts_ok, colls_ok, patHeads_ok, inferInstance⟩

/-- `c` has no function of its own, so the semantic conditions of `Hyp` hold vacuously. -/
theorem hyp : Hyp c :=
  ⟨okAll, srReady, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, namesNumbered⟩

/-- `<k> . </k> <generatedCounter> 0 </generatedCounter>`. -/
def x0 : GroundTerm := .ctor topLabel [.ctor kIds.label [.ctor dotk []], .ctor counterLabel [int 0]]

theorem x0_sort : c.sortOf x0 = some topCellSort := by decide +kernel

def x : Config c := ⟨x0, x0_sort⟩

def σ : Subst := [(0, .ctor dotk []), (1, int 0)]

theorem hσ : c.WellSorted rule.vars σ := by
  intro i s h
  match i, h with
  | 0, h =>
    cases h
    exact ⟨_, rfl, by decide +kernel⟩
  | 1, h =>
    cases h
    exact ⟨_, rfl, by decide +kernel⟩

theorem hmatch : PatVal c σ rule.lhs x.val :=
  .ctor (by decide +kernel)
    (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil))
      (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil))

/-- `N /Int 0` is undefined, so the counter cell around it and the configuration are. -/
theorem heval : EvalTerm c σ rule.rhs none := by
  have hdiv : EvalTerm c σ (.app intTDiv [.var 1, .dv Srt.int (.int 0)]) none :=
    .hook (rs := [some (int 0), some (int 0)]) (by decide +kernel) (by decide +kernel)
      (.cons .var (.cons .dv .nil)) (fun vs h => by
        cases h; exact (Semantics.hookRes_of_notKey (f := intTDiv) (by decide +kernel) _).trans rfl) (fun h => by cases h)
  have hcnt := EvalTerm.ctor (c := c) (σ := σ) (f := counterLabel) (by decide +kernel) (.cons hdiv .nil)
  have hk := EvalTerm.ctor (c := c) (σ := σ) (f := kIds.label) (by decide +kernel) (.cons (.var (i := 0)) .nil)
  exact EvalTerm.ctor (c := c) (σ := σ) (f := topLabel) (by decide +kernel) (.cons hk (.cons hcnt .nil))

/-! ## Without `⌈rhs⌉`: the rule's axiom as the text states it

The rule's axiom of kompile's text has no conjunct `⌈rhs⌉`: `\rewrites(lhs ∧ ⌈req = true⌉, rhs)`.
`ΓText` is `Γ` with that axiom in place of `prioRuleK`'s. For `c` it has no model (`not_model_text`):
the configuration `x` matches the left-hand side, so it is in `•rhs`, and `rhs` denotes nothing.
`Γ c` itself has a model (`has_model`, ModelHas.lean). -/

/-- A rule's axiom without the premise `⌈rhs ∧ ens⌉`: `\rewrites(lhs ∧ ⌈req = true⌉ ∧ ¬ ⋁ competitors,
rhs ∧ ens)`, `prioRuleK` without its conjunct `rightDef`. -/
def textRuleK (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  if comps.isEmpty then
    .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))])
      (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])
  else .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .not C (anyOfC C comps)])
    (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])

def textRuleItem (c : Semantics) (r : Rule) : KoreAML.Item :=
  KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := textRuleK c r, attributes := [] }⟩

/-- The rules' axioms without `⌈rhs⌉`. -/
def ΓRulesText (c : Semantics) : Premises KoreAML.Sym := KoreAML.itemsPremises (c.rules.map (textRuleItem c))

/-- `Γ` with the rules' axioms read without `⌈rhs⌉` (`ΓRulesText` in place of `ΓRules`). -/
def ΓText (c : Semantics) : Premises KoreAML.Sym :=
  ΓSig c ∪ ΓCons c ∪ ΓDomains c ∪ ΓColls c ∪ ΓFns c ∪ ΓRulesText c ∪ ΓFallback c

theorem rule_mem : rule ∈ c.rules := List.mem_singleton_self _

theorem comps_nil : c.rules.filter (·.prio < rule.prio) = [] := by decide +kernel

theorem textRuleK_eq : textRuleK c rule = .rewrites (srtOf c topCellSort)
    (.and (srtOf c topCellSort) [Term.kore c (canonVars c rule.vars) rule.lhs, reqPat (srtOf c topCellSort) none])
    (.and (srtOf c topCellSort) [Term.kore c (canonVars c rule.vars) rule.rhs, .top (srtOf c topCellSort)]) := by
  unfold textRuleK; dsimp only; rw [comps_nil]; rfl

theorem prioRuleK_eq : prioRuleK c rule = .rewrites (srtOf c topCellSort)
    (.and (srtOf c topCellSort) [Term.kore c (canonVars c rule.vars) rule.lhs, reqPat (srtOf c topCellSort) none,
      .ceil (srtOf c topCellSort) (srtOf c topCellSort)
        (.and (srtOf c topCellSort) [Term.kore c (canonVars c rule.vars) rule.rhs, .top (srtOf c topCellSort)])])
    (.and (srtOf c topCellSort) [Term.kore c (canonVars c rule.vars) rule.rhs, .top (srtOf c topCellSort)]) := by
  unfold prioRuleK; dsimp only; rw [comps_nil]; rfl

theorem table_eq : KoreAML.tableOf [] (prioRuleK c rule) = KoreAML.tableOf [] (textRuleK c rule) := by
  decide +kernel

theorem free_eq : (([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (prioRuleK c rule)).eraseDups =
    (([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (textRuleK c rule)).eraseDups := by
  decide +kernel

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The rule's axiom without `⌈rhs⌉` implies the axiom with it: its premise is weaker. -/
theorem ceil_of_text (hD : KoreAML.DefOK I) (h : I ⊧ᴵ (textRuleItem c rule).pat) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c rule, attributes := [] }⟩).pat := by
  intro e m
  have h1 := h e m
  unfold textRuleItem KoreAML.trAxiom at h1
  unfold KoreAML.trAxiom
  dsimp only at h1 ⊢
  have hs1 : KoreAML.sortOf [] (prioRuleK c rule) = some (srtOf c topCellSort) := by rw [prioRuleK_eq]; rfl
  have hs0 : KoreAML.sortOf [] (textRuleK c rule) = some (srtOf c topCellSort) := by rw [textRuleK_eq]; rfl
  simp only [hs1, hs0] at h1 ⊢
  rw [table_eq, free_eq]
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [KoreAML.interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  generalize KoreAML.tableOf [] (textRuleK c rule) = tb at h3 ⊢
  rw [prioRuleK_eq, KoreAML.tr]
  rw [textRuleK_eq, KoreAML.tr] at h3
  unfold KoreAML.sRewrites at h3 ⊢
  rw [KoreAML.interp_sImp] at h3 ⊢
  refine ⟨fun h' => h'.1, fun ha => ⟨ha, fun hL => (h3.mpr ha).2 ?_⟩⟩
  rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at hL
  rw [tr_and2, KoreAML.interp_sAnd]
  exact ⟨hL.1, hL.2.1⟩

theorem defOK_text (hI : I ⊧ᴵP ΓText c) : KoreAML.DefOK I :=
  KoreAML.defOK_of fun x => hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))

/-- A model of `ΓText c` is a model of `Γ c`. -/
theorem gamma_of_text (hI : I ⊧ᴵP ΓText c) : I ⊧ᴵP Γ c := by
  intro φ hφ
  rcases hφ with ((((((h | h) | h) | h) | h) | h) | h)
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact hI φ (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hit
      obtain rfl : r = rule := List.mem_singleton.mp hr
      exact ceil_of_text (defOK_text hI)
        (hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map.mpr ⟨rule, rule_mem, rfl⟩, rfl⟩))))
    · exact hI _ (Or.inl (Or.inr (Or.inr ⟨x, rfl⟩)))
  · exact hI φ (Or.inr h)

end

theorem heads_plain : (Term.heads rule.rhs ++ (rule.req.map Term.heads).getD []).all
    (fun f => (c.lookupFn f).isNone) = true := by decide +kernel

theorem clauses_plain : c.allFns.all (fun fn => fn.clauses.all fun cl => plainPats c cl.pats &&
    (Term.heads cl.rhs ++ (cl.req.map Term.heads).getD [] ++ (cl.ens.map Term.heads).getD []).all
      (fun f => (c.lookupFn f).isNone)) = true := by
  decide +kernel

theorem stage1 : Stage1 c := by
  refine ⟨fun r hr r' hr' => ?_, fun r hr => ?_, fun fn hfn cl hcl => ?_⟩
  · obtain rfl := List.mem_singleton.mp hr
    obtain rfl := List.mem_singleton.mp hr'
    exact Nat.lt_irrefl _
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨by decide +kernel, fun f hf => ⟨fun fn hfn => ?_, fun o ho => nomatch ho⟩⟩
    have := List.all_eq_true.mp heads_plain f hf
    rw [hfn] at this
    cases this
  · have h := List.all_eq_true.mp (List.all_eq_true.mp clauses_plain fn hfn) cl hcl
    simp only [Bool.and_eq_true] at h
    refine ⟨h.1, fun f hf => ⟨fun fn' hfn' => ?_, fun o ho => nomatch ho⟩⟩
    have := List.all_eq_true.mp h.2 f hf
    rw [hfn'] at this
    cases this

/-- **`ΓText c` has no model**: read without `⌈rhs⌉`, the rule's axiom says that `x`, which its
left-hand side matches, is in `•rhs`, and `rhs` (`N /Int 0`) denotes nothing. -/
theorem not_model_text (hpreTop : c.clausesPreTop = true) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP ΓText c) := by
  intro M _ I hI
  have hΓ := gamma_of_text hI
  have hD := defOK hΓ
  have hy : HypCore c := hyp.core
  have hnn : NamesNumbered c := namesNumbered
  have hs := stage1
  have hsc := sortCtx_of_all hy.1 hy.2.1 (OvlOK.ovlCase inferInstance)
  have hmi := CoherentAll_of hy
  have hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
    decide +kernel
  obtain ⟨hlhs, -, hrhss⟩ := rule_ctx hy.1 rule_mem
  have hbinds := Exec.binds_all (by decide +kernel : binds rule.vars.length (varOccs rule.lhs) = true)
  have hplain : plainPat c rule.lhs = true := (hs.2.1 rule rule_mem).1
  have hcalls := (hs.2.1 rule rule_mem).2
  have hax := hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map.mpr ⟨rule, rule_mem, rfl⟩, rfl⟩)))
  unfold textRuleItem at hax
  let vs := canonVars c rule.vars
  let tbl : KoreAML.VarTable := KoreAML.tableOf [] (textRuleK c rule)
  let e' : Valuation M := valOf tbl (ruleVal c I rule.vars.length σ)
  have hVmem : ∀ i, i < rule.vars.length → canonKey c rule.vars i ∈ tbl := fun i hi => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show _ ∈ KoreAML.varsOf (textRuleK c rule)
    rw [textRuleK_eq]
    rw [KoreAML.varsOf, KoreAML.varsOf, KoreAML.varsOfList]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (varsOf_kore c vs rule.lhs (hbinds i hi)))))
  have hVv : ∀ i, i < rule.vars.length → e'.evalEvar (tbl.ev (canonKey c rule.vars i)) =
      (match σ.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [ruleVal]
    rw [varIdx_eq hi]
    try rfl
  have hvsort : ∀ i, i < rule.vars.length → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (rule.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c rule.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hΓ hsw e').1 m).symm
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] (textRuleK c rule) → ∃ i, i < rule.vars.length ∧ k = canonKey c rule.vars i := by
    intro k hk
    rw [textRuleK_eq] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk) | hk
    · exact freeOf_rule_parts hy.1 rule_mem (Or.inl hk)
    · exact freeOf_rule_parts hy.1 rule_mem (Or.inr (Or.inl hk))
    · exact freeOf_rule_parts hy.1 rule_mem (Or.inr (Or.inr (Or.inl hk)))
  have hg : ∀ k ∈ (([] : List Kore.SortVar).map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (textRuleK c rule)).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] (textRuleK c rule) := by
      simpa using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, rfl⟩ := hfree k hk'
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hVv i hi, hw]
    exact (elemOf_spec hΓ hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hΓ x.property e'
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  change (KoreAML.tr ⟨tbl, []⟩ (textRuleK c rule)).interpret I e' a at hP
  rw [textRuleK_eq, KoreAML.tr] at hP
  unfold KoreAML.sRewrites at hP
  rw [KoreAML.interp_sImp] at hP
  obtain ⟨-, himp⟩ := hP
  obtain ⟨σC, hσC1, -⟩ := sortSing hΓ (top_numbered (c := c))
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e' b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have hL := himp (by
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨(patVal_den hΓ hnn.1 hsc.trans hσ (canonVars_length c rule.vars) hag hmatch hplain hlhs).2 a |>.mpr
      ((ha a).mpr rfl), ?_⟩
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSC]
    unfold srtOf at hSC
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp has)
  obtain ⟨n, b, -, hb, -⟩ := KoreAML.interp_app.mp hL
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  exact (evalTerm_den (hpreTop := hpreTop) hΓ hnn hsc hs hy.1 hbc hmi (normDen_of hΓ hsc.trans) heval fns_headsOK hσ
    (canonVars_length c rule.vars) hag hrhss (fun g hg => hcalls g (List.mem_append_left _ hg)) b).mp hb.1

end UndefRhsWitness

end Faithful

end KCore
