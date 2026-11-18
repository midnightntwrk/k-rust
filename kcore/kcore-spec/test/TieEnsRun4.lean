/-
  The step of `run(4)` on `f2-examples/ens.kompile.kore`, derived from the text's rule sentence 155
  as written (C7 form (a), of the kind "from sentences"), for every interpretation H.
  Run from the package root: `lake env lean test/TieEnsRun4.lean`.

  - `Pre4 H`: the 30 function sentences as written (`TextFns`), sentence 155 under the premises that
    its variable `N` is `4` and its variable `_DotVar0` is the counter cell at 0 (`at4`), and the
    families. Γ's rule item, whose left side has the premise `⌈rhs⌉` more, is not a premise.
  - `run_4`: `Pre4 H ⊧ ⟦run(4)⟧ → •⟦done(2)⟧`. A model of `Pre4 H` is one of Γ of the semantics
    without its rule, `c0` (`gamma0_of_pre4`: the function items are the sentences by `fn_shape`,
    the rule items are none, and the rest are Γ's families, the values at the points where every
    clause fails being the same since evaluation reads no rule, `fails_withRulesE`), where
    `half(4) = 2` (`half4`). At the valuation that sends `N` and `_DotVar0` to the matched values, the left side
    of the sentence holds what `run(4)`'s configuration holds and its right side what `done(2)`'s
    holds (`left_iff`, `rightAnd_iff`: the translated sides with those variables, and `half(N)`,
    replaced by the values' patterns are the configurations' patterns, `repl_left`, `repl_right`).
  - `pre4_model`: every model of Γ, for every H, is a model of `Pre4 H`; `at4` holds there by the
    tie of the rule in the direction from Γ to the text (`rule_w2_all`, as test/TieEnsW2.lean).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c
theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)
def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩
noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by kernel_rfl
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The rule (sentence 155): W2 -/

/-- The configuration sort. -/
noncomputable abbrev C0 : Kore.KSort := srtOf c topCellSort

/-- The right side of a rewrite. -/
def rightOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ _ r => r
  | p => p

/-- The first conjunct of the left side of a rewrite. -/
def leftOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ (.and _ (l :: _)) _ => l
  | p => p

/-- The term of a right side `\and{C}(term, \top{C}())`. -/
def rightTerm : Kore.Pattern → Kore.Pattern
  | .and _ (t :: _) => t
  | p => p

/-- Γ's axiom of the rule, and the axiom without the last conjunct of its left side. -/
noncomputable abbrev gRule : Kore.Pattern := prioRuleK c r0
noncomputable def gText : Kore.Pattern := .rewrites C0 (.and C0 [leftOf gRule, .top C0]) (rightOf gRule)

/-- Γ's axiom of the rule is `gText` with one conjunct more on its left side, the definedness of
its right side `\and{C}(r, \top{C}())`, `C` the configuration sort. -/
theorem rule_gamma_shape : gRule =
    .rewrites C0 (.and C0 ([leftOf gRule, .top C0] ++ [.ceil C0 C0 (rightOf gRule)])) (rightOf gRule) ∧
    rightOf gRule = .and C0 [rightTerm (rightOf gRule), .top C0] := by decide +kernel

theorem rule_tables : tableOf [] gRule = tableOf [] gText ∧
    (freeOf [] gRule).eraseDups = (freeOf [] gText).eraseDups := by decide +kernel

/-- `gText` is sentence 155: one translation, and one translation of the right side. -/
theorem rule_gtext : (trS U.ax155).pat = (trAxiom [] [] (kAx gText)).pat ∧
    tr ⟨tableOf U.ax155.ax.sortVars U.ax155.ax.pattern, []⟩ (rightOf U.ax155.ax.pattern) =
      tr ⟨tableOf [] gText, []⟩ (rightOf gRule) := by decide +kernel

theorem top_numbered (H : HookParams) : topCellSort < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)

/-- The variable table of sentence 155. -/
noncomputable def t155 : VarTable := tableOf U.ax155.ax.sortVars U.ax155.ax.pattern

/-- The right side of sentence 155 holds an element at the valuation `e`. -/
def RightDefined {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) : Prop :=
  ∃ b, (tr ⟨t155, []⟩ (rightOf U.ax155.ax.pattern)).interpret I e b

/-- **W2 for the rule, at every valuation**: in a model of Γ, for every H, sentence 155 holds at
each valuation at which its right side holds an element. Γ's axiom is the sentence with the
definedness of the right side on its left side (`rule_gamma_shape`), which holds of every
configuration there. -/
theorem rule_w2_all (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (hdef : RightDefined I e) (m : M) :
    (trS U.ax155).pat.interpret I e m := by
  rw [rule_gtext.1]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI (top_numbered H)
  have hdef' : ∃ b, (tr ⟨tableOf [] gText, []⟩ (rightOf gRule)).interpret I e b := by
    rw [← rule_gtext.2]; exact hdef
  generalize hT : tableOf [] gText = T at hdef'
  have hS : ∀ b, (trSort T C0).interpret I e b ↔ b = σ := fun b => by
    unfold C0 srtOf; rw [trSort_srt]; exact hσ1 b
  have htop : ∀ a, (tr ⟨T, []⟩ (.top C0)).interpret I e a → Inh I σ a := fun a ha => by
    rw [KoreAML.tr, interp_sTop hD (by unfold C0 srtOf; rw [trSort_srt]; rfl), interp_inhOf_of hS] at ha
    exact ha
  have hg : I ⊧ᴵ (trAxiom [] [] (kAx gRule)).pat :=
    hI _ (mem_Γ_rules (Or.inl ⟨_, by rw [ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _, rfl⟩))
  refine tieRule_more hD (g := kAx gRule) (t := kAx gText) (List.cons_ne_nil _ _) rule_gamma_shape.1
    rfl rule_tables.1 rule_tables.2 hg e (fun x hx a hls => ?_) m
  rw [List.mem_singleton.mp hx]
  show (tr ⟨tableOf [] gText, []⟩ (.ceil C0 C0 (rightOf gRule))).interpret I e a
  have hls' : ∀ p ∈ [leftOf gRule, Kore.Pattern.top C0], (tr ⟨tableOf [] gText, []⟩ p).interpret I e a := hls
  rw [hT] at hls' ⊢
  rw [KoreAML.tr]
  refine (interp_sCeil hD hc hS hS hσ2 hσ2 (fun b hb => ?_) a).mpr ⟨hdef', htop a (hls' _ (by simp))⟩
  rw [rule_gamma_shape.2] at hb
  exact htop b ((interp_and (List.cons_ne_nil _ _)).mp hb _ (by simp))

/-- **W2 for the rule** (`AtValues` with the guard): in a model of Γ, for every H, sentence 155
holds at each valuation that sends its variables to values and at which its right side holds an
element. The sentence has no rule of a smaller priority, so the guard has no second part. -/
theorem rule_w2 (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ∀ e, AtValues (cH H) I e U.ax155.ax → RightDefined I e →
      ∀ m, (trS U.ax155).pat.interpret I e m :=
  fun _ _ _ hI e _ hdef m => rule_w2_all H hI e hdef m


/-! ## The function equations (30 sentences), as test/TieEns.lean states them -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 30 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax211, U.ax229, U.ax237, U.ax236, U.ax235, U.ax234, U.ax241, U.ax240, U.ax243, U.ax242, U.ax239,
   U.ax238, U.ax216, U.ax215, U.ax228, U.ax227, U.ax224, U.ax223, U.ax226, U.ax225, U.ax231, U.ax230,
   U.ax233, U.ax232, U.ax220, U.ax219, U.ax222, U.ax221, U.ax218, U.ax217]

/-- Γ's equations are the text's sentences' translations, pattern for pattern (kernel). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]; exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-! ## Γ has a model, for every H, as test/TieEns.lean states it -/

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed

def callOrder : List Nat := [364]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The step of `run(4)`, from sentence 155 at the matched values (C7 form (a), from sentences) -/

/-! ### Evaluation reads no rule -/

/-- The semantics `c` with the rules `rs`. -/
abbrev withRulesE (c : Semantics) (rs : List Rule) : Semantics := { c with rules := rs }

kernel_rfl collVal_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).collVal = c.collVal
kernel_rfl norm_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).norm = c.norm
kernel_rfl wellSorted_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).WellSorted = c.WellSorted
kernel_rfl wellSortedAt_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).WellSortedAt = c.WellSortedAt
kernel_rfl fnRest_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).fnRest = c.fnRest
kernel_rfl hookRes_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).hookRes = c.hookRes
kernel_rfl paramVal_withRulesE : ∀ (c : Semantics) (rs : List Rule), (withRulesE c rs).paramVal = c.paramVal
kernel_rfl extends_withRulesE : ∀ (c : Semantics) (rs : List Rule), Extends (withRulesE c rs) = Extends c

section
variable (c : Semantics) (rs : List Rule)

/-- Matching reads no rule. -/
theorem patVal_withRulesE {σ : Subst} {p : Term} {v : GroundTerm} (h : PatVal c σ p v) :
    PatVal (withRulesE c rs) σ p v :=
  PatVal.rec (c := c) (motive_1 := fun p v _ => PatVal (withRulesE c rs) σ p v)
    (motive_2 := fun ps vs _ => PatVals (withRulesE c rs) σ ps vs)
    (fun h => .var h) .dv (fun h _ ih => .ctor h ih) (fun hp _ hv ih => .hook hp ih hv)
    (fun _ ih => .inj ih) (fun hc hp _ hv ih => .coll hc hp ih ((congrFun (congrFun (collVal_withRulesE c rs) _) _).trans hv)) (fun _ hi ih => .as ih hi)
    (fun hc ho _ hv ih => .ovl hc ho ih ((congrFun (congrFun (norm_withRulesE c rs) _) _).trans hv)) .nil (fun _ _ ih ihs => .cons ih ihs) h

theorem patVals_withRulesE {σ : Subst} {ps : List Term} {vs : List GroundTerm} (h : PatVals c σ ps vs) :
    PatVals (withRulesE c rs) σ ps vs :=
  PatVals.rec (c := c) (motive_1 := fun p v _ => PatVal (withRulesE c rs) σ p v)
    (motive_2 := fun ps vs _ => PatVals (withRulesE c rs) σ ps vs)
    (fun h => .var h) .dv (fun h _ ih => .ctor h ih) (fun hp _ hv ih => .hook hp ih hv)
    (fun _ ih => .inj ih) (fun hc hp _ hv ih => .coll hc hp ih ((congrFun (congrFun (collVal_withRulesE c rs) _) _).trans hv)) (fun _ hi ih => .as ih hi)
    (fun hc ho _ hv ih => .ovl hc ho ih ((congrFun (congrFun (norm_withRulesE c rs) _) _).trans hv)) .nil (fun _ _ ih ihs => .cons ih ihs) h

/-- And back: `c` is `withRulesE c rs` with the rules `c.rules`. -/
theorem patVal_withRulesE_back {σ : Subst} {p : Term} {v : GroundTerm} (h : PatVal (withRulesE c rs) σ p v) :
    PatVal c σ p v :=
  patVal_withRulesE (withRulesE c rs) c.rules h

theorem patVals_withRulesE_back {σ : Subst} {ps : List Term} {vs : List GroundTerm}
    (h : PatVals (withRulesE c rs) σ ps vs) : PatVals c σ ps vs :=
  patVals_withRulesE (withRulesE c rs) c.rules h

/-- **Evaluation reads no rule**: a clause that fails in `c` fails in `c` with other rules. -/
theorem fails_withRulesE {vs : List GroundTerm} {cl : Clause} (h : Fails c vs cl) : Fails (withRulesE c rs) vs cl :=
  Fails.rec (c := c) (motive_1 := fun f vs r _ => Eval (withRulesE c rs) f vs r)
    (motive_2 := fun vs cl _ => Fails (withRulesE c rs) vs cl)
    (motive_3 := fun σ cl _ => ReqFails (withRulesE c rs) σ cl)
    (motive_4 := fun σ t r _ => EvalTerm (withRulesE c rs) σ t r)
    (motive_5 := fun σ ts rs' _ => EvalTerms (withRulesE c rs) σ ts rs')
    (motive_6 := fun n σ p b _ => Holds (withRulesE c rs) n σ p b)
    (fun hfn hmem hσ hmatch _ _ _ _ _ ihreq ihpre ihprio ihrhs ihens =>
      .clause hfn hmem ((congrFun (congrFun (wellSorted_withRulesE c rs) _) _).mpr hσ) (patVals_withRulesE c rs hmatch) ihreq ihpre ihprio ihrhs ihens)
    (fun hfn _ ihnone => fnRest_withRulesE c rs ▸ Eval.rest (c := withRulesE c rs) hfn ihnone)
    (fun hfn hmem hσ hmatch _ _ _ ht _ hw ihreq ihpre ihprio ihe =>
      .ensFails hfn hmem ((congrFun (congrFun (wellSorted_withRulesE c rs) _) _).mpr hσ) (patVals_withRulesE c rs hmatch) ihreq ihpre ihprio ht ihe hw)
    (fun _ ih => .intro fun σ hw hp =>
      ih σ ((congrFun (congrFun (congrFun (wellSortedAt_withRulesE c rs) _) _) _).mp hw) (patVals_withRulesE_back c rs hp))
    (fun ht _ hr ihe => .intro ht ihe hr)
    (fun _ ih => .pre ih)
    .var .dv
    (fun _ ih => .inj ih)
    (fun hk _ ihts => .ctor hk ihts)
    (fun hk hhk _ hh hund ihts => .hook hk hhk ihts
      (fun vs h => (congrFun (congrFun (hookRes_withRulesE c rs) _) _).trans (hh vs h)) hund)
    (fun hk hhk hp _ hr ihts => .param hk hhk hp ihts (by rw [paramVal_withRulesE]; exact hr))
    (fun hk hhk _ hvs _ hp ihts ihf => .call hk hhk ihts hvs ihf hp)
    (fun hk hhk _ hvs hp ihts => .callUndef hk hhk ihts hvs hp)
    (fun hk ho _ ihts => norm_withRulesE c rs ▸ EvalTerm.ovl (c := withRulesE c rs) hk ho ihts)
    .nil
    (fun _ _ ih ihs => .cons ih ihs)
    .top .bot
    (fun _ ih => .not ih)
    (fun _ _ ih ih' => .and ih ih')
    (fun _ _ ih ih' => .or ih ih')
    (fun _ _ ih ih' => .implies ih ih')
    (fun _ ih => .ceil ih)
    (fun _ _ ih ih' => .equals ih ih')
    (fun _ _ ih ih' => .mem ih ih')
    (fun _ ih => .exNone ih)
    (fun g _ _ hr ih ihb => .exSome g ih
      (fun σ' he hp => ihb σ' (by rw [extends_withRulesE] at he; exact he) (patVal_withRulesE_back c rs hp))
      (by rw [extends_withRulesE]; exact hr.trans ⟨fun ⟨σ', h1, h2, h3⟩ => ⟨σ', h1, patVal_withRulesE c rs h2, h3⟩,
        fun ⟨σ', h1, h2, h3⟩ => ⟨σ', h1, patVal_withRulesE_back c rs h2, h3⟩⟩))
    (fun g _ hr ihb => .ex g (fun σ' he => ihb σ' (by rw [extends_withRulesE] at he; exact he))
      (by rw [extends_withRulesE]; exact hr))
    (fun g _ hr ihb => .all g (fun σ' he => ihb σ' (by rw [extends_withRulesE] at he; exact he))
      (by rw [extends_withRulesE]; exact hr))
    h

end

/-! ### The semantics without its rule -/

/-- The semantics without its rule: Γ of it is Γ less the rule item. -/
noncomputable abbrev c0 : Semantics := { c with rules := [] }
noncomputable abbrev c0H (H : HookParams) : Semantics := c0.withHooks H

kernel_rfl sig_noRules : ∀ (c : Semantics) (H : HookParams),
  ΓSig ({ c with rules := [] }.withHooks H) = ΓSig (c.withHooks H)
kernel_rfl cons_noRules : ∀ (c : Semantics) (H : HookParams),
  ΓCons ({ c with rules := [] }.withHooks H) = ΓCons (c.withHooks H)
kernel_rfl dom_noRules : ∀ (c : Semantics) (H : HookParams),
  ΓDomains ({ c with rules := [] }.withHooks H) = ΓDomains (c.withHooks H)
kernel_rfl colls_noRules : ∀ (c : Semantics) (H : HookParams),
  ΓColls ({ c with rules := [] }.withHooks H) = ΓColls (c.withHooks H)
kernel_rfl fallback_noRules : ∀ (c : Semantics) (H : HookParams),
  ({ c with rules := [] }.withHooks H).fallback = (c.withHooks H).fallback
kernel_rfl fnRest_noRules : ∀ (c : Semantics) (H : HookParams),
  ({ c with rules := [] }.withHooks H).fnRest = (c.withHooks H).fnRest
kernel_rfl sortsOf_noRules : ∀ (c : Semantics) (H : HookParams),
  ({ c with rules := [] }.withHooks H).sortsOf = (c.withHooks H).sortsOf
kernel_rfl allFns_noRules : ∀ (c : Semantics) (H : HookParams),
  ({ c with rules := [] }.withHooks H).allFns = (c.withHooks H).allFns
kernel_rfl den_withHooksE : ∀ (c : Semantics) (H : HookParams) (v : GroundTerm), den (c.withHooks H) v = den c v
kernel_rfl symApp_withHooksE : ∀ (c : Semantics) (H : HookParams) (f : Sym) (ps : List Kore.Pattern),
  symApp (c.withHooks H) f ps = symApp c f ps
kernel_rfl koreList_withHooksE : ∀ (c : Semantics) (H : HookParams) (vs : List GroundTerm),
  GroundTerm.koreList (c.withHooks H) vs = GroundTerm.koreList c vs
kernel_rfl fnItems_noRules : ∀ (c : Semantics) (H : HookParams),
  fnItems ({ c with rules := [] }.withHooks H) = fnItems c
kernel_rfl ruleItems_noRules : ∀ (c : Semantics) (H : HookParams),
  ruleItems ({ c with rules := [] }.withHooks H) = []
kernel_rfl den_noRules : ∀ (c : Semantics) (H : HookParams) (v : GroundTerm),
  den ({ c with rules := [] }.withHooks H) v = den c v
kernel_rfl symApp_noRules : ∀ (c : Semantics) (H : HookParams) (f : Sym) (ps : List Kore.Pattern),
  symApp ({ c with rules := [] }.withHooks H) f ps = symApp c f ps
kernel_rfl koreList_noRules : ∀ (c : Semantics) (H : HookParams) (vs : List GroundTerm),
  GroundTerm.koreList ({ c with rules := [] }.withHooks H) vs = GroundTerm.koreList c vs

/-- The values Γ without the rule states at the points where the hooks or the clauses give
nothing hold in a model of those Γ states: the points are the same, a clause failing without the
rule failing with it (`fails_withRulesE`), and the patterns hold the same elements. -/
theorem fallback0 (H : HookParams) {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hF : ∀ φ, ΓFallback (cH H) φ → I ⊧ᴵ φ) : ∀ φ, ΓFallback (c0H H) φ → I ⊧ᴵ φ := by
  intro φ h
  rcases h with ⟨k, vs, hk, hvs, hh, hs, rfl⟩ | ⟨fn, vs, hfn, hvs, hfail, rfl⟩
  · have h1 := hF _ (Or.inl ⟨k, vs, hk, by rw [← sortsOf_noRules c H]; exact hvs, hh, hs, rfl⟩)
    intro e m
    have h2 := h1 e m
    rw [interp_equal hD] at h2 ⊢
    intro a
    rw [symApp_noRules c H, koreList_noRules c H, fallback_noRules c H]
    rw [symApp_withHooksE, koreList_withHooksE] at h2
    refine (h2 a).trans ?_
    cases (cH H).fallback k.name vs with
    | none => exact Iff.rfl
    | some v =>
      show (den (cH H) v).interpret I e a ↔ (den (c0H H) v).interpret I e a
      rw [den_noRules c H, den_withHooksE]
  · have hfail' : ∀ cl ∈ fn.clauses, Fails (cH H) vs cl := fun cl hcl =>
      fails_withRulesE (c0H H) c.rules (hfail cl hcl)
    have h1 := hF _ (Or.inr ⟨fn, vs, by rw [← allFns_noRules c H]; exact hfn,
      by rw [← sortsOf_noRules c H]; exact hvs, hfail', rfl⟩)
    intro e m
    have h2 := h1 e m
    rw [interp_equal hD] at h2 ⊢
    intro a
    rw [symApp_noRules c H, koreList_noRules c H, fnRest_noRules c H]
    rw [symApp_withHooksE, koreList_withHooksE] at h2
    refine (h2 a).trans ?_
    cases (cH H).fnRest fn vs with
    | none => exact Iff.rfl
    | some v =>
      show (den (cH H) v).interpret I e a ↔ (den (c0H H) v).interpret I e a
      rw [den_noRules c H, den_withHooksE]

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem coreOK0H (H : HookParams) : (c0H H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A model of Γ, for every H, is one of Γ without the rule. -/
theorem gamma0_of_gamma (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) : I ⊧ᴵP Γ (c0H H) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · rw [sig_noRules c H] at h; exact hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · rw [cons_noRules c H] at h; exact hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · rw [dom_noRules c H] at h; exact hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · rw [colls_noRules c H] at h; exact hI _ (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_noRules c H] at hit
      exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, rfl⟩))
    · exact hI _ (mem_Γ_fns (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_noRules c H] at hit; exact absurd hit List.not_mem_nil
    · exact hI _ (mem_Γ_rules (Or.inr hx))
  · exact fallback0 H (defOK hI) (fun ψ hψ => hI _ (Or.inr hψ)) φ h

end

/-! ### `half(4) = 2` in Γ without the rule -/

/-- **A defined result is a theorem of Γ**, for a semantics with `HypSoundCore` (as in
test/TieEns.lean). -/
theorem eval_some_sound_core (c : Semantics) (h : HypSoundCore c)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {v : GroundTerm} (hE : Eval c f vs (some v)) (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ den c v) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop hok hfn hcl)
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfn hcl hp') hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  rw [eval_den4 hI hnn hsc hok hbc hph (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hE hfn hvs e a]
  rfl

def half : Sym := 387
def run : Sym := 386
def done : Sym := 385
def kCell : Sym := 383
def cmd : Srt := 32

theorem names : c.symName half = "Lblhalf" ∧ c.symName run = "Lblrun" ∧ c.symName done = "Lbldone" ∧
    c.sortName cmd = "Cmd" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

private theorem hok0 : c0.ok = true := by decide +kernel
private theorem hsr0 : c0.srReady = true := by decide +kernel
private theorem hmr0 : c0.matchReady = true := by decide +kernel

theorem hok0H (H : HookParams) : (c0H H).ok = true := (Semantics.ok_withHooks c0 H).trans hok0
theorem hsr0H (H : HookParams) : (c0H H).srReady = true := (Semantics.srReady_withHooks c0 H).trans hsr0
theorem hmr0H (H : HookParams) : (c0H H).matchReady = true := (Semantics.matchReady_withHooks c0 H).trans hmr0
theorem hfn0H (H : HookParams) : (c0H H).lookupFn half = some fn := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem hvs0H4 (H : HookParams) : (c0H H).sortsOf [int 4] = some fn.args := by
  rw [Semantics.sortsOf_withHooks c0 H noRaw]; decide +kernel

theorem eval0 (H : HookParams) : Eval (c0H H) half [int 4] (some (int 2)) :=
  Exec.evalF_sound (sortCtx_of (hok0H H) (hsr0H H) (Exec.ovlCase_of (hmr0H H))) (Exec.clauseCtx_of (hok0H H))
    (Exec.matchCtx_of (hmr0H H)) 10 (Cert.evalFC_sound 10 (by
      rw [Cert.evalFC_withHooks c0 H noRaw]
      exact (by decide +kernel : Cert.evalFC c0 10 half [int 4] = some (some (int 2))))) (hfn0H H) (hvs0H4 H)

/-- `half(4) = 2`, a theorem of Γ without the rule, for every H. -/
theorem half4 (H : HookParams) :
    Γ (c0H H) ⊧ (KoreAML.den (symApp (c0H H) half (GroundTerm.koreList (c0H H) [int 4])) ≡ den (c0H H) (int 2)) :=
  eval_some_sound_core _ (hypSound_of_core (coreOK0H H)) (Semantics.ok_clauseBinds (hok0H H)) (eval0 H)
    (hfn0H H) (hvs0H4 H)

/-! ### The configurations and the instance of sentence 155 -/

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmd Srt.kitem it, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- `run(4)` in the k cell, and its successor `done(2)`. -/
def X4 : Config c := ⟨cfg (.ctor run [int 4]), by decide +kernel⟩
def Y4 : Config c := ⟨cfg (.ctor done [int 2]), by decide +kernel⟩
/-- The counter cell at 0. -/
def cnt0 : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]

theorem X4_sort0 : c0.sortOf X4.val = some topCellSort := by decide +kernel
theorem Y4_sort0 : c0.sortOf Y4.val = some topCellSort := by decide +kernel
def X4H (H : HookParams) : Config (c0H H) := ⟨X4.val, by rw [Semantics.sortOf_withHooks c0 H noRaw]; exact X4_sort0⟩
def Y4H (H : HookParams) : Config (c0H H) := ⟨Y4.val, by rw [Semantics.sortOf_withHooks c0 H noRaw]; exact Y4_sort0⟩

theorem int4_sort (H : HookParams) : (c0H H).sortOf (int 4) = some Srt.int := by
  rw [Semantics.sortOf_withHooks c0 H noRaw]; decide +kernel
def gcc : Srt := 19
theorem cnt0_sort (H : HookParams) : (c0H H).sortOf cnt0 = some gcc := by
  rw [Semantics.sortOf_withHooks c0 H noRaw]; decide +kernel
theorem sort_names (H : HookParams) : (c0H H).sortName Srt.int = "Int" ∧ (c0H H).sortName gcc = "GeneratedCounterCell" :=
  (by decide +kernel : c0.sortName Srt.int = "Int" ∧ c0.sortName gcc = "GeneratedCounterCell")

/-- The variables `N` and `_DotVar0` of sentence 155. -/
def kN : VarKey := .evar "VarN" (KoreAML.srt "Int")
def kD : VarKey := .evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell")
noncomputable def xN : EVar := t155.ev kN
noncomputable def xD : EVar := t155.ev kD
theorem xN_ne_xD : xN ≠ xD := by decide +kernel

/-- **Sentence 155 at the matched values**: the translated sentence as written, under the two
premises that its variable `N` is `4` and its variable `_DotVar0` is the counter cell at 0. -/
noncomputable def at4 : P :=
  (.evar xN ≡ den c (int 4)) ⇒ ((.evar xD ≡ den c cnt0) ⇒ (trS U.ax155).pat)

/-- The premises of the step: the 30 function sentences as written, sentence 155 at the matched
values, and the families. Γ's rule item is not among them. -/
def TextFns : Premises KoreAML.Sym := fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)
def Pre4 (H : HookParams) : Premises KoreAML.Sym := TextFns ∪ (fun φ => φ = at4) ∪ Families H

/-! ### Replacing subpatterns by patterns of the same elements -/

/-- Replace, top-down, each subpattern `f` names by its image, descending through applications. -/
def replP (f : P → Option P) : P → P
  | .application a b => (f (.application a b)).getD (.application (replP f a) (replP f b))
  | p => (f p).getD p

/-- Where each replaced subpattern and its image hold the same elements, so do the pattern and its
replacement. -/
theorem replP_iff {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} (f : P → Option P)
    (hf : ∀ p q, f p = some q → ∀ b, p.interpret I e b ↔ q.interpret I e b) :
    ∀ (p : P) (b : M), p.interpret I e b ↔ (replP f p).interpret I e b := by
  have other : ∀ p : P, replP f p = (f p).getD p → ∀ b, p.interpret I e b ↔ (replP f p).interpret I e b := by
    intro p hp b
    rw [hp]
    cases h : f p with
    | none => exact Iff.rfl
    | some q => exact hf p q h b
  intro p
  induction p with
  | application a b iha ihb =>
    intro m
    cases h : f (.application a b) with
    | some q => simp only [replP, h, Option.getD_some]; exact hf _ _ h m
    | none =>
      simp only [replP, h, Option.getD_none]
      exact interp_app_congr iha ihb m
  | evar x => exact other _ rfl
  | svar x => exact other _ rfl
  | bottom => exact other _ rfl
  | symbol σ => exact other _ rfl
  | implication a b _ _ => exact other _ rfl
  | existential x a _ => exact other _ rfl
  | mu x a _ => exact other _ rfl

/-- `N` by `4` and `_DotVar0` by the counter cell at 0. -/
noncomputable def fVals : P → Option P := fun p =>
  if p = .evar xN then some (den c (int 4)) else if p = .evar xD then some (den c cnt0) else none

/-- `half(N)`, as sentence 155 writes it. -/
def halfN : Kore.Pattern := .app ⟨⟨"Lblhalf"⟩⟩ [] [KoreAML.ev "VarN" (KoreAML.srt "Int")]

/-- `half(N)` by `2`, then as `fVals`. -/
noncomputable def fRight (al : List String) : P → Option P := fun p =>
  if p = tr ⟨t155, al⟩ halfN then some (den c (int 2)) else fVals p

/-- The first conjunct of each side of a rewrite. -/
def leftTerm : Kore.Pattern → Kore.Pattern
  | .rewrites _ (.and _ (l :: _)) _ => l
  | p => p
def rightTermOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ _ (.and _ (r :: _)) => r
  | p => p

theorem s155_shape : U.ax155.ax.pattern = .rewrites C0 (.and C0 [leftTerm U.ax155.ax.pattern, .top C0])
    (.and C0 [rightTermOf U.ax155.ax.pattern, .top C0]) := by decide +kernel
theorem s155_sort : KoreAML.sortOf kore.symbolDecls U.ax155.ax.pattern = some C0 := by decide +kernel
theorem s155_free : (U.ax155.ax.sortVars.map sortVarKey ++ freeOf [] U.ax155.ax.pattern).eraseDups = [kN, kD] := by
  decide +kernel
theorem s155_rightOf : rightOf U.ax155.ax.pattern = .and C0 [rightTermOf U.ax155.ax.pattern, .top C0] := by
  decide +kernel

/-- The left side of sentence 155 with `N` by `4` and `_DotVar0` by the counter cell is `run(4)`'s
configuration; the right side with `half(N)` by `2` is `done(2)`'s; `half(N)` with `N` by `4` is
`half(4)`. With the translation's aliases, and with none. -/
theorem repl_left : replP fVals (tr ⟨t155, kore.aliasNames⟩ (leftTerm U.ax155.ax.pattern)) = den c X4.val := by
  decide +kernel
theorem repl_half : replP fVals (tr ⟨t155, kore.aliasNames⟩ halfN) =
    KoreAML.den (symApp c half (GroundTerm.koreList c [int 4])) := by decide +kernel
theorem repl_right : replP (fRight kore.aliasNames) (tr ⟨t155, kore.aliasNames⟩ (rightTermOf U.ax155.ax.pattern)) =
    den c Y4.val := by decide +kernel
theorem repl_half0 : replP fVals (tr ⟨t155, []⟩ halfN) =
    KoreAML.den (symApp c half (GroundTerm.koreList c [int 4])) := by decide +kernel
theorem repl_right0 : replP (fRight []) (tr ⟨t155, []⟩ (rightTermOf U.ax155.ax.pattern)) = den c Y4.val := by
  decide +kernel

theorem tr_rw2 {ctx : KoreAML.Ctx} {C : Kore.KSort} {L R : Kore.Pattern} :
    tr ctx (.rewrites C (.and C [L, .top C]) (.and C [R, .top C])) =
      sRewrites (trSort ctx.vars C) (trAndList ctx (trSort ctx.vars C) [L, .top C])
        (trAndList ctx (trSort ctx.vars C) [R, .top C]) := rfl
theorem tr_and {ctx : KoreAML.Ctx} {C : Kore.KSort} {ps : List Kore.Pattern} :
    tr ctx (.and C ps) = trAndList ctx (trSort ctx.vars C) ps := rfl

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A value's pattern holds the same elements at every valuation. -/
theorem den_val_iff {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {v : GroundTerm} {s : Srt} (hs : (c0H H).sortOf v = some s)
    (e e' : Valuation M) (b : M) : (den c v).interpret I e b ↔ (den c v).interpret I e' b := by
  rw [← den_noRules c H v, (elemOf_spec hI hs e).1 b, (elemOf_spec hI hs e').1 b]

/-- A variable whose element is a value's holds what the value's pattern holds. -/
theorem var_val_iff {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {v : GroundTerm} {s : Srt} (hs : (c0H H).sortOf v = some s)
    {x : EVar} {e : Valuation M} (hx : e.evalEvar x = elemOf (c0H H) I v) (b : M) :
    (Pattern.evar x : P).interpret I e b ↔ (den c v).interpret I e b := by
  rw [KoreAML.interp_evar, hx, ← den_noRules c H v, (elemOf_spec hI hs e).1 b]

/-- The valuation that sends `N` to `4`'s element and `_DotVar0` to the counter cell's. -/
structure AtFour (H : HookParams) (e : Valuation M) : Prop where
  n : e.evalEvar xN = elemOf (c0H H) I (int 4)
  d : e.evalEvar xD = elemOf (c0H H) I cnt0

theorem fVals_ok {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) :
    ∀ p q, fVals p = some q → ∀ b, p.interpret I e b ↔ q.interpret I e b := by
  intro p q h b
  unfold fVals at h
  split at h
  · cases h; rename_i hp; subst hp; exact var_val_iff hI (int4_sort H) h4.n b
  · split at h
    · cases h; rename_i _ hp; subst hp; exact var_val_iff hI (cnt0_sort H) h4.d b
    · cases h

theorem half_iff {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) {al : List String}
    (hh : replP fVals (tr ⟨t155, al⟩ halfN) = KoreAML.den (symApp c half (GroundTerm.koreList c [int 4]))) (b : M) :
    (tr ⟨t155, al⟩ halfN).interpret I e b ↔ (den c (int 2)).interpret I e b := by
  rw [replP_iff fVals (fVals_ok hI h4) (tr ⟨t155, al⟩ halfN) b, hh]
  have h2 := (KoreAML.interp_equal (defOK hI)).mp (half4 H hI e default) b
  rw [symApp_noRules c H, koreList_noRules c H, den_noRules c H] at h2
  exact h2

theorem right_iff {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) {al : List String}
    (hh : replP fVals (tr ⟨t155, al⟩ halfN) = KoreAML.den (symApp c half (GroundTerm.koreList c [int 4])))
    (hr : replP (fRight al) (tr ⟨t155, al⟩ (rightTermOf U.ax155.ax.pattern)) = den c Y4.val) (b : M) :
    (tr ⟨t155, al⟩ (rightTermOf U.ax155.ax.pattern)).interpret I e b ↔ (den c Y4.val).interpret I e b := by
  have hf : ∀ p q, fRight al p = some q → ∀ b, p.interpret I e b ↔ q.interpret I e b := by
    intro p q h b
    unfold fRight at h
    split at h
    · cases h; rename_i hp; subst hp; exact half_iff hI h4 hh b
    · exact fVals_ok hI h4 p q h b
  rw [replP_iff (fRight al) hf (tr ⟨t155, al⟩ (rightTermOf U.ax155.ax.pattern)) b, hr]

theorem left_iff {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) (b : M) :
    (tr ⟨t155, kore.aliasNames⟩ (leftTerm U.ax155.ax.pattern)).interpret I e b ↔ (den c X4.val).interpret I e b := by
  rw [replP_iff fVals (fVals_ok hI h4) (tr ⟨t155, kore.aliasNames⟩ (leftTerm U.ax155.ax.pattern)) b, repl_left]

/-- `\top` of the configuration sort holds of a configuration's element. -/
theorem top_of_config {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) (x : Config (c0H H)) {al : List String} {e : Valuation M}
    {b : M} (hb : (den c x.val).interpret I e b) : (tr ⟨t155, al⟩ (.top C0)).interpret I e b := by
  haveI : OvlOK (c0H H) := ovlOK_of_core (coreOK0H H)
  rw [← den_noRules c H, (elemOf_spec hI x.property e).1 b] at hb
  subst hb
  rw [KoreAML.tr, interp_sTop (defOK hI) (by unfold C0 srtOf; rw [trSort_srt]; rfl)]
  exact elemOf_top hI x t155 e

/-- The right side of sentence 155, `\and{C}(done(half(N)), \top{C}())`, at `AtFour`, holds what
`done(2)`'s configuration holds. -/
theorem rightAnd_iff {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) {al : List String}
    (hh : replP fVals (tr ⟨t155, al⟩ halfN) = KoreAML.den (symApp c half (GroundTerm.koreList c [int 4])))
    (hr : replP (fRight al) (tr ⟨t155, al⟩ (rightTermOf U.ax155.ax.pattern)) = den c Y4.val) (b : M) :
    (trAndList ⟨t155, al⟩ (trSort t155 C0) [rightTermOf U.ax155.ax.pattern, .top C0]).interpret I e b ↔
      (den c Y4.val).interpret I e b := by
  rw [interp_trAndList (List.cons_ne_nil _ _)]
  constructor
  · intro h; exact (right_iff hI h4 hh hr b).mp (h _ (by simp))
  · intro hy p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (right_iff hI h4 hh hr b).mpr hy
    · exact top_of_config hI (Y4H H) hy

/-- A translated axiom at one valuation whose guards hold there: its pattern is the whole of its sort. -/
theorem trAxiom_at1 (hD : DefOK I) {ds : List SymbolDecl} {al : List String} {ad : AxiomDecl} {e : Valuation M} {m : M}
    (h : (trAxiom ds al ad).pat.interpret I e m)
    (hg : ∀ k ∈ (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups,
      (guardOf (tableOf ad.ax.sortVars ad.ax.pattern) k).interpret I e m) (a : M) :
    (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, al⟩ ad.ax.pattern).interpret I e a ↔
      (match KoreAML.sortOf ds ad.ax.pattern with
        | some s => inhOf (trSort (tableOf ad.ax.sortVars ad.ax.pattern) s)
        | none => sym (.untranslated "sort of the axiom")).interpret I e a := by
  unfold trAxiom at h
  dsimp only at h
  have h2 := h (interp_conjList fun w hw => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
    exact hg k hk)
  rw [interp_equal hD] at h2
  exact h2 a

/-- The guards of sentence 155 hold at `AtFour`. -/
theorem guards155 {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) (m : M) :
    ∀ k ∈ (U.ax155.ax.sortVars.map sortVarKey ++ freeOf [] U.ax155.ax.pattern).eraseDups,
      (guardOf (tableOf U.ax155.ax.sortVars U.ax155.ax.pattern) k).interpret I e m := by
  have hD := defOK hI
  rw [s155_free]
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · unfold kN; rw [interp_guard_evar hD, trSort_srt]
    show (inhOf (sym (.sort ("Sort" ++ "Int")))).interpret I e (e.evalEvar xN)
    rw [h4.n]
    have := (elemOf_spec hI (int4_sort H) e).2
    rw [(sort_names H).1] at this
    exact this
  · unfold kD; rw [interp_guard_evar hD, trSort_srt]
    show (inhOf (sym (.sort ("Sort" ++ "GeneratedCounterCell")))).interpret I e (e.evalEvar xD)
    rw [h4.d]
    have := (elemOf_spec hI (cnt0_sort H) e).2
    rw [(sort_names H).2] at this
    exact this

/-- At `AtFour`, the premises of `at4` hold. -/
theorem at4_premises {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} (h4 : AtFour (I := I) H e) (m : M) :
    (.evar xN ≡ den c (int 4) : P).interpret I e m ∧ (.evar xD ≡ den c cnt0 : P).interpret I e m :=
  ⟨(KoreAML.interp_equal (defOK hI)).mpr (var_val_iff hI (int4_sort H) h4.n),
    (KoreAML.interp_equal (defOK hI)).mpr (var_val_iff hI (cnt0_sort H) h4.d)⟩

/-- Where the premises of `at4` hold, the valuation is `AtFour`. -/
theorem atFour_of {H : HookParams} (hI : I ⊧ᴵP Γ (c0H H)) {e : Valuation M} {m : M}
    (h1 : (.evar xN ≡ den c (int 4) : P).interpret I e m) (h2 : (.evar xD ≡ den c cnt0 : P).interpret I e m) :
    AtFour (I := I) H e := by
  have k1 := ((KoreAML.interp_equal (defOK hI)).mp h1 (e.evalEvar xN)).mp rfl
  have k2 := ((KoreAML.interp_equal (defOK hI)).mp h2 (e.evalEvar xD)).mp rfl
  rw [← den_noRules c H, (elemOf_spec hI (int4_sort H) e).1] at k1
  rw [← den_noRules c H, (elemOf_spec hI (cnt0_sort H) e).1] at k2
  exact ⟨k1, k2⟩

end

/-! ### The premise set has a model -/

/-- Every model of Γ, for every H, satisfies sentence 155 at the matched values: there its right
side is `done(2)`'s configuration, which holds an element (`rule_w2_all`). -/
theorem at4_of_gamma (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : I ⊧ᴵ at4 := by
  intro e m
  have hΓ := gamma0_of_gamma H hI
  unfold at4
  rw [interpret_impl, interpret_impl]
  intro h1 h2
  have h4 := atFour_of hΓ h1 h2
  refine rule_w2_all H hI e (Exists.intro (elemOf (c0H H) I Y4.val) ?_) m
  rw [s155_rightOf, tr_and]
  refine (rightAnd_iff hΓ h4 repl_half0 repl_right0 _).mpr ?_
  rw [← den_noRules c H, (elemOf_spec (v := Y4.val) hΓ (Y4H H).property e).1]

/-- **The premise set of `run_4` has a model, for every H**: every model of Γ is one. -/
theorem pre4_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Pre4 H := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with ((h | h) | h)
  · rcases h with ⟨ad, had, rfl⟩ | ⟨x, rfl⟩
    · exact fns_entailed H ad had hΓ
    · exact hΓ _ (mem_Γ_fns (Or.inr ⟨x, rfl⟩))
  · have h' : φ = at4 := h
    subst h'; exact at4_of_gamma H hΓ
  · rcases h with (((h | h) | h) | h) | h
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact hΓ _ (Or.inr h)

/-! ### The step -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A model of `Pre4` is one of Γ without the rule: the function sentences as written are Γ's
equations (`fn_shape`), and the families are the rest. -/
theorem gamma0_of_pre4 (H : HookParams) (hI : I ⊧ᴵP Pre4 H) : I ⊧ᴵP Γ (c0H H) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · rw [sig_noRules c H] at h; exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · rw [cons_noRules c H] at h; exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · rw [dom_noRules c H] at h; exact hI _ (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rw [colls_noRules c H] at h; exact hI _ (Or.inr (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_noRules c H] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
    · exact hI _ (Or.inl (Or.inl (Or.inr hx)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_noRules c H] at hit; exact absurd hit List.not_mem_nil
    · exact hI _ (Or.inl (Or.inl (Or.inr hx)))
  · exact fallback0 H (KoreAML.defOK_of fun x => hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))
      (fun ψ hψ => hI _ (Or.inr (Or.inr hψ))) φ h

end

/-- **The step of `run(4)`, derived from sentence 155 as written at N = 4**, for every H:
`⟦run(4)⟧ → •⟦done(2)⟧`, from the 30 function sentences as written (211 gives `half(4) = 2`), the
instance of sentence 155 at the matched values, and the families (`Pre4`, which has a model,
`pre4_model`). Γ's rule item, with its premise `⌈rhs⌉`, is not a premise. -/
theorem run_4 (H : HookParams) : Pre4 H ⊧ (den c X4.val ⇒ KoreAML.sNext (den c Y4.val)) := by
  intro M _ I hI e m
  have hΓ := gamma0_of_pre4 H hI
  have hD := defOK hΓ
  rw [interpret_impl]
  intro hm
  -- the valuation that sends `N` and `_DotVar0` to the matched values
  let e' : Valuation M := ⟨Function.update (Function.update e.evalEvar xN (elemOf (c0H H) I (int 4))) xD
    (elemOf (c0H H) I cnt0), e.evalSvar⟩
  have h4 : AtFour (I := I) H e' :=
    ⟨by show Function.update (Function.update e.evalEvar xN (elemOf (c0H H) I (int 4))) xD
          (elemOf (c0H H) I cnt0) xN = _
        rw [Function.update_noteq xN_ne_xD, Function.update_same],
     by show Function.update (Function.update e.evalEvar xN (elemOf (c0H H) I (int 4))) xD
          (elemOf (c0H H) I cnt0) xD = _
        rw [Function.update_same]⟩
  have hm' : (den c X4.val).interpret I e' m := (den_val_iff (v := X4.val) hΓ (X4H H).property e e' m).mp hm
  -- sentence 155 at e'
  have hat := hI at4 (Or.inl (Or.inr rfl)) e' m
  unfold at4 at hat
  rw [interpret_impl, interpret_impl] at hat
  have h155 := hat (at4_premises hΓ h4 m).1 (at4_premises hΓ h4 m).2
  have h2 := trAxiom_at1 hD h155 (guards155 hΓ h4 m) m
  rw [s155_sort] at h2
  have h3 := h2.mpr (by
    show (inhOf (trSort t155 C0)).interpret I e' m
    have := top_of_config hΓ (X4H H) (al := kore.aliasNames) hm'
    rw [KoreAML.tr, interp_sTop hD (by unfold C0 srtOf; rw [trSort_srt]; rfl)] at this
    exact this)
  change (tr ⟨t155, kore.aliasNames⟩ U.ax155.ax.pattern).interpret I e' m at h3
  rw [s155_shape, tr_rw2] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  have hn := h3.2 ((interp_trAndList (List.cons_ne_nil _ _)).mpr fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (left_iff hΓ h4 m).mpr hm'
    · exact top_of_config hΓ (X4H H) hm')
  have hn' := sNext_congr (rightAnd_iff hΓ h4 repl_half repl_right) hn
  unfold KoreAML.sNext at hn' ⊢
  exact (interp_app_congr (e := e) (e' := e') (fun _ => Iff.rfl) (fun b => den_val_iff (v := Y4.val) hΓ (Y4H H).property e e' b) m).mpr hn'

end KCore.TieEns

#check @KCore.TieEns.run_4
#check @KCore.TieEns.pre4_model
#print axioms KCore.TieEns.run_4
#print axioms KCore.TieEns.pre4_model
