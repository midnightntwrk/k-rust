/-
  KCore, checked layer: the facts of `FnHyp` the deciders leave open, for a semantics, a rank of
  its functions and the parameters its text declares total (`FnObligations`), and `FnHyp` from
  them under `coreOK`, `Semantics.RightHeld` (each clause variable the patterns and conditions do
  not hold is of a sort with a value; a package decides it by `Semantics.rightValued`) and an
  interpretation total on those parameters (`fnHyp_of_fnObligations`), hence soundness and
  completeness (`sound_fn`, `complete_fn`), with no `wf` read.

  `CoreObligations` (Statements.lean) is the same kind of statement over the deciders `wf`'s
  packages use; it has a fifth conjunct (the lazily skipped arguments) that `FnHyp` does not read.
  `FnObligations` has `FnHyp`'s four parts only, each over the larger deciders: termination by a rank
  of the functions, cycles decreasing in a shared weight (`rankObligations`, CallGroups.lean) and self calls decreasing in weight
  (`decObligationsL`, DecreasingL.lean; no certificate is read: each function's decreasing
  argument is found on the data),
  totality from termination by induction on evaluation, calls of every `[total]` function and of the
  parameters `tp` admitted, two clauses with complementary `requires` read as one row
  (`totalObligationsRP`, TotalsG.lean), agreement with list patterns apart, the `requires` compared in either order
  and pairs read at an instance (`agreeObligationsI`, AgreeLists.lean, AgreeInst.lean), match
  independence with list patterns, lone map elements and the arguments read in passes
  (`matchObligationsL`, UniqLists.lean). Each list is decided on the data; a package states each as
  a literal list, so `FnObligations` unfolds to the named facts.

  The parameters' interpretation: every list reads only the data (`*_withHooks`), so for an
  interpretation H the same lists name the facts of `c.withHooks H`. Totality through a parameter
  holds for the interpretations total on it (`ParamsTotal c tp H`): a package takes for `tp` the
  parameters its text declares total (`Definition.totalParams`), and with `tp = []` nothing is
  assumed of H (`ParamsTotal.nil`).
-/
import KcoreSpec.CallGroups
import KcoreSpec.AgreeInst
import KcoreSpec.TotalsG
import KcoreSpec.Sound
import KcoreSpec.RightHeldHooks

set_option autoImplicit false

namespace KCore

open Det

/-- **The facts the deciders leave of `FnHyp`**, for a rank `ord` of the functions and parameters
`tp` taken total: the functions whose termination neither the rank nor their self calls' decrease
in weight shows have a result at every argument list of their sorts; the `[total]` functions
`totalOKP` does not confirm have a value there; the functions `fnExclusiveI` does not confirm have
equations that agree; the clauses `clauseFixedL` does not confirm are match independent; and
`FnHyp`'s two conditions on the theory, `OpenDecided` and `OpenLaws`. -/
def FnObligations (c : Semantics) (ord tp : List Sym) : Prop :=
  (∀ f ∈ c.rankObligations ord ++ c.decObligationsL, Terminates c f) ∧
  (∀ f ∈ c.totalObligationsRP ord tp, Total c f) ∧
  (∀ f ∈ c.agreeObligationsI, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) ∧
  (∀ p ∈ c.matchObligationsL, ∀ fn, c.lookupFn p.1 = some fn → ∀ cl, fn.clauses[p.2]? = some cl →
    MatchIndependent c cl) ∧
  OpenDecided c ∧ OpenLaws c

/-- With none named, the facts hold; the definition being plain gives the last two (decided, also
under an interpretation of the parameters, which `plain` does not read). -/
theorem FnObligations.of_nil {c : Semantics} {ord tp : List Sym}
    (h1 : c.rankObligations ord ++ c.decObligationsL = []) (h2 : c.totalObligationsRP ord tp = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = [])
    (h5 : c.plain = true := by first | decide +kernel | (rw [KCore.Semantics.plain_withHooks]; decide +kernel)) :
    FnObligations c ord tp :=
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts h5).1 r hr))
     (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts h5).2.1 fn hfn cl hcl)),
   openLaws_of_plain (Semantics.plain_parts h5).2.2⟩

variable {c : Semantics} {ord tp : List Sym}

/-- **`fnHyp_of_fnObligations` with the held variables asked of the held-named functions only**:
in place of `RightHeld`, of each function `Semantics.heldObligations` names one of two facts
(`HeldOwed`): the variables of its clauses are held, or it has a result at every argument list of
its sorts, a value where it is `[total]`. The functions not named have their variables held on the
data (`Semantics.heldFn_of_not_named`). Termination: `terminates_of_rankLN`; totality:
`totals_of_rankPN`; the other four conjuncts do not read the held variables. Where no function is
named (`Semantics.heldObligations_eq_nil`: `rightValued`) nothing is asked. -/
theorem fnHyp_of_fnObligationsN (h : c.coreOK = true) (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f)
    (hH : ParamsTotal c tp c.hooks) (hob : FnObligations c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnHyp c := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hterm := terminates_of_rankLN (hpreTop := hpreTop) (hnoEx := hnoEx) hok hsr (Semantics.ovlCase_of_core h) ord hheld hob.1
  have hmc : Exec.MatchCtxO c := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩
  have hag := clausesAgree_of_IO hok hnoEx hsr hmc hob.2.2.1
  have hmi := matchIndependentAll_of_L hok hnoEx hmc hob.2.2.2.1
  have hco : CoherentAll c := coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn ht vs hvs => ?_, hag, fun fn hfn cl hcl => ?_,
    hob.2.2.2.2.1, hob.2.2.2.2.2⟩
  · exact hterm fn.label fn (lookupFn_of_core h hfn) vs hvs
  · exact totals_of_rankPN (hpreTop := hpreTop) (hnoEx := hnoEx) hok hsr (Semantics.ovlCase_of_core h) hheld hterm hco ord tp
      hH hob.2.1 fn.label fn
      (lookupFn_of_core h hfn) ht fn (lookupFn_of_core h hfn) vs hvs
  · exact hmi fn.label fn (lookupFn_of_core h hfn) cl hcl

/-- **What the statements assume of the functions, from `coreOK`, an interpretation total on the
parameters `tp` and `FnObligations`**: termination by the rank and the self calls' decrease in
weight (`terminates_of_rankL`), agreement (`clausesAgree_of_IO`) and match independence
(`matchIndependentAll_of_L`) by their deciders, over the matcher's facts `MatchCtxO` (overloading
symbols admitted), and the named facts; with these evaluation is functional
(`coherentAll_of_parts`), and totality follows from termination by induction on evaluation
(`totals_of_rankP`, TotalsG.lean). Both inductions extend a substitution well sorted on a clause's
patterns and conditions to one on all its variables, which `hrh` allows: each other variable is of
a sort with a value. -/
theorem fnHyp_of_fnObligations (h : c.coreOK = true) (hrh : c.RightHeld) (hH : ParamsTotal c tp c.hooks)
    (hob : FnObligations c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnHyp c :=
  fnHyp_of_fnObligationsN (hpreTop := hpreTop) (hnoEx := hnoEx) h (fun f _ => hrh.heldOwed f) hH hob

/-- `sound_fn` with the held variables asked of the held-named functions only (`HeldOwed`). -/
theorem sound_fnN (c : Semantics) (ord tp : List Sym) (h : c.coreOK = true)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f)
    (hH : ParamsTotal c tp c.hooks) (hob : FnObligations c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : SoundC c :=
  sound_hyp c h (fnHyp_of_fnObligationsN (hpreTop := hpreTop) (hnoEx := hnoEx) h hheld hH hob)

/-- `complete_fn` with the held variables asked of the held-named functions only (`HeldOwed`). -/
theorem complete_fnN (c : Semantics) (ord tp : List Sym) (ref : OutFn)
    (h : c.coreOK = true) (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f)
    (hH : ParamsTotal c tp c.hooks) (hob : FnObligations c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) :
    CompleteC c ref :=
  complete_hyp c ref h (fnHyp_of_fnObligationsN (hpreTop := hpreTop) (hnoEx := hnoEx) h hheld hH hob)

/-- **Soundness** of a semantics that `coreOK` accepts, its interpretation total on `tp`, under
the facts `FnObligations` names. -/
theorem sound_fn (c : Semantics) (ord tp : List Sym) (h : c.coreOK = true) (hrh : c.RightHeld)
    (hH : ParamsTotal c tp c.hooks) (hob : FnObligations c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : SoundC c :=
  sound_hyp c h (fnHyp_of_fnObligations (hpreTop := hpreTop) (hnoEx := hnoEx) h hrh hH hob)

/-- **Completeness** of a semantics that `coreOK` accepts, its interpretation total on `tp`,
under the facts `FnObligations` names. -/
theorem complete_fn (c : Semantics) (ord tp : List Sym) (ref : OutFn)
    (h : c.coreOK = true) (hrh : c.RightHeld) (hH : ParamsTotal c tp c.hooks) (hob : FnObligations c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) :
    CompleteC c ref :=
  complete_hyp c ref h (fnHyp_of_fnObligations (hpreTop := hpreTop) (hnoEx := hnoEx) h hrh hH hob)

kernel_rfl Semantics.coreOK_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).coreOK = c.coreOK

/-- `fnHyp_of_fnObligations` for an interpretation H of the parameters total on `tp`: `coreOK`
decided once on the data, `RightHeld` of the data (`Semantics.rightHeld_withHooks`), the named
facts stated for the interpretation (the lists are the data's). For a semantics without an open
generator (`hr`, decided on the data): `RightHeld` and `ParamsTotal` of the data are carried to the
interpretation only there. -/
theorem fnHyp_withHooks (h : c.coreOK = true) (hrh : c.RightHeld) (H : HookParams) (hH : ParamsTotal c tp H)
    (hob : FnObligations (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnObligations (hpreTop := hpreTop) (hnoEx := hnoEx) ((Semantics.coreOK_withHooks c H).trans h) (Semantics.rightHeld_withHooks hrh H hr)
    (hH.withHooks hr) hob

/-- `sound_fn` for an interpretation of the parameters total on `tp`, of a semantics without an
open generator (`hr`). -/
theorem sound_fn_withHooks (c : Semantics) (ord tp : List Sym) (h : c.coreOK = true) (hrh : c.RightHeld)
    (H : HookParams) (hH : ParamsTotal c tp H) (hob : FnObligations (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) :
    SoundC (c.withHooks H) :=
  sound_hyp _ ((Semantics.coreOK_withHooks c H).trans h) (fnHyp_withHooks (hpreTop := hpreTop) (hnoEx := hnoEx) h hrh H hH hob (hr := hr))

/-- `complete_fn` for an interpretation of the parameters total on `tp`, of a semantics without an
open generator (`hr`). -/
theorem complete_fn_withHooks (c : Semantics) (ord tp : List Sym) (ref : OutFn)
    (h : c.coreOK = true) (hrh : c.RightHeld) (H : HookParams) (hH : ParamsTotal c tp H)
    (hob : FnObligations (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : CompleteC (c.withHooks H) ref :=
  complete_hyp _ ref ((Semantics.coreOK_withHooks c H).trans h) (fnHyp_withHooks (hpreTop := hpreTop) (hnoEx := hnoEx) h hrh H hH hob (hr := hr))

/-- `fnHyp_withHooks` with the held variables asked of the held-named functions only: the list is
the data's (`Semantics.heldObligations_withHooks`), the owed facts (`HeldOwed`) are stated for the
interpretation. The functions not named have their variables held under every interpretation, the
exhibited values applying no open generator, so `hr` is read by `ParamsTotal` alone. -/
theorem fnHyp_withHooksN (h : c.coreOK = true) (H : HookParams)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed (c.withHooks H) f) (hH : ParamsTotal c tp H)
    (hob : FnObligations (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnObligationsN (hpreTop := hpreTop) (hnoEx := hnoEx) ((Semantics.coreOK_withHooks c H).trans h)
    (Semantics.heldObligations_withHooks c H ▸ hheld) (hH.withHooks hr) hob

/-- `sound_fn_withHooks` with the held variables asked of the held-named functions only. -/
theorem sound_fn_withHooksN (c : Semantics) (ord tp : List Sym) (h : c.coreOK = true) (H : HookParams)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed (c.withHooks H) f)
    (hH : ParamsTotal c tp H) (hob : FnObligations (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) :
    SoundC (c.withHooks H) :=
  sound_hyp _ ((Semantics.coreOK_withHooks c H).trans h) (fnHyp_withHooksN (hpreTop := hpreTop) (hnoEx := hnoEx) h H hheld hH hob (hr := hr))

/-- `complete_fn_withHooks` with the held variables asked of the held-named functions only. -/
theorem complete_fn_withHooksN (c : Semantics) (ord tp : List Sym) (ref : OutFn)
    (h : c.coreOK = true) (H : HookParams) (hheld : ∀ f ∈ c.heldObligations, HeldOwed (c.withHooks H) f)
    (hH : ParamsTotal c tp H) (hob : FnObligations (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : CompleteC (c.withHooks H) ref :=
  complete_hyp _ ref ((Semantics.coreOK_withHooks c H).trans h) (fnHyp_withHooksN (hpreTop := hpreTop) (hnoEx := hnoEx) h H hheld hH hob (hr := hr))

/-! ## The owed conditions, rule by rule and clause by clause

`OpenDecided` is a fact about the rules and clauses with `needsWitness` only: their positions are
decided on the data (`owedRules`, `owedClauses`), so a package states them as literal lists and the
fact unfolds to one `CondDecided` per listed rule or clause. `FnFacts` is `FnObligations` without
`OpenDecided`: the theory's model reads none of it (`consistent_of_fnFacts`). -/

/-- The positions of the rules whose conditions are closed over an open variable of an unconfined
sort (`Rule.needsWitness`). -/
def Semantics.owedRules (c : Semantics) : List Nat :=
  c.rules.zipIdx.filterMap fun (r, i) => if r.needsWitness c then some i else none

/-- The clauses of that kind (`Clause.needsWitness`): the function's position and the clause's. -/
def Semantics.owedClauses (c : Semantics) : List (Nat × Nat) :=
  c.fns.zipIdx.flatMap fun (f, i) => f.clauses.zipIdx.filterMap fun (cl, j) =>
    if cl.needsWitness c then some (i, j) else none

-- `owedRules` and `owedClauses` do not read the interpretation of the parameters
kernel_rfl Semantics.owedRules_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).owedRules = c.owedRules
kernel_rfl Semantics.owedClauses_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).owedClauses = c.owedClauses

/-- **The rule side of `OpenDecided`, from the owed rules one by one.** -/
theorem openRules_of_owed {c : Semantics}
    (h : ∀ i ∈ c.owedRules, ∀ r, c.rules[i]? = some r → r.CondDecided c) :
    ∀ r ∈ c.rules, r.needsWitness c = true → r.CondDecided c := by
  intro r hr hn
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  refine h i ?_ r hi
  exact List.mem_filterMap.mpr ⟨(r, i), List.mem_zipIdx_iff_getElem?.mpr hi, by simp [hn]⟩

/-- **The clause side of `OpenDecided`, from the owed clauses one by one.** -/
theorem openClauses_of_owed {c : Semantics}
    (h : ∀ p ∈ c.owedClauses, ∀ fn, c.fns[p.1]? = some fn → ∀ cl, fn.clauses[p.2]? = some cl →
      cl.CondDecided c) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  intro fn hfn cl hcl hn
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hfn
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcl
  refine h (i, j) ?_ fn hi cl hj
  exact List.mem_flatMap.mpr ⟨(fn, i), List.mem_zipIdx_iff_getElem?.mpr hi,
    List.mem_filterMap.mpr ⟨(cl, j), List.mem_zipIdx_iff_getElem?.mpr hj, by simp [hn]⟩⟩

/-- **`FnObligations` less `OpenDecided`**: the facts about the functions the deciders leave open
and the open generators' laws (`OpenLaws`). -/
def FnFacts (c : Semantics) (ord tp : List Sym) : Prop :=
  (∀ f ∈ c.rankObligations ord ++ c.decObligationsL, Terminates c f) ∧
  (∀ f ∈ c.totalObligationsRP ord tp, Total c f) ∧
  (∀ f ∈ c.agreeObligationsI, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) ∧
  (∀ p ∈ c.matchObligationsL, ∀ fn, c.lookupFn p.1 = some fn → ∀ cl, fn.clauses[p.2]? = some cl →
    MatchIndependent c cl) ∧
  OpenLaws c

/-- `FnFacts` and `OpenDecided` are `FnObligations`. -/
theorem FnFacts.obligations {c : Semantics} {ord tp : List Sym} (hob : FnFacts c ord tp)
    (hod : OpenDecided c) : FnObligations c ord tp :=
  ⟨hob.1, hob.2.1, hob.2.2.1, hob.2.2.2.1, hod, hob.2.2.2.2⟩

/-- With no function named and no parameter of the definition open (`raw`), `FnFacts` holds. -/
theorem FnFacts.of_nil {c : Semantics} {ord tp : List Sym}
    (h1 : c.rankObligations ord ++ c.decObligationsL = []) (h2 : c.totalObligationsRP ord tp = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = [])
    (h5 : c.params.all (fun k => !k.raw) = true) : FnFacts c ord tp :=
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openLaws_of_plain fun k hk => by simpa using List.all_eq_true.mp h5 k hk⟩

/-- With none of the four lists naming a fact, `FnFacts` is `OpenLaws`: the form for a semantics
with an open generator, whose laws no decider settles. -/
theorem FnFacts.of_nil_laws {c : Semantics} {ord tp : List Sym}
    (h1 : c.rankObligations ord ++ c.decObligationsL = []) (h2 : c.totalObligationsRP ord tp = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = [])
    (hl : OpenLaws c) : FnFacts c ord tp :=
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil, hl⟩

/-- **`fnModel_of_fnFacts` with the held variables asked of the held-named functions only**
(`HeldOwed` of each function `Semantics.heldObligations` names, in place of `RightHeld`):
termination by `terminates_of_rankLN`; the totality part of `HeldOwed` is not read. -/
theorem fnModel_of_fnFactsN {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f) (hob : FnFacts c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnDet c ∧ FnSolves c := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hterm := terminates_of_rankLN (hpreTop := hpreTop) (hnoEx := hnoEx) hok hsr (Semantics.ovlCase_of_core h) ord hheld hob.1
  have hmc : Exec.MatchCtxO c := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩
  have hag := clausesAgree_of_IO hok hnoEx hsr hmc hob.2.2.1
  have hmi := matchIndependentAll_of_L hok hnoEx hmc hob.2.2.2.1
  have hco : CoherentAll c := coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp
  have hd := fnDet_of_coherent hco
  exact ⟨hd, Faithful.Model.fnSolves_of_total (hypSound_of_core h) hd
    (fun fn hfn vs hvs => hterm fn.label fn (lookupFn_of_core h hfn) vs hvs)
    fun fn hfn cl hcl hne vs σ hdec =>
      (hmi fn.label fn (lookupFn_of_core h hfn) cl hcl).2 hne fn.label fn vs σ (lookupFn_of_core h hfn) hcl hdec⟩

/-- **Every function has a result at arguments of its sorts, from `FnFacts`** with the held
variables asked of the held-named functions only: termination by the rank and the self calls'
decrease in weight. The rank reads the calls of a clause's patterns, conditions and right side, not
those of a predicate in its premise: every clause's predicate is `\top` (`hpreTop`). -/
theorem fnTerminates_of_fnFactsN {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f) (hob : FnFacts c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnTerminates c := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hterm := terminates_of_rankLN (hpreTop := hpreTop) (hnoEx := hnoEx) hok hsr (Semantics.ovlCase_of_core h) ord hheld hob.1
  exact fun fn hfn vs hvs => hterm fn.label fn (lookupFn_of_core h hfn) vs hvs

/-- **`ClausePreDecided` from `FnFacts`**: each clause's predicate has a truth value wherever its
patterns match, every function having a result (`fnTerminates_of_fnFactsN`). -/
theorem clausePreDecided_of_fnFactsN {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f) (hob : FnFacts c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : ClausePreDecided c :=
  Faithful.Model.clausePreDecided_of_terminates (hypSound_of_core h) (fnTerminates_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) h hheld hob)

/-- **`FnDet` and `FnSolves` from `FnFacts`**, under `coreOK` and `RightHeld`: termination by the
rank and the self calls' decrease in weight, agreement and match independence by their deciders
and the named facts give coherence, so one result (`fnDet_of_coherent`), and with termination the
evaluation solves the equations (`fnSolves_of_total`). Neither `OpenDecided` nor the totality facts
are read. -/
theorem fnModel_of_fnFacts {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true) (hrh : c.RightHeld)
    (hob : FnFacts c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnDet c ∧ FnSolves c :=
  fnModel_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) h (fun f _ => hrh.heldOwed f) hob

/-- **Consistency from `FnFacts`** (`consistent_of`): no owed condition is read. -/
theorem consistent_of_fnFacts {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true) (hrh : c.RightHeld)
    (hob : FnFacts c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : Consistent c :=
  consistent_of c h (fnModel_of_fnFacts (hpreTop := hpreTop) (hnoEx := hnoEx) h hrh hob).1 (fnModel_of_fnFacts (hpreTop := hpreTop) (hnoEx := hnoEx) h hrh hob).2
    (clausePreDecided_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) h (fun f _ => hrh.heldOwed f) hob) hob.2.2.2.2

/-- `consistent_of_fnFacts` for an interpretation H of the parameters: `coreOK` and `RightHeld` of
the data, of a semantics without an open generator (`hr`). -/
theorem consistent_of_fnFacts_withHooks {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (hrh : c.RightHeld) (H : HookParams) (hob : FnFacts (c.withHooks H) ord tp)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) :
    Consistent (c.withHooks H) :=
  consistent_of_fnFacts (hpreTop := hpreTop) (hnoEx := hnoEx) ((Semantics.coreOK_withHooks c H).trans h) (Semantics.rightHeld_withHooks hrh H hr) hob

/-- `consistent_of_fnFacts` with the held variables asked of the held-named functions only
(`HeldOwed`). -/
theorem consistent_of_fnFactsN {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f) (hob : FnFacts c ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : Consistent c :=
  consistent_of c h (fnModel_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) h hheld hob).1 (fnModel_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) h hheld hob).2
    (clausePreDecided_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) h hheld hob) hob.2.2.2.2

/-- `fnModel_of_fnFactsN` for an interpretation H of the parameters: the list of the held-named
functions is the data's, their owed facts are stated for the interpretation. -/
theorem fnModel_of_fnFacts_withHooksN {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (H : HookParams) (hheld : ∀ f ∈ c.heldObligations, HeldOwed (c.withHooks H) f)
    (hob : FnFacts (c.withHooks H) ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : FnDet (c.withHooks H) ∧ FnSolves (c.withHooks H) :=
  fnModel_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) ((Semantics.coreOK_withHooks c H).trans h)
    (Semantics.heldObligations_withHooks c H ▸ hheld) hob

/-- `consistent_of_fnFactsN` for an interpretation H of the parameters: `coreOK` of the data, the
list of the held-named functions the data's, their owed facts stated for the interpretation. No
hypothesis on the parameters: the functions not named have their variables held under every H. -/
theorem consistent_of_fnFacts_withHooksN {c : Semantics} {ord tp : List Sym} (h : c.coreOK = true)
    (H : HookParams) (hheld : ∀ f ∈ c.heldObligations, HeldOwed (c.withHooks H) f)
    (hob : FnFacts (c.withHooks H) ord tp) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) : Consistent (c.withHooks H) :=
  consistent_of_fnFactsN (hpreTop := hpreTop) (hnoEx := hnoEx) ((Semantics.coreOK_withHooks c H).trans h)
    (Semantics.heldObligations_withHooks c H ▸ hheld) hob

end KCore
