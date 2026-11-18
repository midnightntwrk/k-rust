/-
  Peano in the second stage of faithfulness: its semantics satisfies `Hyp` and `Stage2`, so every
  step of it is a theorem of `Γ` (`step_sound`). Its function `pred` has a catch-all,
  `pred(_) => z [owise]`, a clause of priority 200 whose equation negates the other, which the
  first stage excludes; it is total, by its two equations (`pred_succ`, `pred_owise`,
  User/Proofs.lean). The decidable facts are kernel decisions.
-/
import User.Proofs
import KcoreSpec.FaithfulStage2

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Peano.FaithfulWitness

open KCore KCore.Faithful Peano

theorem okAll : c.okAll = true := Semantics.okAll_of_ok ok

/-- Each rule's left side binds every variable of the rule (`ok_rule`). -/
theorem rules_bind : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true :=
  fun _ hr => (Semantics.ok_rule ok hr).2.2.2

/-- Each rule's predicates are `\top` (`ok_rule`). -/
theorem rules_top : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top :=
  fun _ hr => ⟨(Semantics.ok_rule ok hr).2.1, (Semantics.ok_rule ok hr).2.2.1⟩

/-- Each clause's patterns bind every variable of the clause (`ok_clauseBinds`). -/
theorem clauses_bind : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true :=
  Semantics.ok_clauseBinds ok

instance : OvlOK c := .of_nil (by decide +kernel) (by decide +kernel)

theorem fns_length : c.fns.length = 1 := by decide +kernel

/-- The definition's one function, `pred`. -/
noncomputable def predFn : Fn := c.fns[0]'(by rw [fns_length]; decide)

theorem fns_eq : c.fns = [predFn] := by
  obtain ⟨f0, hf0⟩ := List.length_eq_one_iff.mp fns_length
  unfold predFn
  simp only [hf0, List.getElem_cons_zero]

theorem lookup_pred : c.lookupFn Sym.«pred» = some predFn := rfl
theorem predFn_label : predFn.label = Sym.«pred» := rfl
theorem predFn_args : predFn.args = [Srt.«Nat»] := rfl
theorem lookup_s : lookupSig c.ctorSigs Sym.«s» = some ⟨Sym.«s», [Srt.«Nat»], Srt.«Nat»⟩ := by
  rw [lookupSig_eq]; decide +kernel

/-- `pred` is total: at `s(M)` its clause gives `M`, anywhere else its catch-all gives `z`. -/
theorem pred_total (N : GroundTerm) (hN : c.sortOf N = some Srt.«Nat») : ∃ v, Pred N v := by
  by_cases h : ∃ M, N = s M
  · obtain ⟨M, rfl⟩ := h
    obtain ⟨k, hk, hks, -⟩ := (sortOf_ctor (by decide +kernel)).mp hN
    rw [lookup_s] at hk; cases hk
    obtain ⟨s', ss', hM, -, he⟩ := sortsOf_cons.mp hks
    cases he
    exact ⟨M, pred_succ M hM⟩
  · exact ⟨z, pred_owise N hN (fun M hM => h ⟨M, hM⟩)⟩

theorem pred_callable : Callable2 c Sym.«pred» := by
  intro fn hfn vs hvs
  rw [lookup_pred] at hfn; cases hfn
  rw [predFn_args] at hvs
  match vs, hvs with
  | [], hvs => rw [sortsOf_nil] at hvs; cases hvs
  | [N], hvs =>
    obtain ⟨s', ss', hN, -, he⟩ := sortsOf_cons.mp hvs
    cases he
    exact pred_total N hN
  | _ :: _ :: _, hvs =>
    obtain ⟨_, _, _, hrest, he⟩ := sortsOf_cons.mp hvs
    cases he
    obtain ⟨_, _, _, _, h⟩ := sortsOf_cons.mp hrest
    cases h

/-- The symbols the rules and the functions apply are constructors and the like, which no
function is named, or `pred`. -/
noncomputable def calledOK (f : Sym) : Bool := (c.lookupFn f).isNone || f == Sym.«pred»

theorem callable_of {f : Sym} (h : calledOK f = true) : Callable2 c f := by
  unfold calledOK at h
  simp only [Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at h
  rcases h with h | rfl
  · intro fn hfn; rw [h] at hfn; cases hfn
  · exact pred_callable

/-- Peano has no overloading symbol, so a symbol `calledOK` reads is callable together with the
functions it overloads (`CallsAll`). -/
theorem callsAll_of {f : Sym} (h : calledOK f = true) : CallsAll c (Callable2 c) f := by
  refine ⟨callable_of h, fun o ho => ?_⟩
  have hn : c.ovls = [] := by decide +kernel
  simp [Semantics.lookupOvl, hn] at ho

theorem rules_ok : c.rules.all (fun r => plainPat c r.lhs &&
    (Term.heads r.rhs ++ (r.req.map Term.heads).getD [] ++ (r.ens.map Term.heads).getD []).all calledOK) = true := by
  decide +kernel

theorem fns_ok : c.allFns.all (fun fn => fn.clauses.all (fun cl => plainPats c cl.pats &&
    (Term.heads cl.rhs ++ (cl.req.map Term.heads).getD [] ++ (cl.ens.map Term.heads).getD []).all calledOK)) = true := by
  decide +kernel

theorem genWf_ok : genWf c = true := by decide +kernel

theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem clauses_prios : (pairs predFn.clauses).all (fun p => p.1.prio != p.2.prio) = true := by decide +kernel

theorem clauses_notAside : (pairs predFn.clauses).all (fun p => !p.1.aside && !p.2.aside) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun fn hfn => ?_, fun fn hfn s hs => ?_⟩
  · have := List.all_eq_true.mp names_plain k hk
    exact Option.isNone_iff_eq_none.mp this
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact Option.isNone_iff_eq_none.mp this.1
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

/-- **Peano satisfies `Hyp`.** -/
theorem hyp : Hyp c := by
  have hmi : MatchIndependentAll c := matchIndependentAll_of ok matchReady (MatchObligations.of_fixed clausesFixed (by decide +kernel))
  refine ⟨okAll, srReady, fun fn hfn vs hvs => ?_, fun fn hfn _ vs hvs => ?_, fun fn hfn => ?_,
    fun fn hfn cl hcl => ?_, namesNumbered⟩
  · rw [fns_eq, List.mem_singleton] at hfn; subst hfn
    obtain ⟨v, hv⟩ := pred_callable predFn lookup_pred vs hvs
    exact ⟨some v, by rw [predFn_label]; exact hv⟩
  · rw [fns_eq, List.mem_singleton] at hfn; subst hfn
    rw [predFn_label]
    exact pred_callable predFn lookup_pred vs hvs
  · rw [fns_eq, List.mem_singleton] at hfn; subst hfn
    intro cl cl' hp hprio
    have := List.all_eq_true.mp clauses_prios _ hp
    simp only [bne_iff_ne, ne_eq] at this
    have ha := List.all_eq_true.mp clauses_notAside _ hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    rcases hprio with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h this
    · rw [ha.1] at h; cases h
    · rw [ha.2] at h; cases h
  · rw [fns_eq, List.mem_singleton] at hfn; subst hfn
    exact hmi _ _ lookup_pred cl hcl

/-- **Peano is in the second stage.** -/
theorem stage2 : Stage2 c := by
  refine ⟨genWf_ok, fun r hr => ?_, fun fn hfn cl hcl => ?_⟩
  · have := List.all_eq_true.mp rules_ok r hr
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1, fun f hf => callsAll_of (List.all_eq_true.mp this.2 f hf)⟩
  · have := List.all_eq_true.mp fns_ok fn hfn
    have h := List.all_eq_true.mp this cl hcl
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, fun f hf => callsAll_of (List.all_eq_true.mp h.2 f hf)⟩

/-- **Every step of peano is a theorem of `Γ`**: in every model of `Γ c`, a configuration has each
of its `Step` successors as a successor. -/
theorem step_sound : ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  step_sound_stage2 c hyp rules_bind rules_top clauses_bind stage2

#print axioms step_sound

end Peano.FaithfulWitness
